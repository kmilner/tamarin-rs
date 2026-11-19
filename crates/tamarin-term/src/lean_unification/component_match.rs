//! Disjoint pattern-variable components of a directional match have independent
//! images. Their subjects stay frozen, including names captured in other groups.
//! See `Matching.independent_product_complete` and `Matching.independent_exists_iff`.

use super::{components, residual, Error, Outcome, RuleTable, Substitutions};
use crate::lterm::LNTerm;
use crate::rewriting::Equal;
use crate::vterm::is_ground_vterm;

fn reversed(eqs: &[Equal<LNTerm>]) -> Vec<Equal<LNTerm>> {
    eqs.iter()
        .map(|e| Equal {
            lhs: e.rhs.clone(),
            rhs: e.lhs.clone(),
        })
        .collect()
}

impl RuleTable {
    fn matching_components(
        &self,
        patterns: &[Equal<LNTerm>],
    ) -> Result<Vec<Vec<Equal<LNTerm>>>, Error> {
        if !(2..=64).contains(&patterns.len()) {
            return Ok(Vec::new());
        }
        let mut budget = residual::MAX_EXPANDED;
        if !residual::charge_expansion(
            &mut budget,
            patterns.iter().flat_map(|e| [&e.lhs, &e.rhs]),
            None,
        )? || !self.admits_terms(patterns)
        {
            return Ok(Vec::new());
        }
        Ok(components::pattern_components(patterns))
    }

    fn part_answers(&self, part: &[Equal<LNTerm>]) -> Result<Outcome, Error> {
        let bags = self.ac_bag_answers(part)?;
        if matches!(bags, Outcome::Complete(_)) {
            return Ok(bags);
        }
        if part.iter().all(|e| is_ground_vterm(&e.rhs)) {
            let ground = self.match_ground_captures(part)?;
            if matches!(ground, Outcome::Complete(_)) {
                return Ok(ground);
            }
        }
        self.match_rigid_subjects(part)
    }

    /// Public orientation is subject first. A complete negative from any
    /// admitted component refutes the conjunction, even if another deferred.
    pub(crate) fn component_has_match(
        &self,
        subjects: &[Equal<LNTerm>],
    ) -> Result<Option<bool>, Error> {
        if !(2..=64).contains(&subjects.len()) {
            return Ok(None);
        }
        let parts = self.matching_components(&reversed(subjects))?;
        if parts.is_empty() {
            return Ok(None);
        }
        let mut complete = true;
        for part in parts {
            tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
            let raw = reversed(&part);
            let mut decision = None;
            if Self::may_be_ac_bag_match(&raw) {
                decision = self.ac_bag_has_match(&raw)?;
            }
            if decision.is_none()
                && let Outcome::Complete(arms) = self.part_answers(&part)?
            {
                decision = Some(!arms.is_empty());
            }
            match decision {
                Some(false) => return Ok(Some(false)),
                None => complete = false,
                Some(true) => {}
            }
        }
        Ok(complete.then_some(true))
    }

    /// Enumeration uses the internal pattern-first orientation. Joining is a
    /// Cartesian product of binding lists, with no substitution into an image.
    pub(crate) fn component_match(&self, patterns: &[Equal<LNTerm>]) -> Result<Outcome, Error> {
        let parts = self.matching_components(patterns)?;
        if parts.is_empty() {
            return Ok(Outcome::Unsupported);
        }
        let mut families = Vec::with_capacity(parts.len());
        let mut count = 1usize;
        let mut image_nodes = 0usize;
        let mut complete = true;
        for part in parts {
            tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
            let Outcome::Complete(arms) = self.part_answers(&part)? else {
                complete = false;
                continue;
            };
            if arms.is_empty() {
                return Ok(Outcome::Complete(Vec::new()));
            }
            if !complete {
                continue;
            }

            // Count image nodes in the expanded result, with one extra cell per
            // answer. Any missing budget discards all partial results.
            let mut remaining = residual::MAX_EXPANDED;
            if !residual::charge_expansion(
                &mut remaining,
                arms.iter().flatten().map(|(_, image)| image),
                None,
            )? {
                complete = false;
                continue;
            }
            let new_nodes = residual::MAX_EXPANDED - remaining;
            image_nodes = image_nodes
                .saturating_mul(arms.len())
                .saturating_add(count.saturating_mul(new_nodes));
            count = count.saturating_mul(arms.len());
            if count.saturating_add(image_nodes) > residual::MAX_EXPANDED {
                complete = false;
                continue;
            }
            families.push(arms);
        }
        if !complete {
            return Ok(Outcome::Unsupported);
        }

        let mut answers = Substitutions::with_capacity(count);
        for mut index in 0..count {
            tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
            let mut arm = Vec::new();
            for family in &families {
                arm.extend_from_slice(&family[index % family.len()]);
                index /= family.len();
            }
            answers.push(arm);
        }
        Ok(Outcome::Complete(answers))
    }
}

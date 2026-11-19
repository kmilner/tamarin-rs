//! Project joint child variants through an inert C or AC constructor.
use super::*;

enum Operand {
    Uniform(LNTerm),
    Changing(usize),
}

impl RuleTable {
    pub(super) fn inert_product_rows(
        &self,
        keys: &[LVar],
        original: &FxHashSet<u64>,
        app: &LNTerm,
        search: &mut JoinSearch,
    ) -> Result<Option<Vec<Row>>, Error> {
        let Term::App(head @ (FunSym::Ac(_) | FunSym::C(_)), args) = app else {
            return Ok(None);
        };
        let Some((id, _, slot)) = self.declaration(*head) else {
            return Ok(None);
        };
        if self.roots.binary_search(&id).is_ok() {
            return Ok(None);
        }
        let mut operands = FxHashMap::default();
        let mut changing = Vec::new();
        for child in args.iter() {
            if operands.contains_key(child) {
                continue;
            }
            let spec = if self.stably_normal_native(child)? {
                Operand::Uniform(child.clone())
            } else {
                // A changing operand must retain the declared slot sort at
                // every specialization. Literals are stably normal above.
                if !matches!(child, Term::App(f, _) if self.declaration(*f).is_some_and(|(_, _, s)| s == slot))
                {
                    return Ok(None);
                }
                if let Some(normal) = self.uniform_reduct(child)? {
                    Operand::Uniform(normal)
                } else if crate::vterm::is_ground_vterm(child) {
                    let Some(normal) = self.reduce_native(child)? else {
                        return Ok(None);
                    };
                    if !crate::vterm::is_ground_vterm(&normal) {
                        return Ok(None);
                    }
                    Operand::Uniform(normal)
                } else {
                    changing.push(child);
                    Operand::Changing(changing.len() - 1)
                }
            };
            operands.insert(child, spec);
        }

        let rows = if let Some((first, others)) = changing.split_first() {
            // The complete child tuple shares *every* original input image.
            // Pointwise uniqueness permits reusing one value at repeated slots.
            let Some(rows) = self.join_applications(keys, original, first, others, search)? else {
                return Ok(None);
            };
            rows
        } else {
            vec![Row {
                images: keys.iter().map(|v| Term::Lit(Lit::Var(*v))).collect(),
                values: vec![],
            }]
        };

        let mut projected = BTreeSet::new();
        for mut row in rows {
            let subst = Subst::from_list(keys.iter().copied().zip(row.images.iter().cloned()));
            let mut values = Vec::with_capacity(args.len());
            for arg in args.iter() {
                let (term, image) = match &operands[arg] {
                    Operand::Uniform(t) => (t, Some(&subst)),
                    Operand::Changing(i) => (&row.values[*i], None),
                };
                if !residual::charge_expansion(&mut search.graph_work, [term], image)? {
                    return Ok(None);
                }
                values.push(match image {
                    Some(subst) => apply_vterm(subst, term.clone()),
                    None => term.clone(),
                });
            }
            row.values = vec![crate::term::f_app(*head, values)];
            projected.insert(row.rename(original));
        }
        // Children can be permuted or spliced at this head. Compare the
        // actual parent value and caller images before discarding rows.
        self.prune_specializations(projected, &mut search.matching)
    }
}

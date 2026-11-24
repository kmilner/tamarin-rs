//! Shared term graph and substitution packets for the verified references.
//! Matches retain literal input variables. Unifier and variant witnesses share
//! a fresh namespace within each returned substitution.
use super::Packet;
use crate::lean_identity::IdentityTable;
use crate::lean_unification::{
    initialize, sort_word, subsort, Error, MatchRows, Outcome, Substitutions, Theory, Watch,
    WordSlice, LEAN_THREAD,
};
use crate::lterm::{LNTerm, LSort, LVar};
use crate::maude_types::sort_of_name;
use crate::rewriting::Equal;
use crate::term::{f_app, Term};
use crate::unifier_presentation::ArmView;
use crate::vterm::Lit;
use rustc_hash::{FxHashMap, FxHashSet};
use tamarin_utils::cancellation;

use std::sync::Arc;
use tamarin_algebra_sys::{
    tamarin_lean_name_unifiers, tamarin_lean_theory_match, tamarin_lean_theory_match_exists,
    tamarin_lean_theory_unify, tamarin_lean_theory_unify_exists,
};

/// The replies of the total unifier, of its existence export and of the
/// naming export, keyed by the words of the request.
///
/// A request packet names variables and constants by the order of their
/// first occurrence, and operators by the fixed ids of the session's theory,
/// so two requests that differ only in the names of variables and constants
/// are the same words, and each export, a function of the words alone, gives
/// them the same reply. A stored reply is therefore the reply the export
/// would give again, and it is stored as the words the export returned: each
/// request reads a stored family through its own tables. An existence reply
/// says nothing about the members of the family and is only ever read back
/// as an existence reply.
#[derive(Default)]
pub struct UnifyReplies {
    families: std::sync::Mutex<FxHashMap<Box<[u64]>, std::sync::Arc<[u64]>>>,
    exists: std::sync::Mutex<FxHashMap<Box<[u64]>, bool>>,
    names: std::sync::Mutex<FxHashMap<Box<[u64]>, std::sync::Arc<[u64]>>>,
}

/// The requests of the naming export [`UnifyReplies`] keeps the tables of.
/// They are small, and a search that renames its variables apart asks a new
/// one each time.
const NAMING_MEMO: usize = 1 << 16;

impl UnifyReplies {
    /// The stored families, and the words they and their requests occupy.
    pub(crate) fn size(&self) -> (usize, usize) {
        let replies = self.families.lock().unwrap();
        let words = replies.iter().map(|(k, v)| k.len() + v.len()).sum();
        (replies.len(), words)
    }

    /// The stored existence replies.
    pub(crate) fn existence_replies(&self) -> usize {
        self.exists.lock().unwrap().len()
    }
}

/// Whether the family a reply of the total unifier lists has a member, or
/// `None` for words that are no such reply.
///
/// The reply is the status row `[1]` and then, for each member, an empty row
/// and the rows of its bindings. A member therefore shows as a row after the
/// status row, and the empty family as the status row alone.
fn family_has_member(reply: &[u64]) -> Option<bool> {
    let mut rows = rows_of(reply);
    if rows.next()?? != [1] {
        return None;
    }
    match rows.next() {
        None => Some(false),
        Some(row) => row?.is_empty().then_some(true),
    }
}

/// The caller's names of the variables of a request, for the naming export.
///
/// A request names a variable by the number of its row. `words` holds, for
/// each row in order, the identifier of the variable's name hint and its
/// index. The hint `x`, which the export gives to the variables it numbers
/// itself, has the identifier 0.
struct Labels {
    hints: IdentityTable<&'static str>,
    words: Vec<u64>,
}

impl Labels {
    fn of(packet: &Packet) -> Result<Self, Error> {
        let mut hints = IdentityTable::default();
        let mut hint = |name: &'static str| hints.intern(name).ok_or(Error::InvalidStatus(255));
        hint(LVar::new("x", LSort::Msg, 0).name)?;
        let mut words = Vec::with_capacity(2 * packet.variables.len());
        for v in packet.variables.values() {
            words.push(hint(v.name)?);
            words.push(v.idx);
        }
        Ok(Self { hints, words })
    }
}

/// What the naming export is told of a reply of the unifier: the identifier
/// and sort words of the query variables, as the rows of the first arm list
/// them, and for each arm the identifier and sort words of the variables of
/// its range in the order of first occurrence.
///
/// Nothing depends on this being right. The export only chooses names with
/// it, and a reply is read through the export's tables by [`read_named`],
/// which fails on a variable the tables do not name.
fn shape(reply: &[u64]) -> Option<(Vec<u64>, Vec<Vec<u64>>)> {
    let mut rows = rows_of(reply);
    if rows.next()?? != [1] {
        return None;
    }
    let mut heads = Vec::new();
    let mut ranges: Vec<Vec<u64>> = Vec::new();
    let mut seen = FxHashSet::default();
    for row in rows {
        let row = row?;
        let [key, sort, tokens @ ..] = row else {
            if !row.is_empty() {
                return None;
            }
            ranges.push(Vec::new());
            seen.clear();
            continue;
        };
        if ranges.len() == 1 {
            heads.extend([*key, *sort]);
        }
        let range = ranges.last_mut()?;
        for &[kind, id, sort] in tokens.as_chunks::<3>().0 {
            if kind == 0 && seen.insert((id, sort)) {
                range.extend([id, sort]);
            }
        }
    }
    Some((heads, ranges))
}

/// What a table of the naming export makes of a range variable.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Target {
    /// The variable with this name hint and index, and its own sort.
    Name(u64, u64),
    /// The query variable in this row of the arm, whose binding is left out.
    Row(u64),
}

/// The tables of the naming export: the words of the query variables, and
/// for each arm it keeps the arm's position and the target of each of its
/// range variables by identifier and sort word.
type Tables<'a> = (&'a [u64], Vec<(u64, FxHashMap<(u64, u64), Target>)>);

fn tables(words: &[u64]) -> Result<Tables<'_>, Error> {
    let mut rows = rows_of(words);
    match rows.next() {
        Some(Some([1])) => {}
        // The export declined to name the family.
        Some(Some([0])) => return Err(Error::FreshVariableOverflow),
        _ => return Err(Error::InvalidStatus(255)),
    }
    let heads = rows.next().flatten().ok_or(Error::InvalidStatus(255))?;
    let mut arms = Vec::new();
    for row in rows {
        let [arm, entries @ ..] = row.ok_or(Error::InvalidStatus(255))? else {
            return Err(Error::InvalidStatus(255));
        };
        let (entries, rest) = entries.as_chunks::<5>();
        if !rest.is_empty() {
            return Err(Error::InvalidStatus(255));
        }
        let mut table = FxHashMap::default();
        for &[id, sort, kind, a, b] in entries {
            let target = match kind {
                0 => Target::Name(a, b),
                1 => Target::Row(a),
                _ => return Err(Error::InvalidStatus(255)),
            };
            // One target for a variable.
            if sort > 4 || table.insert((id, sort), target).is_some() {
                return Err(Error::InvalidStatus(255));
            }
        }
        arms.push((*arm, table));
    }
    Ok((heads, arms))
}

/// A reply of the unifier read through the tables of the naming export, as
/// the export's library specifies the reading (`UnifierNames.apply`).
///
/// An arm with a table lists the query variables as the tables do. A row
/// whose image is one range variable with the row itself as target is left
/// out. In every other row a variable token is the variable its target
/// names, and a token without a name is an error. An arm without a table
/// must hold a variable of the sort of natural numbers, in a module that has
/// no such sort.
fn read_named(
    packet: &Packet,
    labels: &Labels,
    reply: &[u64],
    tables: &[u64],
    nat: bool,
) -> Result<Substitutions, Error> {
    let malformed = Error::InvalidStatus(255);
    let (heads, tables) = self::tables(tables)?;
    let mut tables = tables.iter().peekable();
    let mut rows = rows_of(reply).peekable();
    if rows.next() != Some(Some(&[1])) {
        return Err(malformed);
    }
    let mut answers: Substitutions = Vec::new();
    let mut arm = 0u64;
    while let Some(separator) = rows.next() {
        cancellation::check().map_err(|_| Error::Cancelled)?;
        if !separator.ok_or(malformed)?.is_empty() {
            return Err(malformed);
        }
        let table = tables.next_if(|(listed, _)| *listed == arm);
        let mut member = Vec::new();
        let mut has_nat = false;
        let mut row = 0u64;
        while let Some(binding) = rows.next_if(|r| r.is_some_and(|r| !r.is_empty())) {
            let [key, declared, tokens @ ..] = binding.ok_or(malformed)? else {
                return Err(malformed);
            };
            // Every arm lists the query variables as the tables do, in
            // whole tokens, also an arm that is not read.
            let (whole, rest) = tokens.as_chunks::<3>();
            let head = usize::try_from(2 * row)
                .ok()
                .and_then(|at| heads.get(at..at + 2));
            if head != Some(&[*key, *declared]) || !rest.is_empty() {
                return Err(malformed);
            }
            has_nat |= whole.iter().any(|&[kind, _, sort]| kind == 0 && sort == 4);
            if let Some((_, table)) = table {
                let stands = matches!(tokens, [0, id, sort]
                    if table.get(&(*id, *sort)) == Some(&Target::Row(row)));
                if !stands {
                    let var = packet
                        .variables
                        .get(*key)
                        .ok_or(Error::InvalidVariable(*key))?;
                    let (image, actual) = packet.read_image(tokens, nat, |kind, id, aux| {
                        let Some(Target::Name(hint, idx)) = table.get(&(id, aux)).copied() else {
                            return Err(Error::InvalidVariable(id));
                        };
                        let name = labels.hints.get(hint).ok_or(Error::InvalidVariable(id))?;
                        if kind != 0 {
                            return Err(Error::InvalidVariable(id));
                        }
                        Ok(LVar {
                            name,
                            sort: sort(aux)?,
                            idx,
                        })
                    })?;
                    if sort_word(var.sort) != *declared
                        || !actual.is_some_and(|s| subsort(s, var.sort))
                    {
                        return Err(malformed);
                    }
                    member.push((var, image));
                }
            }
            row += 1;
        }
        if 2 * row != heads.len() as u64 {
            return Err(malformed);
        }
        match table {
            Some(_) => answers.push(member),
            None if !nat && has_nat => {}
            None => return Err(malformed),
        }
        arm += 1;
    }
    // Every table is the table of an arm.
    if tables.next().is_some() {
        return Err(malformed);
    }
    Ok(answers)
}

/// The reply of the total unifier for one request, which lists a complete
/// family of unifiers without names for the variables of its range. The
/// naming export gives it the tables it is read through.
pub(crate) struct Unifiers {
    packet: Packet,
    reply: std::sync::Arc<[u64]>,
    nat: bool,
}

impl Unifiers {
    /// The family, read through the tables of the naming export.
    ///
    /// Without `targets` every range variable is called `x` and numbered
    /// above the indices of the request, and each member binds every
    /// variable of the request, in the order of their first occurrence.
    ///
    /// `targets[k]` proposes a name for each range variable of member `k`
    /// that the caller keeps, in the order of their first occurrence in the
    /// reply, which is the order of [`ArmView::witnesses`]. The export takes the
    /// names only if no two variables of a member get one name at one sort.
    /// The name of a request variable is not a name: the range variable
    /// then stands for that request variable, which is read only where it
    /// is the whole image of that variable, and the member has no binding
    /// for it. A proposal the export does not take is ignored, for the
    /// whole family.
    pub(crate) fn named(
        &self,
        targets: Option<&[Vec<LVar>]>,
        replies: Option<&UnifyReplies>,
    ) -> Result<Substitutions, Error> {
        let malformed = Error::InvalidStatus(255);
        // The empty family has nothing to name.
        if !family_has_member(&self.reply).ok_or(malformed)? {
            return Ok(Vec::new());
        }
        let mut labels = Labels::of(&self.packet)?;
        let (heads, ranges) = shape(&self.reply).ok_or(malformed)?;
        let mut proposal = Vec::new();
        for member in targets.unwrap_or_default() {
            let mut row = Vec::with_capacity(2 * member.len());
            for target in member {
                row.push(labels.hints.intern(target.name).ok_or(malformed)?);
                row.push(target.idx);
            }
            proposal.push(row);
        }
        let read = |proposal: &[Vec<u64>], low: bool| {
            let tables = name(&labels, &heads, &ranges, proposal, self.nat, low, replies)?;
            read_named(&self.packet, &labels, &self.reply, &tables, self.nat)
        };
        let mut family = read(&proposal, false);
        // The export tests a proposal without the reply. A proposal it takes
        // can still leave the reply without a reading, by the name of a
        // request variable for a variable that is more than the whole image
        // of that request variable. It is ignored like one the export does
        // not take.
        if !proposal.is_empty() && !matches!(family, Ok(_) | Err(Error::Cancelled)) {
            family = read(&[], false);
        }
        // A request at the top of the index space leaves no index above it.
        // The export then declines, and is asked for indices the request
        // does not use: the names are still no variable of the request.
        if family == Err(Error::FreshVariableOverflow) {
            family = read(&[], true);
        }
        family
    }

    /// What a proposer of names looks at in the members the caller keeps,
    /// under names of this function's own choosing for the range variables.
    /// Nothing may be answered from it: those names can coincide with
    /// variables the caller holds. `images` selects the request variables
    /// whose images are read as terms too.
    pub(crate) fn views(&self, images: impl Fn(&LVar) -> bool) -> Result<Vec<ArmView>, Error> {
        let malformed = Error::InvalidStatus(255);
        let mut rows = rows_of(&self.reply);
        if rows.next() != Some(Some(&[1])) {
            return Err(malformed);
        }
        let reserved: FxHashSet<u64> = self
            .packet
            .variables
            .values()
            .iter()
            .map(|v| v.idx)
            .collect();
        let hint = LVar::new("x", LSort::Msg, 0).name;
        let mut views: Vec<ArmView> = Vec::new();
        let mut names: FxHashMap<(u64, u64), usize> = FxHashMap::default();
        let free = |i: &u64| !reserved.contains(i);
        let mut unused = (0..=u64::MAX).filter(free);
        let mut has_nat = false;
        let close = |views: &mut Vec<ArmView>, has_nat: &mut bool| {
            // A member the caller does not keep.
            if !self.nat && std::mem::take(has_nat) {
                views.pop();
            }
        };
        for row in rows {
            cancellation::check().map_err(|_| Error::Cancelled)?;
            let [key, _, tokens @ ..] = row.ok_or(malformed)? else {
                close(&mut views, &mut has_nat);
                names.clear();
                unused = (0..=u64::MAX).filter(free);
                views.push(ArmView {
                    bindings: Vec::new(),
                    witnesses: Vec::new(),
                    images: Vec::new(),
                });
                continue;
            };
            let view = views.last_mut().ok_or(malformed)?;
            let var = self
                .packet
                .variables
                .get(*key)
                .ok_or(Error::InvalidVariable(*key))?;
            let mut witness = |id: u64, aux: u64| -> Result<LVar, Error> {
                let at = match names.get(&(id, aux)) {
                    Some(at) => *at,
                    None => {
                        let idx = unused.next().ok_or(Error::FreshVariableOverflow)?;
                        let sort = sort(aux)?;
                        names.insert((id, aux), view.witnesses.len());
                        view.witnesses.push((
                            LVar {
                                name: hint,
                                sort,
                                idx,
                            },
                            0,
                        ));
                        view.witnesses.len() - 1
                    }
                };
                view.witnesses[at].1 += 1;
                Ok(view.witnesses[at].0)
            };
            let mut single = None;
            for &[kind, id, sort] in tokens.as_chunks::<3>().0 {
                if kind == 0 {
                    has_nat |= sort == 4;
                    single = Some(witness(id, sort)?);
                }
            }
            if tokens.len() != 3 {
                single = None;
            }
            view.bindings.push((var, single));
            if images(&var) {
                let (image, _) = self.packet.read_image(tokens, self.nat, |kind, id, aux| {
                    names
                        .get(&(id, aux))
                        .filter(|_| kind == 0)
                        .map(|at| view.witnesses[*at].0)
                        .ok_or(Error::InvalidVariable(id))
                })?;
                view.images.push((var, image));
            }
        }
        close(&mut views, &mut has_nat);
        Ok(views)
    }
}

/// The tables of the naming export for a reply of the total unifier. Without
/// a proposal the export numbers the range above the request, or with `low`,
/// where no index is left there, by indices the request does not use.
///
/// The export is a function of the words it is sent, so `replies` answers a
/// request it has seen with the words the export returned then.
fn name(
    labels: &Labels,
    heads: &[u64],
    ranges: &[Vec<u64>],
    proposal: &[Vec<u64>],
    nat: bool,
    low: bool,
    replies: Option<&UnifyReplies>,
) -> Result<std::sync::Arc<[u64]>, Error> {
    // Everything the export reads, each part behind its length.
    let request = replies.map(|memo| {
        let rows = ranges.iter().chain(proposal);
        let mut words = Vec::with_capacity(
            6 + labels.words.len() + heads.len() + rows.clone().map(|r| r.len() + 1).sum::<usize>(),
        );
        words.extend([u64::from(nat), u64::from(low), labels.words.len() as u64]);
        words.extend(&labels.words);
        words.push(heads.len() as u64);
        words.extend(heads);
        for rows in [ranges, proposal] {
            words.push(rows.len() as u64);
            for row in rows {
                words.push(row.len() as u64);
                words.extend(row);
            }
        }
        (memo, words.into_boxed_slice())
    });
    if let Some((memo, words)) = &request
        && let Some(tables) = memo.names.lock().unwrap().get(words)
    {
        return Ok(tables.clone());
    }
    initialize()?;
    let ranges: Vec<_> = ranges.iter().map(|row| WordSlice::new(row)).collect();
    let proposal: Vec<_> = proposal.iter().map(|row| WordSlice::new(row)).collect();
    let tables: std::sync::Arc<[u64]> = LEAN_THREAD
        .with(|_| {
            // SAFETY: the shim takes owned copies of all slices and transfers its
            // output to MatchRows.
            let tables = MatchRows::new(unsafe {
                tamarin_lean_name_unifiers(
                    WordSlice::new(&labels.words),
                    WordSlice::new(heads),
                    ranges.as_ptr(),
                    ranges.len(),
                    proposal.as_ptr(),
                    proposal.len(),
                    u8::from(nat),
                    u8::from(low),
                )
            })?;
            reply_words(&tables)
        })?
        .into();
    if let Some((memo, words)) = request {
        let mut stored = memo.names.lock().unwrap();
        if stored.len() >= NAMING_MEMO {
            stored.clear();
        }
        stored.insert(words, tables.clone());
    }
    Ok(tables)
}

/// The complete family of unifiers of `eqs`, and whether its reply came from
/// `replies` instead of the export, or `None` when the request is outside the
/// theory's operators. The export stops, with [`Error::Cancelled`] or
/// [`Error::SearchBudget`], when the request is cancelled or its search takes
/// more than `work` steps (zero for no bound).
///
/// The reply of the unifier is not read here. It goes, as it is, to the
/// naming export ([`Unifiers::named`]), whose reply holds the family with
/// every range variable named.
pub(crate) fn unify(
    theory: &Arc<Theory>,
    eqs: &[Equal<LNTerm>],
    replies: Option<&UnifyReplies>,
    work: u64,
) -> Result<(Option<Unifiers>, bool), Error> {
    let Some(packet) = Packet::encode_total(theory, eqs.iter().flat_map(|e| [&e.lhs, &e.rhs]))?
    else {
        return Ok((None, false));
    };
    let request = match replies {
        Some(memo) => Some((memo, packet.request_words()?)),
        None => None,
    };
    if let Some((memo, words)) = &request {
        let stored = memo.families.lock().unwrap().get(words).cloned();
        if let Some(reply) = stored {
            let family = Unifiers {
                packet,
                reply,
                nat: theory.nat(),
            };
            return Ok((Some(family), true));
        }
    }
    initialize()?;
    let rows = packet.rows();
    let mut watch = Watch::new("unification", work);
    let reply: std::sync::Arc<[u64]> = LEAN_THREAD
        .with(|_| {
            // SAFETY: the shim consumes its own copies of all slices and writes
            // the watch, which outlives the call. MatchRows owns the single
            // output reference and releases it on every exit.
            let raw = unsafe {
                tamarin_lean_theory_unify(
                    theory.flags(),
                    WordSlice::new(theory.free()),
                    theory.ac(),
                    rows.as_ptr(),
                    rows.len(),
                    WordSlice::new(&packet.equations),
                    watch.raw(),
                )
            };
            // A stopped call returned no reply.
            watch.finish()?;
            reply_words(&MatchRows::new(raw)?)
        })?
        .into();
    drop(rows);
    // Only the reply of a call that finished is kept, with its status row.
    if family_has_member(&reply).is_none() {
        return Err(Error::InvalidStatus(255));
    }
    if let Some((memo, words)) = request {
        memo.families.lock().unwrap().insert(words, reply.clone());
    }
    let family = Unifiers {
        packet,
        reply,
        nat: theory.nat(),
    };
    Ok((Some(family), false))
}

/// Decide whether [`unify`] would return a unifier, without listing the
/// family, and whether the decision came from `replies` instead of the
/// export. `None` when the request is outside the theory's operators.
///
/// A stored family answers by whether it has a row: the existence export is
/// proved to say "exists" exactly when a unifier exists, and the family
/// export's reply is a complete family, so the two agree.
///
/// The export stops like that of [`unify`], and then decides nothing.
pub(crate) fn unify_exists(
    theory: &Arc<Theory>,
    eqs: &[Equal<LNTerm>],
    replies: Option<&UnifyReplies>,
    work: u64,
) -> Result<(Option<bool>, bool), Error> {
    let Some(packet) = Packet::encode_total(theory, eqs.iter().flat_map(|e| [&e.lhs, &e.rhs]))?
    else {
        return Ok((None, false));
    };
    let request = match replies {
        Some(memo) => Some((memo, packet.request_words()?)),
        None => None,
    };
    if let Some((memo, words)) = &request {
        let listed = memo.families.lock().unwrap().get(words).cloned();
        let listed = match listed {
            Some(reply) => Some(family_has_member(&reply).ok_or(Error::InvalidStatus(255))?),
            None => None,
        };
        let stored = listed.or_else(|| memo.exists.lock().unwrap().get(words).copied());
        if let Some(found) = stored {
            return Ok((Some(found), true));
        }
    }
    initialize()?;
    let rows = packet.rows();
    let mut watch = Watch::new("unifiability decision", work);
    let found = LEAN_THREAD.with(|_| {
        // SAFETY: the shim takes owned copies of all slices, writes the
        // watch, which outlives the call, and returns a scalar.
        let status = unsafe {
            tamarin_lean_theory_unify_exists(
                theory.flags(),
                WordSlice::new(theory.free()),
                theory.ac(),
                rows.as_ptr(),
                rows.len(),
                WordSlice::new(&packet.equations),
                watch.raw(),
            )
        };
        // A stopped call decided nothing, whatever its status.
        watch.finish()?;
        match status {
            1 => Ok(true),
            2 => Ok(false),
            // 0 is a malformed packet; it is never read as "no unifier".
            status => Err(Error::InvalidStatus(status)),
        }
    })?;
    if let Some((memo, words)) = request {
        memo.exists.lock().unwrap().insert(words, found);
    }
    Ok((Some(found), false))
}

/// The rows of a reply's single arm, each behind its length.
fn reply_words(reply: &MatchRows) -> Result<Vec<u64>, Error> {
    if reply.count() != 1 {
        return Err(Error::InvalidStatus(255));
    }
    let mut words = Vec::new();
    for i in 0..reply.rows(0) {
        cancellation::check().map_err(|_| Error::Cancelled)?;
        let size = reply.raw_row_size(0, i);
        if size == usize::MAX {
            return Err(Error::InvalidStatus(255));
        }
        words.push(size as u64);
        let start = words.len();
        words.resize(start + size, 0);
        if size != 0 && reply.copy_row(0, i, &mut words[start..])? != size {
            return Err(Error::InvalidStatus(255));
        }
    }
    Ok(words)
}

/// The rows of [`reply_words`], or `None` at a length that overruns them.
fn rows_of(mut words: &[u64]) -> impl Iterator<Item = Option<&[u64]>> {
    std::iter::from_fn(move || {
        let (&size, rest) = words.split_first()?;
        let Some((row, rest)) = usize::try_from(size)
            .ok()
            .and_then(|n| rest.split_at_checked(n))
        else {
            words = &[];
            return Some(None);
        };
        words = rest;
        Some(Some(row))
    })
}

/// The packet of a match request and the pattern variables it may bind.
fn match_request(
    theory: &Arc<Theory>,
    eqs: &[Equal<LNTerm>],
    bindable: impl Fn(&LVar) -> bool,
) -> Result<Option<(Packet, FxHashSet<LVar>, Vec<u64>)>, Error> {
    let Some(packet) = Packet::encode_total(theory, eqs.iter().flat_map(|e| [&e.lhs, &e.rhs]))?
    else {
        return Ok(None);
    };
    let keys: FxHashSet<_> = eqs
        .iter()
        .flat_map(|e| crate::lterm::frees(&e.lhs))
        .filter(bindable)
        .collect();
    let ids = keys
        .iter()
        .map(|v| packet.variables.id(*v).ok_or(Error::InvalidStatus(255)))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Some((packet, keys, ids)))
}

/// Equations have (pattern, subject) orientation. Subject variables keep their caller identities.
pub(crate) fn matches(
    theory: &Arc<Theory>,
    eqs: &[Equal<LNTerm>],
    bindable: impl Fn(&LVar) -> bool,
) -> Result<Outcome, Error> {
    let Some((packet, keys, ids)) = match_request(theory, eqs, bindable)? else {
        return Ok(Outcome::Unsupported);
    };
    initialize()?;
    let rows = packet.rows();
    LEAN_THREAD.with(|_| {
        // SAFETY: the shim takes owned copies and transfers its output to MatchRows.
        let reply = MatchRows::new(unsafe {
            tamarin_lean_theory_match(
                theory.flags(),
                WordSlice::new(theory.free()),
                theory.ac(),
                rows.as_ptr(),
                rows.len(),
                WordSlice::new(&packet.equations),
                WordSlice::new(&ids),
            )
        })?;
        decode(
            &packet,
            &reply_words(&reply)?,
            theory.nat(),
            DecodeMode::Match(&keys),
        )
        .map(Outcome::Complete)
    })
}

/// Decide whether the request of [`matches`] has an answer, without listing
/// the answers. `None` when the request is outside the theory's operators.
pub(crate) fn has_match(
    theory: &Arc<Theory>,
    eqs: &[Equal<LNTerm>],
    bindable: impl Fn(&LVar) -> bool,
) -> Result<Option<bool>, Error> {
    let Some((packet, _, ids)) = match_request(theory, eqs, bindable)? else {
        return Ok(None);
    };
    initialize()?;
    let rows = packet.rows();
    LEAN_THREAD.with(|_| {
        // SAFETY: the shim takes owned copies of all slices and returns a scalar.
        match unsafe {
            tamarin_lean_theory_match_exists(
                theory.flags(),
                WordSlice::new(theory.free()),
                theory.ac(),
                rows.as_ptr(),
                rows.len(),
                WordSlice::new(&packet.equations),
                WordSlice::new(&ids),
            )
        } {
            1 => Ok(Some(true)),
            2 => Ok(Some(false)),
            // 0 is a malformed packet; it is never read as "no match".
            status => Err(Error::InvalidStatus(status)),
        }
    })
}

impl Packet {
    /// The packet of `terms` over the operators of `theory`, with a root for
    /// each term in order. `None` when a term is outside the theory.
    pub(super) fn encode_total<'a>(
        theory: &Arc<Theory>,
        terms: impl IntoIterator<Item = &'a LNTerm>,
    ) -> Result<Option<Self>, Error> {
        let mut packet = Self::over(theory);
        for t in terms {
            cancellation::check().map_err(|_| Error::Cancelled)?;
            let Some(id) = packet.encode_theory(t) else {
                return Ok(None);
            };
            packet.equations.push(id);
        }
        Ok(Some(packet))
    }

    /// The packet of `terms` over the module's declared operators, with
    /// local operator ids and their declarations.
    pub(super) fn encode_local<'a>(
        sig: &crate::maude_sig::MaudeSig,
        terms: impl IntoIterator<Item = &'a LNTerm>,
    ) -> Result<Option<Self>, Error> {
        let mut packet = Self::default();
        let symbols = sig.declared_fun_syms();
        for t in terms {
            cancellation::check().map_err(|_| Error::Cancelled)?;
            let Some(id) = packet.encode_declared(sig.enable_nat, &symbols, t) else {
                return Ok(None);
            };
            packet.equations.push(id);
        }
        Ok(Some(packet))
    }

    /// Append one term over the module's declared operators, with local
    /// operator ids, and return its root.
    pub(super) fn encode_declared(
        &mut self,
        nat: bool,
        symbols: &crate::function_symbols::FunSig,
        term: &LNTerm,
    ) -> Option<u64> {
        self.encode_term(
            term,
            false,
            |s| nat || s != LSort::Nat,
            |f| {
                symbols
                    .contains(&f)
                    .then(|| crate::lean_unification::declaration(f, nat))
                    .flatten()
            },
        )
    }

    /// The term of a row of postfix tokens `[kind, id, aux]` and its sort.
    /// `variable` reads a variable token: kind 0 names a variable by `id`
    /// with the sort `aux`, and the naming export writes kinds 5 to 9.
    fn read_image(
        &self,
        tokens: &[u64],
        nat: bool,
        mut variable: impl FnMut(u64, u64, u64) -> Result<LVar, Error>,
    ) -> Result<(LNTerm, Option<LSort>), Error> {
        let (tokens, rest) = tokens.as_chunks::<3>();
        if !rest.is_empty() {
            return Err(Error::InvalidStatus(255));
        }
        let mut stack: Vec<(LNTerm, Option<LSort>)> = Vec::new();
        for &[k, id, aux] in tokens {
            let value = match k {
                0 | 5..=9 => {
                    let v = variable(k, id, aux)?;
                    (Term::Lit(Lit::Var(v)), Some(v.sort))
                }
                1 => {
                    let name = self.names.get(id).ok_or(Error::InvalidAtom(id))?;
                    let s = sort_of_name(&name);
                    if sort_word(s) != aux {
                        return Err(Error::InvalidAtom(id));
                    }
                    (Term::Lit(Lit::Con(name)), Some(s))
                }
                _ => {
                    let (f, arity, s) = self
                        .symbols
                        .decode(k, id, nat)
                        .ok_or(Error::InvalidStatus(255))?;
                    if aux != arity as u64 {
                        return Err(Error::InvalidStatus(255));
                    }
                    let start = stack
                        .len()
                        .checked_sub(arity)
                        .ok_or(Error::InvalidStatus(255))?;
                    let mut sorted = true;
                    let children = stack
                        .drain(start..)
                        .map(|(t, actual)| {
                            sorted &= actual.is_some_and(|actual| subsort(actual, s));
                            t
                        })
                        .collect();
                    (f_app(f, children), sorted.then_some(s))
                }
            };
            stack.push(value);
        }
        if stack.len() != 1 {
            return Err(Error::InvalidStatus(255));
        }
        stack.pop().ok_or(Error::InvalidStatus(255))
    }

    /// The variable of the request that a token of kind 0 names.
    fn input_variable(&self, kind: u64, id: u64, aux: u64) -> Result<LVar, Error> {
        let sort = sort(aux)?;
        self.variables
            .get(id)
            .filter(|v| kind == 0 && v.sort == sort)
            .ok_or(Error::InvalidVariable(id))
    }

    pub(super) fn read_term(&self, words: &[u64], nat: bool) -> Result<LNTerm, Error> {
        self.read_image(words, nat, |kind, id, aux| {
            self.input_variable(kind, id, aux)
        })
        .map(|(t, _)| t)
    }
}

fn sort(word: u64) -> Result<LSort, Error> {
    match word {
        0 => Ok(LSort::Pub),
        1 => Ok(LSort::Fresh),
        2 => Ok(LSort::Msg),
        3 => Ok(LSort::Node),
        4 => Ok(LSort::Nat),
        _ => Err(Error::InvalidStatus(255)),
    }
}

#[derive(Clone, Copy)]
enum DecodeMode<'a> {
    Match(&'a FxHashSet<LVar>),
    Variants(usize),
}

struct Arm<'a> {
    mode: DecodeMode<'a>,
    bindings: Vec<Option<LNTerm>>,
    witnesses: FxHashMap<(u64, LSort), LVar>,
    reserved: &'a FxHashSet<u64>,
    next: std::ops::RangeInclusive<u64>,
    has_nat_witness: bool,
}
impl<'a> Arm<'a> {
    fn new(width: usize, reserved: &'a FxHashSet<u64>, mode: DecodeMode<'a>) -> Self {
        Self {
            mode,
            bindings: vec![None; width],
            witnesses: FxHashMap::default(),
            reserved,
            next: 0..=u64::MAX,
            has_nat_witness: false,
        }
    }

    fn variable(&mut self, id: u64, s: LSort) -> Result<LVar, Error> {
        self.has_nat_witness |= s == LSort::Nat;
        if let Some(v) = self.witnesses.get(&(id, s)) {
            return Ok(*v);
        }
        let idx = self
            .next
            .find(|i| !self.reserved.contains(i))
            .ok_or(Error::FreshVariableOverflow)?;
        let v = LVar::new("x", s, idx);
        self.witnesses.insert((id, s), v);
        Ok(v)
    }

    fn binding(&mut self, packet: &Packet, words: &[u64], nat: bool) -> Result<(), Error> {
        let [key, expected, tokens @ ..] = words else {
            return Err(Error::InvalidStatus(255));
        };
        let var = packet
            .variables
            .get(*key)
            .ok_or(Error::InvalidVariable(*key))?;
        if sort_word(var.sort) != *expected {
            return Err(Error::InvalidStatus(255));
        }
        let (term, actual) = packet.read_image(tokens, nat, |kind, id, aux| match self.mode {
            DecodeMode::Variants(_) if kind == 0 => self.variable(id, sort(aux)?),
            DecodeMode::Variants(_) => Err(Error::InvalidVariable(id)),
            DecodeMode::Match(_) => packet.input_variable(kind, id, aux),
        })?;
        let slot = self
            .bindings
            .get_mut(*key as usize)
            .ok_or(Error::InvalidVariable(*key))?;
        if !actual.is_some_and(|s| subsort(s, var.sort)) || slot.replace(term).is_some() {
            return Err(Error::InvalidStatus(255));
        }
        Ok(())
    }

    fn finish(self, packet: &Packet, nat: bool, answers: &mut Substitutions) -> Result<(), Error> {
        let images = self
            .bindings
            .into_iter()
            .collect::<Option<Vec<_>>>()
            .ok_or(Error::InvalidStatus(255))?;
        let pairs = packet.variables.values().iter().copied().zip(images);
        match self.mode {
            DecodeMode::Variants(_) if nat || !self.has_nat_witness => {
                let mut bindings: Vec<_> = pairs.collect();
                bindings.sort_unstable_by_key(|(v, _)| *v);
                answers.push(bindings);
            }
            DecodeMode::Variants(_) => {}
            DecodeMode::Match(keys) => {
                let mut bindings = Vec::with_capacity(keys.len());
                for (var, image) in pairs {
                    if keys.contains(&var) {
                        bindings.push((var, image));
                    } else if image != Term::Lit(Lit::Var(var)) {
                        return Err(Error::InvalidStatus(255));
                    }
                }
                bindings.sort_unstable_by_key(|(v, _)| *v);
                answers.push(bindings);
            }
        }
        Ok(())
    }
}

pub(super) fn header(reply: &MatchRows) -> Result<u64, Error> {
    if reply.count() != 1 || reply.row_size(0, 0)? != 1 {
        return Err(Error::InvalidStatus(255));
    }
    let mut word = [0];
    if reply.copy_row(0, 0, &mut word)? != 1 {
        return Err(Error::InvalidStatus(255));
    }
    Ok(word[0])
}

/// Observations precede rule terms in the shared dictionary. Only observation
/// variables are reply keys. A stopped frontier has exactly one status row.
pub(super) fn decode_variants(
    packet: &Packet,
    reply: &MatchRows,
    nat: bool,
    width: usize,
) -> Result<Outcome, Error> {
    if width > packet.variables.len() {
        return Err(Error::InvalidStatus(255));
    }
    if header(reply)? == 2 && reply.rows(0) == 1 {
        return Ok(Outcome::Unsupported);
    }
    let answers = decode(
        packet,
        &reply_words(reply)?,
        nat,
        DecodeMode::Variants(width),
    )?;
    if answers.is_empty() {
        // A certified variant packet contains at least one arm. If every arm
        // requires a sort absent from this module, leave the request unresolved.
        if !nat && reply.rows(0) > 1 {
            return Ok(Outcome::Unsupported);
        }
        return Err(Error::InvalidStatus(255));
    }
    Ok(Outcome::Complete(answers))
}

fn decode(
    packet: &Packet,
    reply: &[u64],
    nat: bool,
    mode: DecodeMode<'_>,
) -> Result<Substitutions, Error> {
    let mut rows = rows_of(reply);
    if rows.next() != Some(Some(&[1])) {
        return Err(Error::InvalidStatus(255));
    }
    let width = match mode {
        DecodeMode::Variants(n) => n,
        _ => packet.variables.len(),
    };
    let reserved = packet.variables.values()[..width]
        .iter()
        .map(|v| v.idx)
        .collect();
    let mut answers = Vec::new();
    let mut current = None;
    for row in rows {
        cancellation::check().map_err(|_| Error::Cancelled)?;
        let row = row.ok_or(Error::InvalidStatus(255))?;
        if row.is_empty() {
            if let Some(arm) = current.replace(Arm::new(width, &reserved, mode)) {
                arm.finish(packet, nat, &mut answers)?;
            }
        } else {
            current
                .as_mut()
                .ok_or(Error::InvalidStatus(255))?
                .binding(packet, row, nat)?;
        }
    }
    if let Some(arm) = current {
        arm.finish(packet, nat, &mut answers)?;
    }
    Ok(answers)
}

#[cfg(test)]
#[path = "wire_tests.rs"]
mod wire_tests;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn binding_rows_preserve_sharing_and_reject_invalid_terms_and_domains() {
        use crate::function_symbols::{AcSym, FunSym};
        // Multisets alone: union is the AC symbol with id 2.
        let theory = Arc::new(Theory::new(&crate::maude_sig::mset_maude_sig()).unwrap());
        let mut packet = Packet::over(&theory);
        let x = LVar::new("a", LSort::Msg, 0);
        let y = LVar::new("b", LSort::Msg, 0);
        packet.variables.intern(x).unwrap();
        packet.variables.intern(y).unwrap();
        let reserved = [0].into_iter().collect();
        let mut arm = Arm::new(2, &reserved, DecodeMode::Variants(2));
        for malformed in [
            vec![0, 2, 1, 9, 0],                            // unknown atom
            vec![0, 2, 4, 2, 2],                            // missing children
            vec![0, 2, 0, 8, 3],                            // Node in a Msg range
            vec![0, 2, 0, 8, 2, 0, 9, 2],                   // two roots
            vec![1, 0, 0, 8, 2],                            // wrong key sort
            vec![2, 2, 0, 8, 2],                            // unknown key
            vec![0, 2, 0, 8, 2, 0, 8, 2, 4, 0, 2],          // mult, not in the theory
            vec![0, 2, 0, 8, 2, 0, 8, 2, 2, 2, 2],          // id 2 of another kind
            vec![0, 2, 0, 8, 2, 0, 8, 2, 0, 8, 2, 4, 2, 3], // wrong arity
        ] {
            assert!(arm.binding(&packet, &malformed, false).is_err());
        }
        arm.binding(&packet, &[1, 2, 0, 8, 2], false).unwrap();
        arm.binding(&packet, &[0, 2, 0, 8, 2, 0, 8, 2, 4, 2, 2], false)
            .unwrap();
        let mut answers = Vec::new();
        arm.finish(&packet, false, &mut answers).unwrap();
        let w = answers[0][1].1.clone();
        assert!(matches!(w, Term::Lit(Lit::Var(v)) if v.idx != 0));
        assert_eq!(
            answers[0][0].1,
            f_app(FunSym::Ac(AcSym::Union), vec![w.clone(), w])
        );
        let mut incomplete = Arm::new(2, &reserved, DecodeMode::Variants(2));
        incomplete
            .binding(&packet, &[0, 2, 0, 8, 4], false)
            .unwrap();
        assert!(incomplete
            .binding(&packet, &[0, 2, 0, 8, 4], false)
            .is_err());
        assert!(incomplete.finish(&packet, false, &mut answers).is_err());
    }
}

//! Checked reduction and the variant certificate check over the whole active
//! table and the original input graph.
use super::{total, Packet};
use crate::lean_unification::{
    initialize, Error, MatchRows, RuleTable, Watch, WordSlice, LEAN_THREAD,
};
use crate::lterm::{LNTerm, LVar};
use crate::maude_sig::MaudeSig;
use crate::term::Term;
use crate::vterm::Lit;
use rustc_hash::{FxHashMap, FxHashSet};
use tamarin_utils::cancellation;

use tamarin_algebra_sys::{
    tamarin_lean_checked_reduce, tamarin_lean_path_reduce, tamarin_lean_session_reduce,
    tamarin_lean_session_variant_check,
};

impl RuleTable {
    /// Observation roots precede the (left, right) roots of every active rule.
    pub(in crate::lean_unification) fn table_packet(
        &self,
        sig: &MaudeSig,
        observations: &[LNTerm],
    ) -> Result<Option<Packet>, Error> {
        let Some(rules) = self.complete_rules() else {
            return Ok(None);
        };
        Packet::with_rules(sig, observations, rules)
    }
}

/// How a proved export settled one normalization request.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Reduced {
    /// The single-path export on a table the certifier accepted.
    Certified(LNTerm),
    /// The all-paths export found one normal form on every path. This holds
    /// for any table.
    Checked(LNTerm),
    /// The single-path export on a table the certifier did not accept, after
    /// the all-paths check left the term undecided: an irreducible reduct of
    /// the input that keeps its sorts. It is the normal form only under the
    /// premise that the table is convergent.
    Path(LNTerm),
    /// The table is not certified and the all-paths check did not settle
    /// the term within its depth.
    Undecided,
    /// The term or a rule is outside the module's declarations.
    Unsupported,
}

/// The session's rewrite table in wire form, with the certifier's verdict.
///
/// The rules are encoded first and every operator of the module is declared
/// before any query term, so each request packet is this packet followed by
/// the rows of its terms: the declarations, the table rows and the rule roots
/// are word for word those of the packet that was certified. A certified
/// reduce and every variant check pass them to the session exports unchanged
/// and the rows of the terms separately. Lean's
/// `exportedSessionReduce_certified` and
/// `exportedSessionVariantCheck_certified` take `certifyTable = true` on
/// exactly those table words as their hypothesis, so the verdict cached here
/// is the premise of every such call.
pub(crate) struct ReductionTable {
    packet: Packet,
    symbols: crate::function_symbols::FunSig,
    certified: bool,
}

/// Rewrite depth requested from the certifier and from the all-paths check.
const CERTIFIER_DEPTH: u64 = 4;
const CHECKED_DEPTH: u64 = 32;
/// Initial rewrite depth of the single-path exports, doubled on request.
const PATH_DEPTH: u64 = 1 << 16;

/// The export that answers one normalization request.
#[derive(Clone, Copy)]
enum Kernel {
    Certified,
    Checked,
    Path,
}

/// What the certificate checker said about a proposed family of variants.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum FamilyCheck {
    /// Every member is normal, a member subsumes the query, and every
    /// one-step narrowing successor of a member is subsumed by a member. On a
    /// canonical table the family is a complete set of variants.
    Accepted,
    /// The family is not a certificate: `reason` is 1 when member `member`
    /// is not normal, 2 when no member subsumes the query, and 3 when a
    /// narrowing successor of member `member` is not covered.
    Rejected { reason: u8, member: u64 },
    /// The checker ran out of budget before it decided: a rewrite path was
    /// longer than its depth, or the family has more positions to narrow
    /// than its work bound.
    OutOfBudget,
    /// The checker did not decide: the rule shapes are outside its domain,
    /// or the request is outside the module's declarations.
    Undecided,
}

impl ReductionTable {
    /// `None` when a rule mentions an operator the module does not declare.
    pub(crate) fn new(sig: &MaudeSig) -> Result<Option<Self>, Error> {
        let Some(packet) = Packet::full_table(sig, &[])? else {
            return Ok(None);
        };
        initialize()?;
        let certified =
            LEAN_THREAD.with(|_| packet.certifies_table(&packet.equations, CERTIFIER_DEPTH))?;
        Ok(Some(Self {
            packet,
            symbols: sig.declared_fun_syms(),
            certified,
        }))
    }

    pub(crate) fn certified(&self) -> bool {
        self.certified
    }

    /// Normalize `input`. With `follow_path`, a term the all-paths check
    /// leaves undecided on an uncertified table is answered by the
    /// single-path export instead of [`Reduced::Undecided`].
    ///
    /// The single-path exports look for the first match of a rule, which can
    /// take time exponential in the width of an AC product. Each of their
    /// calls stops, with [`Error::Cancelled`] or [`Error::SearchBudget`], when
    /// the request is cancelled or the call takes more than `work` search
    /// steps (zero for no bound). The all-paths export has its own work limit
    /// and declines instead.
    pub(crate) fn reduce(
        &self,
        sig: &MaudeSig,
        input: &LNTerm,
        follow_path: bool,
        work: u64,
    ) -> Result<Reduced, Error> {
        let mut packet = self.packet.clone();
        let Some(root) = packet.encode_declared(sig.enable_nat, &self.symbols, input) else {
            return Ok(Reduced::Unsupported);
        };
        // The table declared every operator, so a term can add rows only.
        if packet.declarations != self.packet.declarations {
            return Err(Error::InvalidStatus(255));
        }
        initialize()?;
        let rows = packet.rows();
        // The first `table` rows are word for word the rows the certifier
        // saw; the rows of the term follow them.
        let table = self.packet.nodes.len();
        let rules = &self.packet.equations;
        let (mut kernel, mut fuel) = if self.certified {
            (Kernel::Certified, PATH_DEPTH)
        } else {
            (Kernel::Checked, CHECKED_DEPTH)
        };
        LEAN_THREAD.with(|_| loop {
            cancellation::check().map_err(|_| Error::Cancelled)?;
            let mut watch = Watch::new("reduction", work);
            // SAFETY: all slices and the watch live through the call.
            // MatchRows owns the returned array. `table` is at most the
            // number of rows.
            let raw = unsafe {
                let declarations = WordSlice::new(&packet.declarations);
                let rules = WordSlice::new(rules);
                match kernel {
                    Kernel::Certified => tamarin_lean_session_reduce(
                        declarations,
                        rows.as_ptr(),
                        table,
                        rules,
                        rows.as_ptr().add(table),
                        rows.len() - table,
                        root,
                        fuel,
                        watch.raw(),
                    ),
                    Kernel::Checked => tamarin_lean_checked_reduce(
                        declarations,
                        rows.as_ptr(),
                        rows.len(),
                        rules,
                        root,
                        fuel,
                    ),
                    Kernel::Path => tamarin_lean_path_reduce(
                        declarations,
                        rows.as_ptr(),
                        rows.len(),
                        rules,
                        root,
                        fuel,
                        watch.raw(),
                    ),
                }
            };
            // A stopped call returned no reply. The all-paths export never
            // touches the watch.
            watch.finish()?;
            let reply = MatchRows::new(raw)?;
            match (total::header(&reply)?, reply.rows(0), kernel) {
                // More depth always settles a certified table; the reply is
                // never read as an answer before it does. A path on any other
                // table ends whenever the table terminates.
                (3, 1, Kernel::Certified | Kernel::Path) if fuel < u64::MAX => {
                    fuel = fuel.saturating_mul(2);
                }
                (2, 1, Kernel::Checked) if follow_path => {
                    (kernel, fuel) = (Kernel::Path, PATH_DEPTH);
                }
                (2, 1, Kernel::Checked) => return Ok(Reduced::Undecided),
                // The table is not range restricted, or the reduct lost a sort.
                (2, 1, Kernel::Path) => return Ok(Reduced::Unsupported),
                (1, 2, _) => {
                    let result = read_normal_form(&packet, &reply, sig, input)?;
                    return Ok(match kernel {
                        Kernel::Certified => Reduced::Certified(result),
                        Kernel::Checked => Reduced::Checked(result),
                        Kernel::Path => Reduced::Path(result),
                    });
                }
                _ => return Err(Error::InvalidStatus(255)),
            }
        })
    }

    /// Ask the certificate checker whether `family` is a complete set of
    /// variants of `query`. `fuel` bounds every rewrite path the checker
    /// follows. `work`, when nonzero, bounds the positions at which the
    /// closure test looks for narrowing steps, added up over the members
    /// ([`Self::variant_check_charge`]): the members whose running total
    /// stays within it are tested, and the reply is then out of budget
    /// unless that was every member. Neither bounds the time spent inside
    /// the unifier on one member, which cannot be interrupted.
    ///
    /// A substitution of a family has a fresh range: a variable of an image
    /// is distinct from every variable of the query, whatever it is called.
    /// The checker reads each row as an ordinary substitution in which an
    /// unlisted variable keeps itself, so a range variable that is spelled
    /// like a query variable is renamed first.
    ///
    /// The request is the table packet, word for word as the certifier saw
    /// it, with the rows of the query and of the images passed separately.
    /// `exportedSessionVariantCheck_certified` then makes an accepted family
    /// a complete set of variants whenever [`Self::certified`] holds; on any
    /// other table that conclusion needs the premise that the table is
    /// canonical.
    pub(crate) fn check_variants(
        &self,
        sig: &MaudeSig,
        query: &LNTerm,
        family: &[Vec<(LVar, LNTerm)>],
        fuel: u64,
        work: u64,
    ) -> Result<FamilyCheck, Error> {
        let Some(request) = self.variant_request(sig, query, family)? else {
            return Ok(FamilyCheck::Undecided);
        };
        initialize()?;
        cancellation::check().map_err(|_| Error::Cancelled)?;
        match request.check(&self.packet.equations, fuel, work)?[..] {
            [1] => Ok(FamilyCheck::Accepted),
            [2, reason @ 1..=3, member] => Ok(FamilyCheck::Rejected {
                reason: reason as u8,
                member,
            }),
            // Reason 4: a rule the checker does not narrow with.
            [2, 4, _] => Ok(FamilyCheck::Undecided),
            [3] => Ok(FamilyCheck::OutOfBudget),
            // Status 0 is a malformed packet, which includes a binding whose
            // image does not have the sort of its variable.
            [0] => Err(Error::MalformedVariants),
            _ => Err(Error::InvalidStatus(255)),
        }
    }

    /// What the closure test charges against the work bound for the whole
    /// of `family` (`VariantClosure.charge` in the Lean library): for each
    /// member, the positions that are not variables in the normal form of
    /// every instantiated observation whose query term is not a variable. An
    /// operator modulo AC of `k` arguments counts as its `k - 1` binary
    /// applications. `None` when a normal form is not available.
    ///
    /// This is a diagnostic for choosing a bound, and no part of the check.
    pub(crate) fn variant_check_charge(
        &self,
        sig: &MaudeSig,
        query: &LNTerm,
        family: &[Vec<(LVar, LNTerm)>],
    ) -> Result<Option<u64>, Error> {
        fn sites(term: &LNTerm) -> u64 {
            match term {
                Term::Lit(Lit::Var(_)) => 0,
                Term::Lit(_) => 1,
                Term::App(symbol, children) => {
                    let own = if symbol.is_ac() {
                        children.len().saturating_sub(1) as u64
                    } else {
                        1
                    };
                    own + children.iter().map(sites).sum::<u64>()
                }
            }
        }
        let mut charge = 0;
        for member in family {
            let bindings = crate::subst::Subst::from_list(member.clone());
            for observation in super::checked_variants::observations(query) {
                if matches!(observation, Term::Lit(Lit::Var(_))) {
                    continue;
                }
                let instance = crate::subst::apply_vterm(&bindings, observation.clone());
                // The charge is an estimate: its reductions stop on
                // cancellation only.
                match self.reduce(sig, &instance, true, 0)? {
                    Reduced::Certified(value) | Reduced::Checked(value) | Reduced::Path(value) => {
                        charge += sites(&value);
                    }
                    Reduced::Unsupported | Reduced::Undecided => return Ok(None),
                }
            }
        }
        Ok(Some(charge))
    }

    /// The table packet extended by the query and the family. `None` when a
    /// term is outside the module's declarations.
    fn variant_request(
        &self,
        sig: &MaudeSig,
        query: &LNTerm,
        family: &[Vec<(LVar, LNTerm)>],
    ) -> Result<Option<VariantRequest>, Error> {
        use crate::lterm::HasFrees;
        let mut packet = self.packet.clone();
        let encode = |packet: &mut Packet, term: &LNTerm| {
            packet.encode_declared(sig.enable_nat, &self.symbols, term)
        };
        let mut roots = Vec::new();
        for observation in super::checked_variants::observations(query) {
            let Some(root) = encode(&mut packet, observation) else {
                return Ok(None);
            };
            roots.push(root);
        }
        let scope: FxHashSet<LVar> = crate::lterm::frees(query).into_iter().collect();
        let mut top = scope.iter().map(|v| v.idx).max().unwrap_or(0);
        for (_, image) in family.iter().flatten() {
            image.for_each_free(&mut |v| top = top.max(v.idx));
        }
        let mut members = Vec::with_capacity(family.len());
        for member in family {
            cancellation::check().map_err(|_| Error::Cancelled)?;
            let mut renamed: FxHashMap<LVar, LVar> = FxHashMap::default();
            let mut overflow = false;
            let mut row = Vec::with_capacity(2 * member.len());
            for (key, image) in member {
                let image = image.clone().map_free(&mut |v| {
                    if !scope.contains(&v) {
                        return v;
                    }
                    *renamed.entry(v).or_insert_with(|| {
                        match top.checked_add(1) {
                            Some(next) => top = next,
                            None => overflow = true,
                        }
                        LVar { idx: top, ..v }
                    })
                });
                let (Some(key), Some(image)) = (
                    encode(&mut packet, &Term::Lit(Lit::Var(*key))),
                    encode(&mut packet, &image),
                ) else {
                    return Ok(None);
                };
                row.extend([key, image]);
            }
            if overflow {
                return Ok(None);
            }
            members.push(row);
        }
        // The table declared every operator, so the terms added rows only.
        if packet.declarations != self.packet.declarations {
            return Err(Error::InvalidStatus(255));
        }
        Ok(Some(VariantRequest {
            table: self.packet.nodes.len(),
            packet,
            roots,
            members,
        }))
    }
}

/// One request to the certificate checker: the graph, whose first `table`
/// rows are the session table, the roots of the observed terms, and one row
/// of (variable, image) node pairs per member.
struct VariantRequest {
    table: usize,
    packet: Packet,
    roots: Vec<u64>,
    members: Vec<Vec<u64>>,
}

impl VariantRequest {
    /// The single status row of the checker's reply.
    fn check(&self, rules: &[u64], fuel: u64, work: u64) -> Result<Vec<u64>, Error> {
        let rows = self.packet.rows();
        let members: Vec<WordSlice> = self.members.iter().map(|row| WordSlice::new(row)).collect();
        LEAN_THREAD.with(|_| {
            // SAFETY: all slices live through the call. MatchRows owns the
            // returned array. `table` is at most the number of rows.
            let reply = MatchRows::new(unsafe {
                tamarin_lean_session_variant_check(
                    WordSlice::new(&self.packet.declarations),
                    rows.as_ptr(),
                    self.table,
                    WordSlice::new(rules),
                    rows.as_ptr().add(self.table),
                    rows.len() - self.table,
                    WordSlice::new(&self.roots),
                    members.as_ptr(),
                    members.len(),
                    fuel,
                    work,
                )
            })?;
            if reply.count() != 1 || reply.rows(0) != 1 {
                return Err(Error::InvalidStatus(255));
            }
            let mut words = vec![0; reply.row_size(0, 0)?];
            if reply.copy_row(0, 0, &mut words)? != words.len() {
                return Err(Error::InvalidStatus(255));
            }
            Ok(words)
        })
    }
}

fn read_normal_form(
    packet: &Packet,
    reply: &MatchRows,
    sig: &MaudeSig,
    input: &LNTerm,
) -> Result<LNTerm, Error> {
    let mut words = vec![0; reply.row_size(0, 1)?];
    if reply.copy_row(0, 1, &mut words)? != words.len() {
        return Err(Error::InvalidStatus(255));
    }
    let result = packet.read_term(&words, sig.enable_nat)?;
    let scope = crate::lterm::frees(input);
    if crate::lterm::frees(&result)
        .iter()
        .any(|v| scope.binary_search(v).is_err())
    {
        return Err(Error::InvalidStatus(255));
    }
    Ok(result)
}

/// Normalize the submitted term against the full active table without the
/// premise that the table is convergent: the certified single-path export on
/// a table the certifier accepts, and the all-paths check otherwise. `None`
/// when that check does not settle the term (two paths end in different
/// normal forms, or the rewrite graph is beyond its work limit) or the
/// request is outside the module's declarations.
pub fn reduction_for_convergent_theory(
    sig: &MaudeSig,
    input: &LNTerm,
) -> Result<Option<LNTerm>, Error> {
    let Some(table) = ReductionTable::new(sig)? else {
        return Ok(None);
    };
    Ok(match table.reduce(sig, input, false, 0)? {
        Reduced::Certified(result) | Reduced::Checked(result) | Reduced::Path(result) => {
            Some(result)
        }
        Reduced::Undecided | Reduced::Unsupported => None,
    })
}

impl Packet {
    pub(super) fn full_table(
        sig: &MaudeSig,
        observations: &[LNTerm],
    ) -> Result<Option<Self>, Error> {
        // The algebra consumes expanded terms. encode_total checks every rule and
        // observation against the actual module declarations, including in theories
        // that also carry parser-only macro names.
        Self::with_rules(sig, observations, sig.rrules().iter())
    }

    pub(super) fn with_rules<'a>(
        sig: &MaudeSig,
        observations: &[LNTerm],
        rules: impl Iterator<Item = &'a crate::rewriting::RRule<LNTerm>>,
    ) -> Result<Option<Self>, Error> {
        let Some(mut packet) = Packet::encode_total(
            sig,
            observations
                .iter()
                .chain(rules.flat_map(|r| [&r.lhs, &r.rhs])),
        )?
        else {
            return Ok(None);
        };
        // Variants quantify over substitutions using any declared operator.
        for f in sig.declared_fun_syms() {
            use crate::function_symbols::FunSym;
            let kind = match f {
                FunSym::NoEq(_) => 2,
                FunSym::C(_) => 3,
                FunSym::Ac(_) => 4,
                FunSym::List => continue,
            };
            let (arity, sort) = crate::lean_unification::declaration(f, sig.enable_nat)
                .ok_or(Error::InvalidStatus(255))?;
            packet
                .symbol(f, kind, arity, sort)
                .ok_or(Error::InvalidStatus(255))?;
        }
        Ok(Some(packet))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function_symbols::AcSym;
    use crate::lterm::{pub_term, LSort};
    use crate::maude_sig::{mset_maude_sig, pair_maude_sig};
    use crate::term::f_app_ac;
    use std::time::{Duration, Instant};

    /// The identity family for a multiset of `factors` distinct public names
    /// and one variable of sort Node, which makes the product kind-level.
    fn kind_level_identity(factors: u64) -> (FamilyCheck, Duration) {
        let sig = pair_maude_sig().merge(mset_maude_sig());
        let table = ReductionTable::new(&sig).unwrap().unwrap();
        assert!(table.certified());
        let mut terms: Vec<LNTerm> = (0..factors).map(|i| pub_term(format!("p{i}"))).collect();
        terms.push(Term::Lit(Lit::Var(LVar::new("outside", LSort::Node, 0))));
        let query = f_app_ac(AcSym::Union, terms);
        let start = Instant::now();
        let verdict = table
            .check_variants(&sig, &query, &[Vec::new()], 1 << 16, 0)
            .unwrap();
        (verdict, start.elapsed())
    }

    /// Acceptance test for a checker whose closure test is not exponential
    /// in the width of a kind-level AC product. Until then such a query is
    /// answered by the checked variants export alone.
    #[test]
    #[ignore = "session variant check, identity family on p0++..++p(k-1)++#outside:Node over the \
                pairing and multiset table: time and memory grow as 2^k. Measured under a 6 GB \
                cap: 16 factors 0.28 s and 90 MB, 20 factors 5.4 s and 1.43 GB peak; 129 factors \
                are killed at 6 GB after 3 s and at 12 GB. The work bound does not see it (the \
                charge is k)"]
    fn kind_level_product_check_is_not_exponential() {
        let mut slow = Vec::new();
        for factors in [16, 20] {
            let (verdict, elapsed) = kind_level_identity(factors);
            assert_eq!(verdict, FamilyCheck::Accepted, "{factors} factors");
            if elapsed > Duration::from_millis(100) {
                slow.push(format!("{factors} factors: {elapsed:?}"));
            }
        }
        assert!(slow.is_empty(), "closure test above 100 ms: {slow:?}");
    }
}

//! Checked reduction and the variant certificate check on the table of the
//! theory: the rules of its enabled builtins, which the exports add, and its
//! user rules.
use super::{total, Packet};
use crate::lean_unification::{
    initialize, Error, MatchRows, RuleTable, Theory, Watch, WordSlice, LEAN_THREAD,
};
use crate::lterm::{LNTerm, LVar};
use crate::maude_sig::MaudeSig;
use crate::rewriting::RRule;
use crate::term::Term;
use crate::vterm::Lit;
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::BTreeSet;
use std::sync::Arc;
use tamarin_utils::cancellation;

use tamarin_algebra_sys::{
    tamarin_lean_theory_certify, tamarin_lean_theory_path_reduce, tamarin_lean_theory_reduce,
    tamarin_lean_theory_variant_check,
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
    /// The single-path export on a table the certifier did not accept: an
    /// irreducible reduct of the input that keeps its sorts. It is the
    /// normal form only under the premise that the table is convergent.
    Path(LNTerm),
    /// The table is not certified and the caller did not ask for a path.
    Undecided,
    /// The term or a rule is outside the module's declarations.
    Unsupported,
}

/// The session's rewrite table in wire form, with the certifier's verdict.
///
/// The table is the theory description and the user rules: their node rows,
/// numbered from 0, and their (lhs, rhs) roots. The rules of the enabled
/// builtins are not among them; the exports add those. Every request passes
/// these words unchanged, and the rows of its terms separately, numbered
/// from 0, over the same variables and names. Lean's
/// `theoryReduce_certified` and `theoryVariantCheck_certified` take
/// `theoryCertify = true` on exactly those table words as their hypothesis,
/// so the verdict cached here is the premise of every such call.
pub(crate) struct ReductionTable {
    packet: Packet,
    certified: bool,
}

/// The rules of `sig` that are not rules of an enabled builtin theory
/// (Diffie-Hellman, bilinear pairing, exclusive or): the equations of the
/// file and those of the rule-carrying builtins such as pairing. A rule that
/// is also a builtin rule is left to the exports, which add every builtin
/// rule, so no rule is sent twice.
pub(crate) fn user_rules(sig: &MaudeSig) -> Vec<RRule<LNTerm>> {
    let mut builtin = BTreeSet::new();
    if sig.enable_dh {
        builtin.extend(crate::builtin::dh_rules());
    }
    if sig.enable_bp {
        builtin.extend(crate::builtin::bp_rules());
    }
    if sig.enable_xor {
        builtin.extend(crate::builtin::xor_rules());
    }
    sig.rrules()
        .into_iter()
        .filter(|rule| !builtin.contains(rule))
        .collect()
}

/// Rewrite depth requested from the certifier.
const CERTIFIER_DEPTH: u64 = 4;
/// Rewrite depth of the second request, made for a table the certifier
/// refused at [`CERTIFIER_DEPTH`]. The verdict is sound at every depth, and
/// a rule whose normal forms lie deeper than the first depth (a chain of
/// rules, or a right side that another rule rewrites) is accepted only here.
const CERTIFIER_RETRY_DEPTH: u64 = 16;
/// Initial rewrite depth of the single-path exports, doubled on request.
const PATH_DEPTH: u64 = 1 << 16;

/// Whether the certifier accepts the table of `packet` at rewrite depth
/// `fuel`: the rules of the theory's builtins and the user rules the packet
/// holds.
fn certify(packet: &Packet, fuel: u64) -> Result<bool, Error> {
    let theory = packet.theory()?;
    initialize()?;
    let rows = packet.rows();
    // SAFETY: the shim copies all words while the borrowed slices are live.
    let verdict = LEAN_THREAD.with(|_| unsafe {
        tamarin_lean_theory_certify(
            theory.flags(),
            WordSlice::new(theory.free()),
            theory.ac(),
            rows.as_ptr(),
            rows.len(),
            WordSlice::new(&packet.equations),
            fuel,
        )
    });
    match verdict {
        0 => Ok(false),
        1 => Ok(true),
        status => Err(Error::InvalidStatus(status)),
    }
}

/// The export that answers one normalization request.
#[derive(Clone, Copy)]
enum Kernel {
    Certified,
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
    /// The table of `sig` over `theory`, the description of `sig`. `None`
    /// when a rule mentions an operator outside the theory.
    pub(crate) fn new(theory: &Arc<Theory>, sig: &MaudeSig) -> Result<Option<Self>, Error> {
        let mut packet = Packet::over(theory);
        for rule in user_rules(sig) {
            cancellation::check().map_err(|_| Error::Cancelled)?;
            let (Some(lhs), Some(rhs)) = (
                packet.encode_theory(&rule.lhs),
                packet.encode_theory(&rule.rhs),
            ) else {
                return Ok(None);
            };
            packet.equations.extend([lhs, rhs]);
        }
        let certified =
            certify(&packet, CERTIFIER_DEPTH)? || certify(&packet, CERTIFIER_RETRY_DEPTH)?;
        Ok(Some(Self { packet, certified }))
    }

    /// The certifier's verdict on this table at rewrite depth `fuel`.
    #[cfg(test)]
    pub(super) fn certifies(&self, fuel: u64) -> Result<bool, Error> {
        certify(&self.packet, fuel)
    }

    pub(crate) fn certified(&self) -> bool {
        self.certified
    }

    /// Normalize `input`. On a table the certifier did not accept the
    /// single-path export answers when `follow_path` is set, and the reply is
    /// [`Reduced::Undecided`] otherwise: nothing proves that a table without
    /// a certificate has one normal form per term.
    ///
    /// The single-path exports look for the first match of a rule, which can
    /// take time exponential in the width of an AC product. Each of their
    /// calls stops, with [`Error::Cancelled`] or [`Error::SearchBudget`], when
    /// the request is cancelled or the call takes more than `work` search
    /// steps (zero for no bound).
    pub(crate) fn reduce(
        &self,
        input: &LNTerm,
        follow_path: bool,
        work: u64,
    ) -> Result<Reduced, Error> {
        let mut term = self.packet.further();
        let Some(root) = term.encode_theory(input) else {
            return Ok(Reduced::Unsupported);
        };
        initialize()?;
        let theory = self.packet.theory()?;
        // The table rows are word for word the rows the certifier saw; the
        // rows of the term are numbered from 0.
        let table = self.packet.rows();
        let extra = term.rows();
        let rules = &self.packet.equations;
        let kernel = if self.certified {
            Kernel::Certified
        } else if follow_path {
            Kernel::Path
        } else {
            return Ok(Reduced::Undecided);
        };
        let mut fuel = PATH_DEPTH;
        LEAN_THREAD.with(|_| loop {
            cancellation::check().map_err(|_| Error::Cancelled)?;
            let mut watch = Watch::new("reduction", work);
            // SAFETY: all slices and the watch live through the call.
            // MatchRows owns the returned array. `table` is at most the
            // number of rows.
            let raw = unsafe {
                let reduce = match kernel {
                    Kernel::Certified => tamarin_lean_theory_reduce,
                    Kernel::Path => tamarin_lean_theory_path_reduce,
                };
                reduce(
                    theory.flags(),
                    WordSlice::new(theory.free()),
                    theory.ac(),
                    table.as_ptr(),
                    table.len(),
                    WordSlice::new(rules),
                    extra.as_ptr(),
                    extra.len(),
                    root,
                    fuel,
                    watch.raw(),
                )
            };
            // A stopped call returned no reply.
            watch.finish()?;
            let reply = MatchRows::new(raw)?;
            match (total::header(&reply)?, reply.rows(0), kernel) {
                // More depth always settles a certified table; the reply is
                // never read as an answer before it does. A path on any other
                // table ends whenever the table terminates.
                (3, 1, _) if fuel < u64::MAX => {
                    fuel = fuel.saturating_mul(2);
                }
                // The table is not range restricted, or the reduct lost a sort.
                (2, 1, Kernel::Path) => return Ok(Reduced::Unsupported),
                (1, 2, _) => {
                    let result = read_normal_form(&term, &reply, input)?;
                    return Ok(match kernel {
                        Kernel::Certified => Reduced::Certified(result),
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
    /// the unifier on one member. The call is interruptible instead: it
    /// stops, with [`Error::Cancelled`] or [`Error::SearchBudget`], when the
    /// request is cancelled or the call takes more than `search` search steps
    /// (zero for no bound), and then decides nothing.
    ///
    /// A substitution of a family has a fresh range: a variable of an image
    /// is distinct from every variable of the query, whatever it is called.
    /// The checker reads each row as an ordinary substitution in which an
    /// unlisted variable keeps itself, so a range variable that is spelled
    /// like a query variable is renamed first.
    ///
    /// The request is the table packet, word for word as the certifier saw
    /// it, with the rows of the query and of the images passed separately.
    /// `theoryVariantCheck_certified` then makes an accepted family
    /// a complete set of variants whenever [`Self::certified`] holds; on any
    /// other table that conclusion needs the premise that the table is
    /// canonical.
    pub(crate) fn check_variants(
        &self,
        query: &LNTerm,
        family: &[Vec<(LVar, LNTerm)>],
        fuel: u64,
        work: u64,
        search: u64,
    ) -> Result<FamilyCheck, Error> {
        let Some(request) = self.variant_request(query, family)? else {
            return Ok(FamilyCheck::Undecided);
        };
        initialize()?;
        cancellation::check().map_err(|_| Error::Cancelled)?;
        match request.check(&self.packet, fuel, work, search)?[..] {
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
                match self.reduce(&instance, true, 0)? {
                    Reduced::Certified(value) | Reduced::Path(value) => {
                        charge += sites(&value);
                    }
                    Reduced::Unsupported | Reduced::Undecided => return Ok(None),
                }
            }
        }
        Ok(Some(charge))
    }

    /// The rows of the query and the family that follow the table. `None`
    /// when a term is outside the theory.
    fn variant_request(
        &self,
        query: &LNTerm,
        family: &[Vec<(LVar, LNTerm)>],
    ) -> Result<Option<VariantRequest>, Error> {
        use crate::lterm::HasFrees;
        let mut packet = self.packet.further();
        let encode = |packet: &mut Packet, term: &LNTerm| packet.encode_theory(term);
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
        Ok(Some(VariantRequest {
            packet,
            roots,
            members,
        }))
    }
}

/// One request to the certificate checker: the rows of the observed terms
/// and of the images, numbered from 0, the roots of the observed terms, and
/// one row of (variable, image) node pairs per member.
struct VariantRequest {
    packet: Packet,
    roots: Vec<u64>,
    members: Vec<Vec<u64>>,
}

impl VariantRequest {
    /// The single status row of the checker's reply on `table`.
    fn check(&self, table: &Packet, fuel: u64, work: u64, search: u64) -> Result<Vec<u64>, Error> {
        let theory = table.theory()?;
        let rules = &table.equations;
        let table = table.rows();
        let rows = self.packet.rows();
        let members: Vec<WordSlice> = self.members.iter().map(|row| WordSlice::new(row)).collect();
        LEAN_THREAD.with(|_| {
            let mut watch = Watch::new("variant check", search);
            // SAFETY: all slices and the watch live through the call.
            // MatchRows owns the returned array.
            let raw = unsafe {
                tamarin_lean_theory_variant_check(
                    theory.flags(),
                    WordSlice::new(theory.free()),
                    theory.ac(),
                    table.as_ptr(),
                    table.len(),
                    WordSlice::new(rules),
                    rows.as_ptr(),
                    rows.len(),
                    WordSlice::new(&self.roots),
                    members.as_ptr(),
                    members.len(),
                    fuel,
                    work,
                    watch.raw(),
                )
            };
            // A stopped call returned no reply.
            watch.finish()?;
            let reply = MatchRows::new(raw)?;
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

fn read_normal_form(packet: &Packet, reply: &MatchRows, input: &LNTerm) -> Result<LNTerm, Error> {
    let mut words = vec![0; reply.row_size(0, 1)?];
    if reply.copy_row(0, 1, &mut words)? != words.len() {
        return Err(Error::InvalidStatus(255));
    }
    let result = packet.read_term(&words, packet.theory()?.nat())?;
    let scope = crate::lterm::frees(input);
    if crate::lterm::frees(&result)
        .iter()
        .any(|v| scope.binary_search(v).is_err())
    {
        return Err(Error::InvalidStatus(255));
    }
    Ok(result)
}

/// Normalize the submitted term against the full active table of a theory
/// that the caller takes to be convergent, as the name says. On a table the
/// certifier accepts the reply is the unique normal form, and that is proved.
/// On any other table it is an irreducible reduct along one rewrite path
/// that keeps the sorts of the term, which is the normal form under the
/// caller's premise. `None` when the table is not range restricted, a reduct
/// lost a sort or the request is outside the theory's operators.
pub fn reduction_for_convergent_theory(
    sig: &MaudeSig,
    input: &LNTerm,
) -> Result<Option<LNTerm>, Error> {
    let Some(theory) = Theory::new(sig) else {
        return Ok(None);
    };
    let Some(table) = ReductionTable::new(&Arc::new(theory), sig)? else {
        return Ok(None);
    };
    Ok(match table.reduce(input, true, 0)? {
        Reduced::Certified(result) | Reduced::Path(result) => Some(result),
        Reduced::Undecided | Reduced::Unsupported => None,
    })
}

impl Packet {
    /// The packet of the variant proposers: the observations, then every
    /// rule of `sig`, builtin rules included, with local operator ids and the
    /// declaration of every operator of the module.
    pub(super) fn full_table(
        sig: &MaudeSig,
        observations: &[LNTerm],
    ) -> Result<Option<Self>, Error> {
        // The algebra consumes expanded terms. encode_local checks every rule and
        // observation against the actual module declarations, including in theories
        // that also carry parser-only macro names.
        Self::with_rules(sig, observations, sig.rrules().iter())
    }

    pub(super) fn with_rules<'a>(
        sig: &MaudeSig,
        observations: &[LNTerm],
        rules: impl Iterator<Item = &'a crate::rewriting::RRule<LNTerm>>,
    ) -> Result<Option<Self>, Error> {
        let Some(mut packet) = Packet::encode_local(
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
            let width = match kind {
                2 => arity,
                _ => 2,
            };
            packet
                .symbols
                .encode(f, width, |_| Some((arity, sort)))
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

    fn session_table(sig: &MaudeSig) -> ReductionTable {
        let theory = Arc::new(Theory::new(sig).unwrap());
        ReductionTable::new(&theory, sig).unwrap().unwrap()
    }

    /// The identity family for a multiset of `factors` distinct public names
    /// and one variable of sort Node, which makes the product kind-level.
    fn kind_level_identity(factors: u64) -> (FamilyCheck, Duration) {
        let sig = pair_maude_sig().merge(mset_maude_sig());
        let table = session_table(&sig);
        assert!(table.certified());
        let mut terms: Vec<LNTerm> = (0..factors).map(|i| pub_term(format!("p{i}"))).collect();
        terms.push(Term::Lit(Lit::Var(LVar::new("outside", LSort::Node, 0))));
        let query = f_app_ac(AcSym::Union, terms);
        let start = Instant::now();
        let verdict = table
            .check_variants(&query, &[Vec::new()], 1 << 16, 0, 0)
            .unwrap();
        (verdict, start.elapsed())
    }

    /// The class the certifier is proved to accept
    /// (`theoryCertify_subterm`): constructor-pattern rules whose
    /// results are subterms or constants. The builtin tables without an AC
    /// operator are of that shape, `verify` returning `true` included.
    #[test]
    fn constructor_pattern_tables_are_certified() {
        use crate::maude_sig::{
            asym_enc_maude_sig, hash_maude_sig, signature_maude_sig, sym_enc_maude_sig,
        };
        let sig = pair_maude_sig()
            .merge(sym_enc_maude_sig())
            .merge(asym_enc_maude_sig())
            .merge(signature_maude_sig())
            .merge(hash_maude_sig());
        assert!(!sig.rrules().is_empty());
        assert!(session_table(&sig).certified());
    }

    /// The table sends the rules of the file and of the rule-carrying
    /// builtins, and none of the rules of Diffie-Hellman, bilinear pairing
    /// and exclusive or, which the exports add, even where the file repeats
    /// one of them.
    #[test]
    fn the_session_table_holds_the_user_rules_alone() {
        use crate::builtin::{bp_rules, dh_rules, xor_rules};
        use crate::maude_sig::{bp_maude_sig, minimal_maude_sig, sym_enc_maude_sig, xor_maude_sig};
        let base = minimal_maude_sig(false).merge(sym_enc_maude_sig());
        let mut sig = base
            .clone()
            .merge(bp_maude_sig())
            .merge(xor_maude_sig())
            .refresh();
        assert!(sig.enable_dh);
        let users = user_rules(&sig);
        assert_eq!(users, base.rrules().into_iter().collect::<Vec<_>>());
        let builtin: BTreeSet<_> = dh_rules()
            .into_iter()
            .chain(bp_rules())
            .chain(xor_rules())
            .collect();
        assert!(users.iter().all(|rule| !builtin.contains(rule)));
        // A file equation that is a builtin rule is the builtin's.
        let (repeated, subterm) = xor_rules()
            .into_iter()
            .find_map(|rule| {
                let subterm = crate::subterm_rule::rrule_to_ctxt_st_rule(&rule)?;
                Some((rule, subterm))
            })
            .unwrap();
        sig.st_rules.insert(subterm);
        let sig = sig.refresh();
        assert!(sig.st_rules.iter().any(|r| r.to_rrule() == repeated));
        assert_eq!(user_rules(&sig), users);
        // The rows of the table are those of the user rules.
        let table = session_table(&sig);
        assert_eq!(table.packet.equations.len(), 2 * users.len());
        assert!(table.certified());
    }

    /// The closure test is not exponential in the width of a kind-level AC
    /// product: only the factors outside the sort of the operator are ever
    /// set aside. With the splits of the whole product it took 5.4 s and
    /// 1.43 GB on 20 factors and did not finish 129 under a 12 GB cap.
    #[test]
    fn kind_level_product_check_is_not_exponential() {
        let mut slow = Vec::new();
        for factors in [16, 20, 129] {
            let (verdict, elapsed) = kind_level_identity(factors);
            assert_eq!(verdict, FamilyCheck::Accepted, "{factors} factors");
            if elapsed > Duration::from_millis(100) {
                slow.push(format!("{factors} factors: {elapsed:?}"));
            }
        }
        assert!(slow.is_empty(), "closure test above 100 ms: {slow:?}");
    }

    /// Time the certifier on the builtin group tables, alone and with the
    /// rules of pairing, symmetric encryption, signatures and hashing. Each
    /// line is `table,verdict,fastest ms,median ms` over `CERTIFY_ROUNDS`
    /// calls (default 7); `CERTIFY_ONLY` selects one table by name.
    #[test]
    #[ignore = "timing"]
    fn certify_timing() {
        use crate::maude_sig::{
            bp_maude_sig, dh_maude_sig, hash_maude_sig, signature_maude_sig, sym_enc_maude_sig,
            xor_maude_sig,
        };
        let rounds: usize = std::env::var("CERTIFY_ROUNDS")
            .ok()
            .and_then(|r| r.parse().ok())
            .unwrap_or(7);
        let only = std::env::var("CERTIFY_ONLY").ok();
        let user = || {
            pair_maude_sig()
                .merge(sym_enc_maude_sig())
                .merge(signature_maude_sig())
                .merge(hash_maude_sig())
        };
        let groups = [
            ("dh", dh_maude_sig()),
            ("dh+bp", dh_maude_sig().merge(bp_maude_sig())),
            ("dh+xor", dh_maude_sig().merge(xor_maude_sig())),
            ("xor", xor_maude_sig()),
        ];
        for (name, group) in groups {
            for (suffix, sig) in [("", group.clone()), ("+user", group.merge(user()))] {
                let label = format!("{name}{suffix}");
                if only.as_ref().is_some_and(|o| *o != label) {
                    continue;
                }
                let table = session_table(&sig.refresh());
                let mut times = Vec::new();
                for _ in 0..rounds {
                    let start = Instant::now();
                    let verdict = table.certifies(CERTIFIER_DEPTH).unwrap();
                    times.push(start.elapsed());
                    assert_eq!(verdict, table.certified());
                }
                times.sort();
                eprintln!(
                    "{label},{},{:.2},{:.2}",
                    table.certified(),
                    times[0].as_secs_f64() * 1e3,
                    times[times.len() / 2].as_secs_f64() * 1e3
                );
            }
        }
    }
}

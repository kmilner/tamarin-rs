//! The words that cross to the algebra library and back, on the queries of
//! the differential fuzzer (`examples/audit_fuzz.rs`), for every signature
//! that fuzzer knows.
//!
//! The encoder of a request and the readers of a reply decide nothing. These
//! tests hold them to that: a request is read back as the terms it was built
//! from, a term sent through the library comes back as itself, requests that
//! differ in more than the names of their variables and constants have
//! different words, and the reader of a named family agrees with the reading
//! the library specifies.
use super::*;
use crate::function_symbols::{FunSym, NoEqSym};
use crate::lterm::{fresh_term, pub_term, HasFrees};
use crate::maude_sig::{dh_maude_sig, minimal_maude_sig, pair_maude_sig, xor_maude_sig, MaudeSig};
use tamarin_algebra_sys::tamarin_lean_apply_names;

#[path = "../../../examples/audit_fuzz.rs"]
mod audit_fuzz;

type Queries = Vec<(&'static str, MaudeSig, Vec<Vec<Equal<LNTerm>>>)>;

fn samples() -> Queries {
    audit_fuzz::imp::wire_samples(0x5eed, 120)
}

/// The theory description of `sig`.
fn theory(sig: &MaudeSig) -> Arc<Theory> {
    Arc::new(Theory::new(sig).expect("a signature the description expresses"))
}

fn var(name: &str, sort: LSort, idx: u64) -> LNTerm {
    Term::Lit(Lit::Var(LVar::new(name, sort, idx)))
}

/// A small generator for the choices these tests make themselves.
struct Rng(u64);
impl Rng {
    fn below(&mut self, n: usize) -> usize {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 >> 11) as usize % n.max(1)
    }
}

/// The term a request row stands for, read with the request's own tables.
/// Only these tests read a request: the library does, in production.
fn request_term(packet: &Packet, rows: &[&[u64]], node: u64) -> LNTerm {
    let row = rows[node as usize];
    match row {
        [0, id, sort] => {
            let v = packet
                .variables
                .get(*id)
                .expect("a variable row names a variable");
            assert_eq!(sort_word(v.sort), *sort);
            Term::Lit(Lit::Var(v))
        }
        [1, id, sort] => {
            let name = packet.names.get(*id).expect("a name row names a constant");
            assert_eq!(sort_word(sort_of_name(&name)), *sort);
            Term::Lit(Lit::Con(name))
        }
        [kind, id, children @ ..] => {
            let (f, _, _) = packet
                .symbols
                .decode(*kind, *id, false)
                .expect("an application row names an operator");
            assert!(matches!(
                (kind, f),
                (2, FunSym::NoEq(_)) | (3, FunSym::C(_)) | (4, FunSym::Ac(_))
            ));
            f_app(
                f,
                children
                    .iter()
                    .map(|child| request_term(packet, rows, *child))
                    .collect(),
            )
        }
        _ => panic!("a request row has a kind and an identifier"),
    }
}

fn request_rows(packet: &Packet) -> Vec<&[u64]> {
    packet.nodes.rows().collect()
}

#[test]
fn a_request_reads_back_as_the_terms_it_was_built_from() {
    let mut requests = 0;
    for (name, sig, queries) in samples() {
        for eqs in &queries {
            let terms: Vec<&LNTerm> = eqs.iter().flat_map(|e| [&e.lhs, &e.rhs]).collect();
            let packet = Packet::encode_total(&theory(&sig), terms.iter().copied())
                .unwrap()
                .unwrap_or_else(|| panic!("{name}: a query outside the module"));
            let rows = request_rows(&packet);
            assert_eq!(packet.equations.len(), terms.len());
            for (root, term) in packet.equations.iter().zip(&terms) {
                assert_eq!(&request_term(&packet, &rows, *root), *term, "{name}");
            }
            // Every row is the row of a subterm, and no row occurs twice.
            assert!(rows.iter().all(|row| !row.is_empty()));
            requests += 1;
        }
    }
    assert!(requests >= 1000, "{requests}");
}

#[test]
fn a_term_sent_through_the_matcher_comes_back_as_itself() {
    let probe = LVar::new("wireprobe", LSort::Msg, 0);
    let (mut sent, mut unsorted) = (0, 0);
    for (name, sig, queries) in samples() {
        for term in queries.iter().flatten().flat_map(|e| [&e.lhs, &e.rhs]) {
            let query = [Equal::new(Term::Lit(Lit::Var(probe)), term.clone())];
            let answers =
                match crate::lean_unification::match_modulo_attributes(&sig, &query, |v| {
                    *v == probe
                })
                .unwrap()
                {
                    Outcome::Complete(answers) => answers,
                    Outcome::Unsupported => panic!("{name}: a term outside the module"),
                };
            // A term without a sort is no image of the probe.
            if answers.is_empty() {
                unsorted += 1;
                continue;
            }
            assert_eq!(answers, vec![vec![(probe, term.clone())]], "{name}");
            sent += 1;
        }
    }
    assert!(sent >= 1500 && unsorted < sent, "{sent} {unsorted}");
}

fn words(sig: &MaudeSig, eqs: &[Equal<LNTerm>]) -> Box<[u64]> {
    Packet::encode_total(&theory(sig), eqs.iter().flat_map(|e| [&e.lhs, &e.rhs]))
        .unwrap()
        .expect("a query of the module")
        .request_words()
        .unwrap()
}

#[test]
fn requests_that_differ_have_different_words() {
    let sig = minimal_maude_sig(false)
        .merge(pair_maude_sig())
        .merge(dh_maude_sig())
        .merge(xor_maude_sig());
    let unary = |name: &str, t: LNTerm| {
        let sym = NoEqSym::new(
            name,
            1,
            crate::function_symbols::Privacy::Public,
            crate::function_symbols::Constructability::Constructor,
        );
        f_app(FunSym::NoEq(sym), vec![t])
    };
    let mut sig = sig;
    for name in ["wf", "wg"] {
        sig = sig.add_fun_sym(crate::function_symbols::UserDefinedSym::NoEqUser(
            NoEqSym::new(
                name,
                1,
                crate::function_symbols::Privacy::Public,
                crate::function_symbols::Constructability::Constructor,
            ),
        ));
    }
    let (a, b) = (pub_term("a"), pub_term("b"));
    let (x, y) = (var("x", LSort::Msg, 0), var("y", LSort::Msg, 0));
    let pair = |l: &LNTerm, r: &LNTerm| crate::builtin::pair(l.clone(), r.clone());
    let mult = |l: &LNTerm, r: &LNTerm| crate::builtin::mult(l.clone(), r.clone());
    let xor = |l: &LNTerm, r: &LNTerm| crate::builtin::xor(l.clone(), r.clone());
    let eq = |l: LNTerm, r: LNTerm| vec![Equal::new(l, r)];
    // Each line holds requests that say different things.
    let apart: Vec<Vec<Vec<Equal<LNTerm>>>> = vec![
        // One constant twice, or two constants.
        vec![eq(pair(&a, &a), x.clone()), eq(pair(&a, &b), x.clone())],
        // One variable twice, or two variables.
        vec![eq(pair(&x, &x), a.clone()), eq(pair(&x, &y), a.clone())],
        // A variable, a public name, a fresh name.
        vec![
            eq(x.clone(), y.clone()),
            eq(x.clone(), a.clone()),
            eq(x.clone(), fresh_term("a")),
        ],
        // The sort of a variable.
        vec![
            eq(x.clone(), var("y", LSort::Msg, 0)),
            eq(x.clone(), var("y", LSort::Fresh, 0)),
            eq(x.clone(), var("y", LSort::Pub, 0)),
            eq(x.clone(), var("y", LSort::Node, 0)),
        ],
        // A free and an associative-commutative operator.
        vec![eq(pair(&x, &y), a.clone()), eq(mult(&x, &y), a.clone())],
        // One associative-commutative operator twice, or two of them.
        vec![
            eq(mult(&x, &y), mult(&a, &b)),
            eq(mult(&x, &y), xor(&a, &b)),
        ],
        // The order of the arguments of a free operator.
        vec![
            eq(pair(&a, &x), pair(&x, &y)),
            eq(pair(&x, &a), pair(&x, &y)),
        ],
        // One operator twice, or two operators of one arity.
        vec![
            eq(unary("wf", x.clone()), unary("wf", a.clone())),
            eq(unary("wf", x.clone()), unary("wg", a.clone())),
        ],
        // One request over two free operators of one arity, or over two
        // associative-commutative operators: operators have the ids of the
        // theory.
        vec![
            eq(unary("wf", x.clone()), unary("wf", a.clone())),
            eq(unary("wg", x.clone()), unary("wg", a.clone())),
        ],
        vec![eq(mult(&x, &y), a.clone()), eq(xor(&x, &y), a.clone())],
        // The sides of the equations.
        vec![
            vec![
                Equal::new(x.clone(), a.clone()),
                Equal::new(y.clone(), b.clone()),
            ],
            vec![
                Equal::new(x.clone(), a.clone()),
                Equal::new(y.clone(), a.clone()),
            ],
            vec![
                Equal::new(x.clone(), y.clone()),
                Equal::new(a.clone(), b.clone()),
            ],
        ],
        // The number of operands of an associative-commutative operator.
        vec![
            eq(mult(&x, &y), a.clone()),
            eq(mult(&mult(&x, &y), &x), a.clone()),
            eq(mult(&mult(&x, &y), &y), a.clone()),
        ],
    ];
    for group in &apart {
        let all: Vec<_> = group.iter().map(|eqs| words(&sig, eqs)).collect();
        for (i, left) in all.iter().enumerate() {
            for right in &all[i + 1..] {
                assert_ne!(left, right, "{group:?}");
            }
        }
    }
    // The words do not depend on how a request names its variables and
    // constants: these requests say one thing.
    let same = [
        eq(pair(&x, &a), pair(&y, &x)),
        eq(pair(&y, &b), pair(&x, &y)),
        eq(
            pair(&var("k", LSort::Msg, 7), &a),
            pair(&var("k", LSort::Msg, 3), &var("k", LSort::Msg, 7)),
        ),
    ];
    assert!(same
        .iter()
        .all(|eqs| words(&sig, eqs) == words(&sig, &same[0])));
    // Requests over two theories have different words.
    let pairing = minimal_maude_sig(false).merge(pair_maude_sig());
    let request = eq(pair(&x, &a), pair(&y, &x));
    assert_ne!(words(&sig, &request), words(&pairing, &request));
    assert_eq!(
        words(
            &sig,
            &[
                Equal::new(x.clone(), a.clone()),
                Equal::new(y.clone(), b.clone())
            ]
        ),
        words(
            &sig,
            &[
                Equal::new(x.clone(), b.clone()),
                Equal::new(y.clone(), a.clone())
            ]
        )
    );
}

/// `term` with occurrence `at` of a variable (counted in the order of
/// `map_free`) replaced by `by`.
fn replace_occurrence(eqs: &[Equal<LNTerm>], at: usize, by: LVar) -> Vec<Equal<LNTerm>> {
    let mut seen = 0;
    let mut change = |v: LVar| {
        seen += 1;
        if seen - 1 == at {
            by
        } else {
            v
        }
    };
    eqs.iter()
        .map(|e| {
            let lhs = e.lhs.clone().map_free(&mut change);
            Equal::new(lhs, e.rhs.clone().map_free(&mut change))
        })
        .collect()
}

#[test]
fn a_changed_variable_changes_the_words_and_a_renaming_does_not() {
    let mut rng = Rng(0x9e3779b97f4a7c15);
    let (mut changed, mut renamed) = (0, 0);
    for (name, sig, queries) in samples() {
        for eqs in &queries {
            let mut occurrences = Vec::new();
            for e in eqs {
                e.lhs.for_each_free(&mut |v| occurrences.push(*v));
                e.rhs.for_each_free(&mut |v| occurrences.push(*v));
            }
            if occurrences.is_empty() {
                continue;
            }
            let before = words(&sig, eqs);
            // A consistent renaming to names that are new to the request.
            let apart: Vec<_> = eqs
                .iter()
                .map(|e| {
                    let mut far = |v: LVar| LVar::new(format!("{}w", v.name), v.sort, v.idx + 1000);
                    Equal::new(
                        e.lhs.clone().map_free(&mut far),
                        e.rhs.clone().map_free(&mut far),
                    )
                })
                .collect();
            // A renaming can reorder the operands of an AC operator, and with
            // them the rows of the request. Only an order it keeps is tested.
            let order = |eqs: &[Equal<LNTerm>]| {
                let mut out = Vec::new();
                for e in eqs {
                    e.lhs
                        .for_each_free(&mut |v| out.push((v.sort, v.idx % 1000)));
                    e.rhs
                        .for_each_free(&mut |v| out.push((v.sort, v.idx % 1000)));
                }
                out
            };
            if order(eqs) == order(&apart) {
                assert_eq!(before, words(&sig, &apart), "{name}: {eqs:?}");
                renamed += 1;
            }
            // One occurrence of a variable that occurs again becomes a
            // variable that is new to the request, or changes its sort.
            let at = rng.below(occurrences.len());
            let old = occurrences[at];
            if occurrences.iter().filter(|v| **v == old).count() > 1 {
                let new = LVar::new("wirenew", old.sort, 0);
                let after = replace_occurrence(eqs, at, new);
                // The new variable may sort to another position of an AC
                // operand list, so the comparison is on a request that reads
                // back as the changed one.
                if order(&after).len() == occurrences.len() {
                    assert_ne!(before, words(&sig, &after), "{name}: {eqs:?} at {at}");
                    changed += 1;
                }
            }
            let sort = if old.sort == LSort::Msg {
                LSort::Fresh
            } else {
                LSort::Msg
            };
            let resorted: Vec<_> = eqs
                .iter()
                .map(|e| {
                    let mut other = |v: LVar| if v == old { LVar { sort, ..v } } else { v };
                    Equal::new(
                        e.lhs.clone().map_free(&mut other),
                        e.rhs.clone().map_free(&mut other),
                    )
                })
                .collect();
            if let Some(packet) = Packet::encode_total(
                &theory(&sig),
                resorted.iter().flat_map(|e| [&e.lhs, &e.rhs]),
            )
            .unwrap()
            {
                assert_ne!(
                    before,
                    packet.request_words().unwrap(),
                    "{name}: {eqs:?} sort of {old:?}"
                );
                changed += 1;
            }
        }
    }
    assert!(changed >= 1000 && renamed >= 300, "{changed} {renamed}");
}

/// The reply of the library's own reading of a reply through tables, in words.
fn library_reading(tables: &[u64], nat: bool, reply: &[u64]) -> Vec<u64> {
    initialize().unwrap();
    let rows = |words| {
        rows_of(words)
            .map(|row| WordSlice::new(row.unwrap()))
            .collect::<Vec<_>>()
    };
    let (tables, reply) = (rows(tables), rows(reply));
    LEAN_THREAD.with(|_| {
        // SAFETY: the shim copies both sets of rows and MatchRows owns its output.
        let read = MatchRows::new(unsafe {
            tamarin_lean_apply_names(
                tables.as_ptr(),
                tables.len(),
                u8::from(nat),
                reply.as_ptr(),
                reply.len(),
            )
        })
        .unwrap();
        reply_words(&read).unwrap()
    })
}

/// The members of a family the library has read through tables. A row
/// `[key, sort, tokens]` binds the variable in row `key` of the request, and a
/// token of kind `5 + sort` is the variable with that sort, the index in its
/// second word and the name hint its third word identifies.
fn named_members(
    packet: &Packet,
    labels: &Labels,
    read: &[u64],
    nat: bool,
) -> Option<Substitutions> {
    let mut rows = rows_of(read);
    if rows.next()?? != [1] {
        return None;
    }
    let mut answers: Substitutions = Vec::new();
    for row in rows {
        let [key, expected, tokens @ ..] = row? else {
            answers.push(Vec::new());
            continue;
        };
        let var = packet.variables.get(*key)?;
        let (image, actual) = packet
            .read_image(tokens, nat, |kind, id, hint| {
                let Hint(name) = labels.hints.get(hint).ok_or(Error::InvalidVariable(id))?;
                let sort = sort(kind.checked_sub(5).ok_or(Error::InvalidVariable(id))?)?;
                Ok(LVar {
                    name,
                    sort,
                    idx: id,
                })
            })
            .ok()?;
        assert_eq!(sort_word(var.sort), *expected);
        assert!(actual.is_some_and(|s| subsort(s, var.sort)));
        answers.last_mut()?.push((var, image));
    }
    Some(answers)
}

/// The reader of this crate and the library's reading of the same reply
/// through the same tables: the same members, or no reading for either.
fn readings_agree(family: &Unifiers, labels: &Labels, tables: &[u64]) -> Option<Substitutions> {
    let ours = read_named(&family.packet, labels, &family.reply, tables, family.nat);
    let theirs = library_reading(tables, family.nat, &family.reply);
    let theirs = named_members(&family.packet, labels, &theirs, family.nat);
    assert_eq!(
        ours.as_ref().ok(),
        theirs.as_ref(),
        "{tables:?} {:?}",
        family.reply
    );
    theirs
}

#[test]
fn the_reader_of_a_named_family_agrees_with_the_library() {
    let mut rng = Rng(0x2545f4914f6cdd1d);
    let (mut read, mut unread, mut dropped, mut standing) = (0, 0, 0, 0);
    let mut bent_replies = 0;
    for (theory, sig, queries) in samples() {
        for eqs in queries.iter().take(60) {
            // A query whose family is large says nothing more about the reader.
            let Ok((Some(family), _)) = unify(&self::theory(&sig), eqs, None, 200_000) else {
                continue;
            };
            let Some((heads, ranges)) = shape(&family.reply) else {
                panic!("{theory}: a reply without a shape");
            };
            if ranges.is_empty() || ranges.len() > 64 {
                continue;
            }
            let mut labels = Labels::of(&family.packet).unwrap();
            // The default names: every member that is kept is read, binds
            // every variable of the request, and names its range above it.
            let defaults = name(&labels, &heads, &ranges, &[], family.nat, false, None).unwrap();
            let members = readings_agree(&family, &labels, &defaults)
                .unwrap_or_else(|| panic!("{theory}: {eqs:?} has no reading"));
            let top = family.packet.variables.values().iter().map(|v| v.idx).max();
            for member in &members {
                assert_eq!(member.len(), family.packet.variables.len());
                for (_, image) in member {
                    image.for_each_free(&mut |w| {
                        assert!(
                            w.name == "x" && top.is_none_or(|top| w.idx > top),
                            "{theory}: {w:?}"
                        );
                    });
                }
            }
            assert_eq!(members, family.named(None, None).unwrap());
            read += 1;
            // Proposals: names of the request, names that repeat, new names.
            for _ in 0..6 {
                let kept: Vec<_> = ranges
                    .iter()
                    .filter(|range| {
                        family.nat || !range.as_chunks::<2>().0.iter().any(|v| v[1] == 4)
                    })
                    .collect();
                dropped += ranges.len() - kept.len();
                let mode = rng.below(4);
                let proposal: Vec<Vec<u64>> = kept
                    .iter()
                    .map(|range| {
                        (0..range.len() / 2)
                            .flat_map(|at| {
                                let known = labels.words.len() / 2;
                                match (mode, rng.below(4)) {
                                    // The name of a request variable.
                                    (0 | 1, 0) if known > 0 => {
                                        let v = rng.below(known);
                                        [labels.words[2 * v], labels.words[2 * v + 1]]
                                    }
                                    // A name that may repeat.
                                    (1, _) => [0, 2000 + rng.below(3) as u64],
                                    _ => [rng.below(3) as u64, 3000 + at as u64],
                                }
                            })
                            .collect()
                    })
                    .collect();
                let tables =
                    name(&labels, &heads, &ranges, &proposal, family.nat, false, None).unwrap();
                match readings_agree(&family, &labels, &tables) {
                    Some(members) => {
                        standing += members
                            .iter()
                            .filter(|member| member.len() < family.packet.variables.len())
                            .count();
                        // No name of the range is a variable of the request.
                        let request: FxHashSet<LVar> =
                            family.packet.variables.values().iter().copied().collect();
                        for (_, image) in members.iter().flatten() {
                            image.for_each_free(&mut |w| assert!(!request.contains(w), "{theory}"));
                        }
                    }
                    None => unread += 1,
                }
                // Tables for other arms, or with an entry less, are read the
                // same way by both, whatever that is.
                let mut bent = tables.to_vec();
                if let Some(word) = bent.get_mut(rng.below(tables.len())) {
                    *word ^= 1 + rng.below(3) as u64;
                }
                if rows_of(&bent).all(|row| row.is_some()) {
                    readings_agree(&family, &labels, &bent);
                }
                // A reply that is not the unifier's has no specified
                // reading. Where the reader of this crate reads one, the
                // library reads the same.
                let mut other = family.reply.to_vec();
                let at = rng.below(other.len());
                other[at] ^= 1 + rng.below(3) as u64;
                if rows_of(&other).all(|row| row.is_some())
                    && let Ok(ours) =
                        read_named(&family.packet, &labels, &other, &tables, family.nat)
                {
                    let theirs = library_reading(&tables, family.nat, &other);
                    assert_eq!(
                        named_members(&family.packet, &labels, &theirs, family.nat),
                        Some(ours),
                        "{theory}: {other:?} through {tables:?}"
                    );
                    bent_replies += 1;
                }
            }
            let _ = labels.hints.intern(Hint("unused"));
        }
    }
    assert!(
        read >= 300 && standing > 0 && unread > 0 && bent_replies > 0,
        "{read} {standing} {unread} {dropped} {bent_replies}"
    );
}

#[test]
fn a_family_has_a_member_exactly_when_a_row_follows_its_status_row() {
    // The words of a reply: each row behind its length.
    assert_eq!(family_has_member(&[1, 1]), Some(false));
    assert_eq!(family_has_member(&[1, 1, 0]), Some(true));
    assert_eq!(family_has_member(&[1, 1, 0, 5, 0, 2, 0, 0, 2]), Some(true));
    // Two members without a binding: the unifiers of a request without variables.
    assert_eq!(family_has_member(&[1, 1, 0, 0]), Some(true));
    // The decline word, no row at all, a binding without a member, a row that
    // overruns the words.
    assert_eq!(family_has_member(&[1, 0]), None);
    assert_eq!(family_has_member(&[]), None);
    assert_eq!(family_has_member(&[0]), None);
    assert_eq!(family_has_member(&[1, 1, 5, 0, 2, 0, 0, 2]), None);
    assert_eq!(family_has_member(&[1, 1, 3, 0]), None);
    // The export agrees on a request with and without a unifier.
    let sig = minimal_maude_sig(false).merge(pair_maude_sig());
    let x = var("x", LSort::Msg, 0);
    for (eqs, member) in [
        (vec![Equal::new(x.clone(), pub_term("a"))], true),
        (vec![Equal::new(pub_term("b"), pub_term("a"))], false),
        (vec![Equal::new(pub_term("a"), pub_term("a"))], true),
    ] {
        let theory = theory(&sig);
        let family = unify(&theory, &eqs, None, 0).unwrap().0.unwrap();
        assert_eq!(family_has_member(&family.reply), Some(member));
        assert_eq!(!family.named(None, None).unwrap().is_empty(), member);
        assert_eq!(
            unify_exists(&theory, &eqs, None, 0).unwrap().0,
            Some(member)
        );
        // A stored family answers the existence question the same way.
        let memo = UnifyReplies::default();
        unify(&theory, &eqs, Some(&memo), 0).unwrap();
        assert_eq!(
            unify_exists(&theory, &eqs, Some(&memo), 0).unwrap(),
            (Some(member), true)
        );
    }
}

#[test]
fn a_reply_is_read_only_through_tables_that_name_all_of_it() {
    let sig = minimal_maude_sig(false).merge(pair_maude_sig());
    let (x, y, z) = (
        LVar::new("x", LSort::Msg, 4),
        LVar::new("y", LSort::Msg, 2),
        LVar::new("z", LSort::Msg, 2),
    );
    let term = |v: LVar| Term::Lit(Lit::Var(v));
    // x = <y, y> leaves z alone: its binding is a variable of its own.
    let eqs = vec![
        Equal::new(term(x), crate::builtin::pair(term(y), term(y))),
        Equal::new(term(z), term(z)),
    ];
    let family = unify(&theory(&sig), &eqs, None, 0).unwrap().0.unwrap();
    let labels = Labels::of(&family.packet).unwrap();
    let (heads, ranges) = shape(&family.reply).unwrap();
    assert_eq!(heads, [0, 2, 1, 2, 2, 2]);
    assert_eq!(ranges.len(), 1);
    // The default names: `x` above the request, in the order of first occurrence.
    let members = family.named(None, None).unwrap();
    let w = |idx| term(LVar::new("x", LSort::Msg, idx));
    assert_eq!(
        members,
        vec![vec![
            (x, crate::builtin::pair(w(5), w(5))),
            (y, w(5)),
            (z, w(6))
        ]]
    );
    // The name of z for the variable z is bound to: the binding is left out.
    let fresh = LVar::new("y", LSort::Msg, 9);
    let members = family.named(Some(&[vec![fresh, z]]), None).unwrap();
    assert_eq!(
        members,
        vec![vec![
            (x, crate::builtin::pair(term(fresh), term(fresh))),
            (y, term(fresh))
        ]]
    );
    // The name of y for the variable y is bound to has no reading, because x
    // mentions that variable too, and one name for both variables is not taken:
    // either way the family keeps its default names.
    for proposal in [vec![y, z], vec![fresh, fresh]] {
        assert_eq!(
            family.named(Some(&[proposal]), None).unwrap(),
            family.named(None, None).unwrap()
        );
    }
    // Stored tables are the words the export returned: a request it has seen
    // is read the same way, and another request is another entry.
    let memo = UnifyReplies::default();
    for _ in 0..2 {
        assert_eq!(
            family.named(None, Some(&memo)).unwrap(),
            family.named(None, None).unwrap()
        );
        assert_eq!(
            family.named(Some(&[vec![fresh, z]]), Some(&memo)).unwrap(),
            family.named(Some(&[vec![fresh, z]]), None).unwrap()
        );
    }
    assert_eq!(memo.names.lock().unwrap().len(), 2);
    // A table without a target for a variable, for an arm the reply lacks,
    // with other variables than the arm lists, or none at all.
    let tables = name(&labels, &heads, &ranges, &[], false, false, None).unwrap();
    assert!(read_named(&family.packet, &labels, &family.reply, &tables, false).is_ok());
    let mut short = tables[..tables.len() - 5].to_vec();
    let last = short.len() - (ranges[0].len() / 2 - 1) * 5 - 2;
    short[last] -= 5;
    for bad in [
        short,
        [&tables[..], &[1, 0][..]].concat(),
        tables
            .iter()
            .map(|w| if *w == 2 { 1 } else { *w })
            .collect(),
        vec![1, 1, heads.len() as u64, 0, 2, 1, 2, 2, 2],
        vec![1, 0],
    ] {
        assert!(
            read_named(&family.packet, &labels, &family.reply, &bad, false).is_err(),
            "{bad:?}"
        );
    }
}

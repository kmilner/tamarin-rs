use super::*;

fn union(factors: Vec<LNTerm>) -> LNTerm {
    f_app_ac(AcSym::Union, factors)
}

fn independent_variables(terms: &[LNTerm]) {
    let mut seen = BTreeSet::new();
    for term in terms {
        let Term::Lit(Lit::Var(var)) = term else {
            panic!("unexpected image {term:?}")
        };
        assert_eq!(var.sort, LSort::Msg);
        assert!(seen.insert(*var), "expected distinct parameters");
    }
}

#[derive(Clone, Copy)]
enum Observations {
    DoubleWithMarker,
    Coupled,
}

impl Observations {
    fn images(self, w: &LNTerm, summands: &[LNTerm]) -> [LNTerm; 2] {
        let mut first = summands.to_vec();
        match self {
            Self::DoubleWithMarker => [union(first), union(vec![w.clone(), w.clone(), out()])],
            Self::Coupled => {
                let mut second = first.clone();
                second.extend_from_slice(summands);
                first.push(w.clone());
                second.push(w.clone());
                [union(first), union(second)]
            }
        }
    }
}

#[test]
fn ac_coordinates_jointly_determine_variant_outputs() {
    for obs in [Observations::DoubleWithMarker, Observations::Coupled] {
        let w = msg_var("w", 10);
        let summands: Vec<_> = (0..4).map(|i| msg_var("s", i)).collect();
        let [left, right] = obs.images(&w, &summands);
        let rules = vec![(select(left, right), wrap(w))];
        let normalizer = theory(rules.clone());
        let h = handle(rules);
        let keys = [
            LVar::new("x", LSort::Msg, 40),
            LVar::new("y", LSort::Msg, 41),
        ];
        let [x, y] = keys.map(var_term);

        let mut shapes = vec![];
        for arm in h.variants(&select(x.clone(), y.clone())).unwrap() {
            assert!(arm.iter().all(|(k, _)| keys.contains(k)));
            let subst = LNSubstVFresh::from_list(arm).fresh_to_free_avoiding_vars(&keys);
            let images = [&x, &y].map(|t| apply_vterm(&subst, t.clone()));
            let term = select(images[0].clone(), images[1].clone());
            let output = normalizer.reduce(&term).unwrap();
            if matches!(images[0], Term::Lit(_)) {
                independent_variables(&images);
                assert_eq!(output, term);
                shapes.push(0);
                continue;
            }

            let Term::App(FunSym::NoEq(f), args) = &output else {
                panic!("expected wrapped capture")
            };
            assert_eq!(*f, symbol(b"wrap", 1));
            let [w] = args.as_ref() else {
                panic!("wrong wrapper arity")
            };
            let Term::App(FunSym::Ac(AcSym::Union), factors) = &images[0] else {
                panic!("expected AC input")
            };
            let mut summands: Vec<_> = factors.iter().filter(|t| *t != w).cloned().collect();
            shapes.push(summands.len());
            // With S the sum of these parameters, X=W+S and Y=W+2S
            // force W through 2X−Y even though neither input fixes W alone.
            assert_eq!(images, obs.images(w, &summands));
            summands.push(w.clone());
            independent_variables(&summands);
        }
        shapes.sort_unstable();
        assert_eq!(shapes, [0, 4]);
        assert_eq!(h.stats().var_count, 0);
    }
}

#[test]
fn one_symmetric_coordinate_does_not_determine_a_variant_output() {
    // The assignments (W,Z)=(a,b) and (b,a) have the same image W+Z.
    for width in [3, 4] {
        let w = msg_var("w", 10);
        let z = msg_var("z", 11);
        let h = handle(vec![(
            select(pattern(width), union(vec![w.clone(), z])),
            wrap(w),
        )]);
        assert!(matches!(
            h.variants(&select(msg_var("x", 20), msg_var("y", 21))),
            Err(MaudeError::UnsupportedOperation("variant generation"))
        ));
    }
}

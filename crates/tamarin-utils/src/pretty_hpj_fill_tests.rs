//! Small eager reference for the pre-suspension HughesPJ fill equations.
//! Kept recursive and used only on small trees, independently of the scheduler.
use super::*;

fn fill(g: bool, ds: &[Doc]) -> Doc {
    match ds {
        [] => Doc::Empty,
        [first, rest @ ..] => fill1(g, first.clone(), 0, rest),
    }
}

fn fill1(g: bool, p: Doc, k: isize, ys: &[Doc]) -> Doc {
    match p {
        Doc::Empty => mk_nest(k, fill(g, ys)),
        Doc::NoDoc => Doc::NoDoc,
        Doc::Nest(n, p) => nest_(n, fill1(g, (*p).clone(), k - n, ys)),
        Doc::TextBeside(s, w, p) => {
            text_beside_(s, w, fill_nb(g, (*p).clone(), k - w as isize, ys))
        }
        Doc::NilAbove(p) => nil_above_(above_nest((*p).clone(), false, k, fill(g, ys))),
        Doc::Union(p, q) => mk_union(
            fill1(g, (*p).clone(), k, ys),
            above_nest((*q).clone(), false, k, fill(g, ys)),
        ),
        Doc::LazyUnion(p, q) => mk_union(
            fill1(g, (*p).clone(), k, ys),
            above_nest((*q.force()).clone(), false, k, fill(g, ys)),
        ),
        Doc::Suspend(_) | Doc::Deferred(_) => panic!("reference input must be eager"),
    }
}

fn fill_nb(g: bool, p: Doc, k: isize, mut ys: &[Doc]) -> Doc {
    match p {
        Doc::Nest(_, p) => fill_nb(g, (*p).clone(), k, ys),
        Doc::Empty => {
            while matches!(ys.first(), Some(Doc::Empty)) {
                ys = &ys[1..];
            }
            let Some((first, rest)) = ys.split_first() else {
                return Doc::Empty;
            };
            mk_union(
                nil_beside(
                    g,
                    fill1(
                        g,
                        elide_nest(one_liner(first.clone())),
                        k - isize::from(g),
                        rest,
                    ),
                ),
                nil_above_nest(false, k, fill(g, ys)),
            )
        }
        other => fill1(g, other, k, ys),
    }
}

fn sample(seed: &mut u64, depth: usize) -> (Doc, Doc) {
    *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
    let n = *seed;
    let kind = if depth == 0 { n % 3 } else { n % 13 };
    if kind < 3 {
        let d = match kind {
            0 => Doc::Empty,
            1 => Doc::text("x"),
            _ => Doc::text("<long>"),
        };
        return (d.clone(), d);
    }
    // Some leaves build fills larger than the direct-suffix budget so outer
    // combinators also receive suspended construction, not just eager trees.
    let count = if depth == 1 && n.is_multiple_of(5) {
        20
    } else {
        n / 13 % 4 + 1
    };
    let (actual, expected): (Vec<_>, Vec<_>) = (0..count).map(|_| sample(seed, depth - 1)).unzip();
    let combine = |mut ds: Vec<Doc>| match kind {
        5 => sep(ds),
        7 => hsep(ds),
        8 => hcat(ds),
        9 => vcat(ds),
        12 => text_beside_(Rc::from("p"), 1, nest_(2, ds.remove(0))),
        10 => ds.remove(0).nest((n / 79 % 7) as isize - 2),
        _ => ds.remove(0).beside_sp(vcat(ds)),
    };
    match kind {
        3 => (fsep(actual), fill(true, &expected)),
        4 | 6 => (fcat(actual), fill(false, &expected)),
        _ => (combine(actual), combine(expected)),
    }
}

#[test]
fn composed_fills_match_eager_reference_in_all_render_modes() {
    let mut seed = 42;
    for i in 0..1000 {
        let (actual, expected) = sample(&mut seed, 4);
        assert_eq!(
            actual.one_line_render(),
            expected.one_line_render(),
            "one-line sample {i}"
        );
        for (width, ribbon) in [(0, 0), (1, 1), (8, 5), (20, 13), (100, 67)] {
            assert_eq!(
                actual.clone().render_with(width, ribbon),
                expected.clone().render_with(width, ribbon),
                "sample {i}, {width}/{ribbon}"
            );
            assert_eq!(
                actual.clone().render_at(width, ribbon, 3),
                expected.clone().render_at(width, ribbon, 3),
                "inline sample {i}, {width}/{ribbon}"
            );
        }
    }
}

#[test]
fn singleton_normalization_is_preserved_under_composition() {
    for token in ["longword".to_owned(), "w".repeat(120)] {
        let raw = text_beside_(Rc::from("p"), 1, nest_(2, Doc::text(&token)));
        for gap in [false, true] {
            let actual = super::fill(gap, vec![raw.clone()]);
            let expected = fill(gap, std::slice::from_ref(&raw));
            for width in [1, 8, 110] {
                for prefix in [Doc::Empty, Doc::text("x")] {
                    let context =
                        |d| fsep(vec![fsep(vec![prefix.clone(), d]), Doc::text("x")]).nest(3);
                    assert_eq!(
                        context(actual.clone()).render_with(width, width),
                        context(expected.clone()).render_with(width, width)
                    );
                }
            }
        }
    }
}

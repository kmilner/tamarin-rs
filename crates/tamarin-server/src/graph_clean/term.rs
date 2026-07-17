//! A minimal term model, sufficient to drive abbreviation (naming + expansion
//! rendering). It is an independent design; it renders tamarin-like surface
//! syntax for the common term shapes observed in legend expansions
//! (variables, constants, pairs, `exp`/`mult`/`union`/`xor`, function apps).
//!
//! Faithful reproduction of the solver's full term pretty-printer (all operators,
//! precedence, line wrapping) is out of scope — see BEHAVIOR.md §3a/§5. The
//! covered shapes are byte-tested against captured legend rows.

use std::collections::HashMap;

/// A term. Variable kinds mirror tamarin's surface decorations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    /// Fresh variable, rendered `~name`.
    Fresh(String),
    /// Public variable, rendered `$name`.
    Pub(String),
    /// Bare message/temporal variable, rendered `name`.
    Msg(String),
    /// Public constant, rendered `'name'`.
    Const(String),
    /// Right-nested pair; rendered flattened as `<a, b, c>`.
    Pair(Box<Term>, Box<Term>),
    /// `exp(base, e)`, rendered `base^e` (the exponent carries its own parens
    /// when it is a product/sum).
    Exp(Box<Term>, Box<Term>),
    /// An associative-commutative operator rendered infix inside parentheses:
    /// `mult`→`*`, `union`→`++`, `xor`→`⊕`. `func` is the logical name used for
    /// the abbreviation prefix.
    Ac { func: String, op: String, args: Vec<Term> },
    /// Ordinary prefix application `func(a, b, …)`.
    App { func: String, args: Vec<Term> },
}

impl Term {
    // ---- convenience constructors --------------------------------------

    pub fn fresh(n: &str) -> Term {
        Term::Fresh(n.to_string())
    }
    pub fn pubv(n: &str) -> Term {
        Term::Pub(n.to_string())
    }
    pub fn msg(n: &str) -> Term {
        Term::Msg(n.to_string())
    }
    pub fn cst(n: &str) -> Term {
        Term::Const(n.to_string())
    }
    pub fn app(func: &str, args: Vec<Term>) -> Term {
        Term::App { func: func.to_string(), args }
    }
    pub fn exp(base: Term, e: Term) -> Term {
        Term::Exp(Box::new(base), Box::new(e))
    }
    pub fn mult(args: Vec<Term>) -> Term {
        Term::Ac { func: "mult".into(), op: "*".into(), args }
    }
    pub fn union(args: Vec<Term>) -> Term {
        Term::Ac { func: "union".into(), op: "++".into(), args }
    }
    pub fn xor(args: Vec<Term>) -> Term {
        Term::Ac { func: "xor".into(), op: "\u{2295}".into(), args }
    }
    /// Build a flattened tuple `<a, b, c>` from ≥1 elements (right-nested pairs).
    pub fn tuple(mut elems: Vec<Term>) -> Term {
        let last = elems.pop().expect("tuple needs ≥1 element");
        elems.into_iter().rev().fold(last, |acc, e| Term::Pair(Box::new(e), Box::new(acc)))
    }

    // ---- naming --------------------------------------------------------

    /// The root symbol's *name*, whose first two letters give the abbreviation
    /// prefix (see [`super::abbrev::prefix_for_symbol`]).
    pub fn root_symbol_name(&self) -> String {
        match self {
            Term::Fresh(n) | Term::Pub(n) | Term::Msg(n) | Term::Const(n) => n.clone(),
            Term::Pair(..) => "pair".to_string(),
            Term::Exp(..) => "exp".to_string(),
            Term::Ac { func, .. } => func.clone(),
            Term::App { func, .. } => func.clone(),
        }
    }

    /// Leaf terms (variables/constants) are atomic; everything else is not.
    pub fn is_atomic(&self) -> bool {
        matches!(self, Term::Fresh(_) | Term::Pub(_) | Term::Msg(_) | Term::Const(_))
    }

    /// A tuple / pair `<a, b, …>`. Tuples are never abbreviated (BEHAVIOR.md §5c,
    /// observed: 0 of 97 538 legend entries is a top-level tuple, and a live probe
    /// left a length-18 tuple occurring twice un-abbreviated).
    pub fn is_tuple(&self) -> bool {
        matches!(self, Term::Pair(..))
    }

    /// Number of Unicode scalar values in the fully-expanded surface rendering —
    /// the measure that gates abbreviation (BEHAVIOR.md §5c). This counts the
    /// surface decorations too (`'…'` quotes, `~`/`$` sigils), matching the
    /// observed boundary (`'12345678'` = 10 chars is abbreviated, `'1234567'` = 9
    /// is not).
    pub fn render_len(&self) -> usize {
        self.render_full().chars().count()
    }

    /// Number of term nodes (atoms + operators) — a simple complexity measure.
    pub fn size(&self) -> usize {
        match self {
            Term::Fresh(_) | Term::Pub(_) | Term::Msg(_) | Term::Const(_) => 1,
            Term::Pair(a, b) => 1 + a.size() + b.size(),
            Term::Exp(a, b) => 1 + a.size() + b.size(),
            Term::Ac { args, .. } | Term::App { args, .. } => {
                1 + args.iter().map(Term::size).sum::<usize>()
            }
        }
    }

    /// Visit this term and every sub-term (pre-order).
    pub fn for_each_subterm(&self, f: &mut dyn FnMut(&Term)) {
        f(self);
        match self {
            Term::Pair(a, b) | Term::Exp(a, b) => {
                a.for_each_subterm(f);
                b.for_each_subterm(f);
            }
            Term::Ac { args, .. } | Term::App { args, .. } => {
                for a in args {
                    a.for_each_subterm(f);
                }
            }
            _ => {}
        }
    }

    // ---- rendering -----------------------------------------------------

    /// Fully-expanded surface rendering (no abbreviations). Used as the dedup key.
    pub fn render_full(&self) -> String {
        self.render_with(&|t| t.render_full())
    }

    /// Render this term's expansion, replacing any *registered* sub-term (present
    /// in `table`, keyed by its full rendering) with its abbreviation name. The
    /// top-level term itself is always rendered structurally.
    pub fn render_abbrev(&self, table: &HashMap<String, String>) -> String {
        self.render_with(&|t| t.substitute(table))
    }

    /// Rendering used for children during abbreviation: a registered term yields
    /// its name, otherwise it renders structurally (recursing on its children).
    fn substitute(&self, table: &HashMap<String, String>) -> String {
        if let Some(name) = table.get(&self.render_full()) {
            return name.clone();
        }
        self.render_with(&|t| t.substitute(table))
    }

    /// Structural rendering; `child` renders each immediate sub-term.
    fn render_with(&self, child: &dyn Fn(&Term) -> String) -> String {
        match self {
            Term::Fresh(n) => format!("~{}", n),
            Term::Pub(n) => format!("${}", n),
            Term::Msg(n) => n.clone(),
            Term::Const(n) => format!("'{}'", n),
            Term::Pair(..) => {
                let elems = self.pair_spine();
                let parts: Vec<String> = elems.iter().map(|t| child(t)).collect();
                format!("<{}>", parts.join(", "))
            }
            Term::Exp(base, e) => format!("{}^{}", child(base), child(e)),
            Term::Ac { op, args, .. } => {
                let parts: Vec<String> = args.iter().map(|t| child(t)).collect();
                format!("({})", parts.join(op))
            }
            Term::App { func, args } => {
                let parts: Vec<String> = args.iter().map(|t| child(t)).collect();
                format!("{}({})", func, parts.join(", "))
            }
        }
    }

    /// Flatten a right-nested pair into its element spine.
    fn pair_spine(&self) -> Vec<&Term> {
        let mut out = Vec::new();
        let mut cur = self;
        while let Term::Pair(a, b) = cur {
            out.push(a.as_ref());
            cur = b.as_ref();
        }
        out.push(cur);
        out
    }
}

//! Explicit continuations for the recursive term grammar.
//!
//! Expressions, application arguments, and grouping all use this loop. Argument-list
//! policies preserve unary tuple arguments, structural-mode strict lists, and
//! resolved applications' trailing commas and delimiter diagnostics.
use super::*;

pub(super) enum TermHead {
    Value(Term),
    Group,
    List(TermList),
}
pub(super) enum TermList {
    Tuple(&'static str),
    App {
        id: String,
        res: Option<ArityRes>,
        head: Pos,
        opening: Pos,
    },
    Diff {
        head: Pos,
        opening: Pos,
    },
    Alg {
        id: String,
        res: Option<ArityRes>,
        head: Pos,
    },
}
impl TermList {
    fn close(&self) -> &'static str {
        match self {
            Self::Tuple(c) => c,
            Self::Alg { .. } => "}",
            _ => ")",
        }
    }
    fn tuple(&self) -> bool {
        matches!(
            self,
            Self::Tuple(_)
                | Self::Alg { .. }
                | Self::App {
                    res: Some(ArityRes::NoEq {
                        opts: FunOptions { arity: 1, .. }
                    }),
                    ..
                }
        )
    }
    fn opening(&self) -> Option<Pos> {
        match self {
            Self::Diff { opening, .. } => Some(*opening),
            Self::App {
                opening,
                res: Some(_),
                ..
            } if !self.tuple() => Some(*opening),
            _ => None,
        }
    }
}
pub(super) enum Frame {
    Expr(usize),
    Infix(usize),
    Join(BinOp, Term, usize),
    Group,
    ListStart(TermList),
    ListNext(TermList, Vec<Term>, bool),
    Alg(String, Option<ArityRes>, Pos, Term),
}
impl Parser<'_> {
    pub(super) fn iterative_term(&mut self, eqn: bool, min: usize) -> Result<Term, ParseError> {
        let closers = self.list_closers.len();
        let mut frames = std::mem::take(&mut self.term_frames);
        let mut value = None;
        let mut next = Some(Frame::Expr(min));
        let result = (|| {
            while let Some(frame) = next.take().or_else(|| frames.pop()) {
                match frame {
                    Frame::Expr(min) => match self.term_head(eqn)? {
                        TermHead::Value(v) => {
                            value = Some(v);
                            next = Some(Frame::Infix(min));
                        }
                        TermHead::Group => {
                            frames.push(Frame::Infix(min));
                            frames.push(Frame::Group);
                            next = Some(Frame::Expr(0));
                        }
                        TermHead::List(list) => {
                            frames.push(Frame::Infix(min));
                            next = Some(Frame::ListStart(list));
                        }
                    },
                    Frame::Infix(min) => {
                        if let Some((rank, op)) = self.term_operator(eqn, min) {
                            frames.push(Frame::Join(op, value.take().unwrap(), min));
                            next = Some(Frame::Expr(rank + 1));
                        } else {
                            self.skip_ws();
                        }
                    }
                    Frame::Join(op, left, min) => {
                        let right = value.take().unwrap();
                        value = Some(Self::bin_op_term(op, left, right));
                        next = Some(Frame::Infix(min));
                    }
                    Frame::Group => {
                        self.require_punct(")")?;
                    }
                    Frame::ListStart(list) => {
                        if list.opening().is_some() {
                            self.list_closers.push(')');
                        }
                        if !list.tuple() && self.try_punct(list.close()) {
                            value = self.finish_term_list(list, Vec::new(), eqn, &mut frames)?;
                        } else {
                            self.skip_ws();
                            let missing = list.opening().is_some()
                                && self.at_unclosed_list_boundary(list.close());
                            frames.push(Frame::ListNext(list, Vec::new(), missing));
                            next = Some(Frame::Expr(0));
                        }
                    }
                    Frame::ListNext(list, mut args, _) => {
                        args.push(value.take().unwrap());
                        if self.try_punct(",")
                            && !(list.opening().is_some() && self.peek_punct(list.close()))
                        {
                            self.skip_ws();
                            let missing = list.opening().is_some()
                                && self.at_unclosed_list_boundary(list.close());
                            frames.push(Frame::ListNext(list, args, missing));
                            next = Some(Frame::Expr(0));
                        } else {
                            if !self.try_punct(list.close()) {
                                let mut error = if list.opening().is_some()
                                    || matches!(list, TermList::Tuple(">"))
                                {
                                    self.err_expect(format!("\",\", \"{}\"", list.close()))
                                } else {
                                    self.err_expect(format!("\"{}\"", list.close()))
                                };
                                if let Some(opening) = list.opening() {
                                    self.skip_ws();
                                    if self.at_unclosed_list_boundary(list.close()) {
                                        Self::mark_unclosed_delimiter(
                                            &mut error,
                                            opening,
                                            list.close(),
                                        );
                                    }
                                }
                                return Err(error);
                            }
                            value = self.finish_term_list(list, args, eqn, &mut frames)?;
                        }
                    }
                    Frame::Alg(id, res, head, left) => {
                        let right = value.take().unwrap();
                        value = Some(match res {
                            Some(ArityRes::Ac) => Self::bin_op_term(
                                BinOp::AcFct(tamarin_term::intern::intern_str(&id)),
                                left,
                                right,
                            ),
                            Some(
                                r @ ArityRes::NoEq {
                                    opts: FunOptions { arity: 2, .. },
                                },
                            ) if r.is_dh_exp(&id) => Self::bin_op_term(BinOp::Exp, left, right),
                            Some(ArityRes::NoEq { opts }) if opts.arity != 2 => {
                                return Err(self.term_arity_error(&id, opts.arity, 2, head));
                            }
                            _ => Term::AlgApp(id, Box::new(left), Box::new(right)),
                        });
                    }
                }
            }
            Ok(value.take().unwrap())
        })();
        self.list_closers.truncate(closers);
        let result = result.map_err(|mut error| {
            for frame in frames.iter().rev() {
                if let Frame::ListNext(list, _, true) = frame
                    && let Some(opening) = list.opening()
                {
                    Self::mark_unclosed_delimiter(&mut error, opening, list.close());
                }
            }
            error
        });
        frames.clear();
        self.term_frames = frames;
        result
    }

    fn term_operator(&mut self, eqn: bool, min: usize) -> Option<(usize, BinOp)> {
        // AC operators bind tighter and win if a user spelling overlaps a
        // builtin. Most signatures have none; avoid refcount traffic then.
        if !self.state.ac_fun_syms.is_empty() {
            let symbols = Arc::clone(&self.state.ac_fun_syms);
            for (i, name) in symbols.iter().enumerate() {
                let rank = 6 + i;
                if rank >= min && self.try_kw(name) {
                    return Some((rank, BinOp::AcFct(tamarin_term::intern::intern_str(name))));
                }
            }
        }
        for (rank, enabled, op) in [
            (1, self.state.sig_enable_mset, BinOp::Union),
            (2, self.state.sig_enable_nat, BinOp::NatPlus),
            (3, self.state.sig_enable_xor, BinOp::Xor),
            (4, self.state.sig_enable_dh, BinOp::Mult),
            (5, self.state.sig_enable_dh, BinOp::Exp),
        ] {
            if rank >= min && enabled && !eqn && self.try_term_operator(op).is_some() {
                return Some((rank, op));
            }
        }
        None
    }

    fn term_arity_error(&self, id: &str, declared: usize, used: usize, head: Pos) -> ParseError {
        self.semantic_error(
            ParseErrorKind::WrongFunctionArity {
                name: diagnostic_lexeme(id),
                declared,
                used,
            },
            head,
            id.len(),
        )
    }
    fn finish_term_list(
        &mut self,
        list: TermList,
        args: Vec<Term>,
        eqn: bool,
        frames: &mut Vec<Frame>,
    ) -> Result<Option<Term>, ParseError> {
        if list.opening().is_some() {
            self.list_closers.pop();
        }
        let tuple = |mut args: Vec<Term>| {
            if args.len() == 1 {
                args.pop().unwrap()
            } else {
                Term::Pair(args)
            }
        };
        let term = match list {
            TermList::Tuple(_) => tuple(args),
            TermList::App {
                id,
                res:
                    Some(ArityRes::NoEq {
                        opts: FunOptions { arity: 1, .. },
                    }),
                ..
            } => Term::App(id, vec![tuple(args)]),
            TermList::App {
                id,
                res: Some(ArityRes::Ac),
                ..
            } => Self::ac_prefix_app(id, args),
            TermList::App { id, res, head, .. } => {
                if let Some(ArityRes::NoEq { opts }) = res
                    && args.len() != opts.arity
                {
                    return Err(self.term_arity_error(&id, opts.arity, args.len(), head));
                }
                if res.is_some_and(|r| r.is_dh_exp(&id)) {
                    let mut it = args.into_iter();
                    Self::bin_op_term(BinOp::Exp, it.next().unwrap(), it.next().unwrap())
                } else {
                    Term::App(id, args)
                }
            }
            TermList::Diff { head, .. } => {
                if args.len() != 2 {
                    return Err(self.term_arity_error("diff", 2, args.len(), head));
                }
                if eqn || !self.state.enable_diff {
                    let why = if eqn {
                        IllegalDiffReason::InEquation
                    } else {
                        IllegalDiffReason::DiffModeDisabled
                    };
                    return Err(self.semantic_error(
                        ParseErrorKind::IllegalDiffOperator(why),
                        head,
                        4,
                    ));
                }
                let mut it = args.into_iter();
                Term::Diff(Box::new(it.next().unwrap()), Box::new(it.next().unwrap()))
            }
            TermList::Alg { id, res, head } => {
                frames.push(Frame::Alg(id, res, head, tuple(args)));
                frames.push(Frame::Expr(usize::MAX));
                return Ok(None);
            }
        };
        Ok(Some(term))
    }
}

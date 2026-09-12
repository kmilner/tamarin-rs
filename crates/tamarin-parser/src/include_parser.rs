// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Guarded include expansion with file-local cursors and conditionals.
//! Signature state and a single source-ordered output vector span all files.

use super::*;

pub(super) struct ConditionalState {
    pub branches: Vec<(bool, bool)>,
    pub active: bool,
}
impl ConditionalState {
    pub fn new() -> Self {
        Self {
            branches: Vec::new(),
            active: true,
        }
    }
}

struct IncludedSource {
    identity: PathBuf,
    content: String,
    resolved: PathBuf,
    staged: Option<PathBuf>,
}

impl Parser<'_> {
    /// Expand an already-consumed `#include` keyword and its following path into the
    /// sequence of theory items declared in the referenced file.
    ///
    /// HS `include` (Theory/Text/Parser.hs:323-343):
    /// ```haskell
    /// include inFile0 thy = do
    ///    filepath <- try (symbol "#include") *> filePathParser
    ///    st <- getState
    ///    let (thy', st') = unsafePerformIO (parseFileWState st ... filepath)
    ///    _ <- putState st'
    ///    addItems inFile0 $ set (sigpMaudeSig . thySignature) (sig st') thy'
    ///  where
    ///    filePathParser = case takeDirectory <$> inFile0 of
    ///        Nothing -> doubleQuoted filePath
    ///        Just s  -> (s </>) <$> doubleQuoted filePath
    /// ```
    /// The double-quoted path is consumed here; the path is
    /// resolved against `self.base_dir` (HS `takeDirectory inFile0`); the file
    /// is read and its header-less fragment parsed by [`Self::expand_include`]
    /// — which threads parser state both ways (signature / known funcs / flags),
    /// matching HS's `getState`/`putState` round-trip and `sig st'` merge.
    pub(super) fn expand_include(&mut self, items: &mut Vec<TheoryItem>) -> Result<(), ParseError> {
        self.in_context(ParseContext::Include, |root| {
            let mut active = tamarin_utils::FastSet::default();
            if let Some(path) = &root.source_file {
                active.insert(path.canonicalize().unwrap_or_else(|_| path.clone()));
            }
            root.include_file(items, &mut active)
        })
    }

    fn include_file(
        &mut self,
        items: &mut Vec<TheoryItem>,
        active: &mut tamarin_utils::FastSet<PathBuf>,
    ) -> Result<(), ParseError> {
        tamarin_utils::stack::ensure_sufficient_stack(|| {
            let IncludedSource {
                identity,
                content,
                resolved,
                staged,
            } = self.read_include(active)?;
            let mut parser = Parser::new(&content, &[], self.is_diff);
            parser.base_dir = resolved.parent().map(|p| p.to_path_buf());
            parser.source_file = Some(resolved);
            parser.staged_file = staged;
            self.swap_include_state(&mut parser);
            active.insert(identity.clone());
            let result = (|| {
                let mut conditionals = ConditionalState::new();
                while parser.theory_items_chunk(&mut conditionals, items)? {
                    parser.include_file(items, active)?;
                }
                parser.skip_ws();
                if !parser.lx.is_eof() {
                    return Err(parser
                        .err_expect_here("end of included file")
                        .with_context(ParseContext::Include));
                }
                Ok(())
            })();
            active.remove(&identity);
            let result = parser
                .lx
                .finish(result)
                .map_err(|error| parser.with_arity_site(error));
            // Return the deepest signature state on success and failure alike.
            self.swap_include_state(&mut parser);
            result.map_err(|error| {
                error.with_source_text(
                    parser.source_file.as_ref().unwrap().display().to_string(),
                    content,
                )
            })
        })
    }

    fn read_include(
        &mut self,
        active: &tamarin_utils::FastSet<PathBuf>,
    ) -> Result<IncludedSource, ParseError> {
        self.skip_ws();
        let path_start = self.save();
        let (raw_path, path_span) = self.string_literal_spanned()?;

        // HS `filePathParser`: resolve relative to the including file's dir when
        // we know it (`Just s -> s </> path`), else verbatim (`Nothing`).
        let resolved: PathBuf = match &self.base_dir {
            Some(dir) => dir.join(&raw_path),
            None => PathBuf::from(&raw_path),
        };
        let staged = if PathBuf::from(&raw_path).is_absolute() {
            None
        } else {
            self.staged_file.as_ref().map(|source| {
                source
                    .parent()
                    .unwrap_or_else(|| std::path::Path::new(""))
                    .join(&raw_path)
            })
        };
        self.state.input_aliases.push(InputAlias {
            physical: resolved.clone(),
            staged: staged.clone(),
        });

        let identity = resolved.canonicalize().unwrap_or_else(|_| resolved.clone());
        if active.contains(&identity) {
            return Err(ParseError::custom(path_start, "circular include".into())
                .with_context(ParseContext::Include));
        }
        let content = std::fs::read_to_string(&resolved).map_err(|e| {
            self.semantic_error(
                ParseErrorKind::IncludeIo {
                    path: resolved.display().to_string(),
                    reason: e.to_string(),
                },
                path_start,
                path_span.len(),
            )
        })?;

        Ok(IncludedSource {
            identity,
            content,
            resolved,
            staged,
        })
    }
}

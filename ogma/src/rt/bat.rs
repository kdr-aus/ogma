//! Batch processing of definitions and expressions.
//!
//! This module provides some structure around batch processing, supplying reporting structures
//! and evaluation semantics.
use crate::prelude::*;
use crate::Mutex;
use ::libs::{
    divvy::*,
    rayon::prelude::*,
    serde::{Deserialize, Serialize},
    serde_json,
};
use ast::Location;
use lang::parse::{Directive, File, Item};
use std::{
    fs, io,
    iter::*,
    path::Path,
    sync::Arc,
    time::{Duration, Instant},
};

/// A batch to process.
pub struct Batch {
    /// The items in the batch to process.
    ///
    /// If parsing a file to create the [`BatchItem`]s, use [`parse_file`].
    pub items: Vec<BatchItem>,
    /// Process the _expressions_ in a parallel fashion.
    pub parallelise: bool,
    /// Stop processing upon encountering an error in one of the items.
    pub fail_fast: bool,
}

/// An item to process.
#[derive(Debug, PartialEq, Eq)]
pub struct BatchItem {
    /// A description of the item.
    pub comment: Option<String>,
    /// The file where this item was defined (used for error reporting).
    pub file: Arc<Path>,
    /// The line where this item was defined (used for error reporting).
    pub line: u16,

    code: String,
    ty: ItemType,
}

impl BatchItem {
    /// Return the expression or definition code.
    pub fn code(&self) -> &str {
        &self.code
    }

    /// The type this item was recognised as.
    pub fn ty(&self) -> ItemType {
        self.ty
    }
}

/// The outcome of an item.
#[derive(Debug, PartialEq, Eq)]
pub enum Outcome {
    /// The item parsed, checked, and evaluated successfully.
    Success,
    /// The item failed parsing, checking, or evaluating.
    Failed(Error),
    /// The item was yet to be processed.
    Outstanding,
    /// Processing was cancelled before the item could be processed.
    Cancelled,
}

impl<T> From<Result<T>> for Outcome {
    fn from(r: Result<T>) -> Self {
        r.map(|_| Outcome::Success).unwrap_or_else(Outcome::Failed)
    }
}

/// The type of this item.
#[derive(Debug, PartialEq, Eq, Copy, Clone, Serialize, Deserialize)]
pub enum ItemType {
    /// An expression.
    Expr,
    /// An implementation definition.
    Impl,
    /// A type definition.
    Type,
}

// ------ Parsing --------------------------------------------------------------
/// Parse a string of items.
///
/// This can be thought of as parsing a code file, with multiple items separated by a blank line.
pub fn parse_str(s: &str, loc: Location) -> Result<Batch> {
    let File {
        doc: _,
        directives,
        types,
        impls,
        exprs,
    } = lang::parse::file(s, loc)?;

    let items = types
        .into_iter()
        .map(|(_, Item { doc, code, line })| BatchItem {
            code,
            comment: doc,
            file: Path::new(".").into(),
            line,
            ty: ItemType::Type,
        })
        .chain(
            impls
                .into_iter()
                .map(|(_, Item { doc, code, line })| BatchItem {
                    code,
                    comment: doc,
                    file: Path::new(".").into(),
                    line,
                    ty: ItemType::Impl,
                }),
        )
        .chain(exprs.into_iter().map(|Item { doc, code, line }| BatchItem {
            code,
            comment: doc,
            file: Path::new(".").into(),
            line,
            ty: ItemType::Expr,
        }))
        .collect();

    Ok(Batch {
        parallelise: !directives.iter().any(|x| x == &Directive::NoParallelise),
        fail_fast: directives.iter().any(|x| x == &Directive::FailFast),
        items,
    })
}

/// Parse the contents of a file into a list of [`BatchItem`]s.
///
/// # Security
/// Filepath should be validated to only be inside working directory.
pub fn parse_file(f: impl AsRef<Path>) -> io::Result<Result<Batch>> {
    let f = Arc::from(f.as_ref());
    let s = fs::read_to_string(&f)?;
    let loc = Location::File(Arc::clone(&f), 0);
    let mut v = parse_str(&s, loc);
    if let Ok(v) = &mut v {
        v.items.iter_mut().for_each(|x| x.file = Arc::clone(&f));
    }
    Ok(v)
}

// ------ Processing -----------------------------------------------------------

/// Process a [`Batch`].
///
/// Processing will process each item, doing definitions in a sequential order, and expressions in
/// either parallel or sequential order based on the `parallelise` field.
/// If `fail_fast` is `true`, the first time an error is encountered, subsequent processing will
/// halt. Items that do not get processed will have an outcome of `Outstanding`. Each `process`
/// call uses a passed in [`Definitions`] which it _owns_ meaning it should not interfere
/// with REPL or other batch instances (store caching is still shared).
///
/// # Cancellation
/// The cancellation switch found in `cx` is checked _before each item is processed_. It is not
/// checked whilst processing an item.
///
/// # Progress Reporting
/// Upon finishing processing an item, a progress report is sent (through `cx.progress`:
/// [`ProgressTx::send`]). This report serialises [`BatchProgress`], which is a status report _of
/// each item to be processed_. [`BatchProgress`] serialises to `json`, and the processor on the
/// other side should _deserialise_ json back to a [`BatchProgress`] to provide detailed progress
/// reporting.
///
/// [`Definitions`]: crate::Definitions
/// [`ProgressTx::send`]: divvy::ProgressTx::send
pub fn process(
    batch: &Batch,
    root: &Path,
    wd: &Path,
    progress: &ProgressTx,
    mut definitions: Definitions,
) -> Vec<(Outcome, Duration)> {
    let ff = batch.fail_fast;
    let parallelise = batch.parallelise;
    let items = &batch.items;

    // build a reporting state. this is necessary for HTML reporting as the callback can not
    // capture environment
    let mut results: Vec<_> = repeat_with(|| (Outcome::Outstanding, Duration::default()))
        .take(items.len())
        .collect();
    let reporter = Mutex::new(
        items
            .iter()
            .map(|b| BatchItemProgress {
                comment: b.comment.clone(),
                file: b.file.display().to_string(),
                line: b.line,
                ty: b.ty,
                status: OutcomeProgress::Outstanding,
            })
            .collect(),
    );

    // anything that is not an expression must be processed in sequence first
    let (defs, xprs) =
        items
            .iter()
            .enumerate()
            .fold((Vec::new(), Vec::new()), |(mut d, mut x), b| {
                if b.1.ty == ItemType::Expr {
                    x.push(b);
                } else {
                    d.push(b);
                };
                (d, x)
            });

    let prog = progress;
    let failure = Switch::off();
    let sw_if_fail = |o: &_| {
        if matches!(o, Outcome::Failed(_)) {
            failure.flip_on();
        }
    };
    let stop = || ff && (prog.cancelled() || failure.get());

    // process the defs (in order)
    for (idx, def) in defs {
        if stop() {
            break;
        }

        let instant = Instant::now();
        let loc = Location::File(def.file.clone(), def.line);
        let r =
            lang::defs::process_definition(&def.code, loc, def.comment.clone(), &mut definitions)
                .into();
        report_progress(prog, &reporter, idx, &r);
        sw_if_fail(&r);
        results[idx] = (r, instant.elapsed());
    }

    // process the expressions
    let f = |(idx, expr): (_, &BatchItem)| {
        let instant = Instant::now();
        if stop() {
            return (
                idx,
                if prog.cancelled() {
                    Outcome::Cancelled
                } else {
                    Outcome::Outstanding
                },
                instant.elapsed(),
            );
        }

        let loc = Location::File(expr.file.clone(), expr.line);
        let r = rt::process_expression((), expr.code.as_str(), loc, &definitions, root, wd).into();
        report_progress(prog, &reporter, idx, &r);
        sw_if_fail(&r);
        (idx, r, instant.elapsed())
    };
    let r: Vec<_> = if parallelise {
        xprs.into_par_iter().map(f).collect()
    } else {
        xprs.into_iter().map(f).collect()
    };
    // write out results
    for (idx, o, t) in r {
        results[idx] = (o, t);
    }

    if prog.cancelled() {
        // transform any outstanding to cancelled
        results
            .iter_mut()
            .filter(|x| matches!(x, (Outcome::Outstanding, _)))
            .for_each(|x| x.0 = Outcome::Cancelled);
    }

    results
}

// ------ Progress -------------------------------------------------------------
type ProgressResults = Mutex<BatchProgress>;
/// Serialisable progress of a [`Batch`].
pub type BatchProgress = Vec<BatchItemProgress>;

/// Serialisable progress of a [`BatchItem`].
///
/// Each item has various metadata, along with a status which reports on the item's processing
/// status.
#[derive(Serialize, Deserialize)]
pub struct BatchItemProgress {
    /// Matches [`BatchItem::comment`].
    pub comment: Option<String>,
    /// Matches [`BatchItem::file`].
    pub file: String,
    /// Matches [`BatchItem::line`].
    pub line: u16,
    /// Matches [`BatchItem::ty`].
    pub ty: ItemType,
    /// The status of the item.
    pub status: OutcomeProgress,
}

/// The serialisable version of [`Outcome`].
#[derive(Serialize, Deserialize)]
pub enum OutcomeProgress {
    /// Matches [`Outcome::Success`].
    Success,
    /// Matches [`Outcome::Failed`].
    Failed,
    /// Matches [`Outcome::Outstanding`].
    Outstanding,
    /// Matches [`Outcome::Cancelled`].
    Cancelled,
}

impl From<&Outcome> for OutcomeProgress {
    fn from(o: &Outcome) -> OutcomeProgress {
        match o {
            Outcome::Success => OutcomeProgress::Success,
            Outcome::Failed(_) => OutcomeProgress::Failed,
            Outcome::Outstanding => OutcomeProgress::Outstanding,
            Outcome::Cancelled => OutcomeProgress::Cancelled,
        }
    }
}

fn report_progress(
    progress: &ProgressTx,
    results: &ProgressResults,
    item_idx: usize,
    outcome: &Outcome,
) {
    let results = &mut *results.lock();
    if let Some(x) = results.get_mut(item_idx) {
        x.status = outcome.into();
    }
    let ser = serde_json::to_string(results).unwrap_or_default();
    progress.send(None, ser);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parsing_str() {
        let src = "def foo () { bar }

# Use comments!
foo | + 5

def-ty Zog { x:Num }";

        let x = parse_str(src, Location::Shell).unwrap().items;

        assert_eq!(
            x,
            vec![
                BatchItem {
                    comment: None,
                    file: Path::new(".").into(),
                    line: 6,
                    code: "def-ty Zog { x:Num }".to_string(),
                    ty: ItemType::Type
                },
                BatchItem {
                    comment: None,
                    file: Path::new(".").into(),
                    code: "def foo () { bar }".to_string(),
                    ty: ItemType::Impl,
                    line: 1,
                },
                BatchItem {
                    file: Path::new(".").into(),
                    code: "foo | + 5".to_string(),
                    ty: ItemType::Expr,
                    comment: Some("Use comments!".to_string()),
                    line: 4,
                },
            ]
        );
    }
}

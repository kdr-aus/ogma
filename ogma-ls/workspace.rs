use super::{completion::*, *};
use ::libs::{parking_lot::RwLock, rustc_hash::FxHashMap as HashMap};
use itertools::Itertools;
use lsp_types::{TextDocumentContentChangeEvent, Url};
use ogma::{
    common::err::help_as_error,
    lang::{ast::Tag, Definitions},
};
use std::{collections::VecDeque, sync::Arc};

type Version = i32;
type ChgList = Vec<TextDocumentContentChangeEvent>;

/// Document header string: `name` [_node-type_]
pub(crate) fn doc_header(name: &str, ty: NodeType) -> String {
    format!("`{}` [_{}_]", name, ty.as_str())
}

pub(crate) fn add_doc_body(mut header: String, body: &str) -> String {
    header.push_str("\n\n```\n");
    header.push_str(body);
    header.push_str("\n```");
    header
}

// ###### WORKSPACE ############################################################
/// A shareable workspace that provides file storage and completion functionality.
pub struct Workspace {
    files: Arc<RwLock<HashMap<Url, File>>>,
    /// The [`Definitions`], stored in a thread-safe manner.
    pub defs: Arc<RwLock<Definitions>>,
}

impl Workspace {
    /// Create a new workspace.
    pub fn init() -> Self {
        Self {
            files: Arc::new(RwLock::new(HashMap::default())),
            defs: Arc::new(RwLock::new(Definitions::new())),
        }
    }

    pub(crate) fn add_file(&self, url: Url, file: File) {
        self.files.write().insert(url, file);
    }

    pub(crate) fn add_file_changes(&self, url: &Url, version: Version, changes: ChgList) {
        if let Some(file) = self.files.write().get_mut(url) {
            file.add_changes(version, changes);
        }
    }

    /// Extract the definition portion from a line number of a file.
    ///
    /// It strips doc comments, but includes text beyond the line number.
    /// Returns the text and the _starting line index_.
    pub(crate) fn get_def_text(&self, url: &Url, line: usize) -> Option<(usize, String)> {
        let l = self.files.read();
        let file = l.get(url)?;
        let lines = file.text.lines().enumerate().collect::<Vec<_>>();
        let pre = lines
            .iter()
            .take(line)
            .rev()
            .take_while(|(_, s)| !s.trim().is_empty())
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .skip_while(|(_, s)| s.starts_with('#'));
        let mut f = true;
        let post = lines.iter().skip(line).take_while(|(_, s)| {
            let x = f || !s.trim().is_empty();
            f = false;
            x
        });

        let (i, s) = pre
            .chain(post)
            .fold((None, String::new()), |(mut i, mut s), (ii, ss)| {
                i = i.or(Some(*ii));
                s.push_str(ss);
                s.push('\n');
                (i, s)
            });

        Some((i.unwrap_or(0), s))
    }

    /// Parse the ogma input.
    ///
    /// If it can parse successfully, a [`Complete`] trait object is returned (no matter the type
    /// of expression. If it cannot parse, [`Incomplete`] is returned, which can still provide some
    /// information as to what is expected.
    pub fn parse(&self, input: &str) -> Result<Box<dyn Complete>, Incomplete> {
        use ogma::lang::parse::ParseSuccess::*;
        ogma::lang::parse::parse(input, &self.defs.read())
            .map(|x| match x {
                Impl(x) => Box::new(x) as Box<_>,
                Ty(x) => Box::new(x) as Box<_>,
                Expr(x) => Box::new(x) as Box<_>,
            })
            .map_err(|(err, exp)| Incomplete { err, exp })
    }

    pub(crate) fn impl_help_string(&self, name: &Tag) -> Option<String> {
        self.defs
            .read()
            .impls()
            .get_help_all(name.str())
            .as_ref()
            .map(ToString::to_string)
    }

    pub(crate) fn type_help_string(&self, name: &Tag) -> Option<String> {
        self.defs
            .read()
            .types()
            .get_using_tag(name)
            .ok()
            .map(|t| help_as_error(&t.help(), None).to_string())
    }

    /// Akin to `def --load`. Loads _all_ current files into the definitions list.
    ///
    /// Runs a clearing of all definitions before loading.
    ///
    /// > This loads what the contents of what is in the virtual file map. If using through a
    /// > terminal where `def --load` can be called it is recommneded to just share the
    /// > `Definitions` file and not use this method.
    pub(crate) fn def_load(&self) {
        let files = self.files.read();
        let defs = &mut self.defs.write();
        defs.clear(false);
        for (url, file) in files.iter() {
            let path = url
                .to_file_path()
                .unwrap_or_else(|_| std::path::PathBuf::from(url.path()));
            defs.add_from_str(&file.text, &path).ok();
        }
    }

    pub(crate) fn impls(&self) -> Vec<Def> {
        let t = NodeType::Command;
        let x = self.defs.read();
        let impls = x.impls();

        impls
            .iter()
            .map(|x| x.name)
            .dedup()
            .map(|name| {
                let helpstr = impls
                    .get_help_all(name)
                    .expect("help should exist")
                    .to_string();
                let doc = Some(add_doc_body(doc_header(name, t), &helpstr));
                Def {
                    name: name.to_string(),
                    kind: Kind::Impl,
                    doc,
                }
            })
            .collect()
    }

    pub(crate) fn types(&self) -> Vec<Def> {
        let t = NodeType::Type;
        self.defs
            .read()
            .types()
            .help_iter()
            .map(|(name, help)| {
                let helpstr = help_as_error(&help, None).to_string();
                let doc = Some(add_doc_body(doc_header(name, t), &helpstr));
                Def {
                    name: name.to_string(),
                    kind: Kind::Type,
                    doc,
                }
            })
            .collect()
    }
}

impl Clone for Workspace {
    fn clone(&self) -> Self {
        Self {
            files: Arc::clone(&self.files),
            defs: Arc::clone(&self.defs),
        }
    }
}

// ###### FILE #################################################################

pub struct File {
    text: String,
    version: Version,
    pending: VecDeque<Change>,
}

impl File {
    pub fn new(text: String, version: Version) -> Self {
        Self {
            text,
            version,
            pending: VecDeque::new(),
        }
    }

    pub fn add_changes(&mut self, version: Version, changes: ChgList) {
        let i = self
            .pending
            .iter()
            .position(|c| c.version >= version)
            .unwrap_or(self.pending.len());

        self.pending.insert(i, Change { version, changes });

        self.apply_pending();
    }

    fn apply_pending(&mut self) {
        let text = &mut self.text;

        while let Some(chg) = self.pending.pop_front() {
            if chg.version < self.version {
                continue;
            } else if chg.version > self.version + 1 {
                self.pending.push_front(chg);
                break;
            }

            self.version = chg.version;
            apply_changes(text, &chg.changes);
        }

        debug!(
            "applied doc edits. VERSION: {}; TEXT: {:?}",
            self.version, text
        );
    }
}

struct Change {
    version: Version,
    changes: ChgList,
}

fn apply_changes(text: &mut String, chgs: &[TextDocumentContentChangeEvent]) {
    for chg in chgs {
        let range = chg
            .range
            .map(|r| lsp_range_to_range(text, r))
            .unwrap_or(0..text.len());
        text.replace_range(range, &chg.text);
    }
}

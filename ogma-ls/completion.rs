//! Ogma completions handling.

use crate::Workspace as Wsp;
use ogma::lang::ast::{self, Tag};
use std::path::Path;

// ###### DEF ##################################################################
/// A completion item definition.
pub struct Def {
    /// The completion value.
    pub name: String,
    /// The completion kind.
    pub kind: Kind,
    /// Associated documentation.
    pub doc: Option<String>,
}

/// The completion kind.
pub enum Kind {
    /// The item is an implementation (command/method/function).
    Impl,
    /// The item is a type (class).
    Type,
    /// The item is a file.
    File,
    /// This item is a directory.
    Dir,
    /// This item is a literal.
    Lit,
}

// ###### CMPL #################################################################
bitflags::bitflags! {
    struct Items: u8 {
        const IMPLS = 0b00000001;
        const TYPES = 0b00000010;
        const PATHS = 0b00000100;
        const SPEC_LIT = 0b00001000;
    }
}

/// Construct a list of completions (stored as [`Def`]s).
///
/// Uses a source line (truncated to the cursor
/// position) and the current working directory. This working directory can be the parent of the
/// file being edited.
pub fn get(wsp: &Wsp, truncated_line: &str, working_dir: Option<&Path>) -> Option<Vec<Def>> {
    let line = truncated_line;
    wsp.parse(line)
        .map(|c| complete_completions(wsp, line, working_dir, c.as_ref()))
        .unwrap_or_else(|inc| incomplete_completions(wsp, line, working_dir, inc))
}

fn complete_completions(
    wsp: &Wsp,
    line: &str,
    working_dir: Option<&Path>,
    complete: &dyn Complete,
) -> Option<Vec<Def>> {
    use NodeType::*;

    let node = complete.node_at_pos(line.len().saturating_sub(1))?;

    match node.ty {
        Command => Some(cmpls(wsp, line, working_dir, Items::IMPLS)),
        Type | TyParameter => Some(cmpls(wsp, line, working_dir, Items::TYPES)),
        Ident => Some(cmpls(
            wsp,
            line,
            working_dir,
            Items::IMPLS | Items::PATHS | Items::SPEC_LIT,
        )),
        Pound => Some(cmpls(wsp, line, working_dir, Items::SPEC_LIT)),
        Num | Var | Flag | Parameter | Field | Variant => None,
    }
}

fn incomplete_completions(
    wsp: &Wsp,
    line: &str,
    working_dir: Option<&Path>,
    incomplete: Incomplete,
) -> Option<Vec<Def>> {
    use ogma::lang::parse::Expecting as Exp;

    match incomplete.exp {
        Exp::Impl => Some(cmpls(wsp, line, working_dir, Items::IMPLS)),
        Exp::Type => Some(cmpls(wsp, line, working_dir, Items::TYPES)),
        Exp::Term => Some(cmpls(
            wsp,
            line,
            working_dir,
            Items::IMPLS | Items::PATHS | Items::SPEC_LIT,
        )),
        Exp::SpecLiteral => Some(cmpls(wsp, line, working_dir, Items::SPEC_LIT)),
        Exp::None => None,
    }
}

fn cmpls(wsp: &Wsp, line: &str, working_dir: Option<&Path>, items: Items) -> Vec<Def> {
    let mut r = Vec::new();

    match working_dir {
        Some(p) if items.contains(Items::PATHS) => r.extend(path_completions(p, line)),
        _ => (),
    }

    if items.contains(Items::IMPLS) {
        r.extend(wsp.impls().into_iter());
    }

    if items.contains(Items::TYPES) {
        r.extend(wsp.types().into_iter());
    }

    if items.contains(Items::SPEC_LIT) {
        r.extend(spec_literal_completions());
    }

    r
}

fn path_completions(working_dir: &Path, line: &str) -> Vec<Def> {
    let mut entries = Vec::new();
    let path = working_dir.join(path_component(line));

    let path = if path.is_dir() && path.exists() {
        Some(&*path)
    } else {
        path.parent()
    };

    if let Some(dir) = path.and_then(|x| x.read_dir().ok()) {
        entries.extend(dir.filter_map(|x| x.ok()).map(|x| {
            let kind = if x.file_type().map(|x| x.is_dir()).unwrap_or_default() {
                Kind::Dir
            } else {
                Kind::File
            };

            Def {
                name: x.file_name().to_string_lossy().into(),
                kind,
                doc: None,
            }
        }));
    }

    entries
}

fn path_component(line: &str) -> &str {
    // see if there is a unmatched char
    let esc = "\"'";
    let mut mat_ch = None;
    let mut i = 0;
    for (idx, ch) in line.char_indices() {
        match mat_ch {
            Some(c) if c == ch => mat_ch = None,
            None if esc.contains(ch) => {
                i = idx;
                mat_ch = Some(ch);
            }
            _ => (),
        }
    }

    if mat_ch.is_none() {
        i = 0;
        for (idx, ch) in line.char_indices().rev() {
            if ch == ' ' {
                break;
            }
            i = idx;
        }
    }

    &line[i..]
}

fn spec_literal_completions() -> impl Iterator<Item = Def> {
    use std::iter::*;
    once(Def {
        name: "#t".into(),
        kind: Kind::Lit,
        doc: Some("`true` boolean value".into()),
    })
    .chain(once(Def {
        name: "#f".into(),
        kind: Kind::Lit,
        doc: Some("`false` boolean value".into()),
    }))
    .chain(once(Def {
        name: "#i".into(),
        kind: Kind::Lit,
        doc: Some("the block's input value".into()),
    }))
}

// ###### PARSING ##############################################################
/// Parsing completed successfully.
pub trait Complete {
    /// Obtain a node at the byte position.
    fn node_at_pos(&self, position_utf8: usize) -> Option<Node>;

    /// Appends the leaves of the AST node to the buffer.
    ///
    /// This can be used at the root node to get a flat list of leaves.
    /// A buffer is used to require only a single allocation.
    ///
    /// The order should be implemented in the same way as it is defined in source (depth-first)
    /// but this is not a guarantee; consider sorting by the tag start to achieve source order.
    fn append_leaves(&self, buf: Vec<Node>) -> Vec<Node>;
}

/// Parsing did not complete successfully.
pub struct Incomplete {
    /// The `ogma` error that was returned.
    pub err: ogma::Error,
    /// The expectation of the node if parsing failed.
    pub exp: ogma::lang::parse::Expecting,
}

/// A rudimentary AST node.
pub struct Node {
    /// The soure slice tag.
    pub tag: Tag,
    /// The language server defined kind (possibly different to the `ogma` kind).
    pub ty: NodeType,
}

/// The AST node kind.
#[derive(Debug, PartialEq, Copy, Clone)]
pub enum NodeType {
    /// An implementation/command/operation.
    Command,
    /// A type.
    Type,
    /// An identifier.
    ///
    /// This is something that _doesn't_ parse as a number, variable, etc.
    Ident,
    /// A number.
    Num,
    /// A variable.
    Var,
    /// A special literal.
    Pound,
    /// A flag.
    Flag,
    /// An implementation parameter.
    Parameter,
    /// A defined type field.
    Field,
    /// A defined type variant.
    Variant,
    /// A defined type - type parameter.
    TyParameter,
}

impl NodeType {
    pub(crate) fn as_str(&self) -> &'static str {
        use NodeType::*;
        match self {
            Command => "command",
            Type => "type",
            Ident => "ident",
            Num => "number",
            Pound => "spec-literal",
            Var => "variable",
            Flag => "flag",
            Parameter => "parameter",
            Field => "field",
            Variant => "variant",
            TyParameter => "type parameter",
        }
    }
}

impl Node {
    pub(crate) fn new(tag: Tag, ty: NodeType) -> Self {
        Self { tag, ty }
    }
}

fn is_node(tag: &Tag, pos: usize, ty: NodeType) -> Option<Node> {
    if tag.range().contains(&pos) {
        Some(Node::new(tag.clone(), ty))
    } else {
        None
    }
}

use NodeType as NT;

impl Complete for ast::DefinitionImpl {
    fn node_at_pos(&self, pos: usize) -> Option<Node> {
        if pos < self.name.start {
            // use the previous tag to the `def` command
            let mut tag = self.name.clone();
            tag.start = 0;
            tag.end = self.name.start.saturating_sub(1);
            return Some(Node::new(tag, NT::Command));
        }

        is_node(&self.name, pos, NT::Command)
            .or_else(|| self.in_ty.as_ref().and_then(|t| is_node(t, pos, NT::Type)))
            .or_else(|| self.expr.node_at_pos(pos))
            .or_else(|| self.params.iter().find_map(|param| param.node_at_pos(pos)))
    }

    fn append_leaves(&self, mut buf: Vec<Node>) -> Vec<Node> {
        buf.push(Node::new(
            {
                let mut tag = self.name.clone();
                tag.start = 0;
                tag.end = self.name.start.saturating_sub(1);
                tag
            },
            NT::Command,
        ));

        buf.push(Node::new(self.name.clone(), NT::Command));

        if let Some(inty) = &self.in_ty {
            buf.push(Node::new(inty.clone(), NT::Type));
        }

        for param in &self.params {
            buf = param.append_leaves(buf);
        }

        self.expr.append_leaves(buf)
    }
}

impl Complete for ast::DefinitionType {
    fn node_at_pos(&self, pos: usize) -> Option<Node> {
        use ast::TypeVariant::*;

        if pos < self.name.start {
            // use the previous tag to the `def-ty` command
            let mut tag = self.name.clone();
            tag.start = 0;
            tag.end = self.name.start.saturating_sub(1);
            return Some(Node::new(tag, NT::Command));
        }

        is_node(&self.name, pos, NT::Type).or_else(|| match &self.ty {
            Sum(variants) => variants.iter().find_map(|v| v.node_at_pos(pos)),
            Product(fields) => fields.iter().find_map(|f| f.node_at_pos(pos)),
        })
    }

    fn append_leaves(&self, mut buf: Vec<Node>) -> Vec<Node> {
        use ast::TypeVariant::*;

        buf.push(Node::new(
            {
                let mut tag = self.name.clone();
                tag.start = 0;
                tag.end = self.name.start.saturating_sub(1);
                tag
            },
            NT::Command,
        ));

        buf.push(Node::new(self.name.clone(), NT::Type));

        match &self.ty {
            Sum(variants) => {
                for variant in variants {
                    buf = variant.append_leaves(buf);
                }
            }
            Product(fields) => {
                for field in fields {
                    buf = field.append_leaves(buf);
                }
            }
        }

        buf
    }
}

impl Complete for ast::Expression {
    fn node_at_pos(&self, pos: usize) -> Option<Node> {
        if !self.tag.range().contains(&pos) {
            None
        } else {
            self.blocks.iter().find_map(|blk| blk.node_at_pos(pos))
        }
    }

    fn append_leaves(&self, mut buf: Vec<Node>) -> Vec<Node> {
        for block in &self.blocks {
            buf = block.append_leaves(buf);
        }
        buf
    }
}

impl Complete for ast::Block {
    fn node_at_pos(&self, pos: usize) -> Option<Node> {
        if !self.block_tag().range().contains(&pos) {
            return None;
        }

        is_node(&self.op(), pos, NT::Command)
            .or_else(|| self.terms().iter().find_map(|term| term.node_at_pos(pos)))
    }

    fn append_leaves(&self, mut buf: Vec<Node>) -> Vec<Node> {
        buf.push(Node::new(self.op().into_owned(), NT::Command));
        for term in self.terms().iter() {
            buf = term.append_leaves(buf);
        }
        buf
    }
}

impl Complete for ast::Term {
    fn node_at_pos(&self, pos: usize) -> Option<Node> {
        use ast::Term::*;
        match self {
            Arg(arg) => arg.node_at_pos(pos),
            Flag(tag) => is_node(tag, pos, NT::Flag),
        }
    }

    fn append_leaves(&self, mut buf: Vec<Node>) -> Vec<Node> {
        use ast::Term::*;
        match self {
            Arg(arg) => arg.append_leaves(buf),
            Flag(tag) => {
                buf.push(Node::new(tag.clone(), NT::Flag));
                buf
            }
        }
    }
}

impl Complete for ast::Argument {
    fn node_at_pos(&self, pos: usize) -> Option<Node> {
        use ast::Argument::*;
        match self {
            Ident(t) => is_node(t, pos, NT::Ident),
            Num(_, t) => is_node(t, pos, NT::Num),
            Var(t) => is_node(t, pos, NT::Var),
            Pound(_, t) => is_node(t, pos, NT::Pound),
            Expr(expr) => expr.node_at_pos(pos),
        }
    }

    fn append_leaves(&self, mut buf: Vec<Node>) -> Vec<Node> {
        use ast::Argument::*;
        let (t, nt) = match self {
            Ident(t) => (t, NT::Ident),
            Num(_, t) => (t, NT::Num),
            Var(t) => (t, NT::Var),
            Pound(_, t) => (t, NT::Pound),
            Expr(expr) => return expr.append_leaves(buf),
        };
        buf.push(Node::new(t.clone(), nt));
        buf
    }
}

impl Complete for ast::Parameter {
    fn node_at_pos(&self, pos: usize) -> Option<Node> {
        is_node(&self.ident, pos, NT::Parameter)
    }

    fn append_leaves(&self, mut buf: Vec<Node>) -> Vec<Node> {
        buf.push(Node::new(self.ident.clone(), NT::Parameter));
        buf
    }
}

impl Complete for ast::Field {
    fn node_at_pos(&self, pos: usize) -> Option<Node> {
        is_node(&self.name, pos, NT::Field)
            .or_else(|| is_node(&self.ty, pos, NT::Type))
            .or_else(|| {
                self.params
                    .iter()
                    .find_map(|p| is_node(p, pos, NT::TyParameter))
            })
    }

    fn append_leaves(&self, mut buf: Vec<Node>) -> Vec<Node> {
        buf.push(Node::new(self.name.clone(), NT::Field));
        buf.push(Node::new(self.ty.clone(), NT::Type));
        for param in &self.params {
            buf.push(Node::new(param.clone(), NT::TyParameter));
        }
        buf
    }
}

impl Complete for ast::Variant {
    fn node_at_pos(&self, pos: usize) -> Option<Node> {
        is_node(&self.name, pos, NT::Variant).or_else(|| {
            self.fields
                .as_ref()
                .and_then(|fields| fields.iter().find_map(|field| field.node_at_pos(pos)))
        })
    }

    fn append_leaves(&self, mut buf: Vec<Node>) -> Vec<Node> {
        buf.push(Node::new(self.name.clone(), NT::Variant));
        if let Some(fields) = &self.fields {
            for field in fields {
                buf = field.append_leaves(buf);
            }
        }
        buf
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn path_component_tests() {
        let f = path_component;
        assert_eq!(f("path/to/something"), "path/to/something");
        assert_eq!(f("foo-bar | in richi"), "richi");
        assert_eq!(
            f(r#"foo-bar | in path/to something/richi"#),
            "something/richi"
        );
        assert_eq!(
            f(r#"foo-bar | in "path/to something/richi"#),
            "\"path/to something/richi"
        );
        assert_eq!(
            f(r#"foo-bar | in 'path/to something/richi"#),
            "'path/to something/richi"
        );
        assert_eq!(f(r#"foo-bar | in "foo bar" foo/bar"#), "foo/bar");
        assert_eq!(f(r#"foo-bar | in "foo 'bar" "foo bar"#), "\"foo bar");
        assert_eq!(f(r#"foo-bar | in "foo bar" foo bar"#), "bar");
        assert_eq!(f(r#"foo-bar | in "foo bar" foo\bar"#), "foo\\bar");
        assert_eq!(
            f(r#"foo-bar | in "foo bar" "foo\foo bar"#),
            "\"foo\\foo bar"
        );
        assert_eq!(f(r#"foo-bar | in "foo bar" foo\foo-bar"#), "foo\\foo-bar");
        assert_eq!(f(r#"foo-bar | in "foo bar" foo\foo bar"#), "bar");
        assert_eq!(f(r#"foo-bar | in 'foo bar' 'foo\foo bar"#), "'foo\\foo bar");
    }
}

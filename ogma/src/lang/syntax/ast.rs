//! AST representation.
//!
//! This is comprised of:
//! ```sh
//! in data.csv | each-row { max | + 1 } | echo
//!    ^------^            ^-----------^        --> Args
//! ^---------^   ^--------------------^   ^--^ --> Blocks
//! ^-----------------------------------------^ --> Expression
//! ```
use ::kserd::Number;
use std::{borrow::Cow, fmt, ops, path, sync::Arc};

/// `Tag` only implements tag _value_ equality checking (as in `.str()`).
#[derive(Clone)]
pub struct Tag(Arc<Tag_>);

/// Inner tag.
#[derive(Clone)]
pub struct Tag_ {
    /// The location this tag is referencing.
    pub anchor: Location,
    /// The source line this tag slices.
    pub line: Arc<str>,
    /// The start byte position (inclusive).
    pub start: usize,
    /// The end byte position (exclusive).
    pub end: usize,
}

impl Default for Tag {
    fn default() -> Self {
        Tag(Arc::new(Tag_ {
            anchor: Location::Shell,
            line: "".into(),
            start: 0,
            end: 0,
        }))
    }
}

impl ops::Deref for Tag {
    type Target = Tag_;
    fn deref(&self) -> &Tag_ {
        self.0.deref()
    }
}

impl From<Tag_> for Tag {
    fn from(t: Tag_) -> Self {
        Tag(Arc::new(t))
    }
}

#[allow(clippy::len_without_is_empty)]
impl Tag {
    /// The string slice of this tag.
    ///
    /// # Panics
    /// Panics if `start` or `end` do not form a valid range in `line`.
    pub fn str(&self) -> &str {
        &self.line[self.start..self.end]
    }

    /// The source line.
    pub fn line(&self) -> &str {
        &self.line
    }

    /// The byte length of the tag (`end - start`).
    pub fn len(&self) -> usize {
        self.end - self.start
    }

    /// Treat this tag as a range.
    pub fn range(&self) -> std::ops::Range<usize> {
        self.start..self.end
    }

    /// COW the inner tag.
    pub fn make_mut(&mut self) -> &mut Tag_ {
        Arc::make_mut(&mut self.0)
    }

    /// Union `self` and `b` together, extending the tag.
    ///
    /// # Panics
    /// Panics if the underlying source string is not the same.
    pub fn union(mut self, b: &Tag) -> Self {
        assert!(
            Arc::ptr_eq(&self.line, &b.line),
            "tag's underlying source string is not the same"
        );

        let t = self.make_mut();
        t.start = t.start.min(b.start);
        t.end = t.end.max(b.end);

        self
    }
}

impl AsRef<str> for Tag {
    fn as_ref(&self) -> &str {
        self.str()
    }
}

impl PartialEq for Tag {
    fn eq(&self, rhs: &Self) -> bool {
        self.str() == rhs.str()
    }
}

impl PartialEq<str> for Tag {
    fn eq(&self, rhs: &str) -> bool {
        self.str() == rhs
    }
}

impl Eq for Tag {}

impl fmt::Debug for Tag {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_tuple("Tag")
            .field(&self.str())
            .field(&format_args!("{}..{}", self.start, self.end))
            .finish()
    }
}

impl fmt::Display for Tag {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.str())
    }
}

/// A location indicator.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Location {
    /// Defined within `ogma`'s core.
    Ogma,
    /// Defined in the current sessions shell.
    Shell,
    /// Defined in a file. `(filepath, line)`.
    ///
    /// Limiting line counts to 2^16.
    File(Arc<path::Path>, u16),
}

impl Default for Location {
    fn default() -> Self {
        Location::Shell
    }
}

impl Location {
    /// Construct a location from a file and a line number.
    pub fn file<F: AsRef<path::Path>>(file: F, line: u16) -> Self {
        Location::File(Arc::from(file.as_ref()), line)
    }
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Location::Ogma => write!(f, "<ogma>"),
            Location::Shell => write!(f, "shell"),
            Location::File(path, line) => write!(f, "'{}' - line {}", path.display(), line),
        }
    }
}

/// An expression. An expression is made of multiple blocks connected by pipes.
///
/// > `expr1 a b | expr2 c d`
#[derive(Debug)]
pub struct Expression {
    /// The overall tag of the expression.
    pub tag: Tag,
    /// The comprising blocks.
    pub blocks: Vec<Block>,
    /// An optionally annotated output type constraint.
    pub out_ty: Option<Tag>,
}

impl PartialEq for Expression {
    fn eq(&self, rhs: &Self) -> bool {
        self.tag == rhs.tag
            && self.out_ty == rhs.out_ty
            && self
                .blocks
                .iter()
                .zip(rhs.blocks.iter())
                .all(|(a, b)| a.op().eq(&b.op()) && a.terms().eq(&b.terms()))
    }
}

impl Clone for Expression {
    fn clone(&self) -> Self {
        Expression {
            tag: self.tag.clone(),
            blocks: self.blocks.iter().map(|x| x.as_ref().clone()).collect(),
            out_ty: self.out_ty.clone(),
        }
    }
}

// ###### BLOCK ################################################################
/// List of terms.
pub type Terms = Vec<Term>;

type CTag<'a> = Cow<'a, Tag>;

/// The common aspects of a processing block.
///
/// Blocks can be in different notation style, but at their core always specify a _single_ op tag,
/// a list of terms, optional input type constraint, and optional output type constraint.
pub trait IBlock: std::fmt::Debug + Send + Sync {
    /// The operation.
    fn op(&self) -> CTag;
    /// The terms.
    fn terms(&self) -> Cow<[Term]>;
    /// An optional annotated input type constraint.
    fn in_ty(&self) -> Option<CTag>;
    /// An optional annotated output type constraint.
    fn out_ty(&self) -> Option<CTag>;

    /// Create a tag that extends across the whole block.
    fn block_tag(&self) -> Tag;
    /// The common aspects of a block: the operation tag and a list of terms.
    fn parts(self: Box<Self>) -> BlockParts;
    /// Trait-object safe clone.
    fn clone(&self) -> Block;
}

/// The concrete parts of a block.
pub struct BlockParts {
    /// The operation.
    pub op: Op,
    /// The terms.
    pub terms: Terms,
    /// Optional annotated input type.
    pub in_ty: Option<Tag>,
    /// Optional annotated output type.
    pub out_ty: Option<Tag>,
}

/// A single expression block. An expression is made of multiple blocks connected by pipes.
pub type Block = Box<dyn IBlock>;

impl<T: IBlock + 'static> From<T> for Block {
    fn from(x: T) -> Self {
        Box::new(x)
    }
}

/// Polish notation block: `op term1 term2`.
#[derive(Debug, Clone, PartialEq)]
pub struct PrefixBlock {
    /// The command/implementation name ident.
    pub op: Op,
    /// The terms.
    pub terms: Terms,
    /// An optional annotated input type constraint.
    pub in_ty: Option<Tag>,
    /// An optional annotated output type constraint.
    pub out_ty: Option<Tag>,
}

impl IBlock for PrefixBlock {
    fn op(&self) -> CTag {
        match self.op.is_op() {
            Some(x) => Cow::Borrowed(x),
            None => panic!("partitions are not yet supported"),
        }
    }

    fn terms(&self) -> Cow<[Term]> {
        self.terms.as_slice().into()
    }

    fn in_ty(&self) -> Option<CTag> {
        self.in_ty.as_ref().map(Cow::Borrowed)
    }

    fn out_ty(&self) -> Option<CTag> {
        self.out_ty.as_ref().map(Cow::Borrowed)
    }

    fn block_tag(&self) -> Tag {
        let mut tag = self.op.tag().into_owned();

        if let Some(t) = &self.in_ty {
            tag.make_mut().start = t.start.saturating_sub(1); // include leading ':'
        }

        if let Some(t) = &self.out_ty {
            tag.make_mut().end = t.end;
        }

        let end = self
            .terms
            .last()
            .map(|term| match term {
                Term::Arg(x) => x.tag().end,
                Term::Flag(x) => x.end,
            })
            .unwrap_or(tag.end);
        tag.make_mut().end = end;

        tag
    }

    fn parts(self: Box<Self>) -> BlockParts {
        let PrefixBlock {
            op,
            terms,
            in_ty,
            out_ty,
        } = *self;

        BlockParts {
            op,
            terms,
            in_ty,
            out_ty,
        }
    }

    fn clone(&self) -> Block {
        Box::new(Clone::clone(self))
    }
}

/// Dot operator has terms that are `[lhs,rhs]`.
#[derive(Debug, Clone, PartialEq)]
pub struct DotOperatorBlock {
    /// The op tag (`.`).
    pub op: Tag,
    /// The left hand side argument.
    pub lhs: Argument,
    /// For the dot infix operator, the rhs is _always_ a plain ident.
    pub rhs: Tag,
    /// An optional annotated output type constraint.
    pub out_ty: Option<Tag>,
}

impl DotOperatorBlock {
    fn terms(&self) -> Terms {
        vec![
            Term::Arg(self.lhs.clone()),
            Term::Arg(Argument::Ident(self.rhs.clone())),
        ]
    }
}

impl IBlock for DotOperatorBlock {
    fn op(&self) -> CTag {
        Cow::Borrowed(&self.op)
    }

    fn terms(&self) -> Cow<[Term]> {
        DotOperatorBlock::terms(self).into()
    }

    fn in_ty(&self) -> Option<CTag> {
        None
    }

    fn out_ty(&self) -> Option<CTag> {
        self.out_ty.as_ref().map(Cow::Borrowed)
    }

    fn block_tag(&self) -> Tag {
        let mut tag = self.lhs.tag().clone();

        if matches!(self.lhs, Argument::Var(_)) {
            tag.make_mut().start = tag.start.saturating_sub(1);
        }
        tag.make_mut().end = self.rhs.end;

        if let Some(t) = &self.out_ty {
            tag.make_mut().end = t.end;
        }

        tag
    }

    fn parts(self: Box<Self>) -> BlockParts {
        let terms = self.terms();
        let DotOperatorBlock {
            op,
            lhs: _,
            rhs: _,
            out_ty,
        } = *self;

        BlockParts {
            op: Op::Single(op),
            terms,
            in_ty: None,
            out_ty,
        }
    }

    fn clone(&self) -> Block {
        Box::new(Clone::clone(self))
    }
}

// ###### TERM #################################################################
/// A expression block term: `bar` in `foo bar`.
#[derive(Debug, PartialEq, Clone)]
pub enum Term {
    /// An argument term.
    Arg(Argument),
    /// A flag.
    Flag(Tag),
}

/// An argument kind.
#[derive(Debug, PartialEq, Clone)]
pub enum Argument {
    /// Recognised as just an identifier.
    Ident(Tag),
    /// Recognised as a number.
    Num(Number, Tag),
    /// Recognised as a special literal (such as `#t` for true).
    Pound(char, Tag),
    /// Recognised as a variable reference.
    Var(Tag),
    /// Recognised as an expression.
    Expr(Expression),
}

impl Argument {
    /// Get the tag which represents the argument.
    ///
    /// For expressions this spans the whole expression.
    /// For variables this _does not_ include the `$` character.
    pub fn tag(&self) -> &Tag {
        use Argument::*;
        match self {
            Ident(x) | Pound(_, x) | Num(_, x) | Var(x) => x,
            Expr(expr) => &expr.tag,
        }
    }
}

// ###### DEFINITIONS ##########################################################
/// A implementation definition's parameters.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Parameter {
    /// The name ident of the parameter.
    pub ident: Tag,
    /// Optional type specifier, eg `x:Num`. This is used to label `expressions`.
    pub ty: Option<Tag>,
}

/// A implementation definition.
#[derive(Debug, PartialEq, Clone)]
pub struct DefinitionImpl {
    /// The location where this impl is defined.
    pub loc: Location,
    /// The source code.
    pub src: Arc<str>,
    /// The name ident of the impl.
    pub name: Tag,
    /// An optional input type.
    pub in_ty: Option<Tag>,
    /// The implementation's required parameters.
    pub params: Vec<Parameter>,
    /// The implementation's evaluation expression.
    pub expr: Expression,
}

/// A type definition.
#[derive(Debug, PartialEq, Eq)]
pub struct DefinitionType {
    /// The location where this type is defined.
    pub loc: Location,
    /// The source code.
    pub src: String,
    /// The name ident of the type.
    pub name: Tag,
    /// The type's flavour (and structure).
    pub ty: TypeVariant,
}

/// Types are either `Sum` (enum) or `Product` (struct).
#[derive(Debug, PartialEq, Eq)]
pub enum TypeVariant {
    /// A 'sum' type, a type composed of mutually exclusive variants.
    Sum(Vec<Variant>),
    /// A 'product' type, a type composed of fields.
    Product(Vec<Field>),
}

/// A sum type variant.
#[derive(Debug, PartialEq, Eq)]
pub struct Variant {
    /// The name ident.
    pub name: Tag,
    /// Optional inner fields
    pub fields: Option<Vec<Field>>,
}

/// A product type field.
#[derive(Debug, PartialEq, Eq)]
pub struct Field {
    /// The name ident.
    pub name: Tag,
    /// The field type.
    pub ty: Tag,
    /// Type parameterisation: Ty<A B C>
    pub params: Vec<Tag>,
}

// ###### PARTITION PATHS ######################################################
/// A partition _path_, terminating in a command.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Path {
    pub(super) components: Arc<[Tag]>,
    pub(super) idx: u8,
    pub(super) rooted: bool,
}

/// The parsed operation, represented as a single tag or a path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Op {
    /// Consists of a path.
    Path(Path),
    /// Consisting of a single tag.
    Single(Tag),
}

impl Path {
    /// Returns the tag from _the current component to the end_ of the path.
    pub fn tag(&self) -> CTag {
        if self.is_last() {
            CTag::Borrowed(self.last())
        } else {
            let mut tag = self.last().clone();
            let t = tag.make_mut();
            t.start = self.component().start;

            if self.rooted && self.idx == 0 {
                t.start = t.start.saturating_sub(1); // include leading `/`
            }

            CTag::Owned(tag)
        }
    }

    /// Returns the current component tag.
    pub fn component(&self) -> &Tag {
        &self.components[self.idx as usize]
    }

    /// Returns if this path is on the _last_ component.
    pub fn is_last(&self) -> bool {
        self.idx as usize == self.components.len() - 1
    }

    /// Return the last component of the path, which is the definition.
    pub fn last(&self) -> &Tag {
        self.components.last().expect("more than zero components")
    }
}

impl Op {
    /// Returns a tag which covers the whole defined op.
    pub fn tag(&self) -> CTag {
        match self {
            Op::Single(t) => CTag::Borrowed(t),
            Op::Path(p) => p.tag(),
        }
    }

    /// Returns `Some` if the op is a singleton, or if path is on its last component.
    pub fn is_op(&self) -> Option<&Tag> {
        match self {
            Op::Single(t) => Some(t),
            Op::Path(p) if p.is_last() => Some(p.last()),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tag_testing() {
        let tag = Tag::from(Tag_ {
            anchor: Location::Shell,
            line: Arc::from("Hello, world!"),
            start: 0,
            end: 5,
        });
        assert_eq!(tag.range(), 0..5);
        assert_eq!(&format!("{:?}", tag), r#"Tag("Hello", 0..5)"#);
    }

    #[test]
    fn sizing() {
        assert_eq!(std::mem::size_of::<Tag>(), 8);
        assert_eq!(std::mem::size_of::<Location>(), 24);
    }

    fn tt(s: &str) -> Tag {
        Tag_ {
            anchor: Location::Shell,
            line: Arc::from(s),
            start: 0,
            end: s.len(),
        }
        .into()
    }

    #[test]
    fn path_testing() {}
}

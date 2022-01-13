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
use std::{borrow::Cow, fmt, path::Path, sync::Arc};

/// `Tag` only implements tag _value_ equality checking (as in `.str()`).
#[derive(Clone)]
pub struct Tag {
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
        Self {
            anchor: Location::Shell,
            line: "".into(),
            start: 0,
            end: 0,
        }
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
#[derive(Debug, PartialEq, Clone)]
pub enum Location {
    /// Defined within `ogma`'s core.
    Ogma,
    /// Defined in the current sessions shell.
    Shell,
    /// Defined in a file. `(filepath, line)`.
    File(Arc<Path>, usize),
}

impl Default for Location {
    fn default() -> Self {
        Location::Shell
    }
}

impl Location {
    /// Construct a location from a file and a line number.
    pub fn file<F: AsRef<Path>>(file: F, line: usize) -> Self {
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
}

impl PartialEq for Expression {
    fn eq(&self, rhs: &Self) -> bool {
        self.tag == rhs.tag
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
        }
    }
}

// ###### BLOCK ################################################################
/// Operation tag.
pub type Op = Tag;
/// List of terms.
pub type Terms = Vec<Term>;

/// The common aspects of a processing block.
///
/// Blocks can be in different notation style, but at their core always specify a _single_ op tag,
/// and a list of terms.
pub trait IBlock: std::fmt::Debug + Send + Sync {
    /// The operation.
    fn op(&self) -> Cow<Tag>;
    /// The terms.
    fn terms(&self) -> Cow<[Term]>;
    /// Create a tag that extends across the whole block.
    fn block_tag(&self) -> Tag;
    /// The common aspects of a a block: the operation tag and a list of terms.
    fn parts(self: Box<Self>) -> (Op, Terms);
    /// Trait-object safe clone.
    fn clone(&self) -> Block;
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
}

impl IBlock for PrefixBlock {
    fn op(&self) -> Cow<Tag> {
        Cow::Borrowed(&self.op)
    }

    fn terms(&self) -> Cow<[Term]> {
        self.terms.as_slice().into()
    }

    fn block_tag(&self) -> Tag {
        let mut tag = self.op.clone();
        let end = self
            .terms
            .last()
            .map(|term| match term {
                Term::Arg(x) => x.tag().end,
                Term::Flag(x) => x.end,
            })
            .unwrap_or(tag.end);
        tag.end = end;
        tag
    }

    fn parts(self: Box<Self>) -> (Op, Terms) {
        (self.op, self.terms)
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
    fn op(&self) -> Cow<Tag> {
        Cow::Borrowed(&self.op)
    }

    fn terms(&self) -> Cow<[Term]> {
        DotOperatorBlock::terms(self).into()
    }

    fn block_tag(&self) -> Tag {
        let mut tag = self.lhs.tag().clone();
        if matches!(self.lhs, Argument::Var(_)) {
            tag.start = tag.start.saturating_sub(1);
        }
        tag.end = self.rhs.end;
        tag
    }

    fn parts(self: Box<Self>) -> (Op, Terms) {
        (self.op.clone(), self.terms())
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
#[derive(Debug, PartialEq, Clone)]
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
#[derive(Debug, PartialEq)]
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
#[derive(Debug, PartialEq)]
pub enum TypeVariant {
    /// A 'sum' type, a type composed of mutually exclusive variants.
    Sum(Vec<Variant>),
    /// A 'product' type, a type composed of fields.
    Product(Vec<Field>),
}

/// A sum type variant.
#[derive(Debug, PartialEq)]
pub struct Variant {
    /// The name ident.
    pub name: Tag,
    /// Optional inner fields
    pub fields: Option<Vec<Field>>,
}

/// A product type field.
#[derive(Debug, PartialEq)]
pub struct Field {
    /// The name ident.
    pub name: Tag,
    /// The field type.
    pub ty: Tag,
    /// Type parameterisation: Ty<A B C>
    pub params: Vec<Tag>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tag_testing() {
        let tag = Tag {
            anchor: Location::Shell,
            line: Arc::from("Hello, world!"),
            start: 0,
            end: 5,
        };
        assert_eq!(tag.range(), 0..5);
        assert_eq!(&format!("{:?}", tag), r#"Tag("Hello", 0..5)"#);
    }
}

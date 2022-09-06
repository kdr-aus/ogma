//! Parsing source into a AST.

#[cfg(test)]
mod test;

use crate::prelude::{ast::*, err, Definitions, HashSet};
use ::kserd::Number;
use ::libs::divvy::Str;
use nom::{
    branch::*, bytes::complete::*, character::complete::*, combinator::*, error::ParseError,
    error::*, multi::*, sequence::*, IResult, Offset,
};
use std::sync::Arc;

struct Line {
    line: Arc<str>,
    loc: Location,
}

impl Line {
    fn create_tag(&self, tag: &str) -> Tag {
        let start = self.line.offset(tag);
        let end = start + tag.len();
        Tag_ {
            anchor: self.loc.clone(),
            line: self.line.clone(),
            start,
            end,
        }
        .into()
    }
}

// ------ Entry and Error ------------------------------------------------------
/// Successful parse result.
pub enum ParseSuccess {
    /// Parsed as a `def`inition.
    Impl(DefinitionImpl),
    /// Parsed as a type definition (`def-ty`).
    Ty(DefinitionType),
    /// Parsed as an expression.
    Expr(Expression),
}

/// Parse the `input` as a valid `ogma` expression or definition.
///
/// Uses `Location::Shell`.
pub fn parse(input: &str, defs: &Definitions) -> Result<ParseSuccess, ParseFail> {
    let loc = Location::Shell;
    if input.starts_with("def ") {
        definition_impl(input, loc, defs).map(ParseSuccess::Impl)
    } else if input.starts_with("def-ty ") {
        definition_type(input, loc).map(ParseSuccess::Ty)
    } else {
        expression(input, loc, defs).map(ParseSuccess::Expr)
    }
}

/// Parse an expression.
pub fn expression<S: Into<Arc<str>>>(
    expr: S,
    location: Location,
    definitions: &Definitions,
) -> Result<Expression, ParseFail> {
    let line = Line {
        loc: location,
        line: expr.into(),
    };
    let expr = &line.line;
    let x = no_trailing_input(self::expr(&line, definitions))(expr)
        .map_err(|e| convert_parse_error(e, &line.line, line.loc.clone()))
        .map(|x| x.1);

    x
}

/// Parse a definition implementation (`def`).
pub fn definition_impl<S: Into<Arc<str>>>(
    def: S,
    location: Location,
    definitions: &Definitions,
) -> Result<DefinitionImpl, ParseFail> {
    let line = Line {
        loc: location.clone(),
        line: def.into(),
    };

    self::def_impl_inner(&line.line, &line, location.clone(), definitions)
        .map(|x| x.1)
        .map_err(|e| convert_parse_error(e, &line.line, location))
}

/// Parse a definition type (`def-ty`).
pub fn definition_type<S: Into<Arc<str>>>(
    def: S,
    location: Location,
) -> Result<DefinitionType, ParseFail> {
    let line = Line {
        loc: location.clone(),
        line: def.into(),
    };

    self::def_type_inner(&line.line, &line, location.clone())
        .map(|x| x.1)
        .map_err(|e| convert_parse_error(e, &line.line, location))
}

/// Failure to parse results in the parse [`Error`], and an expecting AST node.
pub type ParseFail = (err::Error, Expecting);

bitflags::bitflags! {
    /// An indication of expected AST node type if parsing fails.
    ///
    /// This is a best guess based on parsing context.
    pub struct Expecting: u32 {
	/// Unable to provide an AST expectation.
	const NONE = 0;

	/// Expecting a command/implementation.
	const IMPL = 1;

	/// Expecting a type.
	const TYPE = 0b10;

	/// Expecting a term (the `bar` in `foo bar`).
	const TERM = 0b100;

	/// Expecting a Special Literal.
	///
	/// These are `#t`, `#f`, `#i`, `#b`.
	const SPECLITERAL = 0b1000;

    /// Expecting a path.
    const PATH = 0b1_0000;
    }
}

#[derive(Debug, PartialEq)]
struct ParsingError<'a> {
    locs: Vec<(ErrIn<'a>, Str)>,
    expecting: Expecting,
}

#[derive(Debug, PartialEq)]
enum ErrIn<'a> {
    S(&'a str),
    T(Tag),
}

impl From<Tag> for ErrIn<'_> {
    fn from(t: Tag) -> Self {
        ErrIn::T(t)
    }
}

impl<'a> From<&'a str> for ErrIn<'a> {
    fn from(s: &'a str) -> Self {
        ErrIn::S(s)
    }
}

impl<'a> ParseError<&'a str> for ParsingError<'a> {
    fn from_error_kind(input: &'a str, _: ErrorKind) -> Self {
        ParsingError {
            locs: vec![(ErrIn::S(input), "".into())],
            expecting: Expecting::NONE,
        }
    }
    fn append(input: &'a str, _: ErrorKind, mut other: Self) -> Self {
        other.locs.push((ErrIn::S(input), "".into()));
        other
    }
    fn from_char(input: &'a str, ch: char) -> Self {
        ParsingError {
            locs: vec![(ErrIn::S(input), format!("expected `{}`", ch).into())],
            expecting: Expecting::NONE,
        }
    }
}

impl<'a> ContextError<&'a str> for ParsingError<'a> {
    fn add_context(input: &'a str, cx: &'static str, mut other: Self) -> Self {
        other.locs.push((ErrIn::S(input), cx.into()));
        other
    }
}

impl<'a> ParsingError<'a> {
    fn err<I, C>(input: I, cx: C, expecting: Expecting) -> nom::Err<Self>
    where
        I: Into<ErrIn<'a>>,
        C: Into<Str>,
    {
        nom::Err::Error(Self {
            locs: vec![(input.into(), cx.into())],
            expecting,
        })
    }

    fn failure<I, C>(input: I, cx: C, expecting: Expecting) -> nom::Err<Self>
    where
        I: Into<ErrIn<'a>>,
        C: Into<Str>,
    {
        nom::Err::Failure(Self {
            locs: vec![(input.into(), cx.into())],
            expecting,
        })
    }
}

fn convert_parse_error<'a>(
    err: nom::Err<ParsingError<'a>>,
    source: &'a str,
    loc: Location,
) -> ParseFail {
    use err::*;
    let ParsingError { locs, expecting } = match err {
        nom::Err::Error(e) | nom::Err::Failure(e) => e,
        _ => unreachable!("nom parses using a complete parser"),
    };

    let traces = locs
        .into_iter()
        .map(|(input, cx)| {
            let (start, mut len) = match input {
                ErrIn::S(s) => (source.offset(s), s.len()),
                ErrIn::T(t) => (t.start, t.len()),
            };
            if len == 0 && !source.is_empty() {
                len = 1;
            }

            err::Trace {
                loc: loc.clone(),
                source: source.into(),
                desc: Some(cx.to_string()),
                start,
                len,
            }
        })
        .collect();

    let err = Error {
        cat: Category::Parsing,
        desc: "could not parse input line".into(),
        traces,
        ..Error::default()
    };

    (err, expecting)
}

// ------ Utils ----------------------------------------------------------------
/// A combinator that takes a parser `inner` and produces a parser that also consumes both leading
/// and trailing whitespace, returning the output of `inner`.
fn ws<'a, F, O, E: ParseError<&'a str>>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O, E>
where
    F: FnMut(&'a str) -> IResult<&'a str, O, E>,
{
    delimited(multispace0, inner, multispace0)
}

/// Applies the Expecting to an error if occurred.
fn exp<'a, F, O>(
    mut inner: F,
    exp: Expecting,
) -> impl FnMut(&'a str) -> IResult<&'a str, O, ParsingError<'a>>
where
    F: FnMut(&'a str) -> IResult<&'a str, O, ParsingError<'a>>,
{
    move |i| {
        inner(i).map_err(|e| {
            e.map(|mut e| {
                if e.expecting == Expecting::NONE {
                    e.expecting = exp;
                }
                e
            })
        })
    }
}

/// Applies a context if the error does not already have one.
fn maybe_cx<'a, F, O>(
    context: &'static str,
    mut inner: F,
) -> impl FnMut(&'a str) -> IResult<&'a str, O, ParsingError<'a>>
where
    F: FnMut(&'a str) -> IResult<&'a str, O, ParsingError<'a>>,
{
    move |i| {
        inner(i).map_err(|e| {
            e.map(|mut e| {
                e.locs.push((i.into(), context.into()));
                e
            })
        })
    }
}

/// If leading with a ':', treat as a type identifier.
fn opt_ty(line: &Line) -> impl FnMut(&str) -> IResult<&str, Option<Tag>, ParsingError> + '_ {
    move |i| {
        opt(preceded(
            char(':'),
            exp(
                cut(context("expecting a type identifier", op_ident(line))),
                Expecting::TYPE,
            ),
        ))(i)
    }
}

fn no_trailing_input<'a, F, O>(
    mut inner: F,
) -> impl FnMut(&'a str) -> IResult<&'a str, O, ParsingError<'a>>
where
    F: FnMut(&'a str) -> IResult<&'a str, O, ParsingError<'a>>,
{
    move |i| {
        let (rem, o) = inner(i)?;

        if rem.trim().is_empty() {
            Ok(("", o))
        } else {
            let last_brace = i[..i.offset(rem)].rfind('}').map(|x| &i[x..=x]);

            let mut e = ParsingError::failure(rem, "remaining input", Expecting::NONE);

            if let Some(lb) = last_brace {
                e = e.map(|e| ParsingError::add_context(lb, "possibly unnecessary brace", e));
            }

            Err(e)
        }
    }
}

// ------ Expression -----------------------------------------------------------
fn expr<'f>(
    line: &'f Line,
    defs: &'f Definitions,
) -> impl for<'a> Fn(&'a str) -> IResult<&'a str, Expression, ParsingError<'a>> + 'f {
    move |input| {
        let mut blocks: Vec<Block> = Vec::new();
        let mut blkparse = maybe_cx("no command", ws(map(block(line, defs), Box::new)));

        // first -- try block parsing
        let (mut i, blk) = blkparse(input)?;
        blocks.push(blk);

        // subsequent after pipes -- try block parsing
        while i.starts_with('|') {
            let (ii, blk) = blkparse(&i[1..])?;
            i = ii;
            blocks.push(blk);
        }

        // finally, try block but allow failure
        if let Ok((ii, blk)) = blkparse(i) {
            i = ii;
            blocks.push(blk);
        }

        if blocks.is_empty() {
            Err(ParsingError::err(
                &input[..input.offset(i)],
                "no valid blocks",
                Expecting::IMPL,
            ))
        } else {
            let mut tag = line.create_tag(input);
            tag.make_mut().end = line.line.offset(i);
            Ok((
                i,
                Expression {
                    tag,
                    blocks,
                    out_ty: None,
                },
            ))
        }
    }
}

fn block<'f>(
    line: &'f Line,
    defs: &'f Definitions,
) -> impl for<'a> Fn(&'a str) -> IResult<&'a str, PrefixBlock, ParsingError<'a>> + 'f {
    move |i| {
        let (i, in_ty) = opt_ty(line)(i)?;
        // NOTE, op is not wrapped in `ws` since this would consume trailing whitespace
        let (i, op) = exp(preceded(multispace0, op(line)), Expecting::IMPL)(i)?;
        let (i, out_ty) = opt_ty(line)(i)?;
        let (i, terms) = many0(ws(term(line, defs)))(i)?;
        Ok((
            i,
            PrefixBlock {
                op,
                terms,
                in_ty,
                out_ty,
            },
        ))
    }
}

fn path(line: &Line) -> impl Fn(&str) -> IResult<&str, Path, ParsingError> + '_ {
    move |i| {
        let (i_, rooted) = map(opt(tag("/")), |x| x.is_some())(i)?;
        let (i_, p) = map(separated_list1(tag("/"), tmp_op_parser(line)), |cs| Path {
            components: cs.into(),
            idx: 0,
            rooted,
        })(i_)?;

        match i_.strip_prefix('/') {
            Some(x) if x.is_empty() => Err(ParsingError::err(
                i,
                "trailing partition delimiter",
                Expecting::Path,
            )),
            Some(x) => {
                let i = match x.split_once(|c: char| c.is_whitespace()) {
                    Some((x_, _)) if x_.is_empty() => x,
                    Some((x, _)) => x,
                    None => x,
                };
                Err(ParsingError::err(
                    i,
                    "not a valid partition component",
                    Expecting::None,
                ))
            }
            None => Ok((i_, p)),
        }
    }
}

/// Temporary handle `::` until the path sytax takes over.
fn tmp_op_parser(line: &Line) -> impl Fn(&str) -> IResult<&str, Tag, ParsingError> + '_ {
    move |i| {
// op is slightly different to op_ident in that chained paths (Ord::Gt) are resolved to a
        // _single_ Tag. It also enforces that the path `::` must not be trailing (by way of
        // needing to pass 2 parsers)
        let (mut i, mut ident) = op_ident(line)(i)?;
        let start = ident.start;
        while let Ok((ii, end)) = preceded(tag("::"), op_ident(line))(i) {
            i = ii;
            ident = end;
        }

        ident.make_mut().start = start;

        Ok((i, ident))
    }
}

/// OPERATIONS -- This is where the 'default' commands are defined.
fn op(line: &Line) -> impl Fn(&str) -> IResult<&str, Op, ParsingError> + '_ {
    move |i| {
        let x = map(spec_op, |cmd| Op::Single(line.create_tag(cmd)))(i);

        if x.is_ok() {
            return x;
        }

        let (i, x) = path(line)(i)?;
        let op = if x.components.len() == 1 {
            Op::Single(x.components[0].clone())
        } else {
            Op::Path(x)
        };

        Ok((i, op))
    }
}

/// These are specially defined operation symbols
fn spec_op(i: &str) -> IResult<&str, &str, ParsingError> {
    alt((
        tag("\\"),
        tag("+"),
        tag("-"),
        tag("*"),
        tag("×"),
        tag("/"),
        tag("÷"),
        tag("="),
        tag("!="),
        tag(">="),
        tag("<="),
        tag(">"),
        tag("<"),
        tag("."),
    ))(i)
}

/// Operations can be made of a-z,A-Z,0-9,-,_,:: characters and must start with a a-z,A-Z.
/// a-z means alphabetic here.
fn op_ident(line: &Line) -> impl Fn(&str) -> IResult<&str, Tag, ParsingError> + '_ {
    move |i| {
        if i.is_empty() {
            return Err(ParsingError::err(i, "empty identifier", Expecting::NONE));
        }

        let c = i.chars().next().expect("one or more chars");
        if !c.is_alphabetic() {
            return Err(ParsingError::err(
                &i[..c.len_utf8()],
                format!(
                    "invalid identifier, expecting alphabetic character, found `{}`",
                    c,
                ),
                Expecting::NONE,
            ));
        }

        map(
            take_while1(|c: char| c.is_alphanumeric() || c == '-' || c == '_'),
            |ident| line.create_tag(ident),
        )(i)
    }
}

fn known_op<'a>(line: &'a Line, defs: &'a Definitions) -> impl Fn(&str) -> bool + 'a {
    move |i| match op(line)(i) {
        Ok((_, op)) => match op.is_op() {
            Some(t) => defs.impls().contains_op(t.str()),
            None => false, // TODO handle this once `defs` can have path queries
        }
        _ => false,
    }
}

/// Term consists of Flag or Arg.
///
/// If an argument, try applying matching infix operators.
fn term<'f>(
    line: &'f Line,
    defs: &'f Definitions,
) -> impl Fn(&str) -> IResult<&str, Term, ParsingError> + 'f {
    move |i| {
        if i.starts_with("--") {
            map(flag(line), Term::Flag)(i)
        } else {
            let (i, arg) = arg(line, defs)(i)?;
            let (i, arg) = maybe_infix(line, i, arg)?;
            Ok((i, Term::Arg(arg)))
        }
    }
}

/// Maybe infix keeps apply matching infix operators to transform the lhs Argument into a nest of
/// expressions. This only happens if _it matches an infix pattern_.
fn maybe_infix<'a>(
    line: &Line,
    mut i: &'a str,
    mut lhs: Argument,
) -> IResult<&'a str, Argument, ParsingError<'a>> {
    while recognise_infix(i) {
        if i.starts_with('.') {
            let (ii, b) = dot_infixed(lhs, line)(i)?;
            i = ii;
            lhs = Argument::Expr(Expression {
                tag: b.block_tag(),
                blocks: vec![Box::new(b)],
                out_ty: None,
            });
        }
    }

    Ok((i, lhs))
}

fn recognise_infix(i: &str) -> bool {
    i.starts_with('.')
}

/// Parse `rhs` of _infix pattern_ (`lhs<op>rhs`) as an _identifier_, supporting [`op_ident`] as
/// default, but using [`ident`] if the input starts with `'` or `"`. This allows for `rhs`
/// identifiers such as `"foo bar"` or `'Some/Path to/Something'`.
fn infix_rhs_ident(line: &Line) -> impl FnMut(&str) -> IResult<&str, Tag, ParsingError> + '_ {
    move |i| {
        if i.starts_with(&['\'', '"'] as &[_]) {
            ident(line)(i)
        } else {
            op_ident(line)(i)
        }
    }
}

/// Left-hand side has been parsed as argument, `i` requires the dot prefix since this is required
/// to parse into a Tag.
fn dot_infixed(
    lhs: Argument,
    line: &Line,
) -> impl FnOnce(&str) -> IResult<&str, DotOperatorBlock, ParsingError> + '_ {
    move |i| {
        let (i, op) = tag(".")(i)?;
        let (i, rhs) = cut(infix_rhs_ident(line))(i)?;
        let (i, out_ty) = opt_ty(line)(i)?;
        let blk = DotOperatorBlock {
            op: line.create_tag(op),
            lhs,
            rhs,
            out_ty,
        };

        Ok((i, blk))
    }
}

/// Argument is expression, variable, number, or ident.
/// - starts with `{`: parse as expression
/// - starts with `$`: parse as variable
/// - starts with `#`: parse as boolean or special input
/// - starts with `:`: return **Failure** -- unexpected type identifier
/// - parses as number: return Num
/// - first term parses as a KNOWN op: parse as BLOCK (but return as Expression)
/// - finally parse as Ident if nothing else
fn arg<'f>(
    line: &'f Line,
    defs: &'f Definitions,
) -> impl Fn(&str) -> IResult<&str, Argument, ParsingError> + 'f {
    move |i| {
        if i.starts_with('{') {
            if let Ok((r, _)) =
                delimited::<_, _, _, _, (), _, _, _>(char('{'), multispace0, char('}'))(i)
            {
                Err(ParsingError::failure(
                    &i[..i.offset(r)],
                    "empty block",
                    Expecting::IMPL,
                ))
            } else {
                // we know that i starts with { so we grab the start tag position for later.
                let start = line.create_tag(i).start;

                let (i, mut e) = cut(delimited(
                    char('{'),
                    ws(expr(line, defs)),
                    exp(char('}'), Expecting::TERM),
                ))(i)?;

                // see if there is a trailing type
                let (i, out_ty) = opt_ty(line)(i)?;
                e.out_ty = out_ty;

                // expand the tag to capture the braces!
                e.tag.make_mut().start = start;
                e.tag.make_mut().end += 1;
                if let Some(t) = &e.out_ty {
                    e.tag.make_mut().end = t.end;
                }

                Ok((i, Argument::Expr(e)))
            }
        } else if let Some(stripped) = i.strip_prefix(':') {
            // adjust some of the error to capture just the type identifier section
            let (_, ident) = take_till(breakon)(stripped)?;
            let mut tag = line.create_tag(i);
            tag.make_mut().end = tag.start + 1 + ident.len(); // capture :ident

            Err(ParsingError::failure(
                tag,
                "unexpected type identifier",
                Expecting::TERM,
            ))
        } else if breakon_s(i) {
            Err(nom::Err::Error(make_error(i, ErrorKind::IsA)))
        } else if i.starts_with('$') {
            map(var(line), Argument::Var)(i)
        } else if let Some(s) = i.strip_prefix('#') {
            let (ii, mut c) = cut(exp(op_ident(line), Expecting::SPECLITERAL))(s)?;
            if c.str().len() != 1 {
                Err(ParsingError::failure(
                    c,
                    "special literals only have one character",
                    Expecting::SPECLITERAL,
                ))
            } else {
                let ch = c.str().chars().next().unwrap();
                let mut t = c.make_mut();
                t.start = t.start.saturating_sub(1);
                Ok((ii, Argument::Pound(ch, c)))
            }
        } else if let Ok((j, (n, s))) = num(line)(i) {
            Ok((j, Argument::Num(n, s)))
        } else if known_op(line, defs)(i) {
            let mut tag = line.create_tag(i);
            let (i, block) = ws(block(line, defs))(i)?;
            tag.make_mut().end = line.line.offset(i);
            let expr = Expression {
                tag,
                blocks: vec![Box::new(block)],
                out_ty: None,
            };
            Ok((i, Argument::Expr(expr)))
        } else {
            map(ident(line), Argument::Ident)(i)
        }
    }
}

fn var(line: &Line) -> impl Fn(&str) -> IResult<&str, Tag, ParsingError> + '_ {
    move |i| preceded(char('$'), op_ident(line))(i) // can use the same op_ident parser
}

fn flag(line: &Line) -> impl Fn(&str) -> IResult<&str, Tag, ParsingError> + '_ {
    move |i| preceded(tag("--"), ident(line))(i) // parse as ident (can have quotes)
}

fn ident<'a: 'f, 'f>(
    line: &'f Line,
) -> impl Fn(&'a str) -> IResult<&'a str, Tag, ParsingError> + 'f {
    move |i| {
        let wrapped_str = |ch: char| delimited(char(ch), take_till(move |c| c == ch), char(ch));

        let (i, ident) = if i.starts_with(':') {
            // expecting an identifier but found a type specifier
            return Err(ParsingError::failure(
                i,
                "expecting an identifier but found a type specifier",
                Expecting::NONE,
            ));
        } else if i.starts_with('\"') {
            // wrapped in double quotes, don't stop on break chars
            wrapped_str('"')(i)
        } else if i.starts_with('\'') {
            // wrapped in quotes, don't stop on break chars
            wrapped_str('\'')(i)
        } else {
            // no wrapping, split on breaks
            take_till1(breakon)(i)
        }?;

        Ok((i, line.create_tag(ident)))
    }
}

fn num(line: &Line) -> impl Fn(&str) -> IResult<&str, (Number, Tag), ()> + '_ {
    move |i| {
        use std::str::FromStr;
        let (i, n) = take_till1(|c| (c != '.') & breakon(c))(i)?;
        match n {
            "inf" | "∞" => Ok(Number::from(std::f64::INFINITY)),
            "-inf" | "-∞" => Ok(Number::from(std::f64::NEG_INFINITY)),
            "nan" => Ok(Number::from(std::f64::NAN)),
            n => Number::from_str(n),
        }
        .map_err(|_| nom::Err::Error(()))
        .map(|num| (i, (num, line.create_tag(n))))
    }
}

fn breakon(ch: char) -> bool {
    ch == '|' || ch == '{' || ch == '}' || ch == ':' || ch.is_whitespace()
}

fn breakon_s(s: &str) -> bool {
    s.chars().next().map(breakon).unwrap_or(false)
}

// ------ Implementations ------------------------------------------------------
fn def_impl_inner<'a>(
    i: &'a str,
    line: &Line,
    loc: Location,
    definitions: &Definitions,
) -> IResult<&'a str, DefinitionImpl, ParsingError<'a>> {
    let (i, name) = ws(preceded(tag("def "), op(line)))(i)?;
    let name = match name.is_op() {
        Some(t) => Ok(t.clone()),
        None => {
            Err(ParsingError::failure(name.tag().into_owned(), "paths cannot be used to define a definition name", Expecting::None))
        }
    }?;
    let (i, in_ty) = ws(opt(op_ident(line)))(i)?;
    let x = if in_ty.is_some() {
        Expecting::NONE
    } else {
        Expecting::TYPE
    };
    let (i, params) = exp(def_params(line), x)(i)?;
    let (i, expr) = no_trailing_input(ws(delimited(
        char('{'),
        ws(expr(line, definitions)),
        char('}'),
    )))(i)?;

    let def = DefinitionImpl {
        loc,
        src: line.line.clone(),
        name,
        in_ty,
        params,
        expr,
    };

    Ok((i, def))
}

fn def_params(line: &Line) -> impl Fn(&str) -> IResult<&str, Vec<Parameter>, ParsingError> + '_ {
    move |i| {
        let (i, params) = delimited(char('('), many0(ws(def_param(line))), char(')'))(i)?;
        // check that there is only one remainder and it is at the end.
        // also check that parameters are distinct
        let mut set = HashSet::default();
        for param in &params {
            if set.contains(param.ident.str()) {
                return Err(ParsingError::err(
                    param.ident.clone(),
                    format!(
                        "parameters must be distinct: `{}` has been previously defined",
                        param.ident
                    ),
                    Expecting::NONE,
                ));
            }
            set.insert(param.ident.str());
        }

        Ok((i, params))
    }
}

fn def_param(line: &Line) -> impl Fn(&str) -> IResult<&str, Parameter, ParsingError> + '_ {
    move |i| {
        let (i, ident) = op_ident(line)(i)?;
        let (i, ty) = if i.starts_with(':') {
            map(preceded(char(':'), op_ident(line)), Some)(i)?
        } else {
            (i, None)
        };
        Ok((i, Parameter { ident, ty }))
    }
}

// ------ Types ----------------------------------------------------------------
fn def_type_inner<'a>(
    i: &'a str,
    line: &Line,
    loc: Location,
) -> IResult<&'a str, DefinitionType, ParsingError<'a>> {
    // this does not handle paramterisation _after_ type name definition. This might be lifted
    // in the future.
    let (i, name) = ws(preceded(tag("def-ty "), op_ident(line)))(i)?;
    let (i, ty) = match ws::<_, _, ()>(tag("::"))(i) {
        Ok((i, _)) => map(defty_variants(line), TypeVariant::Sum)(i),
        Err(_) => map(defty_fields(line), TypeVariant::Product)(i),
    }?;

    // no more characters after this!
    all_consuming(multispace0)(i)?;

    let def = DefinitionType {
        loc,
        src: line.line.to_string(),
        name,
        ty,
    };

    Ok((i, def))
}

fn defty_variants(line: &Line) -> impl Fn(&str) -> IResult<&str, Vec<Variant>, ParsingError> + '_ {
    move |i| separated_list0(ws(char('|')), ws(defty_variant(line)))(i)
}

fn defty_variant(line: &Line) -> impl Fn(&str) -> IResult<&str, Variant, ParsingError> + '_ {
    move |i| {
        let (i, name) = ws(op_ident(line))(i)?;
        let (i, fields) = opt(ws(defty_fields(line)))(i)?;
        Ok((i, Variant { name, fields }))
    }
}

fn defty_fields(line: &Line) -> impl Fn(&str) -> IResult<&str, Vec<Field>, ParsingError> + '_ {
    move |i| delimited(char('{'), many0(ws(defty_field(line))), char('}'))(i)
}

fn defty_field(line: &Line) -> impl Fn(&str) -> IResult<&str, Field, ParsingError> + '_ {
    move |i| {
        let (i, name) = op_ident(line)(i)?;
        let (i, _) = cut(context(
            "a field requires a type assignment: `field:Type`",
            char(':'),
        ))(i)?;
        let (mut i, ty) = cut(context(
            "missing a valid type specifier: `field:Type`",
            op_ident(line),
        ))(i)?;
        let mut params = vec![];
        if i.starts_with('<') {
            let (ii, p) = cut(delimited(
                char('<'),
                many1(ws(op_ident(line))),
                ws(char('>')),
            ))(i)?;
            params = p;
            i = ii;
        }

        Ok((i, Field { name, ty, params }))
    }
}

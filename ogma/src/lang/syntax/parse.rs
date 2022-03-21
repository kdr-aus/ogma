//! Parsing source into a AST.

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
pub fn parse(input: &str, defs: &Definitions) -> std::result::Result<ParseSuccess, ParseFail> {
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
    let x = self::expr(&line, definitions)(expr)
        .and_then(|(i, expr)| {
            context(
                "remaining input",
                exp(all_consuming(multispace0), Expecting::None),
            )(i)
            .map(|_| expr)
        })
        .map_err(|e| convert_parse_error(e, &line.line, Location::Shell));
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

/// An indication of expected AST node type if parsing fails.
///
/// This is a best guess based on parsing context.
#[derive(Debug, PartialEq, Copy, Clone)]
pub enum Expecting {
    /// Expecting a command/implementation.
    Impl,
    /// Expecting a type.
    Type,
    /// Expecting a term (the `bar` in `foo bar`).
    ///
    /// > Because commands can be inlined, if `Term` is encountered, impls would suit as well.
    Term,
    /// Expecting a Special Literal.
    ///
    /// These are `#t`, `#f`, and `#i`.
    SpecLiteral,
    /// Unable to provide an AST expectation.
    None,
}

#[derive(Debug, PartialEq)]
struct ParsingError<'a> {
    input: ErrIn<'a>,
    cx: Str,
    expecting: Expecting,
}

#[derive(Debug, PartialEq)]
enum ErrIn<'a> {
    S(&'a str),
    T(Tag),
}

impl<'a> ParseError<&'a str> for ParsingError<'a> {
    fn from_error_kind(input: &'a str, _: ErrorKind) -> Self {
        ParsingError {
            input: ErrIn::S(input),
            cx: "".into(),
            expecting: Expecting::None,
        }
    }
    fn append(input: &'a str, _: ErrorKind, _: Self) -> Self {
        ParsingError {
            input: ErrIn::S(input),
            cx: "".into(),
            expecting: Expecting::None,
        }
    }
    fn from_char(input: &'a str, ch: char) -> Self {
        ParsingError {
            input: ErrIn::S(input),
            cx: format!("expected `{}`", ch).into(),
            expecting: Expecting::None,
        }
    }
}

impl<'a> ContextError<&'a str> for ParsingError<'a> {
    fn add_context(_input: &'a str, cx: &'static str, mut other: Self) -> Self {
        other.cx = cx.into();
        other
    }
}

fn convert_parse_error<'a>(
    err: nom::Err<ParsingError<'a>>,
    source: &'a str,
    loc: Location,
) -> ParseFail {
    use err::*;
    let ParsingError {
        input,
        cx,
        expecting,
    } = match err {
        nom::Err::Error(e) | nom::Err::Failure(e) => e,
        _ => unreachable!("nom parses using a complete parser"),
    };

    let (start, mut len) = match input {
        ErrIn::S(s) => (source.offset(s), s.len()),
        ErrIn::T(t) => (t.start, t.len()),
    };
    if len == 0 && !source.is_empty() {
        len = 1;
    }

    let err = Error {
        cat: Category::Parsing,
        desc: "could not parse input line".into(),
        traces: vec![err::Trace {
            loc,
            source: source.into(),
            desc: Some(cx.to_string()),
            start,
            len,
        }],
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

/// Applies the Expecting to and error if occurred.
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
                if e.expecting == Expecting::None {
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
                if e.cx.is_empty() {
                    e.cx = context.into();
                }
                e
            })
        })
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
            Err(nom::Err::Error(ParsingError {
                input: ErrIn::S(&input[..input.offset(i)]),
                cx: "no valid blocks".into(),
                expecting: Expecting::Impl,
            }))
        } else {
            let mut tag = line.create_tag(input);
            tag.make_mut().end = line.line.offset(i);
            Ok((i, Expression { tag, blocks }))
        }
    }
}

fn block<'f>(
    line: &'f Line,
    defs: &'f Definitions,
) -> impl for<'a> Fn(&'a str) -> IResult<&'a str, PrefixBlock, ParsingError<'a>> + 'f {
    move |i| {
        let (i, op) = exp(op(line), Expecting::Impl)(i)?;
        let (i, terms) = many0(ws(term(line, defs)))(i)?;
        Ok((i, PrefixBlock { op, terms }))
    }
}

/// OPERATIONS -- This is where the 'default' commands are defined.
fn op(line: &Line) -> impl Fn(&str) -> IResult<&str, Tag, ParsingError> + '_ {
    move |i| {
        let x = map(spec_op, |cmd| line.create_tag(cmd))(i);
        if x.is_ok() {
            return x;
        }

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
            return Err(nom::Err::Error(ParsingError {
                input: ErrIn::S(i),
                cx: "empty identifier".into(),
                expecting: Expecting::None,
            }));
        }

        let c = i.chars().next().expect("one or more chars");
        if !c.is_alphabetic() {
            return Err(nom::Err::Error(ParsingError {
                input: ErrIn::S(&i[..c.len_utf8()]),
                cx: format!(
                    "invalid identifier, expecting alphabetic character, found `{}`",
                    c,
                )
                .into(),
                expecting: Expecting::None,
            }));
        }

        map(
            take_while1(|c: char| c.is_alphanumeric() || c == '-' || c == '_'),
            |ident| line.create_tag(ident),
        )(i)
    }
}

fn known_op<'a>(line: &'a Line, defs: &'a Definitions) -> impl Fn(&str) -> bool + 'a {
    move |i| match op(line)(i) {
        Ok((_, op)) => defs.impls().contains_op(op.str()),
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
        let blk = DotOperatorBlock {
            op: line.create_tag(op),
            lhs,
            rhs,
        };

        Ok((i, blk))
    }
}

/// Argument is expression, variable, number, or ident.
/// - starts with `{`: parse as expression
/// - starts with `$`: parse as variable
/// - starts with `#`: parse as boolean or special input
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
                Err(nom::Err::Failure(ParsingError {
                    input: ErrIn::S(&i[..i.offset(r)]),
                    cx: "empty block".into(),
                    expecting: Expecting::Impl,
                }))
            } else {
                // we know that i starts with { so we grab the start tag position for later.
                let start = line.create_tag(i).start;
                let (i, mut e) = cut(delimited(
                    char('{'),
                    ws(expr(line, defs)),
                    exp(char('}'), Expecting::Term),
                ))(i)?;
                // expand the tag to capture the braces!
                e.tag.make_mut().start = start;
                e.tag.make_mut().end += 1;
                Ok((i, Argument::Expr(e)))
            }
        } else if breakon_s(i) {
            Err(nom::Err::Error(make_error(i, ErrorKind::IsA)))
        } else if i.starts_with('$') {
            map(var(line), Argument::Var)(i)
        } else if let Some(s) = i.strip_prefix('#') {
            let (ii, mut c) = cut(exp(op_ident(line), Expecting::SpecLiteral))(s)?;
            if c.str().len() != 1 {
                Err(nom::Err::Failure(ParsingError {
                    input: ErrIn::T(c),
                    cx: "special literals only have one character".into(),
                    expecting: Expecting::SpecLiteral,
                }))
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

fn ident<'a: 'f, 'f, E: ParseError<&'a str>>(
    line: &'f Line,
) -> impl Fn(&'a str) -> IResult<&'a str, Tag, E> + 'f {
    move |i| {
        let wrapped_str = |ch: char| delimited(char(ch), take_till(move |c| c == ch), char(ch));

        let (i, ident) = if i.starts_with('\"') {
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
    ch == '|' || ch == '{' || ch == '}' || ch.is_whitespace()
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
    let (i, in_ty) = ws(opt(op_ident(line)))(i)?;
    let x = if in_ty.is_some() {
        Expecting::None
    } else {
        Expecting::Type
    };
    let (i, params) = exp(def_params(line), x)(i)?;
    let (i, expr) = ws(delimited(char('{'), ws(expr(line, definitions)), char('}')))(i)?;
    all_consuming(multispace0)(i)?;

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
        let e = |err| Err(nom::Err::Error(err));
        let (i, params) = delimited(char('('), many0(ws(def_param(line))), char(')'))(i)?;
        // check that there is only one remainder and it is at the end.
        // also check that parameters are distinct
        let mut set = HashSet::default();
        for param in &params {
            if set.contains(param.ident.str()) {
                return e(ParsingError {
                    input: ErrIn::T(param.ident.clone()),
                    cx: format!(
                        "parameters must be distinct: `{}` has been previously defined",
                        param.ident
                    )
                    .into(),
                    expecting: Expecting::None,
                });
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

#[cfg(test)]
mod tests {
    use super::*;
    use nom::Err as E;
    use Argument::*;
    use Expecting as Ex;
    use Term::*;

    fn tag_eq(tag: &Tag, s: &str) -> bool {
        tag.str() == s
    }

    fn line(s: &str) -> Line {
        Line {
            loc: Location::Shell,
            line: Arc::from(s),
        }
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
    fn input_expr() {
        let d = &Definitions::new();
        let x = expression("in", Location::Shell, d);
        assert_eq!(
            x,
            Ok(Expression {
                tag: tt("in"),
                blocks: vec![PrefixBlock {
                    op: tt("in"),
                    terms: vec![]
                }
                .into()]
            })
        );

        let x = expression("in file.csv", Location::Shell, d);
        assert_eq!(
            x,
            Ok(Expression {
                tag: tt("in file.csv"),
                blocks: vec![PrefixBlock {
                    op: tt("in"),
                    terms: vec![Arg(Ident(tt("file.csv")))]
                }
                .into()]
            })
        );
    }

    fn parse_err<'a, T>(
        exp: Ex,
        source: &'a str,
        cx: &str,
        start: usize,
        len: usize,
    ) -> Result<T, ParseFail> {
        Err((
            err::Error {
                cat: err::Category::Parsing,
                desc: "could not parse input line".into(),
                traces: vec![err::Trace {
                    loc: Location::Shell,
                    source: source.into(),
                    desc: Some(cx.into()),
                    start,
                    len,
                }],
                ..Default::default()
            },
            exp,
        ))
    }

    #[test]
    fn empty_expr() {
        let d = &Definitions::new();
        let x = expression("", Location::Shell, d);
        assert_eq!(x, parse_err(Ex::Impl, "", "empty identifier", 0, 0));

        let src = "in something.csv { }";
        let x = expression(src, Location::Shell, d);
        assert_eq!(x, parse_err(Ex::Impl, src, "empty block", 17, 3));
        let s = x.unwrap_err().0.to_string();
        assert_eq!(
            &s,
            "Parsing Error: could not parse input line
--> shell:17
 | in something.csv { }
 |                  ^^^ empty block
"
        );

        let src = "in something.csv | adf {    }";
        let x = expression(src, Location::Shell, d);
        assert_eq!(x, parse_err(Ex::Impl, src, "empty block", 23, 6));
        let err_str = x.unwrap_err().0.to_string();
        assert_eq!(
            &err_str,
            "Parsing Error: could not parse input line
--> shell:23
 | in something.csv | adf {    }
 |                        ^^^^^^ empty block
"
        );

        let src = "in { asdf {   } }";
        let x = expression(src, Location::Shell, d);
        assert_eq!(x, parse_err(Ex::Impl, src, "empty block", 10, 5));
        let err_str = x.unwrap_err().0.to_string();
        assert_eq!(
            &err_str,
            "Parsing Error: could not parse input line
--> shell:10
 | in { asdf {   } }
 |           ^^^^^ empty block
"
        );
    }

    #[test]
    fn empty_expr2() {
        let d = &Definitions::new();

        let x = line(" {  } ");
        let x = expr(&x, d)(&x.line);
        assert_eq!(
            x,
            Err(E::Error(ParsingError {
                input: ErrIn::S("{"),
                cx: "invalid identifier, expecting alphabetic character, found `{`".into(),
                expecting: Ex::Impl,
            }))
        );
        let x = line(" { asdf {  }  } ");
        let x = expr(&x, d)(&x.line);
        assert_eq!(
            x,
            Err(E::Error(ParsingError {
                input: ErrIn::S("{"),
                cx: "invalid identifier, expecting alphabetic character, found `{`".into(),
                expecting: Ex::Impl,
            }))
        );

        let l = line("{  }");
        let x = term(&l, d)(&l.line);
        assert_eq!(
            x,
            Err(E::Failure(ParsingError {
                input: ErrIn::S("{  }"),
                cx: "empty block".into(),
                expecting: Ex::Impl
            }))
        );
    }

    #[test]
    fn after_pipe_error() {
        let d = &Definitions::new();

        let src = "\\ | ";
        let x = expression(src, Location::Shell, d);
        assert_eq!(x, parse_err(Ex::Impl, src, "empty identifier", 4, 1));
        let err_str = x.unwrap_err().0.to_string();
        assert_eq!(
            &err_str,
            r#"Parsing Error: could not parse input line
--> shell:4
 | \ | 
 |     ^ empty identifier
"#
        );

        let src = "\\ { \\ | }";
        let x = expression(src, Location::Shell, d);
        assert_eq!(
            x,
            parse_err(
                Ex::Impl,
                src,
                "invalid identifier, expecting alphabetic character, found `}`",
                8,
                1
            )
        );
        let err_str = x.unwrap_err().0.to_string();
        assert_eq!(
            &err_str,
            r#"Parsing Error: could not parse input line
--> shell:8
 | \ { \ | }
 |         ^ invalid identifier, expecting alphabetic character, found `}`
"#
        );
    }

    #[test]
    fn op_ident_test() {
        let x = line("valid second");
        let x = op_ident(&x)(&x.line);
        assert_eq!(x, Ok((" second", tt("valid"))));
        let x = line("0-invalid second");
        let x = op_ident(&x)(&x.line);
        assert_eq!(
            x,
            Err(E::Error(ParsingError {
                input: ErrIn::S("0"),
                cx: "invalid identifier, expecting alphabetic character, found `0`".into(),
                expecting: Ex::None,
            }))
        );
    }

    #[test]
    fn broken_expr_delimiter() {
        let d = &Definitions::new();
        let src = "\\ { cmd ident ";
        let x = expression(src, Location::Shell, d);
        assert_eq!(x, parse_err(Ex::Term, src, "expected `}`", 14, 1));
        let s = x.unwrap_err().0.to_string();
        assert_eq!(
            &s,
            r#"Parsing Error: could not parse input line
--> shell:14
 | \ { cmd ident 
 |               ^ expected `}`
"#
        );

        let src = "\\ { cmd { ident }";
        let x = expression(src, Location::Shell, d);
        assert_eq!(x, parse_err(Ex::Term, src, "expected `}`", 17, 1));
        let s = x.unwrap_err().0.to_string();
        assert_eq!(
            &s,
            r#"Parsing Error: could not parse input line
--> shell:17
 | \ { cmd { ident }
 |                  ^ expected `}`
"#
        );

        let src = "\\ f | asdf { cmd { ident } ";
        let x = expression(src, Location::Shell, d);
        assert_eq!(x, parse_err(Ex::Term, src, "expected `}`", 27, 1));
        let s = x.unwrap_err().0.to_string();
        assert_eq!(
            &s,
            r#"Parsing Error: could not parse input line
--> shell:27
 | \ f | asdf { cmd { ident } 
 |                            ^ expected `}`
"#
        );

        let src = "\\ file.csv | asdf { cmd {   } ";
        let x = expression(src, Location::Shell, d);
        assert_eq!(x, parse_err(Ex::Impl, src, "empty block", 24, 5));
        let s = x.unwrap_err().0.to_string();
        assert_eq!(
            &s,
            r#"Parsing Error: could not parse input line
--> shell:24
 | \ file.csv | asdf { cmd {   } 
 |                         ^^^^^ empty block
"#
        );

        let src = "\\ adsf | cmd { \\ |";
        let x = expression(src, Location::Shell, d);
        assert_eq!(x, parse_err(Ex::Impl, src, "empty identifier", 18, 1));
        let s = x.unwrap_err().0.to_string();
        assert_eq!(
            &s,
            r#"Parsing Error: could not parse input line
--> shell:18
 | \ adsf | cmd { \ |
 |                   ^ empty identifier
"#
        );
    }

    #[test]
    fn arguments() {
        let src = line("{ \\ asdf } remaining");
        let x = term(&src, &Definitions::new())(&src.line);
        assert_eq!(
            x,
            Ok((
                " remaining",
                Arg(Expr(Expression {
                    tag: tt("{ \\ asdf }"),
                    blocks: vec![PrefixBlock {
                        op: tt("\\"),
                        terms: vec![Arg(Ident(tt("asdf")))]
                    }
                    .into()]
                }))
            ))
        );
    }

    #[test]
    fn pipelining() {
        let src = "\\ test.csv | cmd { \\ asdf }";
        let x = expression(src, Location::Shell, &Definitions::new());
        assert_eq!(
            x,
            Ok(Expression {
                tag: tt("\\ test.csv | cmd { \\ asdf }"),
                blocks: vec![
                    PrefixBlock {
                        op: tt("\\"),
                        terms: vec![Arg(Ident(tt("test.csv")))],
                    }
                    .into(),
                    PrefixBlock {
                        op: tt("cmd"),
                        terms: vec![Arg(Expr(Expression {
                            tag: tt("{ \\ asdf }"),
                            blocks: vec![PrefixBlock {
                                op: tt("\\"),
                                terms: vec![Arg(Ident(tt("asdf")))]
                            }
                            .into()]
                        }))]
                    }
                    .into()
                ]
            })
        );
    }

    #[test]
    fn variable_parsing() {
        let l = line("$in");
        assert_eq!(var(&l)(&l.line), Ok(("", tt("in"))));
        let l = line("in");
        assert!(var(&l)(&l.line).is_err());
    }

    #[test]
    fn variable_term() {
        let l = line("$in");
        assert_eq!(
            term(&l, &Definitions::new())(&l.line),
            Ok(("", Arg(Var(tt("in")))))
        );
    }

    #[test]
    fn identifiers() {
        let i = |s| {
            let line = line(s);
            let x = ident::<ParsingError>(&line)(&line.line).unwrap().1;
            x
        };

        assert_eq!(i("hello"), tt("hello"));
        assert_eq!(i("hello world"), tt("hello"));
        assert_eq!(i("'hello world'"), tt("hello world"));
        assert_eq!(i(r#""hello world""#), tt("hello world"));
        assert_eq!(i(r#"'hello "world"'"#), tt("hello \"world\""));
        assert_eq!(i(r#""hello 'world'""#), tt(r#"hello 'world'"#));
        let x = line("'hello world");
        let x = ident::<ParsingError>(&x)(&x.line);
        assert_eq!(
            x,
            Err(nom::Err::Error(ParsingError {
                input: ErrIn::S(""),
                cx: "expected `\'`".into(),
                expecting: Expecting::None,
            }))
        );
    }

    #[test]
    fn numbers() {
        let l = line("3.14 else");
        let (nan, inf) = (std::f64::NAN, std::f64::INFINITY);
        assert_eq!(
            num(&l)(&l.line),
            Ok((" else", (Number::from(3.14), tt("3.14"))))
        );
        let l = line("-1e6");
        assert_eq!(
            num(&l)(&l.line),
            Ok(("", (Number::from(-1_000_000), tt("-1e6"))))
        );
        let l = line("inf else");
        assert_eq!(
            num(&l)(&l.line),
            Ok((" else", (Number::from(inf), tt("inf"))))
        );
        let l = line("-inf else");
        assert_eq!(
            num(&l)(&l.line),
            Ok((" else", (Number::from(-inf), tt("-inf"))))
        );
        let l = line("∞ else");
        assert_eq!(
            num(&l)(&l.line),
            Ok((" else", (Number::from(inf), tt("∞"))))
        );
        let l = line("-∞ else");
        assert_eq!(
            num(&l)(&l.line),
            Ok((" else", (Number::from(-inf), tt("-∞"))))
        );
        let l = line("nan else");
        assert_eq!(
            num(&l)(&l.line),
            Ok((" else", (Number::from(nan), tt("nan"))))
        );
    }

    #[test]
    fn flags() {
        let defs = &Definitions::new();
        let i = |s| {
            let line = line(s);
            let x = term(&line, defs)(&line.line).unwrap().1;
            x
        };

        assert_eq!(i("--hello"), Term::Flag(tt("hello")));
        assert_eq!(i("--'i!'"), Term::Flag(tt("i!")));
        assert_eq!(i("--\"foo bar'\""), Term::Flag(tt("foo bar'")));
    }

    #[test]
    fn term_parsing_which_is_cmd() {
        let d = &Definitions::new();
        let l = line("filter adsf cdx | ls");
        let x = term(&l, d)(&l.line);
        assert_eq!(
            x,
            Ok((
                "| ls",
                Arg(Expr(Expression {
                    tag: tt("filter adsf cdx "),
                    blocks: vec![PrefixBlock {
                        op: tt("filter"),
                        terms: vec![Arg(Ident(tt("adsf"))), Arg(Ident(tt("cdx")))]
                    }
                    .into()]
                }))
            ))
        );

        let l = line("filter > col-name 1");
        let x = term(&l, d)(&l.line);
        assert_eq!(
            x,
            Ok((
                "",
                Arg(Expr(Expression {
                    tag: tt("filter > col-name 1"),
                    blocks: vec![PrefixBlock {
                        op: tt("filter"),
                        terms: vec![Arg(Expr(Expression {
                            tag: tt("> col-name 1"),
                            blocks: vec![PrefixBlock {
                                op: tt(">"),
                                terms: vec![
                                    Arg(Ident(tt("col-name"))),
                                    Arg(Num(1.into(), tt("1")))
                                ]
                            }
                            .into()]
                        }))]
                    }
                    .into()]
                }))
            ))
        );
    }

    #[test]
    fn nested_expressions_without_braces() {
        let d = &Definitions::new();
        let src = line("filter > col-name 1e3");
        let b = block(&src, d)(&src.line);
        assert_eq!(
            b,
            Ok((
                "",
                PrefixBlock {
                    op: tt("filter"),
                    terms: vec![Arg(Expr(Expression {
                        tag: tt("> col-name 1e3"),
                        blocks: vec![PrefixBlock {
                            op: tt(">"),
                            terms: vec![
                                Arg(Ident(tt("col-name"))),
                                Arg(Num(1000.into(), tt("1e3")))
                            ]
                        }
                        .into()]
                    }))]
                }
            ))
        );

        let src = line("in asdf | filter > col-name 1e3");
        let e = expr(&src, d)(&src.line);
        assert_eq!(
            e,
            Ok((
                "",
                Expression {
                    tag: tt(&src.line),
                    blocks: vec![
                        PrefixBlock {
                            op: tt("in"),
                            terms: vec![Arg(Ident(tt("asdf")))]
                        }
                        .into(),
                        PrefixBlock {
                            op: tt("filter"),
                            terms: vec![Arg(Expr(Expression {
                                tag: tt("> col-name 1e3"),
                                blocks: vec![PrefixBlock {
                                    op: tt(">"),
                                    terms: vec![
                                        Arg(Ident(tt("col-name"))),
                                        Arg(Num(1000.into(), tt("1e3")))
                                    ]
                                }
                                .into()]
                            }))]
                        }
                        .into()
                    ]
                }
            ))
        );

        let src = line("in asdf | filter > col-name 1e3 | ls");
        let e = expr(&src, d)(&src.line);
        assert_eq!(
            e,
            Ok((
                "",
                Expression {
                    tag: tt(&src.line),
                    blocks: vec![
                        PrefixBlock {
                            op: tt("in"),
                            terms: vec![Arg(Ident(tt("asdf")))]
                        }
                        .into(),
                        PrefixBlock {
                            op: tt("filter"),
                            terms: vec![Arg(Expr(Expression {
                                tag: tt("> col-name 1e3 "),
                                blocks: vec![PrefixBlock {
                                    op: tt(">"),
                                    terms: vec![
                                        Arg(Ident(tt("col-name"))),
                                        Arg(Num(1000.into(), tt("1e3")))
                                    ]
                                }
                                .into()]
                            }))]
                        }
                        .into(),
                        PrefixBlock {
                            op: tt("ls"),
                            terms: vec![]
                        }
                        .into()
                    ]
                }
            ))
        );
    }

    #[test]
    fn known_op_test() {
        let d = &Definitions::new();
        let known_op = |s| {
            let line = line(s);
            let x = known_op(&line, d)(&line.line);
            x
        };
        assert!(known_op("> foo"));
        assert!(known_op("\\ foo"));
        assert!(known_op("filter foo"));
        assert!(!known_op("what foo"));
    }

    #[test]
    fn def_param_test() {
        let l = line("--not");
        let x = def_param(&l)(&l.line);
        assert_eq!(
            x,
            Err(E::Error(ParsingError {
                input: ErrIn::S("-"),
                cx: "invalid identifier, expecting alphabetic character, found `-`".into(),
                expecting: Expecting::None
            }))
        );

        let x = line("var rem");
        let x = def_param(&x)(&x.line);
        assert_eq!(
            x,
            Ok((
                " rem",
                Parameter {
                    ident: tt("var"),
                    ty: None
                }
            ))
        );

        let x = line("var:Num rem");
        let x = def_param(&x)(&x.line);
        assert_eq!(
            x,
            Ok((
                " rem",
                Parameter {
                    ident: tt("var"),
                    ty: Some(tt("Num"))
                }
            ))
        );
    }

    #[test]
    fn def_params_test() {
        let x = line("asdf");
        let x = def_params(&x)(&x.line);
        assert_eq!(
            x,
            Err(E::Error(ParsingError {
                input: ErrIn::S("asdf"),
                cx: "expected `(`".into(),
                expecting: Expecting::None,
            }))
        );

        let x = line("(asdf ");
        let x = def_params(&x)(&x.line);
        assert_eq!(
            x,
            Err(E::Error(ParsingError {
                input: ErrIn::S(""),
                cx: "expected `)`".into(),
                expecting: Expecting::None,
            }))
        );

        let x = line("( asdf )");
        let x = def_params(&x)(&x.line).unwrap().1;
        assert_eq!(x.len(), 1);
        assert!(tag_eq(&x[0].ident, "asdf"));

        let x = line("( asdf test )");
        let x = def_params(&x)(&x.line).unwrap().1;
        assert_eq!(x.len(), 2);
        assert!(tag_eq(&x[0].ident, "asdf"));
        assert!(tag_eq(&x[1].ident, "test"));

        let x = line("( asdf test )");
        let x = def_params(&x)(&x.line).unwrap().1;
        assert_eq!(x.len(), 2);
        assert!(tag_eq(&x[0].ident, "asdf"));
        assert!(tag_eq(&x[1].ident, "test"));

        // errors
        let x = line("(test asdf test)");
        let x = def_params(&x)(&x.line);
        assert_eq!(
            x,
            Err(E::Error(ParsingError {
                input: ErrIn::T(tt("test")),
                cx: "parameters must be distinct: `test` has been previously defined".into(),
                expecting: Expecting::None,
            }))
        );
    }

    #[test]
    fn full_op_str() {
        // test that commands such as ls-files won't be recognised as `ls`.
        let x = line("ls what");
        let x = op(&x)(&x.line);
        assert_eq!(x, Ok((" what", tt("ls"))));
        let x = line("ls-files what");
        let x = op(&x)(&x.line);
        assert_eq!(x, Ok((" what", tt("ls-files"))));
    }

    #[test]
    fn spec_op_chars() {
        let x = expression("+ 101 ", Location::Shell, &Definitions::new());
        assert_eq!(
            x,
            Ok(Expression {
                tag: tt("+ 101 "),
                blocks: vec![PrefixBlock {
                    op: tt("+"),
                    terms: vec![Arg(Num(101.into(), tt("101")))]
                }
                .into()],
            })
        );
    }

    #[test]
    fn def_ty_testing() {
        let x = definition_type("def-ty Ord::Lt|Eq|Gt", Location::Shell);
        assert_eq!(
            x,
            Ok(DefinitionType {
                loc: Location::Shell,
                src: "def-ty Ord::Lt|Eq|Gt".to_string(),
                name: tt("Ord"),
                ty: TypeVariant::Sum(vec![
                    Variant {
                        name: tt("Lt"),
                        fields: None
                    },
                    Variant {
                        name: tt("Eq"),
                        fields: None
                    },
                    Variant {
                        name: tt("Gt"),
                        fields: None
                    }
                ])
            })
        );

        let x = definition_type("def-ty Ord :: Lt | Eq | Gt", Location::Shell);
        assert_eq!(
            x,
            Ok(DefinitionType {
                loc: Location::Shell,
                src: "def-ty Ord :: Lt | Eq | Gt".to_string(),
                name: tt("Ord"),
                ty: TypeVariant::Sum(vec![
                    Variant {
                        name: tt("Lt"),
                        fields: None
                    },
                    Variant {
                        name: tt("Eq"),
                        fields: None
                    },
                    Variant {
                        name: tt("Gt"),
                        fields: None
                    }
                ])
            })
        );

        let x = definition_type("def-ty Point { x:Num y:Num }", Location::Shell);
        assert_eq!(
            x,
            Ok(DefinitionType {
                loc: Location::Shell,
                src: "def-ty Point { x:Num y:Num }".to_string(),
                name: tt("Point"),
                ty: TypeVariant::Product(vec![
                    Field {
                        name: tt("x"),
                        ty: tt("Num"),
                        params: vec![]
                    },
                    Field {
                        name: tt("y"),
                        ty: tt("Num"),
                        params: vec![]
                    },
                ])
            })
        );

        let x = definition_type("def-ty Eg :: N { v:Num } | S { s:Str }", Location::Shell);
        assert_eq!(
            x,
            Ok(DefinitionType {
                loc: Location::Shell,
                src: "def-ty Eg :: N { v:Num } | S { s:Str }".to_string(),
                name: tt("Eg"),
                ty: TypeVariant::Sum(vec![
                    Variant {
                        name: tt("N"),
                        fields: Some(vec![Field {
                            name: tt("v"),
                            ty: tt("Num"),
                            params: vec![]
                        },])
                    },
                    Variant {
                        name: tt("S"),
                        fields: Some(vec![Field {
                            name: tt("s"),
                            ty: tt("Str"),
                            params: vec![]
                        },])
                    }
                ])
            })
        );

        let x = definition_type(
            "def-ty Eg :: N { v:Num<A B C> } | S { s:Str }",
            Location::Shell,
        );
        assert_eq!(
            x,
            Ok(DefinitionType {
                loc: Location::Shell,
                src: "def-ty Eg :: N { v:Num<A B C> } | S { s:Str }".to_string(),
                name: tt("Eg"),
                ty: TypeVariant::Sum(vec![
                    Variant {
                        name: tt("N"),
                        fields: Some(vec![Field {
                            name: tt("v"),
                            ty: tt("Num"),
                            params: vec![tt("A"), tt("B"), tt("C")]
                        },])
                    },
                    Variant {
                        name: tt("S"),
                        fields: Some(vec![Field {
                            name: tt("s"),
                            ty: tt("Str"),
                            params: vec![]
                        },])
                    }
                ])
            })
        );
    }

    #[test]
    fn no_type_on_field() {
        let x = definition_type("def-ty Point { x y }", Location::Shell)
            .unwrap_err()
            .0
            .to_string();
        assert_eq!(
            x,
            "Parsing Error: could not parse input line
--> shell:16
 | def-ty Point { x y }
 |                 ^^^^ a field requires a type assignment: `field:Type`
"
        );

        let x = definition_type("def-ty Point { x: y:Num }", Location::Shell)
            .unwrap_err()
            .0
            .to_string();
        assert_eq!(
            x,
            "Parsing Error: could not parse input line
--> shell:17
 | def-ty Point { x: y:Num }
 |                  ^ missing a valid type specifier: `field:Type`
"
        );

        let x = definition_type("def-ty Point { x:Num<A y:Num }", Location::Shell)
            .unwrap_err()
            .0
            .to_string();
        assert_eq!(
            x,
            "Parsing Error: could not parse input line
--> shell:24
 | def-ty Point { x:Num<A y:Num }
 |                         ^^^^^^ expected `>`
"
        );
    }

    #[test]
    fn def_impl_on_ty() {
        let y = "def add Point () { in }";
        let x = definition_impl(y, Location::Shell, &Definitions::new());
        assert_eq!(
            x,
            Ok(DefinitionImpl {
                loc: Location::Shell,
                src: Arc::from(y),
                name: tt("add"),
                in_ty: Some(tt("Point")),
                params: vec![],
                expr: Expression {
                    blocks: vec![PrefixBlock {
                        op: tt("in"),
                        terms: vec![]
                    }
                    .into()],
                    tag: tt("in "),
                }
            })
        );

        let y = "def + Point () { in }";
        let x = definition_impl(y, Location::Shell, &Definitions::new());
        assert_eq!(
            x,
            Ok(DefinitionImpl {
                loc: Location::Shell,
                src: Arc::from(y),
                name: tt("+"),
                in_ty: Some(tt("Point")),
                params: vec![],
                expr: Expression {
                    blocks: vec![PrefixBlock {
                        op: tt("in"),
                        terms: vec![]
                    }
                    .into()],
                    tag: tt("in "),
                }
            })
        );
    }

    #[test]
    fn op_with_path() {
        let x = line("Ord:Gt");
        let x = op(&x)(&x.line);
        assert_eq!(x, Ok((":Gt", tt("Ord"))));

        let x = line("Ord::Gt what");
        let x = op_ident(&x)(&x.line);
        assert_eq!(x, Ok(("::Gt what", tt("Ord"))));

        let x = line("Ord::Gt what");
        let x = op(&x)(&x.line);
        assert_eq!(x, Ok((" what", tt("Ord::Gt"))));

        let x = line("Ord:: what");
        let x = op(&x)(&x.line);
        assert_eq!(x, Ok((":: what", tt("Ord"))));
    }

    // -- partial parsing expecting checks
    #[test]
    fn incomplete_expecting_tests() {
        let exp = |s| parse(s, &Definitions::default()).map(|_| ()).unwrap_err().1;

        assert_eq!(exp("foo-bar | "), Expecting::Impl);
        assert_eq!(exp("foo-bar | in 5 {"), Expecting::Impl);
        assert_eq!(exp("def foo-bar "), Expecting::Type);
        assert_eq!(exp("def foo-bar Num "), Expecting::None);
    }

    #[test]
    fn empty_string() {
        let ident = ident::<()>;
        let l = line("'' else");
        assert_eq!(ident(&l)(&l.line), Ok((" else", tt(""))));
        let l = line(r#""""#);
        assert_eq!(ident(&l)(&l.line), Ok(("", tt(""))));
    }

    #[test]
    fn brace_ends_arg() {
        let src = line("ident{in asdf } remaining");
        let x = ident::<()>(&src)(&src.line);
        assert_eq!(x, Ok(("{in asdf } remaining", tt("ident"))));

        let src = line("$rhs{in asdf } remaining");
        let x = term(&src, &Definitions::new())(&src.line);
        assert_eq!(x, Ok(("{in asdf } remaining", Arg(Var(tt("rhs"))))));

        let src = line("3.14{in asdf } remaining");
        let x = num(&src)(&src.line);
        assert_eq!(
            x,
            Ok(("{in asdf } remaining", (Number::from(3.14), tt("3.14"))))
        );
    }

    #[test]
    fn no_padding() {
        let src = line("{in asdf } remaining");
        let x = term(&src, &Definitions::new())(&src.line);
        assert_eq!(
            x,
            Ok((
                " remaining",
                Arg(Expr(Expression {
                    tag: tt("{in asdf }"),
                    blocks: vec![PrefixBlock {
                        op: tt("in"),
                        terms: vec![Arg(Ident(tt("asdf")))]
                    }
                    .into()]
                }))
            ))
        );

        let src = line("{in asdf} remaining");
        let x = term(&src, &Definitions::new())(&src.line);
        assert_eq!(
            x,
            Ok((
                " remaining",
                Arg(Expr(Expression {
                    tag: tt("{in asdf}"),
                    blocks: vec![PrefixBlock {
                        op: tt("in"),
                        terms: vec![Arg(Ident(tt("asdf")))]
                    }
                    .into()]
                }))
            ))
        );

        let src = line("foo|bar|zog");
        let x = expr(&src, &Definitions::new())(&src.line);
        assert_eq!(
            x,
            Ok((
                "",
                Expression {
                    tag: tt("foo|bar|zog"),
                    blocks: vec![
                        PrefixBlock {
                            op: tt("foo"),
                            terms: vec![]
                        }
                        .into(),
                        PrefixBlock {
                            op: tt("bar"),
                            terms: vec![]
                        }
                        .into(),
                        PrefixBlock {
                            op: tt("zog"),
                            terms: vec![]
                        }
                        .into()
                    ]
                }
            ))
        );
    }

    #[test]
    fn no_padding_integration() {
        let src = line("append{get first|if{= 0}{+ 100}{- 100}}");
        let x = expr(&src, &Definitions::new())(&src.line);
        assert_eq!(
            x,
            Ok((
                "",
                Expression {
                    tag: tt("append{get first|if{= 0}{+ 100}{- 100}}"),
                    blocks: vec![PrefixBlock {
                        op: tt("append"),
                        terms: vec![Arg(Expr(Expression {
                            tag: tt("{get first|if{= 0}{+ 100}{- 100}}"),
                            blocks: vec![
                                PrefixBlock {
                                    op: tt("get"),
                                    terms: vec![Arg(Ident(tt("first")))]
                                }
                                .into(),
                                PrefixBlock {
                                    op: tt("if"),
                                    terms: vec![
                                        Arg(Expr(Expression {
                                            tag: tt("{= 0}"),
                                            blocks: vec![PrefixBlock {
                                                op: tt("="),
                                                terms: vec![Arg(Num(0.into(), tt("0")))],
                                            }
                                            .into()]
                                        })),
                                        Arg(Expr(Expression {
                                            tag: tt("{+ 100}"),
                                            blocks: vec![PrefixBlock {
                                                op: tt("+"),
                                                terms: vec![Arg(Num(100.into(), tt("100")))],
                                            }
                                            .into()]
                                        })),
                                        Arg(Expr(Expression {
                                            tag: tt("{- 100}"),
                                            blocks: vec![PrefixBlock {
                                                op: tt("-"),
                                                terms: vec![Arg(Num(100.into(), tt("100")))],
                                            }
                                            .into()]
                                        }))
                                    ]
                                }
                                .into()
                            ]
                        }))]
                    }
                    .into()]
                }
            ))
        );
    }

    #[test]
    fn no_padding_defty() {
        let src = line("def-ty Ord::Lt|Eq{x:Num y:Num}|Gt");
        let x = def_type_inner(&src.line, &src, Location::Shell);
        assert_eq!(
            x,
            Ok((
                "",
                DefinitionType {
                    loc: Location::Shell,
                    name: tt("Ord"),
                    src: "def-ty Ord::Lt|Eq{x:Num y:Num}|Gt".to_string(),
                    ty: TypeVariant::Sum(vec![
                        Variant {
                            name: tt("Lt"),
                            fields: None
                        },
                        Variant {
                            name: tt("Eq"),
                            fields: Some(vec![
                                Field {
                                    name: tt("x"),
                                    ty: tt("Num"),
                                    params: vec![],
                                },
                                Field {
                                    name: tt("y"),
                                    ty: tt("Num"),
                                    params: vec![],
                                }
                            ])
                        },
                        Variant {
                            name: tt("Gt"),
                            fields: None
                        },
                    ])
                }
            ))
        );
    }

    #[test]
    fn dot_infix_sml() {
        // works on the dot_infixed call
        let src = line("$x.y");
        let x = dot_infixed(Ident(tt("foo")), &src)(&src.line);
        assert_eq!(
            x,
            Err(nom::Err::Error(ParsingError {
                cx: "".into(),
                expecting: Expecting::None,
                input: ErrIn::S("$x.y"),
            }))
        );

        let src = line(".y remaining");
        let x = dot_infixed(Ident(tt("foo")), &src)(&src.line);
        assert_eq!(
            x,
            Ok((
                " remaining",
                DotOperatorBlock {
                    op: tt("."),
                    lhs: Ident(tt("foo")),
                    rhs: tt("y")
                }
            ))
        );

        let src = line(".y.z remaining");
        let x = dot_infixed(Ident(tt("foo")), &src)(&src.line);
        assert_eq!(
            x,
            Ok((
                ".z remaining",
                DotOperatorBlock {
                    op: tt("."),
                    lhs: Ident(tt("foo")),
                    rhs: tt("y")
                }
            ))
        );

        let src = line(".$y remaining");
        let x = dot_infixed(Ident(tt("foo")), &src)(&src.line);
        assert_eq!(
            x,
            Err(nom::Err::Failure(ParsingError {
                input: ErrIn::S("$"),
                cx: "invalid identifier, expecting alphabetic character, found `$`".into(),
                expecting: Expecting::None,
            }))
        );

        // Below we test if encasing identifiers works
        let src = line(".'y y'.z remaining");
        let x = dot_infixed(Ident(tt("foo")), &src)(&src.line);
        assert_eq!(
            x,
            Ok((
                ".z remaining",
                DotOperatorBlock {
                    op: tt("."),
                    lhs: Ident(tt("foo")),
                    rhs: tt("y y")
                }
            ))
        );

        let src = line(r#"."y y".z remaining"#);
        let x = dot_infixed(Ident(tt("foo")), &src)(&src.line);
        assert_eq!(
            x,
            Ok((
                ".z remaining",
                DotOperatorBlock {
                    op: tt("."),
                    lhs: Ident(tt("foo")),
                    rhs: tt("y y")
                }
            ))
        );
    }

    #[test]
    fn dot_infix_large() {
        let d = &Definitions::new();

        let src = line("$x.y");
        let x = term(&src, d)(&src.line);
        assert_eq!(
            x,
            Ok((
                "",
                Arg(Expr(Expression {
                    tag: tt("$x.y"),
                    blocks: vec![DotOperatorBlock {
                        op: tt("."),
                        lhs: Var(tt("x")),
                        rhs: tt("y")
                    }
                    .into()]
                }))
            ))
        );

        let src = line("$x.foo-bar.'foo bar/zog'");
        let x = term(&src, d)(&src.line);
        assert_eq!(
            x,
            Ok((
                "",
                Arg(Expr(Expression {
                    tag: tt("$x.foo-bar.'foo bar/zog"),
                    blocks: vec![DotOperatorBlock {
                        op: tt("."),
                        lhs: Expr(Expression {
                            tag: tt("$x.foo-bar"),
                            blocks: vec![DotOperatorBlock {
                                op: tt("."),
                                lhs: Var(tt("x")),
                                rhs: tt("foo-bar")
                            }
                            .into()]
                        }),
                        rhs: tt("foo bar/zog")
                    }
                    .into()]
                }))
            ))
        );
    }

    #[test]
    fn boolean_parsing() {
        let d = &Definitions::new();
        let src = line("#t foo");
        let x = term(&src, d)(&src.line);
        assert_eq!(x, Ok((" foo", Arg(Pound('t', tt("#t"))))));
        let src = line("#tfoo");
        let x = term(&src, d)(&src.line);
        assert_eq!(
            x,
            Err(nom::Err::Failure(ParsingError {
                input: ErrIn::T(tt("tfoo")),
                cx: "special literals only have one character".into(),
                expecting: Expecting::SpecLiteral
            }))
        );

        let src = line("in #tfoo zog");
        let x = expr(&src, d)(&src.line);
        assert_eq!(
            x,
            Err(nom::Err::Failure(ParsingError {
                input: ErrIn::T(tt("tfoo")),
                cx: "special literals only have one character".into(),
                expecting: Expecting::SpecLiteral
            }))
        );

        let src = line("in #");
        let x = expr(&src, d)(&src.line);
        assert_eq!(
            x,
            Err(nom::Err::Failure(ParsingError {
                input: ErrIn::S(""),
                cx: "empty identifier".into(),
                expecting: Expecting::SpecLiteral
            }))
        );
    }

    #[test]
    fn multiline_def_expecting_impl() {
        let d = &Definitions::new();
        let x = definition_impl(
            "def foo Zog () {
    ",
            Location::Shell,
            d,
        );
        assert!(matches!(x, Err((_, Expecting::Impl))));
    }

    #[test]
    fn spec_ops_dont_need_trailing_space() {
        let src = line("\\#t");
        let x = op(&src)(&src.line);
        assert_eq!(x, Ok(("#t", tt("\\"))));
        let src = line("+#t");
        let x = op(&src)(&src.line);
        assert_eq!(x, Ok(("#t", tt("+"))));

        let defs = &Definitions::new();
        let src = line("\\#t");
        let x = block(&src, defs)(&src.line);
        assert_eq!(
            x,
            Ok((
                "",
                PrefixBlock {
                    op: tt("\\"),
                    terms: vec![Arg(Pound('t', tt("#t")))]
                }
            ))
        );
        let src = line("+#t");
        let x = block(&src, defs)(&src.line);
        assert_eq!(
            x,
            Ok((
                "",
                PrefixBlock {
                    op: tt("+"),
                    terms: vec![Arg(Pound('t', tt("#t")))]
                }
            ))
        );
    }

    #[test]
    fn backslash_str() {
        let ident = ident::<()>;
        let l = line("foo\\bar else");
        assert_eq!(ident(&l)(&l.line), Ok((" else", tt("foo\\bar"))));
        let l = line("'foo bar\\zog' else");
        assert_eq!(ident(&l)(&l.line), Ok((" else", tt("foo bar\\zog"))));
        let l = line(r#""foo bar\zog""#);
        assert_eq!(ident(&l)(&l.line), Ok(("", tt("foo bar\\zog"))));
    }
}

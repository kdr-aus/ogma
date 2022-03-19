use crate::prelude::*;
use ::kserd::Number;
use ::libs::{divvy::Str, rayon::prelude::*};
use ::paste::paste;
use ::table::Entry;
use ast::{Location, Tag};
use eng::{Block, Context, Step};
use lang::{help::*, impls::OperationCategory};
use std::{
    convert::{TryFrom, TryInto},
    iter::*,
};
use Type as Ty;

macro_rules! add {
    ($impls:expr, ($cmd:tt, $cat:ident) $($rem:tt)*) => {{
        add!($impls, ($cmd, $cmd, $cat) $($rem)*)
    }};
    ($impls:expr, ($cmd:literal, $inner:tt, $cat:ident) $($rem:tt)*) => {{
        paste! { add!($impls, ($cmd, [<$inner _intrinsic>], $cat, [<$inner _help>]) $($rem)*) }
    }};
    ($impls:expr, ($cmd:tt, $inner:tt, $cat:ident) $($rem:tt)*) => {{
        paste! { add!($impls, (stringify!($cmd), [<$inner _intrinsic>], $cat, [<$inner _help>]) $($rem)*) }
    }};
    ($impls:expr, ($cmd:expr, $fn:path, $cat:ident, $help:path) $($rem:tt)* ) => {{
        $impls.insert_intrinsic(
            $cmd,
            None,
            $fn,
            Location::Ogma,
            OperationCategory::$cat,
            $help(),
        );
        add!($impls, $($rem)*);
    }};
    ($impls:expr,) => {{}}
}

mod arithmetic;
mod cmp;
mod diagnostics;
mod io;
mod logic;
mod morphism;
mod pipeline;

pub fn add_intrinsics(impls: &mut Implementations) {
    arithmetic::add_intrinsics(impls);
    cmp::add_intrinsics(impls);
    diagnostics::add_intrinsics(impls);
    io::add_intrinsics(impls);
    logic::add_intrinsics(impls);
    morphism::add_intrinsics(impls);
    pipeline::add_intrinsics(impls);
}

// ------ Helpers --------------------------------------------------------------
type InnerTable = ::table::Table<Value>;

/// This standardises the intrinsic where a command can have multiple arguments and perform the
/// same operation across them. For example, the 'add' intrinsic (`+`) can add more than one
/// argument at a time.
///
/// The behaviour is to INCLUDE the input if it fits the type expected of the arguments (so that the
/// expr `\\ 5 | + 1 2` returns an expected 8 (if it were ignore for arguments > 1 it would return
/// 3).
///
/// A special case is provided for TableRow inputs which cannot follow the normal cloning
/// techniques for values.
///
/// The `aggfn` takes the `(prev, next)` and returns the aggregate, along with a flag to exit early
/// if known (for example, short circuiting an `or` or `and`).
fn variadic_intrinsic<T, F>(mut blk: Block, aggfn: F) -> Result<Step>
where
    T: AsType + Into<Value> + 'static,
    T: TryFrom<Value, Error = Error>,
    F: Fn(Option<T>, T) -> (T, bool) + Send + Sync + 'static,
{
    let len = blk.args_len();
    let ty = T::as_type();
    let args = {
        let mut a = Vec::with_capacity(len);
        for _ in 0..len {
            // use blocks input type
            let arg = blk
                .next_arg()?
                .supplied(None)?
                .returns(ty.clone())?
                .concrete()?;
            a.push(arg);
        }
        a
    };
    let err_tag = blk.blk_tag().clone();

    // we have an interesting position here.
    // given blk.in_ty() == ty we can assert that input: T
    // this way we can blk.eval with a known input: T
    // HOWEVER we would be duplicating the business logic if we went down this path. instead we use
    // .eval_value and _cast_ to T in the eval loop (should work!)
    let use_input = blk.in_ty() == &ty;

    blk.eval_o(move |input, cx| {
        let mut prev: Option<T> = if use_input {
            Some(input.clone().try_into()?)
        } else {
            None
        };

        for arg in &args {
            let next: T = arg.resolve(|| input.clone(), &cx)?.try_into()?;
            let (x, exit) = aggfn(prev, next);
            prev = Some(x);
            if exit {
                break;
            }
        }

        prev.ok_or_else(|| Error::insufficient_args(&err_tag, 0, None))
            .map(|x| (x, cx.env))
    })
}

fn variadic_help<C: Into<Str>>(cmd: C, desc: &str, examples: Vec<HelpExample>) -> HelpMessage {
    HelpMessage {
        desc: format!(
            "{}\n-variadic-: more than one argument can be specified",
            desc
        )
        .into(),
        params: vec![HelpParameter::Required("args..".into())],
        examples,
        ..HelpMessage::new(cmd)
    }
}

// table entry builders
fn o<S: Into<Str>>(s: S) -> Entry<Value> {
    Entry::Obj(Value::Str(s.into()))
}
fn n<N: Into<Number>>(n: N) -> Entry<Value> {
    Entry::Num(n.into())
}

/// Used to get a type flag such as `--Str` or `--Num`.
fn type_flag(blk: &mut Block) -> Result<Option<Type>> {
    blk.get_flag(None)
        .map(|ty| {
            let x = if ty.str().starts_with("U_") {
                Tuple::parse_name(ty.str(), blk.defs.types())
            } else {
                None
            };
            match x {
                Some(x) => Ok(x),
                None => blk.defs.types().get_using_tag(&ty).map(|x| x.clone()),
            }
        })
        .transpose()
}

/// Iterator over buf in a parallel fashion, invoking the callback `f` on each item of `buf`.
///
/// This function is meant for iterating over table rows and updating-in-place `T`. The pattern to
/// follow is:
/// 1. `buf` should **have equal or less length than table rows**
/// 2. The first element is skipped over (table header row)
/// 3. The callback should use `*T = foo` to update-in-place.
/// 4. Errors should be propogated through.
///
/// This method utilises `rayon`'s `for_each_init` to seed the colmap amongst workers.
fn par_over_tablerows<T, F>(buf: &mut [T], table: &Table, cx: &Context, f: F) -> Result<()>
where
    F: Fn(&mut T, &mut Context, TableRow) -> Result<()> + Sync,
    T: Send,
{
    let err = crate::Mutex::new(None);
    buf.par_iter_mut().enumerate().skip(1).for_each_init(
        || (Default::default(), cx.clone()),
        |(colmap, cx): &mut (types::TableRowColMap, _), (row, x)| {
            let trow = TableRow::new(table.clone(), colmap.clone(), row);
            if let Err(e) = f(x, cx, trow) {
                *err.lock() = Some(e);
            }
        },
    );
    err.into_inner()
        .map(Result::<()>::Err)
        .transpose()
        .map(|_| ())
}

/// Create an argument list where each argument expects Nil input and resolves to a Str.
/// This is intended for cmds that take a variadic column names.
struct ColNameArgs {
    names: Vec<eng::Argument>,
}

impl ColNameArgs {
    fn build(blk: &mut Block) -> Result<Self> {
        let len = blk.args_len();
        if len == 0 {
            return Err(Error::insufficient_args(blk.blk_tag(), 0, None));
        }

        let mut x = Vec::with_capacity(blk.args_len());
        for _ in 0..blk.args_len() {
            let arg = blk
                .next_arg()?
                .supplied(Ty::Nil)?
                .returns(Ty::Str)?
                .concrete()?;
            x.push(arg);
        }
        Ok(Self { names: x })
    }

    /// Resolves the column index, which **must** exist in the table.
    /// Returns the _name_ of the column that it was resolved to as well.
    fn resolve_indices(&self, table: &Table, cx: &Context) -> Result<Vec<(usize, Str)>> {
        let mut x = Vec::with_capacity(self.names.len());
        for name in &self.names {
            // input is Nil
            let cname: Str = name.resolve(|| Value::Nil, cx)?.try_into()?;
            let i = TableRow::col_idx(table, &cname, &name.tag)?;
            x.push((i, cname));
        }
        Ok(x)
    }

    /// Resolves the column index, **if** it exists in the table.
    /// Returns the _name_ of the column that it was resolved to as well.
    fn resolve_indices_forgiven(
        &self,
        table: &Table,
        cx: &Context,
    ) -> Result<Vec<(Option<usize>, Str)>> {
        let mut x = Vec::with_capacity(self.names.len());
        for name in &self.names {
            // input is Nil
            let cname: Str = name.resolve(|| Value::Nil, cx)?.try_into()?;
            let i = TableRow::col_idx(table, &cname, &name.tag).ok();
            x.push((i, cname));
        }
        Ok(x)
    }
}

fn cnv_num_to_uint<T: TryFrom<u128>>(val: Value, tag: &Tag) -> Result<T> {
    let err = |n: &dyn std::fmt::Display| {
        Error::eval(
            tag,
            "could not convert number into unsigned integer",
            format!("{} does not convert to uint", n),
            None,
        )
    };
    Number::try_from(val)
        .and_then(|n| n.as_u128().map_err(|_| err(&n)))
        .and_then(|n| T::try_from(n).map_err(|_| err(&n)))
}

/// Applies the expression to each row in the table (in parallel).
/// The vector is indexed to the table **(including the header)**.
/// **Uses TableRow as input**.
fn resolve_trow_expr_par(table: &Table, expr: &eng::Argument, cx: &Context) -> Result<Vec<Value>> {
    let mut values: Vec<_> = repeat(Value::Nil).take(table.rows_len()).collect();
    par_over_tablerows(&mut values, table, cx, |v, cx, trow| {
        *v = expr.resolve(|| trow.into(), cx)?;
        Ok(())
    })?;
    Ok(values)
}

/// Abstraction over patterns which follow a binary operator `lhs <cmd> rhs` where `lhs` is the
/// input and `<cmd> rhs` is the block. For instance, the `cmp` command is used in sort-by and
/// grp-by, so this provides a common structure around setting the env, doing the resolve, and
/// handling the variables and error checking. `<cmd>` can be any ogma command.
struct BinaryOp<T> {
    rhs: eng::Variable,
    injector: eng::CodeInjector<eng::Eval>,
    transformation: T,
}

struct BinaryOpRef<'a, T> {
    env: eng::Environment,
    binop: &'a BinaryOp<T>,
}

type CmpReturnHlpr<O> = Box<BinaryOp<Box<dyn Fn(Value) -> O + Send + Sync>>>;

impl<T> BinaryOp<T> {
    /// Construct a new binary operation `cmd`.
    ///
    /// - `ty` is the type of the `lhs` and `rhs`.
    /// - `out_ty` is the expected type returning from `cmd` (eg `Ord` for `cmp`).
    /// - `errtag` is the some tag which defines any error location.
    pub fn new<O>(
        cmd: &str,
        ty: &Type,
        out_ty: &Type,
        defs: &Definitions,
        value_trns: T,
    ) -> Result<Box<Self>>
    where
        T: Fn(Value) -> O,
    {
        let code = format!("{} $rhs", cmd);

        let mut injector = eng::CodeInjector::new(code, defs)
            .map_err(|e| eprintln!("{}", e))
            .expect("this should parse fine");

        let rhs = injector.new_var("rhs", ty.clone());

        let injector = injector.compile(ty.clone(), defs)?;

        if injector.out_ty() != out_ty {
            let oty = injector.out_ty();
            return Err(Error {
                cat: err::Category::Semantics,
                desc: format!(
                    "`{}`'s `{}` impl returns `{}`, expecting `{}`",
                    ty, cmd, oty, out_ty
                ),
                ..Default::default()
            });
        }

        Ok(Self {
            rhs,
            injector,
            transformation: value_trns,
        })
        .map(Box::new)
    }

    /// Creates the expression: `<cmd> $rhs`. Returns the variable tag.
    fn create_expr_and_var(cmd: &str) -> (ast::Expression, Tag) {
        // probably can just use the code injector
        use ast::*;
        let line: Arc<str> = Arc::from(format!("{} $rhs", cmd));
        let end = line.len();
        let tag = Tag {
            anchor: Location::Ogma,
            line,
            start: 0,
            end,
        };
        let op = Tag {
            end: cmd.len(),
            ..tag.clone()
        }; // cmd
        let var = Tag {
            start: op.end + 2, // covers space and $
            end: 8,
            ..tag.clone()
        }; // `rhs`
        let e = Expression {
            tag,
            blocks: vec![Box::new(PrefixBlock {
                op,
                terms: vec![Term::Arg(Argument::Var(var.clone()))],
            })],
        };

        (e, var)
    }

    pub fn pin_env(&self) -> BinaryOpRef<T> {
        BinaryOpRef {
            env: self.injector.env().clone(),
            binop: self,
        }
    }
}

impl BinaryOp<()> {
    /// Helper for creating the `cmp` binary operation.
    ///
    /// - `ty` is type of the `lhs` _and_ `rhs`.
    /// - `caller` is the caller command, used for error reporting.
    /// - `arg` is generally the expression argument being used.
    pub fn cmp_cmd(
        ty: &Type,
        caller: &str,
        blk: &Block,
        arg: &eng::Argument,
    ) -> Result<CmpReturnHlpr<std::cmp::Ordering>> {
        let ordty = Ty::Def(types::ORD.get());
        BinaryOp::new(
            "cmp",
            ty,
            &ordty,
            blk.defs,
            Box::new(cnv_value_to_ord) as Box<_>,
        )
        .map_err(|e| {
            e.add_trace(
                blk.op_tag(),
                format!(
                    "{} requires expression output to implement `cmp` with a single argument",
                    caller
                ),
            )
            .add_trace(&arg.tag, format!("expression returns `{}`", arg.out_ty()))
        })
    }
}

impl<'a, T> BinaryOpRef<'a, T> {
    /// 1. Sets $rhs,
    /// 2. Evals evaluator,
    /// 3. Applies transformation.
    fn eval<O>(&mut self, lhs: Value, rhs: Value, cx: &Context) -> Result<O>
    where
        T: Fn(Value) -> O,
    {
        self.binop.rhs.set_data(&mut self.env, rhs);
        let v = self
            .binop
            .injector
            .eval_with_env(lhs, cx, self.env.clone())?;
        Ok((self.binop.transformation)(v))
    }
}

/// Assumes value is of `Ord` ogma type.
fn cnv_value_to_ord(v: Value) -> std::cmp::Ordering {
    use std::cmp::Ordering::*;
    match v.variant_idx() {
        Some(0) => Less,
        Some(1) => Equal,
        _ => Greater,
    }
}

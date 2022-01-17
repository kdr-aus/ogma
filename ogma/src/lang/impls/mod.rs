mod intrinsics;

use crate::prelude::*;
use ::kserd::Number;
use ::libs::{divvy::Str, fastrand, rayon::prelude::*};
use ::table::Entry;
use ast::{Location, Tag};
use eng::{Block, Context, Step};
use lang::help::*;
use rt::fscache::FSCACHE;
use std::{
    cmp,
    convert::{TryFrom, TryInto},
    fmt,
    io::{self, Write},
    iter::*,
    time::Instant,
};
use Type as Ty;

#[derive(Clone)]
pub enum Implementation {
    Intrinsic {
        loc: Location,
        f: Arc<dyn Fn(Block) -> Result<Step> + Send + Sync>,
    },
    Definition(Box<ast::DefinitionImpl>),
}

impl Implementation {
    pub fn location(&self) -> &Location {
        match self {
            Implementation::Intrinsic { loc, .. } => loc,
            Implementation::Definition(x) => &x.loc,
        }
    }
}

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum OperationCategory {
    Arithmetic,
    Cmp,
    Init,
    Io,
    Logic,
    Morphism,
    Pipeline,
    Diagnostics,
    UserDefined,
}

impl fmt::Display for OperationCategory {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            OperationCategory::Cmp => write!(f, "cmp"),
            OperationCategory::Logic => write!(f, "logic"),
            OperationCategory::Arithmetic => write!(f, "arithmetic"),
            OperationCategory::Morphism => write!(f, "morphism"),
            OperationCategory::Init => write!(f, "init"),
            OperationCategory::Io => write!(f, "io"),
            OperationCategory::Pipeline => write!(f, "pipeline"),
            OperationCategory::Diagnostics => write!(f, "diagnostics"),
            OperationCategory::UserDefined => write!(f, "user-defined"),
        }
    }
}

#[derive(Clone)]
pub struct Implementations {
    /// Impls are the (name, in_ty)
    impls: HashMap<(Str, Option<Type>), Implementation>,
    names: HashMap<Str, (OperationCategory, HelpMessage)>,
}

impl Default for Implementations {
    fn default() -> Self {
        let mut impls = Implementations {
            impls: HashMap::default(),
            names: HashMap::default(),
        };

        intrinsics::add_intrinsics(&mut impls);

        impls
    }
}

impl Implementations {
    pub fn contains_op(&self, op: &str) -> bool {
        self.names.contains_key(op)
    }

    pub fn get_help(&self, op: &Tag) -> Result<&HelpMessage> {
        if !self.contains_op(op.str()) {
            return Err(Error::op_not_found(op));
        }

        Ok(&self.names.get(op.str()).expect("checked was in").1)
    }

    pub fn get_cat(&self, op: &str) -> Option<OperationCategory> {
        self.names.get(op).map(|x| x.0)
    }

    pub fn get_impl(&self, op: &Tag, ty: &Type) -> Result<&Implementation> {
        if !self.contains_op(op.str()) {
            return Err(Error::op_not_found(op));
        }

        let mut key = (Str::new(op), Some(ty.clone()));
        let mut r = self.impls.get(&key); // first try to get impl which matches input type `ty`
        if r.is_none() {
            // if none found, try finding an impl with no ty
            key.1 = None;
            r = self.impls.get(&key);
        }

        r.ok_or_else(|| Error::impl_not_found(op, ty))
    }

    fn insert_intrinsic<O, I, F>(
        &mut self,
        op: O,
        in_ty: I,
        f: F,
        loc: Location,
        cat: OperationCategory,
        help: HelpMessage,
    ) where
        O: Into<Str>,
        I: Into<Option<Type>>,
        F: Fn(Block) -> Result<Step> + Send + Sync + 'static,
    {
        let name = op.into();
        self.impls.insert(
            (name.clone(), in_ty.into()),
            Implementation::Intrinsic {
                loc,
                f: Arc::new(f),
            },
        );
        self.names.insert(name, (cat, help));
    }

    pub fn insert_impl<I>(
        &mut self,
        in_ty: I,
        def: ast::DefinitionImpl,
        cat: OperationCategory,
        help: HelpMessage,
    ) -> Result<()>
    where
        I: Into<Option<Type>>,
    {
        let name = Str::new(&def.name);
        let key = (name.clone(), in_ty.into());
        if let Some(im) = self.impls.get(&key) {
            // we check that the impl does not conflict with ogma defined ones
            let ogma_defined = match im {
                Implementation::Intrinsic { .. } => true,
                Implementation::Definition(x) if x.loc == Location::Ogma => true,
                _ => false,
            };
            if ogma_defined {
                return Err(Error::predefined_impl(&def, key.1.as_ref()));
            }
        }

        self.impls
            .insert(key, Implementation::Definition(Box::new(def)));
        self.names.insert(name, (cat, help));

        Ok(())
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Str, Option<&Type>, &Implementation)> {
        self.impls
            .iter()
            .map(|((name, ty), im)| (name, ty.as_ref(), im))
    }

    pub fn help_iter(&self) -> impl Iterator<Item = (&Str, &HelpMessage)> {
        self.names.iter().map(|(name, (_, help))| (name, help))
    }

    pub fn clear(&mut self, only_files: bool) {
        self.impls.retain(|_, im| match im.location() {
            Location::Ogma => true,
            Location::Shell => only_files,
            Location::File(_, _) => false,
        });
        let names = self.impls.keys().map(|k| &k.0).collect::<HashSet<_>>();
        self.names.retain(|k, _| names.contains(k));
    }
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
    F: Fn(Option<T>, T) -> (T, bool) + Sync + 'static,
{
    let len = blk.args_len();
    let ty = T::as_type();
    let args = {
        let mut a = Vec::with_capacity(len);
        for _ in 0..len {
            a.push(blk.next_arg(None)?.returns(&ty)?); // use blocks input type
        }
        a
    };
    let err_tag = blk.blk_tag.clone();

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

        prev.ok_or_else(|| Error::insufficient_args(&err_tag, 0))
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

/// Used to get a type flag such as `--Str` or `--Num`. `default` is used if no flag existing.
fn type_flag(blk: &mut Block, default: Type) -> Result<Type> {
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
        .unwrap_or(Ok(default))
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
            return Err(Error::insufficient_args(&blk.blk_tag, 0));
        }

        let mut x = Vec::with_capacity(blk.args_len());
        for _ in 0..blk.args_len() {
            x.push(blk.next_arg(Ty::Nil)?.returns(&Ty::Str)?);
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

/// Joins path onto the current cx working directory.
/// If the path goes beyond the store root then an error is returned to disallow users to walk
/// around outside the workspace folders.
fn scrub_filepath(path: &str, cx: &Context) -> io::Result<std::path::PathBuf> {
    let root = cx.root;
    let wd = cx.root.join(cx.wd);

    let wd = wd
        .join(path)
        .canonicalize()
        .map_err(|e| io::Error::new(e.kind(), format!("{}: {}", e, path)))?;

    let root = root
        .canonicalize()
        .unwrap_or_else(|_| std::path::PathBuf::from("."));

    wd.strip_prefix(&root)
        .map(|x| x.to_path_buf())
        .map_err(|_| io::Error::new(io::ErrorKind::Other, "cannot move above root directory"))
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
    env: eng::Environment,
    rhs: eng::Variable,
    evaluator: eng::Evaluator,
    transformation: T,
}

struct BinaryOpRef<'a, T> {
    env: eng::Environment,
    binop: &'a BinaryOp<T>,
}

impl<T> BinaryOp<T> {
    /// Construct a new binary operation `cmd`.
    ///
    /// `ty` is the type of the `lhs` and `rhs`.
    /// `out_ty` is the expected type returning from `cmd` (eg `Ord` for `cmp`).
    /// `caller` is the caller command, used for error reporting.
    /// `errtag` is the some tag which defines any error location.
    pub fn new<O>(
        cmd: &str,
        ty: &Type,
        out_ty: &Type,
        caller: &str,
        errtag: &Tag,
        defs: &Definitions,
        value_trns: T,
    ) -> Result<Box<Self>>
    where
        T: Fn(Value) -> O,
    {
        // create the binary expression and the variables tag
        let (expr, var) = Self::create_expr_and_var(cmd);
        let mut locals = eng::Locals::default();
        // create the $rhs to be set in the new env
        let rhs = locals.add_new_var("rhs".into(), ty.clone(), var);
        // construct the expr evaluator
        // this uses the pseudo-env and the expr we construct, with an input of the type.
        // if the impl of <cmd> on type does not conform to expectations an error will occur
        let evaluator =
            eng::Evaluator::construct(ty.clone(), expr, defs, locals.clone()).map_err(|_| {
                Error {
                    cat: err::Category::Semantics,
                    desc: format!(
                        "`{}` implementation not suitable for `{}` with `{}`",
                        cmd, caller, ty
                    ),
                    traces: vec![err::Trace::from_tag(
                        errtag,
                        format!("this returns `{}`", ty),
                    )],
                    help_msg: Some(format!(
                        "`{}` implementation expects T=>(rhs:T) -> {}",
                        cmd, out_ty
                    )),
                }
            })?;

        if evaluator.ty() != out_ty {
            let mut err = Error::unexp_arg_ty(out_ty, evaluator.ty(), evaluator.tag());
            err.traces.push(err::Trace::from_tag(
                errtag,
                format!("`{}`'s {} impl returns `{}`", ty, cmd, evaluator.ty()),
            ));
            return Err(err);
        }

        Ok(Self {
            env: eng::Environment::new(locals),
            rhs,
            evaluator,
            transformation: value_trns,
        })
        .map(Box::new)
    }

    /// Creates the expression: `<cmd> $rhs`. Returns the variable tag.
    fn create_expr_and_var(cmd: &str) -> (ast::Expression, Tag) {
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
            env: self.env.clone(),
            binop: self,
        }
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
        let (v, _) = self.binop.evaluator.eval(
            lhs,
            Context {
                env: self.env.clone(),
                root: cx.root,
                wd: cx.wd,
            },
        )?;
        Ok((self.binop.transformation)(v))
    }
}

/// Assumes value is of `Ord` ogma type.
fn cnv_value_to_ord(v: Value) -> cmp::Ordering {
    use cmp::Ordering::*;
    match v.variant_idx() {
        Some(0) => Less,
        Some(1) => Equal,
        _ => Greater,
    }
}

// ------ Expr Impl ------------------------------------------------------------
pub fn usr_impl_help(def: &ast::DefinitionImpl) -> HelpMessage {
    let desc: Str = format!("user defined implementation in {}\n`{}`", def.loc, def.src).into();

    let params = def
        .params
        .iter()
        .map(|p| {
            let mut s = p.ident.to_string();
            if let Some(ty) = &p.ty {
                s.push(':');
                s += ty.str();
            }
            HelpParameter::Required(Str::from(s))
        })
        .collect();

    HelpMessage {
        desc,
        params,
        ..HelpMessage::new(Str::new(def.name.str()))
    }
}

// ------ TypeDef Init ---------------------------------------------------------
pub fn add_typedef_init_impls(impls: &mut Implementations, tydef: Arc<types::TypeDef>) {
    fn insert_intrinsic(
        impls: &mut Implementations,
        op: Str,
        loc: Location,
        tydef: Arc<types::TypeDef>,
        variant_idx: usize,
        fields: Vec<types::Field>,
        help: HelpMessage,
    ) {
        impls.insert_intrinsic(
            op,
            None,
            move |blk| typedef_init(blk, tydef.clone(), variant_idx, &fields),
            loc,
            OperationCategory::Init,
            help,
        );
    }

    // TODO one issue here is the type inits do not pass info about their def location to the def
    // --list.
    // This needs to happen.

    match tydef.structure() {
        types::TypeVariant::Sum(variants) => {
            for (idx, variant) in variants.iter().enumerate() {
                let help = typedef_init_help(&tydef);
                let op = format!("{}::{}", tydef.name(), variant.name).into();
                let fields = variant.fields.clone().unwrap_or_default();
                let loc = tydef.loc.clone();
                insert_intrinsic(impls, op, loc, tydef.clone(), idx, fields, help);
            }
        }
        types::TypeVariant::Product(fields) => {
            let help = typedef_init_help(&tydef);
            let fields = fields.clone();
            let loc = tydef.loc.clone();
            insert_intrinsic(impls, Str::new(tydef.name()), loc, tydef, 0, fields, help);
        }
    }
}

fn typedef_init(
    mut blk: Block,
    tydef: Arc<types::TypeDef>,
    variant_idx: usize,
    fields: &[types::Field],
) -> Result<Step> {
    let mut value_places = Vec::with_capacity(fields.len());
    for field in fields {
        value_places.push(blk.next_arg(None)?.returns(field.ty())?);
    }

    blk.eval(Type::Def(tydef.clone()), move |input, cx| {
        let mut values = Vec::with_capacity(value_places.len());
        for value in &value_places {
            values.push(value.resolve(|| input.clone(), &cx)?);
        }

        cx.done(OgmaData::new(tydef.clone(), variant_idx, values))
    })
}

fn typedef_init_help(ty: &types::TypeDef) -> HelpMessage {
    let desc = format!("initialise a `{}`", ty.name()).into();
    let map_field =
        |f: &types::Field| HelpParameter::Required(format!("{}:{}", f.name(), f.ty()).into());

    match ty.structure() {
        types::TypeVariant::Product(fields) => HelpMessage {
            desc,
            params: fields.iter().map(map_field).collect(),
            ..HelpMessage::new(Str::new(ty.name()))
        },
        types::TypeVariant::Sum(variants) => {
            let mut params = Vec::new();
            for variant in variants {
                params.push(HelpParameter::Custom(format!("::{}", variant.name).into()));
                if let Some(fields) = &variant.fields {
                    params.extend(fields.iter().map(map_field));
                }
                params.push(HelpParameter::Break);
            }
            params.pop(); // get rid of last break

            HelpMessage {
                desc,
                params,
                no_space: true,
                ..HelpMessage::new(Str::new(ty.name()))
            }
        }
    }
}

// ------ Dot Op ---------------------------------------------------------------
impl ast::DotOperatorBlock {
    fn help() -> HelpMessage {
        HelpMessage {
            desc: "extract a value out of a structure using infix operator".into(),
            params: vec![HelpParameter::Required("=> $foo.bar".into())],
            examples: vec![
                HelpExample {
                    desc: "extract the x coord of a point structure",
                    code: "$point.x",
                },
                HelpExample {
                    desc: "get the value of a column entry in a TableRow",
                    code: "$table-row.col-name",
                },
            ],
            ..HelpMessage::new(".")
        }
    }

    /// Consists of 2 terms: `input.field`.
    /// For TableRow input we handle separately
    fn instrinsic(mut blk: Block) -> Result<Step> {
        let input = blk.next_arg(None)?;
        let field = blk.next_arg(Ty::Nil)?;
        match input.out_ty() {
            Ty::TabRow => {
                let colarg = field.returns(&Ty::Str)?;
                let ty = TableGetType::Flag(Type::Num); // '.' does not support flags
                blk.eval(ty.ty().clone(), move |lhs_input, cx| {
                    let trow: TableRow = input.resolve(|| lhs_input, &cx)?.try_into()?;
                    table_row_get(&trow, &colarg, &ty, cx)
                })
            }
            x => {
                let (facc, out_ty) = FieldAccessor::construct(x, &field, &blk.op_tag)?;

                blk.eval(out_ty, move |lhs_input, cx| {
                    let input = input.resolve(|| lhs_input, &cx)?;
                    facc.get(input).and_then(|x| cx.done(x))
                })
            }
        }
    }
}

// ------ Get ------------------------------------------------------------------
fn get_help() -> HelpMessage {
    HelpMessage {
        desc: "extract a value out of a data structure
optionally specify a default value if the get type does not match"
            .into(),
        params: vec![
            HelpParameter::Required("field".into()),
            HelpParameter::Optional("default".into()),
        ],
        examples: vec![
            HelpExample {
                desc: "get the x field of a user defined Point type",
                code: "Point 1 3 | get x",
            },
            HelpExample {
                desc: "get the entry of a table row under the column 'size'",
                code: "ls | filter { get size | > 100 }",
            },
            HelpExample {
                desc: "get all files in the directory, using the --Str flag",
                code: "ls | filter { get type --Str | = 'file' }",
            },
            HelpExample {
                desc: "sum the size of files, using a default of zero",
                code: "ls | fold 0 { + {\\$row | get size 0} }",
            },
        ],
        flags: vec![(
            "<type>",
            "assert that the entry is of type. defaults to Num if not specified",
        )],

        ..HelpMessage::new("get")
    }
}

fn get_intrinsic(mut blk: Block) -> Result<Step> {
    match blk.in_ty().clone() {
        Ty::TabRow => {
            let colarg = blk.next_arg(Type::Nil)?.returns(&Ty::Str)?;
            let get_type = match blk
                .next_arg(Type::Nil)
                .ok()
                .map(Box::new)
                .map(TableGetType::Default)
            {
                Some(x) => x,
                None => TableGetType::Flag(type_flag(&mut blk, Type::Num)?),
            };
            blk.eval(get_type.ty().clone(), move |x, cx| {
                let trow: TableRow = x.try_into()?;
                table_row_get(&trow, &colarg, &get_type, cx)
            })
        }
        t => {
            let field_arg = blk.next_arg(None)?;
            let (facc, out_ty) = FieldAccessor::construct(&t, &field_arg, &blk.op_tag)?;
            blk.eval(out_ty, move |input, cx| {
                facc.get(input).and_then(|x| cx.done(x))
            })
        }
    }
}

enum TableGetType {
    // TODO remove box once Argument size reduce
    Default(Box<eng::Argument>),
    Flag(Type),
}

impl TableGetType {
    fn ty(&self) -> &Type {
        match self {
            TableGetType::Default(x) => x.out_ty(),
            TableGetType::Flag(x) => x,
        }
    }
}

fn table_row_get(
    trow: &TableRow,
    colarg: &eng::Argument,
    ty: &TableGetType,
    cx: Context,
) -> Result<(Value, eng::Environment)> {
    let colname = colarg.resolve(|| Value::Nil, &cx).and_then(Str::try_from)?;
    let idx = trow.idx;
    let entry = trow.entry(colname.as_str(), &colarg.tag)?;
    let v = match ty {
        TableGetType::Default(x) => {
            let entry: Value = entry.into();
            if &entry.ty() != x.out_ty() {
                x.resolve(|| Value::Nil, &cx)
            } else {
                Ok(entry)
            }
        }
        TableGetType::Flag(x) => TableRow::cnv_value(entry, x, idx, &colname, &colarg.tag),
    };

    v.and_then(|x| cx.done(x))
}

struct FieldAccessor(usize);

impl FieldAccessor {
    /// Construct a field accessor for the type `ty`. Returns the accessor and the return type of
    /// the field.
    fn construct(ty: &Type, field_arg: &eng::Argument, err_tag: &Tag) -> Result<(Self, Type)> {
        match ty {
            Ty::Def(tydef) => {
                // TypeDefs can use `get` to access a field, so only works for product types.
                // The field is checked, then the accessor index is passed through for the eval Step
                if !matches!(tydef.structure(), types::TypeVariant::Product(_)) {
                    let mut err = Error::wrong_input_type(ty, err_tag);
                    err.help_msg = Some("types with `sum` structure cannot be queried into".into());
                    return Err(err);
                }

                let fields = match tydef.structure() {
                    types::TypeVariant::Product(fields) => fields,
                    _ => unreachable!("just checked that we are on Product type"),
                };

                let field_name = field_arg.extract_literal::<Str>()?.as_str();

                let (idx, field) = fields
                    .iter()
                    .enumerate()
                    .find(|(_, f)| f.name().str() == field_name)
                    .ok_or_else(|| Error::field_not_found(&field_arg.tag, tydef))?;

                let out_ty = field.ty().clone();
                Ok((FieldAccessor(idx), out_ty))
            }
            x => Err(Error::wrong_input_type(x, err_tag)),
        }
    }

    fn get(&self, val: Value) -> Result<Value> {
        let mut x: OgmaData = val.try_into()?;
        Ok(if let Some(x) = x.get_mut() {
            x.data.remove(self.0)
        } else {
            x.data[self.0].clone()
        })
    }
}

// ------ Input ----------------------------------------------------------------
fn in_help() -> HelpMessage {
    HelpMessage {
        desc: "sets the input value for the next pipeline block".into(),
        params: vec![HelpParameter::Required("input".into())],
        examples: vec![
            HelpExample {
                desc: "feed in a number",
                code: "\\ 3.14",
            },
            HelpExample {
                desc: "feed in a string",
                code: "\\ 'hello, world!'",
            },
        ],
        ..HelpMessage::new("\\")
    }
}

fn in_intrinsic(mut blk: Block) -> Result<Step> {
    let arg = blk.next_arg(None)?;
    blk.eval(arg.out_ty().clone(), move |val, cx| {
        arg.resolve(|| val, &cx).and_then(|x| cx.done(x))
    })
}

// ------ Length ---------------------------------------------------------------
fn len_help() -> HelpMessage {
    HelpMessage {
        desc: "return the length of a table or string (chars)
table length **does not include header row**"
            .into(),
        flags: vec![("cols", "return the number of columns in a table")],
        examples: vec![
            HelpExample {
                desc: "return the number of files on the filesystem",
                code: "ls | filter type --Str eq file | len",
            },
            HelpExample {
                desc: "columns in the ls table",
                code: "ls | len --cols",
            },
            HelpExample {
                desc: "length of a string",
                code: "\\ 'Hello, 🌎!' | len",
            },
        ],
        ..HelpMessage::new("len")
    }
}

fn len_intrinsic(mut blk: Block) -> Result<Step> {
    match blk.in_ty() {
        Ty::Str => blk.eval_o(|i, cx| {
            Str::try_from(i)
                .map(|s| s.chars().count())
                .map(Number::from)
                .and_then(|x| cx.done_o(x))
        }),
        Ty::Tab => {
            let cols = blk.get_flag("cols").is_some();
            blk.eval_o(move |t, cx| {
                Table::try_from(t)
                    .map(|t| {
                        if cols {
                            t.cols_len()
                        } else {
                            t.rows_len().saturating_sub(1)
                        }
                    })
                    .map(Number::from)
                    .and_then(|x| cx.done_o(x))
            })
        }
        x => Err(Error::wrong_input_type(x, &blk.op_tag)),
    }
}

// ------ Let ------------------------------------------------------------------
fn let_help() -> HelpMessage {
    HelpMessage {
        desc: "assign variable identifiers to expression results
each binding takes the form `<expr> $var`
optionally a final `$var` can be specified which assigns the input
to `$var` and throughputs the input as the output
variables are scoped to within the expression they are defined"
            .into(),
        params: vec![
            HelpParameter::Optional("<expr-1> $var-1".into()),
            HelpParameter::Optional("<expr-2> $var-2".into()),
            HelpParameter::Required("...".into()),
            HelpParameter::Optional("$var-final".into()),
        ],
        examples: vec![
            HelpExample {
                desc: "assign $x to the number 5",
                code: "\\ 5 | let $x",
            },
            HelpExample {
                desc: "assign $x to 1, $y to 2, $z to 3",
                code: "\\ 6 | let {- 5} $x {/ 3} $y {* 0.5} $z",
            },
            HelpExample {
                desc: "assign $x to double input, assign $y to input and pass through",
                code: "let {* 2} $x $y",
            },
        ],
        ..HelpMessage::new("let")
    }
}

fn let_intrinsic(mut blk: Block) -> Result<Step> {
    type Binding = (eng::Variable, eng::Argument);
    let mut bindings = Vec::with_capacity(blk.args_len() / 2);

    while blk.args_len() > 1 {
        let e = blk.next_arg(None)?;
        let v = blk.create_var_ref(e.out_ty().clone())?;
        bindings.push((v, e));
    }

    // if there is a trailing binding, the input is bound to that variable, and passed through the
    // block as the output. if not, `let` returns the input type!

    let ty = blk.in_ty().clone();

    let trailing_binding = if blk.args_len() > 0 {
        let v = blk.create_var_ref(ty.clone())?;
        Some(v)
    } else {
        None
    };

    fn bind_vars(bindings: &[Binding], value: &Value, cx: &mut Context) -> Result<()> {
        for (var, e) in bindings {
            let v = e.resolve(|| value.clone(), cx)?;
            var.set_data(&mut cx.env, v);
        }
        Ok(())
    }

    blk.eval(ty, move |value, mut cx| {
        bind_vars(&bindings, &value, &mut cx)?;
        if let Some(trailing_var) = &trailing_binding {
            trailing_var.set_data(&mut cx.env, value.clone());
        }
        cx.done(value)
    })
}

// ------ ListFs ---------------------------------------------------------------
fn ls_help() -> HelpMessage {
    HelpMessage {
        desc: "list out aspects of the input
input is Nil; outputs the filesystem contents in the current working dir
input is Table; outputs the headers as a table"
            .into(),
        params: vec![HelpParameter::Optional("path".into())],
        examples: vec![
            HelpExample {
                desc: "list the current working directory items",
                code: "ls",
            },
            HelpExample {
                desc: "list directory items in `path`",
                code: "ls path/to",
            },
            HelpExample {
                desc: "list headers in table",
                code: "open table.csv | ls",
            },
        ],
        ..HelpMessage::new("ls")
    }
}

fn ls_intrinsic(mut blk: Block) -> Result<Step> {
    let blk_tag = blk.blk_tag.clone();
    match blk.in_ty() {
        Ty::Tab => blk.eval_o(move |input, cx| {
            Table::try_from(input)
                .and_then(|t| {
                    t.row(0)
                        .ok_or_else(|| Error::empty_table("", &blk_tag))
                        .map(|r| once(o("header")).chain(r.cloned()).map(|x| vec![x]))
                        .map(|x| x.collect::<Vec<_>>())
                })
                .map(::table::Table::from)
                .map(Table::from)
                .and_then(|x| cx.done_o(x))
        }),
        _ => {
            let path = if blk.args_len() > 0 {
                Some(blk.next_arg(Type::Nil)?.returns(&Type::Str)?)
            } else {
                None
            };

            blk.eval_o(move |_, cx| {
                if let Some(path) = &path {
                    let path: Str = path.resolve(|| Value::Nil, &cx)?.try_into()?;
                    make_dir_table(cx.wd.join(path.as_str()), &blk_tag)
                } else {
                    make_dir_table(cx.wd, &blk_tag)
                }
                .and_then(|x| cx.done_o(x))
            })
        }
    }
}

fn make_dir_table<P: AsRef<std::path::Path>>(dir: P, blk_tag: &Tag) -> Result<Table> {
    use std::iter::*;
    use Entry::*;

    let o = |s: &str| Obj(Str::new(s));

    let mut table = ::table::DataTable::from(vec![vec![
        o("name"),
        o("type"),
        o("size"),
        o("ext"),
        o("modified"),
    ]]);
    table.header = true;

    for entry in dir
        .as_ref()
        .read_dir()
        .map_err(|e| Error::io(blk_tag, e))?
        .filter_map(|x| x.ok())
    {
        let row = once(o(entry.file_name().to_str().unwrap_or("")));
        if let Ok(meta) = entry.metadata() {
            let row = row
                .chain(once(if meta.is_dir() {
                    o("dir")
                } else if meta.is_file() {
                    o("file")
                } else {
                    Nil
                }))
                .chain(once(Num(meta.len().into())))
                .chain(once(
                    entry
                        .path()
                        .extension()
                        .and_then(|x| x.to_str())
                        .map(o)
                        .unwrap_or(Nil),
                ))
                .chain(once(
                    meta.modified().map(fmt_systime).map(Obj).unwrap_or(Nil),
                ));

            table.add_row(row);
        } else {
            table.add_row(row);
        }
    }

    table.sort(0, |x, y| x.partial_cmp(y).unwrap());

    Ok(table.map_obj(Value::Str).into()) // convert to Table<Value>
}

fn fmt_systime(systime: std::time::SystemTime) -> Str {
    let fmt = &time::macros::format_description!("[year].[month].[day] [hour][minute]");
    let dt = time::OffsetDateTime::from(systime);
    dt.format(fmt).unwrap_or_default().into()
}

// ------ Nth ------------------------------------------------------------------
fn nth_help() -> HelpMessage {
    HelpMessage {
        desc: "retrieve the nth element of a data structure
String: retrieves the nth character
Table: retrieves the nth row and applies the expression"
            .into(),
        params: vec![
            HelpParameter::Required("index".into()),
            HelpParameter::Optional("expr".into()),
        ],
        examples: vec![
            HelpExample {
                desc: "get the first row of a table",
                code: "nth 0 {get col-name}",
            },
            HelpExample {
                desc: "get the 2nd last row of a table",
                code: "nth {len | - 2} {get col-name}",
            },
            HelpExample {
                desc: "get the 10th character of a string",
                code: "\\ 'Hello, world!' | nth 10",
            },
        ],
        ..HelpMessage::new("nth")
    }
}

fn nth_intrinsic(mut blk: Block) -> Result<Step> {
    match blk.in_ty() {
        Ty::Tab => {
            let n = blk.next_arg(None)?.returns(&Ty::Num)?;
            let expr = blk.next_arg(Ty::TabRow)?;
            let oty = expr.out_ty().clone();
            blk.eval(oty, move |table, cx| {
                // nth is adj by one to account for header
                let nth = n
                    .resolve(|| table.clone(), &cx)
                    .and_then(|v| cnv_num_to_uint::<usize>(v, &n.tag))?;
                let table = Table::try_from(table)?;
                if nth + 1 >= table.rows_len() {
                    return Err(Error::eval(
                        &n.tag,
                        "index is outside table bounds",
                        format!("this resolves to `{}`", nth),
                        None,
                    ));
                }

                let trow = TableRow::new(table, Default::default(), nth + 1);
                expr.resolve(|| trow.into(), &cx).and_then(|v| cx.done(v))
            })
        }
        Ty::Str => {
            let n = blk.next_arg(None)?.returns(&Ty::Num)?;
            blk.eval_o::<_, Str>(move |string, cx| {
                let nth = n
                    .resolve(|| string.clone(), &cx)
                    .and_then(|v| cnv_num_to_uint::<usize>(v, &n.tag))?;
                Str::try_from(string)
                    .and_then(|s| {
                        s.chars().nth(nth).ok_or_else(|| {
                            Error::eval(
                                &n.tag,
                                "index is outside string bounds",
                                format!("this resolves to `{}`", nth),
                                None,
                            )
                        })
                    })
                    .map(String::from)
                    .map(Str::from)
                    .and_then(|x| cx.done_o(x))
            })
        }
        x => Err(Error::wrong_input_type(x, &blk.op_tag)),
    }
}

// ------ Open -----------------------------------------------------------------
fn open_help() -> HelpMessage {
    HelpMessage {
        desc: "open something
Table (default): parse file as a table
String: reads file as string"
            .into(),
        params: vec![HelpParameter::Required("file".into())],
        flags: vec![(
            "<type>",
            "open file as type. defaults to Table if not specified",
        )],
        examples: vec![
            HelpExample {
                desc: "open a csv as a table",
                code: "open file.csv",
            },
            HelpExample {
                desc: "open a file along a path",
                code: "open 'path/to a/file.csv'",
            },
            HelpExample {
                desc: "open a file as a string",
                code: "open --Str foo.txt",
            },
        ],
        ..HelpMessage::new("open")
    }
}

fn open_intrinsic(mut blk: Block) -> Result<Step> {
    let blktag = blk.blk_tag.clone();
    let arg = blk.next_arg(None)?.returns(&Ty::Str)?;
    let as_ty = type_flag(&mut blk, Ty::Tab)?;

    match as_ty {
        Ty::Tab => blk.eval_o(move |val, cx| {
            // TODO make this better at reading in tables:
            // 1. Recognise extension to choosing deserializing method?
            // 2. Use a flag to choose deserializing method?
            // 3. Support more than just comma for dsv types

            let p: Str = arg.resolve(|| val, &cx)?.try_into()?;
            let path = scrub_filepath(&p, &cx).map_err(|e| Error::io(&blktag, e))?;
            let table = match FSCACHE.get::<Table>(&path) {
                Some(table) => table,
                None => {
                    let s: Str = read_file(&path).map_err(|e| Error::io(&blktag, e))?.into();

                    let table = Table::from(
                        ::table::parse_dsv(',', &s).map_obj(|s| Value::Str(Str::new(s))),
                    );
                    FSCACHE.insert(&path, table.clone());
                    table
                }
            };

            cx.done_o(table)
        }),
        Ty::Str => blk.eval_o(move |val, cx| {
            let p: Str = arg.resolve(|| val, &cx)?.try_into()?;
            let path = scrub_filepath(&p, &cx).map_err(|e| Error::io(&blktag, e))?;
            let s = match FSCACHE.get::<Str>(&path) {
                Some(s) => s,
                None => {
                    let s: Str = read_file(&path).map_err(|e| Error::io(&blktag, e))?.into();

                    FSCACHE.insert(&path, s.clone());
                    s
                }
            };
            cx.done_o(s)
        }),
        x => Err(Error {
            help_msg: None,
            ..Error::wrong_input_type(&x, &blk.op_tag)
        }),
    }
}

/// Read a file to a String, but not necessarily from UTF-8
fn read_file(path: impl AsRef<std::path::Path>) -> io::Result<String> {
    use ::encoding::{all::UTF_8, decode, DecoderTrap};

    decode(&std::fs::read(path)?, DecoderTrap::Strict, UTF_8)
        .0
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
}

// ------ Rand -----------------------------------------------------------------
fn rand_help() -> HelpMessage {
    HelpMessage {
        desc: "return a random number
rand has four ways of calling:
1. Without arguments: this returns a number (0,1],
2. With one argument: this returns a number (0,to],
3. With two arguments: this returns a number (from,to],
4. With three arguments: this returns a table populated with random numbers (from,to]"
            .into(),
        params: vec![
            HelpParameter::Optional("from".into()),
            HelpParameter::Optional("to".into()),
            HelpParameter::Optional("length".into()),
        ],
        examples: vec![
            HelpExample {
                desc: "random integer from 0 to 9",
                code: "rand 0 10 | floor",
            },
            HelpExample {
                desc: "create 10 random numbers",
                code: "rand 0 1 10",
            },
        ],
        ..HelpMessage::new("rand")
    }
}

fn rand_intrinsic(mut blk: Block) -> Result<Step> {
    let args = blk.args_len();
    let mut next_num = || {
        blk.next_arg(None)
            .and_then(|x| x.returns(&Ty::Num))
            .map(Some)
    };

    let (from, to, len) = match args {
        1 => (None, next_num()?, None),
        2 => (next_num()?, next_num()?, None),
        3 => (next_num()?, next_num()?, next_num()?),
        _ => (None, None, None),
    };

    fn bnd(arg: Option<&eng::Argument>, i: &mut Value, cx: &Context, def: f64) -> Result<f64> {
        match arg {
            Some(x) => Ok(Number::try_from(x.resolve(|| i.clone(), cx)?)?.as_f64()),
            None => Ok(def),
        }
    }

    let tag = blk.op_tag.clone();

    if args == 3 {
        let len = len.unwrap();
        blk.eval_o(move |mut i, cx| {
            let f = bnd(from.as_ref(), &mut i, &cx, 0.0)?;
            let t = bnd(to.as_ref(), &mut i, &cx, 1.0)?;
            let d = t - f;
            let len: usize = cnv_num_to_uint(len.resolve(|| i, &cx)?, &len.tag)?;
            check_from_lt_to(f, t, &tag)?;
            let mut table = InnerTable::new();
            let rng = fastrand::Rng::new();
            table
                .add_col(once(o("rand")).chain(repeat_with(|| rng.f64() * d + f).take(len).map(n)));
            cx.done_o(Table::from(table))
        })
    } else {
        blk.eval_o(move |mut i, cx| {
            let f = bnd(from.as_ref(), &mut i, &cx, 0.0)?;
            let t = bnd(to.as_ref(), &mut i, &cx, 1.0)?;
            let d = t - f;
            check_from_lt_to(f, t, &tag)?;
            cx.done_o(Number::from(fastrand::f64() * d + f))
        })
    }
}

fn check_from_lt_to(from: f64, to: f64, tag: &Tag) -> Result<()> {
    if from >= to {
        Err(Error::eval(
            tag,
            format!("from must be less than to. found from: {} to: {}", from, to),
            None,
            None,
        ))
    } else {
        Ok(())
    }
}

// ------ Range ----------------------------------------------------------------
fn range_help() -> HelpMessage {
    HelpMessage {
        desc: "create a single column table of integers (from,to]
`from` is inclusive, `to` is exclusive
`to` can be omitted if input is a number"
            .into(),
        params: vec![
            HelpParameter::Required("from".into()),
            HelpParameter::Optional("to".into()),
        ],
        examples: vec![
            HelpExample {
                desc: "integers from 0 to 9",
                code: "range 0 10",
            },
            HelpExample {
                desc: "the five preceding numbers",
                code: "\\ 10 | range - 5",
            },
        ],
        ..HelpMessage::new("range")
    }
}

fn range_intrinsic(mut blk: Block) -> Result<Step> {
    fn table_range(from: u128, to: u128) -> Table {
        let mut t = vec![vec![o("i")]];
        t.par_extend((from..to).into_par_iter().map(|x| vec![n(x)]));
        Table::from(::table::Table::from(t))
    }

    let from = blk.next_arg(None)?.returns(&Type::Num)?;
    let alen = blk.args_len();
    match (alen, blk.in_ty()) {
        (0, Ty::Num) => {
            let blktag = blk.blk_tag.clone();
            blk.eval_o(move |input, cx| {
                let from = from
                    .resolve(|| input.clone(), &cx)
                    .and_then(|n| cnv_num_to_uint(n, &from.tag))?;
                let to = cnv_num_to_uint(input, &blktag)?;
                cx.done_o(table_range(from, to))
            })
        }
        _ => {
            let to = blk.next_arg(None)?.returns(&Type::Num)?;
            blk.eval_o(move |input, cx| {
                let from = from
                    .resolve(|| input.clone(), &cx)
                    .and_then(|n| cnv_num_to_uint(n, &from.tag))?;
                let to = to
                    .resolve(|| input.clone(), &cx)
                    .and_then(|n| cnv_num_to_uint(n, &to.tag))?;
                cx.done_o(table_range(from, to))
            })
        }
    }
}

// ------ Save -----------------------------------------------------------------
fn save_help() -> HelpMessage {
    HelpMessage {
        desc: "save the input to a file
table input is saved as comma separated values"
            .into(),
        params: vec![HelpParameter::Required("file".into())],
        examples: vec![
            HelpExample {
                desc: "save table as a csv",
                code: "open file1.csv | save file2.csv",
            },
            HelpExample {
                desc: "save text as a string",
                code: "\\ 'Hello, world!' | save hello-world.txt",
            },
        ],
        ..HelpMessage::new("save")
    }
}

fn save_intrinsic(mut blk: Block) -> Result<Step> {
    let ty = blk.in_ty().clone();
    if ty == Ty::TabRow {
        return Err(Error::wrong_input_type(&ty, &blk.op_tag));
    }

    let filepath = blk.next_arg(None)?.returns(&Ty::Str)?;
    let blktag = blk.blk_tag.clone();
    blk.eval(ty, move |val, cx| {
        let p: Str = filepath.resolve(|| val.clone(), &cx)?.try_into()?;
        let p = cx.root.join(cx.wd).join(p.as_str());
        // check path doesn't go beyond root. can't use scrub_filepath as this uses
        // canonicalization for checking
        {
            use std::path::Component::*;
            let x = p.components().fold(0i32, |x, c| {
                x + match c {
                    RootDir => std::i32::MIN,
                    CurDir => 0,
                    ParentDir => -1,
                    _ => 1,
                }
            }); // there is always one for the file name
            if x <= 0 {
                Err(io::Error::new(
                    io::ErrorKind::Other,
                    "cannot move above root directory",
                ))
            } else {
                Ok(())
            }
        }
        .and_then(|_| mkdirs(&p).and_then(|_| std::fs::File::create(p)))
        .and_then(|mut file| write_file(&mut file, val.clone()))
        .map_err(|e| Error::io(&blktag, e))?;
        cx.done(val)
    })
}

fn mkdirs<P: AsRef<std::path::Path>>(p: P) -> io::Result<()> {
    let p = p.as_ref();
    if let Some(p) = p.parent() {
        if !p.exists() {
            std::fs::create_dir_all(p)?;
        }
    }
    Ok(())
}

fn write_file<W: Write>(file: &mut W, value: Value) -> io::Result<()> {
    use ::numfmt::*;
    fn fmt_cell<WW: Write>(
        wtr: &mut WW,
        entry: &Entry<Value>,
        fmtr: &mut Formatter,
    ) -> io::Result<()> {
        match entry {
            Entry::Obj(Value::Nil) | Entry::Nil => Ok(()), // don't write anything
            e => {
                let s = print::fmt_cell(e, fmtr);
                // if s contains commas or new lines need to escape it.
                if s.contains(&[',', '"', '\r', '\n'] as &[_]) {
                    write!(wtr, "\"{}\"", s.escape_debug())
                } else {
                    write!(wtr, "{}", s)
                }
            }
        }
    }

    let fmtr = &mut Formatter::new();
    match value {
        Value::Tab(table) => {
            let mut add_newline = false;
            for row in table.rows() {
                if add_newline {
                    writeln!(file)?;
                }
                add_newline |= true;
                let mut add_comma = false;
                for entry in row {
                    if add_comma {
                        write!(file, ",")?;
                    }
                    add_comma |= true;
                    fmt_cell(file, entry, fmtr)?;
                }
            }
        }
        x => {
            let x = print::fmt_cell(&Entry::from(x), fmtr);
            write!(file, "{}", x)?;
        }
    }
    Ok(())
}

// ------ Table ctor -----------------------------------------------------------
fn table_help() -> HelpMessage {
    variadic_help(
        "Table",
        "create an empty table with the given table headers",
        vec![
            HelpExample {
                desc: "create an empty table",
                code: "Table",
            },
            HelpExample {
                desc: "create table with the headers 'Foo' and 'Bar'",
                code: "Table 'Foo' 'Bar'",
            },
        ],
    )
}

fn table_intrinsic(mut blk: Block) -> Result<Step> {
    // table takes zero or more arguments that resolve to Str (header name)
    let mut names = Vec::with_capacity(blk.args_len());
    for _ in 0..blk.args_len() {
        names.push(blk.next_arg(None)?.returns(&Ty::Str)?);
    }

    blk.eval_o(move |i, cx| {
        let mut t = table::Table::new();
        for name in &names {
            t.add_col(once(name.resolve(|| i.clone(), &cx)?));
        }
        cx.done_o(Table::from(t))
    })
}

// ------ To Str ---------------------------------------------------------------
fn to_str_help() -> HelpMessage {
    HelpMessage {
        desc: "convert the input into a string".into(),
        ..HelpMessage::new("to-str")
    }
}

fn to_str_intrinsic(blk: Block) -> Result<Step> {
    blk.eval_o(|v, cx| {
        cx.done_o(print::fmt_cell(
            &Entry::from(v),
            &mut numfmt::Formatter::default(),
        ))
    })
}

// ------ Tuple ----------------------------------------------------------------
fn tuple_help() -> HelpMessage {
    variadic_help(
        "Tuple",
        "construct a tuple of the result of each expression
tuples impl `eq` and `cmp` if all its fields also implement `eq` and `cmp`
tuples have unique types: `U_<t0_Ty>-<t1_Ty>_`
access of the fields is using `get t#` with the field number",
        vec![
            HelpExample {
                desc: "create a two element tuple of numbers. type: U_Num-Num_",
                code: "Tuple 1 2",
            },
            HelpExample {
                desc: "create 3 numbers after input. type: U_Num-Num-Num_",
                code: "\\ 3 | Tuple {+ 1} {+ 2} {+ 3}",
            },
            HelpExample {
                desc: "tuples are heterogeneous. type: U_Num-Str-Bool_",
                code: "Tuple 1 'foo' #t",
            },
            HelpExample {
                desc: "get the first and third element",
                code: "Tuple 1 'foo' 2 | + {get t0} {get t2}",
            },
        ],
    )
}

fn tuple_intrinsic(mut blk: Block) -> Result<Step> {
    let len = blk.args_len();
    if len < 2 {
        return Err(Error::insufficient_args(&blk.blk_tag, len));
    }
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(blk.next_arg(None)?);
    }

    let ty = Arc::new(Tuple::ty(v.iter().map(|x| x.out_ty().clone()).collect()));

    blk.eval(Type::Def(ty.clone()), move |input, cx| {
        let mut data = Vec::with_capacity(v.len());
        for arg in &v {
            data.push(arg.resolve(|| input.clone(), &cx)?);
        }
        cx.done(OgmaData::new(ty.clone(), None, data))
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn write_file_testing() {
        let f = |v| {
            let mut wtr = Vec::new();
            write_file(&mut wtr, v).unwrap();
            String::from_utf8(wtr).unwrap()
        };
        let s = |s| Entry::Obj(Value::Str(Str::new(s)));
        let n = |n: f64| Entry::Num(n.into());

        let t = |v| Value::Tab(Table::from(::table::Table::from(v)));

        assert_eq!(&f(Value::Bool(true)), "true");
        assert_eq!(&f(Value::Num((3.14).into())), "3.14");
        assert_eq!(&f(Value::Str("Hello, world!".into())), "Hello, world!");
        assert_eq!(
            &f(t(vec![
                vec![n(1.5e6), n(2.5)],
                vec![s("foo"), Entry::Nil, s("foo\nbar")],
                vec![n(3.6e9), s("foo,bar"), s("foo \"zog\" bar")]
            ])),
            r#"1500000.0,2.5,
foo,,"foo\nbar"
3600000000.0,"foo,bar","foo \"zog\" bar""#
        );
    }
}

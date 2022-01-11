use ::kserd::Number;
use ::libs::{divvy::Str, fastrand, rayon::prelude::*};
use ::table::Entry;
use std::{
    iter::*,
    io::{self, Write},
    cell::RefCell,
    fmt,
    path,
    cmp,
    collections::BTreeMap,
    convert::{TryFrom, TryInto},
    mem,
    rc::Rc,
    time::Instant,
};
use crate::prelude::*;
use lang::help::*;
use eng::{Context, Block, Step};
use ast::{Tag, Location};
use rt::fscache::FSCACHE;
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
        use ::paste::paste;

        let mut implementations = Implementations {
            impls: HashMap::default(),
            names: HashMap::default(),
        };
        let impls = &mut implementations;

        macro_rules! add {
            ($cmd:tt, $cat:ident) => {{
                add!($cmd, $cmd, $cat)
            }};
            ($cmd:literal, $inner:tt, $cat:ident) => {{
                paste! { add!($cmd, [<$inner _intrinsic>], $cat, [<$inner _help>]) }
            }};
            ($cmd:tt, $inner:tt, $cat:ident) => {{
                paste! { add!(stringify!($cmd), [<$inner _intrinsic>], $cat, [<$inner _help>]) }
            }};
            ($cmd:expr, $fn:path, $cat:ident, $help:path) => {{
                impls.insert_intrinsic(
                    $cmd,
                    None,
                    $fn,
                    Location::Ogma,
                    OperationCategory::$cat,
                    $help(),
                );
            }};
        }

        // Arithmetic ------------------------------------------
        add!(+, add, Arithmetic);
        add!(*, mul, Arithmetic);
        add!("×", mul, Arithmetic);
        add!("-", sub, Arithmetic);
        add!(/, div, Arithmetic);
        add!("÷", div, Arithmetic);
        add!(ceil, Arithmetic);
        add!(floor, Arithmetic);
        add!("is-finite", isfinite, Arithmetic);
        add!(root, Arithmetic);
        // Cmp -------------------------------------------------
        add!(cmp, Cmp);
        add!(eq, Cmp);
        add!(max, Cmp);
        add!(min, Cmp);
        // Logic -----------------------------------------------
        add!(and, Logic);
        add!(if, Logic);
        add!(not, Logic);
        add!(or, Logic);
        // Morphism --------------------------------------------
        add!(append, Morphism);
        add!("append-row", append_row, Morphism);
        add!(dedup, Morphism);
        add!(filter, Morphism);
        add!(fold, Morphism);
        add!("fold-while", fold_while, Morphism);
        add!(grp, Morphism);
        add!("grp-by", grpby, Morphism);
        add!(map, Morphism);
        add!(pick, Morphism);
        add!(ren, Morphism);
        add!("ren-with", ren_with, Morphism);
        add!(rev, Morphism);
        add!(skip, Morphism);
        add!(sort, Morphism);
        add!("sort-by", sortby, Morphism);
        add!(take, Morphism);
        // Pipeline --------------------------------------------
        add!(benchmark, Pipeline);
        add!(get, Pipeline);
        add!(
            ".",
            ast::DotOperatorBlock::instrinsic,
            Pipeline,
            ast::DotOperatorBlock::help
        );
        add!("\\", in, Pipeline);
        add!(len, Pipeline);
        add!(let, Pipeline);
        add!(nth, Pipeline);
        add!(rand, Pipeline);
        add!(range, Pipeline);
        add!(Table, table, Pipeline);
        add!("to-str", to_str, Pipeline);
        add!(Tuple, tuple, Pipeline);
        // Io --------------------------------------------------
        add!(ls, Io);
        add!(open, Io);
        add!(save, Io);

        // ---- Specialised instrinsic ops --------------

        implementations
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

fn variadic_intrinsic_num<F>(blk: Block, f: F) -> Result<Step>
where
    F: Fn(f64, f64) -> f64 + Sync + 'static,
{
    variadic_intrinsic::<Number, _>(blk, move |prev, next| {
        let x = prev
            .map(|prev| f(prev.as_f64(), next.as_f64()))
            .map(Into::into)
            .unwrap_or(next);
        (x, false)
    })
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
    env: var::Environment,
    rhs: var::Variable,
    evaluator: eng::ExprEvaluator,
    transformation: T,
}

struct BinaryOpRef<'a, T> {
    env: var::Environment,
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
        let mut locals = var::Locals::default();
        // create the $rhs to be set in the new env
        let rhs = locals.add_new_var("rhs".into(), ty.clone(), var);
        // construct the expr evaluator
        // this uses the pseudo-env and the expr we construct, with an input of the type.
        // if the impl of <cmd> on type does not conform to expectations an error will occur
        let evaluator =
            eng::construct_evaluator(ty.clone(), expr, defs, locals.clone()).map_err(|_| {
                Error {
                    cat: err::Category::Semantics,
                    desc: format!(
                        "`{}` implementation not suitable for `{}` with `{}`",
                        cmd, caller, ty
                    ),
                    traces: vec![err::ErrorTrace::from_tag(
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
            err.traces.push(err::ErrorTrace::from_tag(
                errtag,
                format!("`{}`'s {} impl returns `{}`", ty, cmd, evaluator.ty()),
            ));
            return Err(err);
        }

        Ok(Self {
            env: var::Environment::new(locals),
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
    let map_field = |f: &types::Field| HelpParameter::Required(format!("{}:{}", f.name(), f.ty()).into());

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

// ------ Add ------------------------------------------------------------------
fn add_help() -> HelpMessage {
    HelpMessage {
        desc: "add arguments together
if input is a Table, concat or join additional tables
-variadic-: more than one argument can be specified"
            .into(),
        params: vec![HelpParameter::Required("args..".into())],
        flags: vec![
            ("cols", "join tables (append columns)"),
            ("union", "expand table to capture all data (default)"),
            (
                "intersect",
                "use minimum size of table; min rows for --cols, min cols for concat rows",
            ),
        ],
        examples: vec![
            HelpExample {
                desc: "add 2 to 1",
                code: "\\ 1 | + 2",
            },
            HelpExample {
                desc: "add multiple numbers together",
                code: "+ 1 2 3 4 5",
            },
            HelpExample {
                desc: "add two tables together, concatenating rows",
                code: "range 0 10 | + range 10 20",
            },
            HelpExample {
                desc: "index filesystem items, shrink table to min rows",
                code: "range 0 1000 | + --cols --intersect ls",
            },
        ],
        ..HelpMessage::new("+")
    }
}

fn add_intrinsic(blk: Block) -> Result<Step> {
    match blk.in_ty() {
        Ty::Str => variadic_intrinsic::<Str, _>(blk, |prev, next| {
            (
                prev.map(|mut s| {
                    s.to_mut().push_str(&next);
                    s
                })
                .unwrap_or(next),
                false,
            )
        }),
        Ty::Tab => add_table(blk),
        _ => variadic_intrinsic_num(blk, std::ops::Add::add),
    }
}

fn add_table(mut blk: Block) -> Result<Step> {
    let mut f = |s| blk.get_flag(s).is_some();
    let byrow = !f("cols");
    let intersect = !f("union") && f("intersect");

    variadic_intrinsic(blk, move |prev, next| match prev {
        Some(prev) => (add_table2(prev, next, byrow, intersect), false),
        None => (next, false),
    })
}

fn add_table2(prev: Table, next: Table, byrow: bool, intersect: bool) -> Table {
    if byrow {
        add_table_by_row(prev, next, intersect)
    } else {
        add_table_by_col(prev, next, intersect)
    }
}

fn add_table_by_row(mut prev: Table, next: Table, intersect: bool) -> Table {
    // prev has priority for column names
    let table = prev.make_mut();
    let (pc, nc) = (table.cols_len(), next.cols_len());

    if intersect {
        let take = cmp::min(pc, nc);
        table.add_rows(next.rows().skip(1).map(|x| x.take(take).cloned()));
        if nc < pc {
            // remove additional columns in prev
            for col in (nc..pc).rev() {
                table.remove_col_par(col);
            }
        }
    } else {
        // if table is empty there would be no headers, which would make the adding logic flawed.
        // however if table is empty it is easy to just return the `next` table!
        if table.is_empty() {
            return next;
        } else {
            table.add_rows(next.rows().skip(1).map(|x| x.cloned()));
            if nc > pc {
                // name the added cols
                for col in pc..nc {
                    if let Some(h) = table
                        .col_mut(col)
                        .expect("add_rows should extend cols")
                        .next()
                    {
                        *h = next.col(col).unwrap().next().cloned().unwrap_or_default();
                    }
                }
            }
        }
    }

    prev
}

fn add_table_by_col(mut prev: Table, next: Table, intersect: bool) -> Table {
    // prev has priority for column names
    let table = prev.make_mut();
    let (pr, nr) = (table.rows_len(), next.rows_len());

    if intersect {
        let take = cmp::min(pr, nr);
        table.add_cols(next.cols().map(|x| x.take(take).cloned()));
        if nr < pr {
            // remove additional rows in prev in REVERSE
            for row in (nr..pr).rev() {
                table.remove_row(row);
            }
        }
    } else {
        table.add_cols(next.cols().map(|x| x.cloned())); // additional rows are padded
    }

    prev
}

// ------ And ------------------------------------------------------------------
fn and_help() -> HelpMessage {
    variadic_help(
        "and",
        "returns true if all arguments are true",
        vec![HelpExample {
            desc: "10 is less than 20 and equal to 10",
            code: "\\ 10 | and { < 20 } { = 10 }",
        }],
    )
}

fn and_intrinsic(blk: Block) -> Result<Step> {
    variadic_intrinsic::<bool, _>(blk, |prev, next| {
        let x = prev.unwrap_or(true);
        let x = x && next;
        (x, !x) // short circuit if x is false
    })
}

// ------ Append ---------------------------------------------------------------
fn append_help() -> HelpMessage {
    HelpMessage{
        desc: "add new columns onto a table using one or more expressions
each expression adds a new column, populated by row with the result of the expression
tags can be optionally specified to name the columns".into(),
        params: vec![HelpParameter::Required("args..".into())],
        flags: vec![("<col-names>", "name each column in order of expression")],
        examples: vec![
            HelpExample {
                desc: "flag if a filesystem item is a file",
                code: "ls | append { get type --Str | eq file } --is-file",
            },
            HelpExample {
                desc: "add more than one column",
                code: "ls | append { get size | if { > 1e9 } 'big file' '' } { get ext --Str | eq csv }",
            },
        ],
        ..HelpMessage::new("append")
    }
}

fn append_intrinsic(mut blk: Block) -> Result<Step> {
    if blk.in_ty() != &Ty::Tab {
        return Err(Error::wrong_input_type(blk.in_ty(), &blk.op_tag));
    }

    let len = blk.args_len();
    if len == 0 {
        return Err(Error::insufficient_args(&blk.blk_tag, 0));
    }

    let mut cols = Vec::with_capacity(len);
    let mut auto = 1;
    for _ in 0..len {
        let arg = blk.next_arg(Ty::TabRow)?;
        let col = blk
            .get_flag(None)
            .map(|x| Str::new(x.str()))
            .unwrap_or_else(|| (format!("_append{}", auto).into(), auto += 1).0);
        cols.push((arg, col));
    }

    blk.eval_o(move |table, cx| {
        append_table(table.try_into()?, &cx, &cols).and_then(|x| cx.done_o(x))
    })
}

fn append_table(mut table: Table, cx: &Context, with: &[(eng::Argument, Str)]) -> Result<Table> {
    let rows = table.rows_len();
    // seed column buffers
    let mut to_append = with
        .iter()
        .map(|(_, n)| {
            let mut v = Vec::new();
            v.resize_with(rows, Default::default);
            if let Some(x) = v.get_mut(0) {
                *x = Entry::Obj(Value::Str(n.clone()));
            }
            v
        })
        .collect::<Vec<_>>();

    // calculate appending values
    // parallelised over the expressions _and_ the rows
    let err = crate::Mutex::new(None);
    to_append
        .par_iter_mut()
        .enumerate()
        .for_each(|(withidx, av)| {
            let predicate = with[withidx].0.resolver_sync(cx);
            if let Err(e) = par_over_tablerows(av, &table, cx, |a, _, trow| {
                *a = predicate(trow.into())?.into();
                Ok(())
            }) {
                *err.lock() = Some(e);
            }
        });

    // return any error found
    if let Some(e) = err.into_inner() {
        return Err(e);
    }

    // append to the column, if ref shared, clone with known expansion of cols
    let to_append = to_append.into_iter().map(|x| x.into_iter());
    if let Some(t) = table.get_mut() {
        t.add_cols(to_append);
    } else {
        let mut t = table.clone_with_col_capacity(table.cols_len() + with.len());
        t.add_cols(to_append);
        table = t.into();
    }

    Ok(table)
}

// ------ Append-Row -----------------------------------------------------------
fn append_row_help() -> HelpMessage {
    variadic_help(
        "append-row",
        "append a row to the table
the row is populated with the expression results",
        vec![HelpExample {
            desc: "append the row 1 2 3 to the table",
            code: "append-row 1 2 3",
        }],
    )
}

fn append_row_intrinsic(mut blk: Block) -> Result<Step> {
    if blk.in_ty() != &Ty::Tab {
        return Err(Error::wrong_input_type(blk.in_ty(), &blk.op_tag));
    }

    let len = blk.args_len();
    let mut cols = Vec::with_capacity(len);
    while blk.args_len() > 0 {
        cols.push(blk.next_arg(None)?);
    }

    blk.eval_o(move |table, cx| {
        let mut x = Vec::with_capacity(cols.len());
        for c in &cols {
            x.push(c.resolve(|| table.clone(), &cx)?);
        }

        let mut table: Table = table.try_into()?;
        let t = table.make_mut();
        t.add_row(x.into_iter());
        let mut i = 1;
        if let Some(hdr) = t.row_mut(0) {
            for e in hdr {
                if e.is_nil() {
                    *e = Value::Str(format!("_append{}", i).into()).into();
                    i += 1;
                }
            }
        }
        cx.done_o(table)
    })
}

// ------ Benchmark ------------------------------------------------------------
fn benchmark_help() -> HelpMessage {
    HelpMessage {
        desc: "time the expression evaluation\npipes <input> to <expr>".into(),
        params: vec![HelpParameter::Required("expr".into())],
        examples: vec![
            HelpExample {
                desc: "time loading in a file",
                code: "benchmark { open file.csv }",
            },
            HelpExample {
                desc: "time filtering a table",
                code: "\\ file.csv | benchmark filter = col 1",
            },
        ],
        ..HelpMessage::new("benchmark")
    }
}

fn benchmark_intrinsic(mut blk: Block) -> Result<Step> {
    let expr = blk.next_arg(None)?;
    blk.eval_o(move |val, cx| {
        let start = Instant::now();
        expr.resolve(|| val, &cx)?;
        cx.done_o(benchmark_table(start, Instant::now()))
    })
}

fn benchmark_table(start: Instant, end: Instant) -> Table {
    let d = end - start;
    let (ms, us) = (d.subsec_millis(), d.subsec_micros());
    let us = us - (ms * 1000);
    ::table::Table::from(vec![
        vec![
            o("duration"),
            o("seconds"),
            o("milliseconds"),
            o("microseconds"),
        ],
        vec![o(format!("{:?}", d)), n(d.as_secs()), n(ms), n(us)],
    ])
    .into()
}

// ------ Ceil -----------------------------------------------------------------
fn ceil_help() -> HelpMessage {
    HelpMessage {
        desc: "return the smallest integer greater than or equal to a number".into(),
        ..HelpMessage::new("ceil")
    }
}

fn ceil_intrinsic(blk: Block) -> Result<Step> {
    if blk.in_ty() != &Ty::Num {
        return Err(Error::wrong_input_type(blk.in_ty(), &blk.op_tag));
    }
    blk.eval_o(move |n, cx| {
        Number::try_from(n)
            .map(|n| n.as_f64().ceil())
            .and_then(|n| cx.done_o(Number::from(n)))
    })
}

// ------ Cmp ------------------------------------------------------------------
fn cmp_help() -> HelpMessage {
    HelpMessage {
        desc: "compare <rhs> to input".into(),
        params: vec![HelpParameter::Required("rhs".into())],
        examples: vec![HelpExample {
            desc: "compare 2 to 1",
            code: "\\ 1 | cmp 2",
        }],
        ..HelpMessage::new("cmp")
    }
}

fn cmp_intrinsic(mut blk: Block) -> Result<Step> {
    match blk.in_ty() {
        Ty::Nil => {
            blk.next_arg(None)?.returns(&Ty::Nil)?; // we don't use rhs but we do req its existence
            blk.eval_o(|_, cx| cx.done_o(cmp::Ordering::Equal))
        }
        Ty::Bool => {
            let rhs = blk.next_arg(None)?.returns(&Ty::Bool)?;
            blk.eval_o(move |lhs, cx| {
                let lhs: bool = lhs.try_into()?;
                let rhs: bool = rhs.resolve(|| lhs.into(), &cx)?.try_into()?;
                cx.done_o(lhs.cmp(&rhs))
            })
        }
        Ty::Num => {
            let rhs = blk.next_arg(None)?.returns(&Ty::Num)?;
            blk.eval_o(move |lhs, cx| {
                let lhs: Number = lhs.try_into()?;
                let rhs: Number = rhs.resolve(|| lhs.into(), &cx)?.try_into()?;
                cx.done_o(lhs.cmp(&rhs))
            })
        }
        Ty::Str => {
            let rhs = blk.next_arg(None)?.returns(&Ty::Str)?;
            blk.eval_o(move |lhs, cx| {
                let lhs: Str = lhs.try_into()?;
                let rhs: Str = rhs.resolve(|| lhs.clone().into(), &cx)?.try_into()?;
                cx.done_o(lhs.cmp(&rhs))
            })
        }
        Ty::Def(x) if x.as_ref() == "Ord" => {
            let ordty = Type::Def(types::ORD.get());
            let rhs = blk.next_arg(None)?.returns(&ordty)?;
            // cmp Ord to Ord returns another Ord
            blk.eval_o(move |lhs, cx| {
                let lhs_variant = lhs.variant_idx().expect("Ord type");
                let rhs = rhs.resolve(|| lhs, &cx)?.variant_idx().expect("Ord type");
                cx.done_o(lhs_variant.cmp(&rhs))
            })
        }
        Ty::Def(x) if x.name().str().starts_with("U_") => {
            let els = match x.structure() {
                types::TypeVariant::Product(x) => x.len(),
                _ => 0,
            };
            blk.next_arg_do_not_remove(None)?.returns(blk.in_ty())?; // this checks same lhs=rhs type
            let def =
                &lang::syntax::parse::definition_impl(build_tuple_cmp_def_str(els), Location::Ogma, blk.defs)
                    .map_err(|(e, _)| e)?;
            let ordty = Ty::Def(types::ORD.get());
            let evaltr = eng::DefImplEvaluator::build(&mut blk, def)?.returns(&ordty)?;
            blk.eval(ordty, move |input, cx| {
                evaltr.eval(input, cx.clone()).and_then(|(x, _)| cx.done(x))
            })
        }
        x => Err(Error::wrong_input_type(x, &blk.op_tag)),
    }
}

/// follows the pattern `let {get t# | cmp $rhs.t#} $c#` and `if {\\ $c# | != Ord::Eq} $c#`.
fn build_tuple_cmp_def_str(els: usize) -> String {
    use std::fmt::Write;
    let mut s = "def tuple-cmp (rhs) { let ".to_string();
    for i in 0..els {
        write!(&mut s, "{{get t{0} | cmp $rhs.t{0}}} $c{0} ", i).ok();
    }
    s += "| if ";
    let els = els.saturating_sub(1);
    for i in 0..els {
        write!(&mut s, "{{\\ $c{0} | != Ord::Eq}} $c{0} ", i).ok();
    }
    write!(&mut s, "$c{} }}", els).ok(); // instead of testing every element, pass the last through
    s
}

// ------ Dedup ----------------------------------------------------------------
fn dedup_help() -> HelpMessage {
    HelpMessage {
        desc: "deduplicate items
for Tables consectutive repeated rows are removed if the cells in
specified columns match. if no columns are specified the whole row must match.
if the table is sorted, this removes all duplicates.
for Strs duplicate characters are removed."
            .into(),
        params: vec![HelpParameter::Required("col-name..".into())],
        examples: vec![
            HelpExample {
                desc: "remove all duplicate entries in the 'Product' heading",
                code: "sort Product | dedup Product",
            },
            HelpExample {
                desc: "remove duplicates that match the entire row",
                code: "ls foo | + ls bar | sort name | dedup",
            },
        ],
        ..HelpMessage::new("dedup")
    }
}

fn dedup_intrinsic(blk: Block) -> Result<Step> {
    match blk.in_ty() {
        Ty::Str => dedup_str(blk),
        Ty::Tab => dedup_table(blk),
        x => Err(Error::wrong_input_type(x, &blk.op_tag)),
    }
}

/// Assumes already check that input is Table.
fn dedup_table(mut blk: Block) -> Result<Step> {
    let colnames = match blk.args_len() {
        0 => None,
        _ => Some(ColNameArgs::build(&mut blk)?),
    };
    blk.eval_o(move |table, cx| {
        let table: Table = table.try_into()?;
        let cols: Vec<usize> = match &colnames {
            Some(c) => c
                .resolve_indices(&table, &cx)?
                .into_iter()
                .map(|x| x.0)
                .collect(),
            None => (0..table.cols_len()).collect(),
        };
        // we need to own the vector for .dedup function
        let mut t = (&*table).clone().into_raw();
        t.dedup_by(|a, b| cols.iter().all(|&c| a[c] == b[c]));

        cx.done_o(Table::from(InnerTable::from(t)))
    })
}

/// Assumes already check that input is Str.
fn dedup_str(blk: Block) -> Result<Step> {
    blk.eval_o(move |string, cx| {
        let string: Str = string.try_into()?;

        let mut x = None;
        let s: Str = string
            .chars()
            .filter(|&c| match x {
                Some(x) if c == x => false,
                _ => {
                    x = Some(c);
                    true
                }
            })
            .collect::<String>()
            .into();

        cx.done_o(s)
    })
}

// ------ Div ------------------------------------------------------------------
fn div_help() -> HelpMessage {
    variadic_help(
        "/",
        "divide arguments against one another
note: if input is not a Num, the first arg is used as lhs
dividing by 0 will result in infinity (∞)",
        vec![
            HelpExample {
                desc: "divide 4 by 2",
                code: "\\ 4 | / 2",
            },
            HelpExample {
                desc: "divide 2 ÷ 3",
                code: "÷ 2 3",
            },
            HelpExample {
                desc: "divide multiple numbers together",
                code: "/ 1 2 3 4 5",
            },
        ],
    )
}

fn div_intrinsic(blk: Block) -> Result<Step> {
    variadic_intrinsic_num(blk, std::ops::Div::div)
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

// ------ Eq -------------------------------------------------------------------
fn eq_help() -> HelpMessage {
    HelpMessage {
        desc: "returns if <rhs> is equal to input".into(),
        params: vec![HelpParameter::Required("rhs".into())],
        examples: vec![
            HelpExample {
                desc: "does 2 equal 1",
                code: "\\ 1 | eq 2",
            },
            HelpExample {
                desc: "1 equals 1",
                code: "\\ 1 | eq 1",
            },
        ],
        ..HelpMessage::new("eq")
    }
}

fn eq_intrinsic(mut blk: Block) -> Result<Step> {
    match blk.in_ty() {
        Ty::Nil => {
            blk.next_arg(None)?.returns(&Ty::Nil)?; // we don't use rhs but we do req its existence
            blk.eval_o(|_, cx| cx.done_o(true))
        }
        Ty::Bool => {
            let rhs = blk.next_arg(None)?.returns(&Ty::Bool)?;
            blk.eval_o(move |lhs, cx| {
                let lhs: bool = lhs.try_into()?;
                let rhs: bool = rhs.resolve(|| lhs.into(), &cx)?.try_into()?;
                cx.done_o(lhs.eq(&rhs))
            })
        }
        Ty::Num => {
            let rhs = blk.next_arg(None)?.returns(&Ty::Num)?;
            blk.eval_o(move |lhs, cx| {
                let lhs: Number = lhs.try_into()?;
                let rhs: Number = rhs.resolve(|| lhs.into(), &cx)?.try_into()?;
                cx.done_o(lhs.eq(&rhs))
            })
        }
        Ty::Str => {
            let rhs = blk.next_arg(None)?.returns(&Ty::Str)?;
            blk.eval_o(move |lhs, cx| {
                let lhs: Str = lhs.try_into()?;
                let rhs: Str = rhs.resolve(|| lhs.clone().into(), &cx)?.try_into()?;
                cx.done_o(lhs.eq(&rhs))
            })
        }
        Ty::Def(x) if x.as_ref() == "Ord" => {
            let ordty = Type::Def(types::ORD.get());
            let rhs = blk.next_arg(None)?.returns(&ordty)?;
            blk.eval_o(move |lhs, cx| {
                let lhs_variant = lhs.variant_idx().expect("Ord type");
                let rhs = rhs.resolve(|| lhs, &cx)?.variant_idx().expect("Ord type");
                cx.done_o(lhs_variant.eq(&rhs))
            })
        }
        Ty::Def(x) if x.name().str().starts_with("U_") => {
            let els = match x.structure() {
                types::TypeVariant::Product(x) => x.len(),
                _ => 0,
            };
            blk.next_arg_do_not_remove(None)?.returns(blk.in_ty())?; // this checks same lhs=rhs type
            let def =
                &lang::syntax::parse::definition_impl(build_tuple_eq_def_str(els), Location::Ogma, blk.defs)
                    .map_err(|(e, _)| e)?;
            let evaltr = eng::DefImplEvaluator::build(&mut blk, def)?.returns(&Ty::Bool)?;
            blk.eval(Ty::Bool, move |input, cx| {
                evaltr.eval(input, cx.clone()).and_then(|(x, _)| cx.done(x))
            })
        }
        x => Err(Error::wrong_input_type(x, &blk.op_tag)),
    }
}

/// follows the pattern `and {get t# | = $rhs.t#}`.
fn build_tuple_eq_def_str(els: usize) -> String {
    use std::fmt::Write;
    let mut s = "def tuple-eq (rhs) { and ".to_string();
    for i in 0..els {
        write!(&mut s, "{{get t{0} | = $rhs.t{0}}} ", i).ok();
    }
    s.push('}');
    s
}

// ------ Filter ---------------------------------------------------------------
fn filter_help() -> HelpMessage {
    HelpMessage {
        desc: "filter incoming data using a predicate
filter can be used with a column header and a type flag
filtering columns is achievable with the --cols flag"
            .into(),
        params: vec![
            HelpParameter::Optional("col-name".into()),
            HelpParameter::Required("<predicate>".into()),
        ],
        flags: vec![
            (
                "<type>",
                "only filter entries of type. defaults to Num if not specified",
            ),
            (
                "cols",
                "filter columns with predicate. predicate is String -> Bool",
            ),
        ],
        examples: vec![
            HelpExample {
                desc: "filter ls items greater than 5kB",
                code: "ls | filter size > 5e3",
            },
            HelpExample {
                desc: "filter ls by extension",
                code: "ls | filter ext --Str = md",
            },
            HelpExample {
                desc: "filter a table by two columns",
                code: "\\ table.csv | filter { and { get col-a | > 100 } { get col-b | < 10 } }",
            },
            HelpExample {
                desc: "filter table columns",
                code: "\\ table.csv | filter --cols or { = 'foo' } { = bar }",
            },
        ],
        ..HelpMessage::new("filter")
    }
}

fn filter_intrinsic(mut blk: Block) -> Result<Step> {
    if blk.in_ty() != &Ty::Tab {
        return Err(Error::wrong_input_type(blk.in_ty(), &blk.op_tag));
    }

    let cols = blk.get_flag("cols").is_some();
    if cols {
        filter_table_columns(blk)
    } else {
        FilterTable::filter(blk)
    }
}

struct FilterTable {
    expr_predicate: eng::Argument,
    col: Option<eng::Argument>,
    exp_ty: Type,
}

impl FilterTable {
    fn filter(mut blk: Block) -> Result<Step> {
        if blk.args_len() == 1 {
            let ft = Box::new(Self {
                expr_predicate: blk.next_arg(Ty::TabRow)?.returns(&Ty::Bool)?,
                col: None,
                exp_ty: Ty::Nil,
            });

            blk.eval_o(move |table, cx| {
                let table: Table = table.try_into()?;
                let keep = ft.gen_keep_arr_with_table_row_input(&table, &cx)?;
                cx.done_o(FilterTable::retain_keep_rows(table, &keep))
            })
        } else {
            let col = blk.next_arg(Ty::Nil)?.returns(&Ty::Str)?;
            let exp_ty = type_flag(&mut blk, Type::Num)?;
            let expr_predicate = blk.next_arg(exp_ty.clone())?.returns(&Ty::Bool)?;

            let ft = Box::new(Self {
                expr_predicate,
                col: Some(col),
                exp_ty,
            });

            blk.eval_o(move |table, cx| {
                let table: Table = table.try_into()?;
                let keep = ft.gen_keep_arr_with_known_col(&table, &cx)?;
                cx.done_o(FilterTable::retain_keep_rows(table, &keep))
            })
        }
    }

    // filtering works by applying the predicate to each row and marking rows for
    // keeping if it passes the predicate.
    // Rows cannot be removed in the loop as the indexing will break,
    // and the predicate might use the indexing.
    // The specialised syntax which has the col-name out the front can leverage parallelisation
    // since the col-idx can be cached.
    // The normal filter can still utilise parallelisation by using for_each_init
    fn gen_keep_arr_with_table_row_input(&self, table: &Table, cx: &Context) -> Result<Vec<bool>> {
        let mut keep = vec![true; table.rows_len()];
        let predicate = self.expr_predicate.resolver_sync(cx);
        par_over_tablerows(&mut keep, table, cx, |k, _, trow| {
            predicate(trow.into())
                .and_then(TryInto::try_into)
                .map(|x| *k = x)
        })?;

        Ok(keep)
    }

    fn gen_keep_arr_with_known_col(&self, table: &Table, cx: &Context) -> Result<Vec<bool>> {
        let Self {
            col, exp_ty: ty, ..
        } = self;

        let col = col.as_ref().expect("only take this branch if have some");
        let tag = &col.tag;
        let name = &col.resolve(|| Value::Nil, cx).and_then(Str::try_from)?;
        let mut keep = vec![true; table.rows_len()];
        let predicate = self.expr_predicate.resolver_sync(cx);

        par_over_tablerows(&mut keep, table, cx, |k, _, trow| {
            let i = trow.idx;
            let e = trow.entry(name, tag)?;
            match TableRow::cnv_value(e, ty, i, name, tag) {
                Ok(e) => predicate(e).and_then(TryInto::try_into).map(|x| *k = x),
                Err(_) => (*k = false, Ok(())).1,
            }
        })?;

        Ok(keep)
    }

    fn retain_keep_rows(mut table: Table, keep: &[bool]) -> Table {
        // there are three table building branches:
        //   1. keep is all true; just return the table (fast since it is arc)
        //   2. `table` is owned. we use retain to remove the rows
        //   3. `table` is shared. in this case we rebuild a table to avoid cloning the backing data
        if keep.par_iter().all(|x| *x) {
            table
        } else if let Some(t) = table.get_mut() {
            t.retain_rows(|idx, _| keep[idx]);
            table
        } else {
            let keep_c = keep.par_iter().filter(|&&x| x).count();
            table::Table::from((0..table.rows_len()).filter(|&x| keep[x]).fold(
                Vec::with_capacity(keep_c),
                |mut acc, x| {
                    acc.push(table.row(x).unwrap().cloned().collect::<Vec<_>>());
                    acc
                },
            ))
            .into()
        }
    }
}

fn filter_table_columns(mut blk: Block) -> Result<Step> {
    let predicate = blk.next_arg(Ty::Str)?.returns(&Ty::Bool)?;
    blk.eval_o(move |input, cx| {
        let mut table = Table::try_from(input)?;
        // work backwards on cols to remove
        for idx in (0..table.cols_len()).rev() {
            let hdr = table
                .col(idx)
                .and_then(|mut x| x.next())
                .map(|v| match v {
                    Entry::Obj(Value::Str(h)) => h.clone(),
                    _ => Str::default(),
                })
                .unwrap_or_default();
            let rm = predicate
                .resolve(|| hdr.into(), &cx)
                .and_then(bool::try_from)?;
            if !rm {
                // delay cloning (if have to) to last moment
                // should only clone _once_ (if have to)
                table.make_mut().remove_col_par(idx);
            }
        }

        cx.done_o(table)
    })
}

// ------ Floor ----------------------------------------------------------------
fn floor_help() -> HelpMessage {
    HelpMessage {
        desc: "return the largest integer less than or equal to a number".into(),
        ..HelpMessage::new("floor")
    }
}

fn floor_intrinsic(blk: Block) -> Result<Step> {
    if blk.in_ty() != &Ty::Num {
        return Err(Error::wrong_input_type(blk.in_ty(), &blk.op_tag));
    }
    blk.eval_o(move |n, cx| {
        Number::try_from(n)
            .map(|n| n.as_f64().floor())
            .and_then(|n| cx.done_o(Number::from(n)))
    })
}

// ------ Fold -----------------------------------------------------------------
fn fold_help() -> HelpMessage {
    HelpMessage {
        desc: "fold (reduce) table into single value
fold takes a seed value and an accumulator expression
the variable $row is available to query the table row"
            .into(),
        params: vec![
            HelpParameter::Required("seed".into()),
            HelpParameter::Required("accumulator".into()),
        ],
        examples: vec![
            HelpExample {
                desc: "sum numbers (0,10)",
                code: "range 0 11 | fold 0 { + $row.i }",
            },
            HelpExample {
                desc: "count number of files in directory",
                code: "ls | filter { get type --Str | = file } | fold 0 + 1",
            },
        ],
        ..HelpMessage::new("fold")
    }
}

fn fold_intrinsic(mut blk: Block) -> Result<Step> {
    match blk.in_ty() {
        Ty::Tab => {
            let seed = blk.next_arg(Type::Nil)?;
            let out_ty = seed.out_ty().clone();
            let row_var = blk.create_var_manually("row", Ty::TabRow, blk.op_tag.clone());
            let acc_expr = blk.next_arg(out_ty.clone())?;

            blk.eval(out_ty, move |table, mut cx| {
                let table: Table = table.try_into()?;
                let colmap = types::TableRowColMap::default();
                let mut x = seed.resolve(|| Value::Nil, &cx)?;
                for idx in 1..table.rows_len() {
                    let trow = TableRow::new(table.clone(), colmap.clone(), idx);
                    row_var.set_data(&mut cx.env, trow.into());
                    x = acc_expr.resolve(|| x, &cx)?;
                }

                cx.done(x)
            })
        }
        x => Err(Error::wrong_input_type(x, &blk.op_tag)),
    }
}

// ------ Fold-While -----------------------------------------------------------
fn fold_while_help() -> HelpMessage {
    HelpMessage {
        desc: "fold (reduce) table into single value while a predicate remains true
fold-while is similar to fold with an added predicate check on each iteration
the input into the predicate is the current accumulator value
fold-while will stop iterating once the predicate returns false"
            .into(),
        params: vec![
            HelpParameter::Required("seed".into()),
            HelpParameter::Required("predicate".into()),
            HelpParameter::Required("accumulator".into()),
        ],
        examples: vec![HelpExample {
            desc: "sum natural numbers until sum is greater than one million",
            code: "range 1 1e6 | fold-while 0 {<= 1e6} { + $row.i }",
        }],
        ..HelpMessage::new("fold-while")
    }
}

fn fold_while_intrinsic(mut blk: Block) -> Result<Step> {
    match blk.in_ty() {
        Ty::Tab => {
            let seed = blk.next_arg(Type::Nil)?;
            let out_ty = seed.out_ty().clone();
            let row_var = blk.create_var_manually("row", Ty::TabRow, blk.op_tag.clone());
            let acc_predicate = blk.next_arg(out_ty.clone())?.returns(&Ty::Bool)?;
            let acc_expr = blk.next_arg(out_ty.clone())?;

            blk.eval(out_ty, move |table, mut cx| {
                let table: Table = table.try_into()?;
                let colmap = types::TableRowColMap::default();
                let mut x = seed.resolve(|| Value::Nil, &cx)?;
                for idx in 1..table.rows_len() {
                    let met = acc_predicate
                        .resolve(|| x.clone(), &cx)
                        .and_then(bool::try_from)?;
                    if !met {
                        break;
                    }

                    let trow = TableRow::new(table.clone(), colmap.clone(), idx);
                    row_var.set_data(&mut cx.env, trow.into());
                    x = acc_expr.resolve(|| x, &cx)?;
                }

                cx.done(x)
            })
        }
        x => Err(Error::wrong_input_type(x, &blk.op_tag)),
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
            let get_type = match blk.next_arg(Type::Nil).ok().map(TableGetType::Default) {
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
    Default(eng::Argument),
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
) -> Result<(Value, var::Environment)> {
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
                    .ok_or_else(|| Error::field_not_found(field_arg.tag(), tydef))?;

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

// ------ Grouping -------------------------------------------------------------
fn grp_help() -> HelpMessage {
    HelpMessage {
        desc: "group a table by column headers
each value under the header is stringified and
concatenated together separated by a hyphen
to group on a derived value see `grp-by`"
            .into(),
        params: vec![HelpParameter::Required("col-name..".into())],
        examples: vec![
            HelpExample {
                desc: "group by file extension",
                code: "ls | grp ext",
            },
            HelpExample {
                desc: "group by file extension and modified",
                code: "ls | grp ext modified",
            },
        ],
        ..HelpMessage::new("grp")
    }
}

fn grp_intrinsic(mut blk: Block) -> Result<Step> {
    if blk.in_ty() != &Ty::Tab {
        return Err(Error::wrong_input_type(blk.in_ty(), &blk.op_tag));
    }

    let colnames = ColNameArgs::build(&mut blk)?;
    let blktag = blk.blk_tag.clone();
    blk.eval_o(move |table, cx| {
        let table: Table = table.try_into()?;
        if table.is_empty() {
            return Err(Error::eval(&blktag, "table is empty", None, None));
        }

        let cols = colnames.resolve_indices(&table, &cx)?;

        let mut map = BTreeMap::default();
        let row = |i| table.row(i).expect("should exist");
        let fmtr = &mut numfmt::Formatter::new();

        for rowidx in 1..table.rows_len() {
            let key = cols
                .iter()
                .map(|(c, _)| row(rowidx).nth(*c).expect("index inside table"))
                .fold(String::new(), |mut k, e| {
                    if !k.is_empty() {
                        k.push('-');
                    }
                    k.push_str(&print::fmt_cell(e, fmtr));
                    k
                });
            let t = map.entry(key).or_insert_with(|| {
                let mut t = InnerTable::new();
                t.add_row(row(0).cloned()); // hdr should exist
                t
            });
            t.add_row(row(rowidx).cloned());
        }

        cx.done_o(build_table_from_map(map, |s| Value::Str(s.into())))
    })
}

fn build_table_from_map<K, F>(map: BTreeMap<K, InnerTable>, mut key_f: F) -> Table
where
    F: FnMut(K) -> Value,
{
    let mut table = InnerTable::default();
    table.add_row(once("key").chain(once("value")).map(o));
    table.add_rows(
        map.into_iter()
            .map(|(k, v)| once(key_f(k)).chain(once(Value::Tab(Table::from(v))))),
    );
    table.into()
}

// grp-by
// whilst grp uses a string conversion as key, grp-by converts each row into a value using an
// expression, then groups the resulting values (and by proxy; the table)
// grouping the values uses `cmp` definitions
// the actual implementation is a bit more complex; we must create a pseudo-env to eval `cmp`
fn grpby_help() -> HelpMessage {
    HelpMessage {
        desc: "group table using an expression
the result of the expression must define a `cmp` implementation
this can be used to group user-defined types"
            .into(),
        params: vec![HelpParameter::Required("<expr>".into())],
        examples: vec![
            HelpExample {
                desc: "group ls by file extension",
                code: "ls | grp-by { get --Str ext }",
            },
            HelpExample {
                desc: "group using a user-defined type",
                code: "ls | grp-by { Point { get size } }",
            },
        ],
        ..HelpMessage::new("grp-by")
    }
}

fn grpby_intrinsic(mut blk: Block) -> Result<Step> {
    if blk.in_ty() != &Ty::Tab {
        return Err(Error::wrong_input_type(blk.in_ty(), &blk.op_tag));
    }

    // the expression which will be grouped on
    let key = blk.next_arg(Ty::TabRow)?;
    let ordty = Ty::Def(types::ORD.get());
    let cmpr = BinaryOp::new(
        "cmp",
        key.out_ty(),
        &ordty,
        "grp-by",
        key.tag(),
        blk.defs,
        cnv_value_to_ord,
    )?;

    blk.eval_o::<_, Table>(move |table, cx| {
        let table = Table::try_from(table)?;
        let grping_values: SortIdx = resolve_trow_expr_par(&table, &key, &cx)?
            .into_iter()
            .enumerate()
            .collect();
        let t = grp_table(grping_values, &table, cmpr.pin_env(), &cx);
        cx.done_o(t)
    })
}

struct GrpByKey<'a, T> {
    value: Value,
    binop: Rc<RefCell<BinaryOpRef<'a, T>>>,
    cx: &'a Context<'a>,
}

impl<'a, T> PartialEq for GrpByKey<'a, T>
where
    T: Fn(Value) -> cmp::Ordering,
{
    fn eq(&self, rhs: &Self) -> bool {
        self.cmp(rhs).eq(&cmp::Ordering::Equal)
    }
}
impl<'a, T> Eq for GrpByKey<'a, T> where T: Fn(Value) -> cmp::Ordering {}
impl<'a, T> PartialOrd for GrpByKey<'a, T>
where
    T: Fn(Value) -> cmp::Ordering,
{
    fn partial_cmp(&self, rhs: &Self) -> Option<cmp::Ordering> {
        self.binop
            .borrow_mut()
            .eval(self.value.clone(), rhs.value.clone(), self.cx)
            .ok()
    }
}
impl<'a, T> Ord for GrpByKey<'a, T>
where
    T: Fn(Value) -> cmp::Ordering,
{
    fn cmp(&self, rhs: &Self) -> cmp::Ordering {
        self.partial_cmp(rhs).unwrap_or(cmp::Ordering::Equal)
    }
}

fn grp_table<T>(values: SortIdx, table: &Table, binop: BinaryOpRef<T>, cx: &Context) -> Table
where
    T: Fn(Value) -> cmp::Ordering,
{
    let newtable = || {
        let mut t = ::table::Table::default();
        t.add_row(table.row(0).expect("has hdr").cloned());
        t
    };
    let mut map = BTreeMap::new();

    let binop = Rc::new(RefCell::new(binop));
    for (idx, value) in values.into_iter().skip(1) {
        // skip header row
        let key = GrpByKey {
            value,
            cx,
            binop: Rc::clone(&binop),
        };
        let t = map.entry(key).or_insert_with(newtable);
        t.add_row(table.row(idx).expect("row inside table").cloned());
    }

    build_table_from_map(map, |k| k.value)
}

// ------ If -------------------------------------------------------------------
fn if_help() -> HelpMessage {
    HelpMessage {
        desc: "evaluate expression if predicate is met
input is carried through to each of the expressions
`expr-if-true` and `expr-if-false` must evaluate to the same type
`if` can be overloaded such that it can test multiple predicates"
            .into(),
        params: vec![
            HelpParameter::Required("predicate-1".into()),
            HelpParameter::Required("expr-if-true-1".into()),
            HelpParameter::Optional("predicate-2".into()),
            HelpParameter::Optional("expr-if-true-2".into()),
            HelpParameter::Required("... expr-if-false".into()),
        ],
        examples: vec![
            HelpExample {
                desc: "return 2 if 3, otherwise 1",
                code: "\\ 3 | if { = 3 } 2 1",
            },
            HelpExample {
                desc: "return 2 if 3, 1 if 2, otherwise 0",
                code: "\\ 10 | if {= 3} 2 {= 2} 1 0",
            },
        ],
        ..HelpMessage::new("if")
    }
}

fn if_intrinsic(mut blk: Block) -> Result<Step> {
    let args = blk.args_len();
    if args % 2 == 0 {
        let mut e = Error::insufficient_args(&blk.blk_tag, args);
        e.help_msg =
            Some("`if` requires odd number of arguments to match true/false expressions".into());
        return Err(e);
    }

    struct Cond {
        pred: eng::Argument,
        expr: eng::Argument,
    }

    let mut args = Vec::with_capacity(args / 2);
    while blk.args_len() > 1 {
        args.push(Cond {
            pred: blk.next_arg(None)?.returns(&Ty::Bool)?,
            expr: blk.next_arg(None)?,
        });
    }
    let else_ = blk.next_arg(None)?;

    let out_ty = else_.out_ty().clone();

    // validate all the branches
    for cond in &args {
        if out_ty != *cond.expr.out_ty() {
            return Err(Error::eval(
                cond.expr.tag(),
                "branch arms do not have matching output types",
                "this branch has a different output type".to_string(),
                "branching impls require consistent output types".to_string(),
            ));
        }
    }

    blk.eval(out_ty, move |input, cx| {
        for Cond { pred, expr } in &args {
            let predicate: bool = pred.resolve(|| input.clone(), &cx)?.try_into()?;
            if predicate {
                return expr.resolve(|| input, &cx).and_then(|x| cx.done(x));
            }
        }
        else_.resolve(|| input, &cx).and_then(|x| cx.done(x))
    })
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

// ------ Is Finite ------------------------------------------------------------
fn isfinite_help() -> HelpMessage {
    HelpMessage {
        desc: "returns whether a number is finite
a number is finite if it is not infinite AND not NaN"
            .into(),
        examples: vec![
            HelpExample {
                desc: "most numbers are finite",
                code: "\\ 5 | is-finite",
            },
            HelpExample {
                desc: "but dividing by zero isn't!",
                code: "÷ 1 0 | is-finite",
            },
        ],
        ..HelpMessage::new("is-finite")
    }
}

fn isfinite_intrinsic(blk: Block) -> Result<Step> {
    match blk.in_ty() {
        Ty::Num => blk.eval_o(|n, cx| {
            Number::try_from(n)
                .map(|n| n.as_f64().is_finite())
                .and_then(|x| cx.done_o(x))
        }),
        x => Err(Error::wrong_input_type(x, &blk.op_tag)),
    }
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
    type Binding = (var::Variable, eng::Argument);
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

// ------ Map ------------------------------------------------------------------
fn map_help() -> HelpMessage {
    HelpMessage {
        desc: "replace entry in column with result of an expression
`map` provides the variable `$row` which is the TableRow
the input into the expression is the value of the entry"
            .into(),
        params: vec![
            HelpParameter::Required("col-name".into()),
            HelpParameter::Required("value".into()),
        ],
        flags: vec![
            ("<type>", "the type that entry has"),
            ("force", "ignore entry types"),
        ],
        examples: vec![
            HelpExample {
                desc: "scale 'size' by dividing by one million",
                code: "ls | map size / 1e6",
            },
            HelpExample {
                desc: "use a different column and result type",
                code: "ls | map type --Str { \\$row.size | + 100 }",
            },
        ],
        ..HelpMessage::new("map")
    }
}

fn map_intrinsic(blk: Block) -> Result<Step> {
    match blk.in_ty() {
        Ty::Tab => MapTable::map(blk),
        x => Err(Error::wrong_input_type(x, &blk.op_tag)),
    }
}

struct MapTable {
    /// Expecting TableRow.
    transformation: eng::Argument,
    colarg: eng::Argument,
    colty: Option<Type>,
    row_var: var::Variable,
}

impl MapTable {
    fn map(mut blk: Block) -> Result<Step> {
        let colarg = blk.next_arg(Ty::Nil)?.returns(&Ty::Str)?;
        let colty = match blk.get_flag("force") {
            Some(_) => None,
            None => Some(type_flag(&mut blk, Type::Num)?),
        };
        let row_var = blk.create_var_manually("row", Ty::TabRow, blk.op_tag.clone());
        let transformation = blk.next_arg(colty.clone().unwrap_or(Ty::Nil))?;

        let mp = Box::new(Self {
            transformation,
            colarg,
            colty,
            row_var,
        });

        blk.eval_o::<_, Table>(move |table, cx| {
            mp.doit(table.try_into()?, &cx).and_then(|x| cx.done_o(x))
        })
    }

    fn doit(&self, mut table: Table, cx: &Context) -> Result<Table> {
        let colname: Str = self.colarg.resolve(|| Value::Nil, cx)?.try_into()?;
        let ctag = &self.colarg.tag;
        let colidx = TableRow::col_idx(&table, &colname, ctag)?;

        let mut replace_with: Vec<Value> =
            repeat_with(|| Value::Nil).take(table.rows_len()).collect();
        let tf = &self.transformation;
        let var = &self.row_var;

        par_over_tablerows(&mut replace_with, &table, cx, |v, cx, trow| {
            let trowidx = trow.idx;
            var.set_data(&mut cx.env, trow.into());
            let outv = match &self.colty {
                Some(ty) => {
                    let e = TableRow::entry_at(&table, trowidx, colidx);
                    let e = TableRow::cnv_value(e, ty, trowidx, &colname, ctag)?;
                    tf.resolve(|| e, cx)
                }
                None => tf.resolve(|| Value::Nil, cx),
            };
            *v = outv?;
            Ok(())
        })?;

        table
            .make_mut()
            .col_mut(colidx)
            .expect("col should exist")
            .zip(replace_with.into_iter())
            .skip(1) // for header
            .for_each(|(e1, e2)| *e1 = e2.into());

        Ok(table)
    }
}

// ------ Max ------------------------------------------------------------------
fn max_help() -> HelpMessage {
    variadic_help(
        "max",
        "return the maximum value",
        vec![
            HelpExample {
                desc: "maximum of 2 and 3",
                code: "\\ 2 | max 3",
            },
            HelpExample {
                desc: "maximum of multiple args",
                code: "max 1 2 3 4 5",
            },
        ],
    )
}

fn max_intrinsic(blk: Block) -> Result<Step> {
    variadic_intrinsic::<Number, _>(blk, |prev, next| {
        let x = prev.map(|prev| std::cmp::max(prev, next)).unwrap_or(next);
        (x, false)
    })
}

// ------ Min ------------------------------------------------------------------
fn min_help() -> HelpMessage {
    variadic_help(
        "min",
        "return the minimum value",
        vec![
            HelpExample {
                desc: "minimum of 2 and 3",
                code: "\\ 2 | min 3",
            },
            HelpExample {
                desc: "minimum of multiple args",
                code: "min 1 2 3 4 5",
            },
        ],
    )
}

fn min_intrinsic(blk: Block) -> Result<Step> {
    variadic_intrinsic::<Number, _>(blk, |prev, next| {
        let x = prev.map(|prev| std::cmp::min(prev, next)).unwrap_or(next);
        (x, false)
    })
}

// ------ Mul ------------------------------------------------------------------
fn mul_help() -> HelpMessage {
    variadic_help(
        "*",
        "multiply arguments together",
        vec![
            HelpExample {
                desc: "multiply 2 three times",
                code: "\\ 2 | * 3",
            },
            HelpExample {
                desc: "multiply multiple numbers together",
                code: "× 1 2 3 4 5",
            },
        ],
    )
}

fn mul_intrinsic(blk: Block) -> Result<Step> {
    variadic_intrinsic_num(blk, std::ops::Mul::mul)
}

// ------ Not ------------------------------------------------------------------
fn not_help() -> HelpMessage {
    HelpMessage {
        desc: "negates a boolean value.\ninput must be a Bool".into(),
        examples: vec![HelpExample {
            desc: "1 is NOT greater than 2",
            code: "\\ 1 | > 2 | not",
        }],
        ..HelpMessage::new("not")
    }
}

fn not_intrinsic(blk: Block) -> Result<Step> {
    match blk.in_ty() {
        Ty::Bool => blk.eval_o(|val, cx| bool::try_from(val).and_then(|x| cx.done_o(!x))),
        x => Err(Error::wrong_input_type(x, &blk.op_tag)),
    }
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
                    .and_then(|v| cnv_num_to_uint::<usize>(v, n.tag()))?;
                let table = Table::try_from(table)?;
                if nth + 1 >= table.rows_len() {
                    return Err(Error::eval(
                        n.tag(),
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
                    .and_then(|v| cnv_num_to_uint::<usize>(v, n.tag()))?;
                Str::try_from(string)
                    .and_then(|s| {
                        s.chars().nth(nth).ok_or_else(|| {
                            Error::eval(
                                n.tag(),
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

// ------ Or -------------------------------------------------------------------
fn or_help() -> HelpMessage {
    variadic_help(
        "or",
        "returns true if any arguments are true",
        vec![HelpExample {
            desc: "1 is less than OR equal to 2",
            code: "\\ 1 | or { < 2 } { = 2 }",
        }],
    )
}

fn or_intrinsic(blk: Block) -> Result<Step> {
    variadic_intrinsic::<bool, _>(blk, |prev, next| {
        let x = prev.unwrap_or(false);
        let x = x || next;
        (x, x)
    })
}

// ------ Pick -----------------------------------------------------------------
fn pick_help() -> HelpMessage {
    HelpMessage {
        desc: "pick out columns to keep in a table, in order".into(),
        params: vec![HelpParameter::Required("col-name..".into())],
        flags: vec![
            (
                "add",
                "add a blank column if it does not exist in the table",
            ),
            ("trail", "append any remaining columns in order"),
        ],
        examples: vec![HelpExample {
            desc: "choose the size, name, and type columns",
            code: "ls | pick name size type",
        }],
        ..HelpMessage::new("pick")
    }
}

fn pick_intrinsic(blk: Block) -> Result<Step> {
    match blk.in_ty() {
        Ty::Tab => pick_table_columns(blk),
        x => Err(Error::wrong_input_type(x, &blk.op_tag)),
    }
}

fn pick_table_columns(mut blk: Block) -> Result<Step> {
    let addflag = blk.get_flag("add").is_some();
    let trailflag = blk.get_flag("trail").is_some();

    let colnames = ColNameArgs::build(&mut blk)?;
    blk.eval_o::<_, Table>(move |input, cx| {
        let table = Table::try_from(input)?;
        let mut colidxs = if addflag {
            colnames.resolve_indices_forgiven(&table, &cx)?
        } else {
            colnames
                .resolve_indices(&table, &cx)?
                .into_iter()
                .map(|(a, b)| (Some(a), b))
                .collect()
        };

        if trailflag {
            // add columns that weren't touched to end, in order.
            let indices: HashSet<_> = colidxs.iter().filter_map(|x| x.0).collect();
            let toadd = (0..table.cols_len()).filter(|i| !indices.contains(i));
            colidxs.extend(toadd.map(|i| (Some(i), "".into())));
        }

        // rebuild table in parallel fashion
        let mut v = repeat_with(|| Vec::with_capacity(colidxs.len()))
            .take(table.rows_len())
            .collect::<Vec<_>>();
        v.par_iter_mut().enumerate().for_each(|(row, v)| {
            let row = colidxs.iter().map(|i| match i {
                (Some(i), _) => table.row(row).and_then(|mut x| x.nth(*i)).unwrap().clone(),
                (None, n) if row == 0 => Value::Str(n.clone()).into(), // header
                (None, _) => Entry::Nil,
            });
            v.extend(row);
        });

        cx.done_o(::table::Table::from(v).into())
    })
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
            let len: usize = cnv_num_to_uint(len.resolve(|| i, &cx)?, len.tag())?;
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
                    .and_then(|n| cnv_num_to_uint(n, from.tag()))?;
                let to = cnv_num_to_uint(input, &blktag)?;
                cx.done_o(table_range(from, to))
            })
        }
        _ => {
            let to = blk.next_arg(None)?.returns(&Type::Num)?;
            blk.eval_o(move |input, cx| {
                let from = from
                    .resolve(|| input.clone(), &cx)
                    .and_then(|n| cnv_num_to_uint(n, from.tag()))?;
                let to = to
                    .resolve(|| input.clone(), &cx)
                    .and_then(|n| cnv_num_to_uint(n, to.tag()))?;
                cx.done_o(table_range(from, to))
            })
        }
    }
}

// ------ Ren ------------------------------------------------------------------
fn ren_help() -> HelpMessage {
    HelpMessage {
        desc: "rename column headers
each binding takes the form `<col-ref> <name>`
`<col-ref>` can be a string or a column index number"
            .into(),
        params: vec![
            HelpParameter::Optional("<col-ref-1> <name-1>".into()),
            HelpParameter::Optional("<col-ref-2> <name-2>".into()),
            HelpParameter::Required("...".into()),
        ],
        examples: vec![
            HelpExample {
                desc: "rename foo to bar and bar to foo",
                code: "ren foo bar bar foo",
            },
            HelpExample {
                desc: "rename idx 0 to foo",
                code: "ren 0 foo",
            },
        ],
        ..HelpMessage::new("ren")
    }
}

fn ren_intrinsic(mut blk: Block) -> Result<Step> {
    enum Ref {
        Name(eng::Argument),
        Idx(eng::Argument),
    }
    // hdrs and names take Nil input.
    let mut hdrs: Vec<Ref> = Vec::with_capacity(blk.args_len() / 2);
    let mut names = Vec::with_capacity(blk.args_len() / 2);

    while blk.args_len() > 1 {
        let hdr = blk.next_arg(Ty::Nil)?;
        let hdr = match hdr.out_ty() {
            Ty::Num => Ref::Idx(hdr.returns(&Ty::Num)?),
            _ => Ref::Name(hdr.returns(&Ty::Str)?),
        };
        hdrs.push(hdr);
        names.push(blk.next_arg(Ty::Nil)?.returns(&Ty::Str)?);
    }

    match blk.in_ty() {
        Ty::Tab => blk.eval_o(move |table, cx| {
            let mut table: Table = table.try_into()?;
            let mut indices = Vec::with_capacity(hdrs.len());
            // resolve the headers first so we don't encounter weird issues by updating the column
            // headers _while_ resolving the header indices.
            for h in &hdrs {
                let i = match h {
                    Ref::Idx(x) => x
                        .resolve(|| Value::Nil, &cx)
                        .and_then(|n| cnv_num_to_uint::<usize>(n, x.tag())),
                    Ref::Name(x) => x
                        .resolve(|| Value::Nil, &cx)
                        .and_then(Str::try_from)
                        .and_then(|n| TableRow::col_idx(&table, n.as_str(), x.tag())),
                }?;
                indices.push(i);
            }

            let t = table.make_mut();

            for (idx, i) in indices.into_iter().enumerate() {
                match t.col_mut(i) {
                    Some(mut x) => {
                        let name = names[idx].resolve(|| Value::Nil, &cx)?;
                        if let Some(x) = x.next() {
                            *x = name.into();
                        }
                        Ok(())
                    }
                    None => Err(Error::eval(
                        match &hdrs[idx] {
                            Ref::Name(x) | Ref::Idx(x) => x.tag(),
                        },
                        format!("{} is outside table column bounds", i),
                        None,
                        "use `ls` command to view a table's headers".to_string(),
                    )),
                }?;
            }

            cx.done_o(table)
        }),
        x => Err(Error::wrong_input_type(x, &blk.op_tag)),
    }
}

// ------ Ren-With -------------------------------------------------------------
fn ren_with_help() -> HelpMessage {
    HelpMessage {
        desc: "rename column headers using a row as a seed
each entry is fed into the expression, which returns a string
the default entry type required is a string"
            .into(),
        params: vec![
            HelpParameter::Required("row-idx".into()),
            HelpParameter::Required("name-expr".into()),
        ],
        flags: vec![("<type>", "the type of the entry")],
        examples: vec![
            HelpExample {
                desc: "rename the header with what is in row 2",
                code: "ren-with 2 #i",
            },
            HelpExample {
                desc: "append the headers with something",
                code: "ren-with 0 + ' bar'",
            },
            HelpExample {
                desc: "use the first row as a header and forget the old one",
                code: "ren-with 1 #i | skip 1",
            },
        ],
        ..HelpMessage::new("ren-with")
    }
}

fn ren_with_intrinsic(mut blk: Block) -> Result<Step> {
    let row_idx = blk.next_arg(Type::Nil)?.returns(&Type::Num)?;
    let inty = type_flag(&mut blk, Type::Str)?;
    let expr = blk.next_arg(inty.clone())?.returns(&Type::Str)?;
    let blktag = blk.blk_tag.clone();

    match blk.in_ty() {
        Ty::Tab => blk.eval_o(move |table, cx| {
            let rowidx = row_idx
                .resolve(|| Value::Nil, &cx)
                .and_then(|v| cnv_num_to_uint(v, &row_idx.tag))?;
            let mut table: Table = table.try_into()?;
            if table.is_empty() {
                return Err(Error::empty_table(None, &blktag));
            }
            if rowidx >= table.rows_len() {
                return Err(Error::row_out_of_bounds(rowidx, &row_idx.tag));
            }

            let mut hdrs = Vec::with_capacity(table.cols_len());
            for (colidx, entry) in table
                .row(rowidx)
                .expect("row checked for existence")
                .enumerate()
            {
                let entry = TableRow::cnv_value(entry, &inty, rowidx, colidx, &row_idx.tag)?;
                let name: Str = expr.resolve(|| entry, &cx)?.try_into()?;
                hdrs.push(name);
            }

            let t = table.make_mut();
            if let Some(row) = t.row_mut(0) {
                row.zip(hdrs)
                    .for_each(|(e, h)| *e = Entry::from(Value::from(h)));
            }

            cx.done_o(table)
        }),
        x => Err(Error::wrong_input_type(x, &blk.op_tag)),
    }
}

// ------ Reverse --------------------------------------------------------------
fn rev_help() -> HelpMessage {
    HelpMessage {
        desc: "reverse the order of the input
for String inputs; character ordering is reversed
for Table inputs; row or col ordering is reversed"
            .into(),
        flags: vec![("cols", "reverse table column ordering")],
        examples: vec![
            HelpExample {
                desc: "reverse table row ordering",
                code: "ls | rev",
            },
            HelpExample {
                desc: "reverse string character ordering",
                code: "\\ '!dlrow ,olleH' | rev",
            },
        ],
        ..HelpMessage::new("rev")
    }
}

fn rev_intrinsic(mut blk: Block) -> Result<Step> {
    match blk.in_ty() {
        Ty::Str => blk.eval_o(|input, cx| {
            Str::try_from(input)
                .map(|s| s.chars().rev().collect::<String>())
                .map(Str::from)
                .and_then(|x| cx.done_o(x))
        }),
        Ty::Tab => {
            let cols = blk.get_flag("cols").is_some();
            blk.eval_o(move |input, cx| {
                let mut table: Table = input.try_into()?;
                if cols {
                    table.make_mut().reverse_cols_par();
                } else {
                    table.make_mut().reverse_rows();
                }
                cx.done_o(table)
            })
        }
        x => Err(Error::wrong_input_type(x, &blk.op_tag)),
    }
}

// ------ Root -----------------------------------------------------------------
fn root_help() -> HelpMessage {
    HelpMessage {
        desc: "calculate the nth root of a number".into(),
        params: vec![HelpParameter::Required("index".into())],
        examples: vec![
            HelpExample {
                desc: "the square root of 4",
                code: "\\ 4 | root 2",
            },
            HelpExample {
                desc: "the cube root of 27",
                code: "\\ 27 | root 3",
            },
        ],
        ..HelpMessage::new("root")
    }
}

fn root_intrinsic(mut blk: Block) -> Result<Step> {
    if blk.in_ty() != &Ty::Num {
        return Err(Error::wrong_input_type(blk.in_ty(), &blk.op_tag));
    }
    let index = blk.next_arg(None)?.returns(&Ty::Num)?;
    blk.eval_o(move |radicand, cx| {
        let index = index
            .resolve(|| radicand.clone(), &cx)
            .and_then(Number::try_from)?
            .as_f64();
        let radicand = Number::try_from(radicand)?.as_f64();
        let x = if (index - 2.0).abs() < 1e-10 {
            radicand.sqrt()
        } else if (index - 3.0).abs() < 1e-10 {
            radicand.cbrt()
        } else {
            radicand.powf(index.recip())
        };
        cx.done_o(Number::from(x))
    })
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

// ------ Skip -----------------------------------------------------------------
fn skip_help() -> HelpMessage {
    HelpMessage {
        desc: "skip the first n elements of a data structure".into(),
        params: vec![HelpParameter::Required("count".into())],
        examples: vec![
            HelpExample {
                desc: "skip the first 10 rows of a table",
                code: "skip 10",
            },
            HelpExample {
                desc: "skip the first 5 characters of a string",
                code: "\\ 'Hello, world!' | skip 5",
            },
            HelpExample {
                desc: "skip and take can be used to slice into a string",
                code: "\\ 'Hello, world!' | skip 7 | take 5",
            },
        ],
        ..HelpMessage::new("skip")
    }
}

fn skip_intrinsic(mut blk: Block) -> Result<Step> {
    match blk.in_ty() {
        Ty::Tab => {
            let count = blk.next_arg(None)?.returns(&Ty::Num)?;
            blk.eval_o(move |table, cx| {
                let count = count
                    .resolve(|| table.clone(), &cx)
                    .and_then(|v| cnv_num_to_uint::<usize>(v, count.tag()))?;
                let mut table = Table::try_from(table)?;
                if let Some(t) = table.get_mut() {
                    t.retain_rows(|i, _| i == 0 || i > count);
                } else {
                    let rows = table
                        .rows()
                        .take(1)
                        .chain(table.rows().skip(count + 1))
                        .map(|x| x.cloned());
                    let mut t = ::table::Table::new();
                    t.add_rows(rows);
                    table = t.into();
                }
                cx.done_o(table)
            })
        }
        Ty::Str => {
            let count = blk.next_arg(None)?.returns(&Ty::Num)?;
            blk.eval_o::<_, Str>(move |string, cx| {
                let count = count
                    .resolve(|| string.clone(), &cx)
                    .and_then(|v| cnv_num_to_uint::<usize>(v, count.tag()))?;
                Str::try_from(string)
                    .map(|s| s.chars().skip(count).collect::<Str>())
                    .and_then(|x| cx.done_o(x))
            })
        }
        x => Err(Error::wrong_input_type(x, &blk.op_tag)),
    }
}

// ------ Sorting --------------------------------------------------------------
fn sort_help() -> HelpMessage {
    HelpMessage {
        desc: "sort a table by column headers
each header sorts the rows lowest to highest in a canonical fashion,
in order specified (1st column is sorted first)
this sorts different value types, but NOT user-defined types. see `sort-by`"
            .into(),
        params: vec![HelpParameter::Required("col-name..".into())],
        examples: vec![
            HelpExample {
                desc: "sort ls by file size",
                code: "ls | sort size",
            },
            HelpExample {
                desc: "sort ls by ext, THEN by size (notice the inverted order)",
                code: "ls | sort size ext",
            },
        ],
        ..HelpMessage::new("sort")
    }
}

fn sort_intrinsic(mut blk: Block) -> Result<Step> {
    if blk.in_ty() != &Ty::Tab {
        return Err(Error::wrong_input_type(blk.in_ty(), &blk.op_tag));
    }

    let colnames = ColNameArgs::build(&mut blk)?;
    blk.eval_o(move |table, cx| {
        let mut table: Table = table.try_into()?;
        let cols = colnames.resolve_indices(&table, &cx)?;

        let t = table.make_mut();
        for (col, _) in cols {
            t.sort(col, cmp_table_entries);
        }

        cx.done_o(table)
    })
}

/// Ogma data types are compared on name. OgmaData with the same types are considered 'equal'.
fn cmp_table_entries(a: &Entry<Value>, b: &Entry<Value>) -> std::cmp::Ordering {
    // overall order of variants: Bool, Num, Str, OgmaData, Nil, Table, TableRow
    let (ai, bi) = (entry_discriminant(a), entry_discriminant(b));
    if ai != bi {
        return ai.cmp(&bi);
    }

    use std::cmp::Ordering::*;
    use Entry as E;
    use Value as V;
    use E::Obj as O;

    // we know a and b types variants will match now
    match (a, b) {
        (E::Nil, _) | (O(V::Nil), _) => Equal,
        (E::Num(lhs), E::Num(rhs))
        | (O(V::Num(lhs)), E::Num(rhs))
        | (E::Num(lhs), O(V::Num(rhs)))
        | (O(V::Num(lhs)), O(V::Num(rhs))) => lhs.cmp(rhs),
        (O(V::Bool(lhs)), O(V::Bool(rhs))) => lhs.cmp(rhs),
        (O(V::Str(lhs)), O(V::Str(rhs))) => lhs.cmp(rhs),
        (O(V::Tab(_)), _) => Equal,
        (O(V::TabRow(_)), _) => Equal,
        (O(V::Ogma(lhs)), O(V::Ogma(rhs))) => lhs.ty.name().str().cmp(rhs.ty.name().str()),
        _ => unreachable!("should not reach here given all equal cases are done"),
    }
}

/// Assigns a number to each variant of Entry<Value> combo.
/// `Bool = 0, Num = 1, Str = 2, OgmaData = 3, Nil = 4, Table = 5, TableRow = 6`
fn entry_discriminant(e: &Entry<Value>) -> u8 {
    match e {
        Entry::Obj(Value::Bool(_)) => 0,
        Entry::Num(_) | Entry::Obj(Value::Num(_)) => 1,
        Entry::Obj(Value::Str(_)) => 2,
        Entry::Obj(Value::Ogma(_)) => 3,
        Entry::Nil | Entry::Obj(Value::Nil) => 4,
        Entry::Obj(Value::Tab(_)) => 5,
        Entry::Obj(Value::TabRow(_)) => 6,
    }
}

// sort-by
// whilst sort uses canonicalized entry comparison, sort-by converts each row into a value using an
// expression, then sorts the resulting values (and by proxy; the table)
// sorting the values uses `cmp` definitions
// the actual implementation is a bit more complex; we must create a pseudo-env to eval `cmp`
fn sortby_help() -> HelpMessage {
    HelpMessage {
        desc: "sort table using an expression
the result of the expression must define a `cmp` implementation
this can be used to sort user-defined types"
            .into(),
        params: vec![HelpParameter::Required("<expr>".into())],
        examples: vec![
            HelpExample {
                desc: "sort ls by file size",
                code: "ls | sort-by { get size }",
            },
            HelpExample {
                desc: "sort using a user-defined type",
                code: "ls | sort-by { Point { get size } }",
            },
        ],
        ..HelpMessage::new("sort-by")
    }
}

fn sortby_intrinsic(mut blk: Block) -> Result<Step> {
    if blk.in_ty() != &Ty::Tab {
        return Err(Error::wrong_input_type(blk.in_ty(), &blk.op_tag));
    }

    // the expression which will be sorted on
    let key = blk.next_arg(Ty::TabRow)?;

    let ordty = Ty::Def(types::ORD.get());
    let cmpr = BinaryOp::new(
        "cmp",
        key.out_ty(),
        &ordty,
        "sort-by",
        key.tag(),
        blk.defs,
        cnv_value_to_ord,
    )?;

    blk.eval_o::<_, Table>(move |table, cx| {
        let table = Table::try_from(table)?;
        let sorting_values: SortIdx = resolve_trow_expr_par(&table, &key, &cx)?
            .into_iter()
            .enumerate()
            .collect();
        let sorted_values = sort_values(sorting_values, &mut cmpr.pin_env(), &cx)?;
        cx.done_o(reorder_table(table, sorted_values))
    })
}

type SortIdx = Vec<(usize, Value)>;

/// Sort the table according to the order in `values`.
///
/// For each comparison `a` and `b` (which are `Value`s):
///   1. `b` is _set_ as `$rhs`
///   2. comparer is evaluated with `a` as input
///   3. Ord is known to return, and is converted into Ordering
///
/// Table is re-ordered according to sorted values.
fn sort_values<T>(mut values: SortIdx, binop: &mut BinaryOpRef<T>, cx: &Context) -> Result<SortIdx>
where
    T: Fn(Value) -> cmp::Ordering,
{
    let mut err = None;
    // sort values using a comparer
    values[1..].sort_by(|a, b| {
        // lhs is `a`, rhs is `b`
        match binop.eval(a.1.clone(), b.1.clone(), cx) {
            Ok(ord) => ord,
            Err(e) => {
                err = Some(e);
                cmp::Ordering::Equal
            }
        }
    });

    match err {
        Some(e) => Err(e),
        None => Ok(values),
    }
}

fn reorder_table(mut table: Table, order: SortIdx) -> Table {
    let mut x = Vec::with_capacity(table.rows_len());
    if let Some(table) = table.get_mut() {
        let mut table = mem::take(table).into_raw();
        for (idx, _) in order {
            x.push(mem::take(&mut table[idx]));
        }
    } else {
        for (idx, _) in order {
            x.push(table.row(idx).unwrap().cloned().collect());
        }
    }

    ::table::Table::from(x).into()
}

// ------ Sub ------------------------------------------------------------------
fn sub_help() -> HelpMessage {
    variadic_help(
        "-",
        "subtract arguments from one another
note: if input is not a Num, the first arg is used as lhs",
        vec![
            HelpExample {
                desc: "subtract 2 from 1",
                code: "\\ 1 | - 2",
            },
            HelpExample {
                desc: "subtract 1 - 2 = -1",
                code: "- 1 2",
            },
            HelpExample {
                desc: "subtract multiple numbers together",
                code: "- 1 2 3 4 5",
            },
        ],
    )
}

fn sub_intrinsic(blk: Block) -> Result<Step> {
    variadic_intrinsic_num(blk, std::ops::Sub::sub)
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

// ------ Take -----------------------------------------------------------------
fn take_help() -> HelpMessage {
    HelpMessage {
        desc: "take the first n elements of a data structure".into(),
        params: vec![HelpParameter::Required("count".into())],
        examples: vec![
            HelpExample {
                desc: "take the first 10 rows of a table",
                code: "take 10",
            },
            HelpExample {
                desc: "take the first 5 characters of a string",
                code: "\\ 'Hello, world!' | take 5",
            },
            HelpExample {
                desc: "skip and take can be used to slice into a string",
                code: "\\ 'Hello, world!' | skip 7 | take 5",
            },
        ],
        ..HelpMessage::new("take")
    }
}

fn take_intrinsic(mut blk: Block) -> Result<Step> {
    match blk.in_ty() {
        Ty::Tab => {
            let count = blk.next_arg(None)?.returns(&Ty::Num)?;
            blk.eval_o(move |table, cx| {
                let count = count
                    .resolve(|| table.clone(), &cx)
                    .and_then(|v| cnv_num_to_uint::<usize>(v, count.tag()))?;
                let mut table = Table::try_from(table)?;
                if let Some(t) = table.get_mut() {
                    t.retain_rows(|i, _| i == 0 || i <= count);
                } else {
                    let rows = table
                        .rows()
                        .take(1)
                        .chain(table.rows().skip(1).take(count))
                        .map(|x| x.cloned());
                    let mut t = ::table::Table::new();
                    t.add_rows(rows);
                    table = t.into();
                }
                cx.done_o(table)
            })
        }
        Ty::Str => {
            let count = blk.next_arg(None)?.returns(&Ty::Num)?;
            blk.eval_o::<_, Str>(move |string, cx| {
                let count = count
                    .resolve(|| string.clone(), &cx)
                    .and_then(|v| cnv_num_to_uint::<usize>(v, count.tag()))?;
                Str::try_from(string)
                    .map(|s| s.chars().take(count).collect::<Str>())
                    .and_then(|x| cx.done_o(x))
            })
        }
        x => Err(Error::wrong_input_type(x, &blk.op_tag)),
    }
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
    fn build_tuple_eq_test() {
        let f = build_tuple_eq_def_str;
        assert_eq!(&f(1), "def tuple-eq (rhs) { and {get t0 | = $rhs.t0} }");
        assert_eq!(
            &f(2),
            "def tuple-eq (rhs) { and {get t0 | = $rhs.t0} {get t1 | = $rhs.t1} }"
        );
        assert_eq!(&f(3), "def tuple-eq (rhs) { and {get t0 | = $rhs.t0} {get t1 | = $rhs.t1} {get t2 | = $rhs.t2} }");
    }

    #[test]
    fn build_tuple_cmp_test() {
        let f = build_tuple_cmp_def_str;
        assert_eq!(
            &f(1),
            "def tuple-cmp (rhs) { \
let {get t0 | cmp $rhs.t0} $c0 | if \
$c0 }"
        );
        assert_eq!(
            &f(2),
            "def tuple-cmp (rhs) { \
let {get t0 | cmp $rhs.t0} $c0 {get t1 | cmp $rhs.t1} $c1 | if \
{\\ $c0 | != Ord::Eq} $c0 \
$c1 }"
        );
        assert_eq!(
            &f(3),
            "def tuple-cmp (rhs) { \
let {get t0 | cmp $rhs.t0} $c0 {get t1 | cmp $rhs.t1} $c1 {get t2 | cmp $rhs.t2} $c2 | if \
{\\ $c0 | != Ord::Eq} $c0 \
{\\ $c1 | != Ord::Eq} $c1 \
$c2 }"
        );
    }

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

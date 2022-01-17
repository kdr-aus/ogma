mod intrinsics;

use crate::prelude::*;
use ::kserd::Number;
use ::libs::{divvy::Str, rayon::prelude::*};
use ::table::Entry;
use ast::{Location, Tag};
use eng::{Block, Context, Step};
use lang::help::*;
use std::{
    cmp,
    convert::{TryFrom, TryInto},
    fmt,
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

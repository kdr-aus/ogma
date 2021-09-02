use super::{
    ast::{self, DefinitionType, Location, Tag},
    err, impls, parsing, Error, ErrorTrace, HashMap, HelpMessage, Mutex, Result,
};
use ::kserd::{Kserd, Number, ToKserd, ToKserdErr, Value as KValue};
use ::libs::divvy::Str;
use std::{convert::TryFrom, fmt, hash, ops, sync::Arc};
use table::Entry;

// ###### TABLE ################################################################
type TrTable = ::table::Table<Value>;

/// Wrapper of a table, used to specialise drop and cloning behaviour.
#[derive(Clone, PartialEq, Debug, Default)]
pub struct Table(Arc<TrTable>);

impl Table {
    pub fn get_mut(&mut self) -> Option<&mut TrTable> {
        Arc::get_mut(&mut self.0)
    }

    pub fn make_mut(&mut self) -> &mut TrTable {
        Arc::make_mut(&mut self.0)
    }
}

impl From<TrTable> for Table {
    fn from(table: TrTable) -> Self {
        Table(Arc::new(table))
    }
}

impl ops::Deref for Table {
    type Target = TrTable;
    fn deref(&self) -> &TrTable {
        self.0.deref()
    }
}

// TODO once specialisation lands and Table has a specialised drop impl, this can be removed
// Can be substituted for type Table = Arc<Table<'static>>?
impl Drop for Table {
    fn drop(&mut self) {
        self.get_mut()
            .map(|t| {
                let t = std::mem::take(t);
                std::thread::spawn(|| drop(t));
            })
            .unwrap_or(())
    }
}

// ###### TYPE #################################################################
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Type {
    Nil,
    Bool,
    Num,
    Str,
    Tab,
    TabRow,
    Def(Arc<TypeDef>),
}

impl Type {
    pub fn help(&self) -> HelpMessage {
        use Type::*;
        let desc = match self {
            Nil => "nothing value".into(),
            Bool => "boolean value\ntrue | false".into(),
            Num => "number value\n100 | -1 | 3.14 | -1.23e-5".into(),
            Str => "string value".into(),
            Tab => "table value".into(),
            TabRow => "table row".into(),
            Def(tydef) => return tydef.help(),
        };

        HelpMessage {
            desc,
            ..HelpMessage::new(self.to_string())
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let ident = match self {
            Type::Nil => "Nil",
            Type::Bool => "Bool",
            Type::Num => "Number",
            Type::Str => "String",
            Type::Tab => "Table",
            Type::TabRow => "TableRow",
            Type::Def(x) => x.name.str(),
        };

        write!(f, "{}", ident)
    }
}

pub trait AsType {
    fn as_type() -> Type;
}

// ###### VALUE ################################################################
/// The value of an evaluation.
#[derive(Debug, PartialEq, Clone)]
pub enum Value {
    /// Nothing value.
    Nil,
    /// Boolean value.
    Bool(bool),
    /// Number value.
    Num(Number),
    /// String value.
    Str(Str),
    /// Table value.
    Tab(Table),
    /// Table row.
    TabRow(TableRow),
    /// User defined data value.
    Ogma(OgmaData),
}

impl Value {
    /// Get the runtime type.
    pub fn ty(&self) -> Type {
        use Value::*;
        match self {
            Nil => Type::Nil,
            Bool(_) => Type::Bool,
            Num(_) => Type::Num,
            Str(_) => Type::Str,
            Tab(_) => Type::Tab,
            TabRow(_) => Type::TabRow,
            Ogma(x) => Type::Def(x.ty.clone()),
        }
    }

    /// Returns the variant index **IF** the value is a user-defined _sum_ type.
    pub fn variant_idx(&self) -> Option<usize> {
        match self {
            Value::Ogma(x) if matches!(x.ty.ty, TypeVariant::Sum(_)) => Some(x.variant_idx),
            _ => None,
        }
    }
}

/// Clones the [`Value`].
impl From<&Entry<Value>> for Value {
    fn from(e: &Entry<Value>) -> Value {
        match e {
            Entry::Nil => Value::Nil,
            Entry::Num(n) => Value::Num(*n),
            Entry::Obj(v) => v.clone(),
        }
    }
}

impl From<Value> for Entry<Value> {
    fn from(v: Value) -> Self {
        match v {
            Value::Nil => Entry::Nil,
            Value::Num(n) => Entry::Num(n),
            x => Entry::Obj(x),
        }
    }
}

// primitives
macro_rules! prim_type_impls {
    ($($type:ty=>$var:ident),*) => {
        $(
impl AsType for $type {
    fn as_type() -> Type {
        Type::$var
    }
}
impl TryFrom<Value> for $type {
    type Error = crate::Error;
    fn try_from(v: Value) -> Result<Self> {
        match v {
            Value::$var(x) => Ok(x),
            x => Err(Error::conversion_failed(&Type::$var, &x.ty())),
        }
    }
}
impl<'a> TryFrom<&'a Value> for &'a $type {
    type Error = crate::Error;
    fn try_from(v: &'a Value) -> Result<Self> {
        match v {
            Value::$var(x) => Ok(x),
            x => Err(Error::conversion_failed(&Type::$var, &x.ty())),
        }
    }
}
impl From<$type> for Value {
    fn from(x: $type) -> Self {
        Value::$var(x)
    }
}
        )*
    };
}

prim_type_impls!(bool=>Bool, Number=>Num, Str=>Str, Table=>Tab, TableRow=>TabRow);

// additionals that don't fit pattern
impl AsType for () {
    fn as_type() -> Type {
        Type::Nil
    }
}
impl TryFrom<Value> for () {
    type Error = crate::Error;
    fn try_from(v: Value) -> Result<Self> {
        match v {
            Value::Nil => Ok(()),
            x => Err(Error::conversion_failed(&Type::Nil, &x.ty())),
        }
    }
}
impl TryFrom<Value> for OgmaData {
    type Error = crate::Error;
    fn try_from(v: Value) -> Result<Self> {
        match v {
            Value::Ogma(x) => Ok(x),
            x => Err(Error {
                cat: crate::err::Category::Evaluation,
                desc: format!(
                    "converting value into `OgmaData` failed, value has type `{}`",
                    x.ty()
                ),
                traces: Vec::new(),
                help_msg: None,
            }),
        }
    }
}
impl From<()> for Value {
    fn from(_: ()) -> Self {
        Value::Nil
    }
}
impl From<OgmaData> for Value {
    fn from(x: OgmaData) -> Self {
        Value::Ogma(x)
    }
}

// ###### USER TYPES ###########################################################
#[derive(Clone)]
pub struct Types {
    map: HashMap<Str, Type>,
}

impl Types {
    pub fn init(impls: &mut impls::Implementations) -> Self {
        let mut map = HashMap::default();

        map.insert(Str::from("Nil"), Type::Nil);
        map.insert(Str::from("Bool"), Type::Bool);
        map.insert(Str::from("Num"), Type::Num);
        map.insert(Str::from("Str"), Type::Str);
        map.insert(Str::from("Table"), Type::Tab);

        let mut types = Self { map };

        // we add in the ogma primitive types, each one adding onto defs.
        // we can unwrap here as these should always parse just fine (and is tested)
        // we also initialise the associated static references
        let tys = &mut types;
        macro_rules! init {
            ($($id:ident, $ac:literal, $code:literal)|*) => {{
                $(
                tys.insert($code, Location::Ogma, None, impls).unwrap();
                $id.set(match tys.map.get($ac).unwrap() {
                    Type::Def(x) => x.clone(),
                    _ => unreachable!("will always be a a TypeDef"),
                });
                )*
            }};
        }

        init! {
            ORD, "Ord", "def-ty Ord :: Lt | Eq | Gt"
        };

        types
    }

    pub fn get_using_tag(&self, type_name: &Tag) -> Result<&Type> {
        self.get_using_str(type_name.str())
            .ok_or_else(|| Error::type_not_found(type_name))
    }

    pub fn get_using_str(&self, type_name: &str) -> Option<&Type> {
        self.map.get(type_name)
    }

    pub fn contains_type(&self, type_name: &str) -> bool {
        self.map.contains_key(type_name)
    }

    pub fn insert(
        &mut self,
        def: &str,
        loc: Location,
        help: Option<String>,
        impls: &mut impls::Implementations,
    ) -> Result<()> {
        let def = parsing::definition_type(def, loc).map_err(|e| e.0)?;
        let ty = TypeDef::from_parsed_def(def, help, self)?;
        if self.contains_type(ty.name().str()) {
            // TODO allow overwriting type definitions. It will require:
            // a. Error on primitive type defs.
            // b. Relinking any type references previously map to this types name.
            // If no mapping is done, other types defined off this one will still have old
            // reference to them!
            // c. The associated init impl needs to be redone to match the new typedef signature
            let name = ty.name();
            Err(Error {
                cat: err::Category::Semantics,
                desc: format!("can not redefine type `{}`", name),
                traces: vec![ErrorTrace::from_tag(
                    name,
                    format!("`{}` already defined", name),
                )],
                help_msg: Some("try defining your type with a different name".into()),
            })
        } else {
            let ty = Arc::new(ty);
            self.insert_inner(ty.clone());
            impls::add_typedef_init_impls(impls, ty);
            Ok(())
        }
    }

    fn insert_inner(&mut self, typedef: Arc<TypeDef>) {
        let name = Str::new(&typedef.name);
        self.map.insert(name, Type::Def(typedef));
    }

    pub fn clear(&mut self, only_files: bool) {
        self.map.retain(|_, x| match x {
            Type::Def(x) => match &x.loc {
                Location::Ogma => true,
                Location::Shell => only_files,
                Location::File(_, _) => false,
            },
            _ => true,
        })
    }

    pub fn help_iter(&self) -> impl Iterator<Item = (&Str, HelpMessage)> {
        self.map.iter().map(|(n, t)| (n, t.help()))
    }
}

/// Equality and hashing is done on _name alone_.
#[derive(Debug, Clone)]
pub struct TypeDef {
    pub loc: Location,
    src: String,
    help: Option<String>,
    name: Tag,
    ty: TypeVariant,
}

#[derive(Debug, Clone)]
pub enum TypeVariant {
    Sum(Vec<Variant>),
    Product(Fields),
}

type Fields = Vec<Field>;

#[derive(Debug, Clone)]
pub struct Variant {
    pub name: Tag,
    pub fields: Option<Fields>,
}

#[derive(Debug, Clone)]
pub struct Field {
    name: Tag,
    typedef: Tag,
    ty: Type,
    params: Vec<Type>,
}

impl TypeDef {
    pub fn from_parsed_def(
        def: DefinitionType,
        help: Option<String>,
        types: &Types,
    ) -> Result<Self> {
        let DefinitionType { loc, src, name, ty } = def;
        let ty: TypeVariant = match ty {
            ast::TypeVariant::Sum(variants) => {
                let mut v = Vec::with_capacity(variants.len());
                for var in variants {
                    let ast::Variant { name, fields } = var;
                    let fields = if let Some(fields) = fields {
                        Some(from_parsed_fields(fields, types)?)
                    } else {
                        None
                    };
                    v.push(Variant { name, fields });
                }
                TypeVariant::Sum(v)
            }
            ast::TypeVariant::Product(fields) => {
                TypeVariant::Product(from_parsed_fields(fields, types)?)
            }
        };

        Ok(Self {
            loc,
            src,
            help,
            name,
            ty,
        })
    }

    pub fn name(&self) -> &Tag {
        &self.name
    }

    pub fn structure(&self) -> &TypeVariant {
        &self.ty
    }

    pub fn help(&self) -> HelpMessage {
        let cmd = self.name.str().to_string();
        let desc = if let Some(help) = &self.help {
            format!("{}\n`{}`\n\n{}", self.loc, self.src, help)
        } else {
            format!("{}\n`{}`", self.loc, self.src)
        }
        .into();
        HelpMessage {
            desc,
            ..HelpMessage::new(cmd)
        }
    }
}

fn from_parsed_fields(fields: Vec<ast::Field>, types: &Types) -> Result<Vec<Field>> {
    let mut v = Vec::with_capacity(fields.len());
    for field in fields {
        let ast::Field { name, ty, params } = field;
        let typedef = ty;
        let ty = types.get_using_tag(&typedef)?.clone();
        let x = params;
        let mut params = Vec::with_capacity(x.len());
        for param in x {
            params.push(types.get_using_tag(&param)?.clone());
        }

        v.push(Field {
            name,
            typedef,
            ty,
            params,
        });
    }
    Ok(v)
}

impl PartialEq for TypeDef {
    fn eq(&self, rhs: &Self) -> bool {
        self.name.str() == rhs.name.str()
    }
}
impl Eq for TypeDef {}
impl PartialEq<str> for TypeDef {
    fn eq(&self, rhs: &str) -> bool {
        self.name.str() == rhs
    }
}
impl hash::Hash for TypeDef {
    fn hash<H: hash::Hasher>(&self, hasher: &mut H) {
        self.name.str().hash(hasher)
    }
}

impl Field {
    pub fn name(&self) -> &Tag {
        &self.name
    }

    pub fn ty(&self) -> &Type {
        &self.ty
    }
}

// ###### PRIM #################################################################
pub struct PrimTyDef(parking_lot::RwLock<Option<Arc<TypeDef>>>);

impl PrimTyDef {
    const fn new() -> Self {
        PrimTyDef(parking_lot::const_rwlock(None))
    }

    fn set(&self, data: Arc<TypeDef>) {
        let mut lock = self.0.write();
        *lock = Some(data);
    }

    pub fn get(&self) -> Arc<TypeDef> {
        self.0
            .read()
            .clone()
            .expect("have not initialised type definition, Types needs to be initialised first")
    }
}

// ###### DATA #################################################################
#[derive(Debug, PartialEq, Clone)]
pub struct OgmaData(Arc<OgmaDataInner>);

#[derive(Debug, PartialEq, Clone)]
pub struct OgmaDataInner {
    pub(crate) ty: Arc<TypeDef>,
    pub(crate) variant_idx: usize,
    pub(crate) data: Vec<Value>,
}

impl std::ops::Deref for OgmaData {
    type Target = OgmaDataInner;
    fn deref(&self) -> &OgmaDataInner {
        &*self.0
    }
}

impl OgmaData {
    pub fn new<V>(ty: Arc<TypeDef>, variant_idx: V, data: Vec<Value>) -> Self
    where
        V: Into<Option<usize>>,
    {
        OgmaData(Arc::new(OgmaDataInner {
            ty,
            variant_idx: variant_idx.into().unwrap_or_default(),
            data,
        }))
    }

    pub fn get_mut(&mut self) -> Option<&mut OgmaDataInner> {
        Arc::get_mut(&mut self.0)
    }

    pub fn make_mut(&mut self) -> &mut OgmaDataInner {
        Arc::make_mut(&mut self.0)
    }
}

impl ToKserd<'static> for OgmaData {
    fn into_kserd(mut self) -> std::result::Result<Kserd<'static>, ToKserdErr> {
        let this = self.make_mut();
        let data = std::mem::take(&mut this.data);
        match this.ty.structure() {
            TypeVariant::Sum(vars) => {
                let var = &vars[this.variant_idx];
                let name = var.name.to_string();
                if let Some(fields) = &var.fields {
                    Kserd::with_id(name, add_kserd_fields(fields, data)?)
                } else {
                    Kserd::with_id(name, KValue::Unit)
                }
            }
            TypeVariant::Product(fields) => {
                Kserd::with_id(this.ty.name().to_string(), add_kserd_fields(fields, data)?)
            }
        }
        .map_err(Into::into)
    }
}

fn add_kserd_fields(
    fields: &[Field],
    values: Vec<Value>,
) -> std::result::Result<KValue<'static>, ToKserdErr> {
    let mut map = std::collections::BTreeMap::default();

    for (idx, value) in values.into_iter().enumerate() {
        let field = &fields[idx];
        let value = match value {
            Value::Nil => Kserd::new_unit(),
            Value::Bool(b) => Kserd::new_bool(b),
            Value::Num(n) => Kserd::new(KValue::Num(n)),
            Value::Str(s) => Kserd::new_string(s.to_string()),
            Value::Tab(_) => Kserd::new_str("<table>"),
            Value::TabRow(_) => Kserd::new_str("<table row>"),
            Value::Ogma(data) => data.into_kserd()?,
        };
        map.insert(field.name.to_string().into(), value);
    }

    Ok(KValue::Cntr(map))
}

// ###### ORD ##################################################################
pub static ORD: PrimTyDef = PrimTyDef::new();

::lazy_static::lazy_static! {
    pub static ref ORD_LT: OgmaData = OgmaData(Arc::new(OgmaDataInner {
            ty: ORD.get(),
            variant_idx: 0,
            data: vec![],
        }));

    pub static ref ORD_EQ: OgmaData = OgmaData(Arc::new(OgmaDataInner {
            ty: ORD.get(),
            variant_idx: 1,
            data: vec![],
        }));

    pub static ref ORD_GT: OgmaData = OgmaData(Arc::new(OgmaDataInner {
            ty: ORD.get(),
            variant_idx: 2,
            data: vec![],
        }));
}

impl AsType for std::cmp::Ordering {
    fn as_type() -> Type {
        Type::Def(ORD.get())
    }
}

impl From<std::cmp::Ordering> for Value {
    fn from(ord: std::cmp::Ordering) -> Self {
        use std::cmp::Ordering::*;
        match ord {
            Less => Value::Ogma(ORD_LT.clone()),
            Equal => Value::Ogma(ORD_EQ.clone()),
            Greater => Value::Ogma(ORD_GT.clone()),
        }
    }
}

// ###### TABLE ROW ############################################################
pub type TableRowColMap = Arc<Mutex<HashMap<String, usize>>>;

#[derive(Debug, Clone)]
pub struct TableRow {
    pub table: Table,
    /// Row index.
    pub idx: usize,
    pub cached_col_indices: TableRowColMap,
}

impl TableRow {
    /// Retrieve a column index of a table with the given header, otherwise error.
    ///
    /// Meant to be accessible _without_ a `TableRow` object.
    pub fn col_idx(table: &TrTable, col_header: &str, tag: &Tag) -> Result<usize> {
        if let Some(mut header) = table.row(0) {
            if let Some(colidx) =
                header.position(|x| matches!(x, Entry::Obj(Value::Str(y)) if y == col_header))
            {
                Ok(colidx)
            } else {
                Err(Error::header_not_found(col_header, tag))
            }
        } else {
            Err(Error::empty_table(col_header, tag))
        }
    }

    /// Retrive an entry at `(row, col)`. Use if _rowidx_ and _colidx_ are known an can be
    /// memoized.
    ///
    /// # Panics
    /// Panics if either `rowidx` or `colidx` are out of bounds.
    pub fn entry_at(table: &TrTable, rowidx: usize, colidx: usize) -> &Entry<Value> {
        table
            .row(rowidx)
            .and_then(|mut r| r.nth(colidx))
            .expect("trying to access entry outside table bounds")
    }

    pub fn cnv_value<C: fmt::Display>(
        entry: &Entry<Value>,
        exp: &Type,
        rowidx: usize,
        colname: C,
        coltag: &Tag,
    ) -> Result<Value> {
        let entry: Value = entry.into();
        let ty = &entry.ty();
        if ty != exp {
            Err(Error::unexp_entry_ty(exp, ty, rowidx, colname, coltag))
        } else {
            Ok(entry)
        }
    }

    pub fn new(table: Table, colmap: TableRowColMap, idx: usize) -> Self {
        Self {
            table,
            idx,
            cached_col_indices: colmap,
        }
    }

    pub fn entry(&self, col_header: &str, tag: &Tag) -> Result<&Entry<Value>> {
        let colidx = self.get_col_idx(col_header, tag)?;
        Ok(Self::entry_at(&self.table, self.idx, colidx))
    }

    fn get_col_idx(&self, col_header: &str, tag: &Tag) -> Result<usize> {
        let i = self.cached_col_indices.lock().get(col_header).copied();
        match i {
            Some(i) => Ok(i),
            None => Self::col_idx(&self.table, col_header, tag).map(|idx| {
                self.cached_col_indices
                    .lock()
                    .insert(col_header.into(), idx);
                idx
            }),
        }
    }
}

impl PartialEq for TableRow {
    fn eq(&self, other: &Self) -> bool {
        self.idx == other.idx
            && self.table == other.table
            && Arc::ptr_eq(&self.cached_col_indices, &other.cached_col_indices)
    }
}

// ###### TUPLES ###############################################################
// tuples are not defined in the types, instead they are defined in the HIR phase.
pub struct Tuple;
impl Tuple {
    fn tyname(ty: &Type) -> &str {
        match ty {
            Type::Nil => "Nil",
            Type::Bool => "Bool",
            Type::Num => "Num",
            Type::Str => "Str",
            Type::Tab => "Table",
            Type::TabRow => "TableRow",
            Type::Def(x) => x.name.str(),
        }
    }

    fn name(args: &[Type]) -> String {
        use std::fmt::Write;
        let mut name = "U_".to_string();
        for a in args {
            write!(&mut name, "{}-", Self::tyname(a)).ok();
        }
        name.pop();
        name.push('_');
        name
    }

    pub fn ty(args: Vec<Type>) -> TypeDef {
        use std::fmt::Write;
        let name = Self::name(&args);

        let mut i = 0;
        let fields = args
            .iter()
            .map(|a| {
                let x = (format!("t{}", i), Self::tyname(a).to_string());
                i += 1;
                x
            })
            .collect::<Vec<_>>();

        // build string
        let src = {
            let mut src = format!("{} {{ ", name);
            for (n, t) in &fields {
                write!(&mut src, "{}:{} ", n, t).ok();
            }
            src.push('}');
            src
        };

        // build tags
        let t = Tag {
            anchor: Location::Ogma,
            line: Arc::from(src.as_str()),
            start: 0,
            end: 0,
        };

        let name = Tag {
            end: name.len(),
            ..t.clone()
        };

        let mut s = name.end + 3;
        let fields: Vec<Field> = args
            .into_iter()
            .zip(fields.into_iter())
            .map(|(arg, (name, ty))| {
                let name = Tag {
                    start: s,
                    end: s + name.len(),
                    ..t.clone()
                };
                s = name.end + 1;
                let typedef = Tag {
                    start: s,
                    end: s + ty.len(),
                    ..t.clone()
                };
                s = typedef.end + 1;
                Field {
                    name,
                    typedef,
                    ty: arg,
                    params: Vec::new(),
                }
            })
            .collect();

        TypeDef {
            loc: Location::Ogma,
            src,
            help: None,
            name,
            ty: TypeVariant::Product(fields),
        }
    }

    pub fn parse_name(tuple: &str, tys: &Types) -> Option<Type> {
        Split::parse(tuple).and_then(|x| Self::convert_split(x, tys))
    }

    fn convert_split(split: Split, tys: &Types) -> Option<Type> {
        match split {
            Split::Tuple(v) => {
                let mut args = Vec::with_capacity(v.len());
                for x in v {
                    args.push(Self::convert_split(x, tys)?);
                }
                Some(Type::Def(Arc::new(Self::ty(args))))
            }
            Split::Ty(t) => tys.get_using_str(t).cloned(),
        }
    }
}

#[derive(Debug, PartialEq)]
enum Split<'a> {
    Tuple(Vec<Split<'a>>),
    Ty(&'a str),
}

impl<'a> Split<'a> {
    fn parse(s: &'a str) -> Option<Self> {
        use ::nom::{
            bytes::complete::*, character::complete::*, combinator::*, multi::*, sequence::*, *,
        };
        type R<'a, T> = IResult<&'a str, T, ()>;

        fn parse_tuple(i: &str) -> R<Vec<Split>> {
            preceded(
                tag("U_"),
                terminated(separated_list1(char('-'), parse_split), char('_')),
            )(i)
        }
        fn parse_split(i: &str) -> R<Split<'_>> {
            if i.starts_with("U_") {
                map(parse_tuple, Split::Tuple)(i)
            } else {
                map(take_till1(|c| c == '-' || c == '_'), Split::Ty)(i)
            }
        }

        map(all_consuming(parse_tuple), Split::Tuple)(s)
            .ok()
            .map(|(_, x)| x)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use Type::*;

    #[test]
    fn display_impl() {
        let ty = vec![Nil, Bool, Num, Str, Tab, TabRow, Def(ORD.get())]
            .iter()
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        assert_eq!(&ty, "Nil, Bool, Number, String, Table, TableRow, Ord");
    }

    fn x(t: Type) -> String {
        t.help().to_string()
    }

    #[test]
    fn prim_type_help_messages() {
        assert_eq!(
            &x(Nil),
            "Help: `Nil`
--> shell:0
 | nothing value
 | 
 | Usage:
 |  => Nil
"
        );
        assert_eq!(
            &x(Bool),
            "Help: `Bool`
--> shell:0
 | boolean value
 | true | false
 | 
 | Usage:
 |  => Bool
"
        );
        assert_eq!(
            &x(Num),
            "Help: `Number`
--> shell:0
 | number value
 | 100 | -1 | 3.14 | -1.23e-5
 | 
 | Usage:
 |  => Number
"
        );
        assert_eq!(
            &x(Str),
            "Help: `String`
--> shell:0
 | string value
 | 
 | Usage:
 |  => String
"
        );
        assert_eq!(
            &x(Tab),
            "Help: `Table`
--> shell:0
 | table value
 | 
 | Usage:
 |  => Table
"
        );
        assert_eq!(
            &x(TabRow),
            "Help: `TableRow`
--> shell:0
 | table row
 | 
 | Usage:
 |  => TableRow
"
        );
    }

    #[test]
    fn ord_ty_help_msg() {
        assert_eq!(
            &x(Def(ORD.get())),
            "Help: `Ord`
--> shell:0
 | <ogma>
 | `def-ty Ord :: Lt | Eq | Gt`
 | 
 | Usage:
 |  => Ord
"
        );
    }

    #[test]
    fn tuple_type_testing() {
        let args = [Type::Nil, Type::Num, Type::Str];

        let ty = Tuple::ty(args[..2].to_vec());
        assert_eq!(ty.name().str(), "U_Nil-Num_");
        match ty.structure() {
            TypeVariant::Product(x) => {
                assert_eq!(x[0].name().str(), "t0");
                assert_eq!(x[0].ty(), &Type::Nil);
                assert_eq!(x[1].name().str(), "t1");
                assert_eq!(x[1].ty(), &Type::Num);
            }
            _ => panic!(),
        }

        let ty = Tuple::ty(args[1..].to_vec());
        assert_eq!(ty.name().str(), "U_Num-Str_");
        match ty.structure() {
            TypeVariant::Product(x) => {
                assert_eq!(x[0].name().str(), "t0");
                assert_eq!(x[0].ty(), &Type::Num);
                assert_eq!(x[1].name().str(), "t1");
                assert_eq!(x[1].ty(), &Type::Str);
            }
            _ => panic!(),
        }

        let ty = Tuple::ty(args[..].to_vec());
        assert_eq!(ty.name().str(), "U_Nil-Num-Str_");
        match ty.structure() {
            TypeVariant::Product(x) => {
                assert_eq!(x[0].name().str(), "t0");
                assert_eq!(x[0].ty(), &Type::Nil);
                assert_eq!(x[1].name().str(), "t1");
                assert_eq!(x[1].ty(), &Type::Num);
                assert_eq!(x[2].name().str(), "t2");
                assert_eq!(x[2].ty(), &Type::Str);
            }
            _ => panic!(),
        }
    }

    #[test]
    fn tuple_parse_name_testing() {
        let tys = crate::defs::Definitions::new();
        assert_eq!(
            Some(Type::Def(Arc::new(Tuple::ty(vec![
                Type::Nil,
                Type::Num,
                Type::Str
            ])))),
            Tuple::parse_name("U_Nil-Num-Str_", tys.types())
        )
    }

    #[test]
    fn split_parse_testing() {
        use Split::*;
        let f = Split::parse;

        assert_eq!(f(""), None);
        assert_eq!(f("fdsaff sfdsa"), None);
        assert_eq!(f("   "), None);
        assert_eq!(f("U__"), None);
        assert_eq!(f("U_    _"), Some(Tuple(vec![Ty("    ")])));
        assert_eq!(f("U_Nil_"), Some(Tuple(vec![Ty("Nil")])));
        assert_eq!(
            f("U_Nil-Num-Str_"),
            Some(Tuple(vec![Ty("Nil"), Ty("Num"), Ty("Str")]))
        );
        assert_eq!(f("U_Nil-Num-Str-_"), None);
        assert_eq!(f("U_Nil-Num-Str"), None);
        assert_eq!(
            f("U_Nil-U_Num-Str_-Str_"),
            Some(Tuple(vec![
                Ty("Nil"),
                Tuple(vec![Ty("Num"), Ty("Str")]),
                Ty("Str")
            ]))
        );
    }
}

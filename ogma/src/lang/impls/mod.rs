mod intrinsics;

use crate::prelude::*;
use ast::{Location, Tag};
use eng::{Block, Step};
use lang::{defs2, help::*};
use libs::divvy::Str;
use std::{fmt, iter::*};

pub type IntrinsicFn = Arc<dyn Fn(Block) -> Result<Step> + Send + Sync>;

#[derive(Clone)]
pub enum Implementation {
    Intrinsic { loc: Location, f: IntrinsicFn },
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

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
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

type Impl = (Implementation, OperationCategory, HelpMessage);

pub struct Impl2 {
    pub inner: Implementation,
    pub inty: Option<Type>,
    pub cat: OperationCategory,
    pub help: HelpMessage,
}

#[derive(Clone)]
// Structure is a nested map of maps, first by the command name, then by the input type.
pub struct Implementations(HashMap<Str, Keys>);

#[derive(Clone, Default)]
struct Keys {
    tys: HashMap<Type, Impl>,
    agnostic: Option<Impl>,
}

impl Keys {
    /// Get the [`Impl`] keyed on `ty`. If none are present, tries to get an impl keyed on `None`.
    fn get_impl(&self, ty: &Type) -> Option<&Impl> {
        self.tys.get(ty).or(self.agnostic.as_ref())
    }

    fn iter(&self) -> impl Iterator<Item = (Option<&Type>, &Impl)> {
        self.tys
            .iter()
            .map(|(t, x)| (Some(t), x))
            .chain(self.agnostic.iter().map(|x| (None, x)))
    }

    fn retain<F>(&mut self, mut predicate: F)
    where
        F: FnMut(Option<&Type>, &Implementation, &OperationCategory, &HelpMessage) -> bool,
    {
        self.tys.retain(|t, (i, o, h)| predicate(Some(t), i, o, h));
        self.agnostic = self
            .agnostic
            .take()
            .filter(|(i, o, h)| predicate(None, i, o, h));
    }

    fn is_empty(&self) -> bool {
        self.tys.is_empty() && self.agnostic.is_none()
    }
}

impl Default for Implementations {
    fn default() -> Self {
        let mut impls = Implementations(HashMap::default());
        intrinsics::add_intrinsics(&mut impls);
        impls
    }
}

/// An implementation entry.
pub struct ImplEntry<'a> {
    /// The command/op name.
    pub name: &'a Str,
    /// The input type this is keyed on.
    pub ty: Option<&'a Type>,
    /// Command category.
    pub cat: OperationCategory,
    /// Command help.
    pub help: &'a HelpMessage,
    /// The implementation.
    pub impl_: &'a Implementation,
}

impl Implementations {
    /// Is there an op with `name`?
    pub fn contains_op(&self, name: &str) -> bool {
        self.0.contains_key(name)
    }

    /// Gets the specific help message of a command given the input type.
    pub fn get_help(&self, op: &str, ty: &Type) -> Option<&HelpMessage> {
        self.0.get(op)?.get_impl(ty).map(|x| &x.2)
    }

    /// **Builds** the help message which concatenates all applicable input types.
    pub fn get_help_all(&self, op: &str) -> Option<Error> {
        let mut xs = self
            .0
            .get(op)?
            .iter()
            .map(|(t, (_, _, x))| (t, x))
            .collect::<Vec<_>>();
        xs.sort_unstable_by_key(|a| a.0.map(ToString::to_string));

        xs.into_iter()
            .map(|(t, x)| err::help_as_error(x, t))
            .reduce(|mut acc, x| {
                if let Some((a, b)) = acc.traces.get_mut(0).zip(x.traces.get(0)) {
                    if !a.source.ends_with('\n') {
                        a.source += "\n";
                    }
                    a.source += "\n";
                    a.source += &b.source;
                }
                acc
            })
    }

    /// **Builds** the help message which concatenates all applicable input types.
    /// If `op` is not found, returns an error.
    pub fn get_help_with_err(&self, op: &Tag) -> Result<Error> {
        self.get_help_all(op.str())
            .ok_or_else(|| Error::op_not_found(op, None, false, self))
    }

    /// Find the appropriate [`Implementation`] for the command `op` with the input `ty`pe.
    /// This will _fallback_ to commands which have agnostic input types if no specific
    /// implementation is found.
    pub fn get_impl(&self, op: &str, ty: &Type) -> Option<&Implementation> {
        self.0.get(op)?.get_impl(ty).map(|x| &x.0)
    }

    /// Helper which is the same as [`Self::get_impl`] but creates an [`Error`] upon failure.
    pub fn get_impl_with_err(&self, op: &Tag, ty: &Type) -> Result<&Implementation> {
        match self.contains_op(op.str()) {
            true => self
                .get_impl(op.str(), ty)
                .ok_or_else(|| Error::impl_not_found(op, ty)),
            false => Err(Error::op_not_found(op, Some(ty), false, self)),
        }
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
        let keys = self.0.entry(name).or_default();

        let impl_ = (
            Implementation::Intrinsic {
                loc,
                f: Arc::new(f),
            },
            cat,
            help,
        );
        let _not_overwritten = match in_ty.into() {
            Some(t) => keys.tys.insert(t, impl_).is_none(),
            None => {
                let x = keys.agnostic.is_none();
                keys.agnostic = Some(impl_);
                x
            }
        };
        debug_assert!(
            _not_overwritten,
            "intrinsics should not overwrite one another"
        );
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
        let name = def.name.str();
        let ty = in_ty.into();
        // we check that the impl does not conflict with ogma defined ones
        let ogma_defined = self
            .0
            .get(name)
            .and_then(|x| match &ty {
                Some(t) => x.tys.get(t),
                None => x.agnostic.as_ref(),
            })
            .map(|(im, _, _)| im)
            .filter(|im| match im {
                Implementation::Intrinsic { .. } => true,
                Implementation::Definition(x) if x.loc == Location::Ogma => true,
                _ => false,
            })
            .is_some();

        if ogma_defined {
            return Err(Error::predefined_impl(&def, ty.as_ref()));
        }

        let name = Str::new(name);

        let keys = self.0.entry(name).or_default();
        let impl_ = (Implementation::Definition(Box::new(def)), cat, help);

        match ty {
            Some(t) => {
                keys.tys.insert(t, impl_);
            }
            None => keys.agnostic = Some(impl_),
        }

        Ok(())
    }

    /// Iterate over _all_ the implementations.
    pub fn iter(&self) -> impl Iterator<Item = ImplEntry> {
        self.0.keys().flat_map(|name| self.iter_op(name))
    }

    /// Iterate over _all_ the implementations for `op`.
    pub fn iter_op<'a>(&'a self, op: &str) -> impl Iterator<Item = ImplEntry<'a>> {
        self.0
            .get_key_value(op)
            .into_iter()
            .flat_map(|(name, map)| {
                map.iter().map(|(ty, (impl_, cat, help))| ImplEntry {
                    name,
                    ty,
                    cat: *cat,
                    help,
                    impl_,
                })
            })
    }

    /// Remove any loaded implementations, reducing the implementations down to what is defined in
    /// `ogma`. If `only_files` is `true`, items defined in the shell are retained.
    pub fn clear(&mut self, only_files: bool) {
        self.0.values_mut().for_each(|m| {
            m.retain(|_, im, _, _| match im.location() {
                Location::Ogma => true,
                Location::Shell => only_files,
                Location::File(_, _) => false,
            })
        });
        self.0.retain(|_, m| !m.is_empty())
    }
}

pub fn init(mut defs: defs2::Definitions) -> defs2::Definitions {
    todo!()
}

pub fn init_derived_impls(mut defs: defs2::Definitions) -> defs2::Definitions {
    todo!()
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
pub fn add_typedef_init_impls2(defs: &mut defs2::Definitions, tydef: Arc<types::TypeDef>) {
    todo!()
}

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
        let arg = blk
            .next_arg()?
            .supplied(None)?
            .returns(field.ty().clone())?
            .concrete()?;
        value_places.push(arg);
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

mod intrinsics;

use crate::prelude::*;
use ast::{Location, Tag};
use eng::{Block, Step};
use lang::help::*;
use libs::divvy::Str;
use std::{fmt, iter::*};

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

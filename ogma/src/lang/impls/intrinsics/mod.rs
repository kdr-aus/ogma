use super::*;
use ::paste::paste;

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
    morphism::add_intrinsics(impls);
    pipeline::add_intrinsics(impls);
    logic::add_intrinsics(impls);
}

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
mod diagnostics;

pub fn add_intrinsics(impls: &mut Implementations) {
    add! { impls,
        // Cmp -------------------------------------------------
        (cmp, Cmp)
        (eq, Cmp)
        (max, Cmp)
        (min, Cmp)
        // Logic -----------------------------------------------
        (and, Logic)
        (if, Logic)
        (not, Logic)
        (or, Logic)
        // Morphism --------------------------------------------
        (append, Morphism)
        ("append-row", append_row, Morphism)
        (dedup, Morphism)
        (filter, Morphism)
        (fold, Morphism)
        ("fold-while", fold_while, Morphism)
        (grp, Morphism)
        ("grp-by", grpby, Morphism)
        (map, Morphism)
        (pick, Morphism)
        (ren, Morphism)
        ("ren-with", ren_with, Morphism)
        (rev, Morphism)
        (skip, Morphism)
        (sort, Morphism)
        ("sort-by", sortby, Morphism)
        (take, Morphism)
        // Pipeline --------------------------------------------
        (get, Pipeline)
        (
            ".",
            ast::DotOperatorBlock::instrinsic,
            Pipeline,
            ast::DotOperatorBlock::help
        )
        ("\\", in, Pipeline)
        (len, Pipeline)
        (let, Pipeline)
        (nth, Pipeline)
        (rand, Pipeline)
        (range, Pipeline)
        (Table, table, Pipeline)
        ("to-str", to_str, Pipeline)
        (Tuple, tuple, Pipeline)
        // Io --------------------------------------------------
        (ls, Io)
        (open, Io)
        (save, Io)

        // ---- Specialised instrinsic ops --------------
    };

    arithmetic::add_intrinsics(impls);
    diagnostics::add_intrinsics(impls);
}

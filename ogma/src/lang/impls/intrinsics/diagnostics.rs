use super::*;

pub fn add_intrinsics(impls: &mut Implementations) {
    add! { impls,
        (benchmark, Diagnostics)
        (typify, Diagnostics)
    };
}

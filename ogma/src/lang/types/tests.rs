use super::*;
use quickcheck::{Arbitrary, Gen};
use Type::*;

impl Arbitrary for Type {
    fn arbitrary(g: &mut Gen) -> Self {
        match u8::arbitrary(g) % 6 {
            0 => Nil,
            1 => Bool,
            2 => Num,
            3 => Str,
            4 => Tab,
            5 => TabRow,
            _ => unreachable!(),
        }
    }
}

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
    crate::common::err::help_as_error(&t.help(), None).to_string()
}

#[test]
fn prim_type_help_messages() {
    assert_eq!(
        &x(Nil),
        "Help: `Nil`
--> shell:0
 | ---- Input Type: <any> ----
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
 | ---- Input Type: <any> ----
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
 | ---- Input Type: <any> ----
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
 | ---- Input Type: <any> ----
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
 | ---- Input Type: <any> ----
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
 | ---- Input Type: <any> ----
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
 | ---- Input Type: <any> ----
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
    let tys = crate::prelude::Definitions::new();
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

#[quickcheck]
fn type_cmp(a: Type, b: Type) -> bool {
    a.cmp(&b) == b.cmp(&a).reverse()
}

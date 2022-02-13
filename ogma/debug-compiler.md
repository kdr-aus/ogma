# Compiler Debug Report
## AST Graph Nodes
---
```kserd
header = ["Index","AST Node"]
data = [
    [0,"Expr(ls | filter { get 'foo' | > 'bar' })"]
    [1,"Op(ls)"]
    [2,"Op(filter)"]
    [3,"Expr({ get 'foo' | > 'bar' })"]
    [4,"Op(get)"]
    [5,"Ident(foo)"]
    [6,"Op(>)"]
    [7,"Ident(bar)"]
    [8,"Intrinsic"]
    [9,"Intrinsic"]
    [10,"Intrinsic"]
    [11,"Def"]
    [12,"Expr(cmp $rhs | = Ord::Gt )"]
    [13,"Op(cmp)"]
    [14,"Var($rhs)"]
    [15,"Op(=)"]
    [16,"Expr(Ord::Gt )"]
    [17,"Op(Ord::Gt)"]
    [18,"Intrinsic"]
    [19,"Def"]
    [20,"Expr(eq $rhs )"]
    [21,"Op(eq)"]
    [22,"Var($rhs)"]
    [23,"Intrinsic"]
    [24,"Intrinsic"]
]
rowslim = 200
```
## AST Graph Chart
---
```mermaid
flowchart TD
i0["0 :: Expr(ls | filter { get 'foo' | > 'bar' }) <br> Known(Nil) & Known(Table)"]
i1["1 :: Op(ls) <br> Known(Nil) & Known(Table)"]
i2["2 :: Op(filter) <br> Known(Table) & Known(Table)"]
i3["3 :: Expr({ get 'foo' | > 'bar' }) <br> Known(TableRow) & Obliged(Bool)"]
i4["4 :: Op(get) <br> Known(TableRow) & Known(Bool)"]
i5["5 :: Ident(foo) <br> Any & Known(String)"]
i6["6 :: Op(>) <br> Known(Bool) & Unknown"]
i7["7 :: Ident(bar) <br> Any & Known(String)"]
i8["8 :: Intrinsic <br> Unknown & Unknown"]
i9["9 :: Intrinsic <br> Unknown & Unknown"]
i10["10 :: Intrinsic <br> Unknown & Unknown"]
i11["11 :: Def <br> Known(Bool) & Unknown"]
i12["12 :: Expr(cmp $rhs | = Ord::Gt ) <br> Known(Bool) & Unknown"]
i13["13 :: Op(cmp) <br> Known(Bool) & Unknown"]
i14["14 :: Var($rhs) <br> Known(Bool) & Known(String)"]
i15["15 :: Op(=) <br> Unknown & Unknown"]
i16["16 :: Expr(Ord::Gt ) <br> Unknown & Unknown"]
i17["17 :: Op(Ord::Gt) <br> Unknown & Unknown"]
i18["18 :: Intrinsic <br> Unknown & Unknown"]
i19["19 :: Def <br> Unknown & Unknown"]
i20["20 :: Expr(eq $rhs ) <br> Unknown & Unknown"]
i21["21 :: Op(eq) <br> Unknown & Unknown"]
i22["22 :: Var($rhs) <br> Unknown & Unknown"]
i23["23 :: Intrinsic <br> Unknown & Unknown"]
i24["24 :: Intrinsic <br> Unknown & Unknown"]

i0 -- "Normal" --> i1
i0 -- "Normal" --> i2
i2 -- "Normal" --> i3
i3 -- "Normal" --> i4
i4 -- "Normal" --> i5
i3 -- "Normal" --> i6
i6 -- "Normal" --> i7
i1 -- "Keyed(None)" --> i8
i2 -- "Keyed(None)" --> i9
i3 -- "Term(0)" --> i9
i4 -- "Keyed(None)" --> i10
i5 -- "Term(0)" --> i10
i12 -- "Normal" --> i13
i13 -- "Normal" --> i14
i12 -- "Normal" --> i15
i15 -- "Normal" --> i16
i16 -- "Normal" --> i17
i11 -- "Normal" --> i12
i6 -- "Keyed(None)" --> i11
i7 -- "Term(0)" --> i11
i13 -- "Keyed(None)" --> i18
i14 -- "Term(0)" --> i18
i20 -- "Normal" --> i21
i21 -- "Normal" --> i22
i19 -- "Normal" --> i20
i15 -- "Keyed(None)" --> i19
i16 -- "Term(0)" --> i19
i17 -- "Keyed(None)" --> i23
i21 -- "Keyed(None)" --> i24
i22 -- "Term(0)" --> i24
```
## Type Graph Chart
---
```mermaid
flowchart TD
i0["0 :: Expr(ls | filter { get 'foo' | > 'bar' }) <br> Known(Nil) & Known(Table)"]
i1["1 :: Op(ls) <br> Known(Nil) & Known(Table)"]
i2["2 :: Op(filter) <br> Known(Table) & Known(Table)"]
i3["3 :: Expr({ get 'foo' | > 'bar' }) <br> Known(TableRow) & Obliged(Bool)"]
i4["4 :: Op(get) <br> Known(TableRow) & Known(Bool)"]
i5["5 :: Ident(foo) <br> Any & Known(String)"]
i6["6 :: Op(>) <br> Known(Bool) & Unknown"]
i7["7 :: Ident(bar) <br> Any & Known(String)"]
i8["8 :: Intrinsic <br> Unknown & Unknown"]
i9["9 :: Intrinsic <br> Unknown & Unknown"]
i10["10 :: Intrinsic <br> Unknown & Unknown"]
i11["11 :: Def <br> Known(Bool) & Unknown"]
i12["12 :: Expr(cmp $rhs | = Ord::Gt ) <br> Known(Bool) & Unknown"]
i13["13 :: Op(cmp) <br> Known(Bool) & Unknown"]
i14["14 :: Var($rhs) <br> Known(Bool) & Known(String)"]
i15["15 :: Op(=) <br> Unknown & Unknown"]
i16["16 :: Expr(Ord::Gt ) <br> Unknown & Unknown"]
i17["17 :: Op(Ord::Gt) <br> Unknown & Unknown"]
i18["18 :: Intrinsic <br> Unknown & Unknown"]
i19["19 :: Def <br> Unknown & Unknown"]
i20["20 :: Expr(eq $rhs ) <br> Unknown & Unknown"]
i21["21 :: Op(eq) <br> Unknown & Unknown"]
i22["22 :: Var($rhs) <br> Unknown & Unknown"]
i23["23 :: Intrinsic <br> Unknown & Unknown"]
i24["24 :: Intrinsic <br> Unknown & Unknown"]

i0 -- "II" --> i1
i3 -- "II" --> i4
i12 -- "II" --> i13
i16 -- "II" --> i17
i20 -- "II" --> i21
i2 -- "OO" --> i0
i6 -- "OO" --> i3
i15 -- "OO" --> i12
i17 -- "OO" --> i16
i21 -- "OO" --> i20
i1 -- "OI" --> i2
i4 -- "OI" --> i6
i13 -- "OI" --> i15
i6 -- "II" --> i11
i11 -- "II" --> i12
i12 -- "OO" --> i11
i11 -- "OO" --> i6
i15 -- "II" --> i19
i19 -- "II" --> i20
i20 -- "OO" --> i19
i19 -- "OO" --> i15
```
## Current Locals
---
```
13 :: Op(cmp)
2 :: Op(filter)
4 :: Op(get)
1 :: Op(ls)
6 :: Op(>)
```

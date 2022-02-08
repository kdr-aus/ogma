# Compiler Debug Report
## AST Graph Nodes
---
```kserd
header = ["Index","AST Node"]
data = [
    [0,"Expr(\ 3 | > 2)"]
    [1,"Op(\)"]
    [2,"Num(3)"]
    [3,"Op(>)"]
    [4,"Num(2)"]
    [5,"Intrinsic"]
    [6,"Def"]
    [7,"Expr(cmp $rhs | = Ord::Gt )"]
    [8,"Op(cmp)"]
    [9,"Var($rhs)"]
    [10,"Op(=)"]
    [11,"Expr(Ord::Gt )"]
    [12,"Op(Ord::Gt)"]
    [13,"Intrinsic"]
    [14,"Def"]
    [15,"Expr(eq $rhs )"]
    [16,"Op(eq)"]
    [17,"Var($rhs)"]
    [18,"Intrinsic"]
    [19,"Intrinsic"]
]
rowslim = 200
```
## AST Graph Chart
---
```mermaid
flowchart TD
i0["0 :: Expr(\ 3 | > 2) <br> Known(Nil) & Known(Bool)"]
i1["1 :: Op(\) <br> Known(Nil) & Known(Number)"]
i2["2 :: Num(3) <br> Any & Known(Number)"]
i3["3 :: Op(>) <br> Known(Number) & Known(Bool)"]
i4["4 :: Num(2) <br> Any & Known(Number)"]
i5["5 :: Intrinsic <br> Unknown & Unknown"]
i6["6 :: Def <br> Known(Number) & Known(Bool)"]
i7["7 :: Expr(cmp $rhs | = Ord::Gt ) <br> Known(Number) & Known(Bool)"]
i8["8 :: Op(cmp) <br> Known(Number) & Known(Ord)"]
i9["9 :: Var($rhs) <br> Known(Number) & Known(Number)"]
i10["10 :: Op(=) <br> Known(Ord) & Known(Bool)"]
i11["11 :: Expr(Ord::Gt ) <br> Unknown & Unknown"]
i12["12 :: Op(Ord::Gt) <br> Unknown & Unknown"]
i13["13 :: Intrinsic <br> Unknown & Unknown"]
i14["14 :: Def <br> Known(Ord) & Known(Bool)"]
i15["15 :: Expr(eq $rhs ) <br> Known(Ord) & Known(Bool)"]
i16["16 :: Op(eq) <br> Known(Ord) & Known(Bool)"]
i17["17 :: Var($rhs) <br> Known(Ord) & Obliged(Ord)"]
i18["18 :: Intrinsic <br> Unknown & Unknown"]
i19["19 :: Intrinsic <br> Unknown & Unknown"]

i0 -- "Normal" --> i1
i1 -- "Normal" --> i2
i0 -- "Normal" --> i3
i3 -- "Normal" --> i4
i1 -- "Keyed(None)" --> i5
i2 -- "Term(0)" --> i5
i7 -- "Normal" --> i8
i8 -- "Normal" --> i9
i7 -- "Normal" --> i10
i10 -- "Normal" --> i11
i11 -- "Normal" --> i12
i6 -- "Normal" --> i7
i3 -- "Keyed(None)" --> i6
i4 -- "Term(0)" --> i6
i8 -- "Keyed(None)" --> i13
i9 -- "Term(0)" --> i13
i15 -- "Normal" --> i16
i16 -- "Normal" --> i17
i14 -- "Normal" --> i15
i10 -- "Keyed(None)" --> i14
i11 -- "Term(0)" --> i14
i12 -- "Keyed(None)" --> i18
i16 -- "Keyed(None)" --> i19
i17 -- "Term(0)" --> i19
```
## Type Graph Chart
---
```mermaid
flowchart TD
i0["0 :: Expr(\ 3 | > 2) <br> Known(Nil) & Known(Bool)"]
i1["1 :: Op(\) <br> Known(Nil) & Known(Number)"]
i2["2 :: Num(3) <br> Any & Known(Number)"]
i3["3 :: Op(>) <br> Known(Number) & Known(Bool)"]
i4["4 :: Num(2) <br> Any & Known(Number)"]
i5["5 :: Intrinsic <br> Unknown & Unknown"]
i6["6 :: Def <br> Known(Number) & Known(Bool)"]
i7["7 :: Expr(cmp $rhs | = Ord::Gt ) <br> Known(Number) & Known(Bool)"]
i8["8 :: Op(cmp) <br> Known(Number) & Known(Ord)"]
i9["9 :: Var($rhs) <br> Known(Number) & Known(Number)"]
i10["10 :: Op(=) <br> Known(Ord) & Known(Bool)"]
i11["11 :: Expr(Ord::Gt ) <br> Unknown & Unknown"]
i12["12 :: Op(Ord::Gt) <br> Unknown & Unknown"]
i13["13 :: Intrinsic <br> Unknown & Unknown"]
i14["14 :: Def <br> Known(Ord) & Known(Bool)"]
i15["15 :: Expr(eq $rhs ) <br> Known(Ord) & Known(Bool)"]
i16["16 :: Op(eq) <br> Known(Ord) & Known(Bool)"]
i17["17 :: Var($rhs) <br> Known(Ord) & Obliged(Ord)"]
i18["18 :: Intrinsic <br> Unknown & Unknown"]
i19["19 :: Intrinsic <br> Unknown & Unknown"]

i0 -- "II" --> i1
i7 -- "II" --> i8
i11 -- "II" --> i12
i15 -- "II" --> i16
i3 -- "OO" --> i0
i10 -- "OO" --> i7
i12 -- "OO" --> i11
i16 -- "OO" --> i15
i1 -- "OI" --> i3
i8 -- "OI" --> i10
i3 -- "II" --> i6
i6 -- "II" --> i7
i7 -- "OO" --> i6
i6 -- "OO" --> i3
i10 -- "II" --> i14
i14 -- "II" --> i15
i15 -- "OO" --> i14
i14 -- "OO" --> i10
```
## Current Locals
---
```
8 :: Op(cmp)
10 :: Op(=)
12 :: Op(Ord::Gt)
1 :: Op(\)
3 :: Op(>)
```

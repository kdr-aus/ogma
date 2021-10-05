<iframe src="./.ibox.html?raw=true" style="border:none; position:fixed; width:40px; right:0; z-index=999;"></iframe>

# (No) Recursion

Recursion is **not** supported in ogma. _This is intentional for the static type
checking **and** lazy evaluation_. If a definition is defined which is not comprised of already
known definitions, an error will be returned:

```plaintext
>> def recurse () { recurse }
Unknown Command: operation `recurse` not defined
--> shell:17
 | def recurse () { recurse }
 |                  ^^^^^^^ `recurse` not found
--> help: view a list of definitions using `def --list`
```

Although ogma lacks first class support for recursion, problems can be solved using
conditionals and ranges. Below are some examples of where recursion would be used, and how
one can replicate it in ogma.

## Power
---
`n` raised to the power of `x` can be written in terms of itself:
```plaintext
n^x :=
    x = 0 => 1
        x => n * n^(x-1)
```

This can also be framed iteratively; multiply _n_ with itself _x_ times. The base case is
where `x=0`, which returns 1 (ie `n^0=1`).
Using a range with `n` as a seed can achieve the same result:
```plaintext
def pwr (n x) { if { \$x | = 0 } 1 { range 1 $x | fold $n * $n } }
```

The result can be checked:
```plaintext
.> pwr 2 3
8
.> pwr 2 2
4
.> pwr 2 1
2
.> pwr 2 0
1
```

![](./assets/no-recursion.pwr.gif?raw=true)

> A specialisation can be done for when the input is a number type. This means only a
> single parameter (`exp`) can be required:
> ```plaintext
> def pwr Num (exp) { if {\$exp | = 0} 1 {let $n | range 1 $exp | fold $n * $n} }
> ```

## Factorial
---
`n` factorial can be written in terms of itself:
```plaintext
n! :=
    n = 0 => 1
    n = 1 => 1
        n => n * (n-1)!
```

Similarly to `pwr`, one can define factorial using ranges:
```plaintext
def fact Num () { if {<= 1} 1 { + 1 | range 1 | fold 1 * $row.i } }
```

Since `fact` is now defined for a number input, one can build a table listing factorials:
```plaintext
.> range 1 11 | append --'i!' { get i | fact }
```

![](./assets/no-recursion.fact.gif?raw=true)

## Fibonacci
---
A fibonacci term follows the sequence: `0,1,1,2,3,5,8,13`
This can be represented recursively:
```plaintext
fib n :=
    n = 0 => 0
    n = 1 => 1
        n => fib(n-1) + fib(n-2)
```

To define _two_ variables that are tracked, a _type definition_ is used. Below are the
definitions and some comments about the structure.
```plaintext
# Define a structure to hold two numbers, the current 'x' and the previous number 'prev'
def-ty Fib { x:Num prev:Num }

# Define an impl which folds over the Fib structure, keeping track of previous and current number
# notice the accumulator: `Fib { + $acc.x $acc.prev } $acc.x`. This sums the old $acc Fib to
# get the new `x`, and stores the old `$acc.x` as the previous.
def fib-inner (n) { range 1 $n | fold { Fib 1 0 } { let $acc | Fib { + $acc.x $acc.prev } $acc.x } }

# Define the main fib impl which _extracts_ the actual fibonacci number.
# '{fib-inner #i}.x' does the calculation _and_ extraction.
def fib Num () { if {<= 1} #i {fib-inner #i}.x }
```

With these functions the first 10 fibonacci numbers can be printed out like so, we encourage you to
try it yourself!
```plaintext
range 1 11 | append --Fibonacci { get i | fib }
```

It is also possible to inspect the state by way of the `fib-inner`:
```plaintext
range 1 11 | append --'Fib working' fib-inner get i
```

**Alternative Method: constructing a growing table**

Since a fibonacci sequence is based on the numbers that come before it, there is an
alternate way to construct a table of the sequence which demonstrates how to use `fold`
and `append-row` to create a _growing_ table. The idea is to start with a table filled
with rows 0 and 1. Then given a `range 1 $n` one can `fold` appending the sum of the last 
and second last rows to the seed table. This will create a table `$n` rows long, with each
row containing describing the sequence.

In the code below `$acc` is the _growing_ `Table`, and for each fold iteration:
1. the last and 2nd last rows are extracted and set as variables `$last` and `$last2`
  (using `nth {len | - 1} get i` and `nth {len | - 2} get i` respectively),
4. the summed value is appended as a row to the input.
```plaintext
def fib-table Num () { range 1 #i | 
    fold {range 0 2}
    { let
        {nth {len | - 1} get i} $last
        {nth {len | - 2} get i} $last2
      | append-row { + $last $last2 }
    }
}
```

## GCD - Greatest Common Divisor
---
The greatest common divisor of two numbers, calculated 
[using Euclid's
algorithm](https://www.khanacademy.org/computing/computer-science/cryptography/modarithmetic/a/the-euclidean-algorithm)
can be written recursively:
```plaintext
gcd a b :=
  a = 0 => b
  b = 0 => a
  a > b => gcd(a mod b, b)
    a b => gcd(a, b mod a)
```

Similarly to the fibonacci sequence, a structure could be defined which holds the two
numbers `a` and `b`. For this example the `Tuple` structure will be demonstrated instead.
To seed the number of fold iterations that are required to reach the GCD, the minimum
between the absolutes of a and b is taken.

```plaintext
# Greatest Common Divisor
# Invariant that `b < a` is upheld to reduce number of branches.
def gcd (a b) { range 0 {\$a|abs|min {\$b|abs}} |
    fold-while { if {\$a|< $b} {Tuple $b $a} {Tuple $a $b} }
        { get t1 | != 0 }
        { let $acc | get t0 | mod $acc.t1 | Tuple $acc.t1 #i }
    | get t0
}
```

The code above does the following:
1. Defines a range from 0 to the minimum of the absolutes between _a_ and _b_. The minimum
   expression uses some condensed syntax, but can be read like `\ $a | abs | min { \ $b |
   abs }`,
2. `fold-while` is used to stop iterating early if the break condition is met,
3. The seed value places the _smaller_ number into the 2nd tuple element (`if {\$a|< $b}
   {Tuple $b $a} {Tuple $a $b}`),
4. Continue iterating whilst `get t1 | != 0`, that is, while the Tuple's 2nd element has
   not reached zero,
5. Do the reduction math; inputs `$acc`, calculates the mod between the 1st and 2nd
   element, build a new Tuple with `t1` going into `t0` and the mod being `t1`
   `let $acc | get t0 | mod $acc.t1 | Tuple $acc.t1 #i`,
6. Extract the 1st element out of the folded value.

![](./assets/no-recursion.gcd.gif?raw=true)

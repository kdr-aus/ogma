<iframe src="/.ibox.html?raw=true" style="border:none; position:fixed; width:40px; right:0; z-index=999;"></iframe>

# Common Commands
---
To view a list of available commands, use the command `def --list`. This will output a table of the
commands. To view say the _arithmetic_ commands, a filter can be applied to the table: `def --list
| filter 'category' --Str = 'arithmetic'`. Since the table will be elided, the table can be written
to disk using `def --list | save ogma-defs.csv`.
Most commands are defined by `ogma` as an intrinsic for various reasons such as performance, arity,
and specialisations.
To view the information about a single command, use `cmd --help` where `cmd` is the command name.
For example, to view information about the `filter` command, use `filter --help`. The help usually
comes with some examples.

## Input command
The input command is a single backslash (`\`). The purpose of the input command is simple, take the
resolve the argument and return that value as the block's output. Despite the simplicity of the
command, it sees use in many cases when the input needs to adjust for a chain of blocks. Because
the command uses a special character, there is no need to add a space after the command. Below are
some examples:
```plaintext
\ 3 --> Make input 3
\3  --> Same as \ 3
\$x --> Input variable $x
# Example where changing the input is necessary
\ 10 | if {= {\100 |- 90}} yes no
```

## Open command
Another common command is `open`. This takes an argument (usually a file) and 'fits' it into
usually a table (there are flags to read in as a string).
The main use case of `open` is to read in a table of data to be processed, which is why it sees
common use.

## Arithmetic
`ogma` supports arithmetic operations. Many basic operations, such as adding, subtracting,
multiplying, and dividing are _variadic_, meaning they can take more than one argument.
These operations have some interesting semantics. Take for example the block `+ 1 2 3`. This
would add its arguments together to produce six. If however the **_input_** into the block is a
number, this acts _as the left hand side_, such that `\ 4 | + 1 2 3` is 10. However, if the blocks
input is _not_ a number, then the input is ignored.
The input generally drives this behaviour. For instance `\ foo | + ' bar'` would return `foo bar`,
but `\ foo | + 1 2 3` would return a semantics error.
This semantic behaviour is important to understand when working with subtraction or division. Each
argument is applied _successively_. So `\ 10 | - 3 2 1` returns 4, and `\ 50 | / 2 5` returns 5.

## Comparisons
Comparisons and equality of types can be done through `eq` and `cmp`. `eq` does an equality check
between the input and the argument whilst `cmp` returns an ordering type. These two commands in
turn are used by the operators `=`, `!=`, `<`, `>`, `<=`, `>=` for ordering operators. The
comparison operators show case **_derived_** implementations. For example, the help of `=` outputs:
```plaintext
>> = --help
Help: `=`
--> shell:0
 | user defined implementation in <ogma>
 | `def = (rhs) { eq $rhs }`
 | test if input is not equal to rhs
 |
 | Usage:
 |  => = rhs
 |
 | Examples:
 |  test if 1 is equal to 0
 |  => in 1 | = 0
```

Notice how `=` is defined in terms of `eq`. The same goes for `!=`. This is done to facilitate
user-defined types being able to leverage `eq` and `cmp` with minimal implementations.
Below is a `Point` type defined, along with an implementation of `eq`. By implementing `eq`, the
commands `=` and `!=` extend to work with `Point`.
```plaintext
def-ty Point { x:Num y:Num }
def eq Point (rhs) { and {get x | = $rhs.x} {get y | = $rhs.y} }
```

> This pattern extends for other commands, a good example is the `sort-by` command.

> Boolean logic such as AND and OR is done with a prefix `and` and `or` comand. Both are variadic
> such that a logical expression can look like `\ 5 | or {= 3} {= 2} {= 5}`.

## Filter, skip, take, and pick
These next commands are centered around table operations (although some of the commands can work
with other data structures). `filter`, `skip`, `take`, and `pick` all work to return a _subset_ of
a table. `skip` and `take` work by `skip`ping and `take`ing the specified number of rows. `pick`
chooses the specified columns, in order. `filter` applies a predicate to a table to filter out
either rows or columns. `filter` demonstrates common table operation semantics, the help alludes to
the use:
```plaintext
>> filter --help
Help: `filter`
--> shell:0
 | filter incoming data using a predicate
 | filter can be used with a column header and a type flag
 | filtering columns is achievable with the --cols flag
 |
 | Usage:
 |  => filter [col-name] <predicate>
 |
 | Flags:
 |  --<type>: only filter entries of type. defaults to Num if not specified
 |  --cols: filter columns with predicate. predicate is String -> Bool
 |
 | Examples:
 |  filter ls items greater than 5kB
 |  => ls | filter size > 5e3
 |
 |  filter ls by extension
 |  => ls | filter ext --Str = md
 |
 |  filter a table by two columns
 |  => \ table.csv | filter { and { get col-a | > 100 } { get col-b | < 10 } }
 |
 |  filter table columns
 |  => \ table.csv | filter --cols or { = 'foo' } { = bar }
```

For example, the **iris** dataset is used to demonstrate the filtering.
Say the table is to be filtered to petal widths greater than 2 cm, the expression can be used
(ignore the table formatting).
```plaintext
>> open iris.csv | filter 'Petal Width' > 2
┌──────────────┬─────────────┬──────────────┬─────────────┬────────────────┐
│ Sepal Length ┆ Sepal Width ┆ Petal Length ┆ Petal Width ┆ Class          │
╞══════════════╪═════════════╪══════════════╪═════════════╪════════════════╡
│ 6.3          ┆ 3.3         ┆ 6.0          ┆ 2.5         ┆ Iris-virginica │
│ 7.1          ┆ 3.0         ┆ 5.9          ┆ 2.1         ┆ Iris-virginica │
│ 6.5          ┆ 3.0         ┆ 5.8          ┆ 2.2         ┆ Iris-virginica │
│ 7.6          ┆ 3.0         ┆ 6.6          ┆ 2.1         ┆ Iris-virginica │
│ 7.2          ┆ 3.6         ┆ 6.1          ┆ 2.5         ┆ Iris-virginica │
│ 6.8          ┆ 3.0         ┆ 5.5          ┆ 2.1         ┆ Iris-virginica │
│ 5.8          ┆ 2.8         ┆ 5.1          ┆ 2.4         ┆ Iris-virginica │
│ 6.4          ┆ 3.2         ┆ 5.3          ┆ 2.3         ┆ Iris-virginica │
│ 7.7          ┆ 3.8         ┆ 6.7          ┆ 2.2         ┆ Iris-virginica │
│ 7.7          ┆ 2.6         ┆ 6.9          ┆ 2.3         ┆ Iris-virginica │
│ 6.9          ┆ 3.2         ┆ 5.7          ┆ 2.3         ┆ Iris-virginica │
│ 6.7          ┆ 3.3         ┆ 5.7          ┆ 2.1         ┆ Iris-virginica │
│ 6.4          ┆ 2.8         ┆ 5.6          ┆ 2.1         ┆ Iris-virginica │
│ 6.4          ┆ 2.8         ┆ 5.6          ┆ 2.2         ┆ Iris-virginica │
│ 7.7          ┆ 3.0         ┆ 6.1          ┆ 2.3         ┆ Iris-virginica │
│ 6.3          ┆ 3.4         ┆ 5.6          ┆ 2.4         ┆ Iris-virginica │
│ 6.9          ┆ 3.1         ┆ 5.4          ┆ 2.1         ┆ Iris-virginica │
│ 6.7          ┆ 3.1         ┆ 5.6          ┆ 2.4         ┆ Iris-virginica │
│ 6.9          ┆ 3.1         ┆ 5.1          ┆ 2.3         ┆ Iris-virginica │
│ 6.8          ┆ 3.2         ┆ 5.9          ┆ 2.3         ┆ Iris-virginica │
│ 6.7          ┆ 3.3         ┆ 5.7          ┆ 2.5         ┆ Iris-virginica │
│ 6.7          ┆ 3.0         ┆ 5.2          ┆ 2.3         ┆ Iris-virginica │
│ 6.2          ┆ 3.4         ┆ 5.4          ┆ 2.3         ┆ Iris-virginica │
└──────────────┴─────────────┴──────────────┴─────────────┴────────────────┘
```

If the filter is to be applied to more than one column, the column name is omitted and an
expression is used to filter. **The input into the expression is a TableRow**. A table row can use
the `get` command to retrieve the value of a column on the given row. In the expression below,
`filter` takes an expression (predicate) which returns true if petal width is greater than 2 AND
petal length is greater than 6.
```plaintext
>> open iris.csv | filter {and {get 'Petal Width' | > 2} {get 'Petal Length' | > 6} }
┌──────────────┬─────────────┬──────────────┬─────────────┬────────────────┐
│ Sepal Length ┆ Sepal Width ┆ Petal Length ┆ Petal Width ┆ Class          │
╞══════════════╪═════════════╪══════════════╪═════════════╪════════════════╡
│ 7.6          ┆ 3.0         ┆ 6.6          ┆ 2.1         ┆ Iris-virginica │
│ 7.2          ┆ 3.6         ┆ 6.1          ┆ 2.5         ┆ Iris-virginica │
│ 7.7          ┆ 3.8         ┆ 6.7          ┆ 2.2         ┆ Iris-virginica │
│ 7.7          ┆ 2.6         ┆ 6.9          ┆ 2.3         ┆ Iris-virginica │
│ 7.7          ┆ 3.0         ┆ 6.1          ┆ 2.3         ┆ Iris-virginica │
└──────────────┴─────────────┴──────────────┴─────────────┴────────────────┘
```

Filtering can also apply to column headers. In the expression below, the `--cols` flag makes the
predicate supply the column header (as a string) as input. The predicate `{ take 5 | = Petal }`
does the following:
1. The input is the column header (a string),
2. `take 5` takes the first 5 characters (of the input),
3. Test that it equals the string `Petal`.

```plaintext
>> open iris.csv | filter --cols { take 5 | = Petal }
┌─────────────────┬─────────────┐
│ Petal Length    ┆ Petal Width │
╞═════════════════╪═════════════╡
│ 1.4             ┆ 0.2         │
│ 1.4             ┆ 0.2         │
│ 1.3             ┆ 0.2         │
│ 1.5             ┆ 0.2         │
│ 1.4             ┆ 0.2         │
│ 140 rows elided ┆ ...         │
│ 5.2             ┆ 2.3         │
│ 5.0             ┆ 1.9         │
│ 5.2             ┆ 2.0         │
│ 5.4             ┆ 2.3         │
│ 5.1             ┆ 1.8         │
└─────────────────┴─────────────┘
```

Finally, the `--<type>` flag is common when working with TableRows. The flag specifies the expected
type of value that will be returned when fetching the entry from a table row. The typical behaviour
if the flag is not specified is to return a number value. As the type of a value within a TableRow
entry might _not_ be a number, an evaluation error will be returned. For example, trying to filter
on the column 'Class' when a number is expected will return an evaluation error finding that a
number was not found:
```plaintext
>> open iris.csv | filter {get Class | > 100}
Evaluation Error: table entry for [row:108,col:'Class'] did not have expected type
expected `Number`, found `String`
--> shell:28
 | open iris.csv | filter {get Class | > 100}
 |                             ^^^^^
--> help: column entries must have a matching type
```

To make this filter work, a type flag is used to define the _expected_ type:

```plaintext
>> open iris.csv | filter {get Class --Str | = Iris-virginica}
┌────────────────┬─────────────┬──────────────┬─────────────┬────────────────┐
│ Sepal Length   ┆ Sepal Width ┆ Petal Length ┆ Petal Width ┆ Class          │
╞════════════════╪═════════════╪══════════════╪═════════════╪════════════════╡
│ 6.3            ┆ 3.3         ┆ 6.0          ┆ 2.5         ┆ Iris-virginica │
│ 5.8            ┆ 2.7         ┆ 5.1          ┆ 1.9         ┆ Iris-virginica │
│ 7.1            ┆ 3.0         ┆ 5.9          ┆ 2.1         ┆ Iris-virginica │
│ 6.3            ┆ 2.9         ┆ 5.6          ┆ 1.8         ┆ Iris-virginica │
│ 6.5            ┆ 3.0         ┆ 5.8          ┆ 2.2         ┆ Iris-virginica │
│ 40 rows elided ┆ ...         ┆ ...          ┆ ...         ┆ ...            │
│ 6.7            ┆ 3.0         ┆ 5.2          ┆ 2.3         ┆ Iris-virginica │
│ 6.3            ┆ 2.5         ┆ 5.0          ┆ 1.9         ┆ Iris-virginica │
│ 6.5            ┆ 3.0         ┆ 5.2          ┆ 2.0         ┆ Iris-virginica │
│ 6.2            ┆ 3.4         ┆ 5.4          ┆ 2.3         ┆ Iris-virginica │
│ 5.9            ┆ 3.0         ┆ 5.1          ┆ 1.8         ┆ Iris-virginica │
└────────────────┴─────────────┴──────────────┴─────────────┴────────────────┘ 
```

## Mapping, appending, and concatenation
`map`pping, `append`ing, and concatenation all work to _alter the contents_ of a table. `map` and
`append` work on _one_ table, whilst concatenation is for multiple tables. `map` **changes** the
entries within a column in a table. For instance, to alter the 'Class' column to remove the prefix
`Iris-`, `map` can be used. Map uses an expression which the output value will become the value of
the entry. The input to the expression the entry value map defines a variable `$row` which is
the **value of the TableRow** (this has the same restriction of requiring a type flag).
```plaintext
>> open iris.csv | map Class --Str { skip 5 }
┌─────────────────┬─────────────┬──────────────┬─────────────┬───────────┐
│ Sepal Length    ┆ Sepal Width ┆ Petal Length ┆ Petal Width ┆ Class     │
╞═════════════════╪═════════════╪══════════════╪═════════════╪═══════════╡
│ 5.1             ┆ 3.5         ┆ 1.4          ┆ 0.2         ┆ setosa    │
│ 4.9             ┆ 3.0         ┆ 1.4          ┆ 0.2         ┆ setosa    │
│ 4.7             ┆ 3.2         ┆ 1.3          ┆ 0.2         ┆ setosa    │
│ 4.6             ┆ 3.1         ┆ 1.5          ┆ 0.2         ┆ setosa    │
│ 5.0             ┆ 3.6         ┆ 1.4          ┆ 0.2         ┆ setosa    │
│ 140 rows elided ┆ ...         ┆ ...          ┆ ...         ┆ ...       │
│ 6.7             ┆ 3.0         ┆ 5.2          ┆ 2.3         ┆ virginica │
│ 6.3             ┆ 2.5         ┆ 5.0          ┆ 1.9         ┆ virginica │
│ 6.5             ┆ 3.0         ┆ 5.2          ┆ 2.0         ┆ virginica │
│ 6.2             ┆ 3.4         ┆ 5.4          ┆ 2.3         ┆ virginica │
│ 5.9             ┆ 3.0         ┆ 5.1          ┆ 1.8         ┆ virginica │
└─────────────────┴─────────────┴──────────────┴─────────────┴───────────┘
```

`append`ing is similar to `map` but _appends_ columns with the output of each supplied expression.
Each expression's input is TableRow.
Each new column has a default name, but the columns can be named by using flags. The
example below appends a new column using the previous example's expression, and also adds a column
that is the difference between Sepal Width and Petal Width.
```plaintext
>> open iris.csv | append --'Short Class' {get Class --Str | skip 5}
{let {get 'Sepal Width'} $a {get 'Petal Width'} $b | - $a $b}   
┌─────────────────┬─────────────┬──────────────┬─────────────┬────────────────┬─────────────┬──────────┐
│ Sepal Length    ┆ Sepal Width ┆ Petal Length ┆ Petal Width ┆ Class          ┆ Short Class ┆ _append1 │
╞═════════════════╪═════════════╪══════════════╪═════════════╪════════════════╪═════════════╪══════════╡
│ 5.1             ┆ 3.5         ┆ 1.4          ┆ 0.2         ┆ Iris-setosa    ┆ setosa      ┆ 3.3      │
│ 4.9             ┆ 3.0         ┆ 1.4          ┆ 0.2         ┆ Iris-setosa    ┆ setosa      ┆ 2.8      │
│ 4.7             ┆ 3.2         ┆ 1.3          ┆ 0.2         ┆ Iris-setosa    ┆ setosa      ┆ 3.0      │
│ 4.6             ┆ 3.1         ┆ 1.5          ┆ 0.2         ┆ Iris-setosa    ┆ setosa      ┆ 2.9      │
│ 5.0             ┆ 3.6         ┆ 1.4          ┆ 0.2         ┆ Iris-setosa    ┆ setosa      ┆ 3.4      │
│ 140 rows elided ┆ ...         ┆ ...          ┆ ...         ┆ ...            ┆ ...         ┆ ...      │
│ 6.7             ┆ 3.0         ┆ 5.2          ┆ 2.3         ┆ Iris-virginica ┆ virginica   ┆ 0.700    │
│ 6.3             ┆ 2.5         ┆ 5.0          ┆ 1.9         ┆ Iris-virginica ┆ virginica   ┆ 0.600    │
│ 6.5             ┆ 3.0         ┆ 5.2          ┆ 2.0         ┆ Iris-virginica ┆ virginica   ┆ 1.0      │
│ 6.2             ┆ 3.4         ┆ 5.4          ┆ 2.3         ┆ Iris-virginica ┆ virginica   ┆ 1.1      │
│ 5.9             ┆ 3.0         ┆ 5.1          ┆ 1.8         ┆ Iris-virginica ┆ virginica   ┆ 1.2      │
└─────────────────┴─────────────┴──────────────┴─────────────┴────────────────┴─────────────┴──────────┘
```

Table concatenation uses the `+` command. Concatenation can be done by rows or cols, the default
being rows. So to _extend_ a table, the syntax is `table1 | + table2 table 3`. To _join_ a table
(add cols together), the syntax is `table1 | + --cols table2 table3`. There are also flags to
control the _behaviour_ of concatenation, allowing for table intersections and unions based on
sizes.

## Sorting and grouping
Sorting can be done using two commands. `sort` takes column headers and sorts the entries **_in a
canoncial fashion_** (this means entry _types_ have _order_ enforced on them). In general, `sort`
is the 'go to' sorting command. The sort help shows how specifying more than one header can be
used to do 'then by' sorting.
```plaintext
>> range 0 6 | rev | fold {range 0 0} {+ { range 0 $row.i }} | sort i
┌─────┐
│ i   │
╞═════╡
│ 0   │
│ 0   │
│ 0   │
│ 0   │
│ 0   │
│ 1.0 │
│ 1.0 │
│ 1.0 │
│ 1.0 │
│ 2.0 │
│ 2.0 │
│ 2.0 │
│ 3.0 │
│ 3.0 │
│ 4.0 │
└─────┘ 
```

`sort-by` differs to `sort`. It sorts based on the output of an expression. This can be used to
sort on the output from the _combination_ of columns. It is also used to sort based on
_user-defined_ types which **define a `cmp` implementation**.

Grouping is similarly done using `grp` and `grp-by`. `grp` takes column headers and **_concatenates
the stringified row values together_**, separated by a hyphen. This string is used as the key. The
**value** component of a grouping is the table subset of each row which with the shared key.
`grp-by` uses an _expression_ for the key rather than a string. As `grp` and `grp-by` have _tables_
in the value column for each row, another transformation is usually applied to the value rows.
```plaintext
# Count the number of occurrences of a grouping.
>> open diamonds.csv | grp cut | map value --Table len
┌───────────┬──────────┐
│ key       ┆ value    │
╞═══════════╪══════════╡
│ Fair      ┆ 1.61 K   │
│ Good      ┆ 4.906 K  │
│ Ideal     ┆ 21.551 K │
│ Premium   ┆ 13.791 K │
│ Very Good ┆ 12.082 K │
└───────────┴──────────┘  

# Grouping can be used to create summaries
>> open diamonds.csv | grp cut | append
--'Max Price' {get value --Table | fold 0 max $row.price}
--'Total Carats' {get value --Table | fold 0 + $row.carat} |
filter --cols != value
┌───────────┬───────────┬──────────────┐
│ key       ┆ Max Price ┆ Total Carats │
╞═══════════╪═══════════╪══════════════╡
│ Fair      ┆ 18.574 K  ┆ 1.684 K      │
│ Good      ┆ 18.788 K  ┆ 4.166 K      │
│ Ideal     ┆ 18.806 K  ┆ 15.146 K     │
│ Premium   ┆ 18.823 K  ┆ 12.300 K     │
│ Very Good ┆ 18.818 K  ┆ 9.742 K      │
└───────────┴───────────┴──────────────┘
```

## Fold
Folding is used to _reduce_ a table to a single value. This relatively simple concept is extremely
powerful, and many common concepts can be defined in terms of a fold.
`fold` takes an initial value and an expression. The expression has an input value of the
_previous_ output (the seed value for the first row. `fold` also supplies the variable `$row` which 
is the `TableRow` that is being evaluated.

Many concepts can be expressed as a `fold`. The sum of values in a column? `fold 0 + $row.col`
The maximum value? `fold -inf max $row.col`. More complicated folds can use
user-defined types or tuples as a way aggregating a data structure. Even tables can be constructed
through folds (by way of the `append-row` command). There is also a variant `fold-while` which
breaks early if a predicate returns false.


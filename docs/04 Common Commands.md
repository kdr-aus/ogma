<iframe src="./.ibox.html?raw=true" style="border:none; position:fixed; width:40px; right:0; z-index=999;"></iframe>

# Common Commands

To view a list of available commands, use the command `def --list`. This will output a table of commands,
including user defined implementations.
To view, say, the _arithmetic_ commands, a filter can be applied to the table: `def --list
| filter 'category' --Str = 'arithmetic'`. Since the table will be elided, the table can be written
to disk using `def --list | save ogma-defs.csv`.
Most commands are defined by `ogma` intrinsically for various reasons such as performance, arity,
and specialisations.
To view the information about a single command, use `<cmd> --help` where `<cmd>` is the command name.
For example, to view information about the `filter` command, use `filter --help`. The help usually
comes with some examples and is a good place to start.

> ❗When starting out it is recommended to save the list of commands for easy reference:
> ```plaintext
> def --list | save ogma-defs.csv
> ```

## Input command
---
The input command is a single backslash (`\`). The purpose of the input command is simple, take the
argument and return that value as the block's output. Despite the simplicity of the
command, it sees use in many cases when the input needs to be adjusted for a chain of blocks. Because
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
---
Another common command is `open`. This takes a file path as an argument and reads the contents into
an ogma value type. The vanilla command reads the file into a Table, but flags can be specified to
read the file is specific ways.

> 🔬 This is an area of improvement to read more data types and improve file heuristics.
> Please consider contributing or sponsoring to help development!

## Arithmetic
---
`ogma` supports arithmetic operations. Many basic operations, such as adding, subtracting,
multiplying, and dividing are _variadic_, meaning they can take more than one argument.
These operations have some interesting semantics. Take for example the block `+ 1 2 3`. This
would add its arguments together to produce six. If however the **_input_** into the block is a
number, this acts _as the left hand side_, such that `\ 4 | + 1 2 3` is 10. However, if the blocks
input is _not_ a number, then the input is ignored.
The input generally drives this behaviour. For instance `\ foo | + ' bar'` would return `foo bar`,
but `\ foo | + 1 2 3` would return a semantics error, since adding a number to string does not make
sense.
This semantic behaviour is important to understand when working with subtraction or division. Each
argument is applied _successively_. So `\ 10 | - 3 2 1` returns 4, and `\ 50 | / 2 5` returns 5.

> ogma uses _prefix_ notation which can feel unfamiliar!

## Comparisons
---
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
User defined types are documented later on.
```plaintext
def-ty Point { x:Num y:Num }
def eq Point (rhs) { and {get x | = $rhs.x} {get y | = $rhs.y} }
```

> This pattern extends for other commands, a good example is the `sort-by` command.

> Boolean logic such as AND and OR is done with a prefix `and` and `or` comand. Both are variadic
> such that a logical expression can look like `\ 5 | or {= 3} {= 2} {= 5}`.

## Get
---
`get` is used when working with data structures where inner values can be extracted.
This is commonly on inputs of `TableRow`, `Tuple`, or a user defined type.
**`get` must know the return _type_.** For tuples and user defined types this is well specified,
but for table rows the type of a value in a given row/column is unknown until the value is fetched.
This means that the `get` command must _specify_ the **expected** type when working on `TableRow`
input.
Use type annotations to specify the output type of the command: `get:<Type>` for example,
`get:Str foo` would expect to return a string.

```plaintext
Tuple 1 2 | get t0 --> returns 1
Tuple 1 2 | get t1 --> returns 2
open diamonds.csv | last get color --> ERROR: tried to get a number but found a string
open diamonds.csv | last get --Str color --> returns 'D'
```

## Filter, skip, take, and pick
---
These next commands are centered around table operations (although some of the commands can work
with other data structures). `filter`, `skip`, `take`, and `pick` all work to return a _subset_ of
a table:
- `skip` will _skip_ over a specified number of rows,
- `take` returns the initial specified number of rows,
- `pick` chooses the specified columns, in order, and
- `filter` applies a predicate to a table to filter out either rows or columns.

`filter` demonstrates common table operation semantics, the `--help` alludes to
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

![](./assets/common-cmds.filter.gif?raw=true)

If the filter is to be applied to more than one column, the column name is omitted and an
expression is used to filter. **The input into the expression is a TableRow**. A table row can use
the `get` command to retrieve the value of a column on the given row. 

![](./assets/common-cmds.filter2.gif?raw=true)

Filtering can also apply to column headers by passing it the `--cols` flag. In the animation below,
only the columns starting with the character 'c' are included in the table.

![](./assets/common-cmds.filter3.gif?raw=true)

Finally, the `--<type>` flag is common when working with TableRows. The flag specifies the expected
type of value that will be returned when fetching the entry from a table row. The typical behaviour
if the flag is not specified is to return a number value. As the type of a value within a TableRow
entry might _not_ be a number, an evaluation error will be returned. For example, trying to filter
on the column 'color' when a number is expected will return an evaluation error finding that a
number was not found. To make this work, the `--Str` type flag is used to define the _expected_
type:

![](./assets/common-cmds.filter4.gif?raw=true)

## Mapping, appending, and concatenation
---
`map`pping, `append`ing, and concatenation all work to _alter the contents_ of a table. `map` and
`append` work on _one_ table, whilst concatenation is for multiple tables. `map` **changes** the
entries _within_ a column in a table. 
For instance, to alter the 'Class' column to remove the prefix
`Iris-`, `map` can be used. Map uses an expression which the output value will become the value of
the entry. The input to the expression the entry value map defines a variable `$row` which is
the **value of the TableRow** (this has the same restriction of requiring a type flag).

![](./assets/common-cmds.map.png?raw=true)

`append`ing is similar to `map` but _appends_ columns with the output of each supplied expression.
Each expression's input is `TableRow`.
Each new column has a default name, but the columns can be named by using flags. The
example below appends a new column using the previous example's expression, and also adds a column
that is the difference between Sepal Width and Petal Width.

![](./assets/common-cmds.append.png?raw=true)

Table concatenation uses the `+` command. Concatenation can be done by rows or cols, the default
being rows. So to _extend_ a table, the syntax is `table1 | + table2 table 3`. To _join_ a table
(add cols together), the syntax is `table1 | + --cols table2 table3`. There are also flags to
control the _behaviour_ of concatenation, allowing for table intersections and unions based on
sizes. Use `+ --help` to view these details.

## Sorting and grouping
---
Sorting can be done using two commands. `sort` takes column headers and sorts the entries **_in a
canoncial fashion_** (this means entry _types_ have _order_ enforced on them). In general, `sort`
is the 'go to' sorting command. The sort help shows how specifying more than one header can be
used to do 'then by' sorting.

![](./assets/common-cmds.sort.gif?raw=true)

`sort-by` differs to `sort`. It sorts based on the _output_ of an expression. This can be used to
sort on the output from the _combination_ of columns. It is also used to sort based on
_user-defined_ types which **define a `cmp` implementation**.

> The [3D Vector](./15%20Examples/15.2%203D%20Vector.md?book=true)
> is an example of how defining `cmp` on a user-defined type can be achieved.

Grouping is similarly done using `grp` and `grp-by`. `grp` takes column headers and **_concatenates
the stringified row values together_**, separated by a hyphen. This string is used as the key. The
**value** component of a grouping is the table subset of each row which with that shared key.
`grp-by` uses an _expression_ for the key rather than a string. As `grp` and `grp-by` have _tables_
in the value column for each row, another transformation is usually applied to the value rows.

For example, to output the _count_ of each cut type entry in `diamonds.csv`, first group by the
'cut' column, then map the 'value' column from a table to the table's length:

![](./assets/common-cmds.grp.gif?raw=true)

Grouping is also very useful for creating summaries, the expression below summarizes the
`diamonds.csv` dataset by outputting the maximum price and sum of the carats, grouped by 'cut':
```plaintext
open diamonds.csv | grp cut | append
--'Max Price' {get value --Table | fold 0 max $row.price}
--'Total Carats' {get value --Table | fold 0 + $row.carat}
| filter --cols != value
```

![](./assets/common-cmds.grp2.png?raw=true)

## Fold
---
Examples of `fold` have already been used, and this speaks to `fold`'s extreme powerfulness.
Between `fold`, `map`, `filter`, and `grp`, a huge set of solutions can be found for manipulating
tables. It is worth deeply understanding `fold`, since most higher level expression can be built
from it.

Folding is used to _reduce_ a table to a single value. This relatively simple concept is extremely
powerful, and many common concepts can be defined in terms of a fold.
`fold` takes an initial value and an expression. There are three components of a `fold` expression:

1. The expression has an input value of the _previous_ output. This is known as the _accumulator_.
2. The `$row` variable is the current `TableRow` and is used to fetch data from the table.
3. The _output_ of the expression must match the accumulator's type, since the output will become
   the input on the next iteration.

> The notion of a _single_ value means that the _many_ rows collapse into one.
> The _value_ can still be something such as a `Table` with rows.
> This is how one can achieve cumulative sums, by setting the accumulator type as a `Table`.

Many concepts can be expressed as a `fold`. The sum of values in a column? `fold 0 + $row.col`
The maximum value? `fold -inf max $row.col`. More complicated folds can use
user-defined types or tuples as a way aggregating a data structure. Even tables can be constructed
through folds (by way of the `append-row` command). There is also a variant `fold-while` which
breaks early if a predicate returns false.

The picture below shows fold being used to:
1. Sum the 'price' values,
2. Get the max of the 'carat' values,
3. Create a table of the cumulative sum of prices.

![](./assets/common-cmds.fold.png?raw=true)

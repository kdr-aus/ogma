<iframe src="./.ibox.html?raw=true" style="border:none; position:fixed; width:40px; right:0; z-index=999;"></iframe>

# Variables

Variables are used in many contexts. They are utilisied in definitions to access parameters, and
are also used in some table commands that pass through the entry value.
Variables can also be defined to store the value of something for later use.
Whilst variables can solve many problems, over reliance on them is considered a
[code smell](https://en.wikipedia.org/wiki/Code_smell).
The use of variables can be minimised due to ogma's focus on data pipelines and functional
programming, and are most efficient when used _outside_ of hot code.

To set a variable the `let` command is used. Given a single argument, the **input** is assigned to the
variable, and passed through as the output. `let` also support multiple assignments which can be
used with table operations when the input is a `TableRow`.

For example, to create a column of 'Price per Carat', the price is fetched and set to `$price`, the
carats are fetched and set to `$carat`, then the divide command is called with the two variables.

```plaintext
open diamonds.csv | append --'Price per Carat' {
let {get price} $price {get carat} $ct | / $price $ct }
```

![](./assets/variables-1.png?raw=true)

A more idiomatic way of achieving the same result without the use of variables is to use the dot
(`.`) operator:

```plaintext
open diamonds.csv | append --'Price per Carat' / #i.price #i.carat
```

![](./assets/variables-2.gif?raw=true)

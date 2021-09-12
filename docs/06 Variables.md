<iframe src="/.ibox.html?raw=true" style="border:none; position:fixed; width:40px; right:0; z-index=999;"></iframe>

# Variables
---
Variables are used in many contexts. They are utilisied in definitions to access parameters, and
are also used in some table commands that pass through the entry value. Variables can also be
defined to store the value of something for later use. Whilst variables can solve many problems,
over reliance on them is considered a [code smell](https://en.wikipedia.org/wiki/Code_smell) and
generally variables can be minimised due to `ogma`'s focus on data pipelines and functional
programming.

To set a variable the `let` command is used. Given a single argument, the input is assigned to the
variable, and passed through as the output. `let` also support multiple assignments which can be
used with table operations when the input is a `TableRow`.
```plaintext
>> open diamonds.csv | append --'Price per Carat' {
let {get price} $price {get carat} $ct | / $price $ct}
┌───────────────────┬───────────┬───────┬───────────────┬──────┬──────┬─────────────────┐
│ carat             ┆ cut       ┆ color ┆ 5 cols elided ┆ y    ┆ z    ┆ Price per Carat │
╞═══════════════════╪═══════════╪═══════╪═══════════════╪══════╪══════╪═════════════════╡
│ 0.23              ┆ Ideal     ┆ E     ┆ ...           ┆ 3.98 ┆ 2.43 ┆ 1.417 K         │
│ 0.21              ┆ Premium   ┆ E     ┆ ...           ┆ 3.84 ┆ 2.31 ┆ 1.552 K         │
│ 0.23              ┆ Good      ┆ E     ┆ ...           ┆ 4.07 ┆ 2.31 ┆ 1.421 K         │
│ 0.29              ┆ Premium   ┆ I     ┆ ...           ┆ 4.23 ┆ 2.63 ┆ 1.151 K         │
│ 0.31              ┆ Good      ┆ J     ┆ ...           ┆ 4.35 ┆ 2.75 ┆ 1.080 K         │
│ 53930 rows elided ┆ ...       ┆ ...   ┆ ...           ┆ ...  ┆ ...  ┆ ...             │
│ 0.72              ┆ Ideal     ┆ D     ┆ ...           ┆ 5.76 ┆ 3.5  ┆ 3.829 K         │
│ 0.72              ┆ Good      ┆ D     ┆ ...           ┆ 5.75 ┆ 3.61 ┆ 3.829 K         │
│ 0.7               ┆ Very Good ┆ D     ┆ ...           ┆ 5.68 ┆ 3.56 ┆ 3.938 K         │
│ 0.86              ┆ Premium   ┆ H     ┆ ...           ┆ 6.12 ┆ 3.74 ┆ 3.205 K         │
│ 0.75              ┆ Ideal     ┆ D     ┆ ...           ┆ 5.87 ┆ 3.64 ┆ 3.676 K         │
└───────────────────┴───────────┴───────┴───────────────┴──────┴──────┴─────────────────┘
```


<iframe src="./.ibox.html?raw=true" style="border:none; position:fixed; width:40px; right:0; z-index=999;"></iframe>

# Performance

Performance is a main design goal in ogma. Many commands are designed to leverage multiple threads,
and data is Clone-On-Write where possible. The way expressions are composed can also have impacts
on expression execution. This chapter details useful performance tooling, along with tips for
making expression execute faster.

## Profiling

---

### `benchmark`

The `benchmark` command can be used to _time_ the execution of an expression. This is useful when
AB testing different implementations.

> 🔬 Additions to profiling tools are required! Get involved
> through Github to help shape ogma's development.

## Performance Tips

---

### Reduce dataset sizes

The best way to improve performance is to reduce dataset sizes. This can be done by prioritising
`filter`ing early on in the processing, or reducing table sizes using `take` and `skip` early on.
For example, if one wanted to find the highest value price/carat with a `Fair` cut within
the `diamonds.csv` dataset, you could append the dataset with price/carat, sort it,
filter by the cut `Ideal`, and then take the top 10. Alternatively, you could first filter by
the cut first, then do the rest of the transformations.

- Method #1 -- Sort first:
  `open diamonds.csv | append --ppc / #i.price #i.carat | sort ppc |
  rev | filter cut --Str = Fair | take 10`
- Method #2 -- Filter first:
  `open diamonds.csv | filter cut --Str = Fair | append --ppc / #i.price #i.carat
  | sort ppc | rev | take 10`

We can time both these expressions using the `benchmark` command. The 2nd method ends up being
about twice as fast.

![](./assets/perf.reduce.gif?raw=true)

### Avoid repetitive large clones

Although ogma uses Clone-On-Write data structures, it is still possible to incur large cloning
penalties if clones occur in hot code.
This usually occurs in `fold`s which are constructing a data structure, such as a table, and is
having to clone the table each time.
As a contrived example, the expression `range 0 1e4 | fold {Table} { let $t | append-row 'a' }`
is _similar_ to `range 0 1e4 | fold {Table} { append-row 'a' }`.
They both create a table column full of 'a' characters. **However**, the first expression
assigns the `fold` input to the variable `$t`. Since `append-row` now has to clone the table to be
able to mutate it, the first expression now takes **much** longer. The animation below highlights
this point, the speed improvement if ~150x.

![](./assets/perf.cloning.gif?raw=true)

### Use parallelised commands

Certain commands that work on table structures are parallelised across row operations. This can
make them much faster when working with large tables.
When building expressions, try to leverage this parallelisation.

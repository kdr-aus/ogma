<iframe src="./.ibox.html?raw=true" style="border:none; position:fixed; width:40px; right:0; z-index=999;"></iframe>

# Daedalus Integration

[daedalus](https://daedalus.report) uses ogma as its scripting language,
since daedalus focuses on visual representations of tabular data, it makes sense to use ogma for
the tabular _transformations_.
When a local daedalus server is started, an integrated ogma REPL is started. There is also
specialised processing widgets for batch files.

## Batch Files
---
Viewing the example file shows how a batch renders an evaluation widget:
[Example Batch File.ogma](./Example%20Batch%20File.ogma).
The evaluation widget is not limited to just a file type. When defining a codeblock, if
`ogma` is used as the language the content is used as the source of the batch file.

For example the codeblock:
````
```ogma,no-parallelise,fail-fast
# First expression
\ 'foo' | + ' bar'

# Open a table
\ open '../data/diamonds.csv'
```
````

Would render as:
```ogma,no-parallelise,fail-fast
# First expression
\ 'foo' | + ' bar'

# Open a table
\ open '../data/diamonds.csv'
```

Files can also be linked in:
````
```ogma
Example Batch File.ogma
```
````

Would render as:
```ogma
Example Batch File.ogma
```

## Shared Definitions
---
Common definitions and user types can be shared between batch files by populating a definitions
file at `/.daedalus/defs.ogma`. Any definitions will be available for batch files.

> If using the REPL, use `def --load` to load definitions in `/.daedalus/defs.ogma`.

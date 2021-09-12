<iframe src="/.ibox.html?raw=true" style="border:none; position:fixed; width:40px; right:0; z-index=999;"></iframe>

# Batch Files
---

A batch file is one with the `ogma` extension. Viewing the example file shows how a batch
renders an evaluation widget.
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
Example Ogma Batch File.ogma
```
````

Would render as:
```ogma
Example Ogma Batch File.ogma
```

## Directives

Batch files support directives to alter the processing methodology.
Use the syntax as `#[directive-1,directive-2]` as the **first line** of the batch file.
For example, to _disable_ parallel processing and to _enable_ fast fail the first line of a batch
file would contain: `#[no-parallelise,fail-fast]`

## Shared Definitions

Common definitions and user types can be shared between batch files by populating a definitions
file at `/.daedalus/defs.ogma`. Any definitions will be available for batch files.

> If using the REPL, use `def --load` to load definitions in `/.daedalus/defs.ogma`.

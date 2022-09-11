<iframe src="./.ibox.html?raw=true" style="border:none; position:fixed; width:40px; right:0; z-index=999;"></iframe>

# Batch Files

A batch file is one with the `ogma` extension. It defines implementations, types, and expressions.
Below is an example of a batch file:
```plaintext
# First expression
\ 5 | + 5

# Opening a file
ls | filter size > 50 | fold 0 + $row.size

# A implementation definition
def add-2 () { + 2 }
```

## Syntax
---
Each item is demarcated by **a blank line**. This chunks the file into separate items, and
classifies each item. Multiline comments are supported _before_ an item, prefixed with the pound
(`#`) character.

## Directives
---
Batch files support directives to alter the processing methodology.
Use the syntax `[directive-1 directive-2]` _after any file comments, but **before any items.**_
For example, to _disable_ parallel processing and to _enable_ fast fail the batch
file would contain: `[no-parallelise fail-fast]`

## Processing
---
A batch file is run in its own context. This means definitions made in one batch file will not leak
into another batch file. The working directory that feeds into IO commands is the current working
directory of where the batch file is invoked.
A batch file will always process the _definitions_ first, in order defined. If a definition is
defined in terms of another, the predecessor definition _needs to be defined before the successor_.

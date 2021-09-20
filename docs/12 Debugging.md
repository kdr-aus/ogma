<iframe src="/.ibox.html?raw=true" style="border:none; position:fixed; width:40px; right:0; z-index=999;"></iframe>

# Debugging

To go about debugging an ogma expression, it is helpful to break it apart into the smallest
_blocks_ possible.
The types that are going into and out of a block are generally inferred, but an _impl_ definition
can help force the types, shedding light on where a type assumption may have been incorrect.
A useful tool for debugging operations across tables is to save a temporary table to disk and
inspect its contents. This can be done by inserting `save tmp.csv` as a trailing block.
Another handy debugging tool is the REPL. Any implementations can be tested when loaded into the
REPL. If working with a batch file, link the batch file into the REPL and use `def --load` to load
the definitions. This way the definitions can be tested using the REPL.

> 🔬 Improvements to debugging capabilities and tooling are required! Get involved
> through Github to help shape ogma's development.

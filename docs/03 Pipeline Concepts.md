<iframe src="/.ibox.html?raw=true" style="border:none; position:fixed; width:40px; right:0; z-index=999;"></iframe>

# Pipeline Concepts

A fundamental design choice of ogma is to chunk expressions into a 'block'. Each block has a
definitive _input_ and _output_ type. This style of data flow is commonly referred to as
_pipelining_. It is more common to see pipelining in functional languages and terminal shells.
In terminal shells, the data transferred through a pipe is a stream of bytes, in ogma the data is
more structured and has a definitive _type_ when passing through a pipe.

```plaintext
\'Hello' | + ', world! | len | = 13
```

TODO: Mermaid chart of above

all

rule "line-length", :line_length => 100
rule "header-style", :style => :atx
rule "ul-style", :style => :dash
rule "ol-prefix", :style => :ordered
rule "hr-style", :style => "---"
rule "code-block-style", :style => :fenced

# TODO
exclude_rule "no-inline-html"
exclude_rule "first-line-h1"
exclude_rule "no-blanks-blockquote"

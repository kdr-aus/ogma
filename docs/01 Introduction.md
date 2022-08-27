<iframe src="./.ibox.html?raw=true" style="border:none; position:fixed; width:40px; right:0; z-index=999;"></iframe>

<img 
src="./assets/logo.png?raw=true"
style="height: 200px; display:block; margin: auto; padding-top: 30px"/>

# Introduction

Welcome to the _ogma book_, a source of documentation for the ogma scripting language.
The ogma language is focused on _ergonomic_ and _efficient_ tabular data processing.
Mixing aspects of terminal shells and functional programming, the ogma project lets one interact
with data in a refreshing way.
The language is syntactically lightweight yet boasts powerful constructs designed to
work efficiently with tabular data.

## Characteristics
---
ogma takes inspiration from multiple sources. 
For the _semantics_, programming languages Rust, Haskell, ML, and Elm have
all been an influence, while the _syntax_ is derived primarily from terminal shells (with
smatterings from other languages). Some major characteristics of ogma are:
- small language with few keywords and opting for a **prefix** notation,
- uses **pipelines** to _chain_ together commands, composing their effects,
- it is **strongly typed**,
- can be extended with **user-defined** implementations _and_ types.

## Project Philosophy
---

The ogma project is continuously developed. To keep the project focused, there are three design
philosophies which are intended to be evident when using ogma:

- **_Ergonomic_**
  - Pipelines make data transformations feel like natural consecutive steps.
  - The language is syntactically _light_, making it easier to learn. Despite this there are
      powerful constructs in ogma.
  - Commands operate _across_ tables rather than singular values.
  - Easy to focus on the output of data, rather than _state_.
  - Typed data not only helps avoid semantic errors, but also allows for overloading of commands.

- **_Efficient_**
  - The ogma evaluation process sits between compiled and interpreted. When an expression is processed,
each atomic block of the expression is 'compiled' into an evaluation unit, with only knowledge of
_types_. This series of evaluation 'steps' is then evaluated with actual _values_. The split
between the 'typing' and the 'value' makes evaluations of repeated expressions (such as _mapping_
rows in a column) very fast since the typing evaluation has already been done.
  - ogma is written in Rust, which helps keep the performance profile consistent, along with providing
very fast evaluation performance of the compiled units.
  - Parallelisation is leveraged where possible, particularly with operations across tables. This
      can make huge differences to processing time and can shape how expressions are written to
      unlock this full performance potential.
  - Despite having value immutability, cloning of data is minimised with clone-on-writes.

- **_Batteries Included_**
  - Single binary with all dependencies embedded.
  - VS Code extension for integration with workflows.


## Development and Support
---
The ogma project needs development and financial support to help keep the project growing.
Financial support in the form of sponsorship is greatly appreciated, helping us spend more time on
the project.
The project is also open source, hosted on Github. Contributions are encouraged, not just for
features but important aspects such as bug fixes and documentation.
There is also a forum in which to ask and answer questions. The forum is a great way to cultivate a
community around the project and it is encouraged to participate.

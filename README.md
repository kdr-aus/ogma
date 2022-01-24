# ogma

![](logo.png)

Welcome to the `ogma` project!
`ogma` is a scripting language focused on _ergonomically_ and _efficiently_ 
processing tabular data, with _batteries included_.
Mixing aspects of terminal shells and functional programming, the ogma project lets one interact
with data in a refreshing way.
The language is syntactically lightweight yet boasts powerful constructs designed to
efficiently work with tabular data.

![](./docs/assets/common-cmds.filter.gif?raw=true)

# Getting Started

- [📥 Installation](https://daedalus.report/d/docs/Ogma.book/02%20getting%20started/2.1%20installation.md?pwd-raw=docs)
- [📖 Documentation](https://daedalus.report/d/docs/Ogma.book/01%20Introduction.md?pwd-raw=docs)
- [❓ Forum](https://forum.daedalus.report/)
- [❤️ Support us!](https://github.com/sponsors/kdr-aus)

# Language Characteristics

ogma takes inspiration from multiple sources. 
For the _semantics_, programming languages Rust, Haskell, ML, and Elm have
all been an influence, while the _syntax_ is derived primarily from terminal shells (with
smatterings from other languages). Some major characteristics of ogma are:
- small language with few keywords and opting for a **prefix** notation,
- uses **pipelines** to _chain_ together commands, composing their effects,
- it is **strictly typed**,
- can be extended with **user-defined** implementations _and_ types.


# Development and Support

The ogma project needs development and financial support to help keep the project growing.
Financial support in the form of sponsorship is greatly appreciated, helping us spend more time on
the project.
The project is also open source, hosted on Github. Contributions are encouraged, not just for
features but important aspects such as bug fixes and documentation.
There is also a forum in which to ask and answer questions. The forum is a great way to cultivate a
community around the project and it is encouraged to participate.

## Contributions
Pull requests are appreciated and encouraged! The request will be subject to a review and will 
need to pass the CI before being merged in. Please ensure:
- Tests are added where necessary,
- `cargo fmt -- --check` passes,
- `cargo clippy -- -D warnings` passes,
- `cargo test` passes,
- An item describing your pull request is added to [RELEASE.md](./RELEASE.md).

Happy coding!

# Release Process

When a release is ready, simply create a release tag and push it to Github.
The release workflow will take care of the build and release creation.
**The release body uses [RELEASE.md](./RELEASE.md) as the release notes.
Be sure to update this before the tag push!**

```
# Update RELEASE.md
git push
git tag v#.#
git push origin v#.#
```

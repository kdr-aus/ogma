**🛑 Breaking Changes**

**🔬 New Features**
- Improve help messages for defs with multiple input types
    (https://github.com/kdr-aus/ogma/pull/134)

**🐛 Bug Fixes**
- Fix variable type inferencing when passing variables to `def`s (https://github.com/kdr-aus/ogma/pull/115)
- Detect trailing command in `let` and suggest a pipe (https://github.com/kdr-aus/ogma/pull/113)
- Fix error where stronger type guarantees were present (https://github.com/kdr-aus/ogma/pull/117)
- Fix def not inferring correct input in `last` (https://github.com/kdr-aus/ogma/pull/147)
- Fix _locals graph needs updating_ bug (https://github.com/kdr-aus/ogma/pull/148)
- Provide more verbose parsing errors (https://github.com/kdr-aus/ogma/pull/151)
- Fix CPU spinning with completion prompt open (https://github.com/kdr-aus/ogma/pull/152)

**✨ Other Updates**
- `ogma` crate API documentation is now published at https://kdr-aus.github.io/ogma/ogma/ (https://github.com/kdr-aus/ogma/commit/cf5cc7979c399b609e2e0605ffe176e70e474ac2)
- Improve help messages and back end def input type matching
    (https://github.com/kdr-aus/ogma/pull/141)
- Introduce `TypesSet`s into the inferencer (https://github.com/kdr-aus/ogma/pull/144)
- Fully move to `TypesSets` for more robust type inference
    (https://github.com/kdr-aus/ogma/pull/145)

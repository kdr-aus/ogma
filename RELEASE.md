**🛑 Breaking Changes**
- [`to-str` now defaults to full number formatting with optional formatting string
    (https://github.com/kdr-aus/ogma/pull/85)
- Output inference is somewhat smarter for variadic cmds.
    (https://github.com/kdr-aus/ogma/pull/101)
    It does place stricter typing constraints on `+ - * / min max`.

**🔬 New Features**
- `#b` -- Newline constant (b for _break_) (https://github.com/kdr-aus/ogma/pull/75)
- `filter` now accepts `Str` input: it will supply one character at a time to the predicate.
    (https://github.com/kdr-aus/ogma/pull/76)

**🐛 Bug Fixes**
- Use a `BufWriter` around a `File` to improve `save` performance.
    (https://github.com/kdr-aus/ogma/pull/77)
- Flush `Write`r once finished writing. (https://github.com/kdr-aus/ogma/pull/78)
- Fixes (https://github.com/kdr-aus/ogma/issues/15) with new compilation engine.
- Output better error messages for unmatched commands (https://github.com/kdr-aus/ogma/pull/86)
- Dot operator now _infers_ output type when used with `TableRow`s.
    (https://github.com/kdr-aus/ogma/pull/87)
- Unscoped variables do not return a internal compiler error
    (https://github.com/kdr-aus/ogma/pull/102)

**✨ Other Updates**

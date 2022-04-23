**🛑 Breaking Changes**
- [`to-str` now defaults to full number formatting with optional formatting string
    (https://github.com/kdr-aus/ogma/pull/85)

**🔬 New Features**
- `#b` -- Newline constant (b for _break_) (https://github.com/kdr-aus/ogma/pull/75)
- `filter` now accepts `Str` input: it will supply one character at a time to the predicate.
    (https://github.com/kdr-aus/ogma/pull/76)

**🐛 Bug Fixes**
- Use a `BufWriter` around a `File` to improve `save` performance.
    (https://github.com/kdr-aus/ogma/pull/77)
- Flush `Write`r once finished writing. (https://github.com/kdr-aus/ogma/pull/78)
- Fixes (https://github.com/kdr-aus/ogma/issues/15) with new compilation engine.

**✨ Other Updates**

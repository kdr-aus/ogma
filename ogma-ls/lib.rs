//! Language server and completion generation for the `ogma` language.
#![warn(missing_docs)]

#[macro_use]
extern crate log;
use lsp_types::{Position, Range};

pub mod completion;
pub mod server;
mod workspace;

use workspace::*;

pub use workspace::Workspace;

// ###### LSP CODE SPANS HANDLING (UTF-16 =( ) #################################
/// Converts a `Position.character` into a byte position. The string to use is the _line_ the
/// character is on.
fn linech_to_idx(line: &str, chpos: usize) -> usize {
    let mut co_utf16 = 0;
    let mut co_utf8 = 0;
    for ch in line.chars() {
        if co_utf16 == chpos {
            break;
        }

        co_utf8 += ch.len_utf8();
        co_utf16 += ch.len_utf16();
    }

    co_utf8
}

fn pos_to_idx(s: &str, pos: Position) -> usize {
    let (posline, posch) = (pos.line as usize, pos.character as usize);

    let line = s.lines().nth(posline);

    match line {
        Some(line) => {
            // Offset of line starting pointer to string pointer
            let line_offset = (line.as_ptr() as usize).saturating_sub(s.as_ptr() as usize);
            let ch_offset = linech_to_idx(line, posch);

            line_offset + ch_offset
        }
        None => s.len(),
    }
}

fn lsp_range_to_range(s: &str, range: Range) -> std::ops::Range<usize> {
    pos_to_idx(s, range.start)..pos_to_idx(s, range.end)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_byte_position_works() {
        let pos = |line, character| Position { line, character };
        assert_eq!(pos_to_idx("Hello, world!", pos(0, 0)), 0);
        assert_eq!(pos_to_idx("Hello, world!", pos(0, 7)), 7);
        assert_eq!(pos_to_idx("hello\nworld\n!", pos(0, 5)), 5);
        assert_eq!(pos_to_idx("hello\nworld\n!", pos(0, 6)), 5);
        assert_eq!(pos_to_idx("hello\r\nworld\n!", pos(1, 0)), 7);
        assert_eq!(pos_to_idx("hello\r\nworld\n!", pos(1, 5)), 12);
        assert_eq!(pos_to_idx("hello\r\nworld\n!", pos(1, 6)), 12);
        assert_eq!(pos_to_idx("hello\r\nworld\n!", pos(2, 0)), 13);
        assert_eq!(pos_to_idx("hello\r\nworld\n!", pos(3, 100)), 14);
    }
}

#[derive(Copy, Clone, PartialEq, Debug)]
pub enum Mvmt {
    Ch(usize),
    Word,
}

pub struct InputBuffer {
    buf: Vec<char>,
    pos: usize,
    buf_changed: bool,
}

impl InputBuffer {
    pub fn new() -> Self {
        Self {
            buf: Vec::new(),
            pos: 0,
            buf_changed: false,
        }
    }

    pub fn clear(&mut self) {
        self.buf.clear();
        self.pos = 0;
        self.buf_changed = true;
    }

    pub fn buffer<T>(&self, range: T) -> String
    where
        T: std::slice::SliceIndex<[char], Output = [char]>,
    {
        self.buf[range].iter().collect()
    }

    pub fn chars<T>(&self, range: T) -> &[char]
    where
        T: std::slice::SliceIndex<[char], Output = [char]>,
    {
        &self.buf[range]
    }

    /// Calculates the _byte_ position of the position.
    pub fn buf_pos(&self) -> usize {
        self.buf[..self.pos].iter().map(|x| x.len_utf8()).sum()
    }

    /// Returns the _character_ position.
    pub fn ch_pos(&self) -> usize {
        self.pos
    }

    pub fn insert(&mut self, ch: char) {
        self.buf.insert(self.pos, ch);
        self.pos += 1;
        self.buf_changed = true;
    }

    pub fn insert_str(&mut self, s: &str) {
        for c in s.chars() {
            self.insert(c);
        }
    }

    /// Removes from _start_ of position.
    pub fn backspace(&mut self) {
        if self.pos > 0 {
            self.pos -= 1;
            self.buf.remove(self.pos);
            self.buf_changed = true;
        }
    }

    /// Removes from _end_ of position.
    pub fn delete(&mut self) {
        if self.pos < self.buf.len() {
            self.buf.remove(self.pos);
            self.buf_changed = true;
        }
    }

    pub fn move_start(&mut self) {
        self.pos = 0;
    }

    pub fn move_left(&mut self, by: Mvmt) {
        let n = mv_magnitude(by, self.buf[..self.pos].iter().copied().rev());
        self.pos = self.pos.saturating_sub(n);
    }

    pub fn move_right(&mut self, by: Mvmt) {
        let n = mv_magnitude(by, self.buf[self.pos..].iter().copied());
        self.pos = std::cmp::min(self.pos + n, self.buf.len());
    }

    pub fn buffer_changed(&self) -> bool {
        self.buf_changed
    }

    pub fn reset_buf_changed(&mut self) {
        self.buf_changed = false;
    }
}

fn mv_magnitude(by: Mvmt, chars: impl Iterator<Item = char>) -> usize {
    match by {
        Mvmt::Ch(x) => x,
        Mvmt::Word => {
            let mut seen = false;
            chars
                .take_while(|&c| {
                    let b = c.is_alphanumeric() || "-_".contains(c);
                    seen |= b;
                    seen == b
                })
                .count()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use Mvmt::*;

    #[test]
    fn test_input_movement() {
        let mut input = InputBuffer::new();

        "Hello, world!".chars().for_each(|c| input.insert(c));
        assert_eq!(&input.buffer(..), "Hello, world!");
        assert_eq!(input.pos, 13);

        // can't go past end of buffer
        input.move_right(Ch(1));
        assert_eq!(input.pos, 13);

        input.move_left(Ch(1));
        assert_eq!(input.pos, 12);

        input.insert('?');
        assert_eq!(&input.buffer(..), "Hello, world?!");
        assert_eq!(input.pos, 13);

        // can't go past start of buffer
        input.move_left(Ch(14));
        assert_eq!(input.pos, 0);
    }

    #[test]
    fn test_input_removing() {
        let mut input = InputBuffer::new();

        "Hello, world!".chars().for_each(|c| input.insert(c));

        input.delete();
        assert_eq!(&input.buffer(..), "Hello, world!");
        assert_eq!(input.pos, 13);

        input.backspace();
        assert_eq!(&input.buffer(..), "Hello, world");
        assert_eq!(input.pos, 12);

        input.move_left(Ch(14));
        input.backspace();
        assert_eq!(&input.buffer(..), "Hello, world");
        assert_eq!(input.pos, 0);

        input.delete();
        assert_eq!(&input.buffer(..), "ello, world");
        assert_eq!(input.pos, 0);
    }

    #[test]
    fn test_word_movement() {
        let f = |s: &str| mv_magnitude(Word, s.chars());
        assert_eq!(f("Hello, world!"), 5);
        assert_eq!(f(", world! Another word"), 7);
    }

    #[test]
    fn input_newline() {
        let mut input = InputBuffer::new();

        "Hello, world!".chars().for_each(|c| input.insert(c));
        assert_eq!(&input.buffer(..), "Hello, world!");
        assert_eq!(input.pos, 13);

        input.insert('\n');
        assert_eq!(&input.buffer(..), "Hello, world!\n");
        assert_eq!(input.pos, 14);
    }
}

use super::InputBuffer;
use crossbeam::channel::{unbounded, Receiver, Sender};
use std::sync::Arc;

const CMPL_ITEMS_LIM: usize = 10;

pub trait Completer: Send {
    fn complete(&self, input: &str, cursor_pos: usize, word_pos: usize) -> Vec<Completion>;
}

pub struct Completions {
    // engine
    changeset: u128,
    tx: Sender<Request>,
    rx: Receiver<Package>,

    // drawing
    items: Vec<Completion>,
    highlighted: Option<usize>,

    // inserting
    replace: String,
    start_pos: usize, // chars
    ins_len: usize,   // chars
}

impl Completions {
    pub fn new(completers: Vec<Box<dyn Completer>>) -> Self {
        let (req_tx, req_rx) = unbounded();
        let (pkg_tx, pkg_rx) = unbounded();

        spawn_engine(req_rx, pkg_tx, completers);

        Self {
            changeset: 0,
            tx: req_tx,
            rx: pkg_rx,
            items: Vec::new(),
            highlighted: None,
            replace: String::new(),
            start_pos: 0,
            ins_len: 0,
        }
    }

    pub fn request(&mut self, input_buf: &InputBuffer) {
        self.changeset = self.changeset.wrapping_add(1);
        self.reset();

        let input = input_buf.buffer(..);
        let cursor_pos = input_buf.buf_pos();
        let word_pos = word_start(&input, cursor_pos);
        self.replace = input[word_pos..cursor_pos].to_string();
        self.ins_len = self.replace.chars().count();
        self.start_pos = input_buf.ch_pos().saturating_sub(self.ins_len);

        let req = Request {
            changeset: self.changeset,
            input,
            cursor_pos,
            word_pos,
        };

        self.tx.send(req).ok();
    }

    /// Returns if there were items that were received.
    pub fn recv(&mut self) -> bool {
        let mut has = false;
        let chgset = self.changeset;
        for pkg in self.rx.try_iter().filter(|x| x.changeset == chgset) {
            has |= true;
            self.items.extend(pkg.items);
        }

        has
    }

    pub fn reset(&mut self) {
        self.items.clear();
        self.highlighted = None;
    }

    pub fn has(&self) -> bool {
        !self.items.is_empty()
    }

    pub fn word_pos(&self) -> usize {
        self.start_pos
    }

    pub fn items(&self) -> &[Completion] {
        &self.items
    }

    pub fn highlighted(&self) -> Option<usize> {
        self.highlighted
    }

    /// Returns the length to replace and the string to replace with.
    /// Can be used with `word_pos` to replace a range.
    /// The returned string is the new length that is to be replaced.
    pub fn highlight_next(&mut self) -> (usize, &str) {
        let l = Some(self.items.len().saturating_sub(1));
        self.highlighted = if l == self.highlighted {
            None
        } else if let Some(i) = self.highlighted {
            Some(i + 1)
        } else {
            Some(0)
        };
        self.replace_with()
    }

    /// See `highlight_next`.
    pub fn highlight_prev(&mut self) -> (usize, &str) {
        self.highlighted = match self.highlighted {
            Some(0) => None,
            Some(x) => Some(x.saturating_sub(1)),
            None => Some(self.items.len().saturating_sub(1)),
        };
        self.replace_with()
    }

    fn replace_with(&mut self) -> (usize, &str) {
        let len = self.ins_len; // copy prev len
        self.ins_len = self.cmpl().unwrap_or(&self.replace).chars().count();
        let with = self.cmpl().unwrap_or(&self.replace);
        (len, with)
    }

    fn cmpl(&self) -> Option<&str> {
        self.highlighted
            .and_then(|i| self.items.get(i))
            .map(|c| c.value.as_str())
    }
}

fn word_start(s: &str, before: usize) -> usize {
    let spliton = " \t\r\n./\\";
    let mut pos = 0;
    for (idx, ch) in s.char_indices() {
        if idx > before {
            break;
        }

        if spliton.contains(ch) {
            pos = idx + ch.len_utf8();
        }
    }

    std::cmp::min(pos, before) // ensure pos is always less than or eq before
}

struct Package {
    changeset: u128,
    items: Vec<Completion>,
}

pub struct Completion {
    pub value: String,
    pub ty: CompletionType,
}

pub enum CompletionType {
    Method,
    Type,
    Path,
    Literal,
}

impl CompletionType {
    pub fn tag(&self) -> &'static str {
        use CompletionType::*;
        match self {
            Method => "[M]",
            Type => "[T]",
            Path => "[P]",
            Literal => "[L]",
        }
    }
}

struct Request {
    changeset: u128,
    input: String,
    cursor_pos: usize,
    word_pos: usize,
}

fn spawn_engine(rx: Receiver<Request>, tx: Sender<Package>, completers: Vec<Box<dyn Completer>>) {
    std::thread::Builder::new()
        .name("completion-engine".into())
        .spawn(move || run_engine(rx, tx, completers))
        .unwrap();
}

fn run_engine(rx: Receiver<Request>, tx: Sender<Package>, completers: Vec<Box<dyn Completer>>) {
    // we spool off a thread per completer
    // each one has it's own channel and for each req that comes in we clone the request and send
    // it to the completer loops
    let mut senders = Vec::with_capacity(completers.len());
    for cmpltr in completers {
        let (txx, rxx) = unbounded();
        senders.push(txx);
        let tx = tx.clone();
        std::thread::Builder::new()
            .name("completion-engine-looper".into())
            .spawn(|| loop_completer(rxx, tx, cmpltr))
            .unwrap();
    }

    while let Ok(req) = rx.recv() {
        if rx.is_empty() {
            let req = Arc::new(req);
            for tx in &senders {
                tx.send(req.clone()).ok();
            }
        }
    }
}

fn loop_completer(rx: Receiver<Arc<Request>>, tx: Sender<Package>, completer: Box<dyn Completer>) {
    while let Ok(req) = rx.recv() {
        let Request {
            changeset,
            input,
            cursor_pos,
            word_pos,
        } = &*req;
        let mut items = completer.complete(input, *cursor_pos, *word_pos);
        // we do some cleaning of the items here to avoid massive completion lists.
        items.truncate(CMPL_ITEMS_LIM);
        if !items.is_empty() {
            let pkg = Package {
                changeset: *changeset,
                items,
            };
            tx.send(pkg).ok();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_word_start() {
        let f = word_start;
        assert_eq!(f("", 0), 0);
        assert_eq!(f("asdf", 4), 0);
        assert_eq!(f(" asdf", 5), 1);
        assert_eq!(f(" asdf.foo", 5), 5);
        assert_eq!(f(" asdf.foo", 10), 6);
        assert_eq!(f(" asdf.foo", 0), 0);
        assert_eq!(f(" asdf.foo", 1), 1);
    }
}

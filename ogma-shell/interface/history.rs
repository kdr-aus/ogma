const LIM: usize = 100;

pub struct History {
    items: Vec<String>,
    idx: Option<usize>,
}

impl History {
    pub fn new() -> Self {
        Self {
            items: Vec::new(),
            idx: None,
        }
    }

    pub fn current(&self) -> Option<&str> {
        self.idx.and_then(|i| self.items.get(i)).map(|x| x.as_str())
    }

    pub fn back(&mut self) {
        self.idx = match self.idx {
            Some(0) => None,
            Some(x) => Some(x.saturating_sub(1)),
            None => Some(self.items.len().saturating_sub(1)),
        };
    }

    pub fn fwd(&mut self) {
        let l = Some(self.items.len().saturating_sub(1));
        self.idx = if self.idx == l {
            None
        } else if let Some(x) = self.idx {
            Some(x + 1)
        } else {
            Some(0)
        };
    }

    /// Reset history posiiton to neutral value.
    pub fn add(&mut self, line: String) {
        while self.items.len() >= LIM {
            self.items.remove(0);
        }
        self.items.push(line);
        self.idx = None;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn truncating() {
        let mut h = History::new();
        for _ in 0..1000 {
            h.add(String::from("foo"));
        }
        assert_eq!(h.items.len(), LIM);
        assert_eq!(h.idx, None);
    }

    #[test]
    fn mvmt() {
        let mut h = History::new();
        h.add(String::from("one"));
        h.add(String::from("two"));
        h.add(String::from("three"));

        assert_eq!(h.idx, None);
        assert_eq!(h.current(), None);

        h.back();
        assert_eq!(h.idx, Some(2));
        assert_eq!(h.current(), Some("three"));

        h.back();
        h.back();
        assert_eq!(h.idx, Some(0));
        assert_eq!(h.current(), Some("one"));

        h.back();
        assert_eq!(h.idx, None);
        assert_eq!(h.current(), None);

        h.fwd();
        assert_eq!(h.idx, Some(0));
        assert_eq!(h.current(), Some("one"));

        h.fwd();
        h.fwd();
        assert_eq!(h.idx, Some(2));
        assert_eq!(h.current(), Some("three"));

        h.fwd();
        assert_eq!(h.idx, None);
        assert_eq!(h.current(), None);
    }
}

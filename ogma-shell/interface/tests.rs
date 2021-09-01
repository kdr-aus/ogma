use super::*;
use tui::backend::TestBackend;
use Event::*;
use KeyCode::*;
use KeyModifiers as Km;

struct TestCompleter;
impl Completer for TestCompleter {
    fn complete(&self, input: &str, cursor_pos: usize, word_pos: usize) -> Vec<Completion> {
        let items = &["aardvark", "animal", "animation", "banana", "baby", "boy"];
        let s = &input[word_pos..cursor_pos];
        let mut r = Vec::new();
        for item in items {
            if item.starts_with(s) {
                r.push(Completion {
                    value: item.to_string(),
                    ty: CompletionType::Path,
                });
            }
        }

        r
    }
}

struct Tester {
    term: Term<TestBackend>,
    state: TermState,
    enterfn: EnterFn,
}

impl Tester {
    fn new() -> Self {
        let config = || Config {
            title: " Testing ".into(),
            completers: vec![Box::new(TestCompleter)],
            ..Default::default()
        };

        let (state, enterfn) = init(config(), 10);
        let term = Term::new(TestBackend::new(30, 8)).unwrap();

        let state = TermState {
            tabs: vec![state],
            tab_selected: 0,
            draw_help: false,
            config_bldr: Box::new(config),
        };

        Self {
            term,
            state,
            enterfn,
        }
    }

    /// help for pushing characters as events
    fn input(&mut self, s: &str) {
        let evs: Vec<_> = s
            .chars()
            .map(|c| {
                let m = if c.is_uppercase() { Km::SHIFT } else { NOMOD };
                Key {
                    code: Char(c),
                    mods: m,
                }
            })
            .collect();
        self.push(evs);
    }

    fn enter(&mut self) {
        self.push(vec![Key {
            code: Enter,
            mods: NOMOD,
        }]);
    }

    fn shift_enter(&mut self) {
        self.push(vec![Key {
            code: Enter,
            mods: Km::SHIFT,
        }]);
    }

    fn trigger_completion(&mut self) {
        std::thread::sleep(std::time::Duration::from_millis(20)); // give time to return completions
        self.push(vec![]); // receives completions
        self.push(vec![]); // flags to draw them
    }

    fn push(&mut self, ev: Vec<Event>) {
        let Tester {
            term,
            state,
            enterfn,
        } = self;
        events_cycle(term, ev.into_iter(), enterfn, state).unwrap();
    }

    fn assert(&self, s: &str) {
        let buf = bufstr(self.term.backend().buffer());
        println!("{}", buf);
        let buf = format!("\n{}", buf);
        assert_eq!(buf, s);
    }
}

fn bufstr(buf: &tui::buffer::Buffer) -> String {
    let mut s = String::with_capacity(buf.content.len());
    for y in 0..buf.area.height {
        for x in 0..buf.area.width {
            s.push_str(&buf.get(x, y).symbol);
        }
        s.push('\n');
    }

    s
}

const LEFT: Event = Key {
    code: Left,
    mods: NOMOD,
};
const RIGHT: Event = Key {
    code: Right,
    mods: NOMOD,
};
const UP: Event = Key {
    code: Up,
    mods: NOMOD,
};
const DOWN: Event = Key {
    code: Down,
    mods: NOMOD,
};
const CLEFT: Event = Key {
    code: Left,
    mods: Km::CONTROL,
};
const CRIGHT: Event = Key {
    code: Right,
    mods: Km::CONTROL,
};

#[test]
fn test_input() {
    let mut t = Tester::new();
    t.input("Hello");
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> Hello                     ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.input(", world!");
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> Hello, world!             ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );
}

#[test]
fn outputs_reversed() {
    let mut t = Tester::new();
    t.input("Hello");
    t.enter();
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃>                           ┃
┃ Outputs ───────────────────┃
┃Hello                       ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.input("Hello1");
    t.enter();
    t.input("Hello2");
    t.enter();
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃>                           ┃
┃ Outputs ───────────────────┃
┃Hello2                      ┃
┃Hello1                      ┃
┃Hello                       ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );
}

#[test]
fn multiline_input() {
    let mut t = Tester::new();
    t.input("Hello, this should wrap into more lines. abcdefghijklmnopqrstuvwxyz");
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> Hello, this should wrap in┃
┃  to more lines. abcdefghijk┃
┃  lmnopqrstuvwxyz           ┃
┃ Outputs ───────────────────┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.enter();
    // one column for the scroll bar!
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃>                           ┃
┃ Outputs ───────────────────┃
┃Hello, this should wrap int ┃
┃o more lines. abcdefghijklm ┃
┃nopqrstuvwxyz               ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );
}

#[test]
fn completion_placement() {
    let mut t = Tester::new();
    t.input(" ");
    t.trigger_completion();
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃>                           ┃
┃ O aardvark  [P] ───────────┃
┃   animal    [P]            ┃
┃   animation [P]            ┃
┃   banana    [P]            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.input("a");
    t.trigger_completion();
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃>  a                        ┃
┃ O aardvark  [P] ───────────┃
┃   animal    [P]            ┃
┃   animation [P]            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.enter();
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃>                           ┃
┃ Outputs ───────────────────┃
┃ a                          ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.input("ba");
    t.trigger_completion();
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> ba                        ┃
┃  banana [P] ───────────────┃
┃  baby   [P]                ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );
}

#[test]
fn output_scrolling() {
    let mut t = Tester::new();
    t.input(
        "test01
test02
test03
test04
test05
test06
test07
test08
test09
test10
test11
test12
test13",
    );
    t.enter();
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃>                           ┃
┃ Outputs ───────────────────┃
┃test01                      ┃
┃test02                      ┃
┃test03                      ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    let up = Key {
        code: Up,
        mods: Km::SHIFT,
    };
    let down = Key {
        code: Down,
        mods: Km::SHIFT,
    };
    let pgup = Key {
        code: PageUp,
        mods: NOMOD,
    };
    let pgdown = Key {
        code: PageDown,
        mods: NOMOD,
    };

    t.push(vec![down]);
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃>                           ┃
┃ Outputs ───────────────────┃
┃test06                      ┃
┃test07                      ┃
┃test08                      ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.push(vec![up, up, up, up]);
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃>                           ┃
┃ Outputs ───────────────────┃
┃test01                      ┃
┃test02                      ┃
┃test03                      ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.push(vec![pgdown]);
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃>                           ┃
┃ Outputs ───────────────────┃
┃test13                      ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );
    t.push(vec![pgup]);
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃>                           ┃
┃ Outputs ───────────────────┃
┃test01                      ┃
┃test02                      ┃
┃test03                      ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.push(vec![down, down]);
    t.input("hello");
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> hello                     ┃
┃ Outputs ───────────────────┃
┃test11                      ┃
┃test12                      ┃
┃test13                      ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.enter();
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃>                           ┃
┃ Outputs ───────────────────┃
┃hello                       ┃
┃test01                      ┃
┃test02                      ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );
}

#[test]
fn toggle_help() {
    let mut t = Tester::new();
    t.input(" ");
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃>                           ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.push(vec![Key {
        code: Char('h'),
        mods: Km::CONTROL,
    }]);
    t.assert(
        "
┃ Tab 1                      ┃
           Ctrl+h: toggle help
             Ctrl+q: close tab
          Ctrl+t: open new tab
               Tab: cycle tabs
Shift+↑|PgUp: scroll output up
Shift+↓|PgDown: scroll output 
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );
}

#[test]
fn test_tabbing() {
    let mut t = Tester::new();
    let newtab = Key {
        code: Char('t'),
        mods: Km::CONTROL,
    };
    let tab = Key {
        code: Tab,
        mods: NOMOD,
    };
    t.input("One");
    t.push(vec![newtab]);
    t.input("Two");
    t.enter();
    t.assert(
        "
┃ Tab 1 │ Tab 2              ┃
┃ Testing ───────────────────┃
┃>                           ┃
┃ Outputs ───────────────────┃
┃Two                         ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.push(vec![tab]);
    t.assert(
        "
┃ Tab 1 │ Tab 2              ┃
┃ Testing ───────────────────┃
┃> One                       ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.push(vec![Key {
        code: Char('q'),
        mods: Km::CONTROL,
    }]);
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃>                           ┃
┃ Outputs ───────────────────┃
┃Two                         ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );
}

#[test]
fn left_mvmt() {
    let mut t = Tester::new();
    t.input("elo");
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> elo                       ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.push(vec![LEFT]);
    t.input("l");
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> ello                      ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.push(vec![LEFT, LEFT, LEFT, LEFT, LEFT, LEFT, LEFT, LEFT, LEFT]);
    t.input("H");
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> Hello                     ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );
}

#[test]
fn right_mvmt() {
    let mut t = Tester::new();
    t.input("elo");
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> elo                       ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.push(vec![LEFT, LEFT, LEFT, LEFT, LEFT, LEFT, LEFT, LEFT, LEFT]);
    t.input("H");
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> Helo                      ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.push(vec![RIGHT, RIGHT]);
    t.input("l");
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> Hello                     ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.push(vec![RIGHT, RIGHT, RIGHT, RIGHT, RIGHT, RIGHT, RIGHT]);
    t.input(", world!");
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> Hello, world!             ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );
}

#[test]
fn completions_hide_with_cursor_mvmt() {
    let mut t = Tester::new();
    t.input("an");
    t.trigger_completion();
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> an                        ┃
┃  animal    [P] ────────────┃
┃  animation [P]             ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.push(vec![LEFT]);
    t.trigger_completion();
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> an                        ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );
}

#[test]
fn backspace_testing() {
    let mut t = Tester::new();
    t.input("Helllo");
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> Helllo                    ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    let bksp = Key {
        code: Backspace,
        mods: NOMOD,
    };

    t.push(vec![LEFT, bksp]);
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> Hello                     ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.push(vec![bksp, bksp, bksp, bksp, bksp, bksp]);
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> o                         ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    let bksp = Key {
        code: Backspace,
        mods: Km::SHIFT,
    };

    t.input("Hell");
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> Hello                     ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.push(vec![bksp, bksp]);
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> Heo                       ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );
}

#[test]
fn delete_testing() {
    let mut t = Tester::new();
    t.input("Helllo");
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> Helllo                    ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    let del = Key {
        code: Delete,
        mods: NOMOD,
    };

    t.push(vec![LEFT, LEFT, del]);
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> Hello                     ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.push(vec![del, del, del, del, del, del]);
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> Hell                      ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );
}

#[test]
fn completions_testing() {
    let mut t = Tester::new();
    t.input("a");
    t.trigger_completion();
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> a                         ┃
┃  aardvark  [P] ────────────┃
┃  animal    [P]             ┃
┃  animation [P]             ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    let up = UP;
    let down = DOWN;

    t.push(vec![up, up]);
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> animal                    ┃
┃  aardvark  [P] ────────────┃
┃  animal    [P]             ┃
┃  animation [P]             ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.push(vec![down, down, down]);
    t.input(" ba");
    t.trigger_completion();
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> aardvark ba               ┃
┃ Outputs ─ banana [P] ──────┃
┃           baby   [P]       ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.push(vec![Key {
        code: Esc,
        mods: NOMOD,
    }]);
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> aardvark ba               ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );
}

#[test]
fn history_testing() {
    let mut t = Tester::new();
    t.input("Helllo");
    t.enter();
    t.input("World");
    t.enter();
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃>                           ┃
┃ Outputs ───────────────────┃
┃World                       ┃
┃Helllo                      ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.push(vec![UP]);
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> World                     ┃
┃ Outputs ───────────────────┃
┃World                       ┃
┃Helllo                      ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.push(vec![DOWN, DOWN]);
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> Helllo                    ┃
┃ Outputs ───────────────────┃
┃World                       ┃
┃Helllo                      ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.push(vec![DOWN, DOWN]);
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃>                           ┃
┃ Outputs ───────────────────┃
┃World                       ┃
┃Helllo                      ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );
}

#[test]
fn left_word_mvmt() {
    let mut t = Tester::new();
    t.input("ello, orld!  , . ");
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> ello, orld!  , .          ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    // The way the movement words, it ignore non-word (! or space) to bring it to beginning of
    // other word
    t.push(vec![CLEFT]);
    t.input("w");
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> ello, world!  , .         ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.push(vec![CLEFT, CLEFT, CLEFT]);
    t.input("H");
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> Hello, world!  , .        ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );
}

#[test]
fn right_word_mvmt() {
    let mut t = Tester::new();
    t.input("ell");
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> ell                       ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.push(vec![CLEFT]);
    t.input("H");
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> Hell                      ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.push(vec![CRIGHT, CRIGHT]);
    t.input("o");
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> Hello                     ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );
}

#[test]
fn completions_offscreen_testing() {
    let mut t = Tester::new();

    t.input("a");
    t.trigger_completion();
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> a                         ┃
┃  aardvark  [P] ────────────┃
┃  animal    [P]             ┃
┃  animation [P]             ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.input("nimal foobar a");
    t.trigger_completion();
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> animal foobar a           ┃
┃ Outputs ────── aardvark  [P┃
┃                animal    [P┃
┃                animation [P┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.input("  a");
    t.trigger_completion();
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> animal foobar a  a        ┃
┃ Outputs ───────── aardvark ┃
┃                   animal   ┃
┃                   animation┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.input("  a");
    t.trigger_completion();
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> animal foobar a  a  a     ┃
┃ Outputs ──────────── aardva┃
┃                      animal┃
┃                      animat┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.input("    a");
    t.trigger_completion();
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> animal foobar a  a  a    a┃
┃ Outputs ───────────────── a┃
┃                           a┃
┃                           a┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );
}

#[test]
fn shift_enter_newlines() {
    let mut t = Tester::new();
    t.input("Hello, this should\nwrap into more lines");
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> Hello, this should        ┃
┃  wrap into more lines      ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.enter();
    // one column for the scroll bar!
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃>                           ┃
┃ Outputs ───────────────────┃
┃Hello, this should          ┃
┃wrap into more lines        ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.input("Hello");
    t.shift_enter();
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> Hello                     ┃
┃                            ┃
┃ Outputs ───────────────────┃
┃Hello, this should          ┃
┃wrap into more lines        ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.input("World");
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> Hello                     ┃
┃  World                     ┃
┃ Outputs ───────────────────┃
┃Hello, this should          ┃
┃wrap into more lines        ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );
}

#[test]
fn completions_multiline_testing() {
    let mut t = Tester::new();
    t.input("animal\na");
    t.trigger_completion();
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> animal                    ┃
┃  a                         ┃
┃  aardvark  [P] ────────────┃
┃  animal    [P]             ┃
┃  animation [P]             ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    let up = UP;
    let down = DOWN;

    t.push(vec![up, up]);
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> animal                    ┃
┃  animal                    ┃
┃  aardvark  [P] ────────────┃
┃  animal    [P]             ┃
┃  animation [P]             ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.push(vec![down, down, down]);
    t.input(" ba");
    t.trigger_completion();
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> animal                    ┃
┃  aardvark ba               ┃
┃ Outputs ─ banana [P] ──────┃
┃           baby   [P]       ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );

    t.push(vec![Key {
        code: Esc,
        mods: NOMOD,
    }]);
    t.assert(
        "
┃ Tab 1                      ┃
┃ Testing ───────────────────┃
┃> animal                    ┃
┃  aardvark ba               ┃
┃ Outputs ───────────────────┃
┃                            ┃
┃                            ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
",
    );
}

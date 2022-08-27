use ::libs::crossbeam::channel::{unbounded, Receiver};
use crossterm::event::{read, Event as XtEvent, KeyEvent};
use std::io;

pub use crossterm::event::{KeyCode, KeyModifiers};

pub struct Events(Receiver<Event>);

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum Event {
    Key { code: KeyCode, mods: KeyModifiers },
    Resize,
}

impl Events {
    pub fn new() -> io::Result<Self> {
        let (tx, rx) = unbounded();
        std::thread::Builder::new()
            .name("terminal-event-buffer".into())
            .spawn(move || loop {
                while let Ok(ev) = read() {
                    if let Some(ev) = Event::convert_xt(ev) {
                        if tx.send(ev).is_err() {
                            break;
                        }
                    }
                }
            })?;
        Ok(Events(rx))
    }
}

impl Iterator for Events {
    type Item = Event;
    fn next(&mut self) -> Option<Event> {
        self.0.try_recv().ok()
    }
}

impl Event {
    fn convert_xt(ev: XtEvent) -> Option<Self> {
        match ev {
            XtEvent::Key(KeyEvent { code, modifiers }) => Some(Event::Key {
                code,
                mods: modifiers,
            }),
            XtEvent::Resize(_, _) => Some(Event::Resize),
            _ => None,
        }
    }
}

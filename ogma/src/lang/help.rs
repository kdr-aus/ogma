use crate::prelude::{err::help_as_error, Str};
use std::fmt;

/// Help messages work off the back of error messages such that:
/// ```shell
/// Help: `command`
/// --> help:0
///  | description
///  |
///  | Usage:
///  |  => command params
///  |
///  | Examples:
///  |  example-desc
///  |  => command example-code
/// ```
#[derive(Clone)]
pub struct HelpMessage {
    pub cmd: Str,
    pub desc: Str,
    pub params: Vec<HelpParameter>,
    pub no_space: bool,
    /// (flag-name, description)
    pub flags: Vec<(&'static str, &'static str)>,
    pub examples: Vec<HelpExample>,
}

impl HelpMessage {
    pub fn new<C: Into<Str>>(cmd: C) -> Self {
        Self {
            cmd: cmd.into(),
            desc: Str::default(),
            params: Vec::new(),
            no_space: false,
            flags: Vec::new(),
            examples: Vec::new(),
        }
    }
}

impl fmt::Display for HelpMessage {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", help_as_error(self))
    }
}

#[derive(Clone)]
pub enum HelpParameter {
    Required(Str),
    Optional(Str),
    Custom(Str),
    /// Used to break to a new line for the help usage message.
    Break,
}

impl HelpParameter {
    pub fn write(&self, wtr: &mut dyn fmt::Write) {
        match self {
            HelpParameter::Required(p) | HelpParameter::Custom(p) => write!(wtr, "{}", p),
            HelpParameter::Optional(p) => write!(wtr, "[{}]", p),
            HelpParameter::Break => panic!("`write` should not be called on HelpParameter::Break"),
        }
        .ok();
    }
}

#[derive(Clone)]
pub struct HelpExample {
    pub desc: &'static str,
    pub code: &'static str,
}

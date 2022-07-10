use crate::prelude::Str;
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::err::help_as_error;

    #[test]
    fn help_msg() {
        use HelpParameter::*;

        let h = HelpMessage {
            desc: "this is a description".into(),
            params: vec![Required("required1".into()), Required("req2".into())],
            ..HelpMessage::new("cmd-name")
        };
        let s = help_as_error(&h, None).to_string();
        assert_eq!(
            &s,
            "Help: `cmd-name`
--> shell:0
 | ---- Input Type: <any> ----
 | this is a description
 | 
 | Usage:
 |  => cmd-name required1 req2
"
        );

        let h = HelpMessage {
            desc: "this is a description".into(),
            examples: vec![
                HelpExample {
                    desc: "example 1",
                    code: "cmd-name this is a thingo",
                },
                HelpExample {
                    desc: "example 2",
                    code: "cmd-name ",
                },
            ],
            ..HelpMessage::new("cmd-name")
        };
        let s = help_as_error(&h, Some(&crate::prelude::Type::Tab)).to_string();
        assert_eq!(
            &s,
            "Help: `cmd-name`
--> shell:0
 | ---- Input Type: Table ----
 | this is a description
 | 
 | Usage:
 |  => cmd-name
 | 
 | Examples:
 |  example 1
 |  => cmd-name this is a thingo
 | 
 |  example 2
 |  => cmd-name 
"
        );
    }
}

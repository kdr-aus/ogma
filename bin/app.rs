use clap::*;

#[derive(Parser, PartialEq, Eq, Debug)]
#[clap(name = "ogma")]
#[clap(author = "Kurt Lawrence <kurtlawrence92@gmail.com>")]
#[clap(about = "Scripting language for manipulating tabular data")]
pub struct App {
    /// Suppress progress output.
    #[clap(short, long)]
    pub quiet: bool,

    /// Include definition file. Glob syntax is supported.
    #[clap(long)]
    pub def: Option<Vec<String>>,

    /// Files to process. If none specified, a REPL instance is started.
    pub files: Vec<String>,
}

#[cfg(test)]
mod tests {
    use super::App;
    use super::*;

    #[test]
    fn verify_app_01() {
        App::command().debug_assert();
    }

    #[test]
    fn verify_app_02() {
        let a = App::try_parse_from(["ogma"]).unwrap();
        assert_eq!(
            a,
            App {
                quiet: false,
                def: None,
                files: vec![]
            }
        );

        let a = App::try_parse_from("ogma -q".split(' ')).unwrap();
        assert_eq!(
            a,
            App {
                quiet: true,
                def: None,
                files: vec![]
            }
        );

        let a = App::try_parse_from("ogma --def foo".split(' ')).unwrap();
        assert_eq!(
            a,
            App {
                quiet: false,
                def: Some(vec!["foo".to_string()]),
                files: vec![]
            }
        );

        let a = App::try_parse_from("ogma --def foo --def bar".split(' ')).unwrap();
        assert_eq!(
            a,
            App {
                quiet: false,
                def: Some(vec!["foo".to_string(), "bar".to_string()]),
                files: vec![]
            }
        );

        let a = App::try_parse_from("ogma foo".split(' ')).unwrap();
        assert_eq!(
            a,
            App {
                quiet: false,
                def: None,
                files: vec!["foo".to_string()]
            }
        );

        let a = App::try_parse_from("ogma foo bar".split(' ')).unwrap();
        assert_eq!(
            a,
            App {
                quiet: false,
                def: None,
                files: vec!["foo".to_string(), "bar".to_string()]
            }
        );

        let a = App::try_parse_from("ogma --def=foo --def bar foo bar".split(' ')).unwrap();
        assert_eq!(
            a,
            App {
                quiet: false,
                def: Some(vec!["foo".to_string(), "bar".to_string()]),
                files: vec!["foo".to_string(), "bar".to_string()]
            }
        );
    }
}

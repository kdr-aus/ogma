use clap::*;

#[derive(Parser)]
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

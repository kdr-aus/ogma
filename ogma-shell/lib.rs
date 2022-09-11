//! A terminal interface for `ogma`.
#![warn(missing_docs)]
use ::libs::{colored::*, divvy::*, rustc_hash::FxHashMap as HashMap};
use ogma::{
    lang::{ast::Location, Value},
    rt::bat::Batch,
};
use ogma_ls::{completion::Node, Workspace};
use std::{
    fmt::Write as _,
    io::{self, Write},
    path::{Path, PathBuf},
};
use tui::{backend::Backend, Terminal};

mod interface;

use interface::{Cancelled, Completion, Config, Events, Input, TabId};

/// Builder for `ogma` shell.
pub struct OgmaShell {
    /// The title to use.
    pub title: String,
    /// The working directory root.
    pub root: PathBuf,
    /// File paths to look for definitions.
    pub defs_file_paths: Vec<PathBuf>,
}

impl OgmaShell {
    /// Initialise a builder with required items.
    pub fn init(root: PathBuf) -> Self {
        Self {
            title: String::new(),
            root,
            defs_file_paths: Vec::new(),
        }
    }

    /// Set the title.
    pub fn title(mut self, title: String) -> Self {
        self.title = title;
        self
    }

    /// Add a definition file path.
    ///
    /// Processes the path, if absolute takes verbatim, if not the root is prefixed.
    pub fn defs_file_path<P: AsRef<Path>>(mut self, path: P) -> Self {
        let path = path.as_ref();
        let path = if path.is_absolute() {
            path.to_path_buf()
        } else {
            self.root.join(path)
        };
        self.defs_file_paths.push(path);
        self
    }

    /// Run the shell.
    ///
    /// > Blocking operation.
    pub fn run(self) -> io::Result<()> {
        let OgmaShell {
            title,
            root,
            defs_file_paths,
        } = self;

        let wsp = Workspace::init();
        let mut state = RunState {
            wsp: wsp.clone(),
            root: root.clone(),
            tabs: HashMap::default(),
            defs_file_paths,
        };
        let on_enter_press = Box::new(move |i, t, c| state.on_enter(i, t, c));
        let wsp2 = wsp.clone();
        let decorate_input = Box::new(move |line: String, _| syntax_highlight(&line, &wsp2));

        run(move || {
            let prompt = format!("{}> ", root.display());
            let completers = Completer::init(wsp.clone(), root.clone());

            Config {
                title: title.clone(),
                prompt,
                on_enter_press: on_enter_press.clone(),
                completers,
                decorate_input: decorate_input.clone(),
            }
        })
    }
}

fn run<F>(config: F) -> io::Result<()>
where
    F: FnMut() -> Config + 'static,
{
    let stdout = io::stdout();
    let backend = tui::backend::CrosstermBackend::new(stdout);
    let events = Events::new()?;

    crossterm::terminal::enable_raw_mode().ok();
    let r = interface::run(events, backend, config).and_then(cleanup);
    crossterm::terminal::disable_raw_mode().ok();
    r
}

fn cleanup<B: Backend>(mut term: Terminal<B>) -> io::Result<()> {
    term.clear()
}

#[derive(Clone)]
struct RunState {
    /// This is a convenient store of the `Definitions`. It also is required for completions
    /// (normally for a a LSP server but can be used through the API to get completions).
    wsp: Workspace,
    root: PathBuf,
    defs_file_paths: Vec<PathBuf>,
    tabs: HashMap<TabId, PathBuf>,
}

struct Context<'a> {
    root: &'a Path,
    wd: &'a Path,
    progress: &'a ProgressTx,
}

// ###### ON ENTER PRESS #######################################################
impl RunState {
    fn on_enter(
        &mut self,
        input: Input,
        tabid: TabId,
        cancelled: Cancelled,
    ) -> interface::ConfigUpdate {
        let mut cu = interface::ConfigUpdate::default();

        // the output is captured in a buffer and written as an output at the end
        // the outputs _should_ be all valid utf8
        let mut buffer = Vec::new();
        let buf = &mut buffer;

        // write the header input line
        writeln!(buf, ">> {}", input.as_str().yellow()).ok();

        if let Some(remaining) = input.strip_prefix("cd ") {
            // change the working directory
            self.handle_cd(tabid, remaining, buf);
            let wd = self.tab_wd(tabid).to_path_buf();
            cu.new_prompt = Some(format!("{}> ", wd.display()));
            cu.new_completions = Some(interface::Completions::new(Completer::init(
                self.wsp.clone(),
                wd,
            )));
        } else if let Some(remaining) = input.strip_prefix("run ") {
            // process a batch
            match self.parse_batch(tabid, remaining) {
                Ok(b) => match b {
                    Ok(b) => self.process_batch(tabid, cancelled, buf, b),
                    Err(e) => {
                        write_err(e, &self.wsp, buf).ok();
                    }
                },
                Err(e) => (writeln!(buf, "{}", e.to_string().bright_red()).ok(), ()).1,
            }
        } else if ogma::lang::recognise_definition(&input) {
            if input.contains(" --load") {
                // load defs from the paths defined
                self.load_defs_files(buf);
            } else {
                let r = {
                    let defs = &mut self.wsp.defs.write();
                    ogma::lang::process_definition(&input, Location::Shell, None, defs)
                };
                match r {
                    Ok((input, Some(code))) => {
                        self.process_expr(tabid, cancelled, buf, code.into(), input)
                    }
                    x => write_result(x.map(|x| x.0), &self.wsp, buf),
                }
            }
        } else {
            self.process_expr(tabid, cancelled, buf, input, ().into());
        }

        let value = String::from_utf8(buffer).expect("all valid utf8");
        cu.add_output = Some(value);
        cu
    }

    fn tab_wd(&mut self, id: TabId) -> &Path {
        let RunState { tabs, root, .. } = self;
        tabs.entry(id).or_insert_with(|| root.clone())
    }

    fn handle_cd<W: Write>(&mut self, tab_id: TabId, path: &str, mut buf: W) {
        if !path.is_empty() {
            if let Err(e) = self.change_working_dir(tab_id, path) {
                writeln!(buf, "{}", e.to_string().bright_red()).ok();
            }
        }
        write!(buf, "working dir: {}", self.tab_wd(tab_id).display()).ok();
    }

    fn change_working_dir<P: AsRef<Path>>(&mut self, tab_id: TabId, path: P) -> io::Result<()> {
        let wd = self.validate_path(tab_id, path)?;
        self.tabs.insert(tab_id, wd);
        Ok(())
    }

    /// Ensures the path exists and it **does not point to above the root directory**.
    fn validate_path<P: AsRef<Path>>(&self, tab_id: TabId, path: P) -> io::Result<PathBuf> {
        let path = path.as_ref();
        let wd = match self.tabs.get(&tab_id) {
            Some(p) => self.root.join(p),
            None => self.root.clone(),
        };
        let wd = wd
            .join(path)
            .canonicalize()
            .map_err(|e| io::Error::new(e.kind(), format!("{}: {}", e, path.display())))?;

        let root = self
            .root
            .canonicalize()
            .unwrap_or_else(|_| PathBuf::from("."));

        wd.strip_prefix(&root)
            .map_err(|_| io::Error::new(io::ErrorKind::Other, "cannot move above root directory"))
            .map(|x| x.to_path_buf())
    }

    fn load_defs_files<W: Write>(&mut self, mut buf: W) {
        let mut x = true;
        let defs = &mut self.wsp.defs.write();
        for path in &self.defs_file_paths {
            // append new lines only on subsequent paths
            if x {
                x = false;
            } else {
                writeln!(buf).ok();
            }

            match defs.add_from_file(path) {
                Ok(n) => write!(
                    buf,
                    "{}: {}",
                    path.display(),
                    format!("parsed in {} definitions", n).bright_green()
                ),
                Err(e) => ogma::output::print_error(&e, &mut buf),
            }
            .ok();
        }
    }

    fn process_seq<W, F>(&mut self, tab_id: TabId, cancelled: Switch, mut buf: W, f: F)
    where
        W: Write,
        F: FnOnce(Context) -> String + Send + 'static,
    {
        let root = self.root.to_path_buf();
        let wd = self.tab_wd(tab_id).to_path_buf();
        let progress = ProgressTx::dummy();
        let completed = Switch::off();
        let completed_clone = completed.clone();

        let thread = std::thread::Builder::new()
            .name("ogma-shell-processing".into())
            .spawn(move || {
                let x = f(Context {
                    root: &root,
                    wd: &wd,
                    progress: &progress,
                });
                completed_clone.flip_on();
                x
            })
            .expect("should be fine spawning a thread");

        while !completed.get() {
            if cancelled.get() {
                return;
            }
            std::thread::sleep(std::time::Duration::from_millis(100));
        }

        match thread.join() {
            Ok(r) => write!(buf, "{}", r),
            Err(_) => write!(buf, "failed joining processing thread"),
        }
        .ok();
    }

    fn process_expr<W: Write>(
        &mut self,
        tab_id: TabId,
        cancelled: Switch,
        buf: W,
        expr: String,
        input: ::ogma::lang::Value,
    ) {
        use ::ogma::{lang::Value::*, rt::process_expression as proc};
        let wsp = self.wsp.clone();
        self.process_seq(tab_id, cancelled, buf, move |cx| {
            let d = &wsp.defs.read();
            let e = expr;
            let l = Location::Shell;
            let root = cx.root;
            let wd = cx.wd;
            let r = match input {
                Nil => proc((), e, l, d, root, wd),
                Bool(x) => proc(x, e, l, d, root, wd),
                Num(x) => proc(x, e, l, d, root, wd),
                Str(x) => proc(x, e, l, d, root, wd),
                Tab(x) => proc(x, e, l, d, root, wd),
                x => panic!(
                    "cannot process the type {:?} as input into process_expression",
                    x
                ),
            };

            let mut buf = Vec::new();
            write_result(r, &wsp, &mut buf);
            String::from_utf8(buf).expect("all written output should be utf8")
        })
    }

    fn parse_batch(
        &self,
        tab_id: TabId,
        file_flags: &str,
    ) -> io::Result<Result<Batch, ogma::Error>> {
        let (pflag, fflag) = (" --no-par", " --no-fast-fail");
        let (r, parallelise) = if file_flags.contains(pflag) {
            (file_flags.replace(pflag, ""), Some(false))
        } else {
            (file_flags.to_string(), None)
        };
        let (r, fail_fast) = if r.contains(fflag) {
            (r.replace(fflag, ""), Some(false))
        } else {
            (r, None)
        };
        self.validate_path(tab_id, r)
            .and_then(ogma::rt::bat::parse_file)
            .map(|mut batch| {
                if let Ok(batch) = &mut batch {
                    if let Some(x) = parallelise {
                        batch.parallelise = x;
                    }
                    if let Some(x) = fail_fast {
                        batch.fail_fast = x;
                    }
                }
                batch
            })
    }

    fn process_batch<W: Write>(&mut self, tab_id: TabId, cancelled: Switch, buf: W, batch: Batch) {
        use ogma::rt::bat::Outcome::*;
        let defs = self.wsp.defs.read().clone();
        self.process_seq(tab_id, cancelled, buf, move |cx| {
            let report = || batch.items.iter().map(|i| (i.line, i.ty()));
            let root = cx.root;
            let wd = cx.wd;
            let prg = cx.progress;
            let outcomes = ogma::rt::bat::process(&batch, root, wd, prg, defs);

            let mut buffer = Vec::new();
            let buf = &mut buffer;
            for ((line, ty), o) in report().zip(outcomes.iter()) {
                write!(buf, "line {} :: {:?} :: ", line, ty).ok();
                match o {
                    (Success, t) => writeln!(buf, "{} ... {:#?}", "SUCCESS".bright_green(), t),
                    (Failed(_), t) => writeln!(buf, "{} ... {:#?}", "ERROR".bright_red(), t),
                    (Outstanding, _) => writeln!(buf, "{}", "OUTSTANDING".bright_cyan()),
                    (Cancelled, _) => writeln!(buf, "{}", "CANCELLED".bright_yellow()),
                }
                .ok();
            }

            for ((line, ty), err) in report()
                .zip(outcomes.into_iter())
                .filter_map(|(x, o)| match o {
                    (Failed(e), _) => Some((x, e)),
                    _ => None,
                })
            {
                writeln!(buf, "--- Error line {} :: {:?} ---", line, ty).ok();
                ogma::output::print_error(&err, buf).ok();
            }
            String::from_utf8(buffer).expect("all written output should be utf8")
        })
    }
}

fn write_result<W: Write>(
    res: Result<ogma::lang::Value, ogma::Error>,
    wsp: &Workspace,
    mut wtr: W,
) {
    use ogma::output::*;

    match res {
        Ok(output) => match output {
            Value::Nil => write!(wtr, "()"),
            Value::Bool(b) => write!(wtr, "{}", b),
            Value::Num(num) => write!(wtr, "{}", num),
            Value::Str(s) => write!(wtr, "{}", s),
            Value::Tab(table) => print_table(&table, &mut wtr),
            Value::TabRow(_) => write!(wtr, "<table row>"),
            Value::Ogma(data) => write!(wtr, "{}", print_ogma_data(data)),
        },
        Err(e) => write_err(e, wsp, wtr),
    }
    .expect("failed writing to REPL");
}

fn write_err<W: Write>(e: ogma::Error, wsp: &Workspace, mut wtr: W) -> io::Result<()> {
    use ogma::output::*;

    let mut buf = Vec::new();
    print_error(&e, &mut buf).ok();
    let buf = String::from_utf8(buf).expect("help uses valid utf-8");
    let buf = if buf
        .lines()
        .next()
        .map(|s| s.contains("Help"))
        .unwrap_or(false)
    {
        highlight_help(&buf, wsp)
    } else {
        buf
    };
    write!(wtr, "{}", buf)
}

// ###### COMPLETIONS ##########################################################
struct Completer {
    wsp: Workspace,
    wd: PathBuf,
}

impl Completer {
    pub fn init<P: Into<PathBuf>>(wsp: Workspace, wd: P) -> Vec<Box<dyn interface::Completer>> {
        vec![Box::new(Self { wsp, wd: wd.into() })]
    }
}

impl interface::Completer for Completer {
    fn complete(&self, input: &str, cursor_pos: usize, word_pos: usize) -> Vec<Completion> {
        fn def_to_completion(def: ogma_ls::completion::Def) -> Completion {
            use interface::CompletionType as C;
            use ogma_ls::completion::Kind as K;

            let value = def.name;
            let ty = match def.kind {
                K::Impl => C::Method,
                K::Type => C::Type,
                K::Dir | K::File => C::Path,
                K::Lit => C::Literal,
            };

            Completion { value, ty }
        }

        let word = &input[word_pos..cursor_pos];

        ogma_ls::completion::get(&self.wsp, &input[..cursor_pos], Some(&self.wd))
            .unwrap_or_default()
            .into_iter()
            .filter(|def| def.name.starts_with(word))
            .take(24)
            .map(def_to_completion)
            .collect()
    }
}

// ###### COLOURING ############################################################

fn syntax_highlight(line: &str, wsp: &Workspace) -> String {
    // manually allow def and def-ty code. not a great handling but good enough.
    match wsp.parse(line) {
        Ok(x) => highlight_from_nodes(line, x.append_leaves(Vec::new())),
        Err(_) => {
            let allowed = ["def --list", "def --clear", "def --load"];
            if allowed.iter().any(|x| line.contains(x)) {
                line.into()
            } else {
                let mut buf = String::new();
                write!(&mut buf, "{}", line.red().underline()).ok();
                buf
            }
        }
    }
}

fn highlight_from_nodes(line: &str, mut nodes: Vec<Node>) -> String {
    use ogma_ls::completion::NodeType::*;
    // mutate variables and flags to capture the $ and -- prefixes
    for node in &mut nodes {
        match node.ty {
            Var => node.tag.make_mut().start = node.tag.start.saturating_sub(1), // $
            Flag => {
                // --
                // if has a quote or double quote at tag.start - 1 then have to colour that and tag.end + 1
                let c = line.chars().nth(node.tag.start.saturating_sub(1));
                let (s, e) = if c == Some('\'') || c == Some('"') {
                    (3, 1)
                } else {
                    (2, 0)
                };
                node.tag.make_mut().start = node.tag.start.saturating_sub(s);
                node.tag.make_mut().end += e;
            }
            _ => (),
        }
    }

    // sort the nodes into tag.start order
    nodes.sort_unstable_by_key(|n| n.tag.start);

    // rebuild string with colouring applied.
    let mut buf = String::new();
    let mut i = 0;
    for node in &nodes {
        if node.tag.start > i {
            write!(&mut buf, "{}", &line[i..node.tag.start]).ok();
        }

        highlight_node(node, &mut buf);

        i = node.tag.end;
    }

    if i < line.len() {
        write!(&mut buf, "{}", &line[i..]).ok();
    }

    buf
}

fn highlight_node(node: &Node, buf: &mut String) {
    use ogma_ls::completion::NodeType::*;
    let s = node.tag.str();
    let w = match node.ty {
        Command => s.bright_cyan().bold(),
        Type => s.bright_green().underline(),
        Num => s.magenta(),
        Pound => s.bright_red(),
        Var => s.yellow(),
        Flag => s.bright_red(),
        Parameter => s.bright_blue(),
        Field => s.green(),
        Variant => s.bright_magenta().underline(),
        _ => s.white(),
    };
    write!(buf, "{w}").ok();
}

fn highlight_help(printed_error: &str, wsp: &Workspace) -> String {
    use std::fmt::Write;
    enum Stage {
        None,
        InputType,
        Usage,
        Flags,
        Examples,
    }
    let mut buffer = String::with_capacity(printed_error.len());
    let buf = &mut buffer;

    let line_prefix = "\u{1b}[95m | \u{1b}[0m\u{1b}[37m";
    let line_suffix = "\u{1b}[0m";
    let mut stg = Stage::None;
    for line in printed_error.lines() {
        if let Some(x) = line.strip_prefix(line_prefix) {
            // update stage
            if x.starts_with("---- Input Type:") {
                stg = Stage::InputType;
            } else if x.starts_with("Usage:") {
                stg = Stage::Usage;
            } else if x.starts_with("Flags:") {
                stg = Stage::Flags;
            } else if x.starts_with("Examples:") {
                stg = Stage::Examples;
            }

            let empty = x == line_suffix;

            // colour based on stage
            match stg {
                Stage::InputType if !empty => {
                    let s = x.trim_end_matches(line_suffix);
                    stg = Stage::None;
                    writeln!(buf, "{line_prefix}{}", s.bright_blue().bold().underline())
                }
                Stage::Usage if !empty => {
                    let s = x.trim_end_matches(line_suffix);
                    writeln!(buf, "{line_prefix}{}", s.green().bold())
                }
                Stage::Flags if !empty => {
                    let s = x.trim_end_matches(line_suffix);
                    if s.starts_with(" --") {
                        let mut split = s.splitn(2, ':');
                        writeln!(
                            buf,
                            "{line_prefix}{}:{}",
                            split.next().unwrap().red(),
                            split.next().unwrap().white()
                        )
                    } else {
                        writeln!(buf, "{line_prefix}{}", s.red().bold())
                    }
                }
                Stage::Examples if x.starts_with("Examples:") => {
                    let s = x.trim_end_matches(line_suffix);
                    writeln!(buf, "{line_prefix}{}", s.magenta().bold())
                }
                Stage::Examples if x.starts_with(" => ") => {
                    let code = x.trim_start_matches(" => ").trim_end_matches(line_suffix);
                    let s = syntax_highlight(code, wsp);
                    writeln!(buf, "{line_prefix} => {s}{line_suffix}")
                }
                Stage::Examples if !empty => {
                    let s = x.trim_end_matches(line_suffix);
                    writeln!(buf, "{line_prefix}{}", s.yellow())
                }
                _ => writeln!(
                    buf,
                    "{line_prefix}{}",
                    x.trim_end_matches(line_suffix).italic()
                ),
            }
            .ok();
        } else {
            writeln!(buf, "{line}").ok();
        }
    }

    buffer
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn highlighting_test() {
        let wsp = Workspace::init();
        let f = |s| syntax_highlight(s, &wsp);

        assert_eq!(
            f("1-invalid string --foo"),
            format!("{}", "1-invalid string --foo".red().underline())
        );
        assert_eq!(
            f("filter one 2"),
            format!(
                "{} {} {}",
                "filter".bright_cyan().bold(),
                "one".white(),
                "2".magenta()
            )
        );
        assert_eq!(
            f("filter $x --bar   "),
            format!(
                "{} {} {}   ",
                "filter".bright_cyan().bold(),
                "$x".yellow(),
                "--bar".bright_red()
            )
        );
        assert_eq!(
            f("filter --'bar' --\"zog 2\""),
            format!(
                "{} {} {}",
                "filter".bright_cyan().bold(),
                "--'bar'".bright_red(),
                "--\"zog 2\"".bright_red()
            )
        );
        assert_eq!(
            f("def foo-bar Ord (x y) { + $x $y | Ord::Gt }"),
            format!(
                "{} {} {} ({} {}) {{ {} {} {} | {} }}",
                "def".bright_cyan().bold(),
                "foo-bar".bright_cyan().bold(),
                "Ord".bright_green().underline(),
                "x".bright_blue(),
                "y".bright_blue(),
                "+".bright_cyan().bold(),
                "$x".yellow(),
                "$y".yellow(),
                "Ord::Gt".bright_cyan().bold()
            )
        );
        assert_eq!(
            f("def-ty Either :: A | B"),
            format!(
                "{} {} :: {} | {}",
                "def-ty".bright_cyan().bold(),
                "Either".bright_green().underline(),
                "A".bright_magenta().underline(),
                "B".bright_magenta().underline()
            )
        );

        assert_eq!(f("def --list"), "def --list".to_string());
        assert_eq!(f("def --clear"), "def --clear".to_string());
        assert_eq!(f("def --load"), "def --load".to_string());

        assert_eq!(
            f("if #t #i #i"),
            format!(
                "{} {} {} {}",
                "if".bright_cyan().bold(),
                "#t".bright_red(),
                "#i".bright_red(),
                "#i".bright_red(),
            )
        );
    }

    #[test]
    fn help_highlighting_test() {
        let wsp = Workspace::init();
        let hlp_dbg = "\u{1b}[93mHelp\u{1b}[0m\u{1b}[97m: `filter`\u{1b}[0m
\u{1b}[95m--> shell:0\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m---- Input Type: <any> ----\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37mfilter incoming data using a predicate\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37mfilter can be used with a column header and a type flag\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37mfiltering columns is achievable with the --cols flag\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37mUsage:\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m => filter [col-name] <predicate>\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37mFlags:\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m --<type>: only filter entries of type. defaults to Num if not specified\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m --cols: filter columns with predicate. predicate is String -> Bool\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37mExamples:\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m filter ls items greater than 5kB\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m => ls | filter size > 5e3\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m filter ls by extension\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m => ls | filter ext --Str = md\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m filter a table by two columns\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m => \\ table.csv | filter { and { get col-a | > 100 } { get col-b | < 10 } }\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m filter table columns\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m => \\ table.csv | filter --cols or { = \'foo\' } { = bar }\u{1b}[0m
";

        let e = highlight_help(hlp_dbg, &wsp);

        let exp = "\u{1b}[93mHelp\u{1b}[0m\u{1b}[97m: `filter`\u{1b}[0m
\u{1b}[95m--> shell:0\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m\u{1b}[1;4;94m---- Input Type: <any> ----\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m\u{1b}[3mfilter incoming data using a predicate\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m\u{1b}[3mfilter can be used with a column header and a type flag\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m\u{1b}[3mfiltering columns is achievable with the --cols flag\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m\u{1b}[3m\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m\u{1b}[1;32mUsage:\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m\u{1b}[1;32m => filter [col-name] <predicate>\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m\u{1b}[3m\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m\u{1b}[1;31mFlags:\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m\u{1b}[31m --<type>\u{1b}[0m:\u{1b}[37m only filter entries of type. defaults to Num if not specified\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m\u{1b}[31m --cols\u{1b}[0m:\u{1b}[37m filter columns with predicate. predicate is String -> Bool\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m\u{1b}[3m\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m\u{1b}[1;35mExamples:\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m\u{1b}[33m filter ls items greater than 5kB\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m => \u{1b}[1;96mls\u{1b}[0m | \u{1b}[1;96mfilter\u{1b}[0m \u{1b}[37msize\u{1b}[0m \u{1b}[1;96m>\u{1b}[0m \u{1b}[35m5e3\u{1b}[0m\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m\u{1b}[3m\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m\u{1b}[33m filter ls by extension\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m => \u{1b}[1;96mls\u{1b}[0m | \u{1b}[1;96mfilter\u{1b}[0m \u{1b}[37mext\u{1b}[0m \u{1b}[91m--Str\u{1b}[0m \u{1b}[1;96m=\u{1b}[0m \u{1b}[37mmd\u{1b}[0m\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m\u{1b}[3m\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m\u{1b}[33m filter a table by two columns\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m => \u{1b}[1;96m\\\u{1b}[0m \u{1b}[37mtable.csv\u{1b}[0m | \u{1b}[1;96mfilter\u{1b}[0m { \u{1b}[1;96mand\u{1b}[0m { \u{1b}[1;96mget\u{1b}[0m \u{1b}[37mcol-a\u{1b}[0m | \u{1b}[1;96m>\u{1b}[0m \u{1b}[35m100\u{1b}[0m } { \u{1b}[1;96mget\u{1b}[0m \u{1b}[37mcol-b\u{1b}[0m | \u{1b}[1;96m<\u{1b}[0m \u{1b}[35m10\u{1b}[0m } }\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m\u{1b}[3m\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m\u{1b}[33m filter table columns\u{1b}[0m
\u{1b}[95m | \u{1b}[0m\u{1b}[37m => \u{1b}[1;96m\\\u{1b}[0m \u{1b}[37mtable.csv\u{1b}[0m | \u{1b}[1;96mfilter\u{1b}[0m \u{1b}[91m--cols\u{1b}[0m \u{1b}[1;96mor\u{1b}[0m { \u{1b}[1;96m=\u{1b}[0m '\u{1b}[37mfoo\u{1b}[0m' } { \u{1b}[1;96m=\u{1b}[0m \u{1b}[37mbar\u{1b}[0m }\u{1b}[0m
";

        dbg!(&e);
        println!("### EXPECTED ###:\n{exp}");
        println!("### FOUND ###:\n{e}");

        for (a, b) in e.lines().zip(exp.lines()) {
            assert_eq!(a, b);
        }
        assert_eq!(&e, exp);
    }
}

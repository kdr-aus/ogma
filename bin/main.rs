use ::libs::colored::*;
use std::path::{Path, PathBuf};

fn main() {
    use ::clap::{App, Arg};

    let matches = App::new("ogma")
        .author("Kurt Lawrence <kurtlawrence92@gmail.com>")
        .about("Scripting language for manipulating tabular data")
        .arg(
            Arg::with_name("quiet")
                .long("quiet")
                .short("q")
                .takes_value(false)
                .help("suppress progress output"),
        )
        .arg(
            Arg::with_name("def")
                .long("def")
                .takes_value(true)
                .number_of_values(1)
                .multiple(true)
                .help("include definition file. glob syntax is supported"),
        )
        .arg(
            Arg::with_name("FILES")
                .multiple(true)
                .help("files to process. if none specified, a REPL instance is started"),
        )
        .get_matches();

    let defs = expand_globs(matches.values_of("def"), "definition", true);
    let files = expand_globs(matches.values_of("FILES"), "processing", true);
    let verbose = !matches.is_present("quiet");

    if files.is_empty() {
        // run the ogma-shell/REPL since no processing files were given
        run_shell(defs)
    } else {
        if let Err(_) = process_files(defs, files, verbose) {
            std::process::exit(1); // failed
        }
    }
}

fn expand_globs(values: Option<clap::Values>, file_ty: &str, panic_on_empty: bool) -> Vec<PathBuf> {
    let mut defs: Vec<PathBuf> = match values {
        Some(globs) => globs
            .flat_map(|s| {
                let paths = match ::glob::glob(s) {
                    Ok(paths) => paths.map(|r| r.expect("glob path error")),
                    Err(err) => {
                        panic!("could not parse '{}' as a glob pattern: {}", s, err)
                    }
                }
                .collect::<Vec<_>>();

                if paths.is_empty() && panic_on_empty {
                    panic!("could not find any {} files along path '{}'", file_ty, s)
                }

                paths.into_iter()
            })
            .collect::<Vec<_>>(),
        None => Default::default(),
    };

    defs.sort();
    defs.dedup();

    defs
}

fn run_shell(defs: Vec<PathBuf>) {
    let root = Path::new(".")
        .canonicalize()
        .expect("should be able to canonicalize root");
    let title = format!(
        " {} in {} ",
        "ogma".bright_purple(),
        root.display().to_string().green()
    );

    let mut shell = ogma_shell::OgmaShell::init(PathBuf::from(".")).title(title);
    for def in defs {
        shell = shell.defs_file_path(def);
    }

    shell.run().expect("failed running the ogma shell")
}

fn process_files(defs: Vec<PathBuf>, files: Vec<PathBuf>, verbose: bool) -> Result<(), ()> {
    let mut definitions = ogma::Definitions::default();

    // add defs
    for def in defs {
        if let Err(e) = definitions.add_from_file(&def) {
            panic!("failed loading definition file '{}': {}", def.display(), e);
        }
    }

    // turn files into batchs and process

    let batches = files
        .iter()
        .map(|p| {
            ogma::bat::parse_file(p).expect(&format!(
                "failed parsing in '{}' as batch process",
                p.display()
            ))
        })
        .collect::<Vec<_>>();

    for (path, batch) in files.iter().zip(batches) {
        process_and_print_batch(path, &batch, &definitions, verbose)?;
    }

    Ok(())
}

fn process_and_print_batch(
    path: &Path,
    batch: &ogma::bat::Batch,
    defs: &ogma::Definitions,
    verbose: bool,
) -> Result<(), ()> {
    use ogma::bat::Outcome::*;
    use std::io::Write;

    if verbose {
        println!(
            "processing {} items from file '{}'",
            batch.items.len(),
            path.display()
        );
    }

    let dummy = &::libs::divvy::ProgressTx::dummy();
    let defs = defs.clone();
    let p = Path::new(".");
    let outcomes = ogma::bat::process(&batch, p, p, dummy, defs);

    let report = || batch.items.iter().map(|i| (i.line, i.ty()));

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

    let mut errors = false;
    for ((line, ty), err) in report()
        .zip(outcomes.into_iter())
        .filter_map(|(x, o)| match o {
            (Failed(e), _) => Some((x, e)),
            _ => None,
        })
    {
        errors = true;
        writeln!(buf, "--- Error line {} :: {:?} ---", line, ty).ok();
        ogma::print_error(&err, buf).ok();
    }

    let p = String::from_utf8(buffer).expect("all written output should be utf8");

    if errors {
        eprintln!("{}", p);
        return Err(());
    } else if verbose {
        println!("{}", p);
    }

    Ok(())
}

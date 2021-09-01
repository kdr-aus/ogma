use std::path::PathBuf;

fn main() {
    if cfg!(debug_assertions) {
        use simplelog::*;
        let logfile = std::env::current_exe()
            .ok()
            .and_then(|x| x.parent().map(|x| x.to_path_buf()))
            .unwrap_or_default()
            .join("ogma-ls.log");
        let logfile = std::fs::File::create(logfile).unwrap();
        WriteLogger::init(LevelFilter::Trace, Config::default(), logfile).unwrap();
    }

    let paths: Vec<_> = std::env::args().skip(1).map(PathBuf::from).collect();
    ogma_ls::server::run(paths)
}

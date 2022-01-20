use crate::prelude::*;
use ::libs::{colored::*, divvy::ProgressTx};
use ::table::Entry::*;
use ast::*;
use err::*;
use lang::{defs::*, help::*, syntax::parse::expression};
use print::*;
use rt::{bat::*, process_expression};
use std::{iter::*, path::*};
use HelpParameter::*;



fn print_help(src: &str, defs: &Definitions) -> String {
    let x = eng::handle_help(&expression(src, Location::Shell, defs).unwrap(), defs)
        .unwrap_err()
        .to_string();
    println!("{}", x);
    x
}


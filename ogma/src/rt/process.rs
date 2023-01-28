use crate::prelude::*;

/// Parse and evaluate an `expr`, returning the value if successful.
///
/// `root`: The root directory that the ogma instance is evaluating in.
/// `wd`: The working directory that the expression is evaluating in.
///
/// These two paths are important since commands such as `open` and `ls` are relative.
/// There are also security concerns with accessing items _above_ the `root` path, so this is
/// generally disallowed.
pub fn process_expression<I, S>(
    seed: I,
    expr: S,
    loc: ast::Location,
    defs: &Definitions,
    root: &std::path::Path,
    wd: &std::path::Path,
) -> Result<Value>
where
    I: AsType + Into<Value> + 'static,
    S: Into<Arc<str>>,
{
    rt::fscache::ensure_init(root); // initialise the cache

    let expr = lang::syntax::parse::expression(expr, loc, defs).map_err(|e| e.0)?;
    handle_help(&expr, defs)?;
    let eng::FullCompilation { eval_stack, env } = eng::compile(expr, defs, I::as_type())?;
    let cx = eng::Context { root, wd, env };
    let output = eval_stack.eval(seed.into(), cx)?.0;

    Ok(output)
}

/// Check if an expression has a help flag and output the help message (as the `Err` variant).
pub fn handle_help(expr: &ast::Expression, definitions: &Definitions) -> Result<()> {
    if let Some(block) = expr.blocks.get(0) {
        let help_flagged = block
            .terms()
            .iter()
            .any(|x| matches!(x, ast::Term::Flag(f) if f.str() == "help"));

        if help_flagged {
            todo!("understand how the help is retrieved for API use");
            let x = definitions.impls().help(&*block.op())?;
            Err(x)
        } else {
            Ok(())
        }
    } else {
        Ok(())
    }
}

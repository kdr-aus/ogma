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
    eng::handle_help(&expr, defs)?;
    let vars = var::Locals::default();
    let evaluator = eng::construct_evaluator(I::as_type(), expr, defs, vars.clone())?;
    let cx = eng::Context {
        root,
        wd,
        env: var::Environment::new(vars),
    };
    let output = evaluator.eval(seed.into(), cx)?.0;

    Ok(output)
}

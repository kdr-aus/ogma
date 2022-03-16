//! `Def` parameter handling.
//!
//! Parameters come in two flavours;
//! 1. Evaluated at the _callsite_, and
//! 2. Expressions are _lazy_ and resolved when _used_.
//!
//! The handling of these parameters is dichotomous. The **callsite** params must have a variable
//! slot assigned which is _set_ before evaluation of the sub-expression.
//! The **lazy** param should be treated like a regular argument, _except that it points to an
//! argument node **outside** of the regular one_.
//!
//! ## Lazy Params
//! The requirement for lazy parameters to shadow the referencer argument is so that local
//! injection can be valid. For example, passing a filter predicate through a def boundary needs to
//! support the `$row` variable being available for the predicate.
//! With the locals graph, this is possible to inject the variable locally, and even environment
//! capturing seems to fall out this graph implementation (testing to be done...).



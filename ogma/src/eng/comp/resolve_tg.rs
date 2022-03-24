use super::*;

impl<'d> Compiler<'d> {
    pub fn resolve_tg(&mut self) -> Result<()> {
        loop {
            match self.tg.flow_types(&mut self.flowed_edges) {
                Ok(true) => (), // keep going!
                Ok(false) => break Ok(()),
                Err(reserr) => break Err(self.ty_resolution_err(reserr)),
            }
        }
    }

    fn ty_resolution_err(&self, reserr: tygraph::ResolutionError) -> Error {
        use crate::common::err::*;
        use tygraph::{Conflict::*, Flow::*};

        let mut err = Error {
            cat: Category::Type,
            desc: "Type resolution failed".into(),
            ..Default::default()
        };

        let tygraph::ResolutionError {
            from,
            to,
            flow,
            conflict,
        } = reserr;

        let from = self.ag[from].tag();
        let to = self.ag[to].tag();

        match (flow, conflict) {
            (_, UnknownSrc) => {
                err.desc.push_str(". Unknown source type");
                err.traces.push(Trace::from_tag(
                    from,
                    "this node's type is unknown".to_string(),
                ));
            }
            (_, OverpoweringInferred) => {
                err.traces.push(Trace::from_tag(
                    from,
                    "this node is only inferred".to_string(),
                ));
                err.traces.push(Trace::from_tag(
                    to,
                    "but this node is has stronger type garauntees".to_string(),
                ));
                err.help_msg = Error::internal_err_help();
            }
            (flow, ConflictingKnown { src, dst }) => {
                let (from_ty, to_ty) = match flow {
                    II => ("input", "input"),
                    IO => ("input", "output"),
                    OI => ("output", "input"),
                    OO => ("output", "output"),
                };
                let from_trace = match flow {
                    II | IO => Trace::from_tag(
                        from,
                        format!("the source node has a known input type of `{}`", src),
                    ),
                    OI | OO => {
                        Trace::from_tag(from, format!("the source node returns a `{}`", src))
                    }
                };
                let to_trace = match flow {
                    II | IO => Trace::from_tag(
                        to,
                        format!("but the flow target expects a `{}` input", dst),
                    ),
                    OI | OO => Trace::from_tag(
                        to,
                        format!("but the flow target already returns a `{}`", dst),
                    ),
                };

                err.desc += &format!(
                    ". Conflicting source {} into destination {}",
                    from_ty, to_ty
                );
                err.traces.push(from_trace);
                err.traces.push(to_trace);
            }
            (flow, UnmatchedObligation { src, dst }) => {
                let from_trace = match flow {
                    II | IO => Trace::from_tag(from, format!("this node has input type `{}`", src)),
                    OI | OO => Trace::from_tag(from, format!("this node returns a `{}`", src)),
                };
                let to_trace = match flow {
                    II | IO => Trace::from_tag(
                        to,
                        format!("but this node is obliged to use input `{}`", dst),
                    ),
                    OI | OO => {
                        Trace::from_tag(to, format!("but this node is obliged to return `{}`", dst))
                    }
                };

                err.desc.push_str(". Conflicting obligation type");
                err.traces.push(from_trace);
                err.traces.push(to_trace);
            }
            (flow, UnmatchedInferred { src, dst }) => {
                let from_trace = match flow {
                    II | IO => Trace::from_tag(from, format!("this node has input type `{}`", src)),
                    OI | OO => Trace::from_tag(from, format!("this node returns a `{}`", src)),
                };
                let to_trace = match flow {
                    II | IO => Trace::from_tag(
                        to,
                        format!("but this node is inferred to use input `{}`", dst),
                    ),
                    OI | OO => Trace::from_tag(
                        to,
                        format!("but this node is inferred to return `{}`", dst),
                    ),
                };

                err.desc.push_str(". Conflicting inferred type");
                err.traces.push(from_trace);
                err.traces.push(to_trace);
            }
        }

        err
    }

    /// Returns if any of the graphs were altered when applying the changes.
    pub fn apply_graph_chgs<C>(&mut self, chgs: C) -> Result<bool>
    where
        C: Iterator<Item = graphs::Chg>,
    {
        use graphs::Chg::*;

        chgs.map(|c| match c {
            Tg(c) => {
                let node = c.node();
                self.tg.apply_chg(c).map_err(|e| self.conflict_err(node, e))
            }
            Lg(c) => Ok(self.lg.apply_chg(c)),
        })
        .try_fold(false, |a, b| b.map(|b| a | b))
    }

    fn conflict_err(
        &self,
        node: petgraph::prelude::NodeIndex,
        conflict: tygraph::Conflict,
    ) -> Error {
        use crate::common::err::*;
        use tygraph::Conflict::*;

        let mut err = Error {
            cat: Category::Type,
            desc: "Type application failed".into(),
            hard: true, // unrecoverable error, will always have this conflict
            ..Default::default()
        };

        let node = self.ag[node].tag();

        let appliction = match &conflict {
            UnknownSrc => {
                Trace::from_tag(node, "this node's type is specified as unknown".to_string())
            }
            OverpoweringInferred => {
                err.help_msg = Error::internal_err_help();
                Trace::from_tag(
                    node,
                    "trying to apply type inference to already known type".to_string(),
                )
            }
            ConflictingKnown { src, dst: _ }
            | UnmatchedObligation { src, dst: _ }
            | UnmatchedInferred { src, dst: _ } => Trace::from_tag(
                node,
                format!("this node is trying to have a type `{}` applied to it", src),
            ),
        };

        let exists = match conflict {
            UnknownSrc | OverpoweringInferred => None,
            ConflictingKnown { src: _, dst } => Some(Trace::from_tag(
                node,
                format!("but it is already known to use type `{}`", dst),
            )),
            UnmatchedObligation { src: _, dst } => {
                err.help_msg = Some("maybe remove any type annotations".to_string());
                Some(Trace::from_tag(
                    node,
                    format!("but it is already obligated to use type `{}`", dst),
                ))
            }
            UnmatchedInferred { src: _, dst } => Some(Trace::from_tag(
                node,
                format!("but it is already inferred to use type `{}`", dst),
            )),
        };

        err.traces.push(appliction);
        if let Some(e) = exists {
            err.traces.push(e);
        }

        err
    }
}

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
}

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
        use tygraph::{Flow::*, Conflict::*};

        let mut err = Error {
            cat: Category::Type,
            desc: "Type resolution failed".into(),
            ..Default::default()
        };

        let tygraph::ResolutionError { from, to, flow, conflict } = reserr;

        dbg!(&self.ag[from]);
        let from = self.ag[DefNode(from).expr(&self.ag).idx()].tag();
        let to = self.ag[to].tag();

        match (flow, conflict) {
            (_, UnknownSrc) => {
                err.desc.push_str(". Unknown source type");
                err.traces.push(Trace::from_tag(
                    from,
                    "this node's type is unknown".to_string(),
                ));
            }
            (II, ConflictingKnown { src, dst }) => {
                err.desc.push_str(". Conflicting source input into destination input");
                err.traces.push(Trace::from_tag(
                    from,
                    format!("the source node has a known input type of `{}`", src),
                ));
                err.traces.push(Trace::from_tag(
                    to,
                    format!("but the destination node expects a `{}` input", dst),
                ));
            }
            (OO, ConflictingKnown { src, dst }) => {
                err.desc.push_str(". Conflicting source output into destination output");
                err.traces.push(Trace::from_tag(
                    from,
                    format!("the source node returns a `{}`", src),
                ));
                err.traces.push(Trace::from_tag(
                    to,
                    format!("but the flow target already returns a `{}`", dst),
                ));
            }
            (II, UnmatchedObligation { src, dst }) => {
                err.desc.push_str(". Conflicting obligation type");
                err.traces.push(Trace::from_tag(
                    from,
                    format!("this node has type `{}`", src),
                ));
                err.traces.push(Trace::from_tag(
                    to,
                    format!("but this node is obliged to return `{}`", dst),
                ));
            }
            _ => todo!()
        }

        err
    }
}

use super::*;
use lsp_types::{
    Hover, HoverContents, HoverParams, MarkedString, Position, TextDocumentPositionParams, Url,
};

struct HoverCmd(Wsp);

impl LsMethod<HoverParams> for HoverCmd {
    type Output = Option<Hover>;
    type Error = ();

    fn call(&self, params: HoverParams) -> Res<Self::Output, Self::Error> {
        let TextDocumentPositionParams {
            text_document,
            position,
        } = params.text_document_position_params;

        Ok(get_hover(&self.0, &text_document.uri, position))
    }
}

fn get_hover(wsp: &Wsp, uri: &Url, position: Position) -> Option<Hover> {
    let posline = position.line as usize;
    let (line, code) = wsp.get_def_text(uri, posline)?;
    let expr = wsp.parse(&code).ok()?;
    let diff = posline.saturating_sub(line);
    let pos = linech_to_idx(code.lines().nth(diff)?, position.character as usize);
    let pos = code.lines().take(diff).fold(pos, |x, y| x + y.len() + 1);
    let node = expr.node_at_pos(pos)?;

    use NodeType::*;
    let help = match node.ty {
        Command => wsp.impl_help_string(&node.tag),
        Type => wsp.type_help_string(&node.tag),
        _ => None,
    };

    let mut s = doc_header(node.tag.str(), node.ty);

    if let Some(help) = help {
        s = add_doc_body(s, &help);
    }

    Some(Hover {
        contents: HoverContents::Scalar(MarkedString::from_markdown(s)),
        range: None,
    })
}

pub fn register(server: &mut Server, wsp: &Wsp) {
    server.add_method::<lsp_request!("textDocument/hover"), _>(HoverCmd(wsp.clone()));
}

use super::*;
use lsp_types::{
    CompletionItem, CompletionItemKind, CompletionParams, CompletionResponse, Documentation,
    MarkupContent, MarkupKind, Position, Url,
};

struct Completion(Wsp);

impl LsMethod<CompletionParams> for Completion {
    type Output = Option<CompletionResponse>;
    type Error = ();

    fn call(&self, params: CompletionParams) -> Res<Self::Output, Self::Error> {
        let url = params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;
        Ok(get_completions(&self.0, &url, position).map(Into::into))
    }
}

fn get_completions(wsp: &Wsp, url: &Url, position: Position) -> Option<Vec<CompletionItem>> {
    let posline = position.line as usize;
    let (line, code) = wsp.get_def_text(url, posline)?;
    let diff = posline.saturating_sub(line);
    let pos = linech_to_idx(code.lines().nth(diff)?, position.character as usize);
    let pos = code.lines().take(diff).fold(pos, |x, y| x + y.len() + 1);
    let input = &code[..pos];

    let wd = url.to_file_path().ok();
    let wd = wd.as_ref().and_then(|x| x.parent());
    debug!("working directory: {:?}", wd);

    crate::completion::get(wsp, input, wd).map(|x| x.into_iter().map(def_to_cmpl_item).collect())
}

fn def_to_cmpl_item(def: Def) -> CompletionItem {
    use Kind::*;
    let kind = Some(match def.kind {
        Impl => CompletionItemKind::Function,
        Type => CompletionItemKind::Class,
        Dir => CompletionItemKind::Folder,
        File => CompletionItemKind::File,
        Lit => CompletionItemKind::Constant,
    });

    CompletionItem {
        label: def.name,
        kind,
        documentation: def.doc.map(|d| {
            Documentation::MarkupContent(MarkupContent {
                kind: MarkupKind::Markdown,
                value: d,
            })
        }),
        ..Default::default()
    }
}

pub fn register(server: &mut Server, wsp: &Wsp) {
    server.add_method::<lsp_request!("textDocument/completion"), _>(Completion(wsp.clone()));
}

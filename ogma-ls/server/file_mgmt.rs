use super::*;
use lsp_types::{
    DidChangeTextDocumentParams, DidOpenTextDocumentParams, DidSaveTextDocumentParams,
    TextDocumentItem, VersionedTextDocumentIdentifier,
};

struct DocChanges(Wsp);
impl LsNotify<DidOpenTextDocumentParams> for DocChanges {
    fn call(&self, params: DidOpenTextDocumentParams) {
        let TextDocumentItem {
            uri, version, text, ..
        } = params.text_document;

        let file = File::new(text, version);
        self.0.add_file(uri, file);

        self.0.def_load();
    }
}

impl LsNotify<DidChangeTextDocumentParams> for DocChanges {
    fn call(&self, params: DidChangeTextDocumentParams) {
        let VersionedTextDocumentIdentifier { uri, version } = params.text_document;
        self.0
            .add_file_changes(&uri, version, params.content_changes);
    }
}

impl LsNotify<DidSaveTextDocumentParams> for DocChanges {
    fn call(&self, _: DidSaveTextDocumentParams) {
        self.0.def_load();
    }
}

pub fn register(server: &mut Server, wsp: &Wsp) {
    server.add_notify::<lsp_notification!("textDocument/didOpen"), _>(DocChanges(wsp.clone()));
    server.add_notify::<lsp_notification!("textDocument/didChange"), _>(DocChanges(wsp.clone()));
    server.add_notify::<lsp_notification!("textDocument/didSave"), _>(DocChanges(wsp.clone()));
}

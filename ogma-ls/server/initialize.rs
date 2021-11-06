use super::*;
use lsp_types::{
    CompletionOptions, InitializeError, InitializeParams, InitializeResult, OneOf,
    ServerCapabilities, ServerInfo, TextDocumentSyncKind,
};

struct Initialize;

impl LsMethod<InitializeParams> for Initialize {
    type Output = InitializeResult;
    type Error = InitializeError;

    fn call(&self, _change: InitializeParams) -> Res<Self::Output, Self::Error> {
        Ok(InitializeResult {
            server_info: Some(ServerInfo {
                name: "Ogma language server".into(),
                ..Default::default()
            }),
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncKind::INCREMENTAL.into()),
                completion_provider: Some(CompletionOptions {
                    trigger_characters: Some(vec![" ".into(), "/".into(), "\\".into()]),
                    ..Default::default()
                }),
                hover_provider: Some(true.into()),
                definition_provider: Some(OneOf::Left(true)),
                ..Default::default()
            },
        })
    }

    fn invalid_params(&self) -> Option<Self::Error> {
        Some(InitializeError { retry: false })
    }
}

pub fn register(server: &mut Server) {
    server.add_method::<lsp_request!("initialize"), _>(Initialize)
}

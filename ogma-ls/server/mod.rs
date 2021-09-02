//! Server items.

use super::{add_doc_body, completion::*, doc_header, linech_to_idx, File};
use ::libs::{
    crossbeam::channel::{Receiver, Sender},
    fxhash::FxHashMap as HashMap,
    rayon,
    serde::{Deserialize, Serialize},
    serde_json::{from_value, to_value, Value},
};
use lsp_server::{Connection, Message, Notification, Request, Response};
use lsp_types::{lsp_notification, lsp_request, Url};
use std::{marker::PhantomData, path::PathBuf, sync::Arc};

mod completion;
mod file_mgmt;
mod hover;
mod initialize;

// ###### RUNNING ##############################################################
type Tx = Sender<Message>;
type Rx = Receiver<Message>;
type Wsp = super::Workspace;

/// Run a new `ogma` language server, using the LSP protocol.
pub fn run(def_file_paths: Vec<PathBuf>) {
    let wsp = super::Workspace::init();

    let files = def_file_paths
        .iter()
        .map(|x| x.as_path())
        .filter_map(read_in_file);

    for (url, file) in files {
        wsp.add_file(url, file);
    }

    Server::stdio().init(wsp).run()
}

fn read_in_file(file: &std::path::Path) -> Option<(Url, File)> {
    let file = file.canonicalize().ok()?;
    let text = std::fs::read_to_string(&file).ok()?;
    let url = Url::from_file_path(file).ok()?;
    let file = File::new(text, 0);
    Some((url, file))
}

/// The `ogma` language server, using LSP.
pub struct Server {
    tx: Tx,
    rx: Rx,
    request_handlers: HashMap<&'static str, Arc<dyn RpcRequest>>,
    notifications_handlers: HashMap<&'static str, Arc<dyn RpcNotication>>,
}

impl Server {
    fn stdio() -> Self {
        let (Connection { sender, receiver }, _) = Connection::stdio();
        Self {
            tx: sender,
            rx: receiver,
            request_handlers: HashMap::default(),
            notifications_handlers: HashMap::default(),
        }
    }

    fn init(mut self, wsp: Wsp) -> Self {
        let s = &mut self;
        let wsp = &wsp;

        s.add_method::<lsp_request!("shutdown"), _>(Shutdown);
        s.add_notify::<lsp_notification!("exit"), _>(Exit);

        initialize::register(s);
        file_mgmt::register(s, wsp);
        completion::register(s, wsp);
        hover::register(s, wsp);

        self
    }

    fn add_method<T, U>(&mut self, method: U)
    where
        T: lsp_types::request::Request,
        T::Params: Send + 'static,
        U: LsMethod<T::Params>,
    {
        self.request_handlers
            .insert(T::METHOD, Arc::new(ServerCommand::method(method)));
    }

    fn add_notify<T, U>(&mut self, notify: U)
    where
        T: lsp_types::notification::Notification,
        T::Params: Send + 'static,
        U: LsNotify<T::Params>,
    {
        self.notifications_handlers
            .insert(T::METHOD, Arc::new(ServerCommand::notify(notify)));
    }

    fn run(self) {
        for msg in &self.rx {
            match msg {
                Message::Request(req) => self.handle_req(req),
                Message::Notification(notif) => self.handle_notification(notif),
                _ => (),
            }
        }
    }

    fn handle_req(&self, req: Request) {
        if let Some(f) = self.request_handlers.get(req.method.as_str()) {
            let tx = self.tx.clone();
            let f = Arc::clone(f);
            rayon::spawn(move || {
                let resp = match f.call(req.params) {
                    Ok(result) => Response {
                        id: req.id,
                        result: Some(result),
                        error: None,
                    },
                    Err(err) => Response {
                        id: req.id,
                        result: None,
                        error: Some(err.into()),
                    },
                };
                tx.send(resp.into()).ok();
            });
        } else {
            debug!("request not registered: '{}'", req.method);
        }
    }

    fn handle_notification(&self, notif: Notification) {
        if let Some(f) = self.notifications_handlers.get(notif.method.as_str()) {
            let f = Arc::clone(f);
            rayon::spawn(move || f.call(notif.params));
        } else {
            debug!("notification not registered: '{}'", notif.method);
        }
    }
}

struct ServerError<E> {
    msg: String,
    data: Option<E>,
}

impl<E, D> From<E> for ServerError<D>
where
    E: std::error::Error,
{
    fn from(err: E) -> Self {
        Self {
            msg: err.to_string(),
            data: None,
        }
    }
}

struct Shutdown;
impl LsMethod<()> for Shutdown {
    type Output = ();
    type Error = ();
    fn call(&self, _: ()) -> Res<(), ()> {
        Ok(())
    }
}
struct Exit;
impl LsNotify<()> for Exit {
    fn call(&self, _: ()) {
        std::process::exit(0);
    }
}

// ###### RPC ##################################################################
type Res<T, E> = Result<T, ServerError<E>>;

trait RpcRequest: Send + Sync + 'static {
    fn call(&self, params: Value) -> Result<Value, Error>;
}

trait RpcNotication: Send + Sync + 'static {
    fn call(&self, params: Value);
}

trait LsMethod<P>: Send + Sync + 'static {
    type Output: Serialize;
    type Error: Serialize;

    fn call(&self, params: P) -> Res<Self::Output, Self::Error>;

    fn invalid_params(&self) -> Option<Self::Error> {
        None
    }
}

trait LsNotify<P>: Send + Sync + 'static {
    fn call(&self, params: P);
}

struct Error {
    code: ErrorCode,
    message: String,
    data: Option<Value>,
}

impl From<Error> for lsp_server::ResponseError {
    fn from(err: Error) -> Self {
        Self {
            code: err.code.into(),
            message: err.message,
            data: err.data,
        }
    }
}

enum ErrorCode {
    // ParseError,
    // InvalidRequest,
    // MethodNotFound,
    InvalidParams,
    InternalError,
    // ServerError(i32),
}

impl From<ErrorCode> for i32 {
    fn from(ec: ErrorCode) -> i32 {
        match ec {
            // ErrorCode::ParseError => -32700,
            // ErrorCode::InvalidRequest => -32600,
            // ErrorCode::MethodNotFound => -32601,
            ErrorCode::InvalidParams => -32602,
            ErrorCode::InternalError => -32603,
            // ErrorCode::ServerError(code) => code,
        }
    }
}

struct ServerCommand<T, P>(T, PhantomData<fn(P)>);

impl<T, P> ServerCommand<T, P>
where
    T: LsMethod<P>,
    P: for<'de> Deserialize<'de> + Send + 'static,
{
    fn method(method: T) -> Self {
        ServerCommand(method, PhantomData)
    }
}

impl<T, P> ServerCommand<T, P>
where
    T: LsNotify<P>,
    P: for<'de> Deserialize<'de> + Send + 'static,
{
    fn notify(notify: T) -> Self {
        ServerCommand(notify, PhantomData)
    }
}

impl<T, P> RpcRequest for ServerCommand<T, P>
where
    T: LsMethod<P>,
    P: for<'de> Deserialize<'de> + 'static,
{
    fn call(&self, params: Value) -> Result<Value, Error> {
        let ser_data = |data: Option<_>| {
            data.as_ref()
                .map(|v| to_value(v).expect("error data could not be serialised"))
        };

        match from_value(params) {
            Ok(param) => self
                .0
                .call(param)
                .map(|v| to_value(v).expect("result data could not be serialised"))
                .map_err(|e| Error {
                    code: ErrorCode::InternalError,
                    message: e.msg,
                    data: ser_data(e.data),
                }),
            Err(e) => {
                let data = ser_data(self.0.invalid_params());
                Err(Error {
                    code: ErrorCode::InvalidParams,
                    message: format!("Invalid params: {}", e),
                    data,
                })
            }
        }
    }
}

impl<T, P> RpcNotication for ServerCommand<T, P>
where
    T: LsNotify<P>,
    P: for<'de> Deserialize<'de> + 'static,
{
    fn call(&self, params: Value) {
        from_value(params).map(|param| self.0.call(param)).ok();
    }
}

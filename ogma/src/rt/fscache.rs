//! A filesystem cache system.

use crate::prelude::*;
use crate::Mutex;
use ::libs::parking_lot::Once;
use std::{
    convert::TryFrom,
    error,
    path::{Path, PathBuf},
    result::Result,
    time::{Duration, Instant},
};

::lazy_static::lazy_static! {
    /// The global persistent [`FsCache`].
    pub static ref FSCACHE: FsCache = Default::default();
}

const LIFESPAN: Duration = Duration::from_secs(60 * 3); // 3 minutes
const DEBOUNCE: Duration = Duration::from_millis(5); // 5ms fs watching
static INIT: Once = Once::new();

#[derive(PartialEq, Eq, Hash)]
struct Key(String, Type);
type Value = (Instant, types::Value);
type Map = HashMap<Key, Value>;

/// A filesystem cache which caches the [`Value`] along a _path_.
///
/// This is useful for caching large datasets, usually [`Table`]s which have a non-trival
/// parsing cost.
#[derive(Default)]
pub struct FsCache {
    map: Mutex<Map>,
}

impl Key {
    fn from<T: AsType>(path: &Path) -> Self {
        Key(path_to_str(path), T::as_type())
    }
}

impl FsCache {
    /// Fetch a value from the cache along `path`.
    ///
    /// If a cache hit occurs it resets the use timer to keep this item alive.
    pub fn get<T>(&self, path: &Path) -> Option<T>
    where
        T: AsType,
        T: TryFrom<types::Value>,
    {
        std::thread::sleep(DEBOUNCE * 5); // we sleep for the 5 x debounce duration to give time for the fs watcher to catch up

        let key = Key::from::<T>(path);
        let mut lock = self.map.lock();
        lock.get_mut(&key)
            .map(|x| {
                x.0 = Instant::now();
                x.1.clone()
            })
            .and_then(|x| T::try_from(x).ok())
    }

    /// Insert the value `T` along path.
    pub fn insert<T>(&self, path: &Path, value: T)
    where
        T: AsType,
        T: Into<types::Value>,
    {
        let key = Key::from::<T>(path);
        self.map.lock().insert(key, (Instant::now(), value.into()));
    }

    fn remove_expired(&self, age: Duration) {
        self.map.lock().retain(|_, v| v.0.elapsed() < age);
    }

    fn remove_path_changes<I, P>(&self, paths: I)
    where
        I: Iterator<Item = P>,
        P: AsRef<Path>,
    {
        let paths: HashSet<String> = paths.map(|p| path_to_str(p.as_ref())).collect();
        if !paths.is_empty() {
            self.map.lock().retain(|k, _| !paths.contains(&k.0));
        }
    }
}

/// Ensures the [`FSCACHE`] is initialised.
///
/// Calling this multiple times is safe, once initialised the initialised map will be kept
/// alive.
///
/// # Panics
/// Panics if `root` can not be canonicalized.
pub fn ensure_init(root: &Path) {
    let canon_root = root
        .canonicalize()
        .expect("must be able to canonicalize root");

    INIT.call_once(|| {
        std::thread::Builder::new()
            .name("ogma-fs-cache-cleaner".to_string())
            .spawn(clean_opened_cache_periodically)
            .unwrap();
        std::thread::Builder::new()
            .name("ogma-fs-watcher".to_string())
            .spawn(|| watch_fs(canon_root).expect("failed to start fs watcher"))
            .unwrap();
    });
}

fn path_to_str(path: &Path) -> String {
    path.display().to_string().to_lowercase()
}

fn clean_opened_cache_periodically() {
    loop {
        std::thread::sleep(LIFESPAN);
        FSCACHE.remove_expired(LIFESPAN);
    }
}

fn watch_fs(canon_root: PathBuf) -> Result<(), Box<dyn error::Error>> {
    use ::notify::{DebouncedEvent::*, *};

    // create the mpsc channel to communicate with the file watcher
    let (wsx, wrx) = std::sync::mpsc::channel();
    let mut watcher =
        notify::watcher(wsx, DEBOUNCE).map_err(|e| format!("failed to setup watcher: {}", e))?;

    // spawn a new thread in which we look for events
    let _ = watcher.watch(&canon_root, RecursiveMode::Recursive);

    let mut set = HashSet::default();
    loop {
        std::thread::sleep(DEBOUNCE);
        set.clear();
        for ev in wrx.try_iter() {
            match ev {
                Write(p) | Create(p) | Remove(p) => {
                    set.insert(p);
                }
                Rename(a, b) => {
                    set.insert(a);
                    set.insert(b);
                }
                _ => (),
            }
        }

        let drain = set
            .drain()
            .map(|x| x.strip_prefix(&canon_root).unwrap().to_path_buf());
        FSCACHE.remove_path_changes(drain);
    }
}

//! Source file and related things.

use std::{
    fmt::Debug,
    fs, io,
    path::{Path, PathBuf},
};

use crate::FileId;

/// A source file, mapped in [`SourceMap`].
#[derive(Debug, Clone)]
pub struct SourceFile {
    pub path: PathBuf,
    pub src: String,
    pub fid: FileId,
}

/// An abstraction over a file loader.
pub trait FileLoader: Debug + Send + Sync {
    /// Query the existence of a file.
    fn file_exists(&self, path: &Path) -> bool;

    /// Reads a file as an UTF-8 string.
    fn read_file(&self, path: &Path) -> io::Result<String>;
}

/// [`std::fs`] file loader.
#[derive(Debug)]
pub struct FsFileLoader;

impl FileLoader for FsFileLoader {
    fn file_exists(&self, path: &Path) -> bool {
        path.exists()
    }

    fn read_file(&self, path: &Path) -> io::Result<String> {
        fs::read_to_string(path)
    }
}

const fn assert_sync_send<T: Send + Sync>() {}

/// Maps [`FileId`] to a [`SourceFile`].
#[derive(Debug)]
pub struct SourceMap {
    files: boxcar::Vec<SourceFile>,
    loader: Box<dyn FileLoader>,
}

impl SourceMap {
    /// Create a new source map with the following file loader.
    pub fn new(loader: impl FileLoader + 'static) -> SourceMap {
        assert_sync_send::<SourceMap>();

        SourceMap {
            files: boxcar::Vec::new(),
            loader: Box::new(loader) as Box<dyn FileLoader>,
        }
    }

    /// Tries to register the file in the source map, returns the file id.
    pub fn try_register(&self, path: impl AsRef<Path>) -> io::Result<FileId> {
        let path = path.as_ref();

        let src = self.loader.read_file(path)?;

        let idx = self.files.push_with(|idx| SourceFile {
            path: path.to_path_buf(),
            src,
            fid: FileId::new(idx as u32),
        });

        Ok(FileId::new(idx as u32))
    }

    /// Registers a file in the source map, panics if source map is unable to
    /// lock the files.
    pub fn register(&self, path: impl AsRef<Path>) -> FileId {
        self.try_register(path)
            .expect("failed to register a file in the source map")
    }

    /// Get the path of the given file.
    pub fn get_path(&self, fid: FileId) -> &Path {
        &self
            .files
            .get(fid.as_usize())
            .expect("unknown file in source map")
            .path
    }

    /// Get the source of the given file.
    pub fn get_src(&self, fid: FileId) -> &str {
        &self
            .files
            .get(fid.as_usize())
            .expect("unknown file in source map")
            .src
    }
}

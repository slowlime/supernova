use std::error::Error;
use std::path::{Path, PathBuf};
use std::{fs, io};

use fxhash::FxHashMap;
use thiserror::Error;

use crate::sourcemap::{SourceFile, SourceMap};

pub trait FileLoader {
    fn get_source(&self) -> &SourceMap;
    fn load_builtin_class(
        &mut self,
        class_name: &str,
    ) -> Result<&SourceFile, Box<dyn Error + Send + Sync>>;
    fn load_user_class(
        &mut self,
        class_name: &str,
    ) -> Result<&SourceFile, Box<dyn Error + Send + Sync>>;
    fn load_file(&mut self, path: &Path) -> Result<String, Box<dyn Error + Send + Sync>>;
}

#[derive(Error, Debug)]
pub enum PathFileLoaderError {
    #[error("illegal class name: {0}")]
    IllegalClassName(String),

    #[error("could not load file {}", path.display())]
    LoadFailed { path: PathBuf, source: io::Error },

    #[error("file {} not found", .0.display())]
    FileNotFound(PathBuf),

    #[error("class not found: {0}")]
    ClassNotFound(String),
}

pub trait FileReader {
    fn read_to_string(&mut self, path: &Path) -> io::Result<String>;
}

#[derive(Debug, Default, Clone)]
pub struct FsFileReader;

impl FileReader for FsFileReader {
    fn read_to_string(&mut self, path: &Path) -> io::Result<String> {
        fs::read_to_string(path)
    }
}

pub struct PathFileLoader {
    pub file_reader: Box<dyn FileReader>,
    source_map: SourceMap,
    search_paths: Vec<PathBuf>,

    // maps a class name to its source name
    loaded_classes: FxHashMap<String, String>,
}

impl PathFileLoader {
    pub fn new<R: FileReader + Default + 'static>(search_paths: Vec<PathBuf>) -> Self {
        Self::with_file_reader(search_paths, Box::<R>::default())
    }

    pub fn with_file_reader(search_paths: Vec<PathBuf>, file_reader: Box<dyn FileReader>) -> Self {
        PathFileLoader {
            file_reader,
            source_map: SourceMap::new(),
            search_paths,
            loaded_classes: Default::default(),
        }
    }

    pub fn load_class(&mut self, class_name: &str) -> Result<&SourceFile, PathFileLoaderError> {
        use PathFileLoaderError::*;

        if let Some(source_name) = self.loaded_classes.get(class_name) {
            return Ok(self.source_map.get_by_name(source_name).unwrap());
        }

        if class_name.contains(|c: char| !c.is_ascii_alphanumeric() && c != '_') {
            return Err(IllegalClassName(class_name.to_owned()));
        }

        for search_path in &self.search_paths {
            let mut path = search_path.clone();
            path.push(format!("{}.som", class_name));

            let contents = match self.file_reader.read_to_string(&path) {
                Ok(contents) => contents,
                Err(e) if e.kind() == io::ErrorKind::NotFound => continue,
                Err(e) => return Err(LoadFailed { path, source: e }),
            };

            let source_name = path.into_os_string().to_string_lossy().into_owned();
            let source = self.source_map.add_source(source_name.clone(), contents);
            self.loaded_classes
                .insert(class_name.to_owned(), source_name);

            return Ok(source);
        }

        Err(ClassNotFound(class_name.to_owned()))
    }
}

impl FileLoader for PathFileLoader {
    fn get_source(&self) -> &SourceMap {
        &self.source_map
    }

    fn load_builtin_class(
        &mut self,
        class_name: &str,
    ) -> Result<&SourceFile, Box<dyn Error + Send + Sync>> {
        self.load_class(class_name).map_err(Into::into)
    }

    fn load_user_class(
        &mut self,
        class_name: &str,
    ) -> Result<&SourceFile, Box<dyn Error + Send + Sync>> {
        self.load_class(class_name).map_err(Into::into)
    }

    fn load_file(&mut self, file_path: &Path) -> Result<String, Box<dyn Error + Send + Sync>> {
        use PathFileLoaderError::*;

        for search_path in &self.search_paths {
            let mut path = search_path.clone();
            path.push(file_path);

            match self.file_reader.read_to_string(&path) {
                Ok(contents) => return Ok(contents),
                Err(e) if e.kind() == io::ErrorKind::NotFound => continue,
                Err(e) => return Err(LoadFailed { path, source: e }.into()),
            }
        }

        Err(FileNotFound(file_path.to_path_buf()).into())
    }
}

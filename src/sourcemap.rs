use std::fmt::{Debug, Display};

use ariadne::Source;
use fxhash::FxHashMap;

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SourceId(u32);

impl SourceId {
    pub const UNKNOWN: Self = Self(0);
}

#[derive(Debug, Clone)]
pub struct SourceFile {
    id: SourceId,
    name: String,
    source: Source<String>,
}

impl SourceFile {
    fn new_unknown() -> Self {
        Self {
            id: SourceId::UNKNOWN,
            name: "<unknown>".into(),
            source: String::new().into(),
        }
    }

    pub fn id(&self) -> SourceId {
        self.id
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn source(&self) -> &Source<String> {
        &self.source
    }

    pub fn contents(&self) -> &str {
        self.source.text()
    }
}

#[derive(Debug, Clone)]
pub struct SourceMap {
    files: Vec<SourceFile>,
    file_names: FxHashMap<String, usize>,
}

impl SourceMap {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn add_source(&mut self, name: String, contents: String) -> &SourceFile {
        assert!(
            !self.file_names.contains_key(&name),
            "source `{name}` already added",
        );

        let id = SourceId(self.files.len() as u32);
        let file = SourceFile {
            id,
            name: name.clone(),
            source: contents.into(),
        };

        self.file_names.insert(name, self.files.len());
        self.files.push(file);

        self.files.last().unwrap()
    }

    pub fn get_by_name(&self, name: impl AsRef<str>) -> Option<&SourceFile> {
        self.file_names
            .get(name.as_ref())
            .map(|&idx| &self.files[idx])
    }

    pub fn get_by_id(&self, source_id: SourceId) -> &SourceFile {
        &self.files[source_id.0 as usize]
    }

    pub fn to_cache(&self) -> SourceMapCache<'_> {
        SourceMapCache { source_map: self }
    }
}

impl Default for SourceMap {
    fn default() -> Self {
        Self {
            files: vec![SourceFile::new_unknown()],
            file_names: Default::default(),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct SourceMapCache<'src> {
    source_map: &'src SourceMap,
}

impl ariadne::Cache<SourceId> for SourceMapCache<'_> {
    type Storage = String;

    fn fetch(&mut self, id: &SourceId) -> Result<&Source<String>, Box<dyn Debug + '_>> {
        Ok(self.source_map.files[id.0 as usize].source())
    }

    fn display<'a>(&self, id: &'a SourceId) -> Option<Box<dyn Display + 'a>> {
        Some(Box::new(
            self.source_map.files.get(id.0 as usize)?.name.clone(),
        ))
    }
}

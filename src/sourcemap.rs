use std::fmt::Debug;
use std::ops::Range;

use fxhash::FxHashMap;

use codespan_reporting::files::Error as CodespanError;

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SourceId(u32);

#[derive(Debug, Clone)]
pub struct SourceFile {
    id: SourceId,
    name: String,
    contents: String,
    line_starts: Vec<usize>,
}

impl SourceFile {
    pub fn id(&self) -> SourceId {
        self.id
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn contents(&self) -> &str {
        &self.contents
    }
}

#[derive(Debug, Default, Clone)]
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
        let line_starts = codespan_reporting::files::line_starts(&contents).collect();
        let file = SourceFile {
            id,
            name: name.clone(),
            contents,
            line_starts,
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
}

impl<'a> codespan_reporting::files::Files<'a> for SourceMap {
    type FileId = SourceId;
    type Name = &'a str;
    type Source = &'a str;

    fn name(&'a self, id: Self::FileId) -> Result<Self::Name, CodespanError> {
        Ok(self.get_by_id(id).name())
    }

    fn source(&'a self, id: Self::FileId) -> Result<Self::Source, CodespanError> {
        Ok(self.get_by_id(id).contents())
    }

    fn line_index(&'a self, id: Self::FileId, byte_index: usize) -> Result<usize, CodespanError> {
        Ok(self
            .get_by_id(id)
            .line_starts
            .binary_search(&byte_index)
            .unwrap_or_else(|n| n - 1))
    }

    fn line_range(
        &'a self,
        id: Self::FileId,
        line_index: usize,
    ) -> Result<Range<usize>, CodespanError> {
        let source = self.get_by_id(id);

        let Some(&start) = source.line_starts.get(line_index) else {
            return Err(CodespanError::LineTooLarge {
                given: line_index,
                max: source.line_starts.len() - 1,
            });
        };

        let end = source
            .line_starts
            .get(line_index + 1)
            .copied()
            .unwrap_or(source.contents.len());

        Ok(start..end)
    }
}

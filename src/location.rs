use std::ops::{Range, RangeBounds};

use miette::{SourceOffset, SourceSpan};

use crate::util::try_match;

pub trait Offset: Copy {
    fn offset(self) -> usize;
}

impl Offset for usize {
    fn offset(self) -> usize {
        self
    }
}

impl Offset for SourceOffset {
    fn offset(self) -> usize {
        SourceOffset::offset(&self)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: usize,
    pub len: usize,
}

impl Span {
    pub fn new_with_extent(start: impl Offset, len: usize) -> Self {
        Self {
            start: start.offset(),
            len,
        }
    }

    pub fn new_spanning<T: Offset>(range: impl RangeBounds<T>) -> Self {
        use std::ops::Bound;

        let start = match range.start_bound() {
            Bound::Included(&start) => start.offset(),
            Bound::Excluded(&start) => start.offset() + 1,
            Bound::Unbounded => panic!("span is unbounded"),
        };

        let end = match range.end_bound() {
            Bound::Included(&end) => end.offset() + 1,
            Bound::Excluded(&end) => end.offset(),
            Bound::Unbounded => panic!("span is unbounded"),
        };

        assert!(start <= end, "end offset precedes start offset");

        Self::new_with_extent(start, end - start)
    }

    pub fn start(&self) -> SourceOffset {
        self.start.into()
    }

    pub fn end(&self) -> SourceOffset {
        (self.start + self.len).into()
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn len(&self) -> usize {
        self.len
    }
}

impl From<SourceSpan> for Span {
    fn from(span: SourceSpan) -> Self {
        Self {
            start: span.offset(),
            len: span.len(),
        }
    }
}

impl From<Span> for SourceSpan {
    fn from(span: Span) -> Self {
        Self::new(span.start.into(), span.len.into())
    }
}

impl From<Range<usize>> for Span {
    fn from(range: Range<usize>) -> Self {
        Self::new_spanning(range)
    }
}

impl From<Range<SourceOffset>> for Span {
    fn from(range: Range<SourceOffset>) -> Self {
        Self::new_spanning(range.start.offset()..range.end.offset())
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub enum Location {
    UserCode(Span),

    #[default]
    Builtin,
}

impl Location {
    pub fn span(&self) -> Option<Span> {
        try_match!(*self, Location::UserCode(span) => span)
    }
}

impl From<Location> for Option<SourceSpan> {
    fn from(location: Location) -> Self {
        try_match!(location, Location::UserCode(span) => span.into())
    }
}

impl From<Option<Span>> for Location {
    fn from(span: Option<Span>) -> Self {
        span.map(Into::into).unwrap_or_default()
    }
}

impl From<Span> for Location {
    fn from(span: Span) -> Self {
        Self::UserCode(span)
    }
}

impl From<Range<SourceOffset>> for Location {
    fn from(range: Range<SourceOffset>) -> Self {
        Self::UserCode(range.into())
    }
}

pub trait ConvexHull<Rhs = Self> {
    type Result;

    fn convex_hull(&self, other: &Rhs) -> Self::Result;
}

impl ConvexHull for Span {
    type Result = Span;

    fn convex_hull(&self, other: &Self) -> Self {
        let start = self.start.min(other.start);
        let end = self.end().offset().max(other.end().offset());

        Self::new_spanning(start..end)
    }
}

impl ConvexHull<Location> for Span {
    type Result = Location;

    fn convex_hull(&self, other: &Location) -> Location {
        other.convex_hull(self)
    }
}

impl ConvexHull<Span> for Location {
    type Result = Location;

    fn convex_hull(&self, other: &Span) -> Self {
        self.convex_hull(&Location::from(*other))
    }
}

impl ConvexHull for Location {
    type Result = Location;

    fn convex_hull(&self, other: &Location) -> Location {
        match (self, other) {
            (Location::UserCode(lhs), Location::UserCode(ref rhs)) => {
                Location::UserCode(lhs.convex_hull(rhs))
            }

            _ => Location::Builtin,
        }
    }
}

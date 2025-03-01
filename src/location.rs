use std::cmp::Ordering;
use std::ops::{Range, RangeBounds};

use crate::sourcemap::SourceId;
use crate::util::try_match;

pub trait Offset: Copy {
    fn offset(self) -> u64;
}

impl Offset for usize {
    fn offset(self) -> u64 {
        self as u64
    }
}

impl Offset for u64 {
    fn offset(self) -> u64 {
        self
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span {
    source_id: SourceId,
    start: u64,
    len: u32,
}

impl Span {
    pub fn new_with_extent(source_id: SourceId, start: impl Offset, len: u32) -> Self {
        Self {
            source_id,
            start: start.offset(),
            len,
        }
    }

    pub fn new_spanning<T: Offset>(source_id: SourceId, range: impl RangeBounds<T>) -> Self {
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

        Self::new_with_extent(source_id, start, (end - start).try_into().unwrap())
    }

    pub fn start(&self) -> usize {
        self.start as usize
    }

    pub fn end(&self) -> usize {
        self.start() + self.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn len(&self) -> usize {
        self.len as usize
    }
}

impl ariadne::Span for Span {
    type SourceId = SourceId;

    fn source(&self) -> &SourceId {
        &self.source_id
    }

    fn start(&self) -> usize {
        self.start()
    }

    fn end(&self) -> usize {
        self.end()
    }

    fn len(&self) -> usize {
        self.len()
    }

    fn is_empty(&self) -> bool {
        self.is_empty()
    }
}

impl<I: Offset> From<(SourceId, Range<I>)> for Span {
    fn from((source_id, range): (SourceId, Range<I>)) -> Self {
        Self::new_spanning(source_id, range)
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
        try_match!(*self, Self::UserCode(span) => span)
    }

    pub fn has_span(&self) -> bool {
        matches!(self, Self::UserCode(_))
    }

    pub fn is_builtin(&self) -> bool {
        matches!(self, Self::Builtin)
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

impl<I: Offset> From<(SourceId, Range<I>)> for Location {
    fn from(v: (SourceId, Range<I>)) -> Self {
        Self::UserCode(v.into())
    }
}

impl PartialOrd for Location {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Location {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Self::UserCode(lhs), Self::UserCode(rhs)) => lhs.cmp(rhs),
            (Self::UserCode(_), _) => Ordering::Less,
            (_, Self::UserCode(_)) => Ordering::Greater,
            _ => Ordering::Equal,
        }
    }
}

impl ariadne::Span for Location {
    type SourceId = SourceId;

    fn source(&self) -> &SourceId {
        match self {
            Self::UserCode(span) => span.source(),
            Self::Builtin => &SourceId::UNKNOWN,
        }
    }

    fn start(&self) -> usize {
        self.span().map(|span| span.start()).unwrap_or(0)
    }

    fn end(&self) -> usize {
        self.span().map(|span| span.end()).unwrap_or(0)
    }

    fn len(&self) -> usize {
        self.span().map(|span| span.len()).unwrap_or(0)
    }

    fn is_empty(&self) -> bool {
        self.span().map(|span| span.is_empty()).unwrap_or(true)
    }
}

pub trait ConvexHull<Rhs = Self> {
    type Result;

    fn convex_hull(&self, other: &Rhs) -> Self::Result;
}

impl ConvexHull for Span {
    type Result = Span;

    fn convex_hull(&self, other: &Self) -> Self {
        assert_eq!(self.source_id, other.source_id);
        let start = self.start.min(other.start);
        let end = self.end().offset().max(other.end().offset());

        Self::new_spanning(self.source_id, start..end)
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

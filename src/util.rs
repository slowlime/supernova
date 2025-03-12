use std::fmt::{self, Display};

macro_rules! try_match {
    ($scrutinee:expr, $pattern:pat => $map:expr) => {
        match ($scrutinee) {
            $pattern => Some($map),
            _ => None,
        }
    };
}

pub(crate) use try_match;

pub fn format_list<T: Display>(
    values: &[T],
    conj: &'static str,
    on_empty: &'static str,
) -> impl Display {
    struct ListFormatter<'a, T>(&'a [T], &'static str, &'static str);

    impl<T: Display> Display for ListFormatter<'_, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self.0 {
                [] => self.2.fmt(f),
                [v] => v.fmt(f),
                [lhs, rhs] => write!(f, "{lhs} {} {rhs}", self.1),

                _ => {
                    for (idx, v) in self.0.iter().enumerate() {
                        if idx > 0 {
                            write!(f, ", ")?;
                        }

                        if idx + 1 == self.0.len() {
                            write!(f, "{} ", self.1)?;
                        }

                        write!(f, "{v}")?;
                    }

                    Ok(())
                }
            }
        }
    }

    ListFormatter(values, conj, on_empty)
}

pub fn format_iter<'a, T, I, II>(values: II, conj: &'a str, on_empty: &'a str) -> impl Display
where
    T: Display,
    I: Iterator<Item = T> + Clone,
    II: IntoIterator<Item = T, IntoIter = I>,
{
    struct IterFormatter<'a, I> {
        iter: I,
        conj: &'a str,
        on_empty: &'a str,
    }

    impl<I, T> Display for IterFormatter<'_, I>
    where
        T: Display,
        I: Iterator<Item = T> + Clone,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let mut iter = self.iter.clone();

            let Some(first) = iter.next() else {
                return self.on_empty.fmt(f);
            };

            let Some(second) = iter.next() else {
                return first.fmt(f);
            };

            match iter.next() {
                None => write!(f, "{first} {} {second}", self.conj),

                Some(mut prev) => {
                    write!(f, "{first}, {second}")?;

                    for v in iter {
                        write!(f, ", {prev}")?;
                        prev = v;
                    }

                    write!(f, " {} {prev}", self.conj)
                }
            }
        }
    }

    IterFormatter {
        iter: values.into_iter(),
        conj,
        on_empty,
    }
}

pub trait SliceExt {
    type Item;

    fn zip_all<F>(&self, other: &Self, f: F) -> bool
    where
        F: FnMut(&Self::Item, &Self::Item) -> bool;
}

impl<T> SliceExt for [T] {
    type Item = T;

    fn zip_all<F>(&self, other: &Self, mut f: F) -> bool
    where
        F: FnMut(&Self::Item, &Self::Item) -> bool,
    {
        self.len() == other.len() && self.iter().zip(other).all(|(lhs, rhs)| f(lhs, rhs))
    }
}

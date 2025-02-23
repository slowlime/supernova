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

pub fn format_list<'a, T: Display>(
    values: &'a [T],
    conj: &'static str,
    on_empty: &'static str,
) -> impl Display + use<'a, T> {
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

                        if idx + 1 == self.1.len() {
                            write!(f, "{}", self.1)?;
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

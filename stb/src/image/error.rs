use std::io;
use std::fmt;

macro_rules! impl_error_abbr {
    ($(($func:ident, $ekid:expr)),+ $(,)?) => {
        impl Error {$(
            pub fn $func<E: Into<Box<dyn std::error::Error + Send + Sync>>>(error: E) -> Self {
                Self { kind: $ekid, error: error.into() }
            }
        )+}
    };
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorKind {
    Io,
    Corrupt,
    BadDepth,
    Internal,
    NotSupport,
    OutOfMem,
    Custom,

    BadPngSig,
}

#[derive(Debug)]
pub struct Error {
    kind: ErrorKind,
    error: Box<dyn std::error::Error + Send + Sync>,
}

impl_error_abbr!{
    (io,          ErrorKind::Io),
    (corrupt,     ErrorKind::Corrupt),
    (internal,    ErrorKind::Internal),
    (bad_png_sig, ErrorKind::BadPngSig),
    (bad_depth,   ErrorKind::BadDepth),
    (not_support, ErrorKind::NotSupport),
    (out_of_mem,  ErrorKind::OutOfMem),
    (custom,      ErrorKind::Custom),
}

impl From<io::Error> for Error {
    fn from(error: io::Error) -> Error {
        Self::io(error)
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.error.source()
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}: {}", self.kind, self.error)
    }
}


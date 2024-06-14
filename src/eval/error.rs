#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Error {
    pub message: String,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

#[macro_export]
macro_rules! err {
    ($($arg:tt)*) => {
        EvalResult::Err(Error { message: format!($($arg)*) })
    };
}

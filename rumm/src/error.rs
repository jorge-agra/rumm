use crate::parser::Token;
use annotate_snippets::{snippet::{Snippet, Annotation, AnnotationType, Slice, SourceAnnotation}, display_list::FormatOptions};
use metamath_rs::{diag::{Diagnostic, StmtParseError}, statement::StatementAddress};
use typed_arena::Arena;



// Check if crate "thiserror" would help here?

pub type Result<T = ()> = std::result::Result<T, Error>;

#[derive(Debug)]
pub struct Location {
    pub filename: String,
    pub line: String,
    pub line_number: usize,
    pub start: usize,
    pub end: usize,
}

impl Location {
    fn to_slice<'a>(&self, label: String, arena: &'a Arena<String>) -> Slice<'a> {
        Slice{
            source: arena.alloc(self.line.clone()),
            line_start: self.line_number,
            origin: Some(arena.alloc(self.filename.clone())),
            annotations: vec![SourceAnnotation{
                range: (self.start, self.end),
                label: arena.alloc(label.clone()),
                annotation_type: AnnotationType::Note }],
            fold: true,
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("I/O Error: {0}")]
    IoError(#[from] std::io::Error),
    #[error("Cannot read {0}: {1}")]
    FileError(String, #[source] std::io::Error),
    #[error("Metamath database error(s) while loading {0}:{}", Error::format_mm_err(.1))]
    DBError(String, Vec<(StatementAddress, Diagnostic)>),
    #[error("Metavariables: {0}")]
    MetavariableError(String),
    #[error("Metamath Parse Error ")]
    DBParseError { #[source] error: StmtParseError, location: Location },
    #[error("Lexer Error")]
    MMLexerError { location: Location },
    #[error("While parsing parameters for tactics {1}")]
    TacticsParameterParseError (#[source] Box<Error>, String),
    #[error("While parsing tactics {1}")]
    TacticsParseError (#[source] Box<Error>, String),
    #[error("Parse Error: expected {expected}, found {found}")]
    ParseError { location: Location, expected: String, found: Token },
    #[error("Unexpected end of file: expected {expected}")]
    UnexpectedEndOfFile { location: Location, expected: String },
    #[error("Unknown symbol {symbol}")]
    UnknownSymbol{ location: Location, symbol: String },
    #[error("Unknown label {label}")]
    UnknownLabel{ location: Location, label: String },
    #[error("Unknown tactics name {1}")]
    UnknownTacticsName(Location, String),
}

impl Error {
    pub fn format_mm_err(data: &Vec<(StatementAddress, Diagnostic)>) -> String {
        data.iter().fold(String::new(), |s, (saddr, diag)| format!("{}\n{:?}:{:?}", s, saddr, diag))
    }

    /// The error as one text: where it happened, if it has a place in the source, then the
    /// message of each cause.
    pub fn describe(&self) -> String {
        let mut text = String::new();
        if let Some(location) = self.location() {
            text.push_str(&format!("{}:{}: ", location.filename, location.line_number));
        }
        text.push_str(&self.to_string());
        let mut cause = self.caused_by();
        while let Some(error) = cause {
            text.push_str(&format!(": {}", error));
            cause = error.caused_by();
        }
        text
    }

    pub fn caused_by(&self) -> Option<&Error> {
        match self {
            Error::TacticsParameterParseError(e, _) => Some(&*e),
            Error::TacticsParseError(e, _) => Some(&*e),
            _ => None,
        }
    }

    /// The source location of the error, if it has one. Errors raised outside the Rumm
    /// source (I/O, database diagnostics) carry their file in the message instead.
    fn location(&self) -> Option<&Location> {
        match self {
            Error::IoError(_) => None,
            Error::FileError(_, _) => None,
            Error::DBError(_, _) => None,
            Error::MetavariableError(_) => None,
            Error::DBParseError { location, .. } => Some(location),
            Error::MMLexerError { location } => Some(location),
            Error::TacticsParameterParseError(e, _) => e.location(),
            Error::TacticsParseError(e, _) => e.location(),
            Error::ParseError { location, .. } => Some(location),
            Error::UnexpectedEndOfFile { location, .. } => Some(location),
            Error::UnknownSymbol { location, .. } => Some(location),
            Error::UnknownLabel { location, .. } => Some(location),
            Error::UnknownTacticsName(location, _) => Some(location),
        }
    }

    fn add_slice<'a>(&self, slices: &mut Vec<Slice<'a>>, arena: &'a Arena<String>) {
        if let Some(location) = self.location() {
            slices.push(location.to_slice(format!("{}",self), arena));
        }
        self.caused_by().and_then(|e| Some(e.add_slice(slices, arena)));
    }

    pub fn to_snippet<'a>(&self, arena: &'a Arena<String>) -> Snippet<'a> {
        let mut slices = vec![];
        self.add_slice(&mut slices, arena);
        Snippet {
            title: Some(Annotation{
                id: None,
                label: Some(arena.alloc(format!("{}",self))), 
                annotation_type: AnnotationType::Error,
            }),
            footer: vec![],
            slices,
            opt: FormatOptions {
                color: true,
                ..FormatOptions::default()
            },
        }
    }
}
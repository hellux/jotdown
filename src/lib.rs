mod block;
mod span;
mod tree;

pub use block::parse;
pub use block::Tree;

const EOF: char = '\0';

use span::Span;

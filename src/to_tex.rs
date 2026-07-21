use std::fmt;

use crate::{Expr, SeqOp, Triop};

// impl fmt::Display for Point {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         // Use the write! macro to send text to the formatter target buffer
//         write!(f, "Point({}, {})", self.x, self.y)
//     }
// }

pub fn expr<Metadata>(e: Expr<Metadata>) -> fmt::Result {
    todo!()
}

fn monop<F: FnOnce(&mut fmt::Formatter<'_>) -> fmt::Result>(op: SeqOp, e: F) -> fmt::Result {
    todo!()
}

fn binop<F0: FnOnce(&mut fmt::Formatter<'_>) -> fmt::Result, F1: FnOnce(&mut fmt::Formatter<'_>) -> fmt::Result>(op: SeqOp, e0: String, e1: String) -> fmt::Result {
    todo!()
}

fn triop<F0: FnOnce(&mut fmt::Formatter<'_>) -> fmt::Result, F1: FnOnce(&mut fmt::Formatter<'_>) -> fmt::Result, F2: FnOnce(&mut fmt::Formatter<'_>) -> fmt::Result>(op: Triop, e0: F0, e1: F1, e2: F2) -> fmt::Result {
    todo!()
}

fn finop<F: FnMut(&mut fmt::Formatter<'_>) -> fmt::Result>(op: SeqOp, exprs: F) -> fmt::Result {
    todo!()
}

fn seqop(op: SeqOp) -> fmt::Result { // todo: add parameters
    todo!()
}

#[cfg(test)]
mod tests {
}

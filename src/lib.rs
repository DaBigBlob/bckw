//! A no_std zero-dependency stack machine for Curry's B, C, K, W combinators with support for external effects.

#![no_std]
extern crate alloc;
mod modus;
mod axiom;
use core::fmt::Debug;
use crate::{axiom::Axiom, modus::MStack};

/** Root expression: Hilbert Style axiom schemes and Modus Ponens */
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Expr<Ex> {
    /// Modus ponens (the only rule) application list
    M(MStack<Ex>),
    /// Axiom
    A(Axiom<Ex>)
}
impl <Ex: Debug> Debug for Expr<Ex> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::M(m) => write!(f, "( {:?})", m),
            Self::A(a) => write!(f, "{:?}", a),
        }
    }
}
impl <Ex> Clone for Expr<Ex> { // #[derive(Clone)] needs Ex: Clone
    fn clone(&self) -> Self {
        match self {
            Self::M(arg0) => Self::M(arg0.clone()),
            Self::A(arg0) => Self::A(arg0.clone()),
        }
    }
}
use Expr::*;

impl <Ex> From<Ex> for Expr<Ex> {
    fn from(value: Ex) -> Self { A(Axiom::from(value)) }
}
impl <Ex> From<Axiom<Ex>> for Expr<Ex> {
    fn from(value: Axiom<Ex>) -> Self { A::<Ex>(value) }
}
impl <Ex> From<(Expr<Ex>, Expr<Ex>)> for Expr<Ex> {
    fn from(value: (Expr<Ex>, Expr<Ex>)) -> Self { M(MStack::from(value)) }
}

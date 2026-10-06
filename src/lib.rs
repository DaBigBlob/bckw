//! A no_std zero-dependency stack machine for Curry's B, C, K, W combinators with support for external effects.

#![no_std]
extern crate alloc;
use core::fmt::Debug;
use alloc::vec::Vec;

/** Essentially a stack (backed by Vec) for the underlying stack machine */
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MStack<Ex>(Vec<Expr<Ex>>);
impl <Ex: Debug> Debug for MStack<Ex> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "( ")?;
        self.0.iter().rev().try_for_each(|x| write!(f, "{:?} ", x))?;
        write!(f, ")")
    }
}
impl <Ex> MStack<Ex> {
    pub(crate) const fn new() -> Self { Self(Vec::new()) }
    pub(crate) fn len(&self) -> usize { self.0.len() }
    pub(crate) fn push(mut self, value: Expr<Ex>) -> Self { self.0.push(value); self}
    pub(crate) fn peek(&self) -> Option<&Expr<Ex>> { self.0.last() }
    pub(crate) fn append(mut self, mut other: Self) -> Self { self.0.append(&mut other.0); self }
    pub(crate) fn pop(&mut self) -> Option<Expr<Ex>> { self.0.pop() }
    pub(crate) fn pop3(mut self) -> Result<((Expr<Ex>, Expr<Ex>, Expr<Ex>), Self), Self> {
        if self.len() < 3 { return Err(self) } // restore and return
        let (f, x, y) = match (self.pop(), self.pop(), self.pop()) {
            ( Some(f), Some(x), Some(y)) => (f, x, y),
            _ => unreachable!("we have checked 3")
        };
        Ok(((f, x, y), self))
    }
    pub(crate) fn pop4(mut self) -> Result<((Expr<Ex>, Expr<Ex>, Expr<Ex>, Expr<Ex>), Self), Self> {
        if self.len() < 4 { return Err(self) } // restore and return
        let (f, x, y, z) = match (self.pop(), self.pop(), self.pop(), self.pop()) {
            (Some(f), Some(x), Some(y), Some(z)) => (f, x, y, z),
            _ => unreachable!("we have checked 4")
        };
        Ok(((f, x, y, z), self))
    }
}
impl <Ex> From<(Expr<Ex>, Expr<Ex>)> for MStack<Ex> {
    fn from((f, x): (Expr<Ex>, Expr<Ex>)) -> Self { Self::new().push(x).push(f) }
}

/** Signature of External axiom.
 * The implementer may want to implement the Eq trait.
 */
pub trait ExtAxiom: Sized {
    /// Receives remaining stack excluding this axiom.
    ///
    /// Must return original arguments intact (but ExtAxiom allowed to have internal mutation).
    fn call(&mut self, args: MStack<Self>) -> Result<MStack<Self>, MStack<Self>>;
}

/** Root expression: Hilbert Style axiom schemes and Modus Ponens */
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Expr<Ex> {
    /// Modus ponens (the only rule) application list
    M(MStack<Ex>),
    /// axiom
    A(Axiom<Ex>)
}
use Expr::*;
impl <Ex: ExtAxiom> From<Ex> for Expr<Ex> {
    fn from(value: Ex) -> Self { A(E(value)) }
}
impl <Ex> From<Axiom<Ex>> for Expr<Ex> {
    fn from(value: Axiom<Ex>) -> Self { A::<Ex>(value) }
}
impl <Ex> From<(Expr<Ex>, Expr<Ex>)> for Expr<Ex> {
    fn from(value: (Expr<Ex>, Expr<Ex>)) -> Self { M(MStack::from(value)) }
}

/** Hilbert Style axiom schemes */
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Axiom<Ex> {
    /** B x y z = x (y z) */B, /** C x y z = x z y */ C,
    /** K x y = x */        K,  /** W x y = x y y */  W,
    /// External axiom; effect (including on the entire stack).
    E(Ex)
}
use Axiom::*;
impl <Ex: Debug> Debug for Axiom<Ex> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            B => write!(f, "B"), C => write!(f, "C"),
            K => write!(f, "K"), W => write!(f, "W"),
            E(ex) => write!(f, "<{:?}>", ex),
        }
    }
}
impl <Ex: ExtAxiom> From<Ex> for Axiom<Ex> {
    fn from(value: Ex) -> Self { E(value) }
}

impl <Ex: ExtAxiom + Clone> MStack<Ex> {
    /// Normalize to 1 Expression or failed application
    pub fn norm(mut self) -> Result<Expr<Ex>, Self> {
        loop {
            match self.modus_ponens() {
                Ok(nx) => { self = nx },
                Err(mut x) => return if x.len() == 1 {
                    match x.pop() {
                        Some(exp) => Ok(exp),
                        None => unreachable!("checked len == 1"),
                    }
                } else { Err(x) },
            }
        }
    }
    /// 1 step of normalization
    pub fn modus_ponens(mut self) -> Result<Self, Self> { // Err => same
        match self.peek() {
            Some(fst) => match fst {
                M(_) => match self.pop() {
                    Some(M(modus)) => Ok(self.append(modus)), // ((a...) b...) => (a... b...),
                    _ => unreachable!("re-match after ownership"),
                }, // recur till 1 norm
                A(axiom) => match axiom {
                    B => {
                        match self.pop4() {
                            Ok(((_, x, y, z), ss)) => Ok(ss.push(Expr::from((x, Expr::from((y, z)))))),
                            Err(slf) => Err(slf),
                        }
                    },
                    C => {
                        match self.pop4() {
                            Ok(((_, x, y, z), ss)) => Ok(ss.push(Expr::from((Expr::from((x, z)), y)))),
                            Err(slf) => Err(slf),
                        }
                    },
                    K => {
                        match self.pop3() {
                            Ok(((_, x, _), ss)) => Ok(ss.push(x)),
                            Err(slf) => Err(slf),
                        }
                    },
                    W => {
                        match self.pop3() {
                            Ok(((_, x, y), ss)) => Ok(ss.push(Expr::from((Expr::from((x, y.clone())), y)))),
                            Err(slf) => Err(slf),
                        }
                    },
                    E(_) => match self.pop() {
                        Some(A(E(mut eff))) => match eff.call(self) {
                            Ok(next) => Ok(next),
                            Err(rest) => Err(rest.push(A(E(eff)))),
                        },
                        _ => unreachable!("re-match after ownership"),
                    },
                },
            },
            None => Err(self),
        }
    }
}

//! A no_std zero-dependency stack machine for B, C, K, W combinators with external effects.

#![no_std]
extern crate alloc;
use core::fmt::Debug;
use alloc::vec::Vec;

macro_rules! unreachable_fast {
    ($($arg:tt)*) => {{
        #[cfg(debug_assertions)]
        { unreachable!($($arg)*) }

        #[cfg(not(debug_assertions))]
        // SAFETY: each call site proves unreachable.
        unsafe { core::hint::unreachable_unchecked() }
    }};
}

/** Essentially a stack (backed by Vec) for the underlying stack machine */
#[derive(Clone)]
pub struct MStack(Vec<Expr>);
impl Debug for MStack {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "( ")?;
        self.0.iter().rev().try_for_each(|x| write!(f, "{:?} ", x))?;
        write!(f, ")")
    }
}
impl MStack {
    pub(crate) const fn new() -> Self { Self(Vec::new()) }
    pub(crate) fn len(&self) -> usize { self.0.len() }
    pub(crate) fn push(mut self, value: Expr) -> Self { self.0.push(value); self}
    pub(crate) fn peek(&self) -> Option<&Expr> { self.0.last() }
    pub(crate) fn append(mut self, mut other: Self) -> Self { self.0.append(&mut other.0); self }
    pub(crate) fn pop(&mut self) -> Option<Expr> { self.0.pop() }
    pub(crate) fn pop3(mut self) -> Result<((Expr, Expr, Expr), Self), Self> {
        if self.len() < 3 { return Err(self) } // restore and return
        let (f, x, y) = match (self.pop(), self.pop(), self.pop()) {
            ( Some(f), Some(x), Some(y)) => (f, x, y),
            _ => unreachable!("we have checked 3")
        };
        Ok(((f, x, y), self))
    }
    pub(crate) fn pop4(mut self) -> Result<((Expr, Expr, Expr, Expr), Self), Self> {
        if self.len() < 4 { return Err(self) } // restore and return
        let (f, x, y, z) = match (self.pop(), self.pop(), self.pop(), self.pop()) {
            (Some(f), Some(x), Some(y), Some(z)) => (f, x, y, z),
            _ => unreachable!("we have checked 4")
        };
        Ok(((f, x, y, z), self))
    }
}
impl From<(Expr, Expr)> for MStack {
    fn from((f, x): (Expr, Expr)) -> Self { Self::new().push(x).push(f) }
}

/** Signature of External axiom.
 * Must guarantee: Err ==> unchanged
*/
pub type ExternalAxiom = fn(MStack) -> Result<MStack, MStack>;

/** Root expression: Hilbert Style axiom schemes and Modus Ponens */
#[derive(Clone, Debug)]
pub enum Expr {
    /// Modus ponens (the only rule) application list
    M(MStack),
    /// axiom
    A(Axiom)
}
use Expr::*;
impl From<ExternalAxiom> for Expr {
    fn from(value: ExternalAxiom) -> Self { A(E(value)) }
}
impl From<Axiom> for Expr {
    fn from(value: Axiom) -> Self { A(value) }
}
impl From<(Expr, Expr)> for Expr {
    fn from(value: (Expr, Expr)) -> Self { M(MStack::from(value)) }
}

/** Hilbert Style axiom schemes */
#[derive(Clone)]
pub enum Axiom {
    /** B x y z = x (y z) */B, /** C x y z = x z y */ C,
    /** K x y = x */        K,  /** W x y = x y y */  W,
    /// External axiom; effect (including on the entire stack).
    E(ExternalAxiom)
}
use Axiom::*;
impl Debug for Axiom {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            B => write!(f, "B"), C => write!(f, "C"),
            K => write!(f, "K"), W => write!(f, "W"),
            E(fun) => write!(f, "<{:p}>", *fun),
        }
    }
}
impl From<ExternalAxiom> for Axiom {
    fn from(value: ExternalAxiom) -> Self { E(value) }
}

impl MStack {
    /// Normalize to 1 Expression or failed application
    pub fn norm(mut self) -> Result<Expr, Self> {
        loop {
            match self.modus_ponens() {
                Ok(nx) => { self = nx },
                Err(mut x) => return if x.len() == 1 {
                    match x.pop() {
                        Some(exp) => Ok(exp),
                        None => unreachable!(),
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
                    _ => unreachable_fast!("re-match after ownership"),
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
                        Some(A(E(eff))) => match eff(self) {
                            Ok(next) => Ok(next),
                            Err(rest) => Err(rest.push(A(E(eff)))),
                        },
                        _ => unreachable_fast!("re-match after ownership"),
                    },
                },
            },
            None => Err(self),
        }
    }
}

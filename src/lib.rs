//! A no_std zero-dependency stack machine for Curry's B, C, K, W combinators with support for external effects.

#![no_std]
extern crate alloc;
use core::fmt::Debug;
use alloc::{rc::Rc, vec::Vec};

/** External axiom trait.*/
///
/// NOTE: This object is kept behind Rc so will never be cloned by the runtime,
/// and if dropped, will never be reused.
pub trait ExtAxiom: Sized {
    /// Receives remaining stack excluding this axiom.
    ///
    /// Must return original arguments intact on Err.
    ///
    /// NOTE: Implementations must regard arguments in their Beta Equivalency classes.
    fn call(&self, args: MStack<Self>) -> Result<MStack<Self>, MStack<Self>>;
}

/** Root expression: Hilbert Style axiom schemes and Modus Ponens */
#[derive(PartialEq, Eq, Hash)]
pub enum Expr<Ex> {
    /// Modus ponens (the only rule) application list
    M(MStack<Ex>),
    /** Axiom: B x y z = x (y z) */ B,  /** Axiom: C x y z = x z y */ C,
    /** Axiom: K x y = x */         K,  /** Axiom: W x y = x y y */   W,
    /// External axiom/variable; may have effects.
    E(Rc<Ex>) // Single threaded so Arc not needed
}
use Expr::*;
impl <Ex: Debug> Debug for Expr<Ex> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            M(m) => write!(f, "( {:?})", m),
            B => write!(f, "B"), C => write!(f, "C"),
            K => write!(f, "K"), W => write!(f, "W"),
            E(ex) => write!(f, "#[{:?}]", ex)
        }
    }
}
impl <Ex> Clone for Expr<Ex> {
    fn clone(&self) -> Self {
        match self {
            M(arg0) => M(arg0.clone()),
            B => B, C => C, K => K, W => W,
            E(arg0) => E(arg0.clone()),
        }
    }
}
impl <Ex> From<(Expr<Ex>, Expr<Ex>)> for Expr<Ex> {
    fn from(value: (Expr<Ex>, Expr<Ex>)) -> Self { M(MStack::from(value)) }
}
impl <Ex: ExtAxiom> From<Ex> for Expr<Ex> {
    fn from(value: Ex) -> Self { E(Rc::new(value)) }
}

/** Essentially a stack (backed by Vec) for the underlying stack machine
 * Implemented functions behave how they are named (and typed).
 */
#[derive(PartialEq, Eq, Hash)]
pub struct MStack<Ex>(Vec<Expr<Ex>>);
impl <Ex: Debug> Debug for MStack<Ex> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.0.iter().rev().try_for_each(|x| write!(f, "{:?} ", x))
    }
}
impl <Ex> Clone for MStack<Ex> { // #[derive(Clone)] needs Ex: Clone
    fn clone(&self) -> Self { Self(self.0.clone()) }
}
impl <Ex> MStack<Ex> {
    pub const fn new() -> Self { Self(Vec::new()) }
    pub fn len(&self) -> usize { self.0.len() }
    pub fn push(mut self, value: Expr<Ex>) -> Self { self.0.push(value); self}
    pub fn peek(&self) -> Option<&Expr<Ex>> { self.0.last() }
    pub fn append(mut self, mut other: Self) -> Self { self.0.append(&mut other.0); self }
    pub fn pop(mut self) -> Result<(Expr<Ex>, Self), Self> {
        match self.0.pop() {
            Some(exp) => Ok((exp, self)),
            None => Err(self),
        }
    }
}
impl <Ex> From<(Expr<Ex>, Expr<Ex>)> for MStack<Ex> {
    fn from((f, x): (Expr<Ex>, Expr<Ex>)) -> Self { Self::new().push(x).push(f) }
}
impl <Ex: ExtAxiom> MStack<Ex> {
    /// Normalize to 1 Expression or failed application
    pub fn norm(mut self) -> Result<Expr<Ex>, Self> {
        loop {
            match self.modus_ponens() {
                Ok(nx) => { self = nx },
                Err(x) => return if x.len() == 1 {
                    match x.pop() {
                        Ok((exp, _)) =>  Ok(exp),
                        _ => unreachable!("checked len == 1"),
                    }
                } else { Err(x) },
            }
        }
    }
    /// 1 step of normalization (WK = I is considered 1 step)
    pub fn modus_ponens(self) -> Result<Self, Self> { // Err => same
        match self.peek() {
            Some(fst) => match fst {
                M(_) => match self.pop() {
                    Ok((M(modus), xs)) => Ok(xs.append(modus)), // ((a...) b...) => (a... b...),
                    _ => unreachable!("re-match after ownership"),
                },
                B => {
                    if self.len() < 4 { return Err(self);}
                    let (x, xs) = self.pop()?.1.pop()?;
                    let (y, ys) = xs.pop()?;
                    let (z, zs) = ys.pop()?;
                    Ok(zs.push(Expr::from((x, Expr::from((y, z))))))
                },
                C => {
                    if self.len() < 4 { return Err(self);}
                    let (x, xs) = self.pop()?.1.pop()?;
                    let (y, ys) = xs.pop()?;
                    let (z, zs) = ys.pop()?;
                    Ok(zs.push(Expr::from((Expr::from((x, z)), y))))
                },
                K => {
                    if self.len() < 3 { return Err(self);}
                    let (x, xs) = self.pop()?.1.pop()?;
                    let (_, ys) = xs.pop()?;
                    Ok(ys.push(x))
                },
                W => {
                    if self.len() < 3 { return Err(self);}
                    let (x, xs) = self.pop()?.1.pop()?;
                    match x {
                        K => Ok(xs), // WK = I optimization
                        _ => {
                            let (y, ys) = xs.pop()?;
                            Ok(ys.push(Expr::from((Expr::from((x, y.clone())), y))))
                        },
                    }
                },
                E(_) => match self.pop() {
                    Ok((E(eff), xs)) => match eff.call(xs) {
                        Ok(next) => Ok(next),
                        Err(rest) => Err(rest.push(E(eff))),
                    },
                    _ => unreachable!("re-match after ownership"),
                },
            },
            None => Err(self),
        }
    }
}

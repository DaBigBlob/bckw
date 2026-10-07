use core::fmt::Debug;
use alloc::rc::Rc;
use crate::modus::MStack;

/** Curry's combinators (axioms) with effect */
#[derive(PartialEq, Eq, Hash)]
pub enum Axiom<Ex> {
    /** B x y z = x (y z) */B, /** C x y z = x z y */ C,
    /** K x y = x */        K,  /** W x y = x y y */  W,
    /// External axiom; effect (including on the entire stack).
    E(Rc<Ex>) // Single threaded so Arc not needed
}

use Axiom::*;

impl <Ex: Debug> Debug for Axiom<Ex> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            B => write!(f, "B"), C => write!(f, "C"),
            K => write!(f, "K"), W => write!(f, "W"),
            E(ex) => write!(f, "#\"{:?}\"", ex),
        }
    }
}
impl <Ex> Clone for Axiom<Ex> { // #[derive(Clone)] needs Ex: Clone
    fn clone(&self) -> Self {
        match self {
            Self::B => Self::B, Self::C => Self::C,
            Self::K => Self::K, Self::W => Self::W,
            Self::E(arg0) => Self::E(arg0.clone()),
        }
    }
}
impl <Ex> From<Ex> for Axiom<Ex> {
    fn from(value: Ex) -> Self { E(Rc::new(value)) }
}

/** Signature of External axiom.*/
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

# BCKW
A tiny no_std zero-dependency stack machine for Curry's B, C, K, W combinators with support for external effects.

- Freestanding (no_std): does not depend on system libraries.
- Zero dependency.
- Computationally complete: every closed untyped lambda term can be translated into BCKW using bracket abstraction. (Also implements WK = I optimization.)
- Iterative reduction: uses an explicit stack.

Every line of code in this Crate was written by hand (no generative AI used).

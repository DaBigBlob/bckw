# BCKWE
A no_std zero-dependency stack machine for Curry's B, C, K, W combinators with support for external effects.

- Freestanding (no_std): does not depend on system libraries.
- Zero dependency.
- Ridiculously tiny: under 150 LOC and 1 file.
- Computationally complete: every closed untyped lambda term can be translated into BCKW using bracket abstraction. (Also implements WK = I optimization.)
- Iterative reduction: uses an explicit stack.

#### Every Line of Code in This Crate Was Written by (My) Hand

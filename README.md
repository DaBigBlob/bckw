# BCKWE
A no_std zero-dependency stack machine for Curry's B, C, K, W combinators with external effects.

- Freestanding (no_std): does not depend on system libraries.
- Zero dependency.
- Ridiculously tiny: 136 LOC in a single file.
- Computationally complete: every closed untyped lambda term can be translated into BCKW using bracket abstraction.
- Iterative reduction: uses an explicit stack.

#### Every Line of Code in This Crate Was Written by (My) Hand

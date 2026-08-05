# Canonical gap ancestry realization bridge

This note accompanies `RHLean/Proof/CanonicalGapAncestryBridge.lean`.

The module closes the finite realization and termination obligations left after
`CanonicalGapAncestryFlow.lean`:

- canonical cores are defined directly by squarefreeness, coprimality, and their
  prime-divisor bound below the distinguished prime;
- every smooth-oriented core has a unique parent obtained by stripping its
  largest prime factor;
- the parent remains admissible, has strictly smaller core rank, and carries the
  opposite Möbius sign;
- bounded core flows are nilpotent and therefore have a tail-free finite
  alternating renewal expansion;
- the expansion is pushed through the actual `Nat.sqrt` entry clock;
- the induced square-block increments telescope exactly to the canonical source
  prefix.

No analytic energy estimate is asserted. The remaining open theorem is the
square-root-scale prefix-energy estimate for the resulting finite alternating
flow after the already-controlled low-imbalance contribution is removed.

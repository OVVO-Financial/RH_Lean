# Centered signed K2 theorem

This package records the theorem uncovered by the RH_Lean signed second-Selberg experiments:

\[
\sum_{n\le N}\frac{(\Lambda*\Lambda)(n)-\Lambda(n)\log n}{n}
=-2\gamma\log N+4\gamma^2+6\gamma_1+o(1).
\]

The repository's role was discovery: its exact signed K2 divisor identity, reciprocal Fubini coordinate, and factor-four experiments exposed the hidden centering. The proof itself is classical analytic number theory.

Files in this branch:

- `research/K2_CENTERED_CLASSICAL_PROOF_COMPLETE.md` — complete mathematical proof.
- `RHLean/Analysis/K2CenteredFinite.lean` — finite Abel and hyperbola core, with no new analytic axiom.
- `RHLean/Analysis/K2CenteredClassicalInterface.lean` — explicit analytic interface, with no hidden axiom.
- `research/STRONG_PNT_CLOSURE_ROUTE.md` — preferred route to an end-to-end checked Lean theorem using the already-formalized strong PNT for `psi`.
- `research/K2_LEAN_FORMALIZATION_STATUS.md` — formal audit and current limitation.

The branch deliberately distinguishes mathematical completion from end-to-end machine verification. The finite core is written as Lean source; the remaining analytic bridge is documented explicitly rather than represented as a theorem whose proof has not been checked.

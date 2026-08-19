# External formal sources used for the K2 closure plan

This note records the external Lean sources consulted while isolating the analytic closure.

## Strong PNT

The public `math-inc/strongpnt` development contains a Lean formalization of a de la Vallée Poussin type strong prime number theorem for Chebyshev's `psi`. Its source is organized around the zeta logarithmic derivative, a zero-free region, and the final strong estimate.

Relevant files include:

- `StrongPNT/PNT2_LogDerivative.lean`
- `StrongPNT/PNT3_RiemannZeta.lean`
- `StrongPNT/PNT4_ZeroFreeRegion.lean`
- `StrongPNT/PNT5_Strong.lean`
- `StrongPNT/ZetaZeroFree.lean`

The package depends on `PrimeNumberTheoremAnd` and Mathlib.

## Mathlib zeta asymptotics

Mathlib's `Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean` already provides the near-one regularization

\[
\zeta(s)=(s-1)^{-1}\zeta_1(s),
\qquad
\zeta_1(1)=1,
\qquad
\zeta_1'(1)=\gamma,
\]

and corresponding asymptotics for `1 / zeta` and `zeta' / zeta`. This is enough to identify the Euler-Mascheroni centering coefficient without adding new special-function axioms.

## PrimeNumberTheoremAnd

`PrimeNumberTheoremAnd` supplies Mertens, Abel-summation, L-series, zeta, and prime-number-theorem infrastructure useful for the remaining bridge.

Particularly relevant are:

- `PrimeNumberTheoremAnd/IEANTN/Mertens.lean`
- `PrimeNumberTheoremAnd/Consequences.lean`
- `PrimeNumberTheoremAnd/MediumPNT.lean`
- `PrimeNumberTheoremAnd/StrongPNT.lean`

## Direct sharp-Mertens contour status

A public `ternary-goldbach-lean` file develops the `1 / zeta` contour route for a sharp Mertens estimate, but explicitly marks the decisive shifted-contour bound as unfinished. This branch therefore does not consume that target as if it were a proved theorem.

## AlphaProof Nexus

`google-deepmind/alphaproof-nexus-results` was searched as a secondary proof-pattern corpus. The indexed repository did not expose a directly reusable Riemann-zeta or Abel-summation theorem for this analytic step. It remains useful as a source of general Lean proof patterns, but not as the primary analytic dependency for this result.

# Centered reciprocal signed K2: Lean formalization status

## Current status

This branch separates the result into two layers.

1. `RHLean.Analysis.K2CenteredFinite` contains the finite algebraic core: the discovered K2 hyperbola identity and the two centered Abel transforms.
2. `RHLean.Analysis.K2CenteredClassicalInterface` records the analytic inputs needed to close the theorem without disguising them as axioms.

The accompanying classical proof establishes

\[
\sum_{n\le N}\frac{(\Lambda*\Lambda)(n)-\Lambda(n)\log n}{n}
=-2\gamma\log N+4\gamma^2+6\gamma_1+o(1).
\]

The mathematical argument is complete. The full Lean closure is not yet claimed machine-checked in this branch.

## Why the split is deliberate

The public Lean ecosystem already contains strong analytic ingredients:

- a formal strong prime number theorem with de la Vallée Poussin type decay for `psi`;
- Mathlib's expansion of the Riemann zeta function near `1`, including the Euler-Mascheroni coefficient;
- Abel summation and L-series infrastructure.

However, the public direct sharp-Mertens contour development currently labels its decisive shifted-contour estimate as unfinished. Therefore this branch does not introduce a new axiom or hide that missing contour estimate behind a theorem name.

The preferred formal route is instead to derive the reciprocal Möbius moments from the already formalized strong-PNT input through an explicit summation-by-parts bridge. That route is documented in `research/STRONG_PNT_CLOSURE_ROUTE.md`.

## Finite theorem inventory

`RHLean.Analysis.K2CenteredFinite` defines

- `k2A2`
- `k2C3`
- `k2r`
- `k2H`

and proves

- `k2_abel_Icc_one`
- `k2C3_eq`
- `k2_log_telescope`
- `k2C3_centered_abel`
- `k2F_eq_hyperbola`
- `k2_diff_telescope`
- `k2H_telescope`
- `k2F_centered_abel`

These are finite identities only. They consume the existing RH_Lean signed second-Selberg coordinate but no RH hypothesis.

## Analytic interface

`RHLean.Analysis.K2CenteredClassicalInterface` declares the proposition-valued structure `K2ClassicalMomentInput`, containing exactly the convergence statements needed by the finite proof:

\[
r(N)\to0,
\qquad
r(N)\log N\to0,
\qquad
C_3(N)\to L.
\]

It also records the intended output propositions

- `K2CenteredBounded`
- `K2CenteredConverges`.

The interface is intentionally assumption-explicit. It is not an axiom declaration and it is not presented as the final theorem.

## Exact constant

With

\[
\zeta(1+z)=z^{-1}+\gamma-\gamma_1z+O(z^2),
\]

one obtains

\[
\frac1{\zeta(1+z)}
=z-\gamma z^2+(\gamma^2+\gamma_1)z^3+O(z^4).
\]

Therefore

\[
\sum_{n\ge1}\frac{\mu(n)(\log n)^2}{n}=-2\gamma,
\]

and

\[
\sum_{n\ge1}\frac{\mu(n)(\log n)^3}{n}=-6(\gamma^2+\gamma_1).
\]

The final centered limit is

\[
4\gamma^2+6\gamma_1.
\]

## Acceptance criteria

Before this result is promoted from research closure to a theorem consumed by the main proof path, the Lean development should satisfy both repository criteria:

1. preserve the square-block and prime-wheel chronology by keeping the signed K2 finite coordinate linked to its native source rather than replacing it by an unrelated global theorem;
2. contract the generalized proven PNT bound toward the RH scale by making the improved reciprocal K2 estimate available to the existing endpoint amplification path.

## Validation still required

A compiler session should verify API details in the two new Lean files and then formalize the strong-PNT closure route. No claim of end-to-end machine checking is made until those checks pass.

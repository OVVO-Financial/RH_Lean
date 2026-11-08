# Explicit finite-slot bounds for the original amplification

## Proved statements and their source

Let `N = OAI.SevenEighths.Parameters.explicitSlotCount`. The existing
`exists_explicit_high_data_fine` constructs a fixed, sufficiently fine source
whose every slot length is at least `1 / (12 * N)`. Applying the complete
total-mass endpoint to that same source gives

\[
\beta_{\mathrm{Hecke}}\le\frac78-\frac1{48N}.
\]

The count is specifically defined. With `Delta = 10^(-6)`, `t = 10^(-8)`,
and `h = detectorMesh Delta t`, its definition is equivalently

\[
L=\frac{\min(t,h)}{200},\qquad
N=\left\lceil\max\left(1,\frac1{3L}\right)\right\rceil_{\mathbb N}+2.
\]

The source proves `L > 0` and `N >= 2`. The count is chosen once, independently
of the outer cutoff. Its decimal value is not evaluated in this development.

This composes existing arithmetic theorems. The coefficient `1/4` in the
complete total-mass theorem replaces the older `1/24`, increasing this
particular explicit saving by six. The count is a fixed number of source
slots; the ranges represented by those slots grow with the outer scale.
Cardinality alone is not the lower-bound proof: the constructed lengths
and their checked fineness are essential.

The native Mertens transfer gives

\[
\forall\varepsilon>0\;\exists C_\varepsilon\ge0\;\forall n\ge1:
\quad |M(n)|\le C_\varepsilon n^{7/8-1/(48N)+\varepsilon}.
\]

Spending half the explicit saving gives a fixed power envelope at
`7/8 - 1/(96*N)`. No desired bound, owner hypothesis, or extra zero-free
assumption is introduced.

## Exact historical normalization

All conclusions use the committed objects in
`RHLean/Proof/SquareRootAmplificationLogGrowth.lean`:

\[
K_R=\max_{0\le y<R}\frac{(M(y)-1)^2}{y+1},\qquad
\alpha_R=\frac{(M(R^2-1)-1)^2}{R^2K_R},
\]

\[
\mathcal A(X)=\max_{\substack{R\ge2\\R^2-1\le X}}\alpha_R,
\qquad q(X)=\frac{\log(1+\mathcal A(X))}{\log X}.
\]

The maximum uses its existing zero baseline when the endpoint set is empty.
The lower envelope includes `y=0`, which already proves `K_R >= 1`.
The complex/integer identity `mertensSummatoryInt_cast` identifies the
native analytic Mertens sum with this actual arithmetic source.

The new generic consumer proves, for `b >= 1/2`, `C >= 0`, and a global
integer bound `|M(n)| <= C*n^b`,

\[
\alpha_R\le(C+1)^2(R^2-1)^{2b-1}\quad(R\ge2),
\]

\[
\mathcal A(X)\le(C+1)^2X^{2b-1}\quad(X\ge1),
\]

\[
q(X)\le2b-1+
\frac{\log(1+(C+1)^2)}{\log X}\quad(X\ge2).
\]

The unit subtraction, denominator, and every admitted endpoint are retained.
The constant is chosen before `X`. For any `eta > 0`, the explicit finite
threshold

\[
X\ge\exp\!\left(\frac{\log(1+(C+1)^2)}{\eta}\right),\quad X\ge2
\]

implies `q(X) <= 2*b - 1 + eta`.

## Unconditional amplification conclusions

Combining the new explicit endpoint with that consumer gives

\[
\boxed{\forall\varepsilon>0\;\exists A_\varepsilon>0\;\forall X\ge1:
\quad\mathcal A(X)\le A_\varepsilon
X^{3/4-1/(24N)+\varepsilon}.}
\]

The loss-free fixed power obtained by spending half the Mertens saving is

\[
\boxed{\exists A>0\;\forall X\ge1:
\quad\mathcal A(X)\le AX^{3/4-1/(48N)}.}
\]

The logarithmic consequences are

\[
\forall\varepsilon>0,\quad
q(X)\le\frac34-\frac1{24N}+\varepsilon
\quad\text{for all sufficiently large }X,
\]

\[
\boxed{\limsup_{X\to\infty}q(X)
\le\frac34-\frac1{24N}<\frac34,}
\]

and `A(X) < X` for all sufficiently large natural cutoffs.

The sharper `3/4 - 1/(24*N)` is an every-positive-loss boundary and a limsup
upper bound. The fixed power theorem has exponent `3/4 - 1/(48*N)`.
The development does not assert that the limsup equals its upper bound,
that the original amplification has a single constant upper bound, or that
`q(X)` tends to zero. Those conclusions are stronger than these statements.

## Interpreting the exponents

The Mertens-to-amplification exponent conversion is `b -> 2*b - 1`.
For example, squaring a bound of size `X^(7/8)` and dividing by `X`
gives size `X^(3/4)`. The exponent `3/4` in an amplification conclusion is
therefore not a Mertens exponent of `3/4`.

The exact reverse identity at `X = R^2 - 1` also retains the historical factor:

\[
|M(X)-1|=\sqrt{(X+1)K_R\alpha_R}.
\]

An upper bound on the normalized amplification does not remove `K_R` from
this identity. The new Mertens boundary is `7/8 - 1/(48*N)` with every positive
exponent allowance; its amplification boundary is `3/4 - 1/(24*N)`.

Eventual `A(X) < X` alone does not imply the requested logarithmic limit.
For the example function `F(X) = sqrt(X)`, one has `F(X) < X` for `X > 1`,
but `log(1 + F(X)) / log(X)` tends to `1/2`. The original zero-growth target
requires bounds below every positive power, equivalently

\[
\forall\eta>0\;\exists C_\eta>0\;\forall X\ge1:
\quad\mathcal A(X)\le C_\eta X^\eta.
\]

This PR supplies a particular positive exponent ceiling. It does not supply
the displayed every-positive-power statement.

## Files and verification

- `RHLean/Proof/SquareRootAmplificationPowerBounds.lean`: generic exact
  arithmetic power, log, finite-threshold, and eventual-sublinearity consumers;
  exported through `RHLean.lean`.
- `research/oai_434/VF919ExplicitSlotTotalMass.lean`: explicit finite-slot
  zero boundary and native Mertens consequences.
- `research/oai_434/VF919ExplicitAmplificationBound.lean`: the exact-source
  bridge, unconditional amplification bounds, eventual log bound and limsup.

The dedicated `explicit-slot-amplification.yml` workflow checks the exact PR
head with Lean 4.34.1 and the repository's pinned Mathlib and original OAI
sources. It retains the existing complete total-mass audit unchanged, compiles
the explicit finite-slot source and all new modules with fatal warnings,
checks the committed exact public types and import/export inventory, and audits
all ten unconditional terminals against only `propext`, `Classical.choice`,
and `Quot.sound`. Live proof dependencies must include the explicit source,
the new total-mass theorem, the native Mertens transfer, and the exact integer
and historical-amplification consumers. Compilation status is established by
the corresponding Actions run, not by source generation.

The existing native and original analytic build caches remain source-pinned.
Within the new audit, normalized dependency lists are cached by declaration
name in one fixed imported environment, so the ten terminal checks reuse the
expensive dependency extraction. Every terminal still starts with its own
empty reached set, collects its axioms independently, and executes every
required and forbidden dependency check. The cache contains dependency lists,
not prior audit verdicts.

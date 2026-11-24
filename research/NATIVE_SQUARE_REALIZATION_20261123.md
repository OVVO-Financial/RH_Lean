# Square-clock scalar realization and the simultaneous-family boundary

Date: 2026-11-23. Baseline: `8e5f9b59ebacc022757e13ec6737c272633c13bc`.

## Result

At the native endpoint `x = R² - 1`, the integer choice **m = R** and real
parameter **k = xR** satisfy all four multiplicity/lattice-size fields of
`AlpogeNativeRestSize` on the **same previously selected dyadic host**.
The consumer's existing largeness threshold already suffices. No new
asymptotic threshold, host chooser, or prime-pair selection is required.

This result removes scalar parameter selection from P3. It does not identify
these parameters with measured invariants of an actual recovery/cost object.
P3's simultaneous physical realization, including the retained count and
height conditions, remains open. In particular, this is not a constructed
`AlpogeNativeZetaWindowWitness` and does not supply its `top` field.

The new module is
[`AlpogeNativeSquareMultiplicity.lean`](../RHLean/Analysis/AlpogeNativeSquareMultiplicity.lean).
Its proof text is complete; hosted Lean validation and axiom audit are handled
by the containing PR. No local Lean execution was performed.

## Exact parameter calculation

Let `R ≥ 2`, `x = R² - 1`, and `0 < ε < 1/52`. Then

\[
\sqrt{x}\le R\le2\sqrt{x}.
\]

If `2 ≤ x^(ε/2)`, this gives

\[
x^{1/2-\varepsilon}\le R\le x^{1/2+\varepsilon/2}.
\]

The existing `alpogeNativeLargeX ε C x` includes `x ≥ 3` and
`26 ≤ x^(3ε/8)`. Since `3ε/8 ≤ ε/2`, it already implies the needed
`2 ≤ x^(ε/2)`.

For any host cardinality `n ≥ x`, choose `k = xR`. The lower lattice
inequality is equality. The upper follows from

\[
\begin{aligned}
k=xR
&\le x^{3/2+\varepsilon/2}\\
&\le x^{5/2-\varepsilon}\\
&\le n^2x^{1/2-\varepsilon}.
\end{aligned}
\]

The middle inequality only needs `ε ≤ 2/3`, so the original range
`ε < 1/52` has ample room.

The constructed host's exact cardinality is `n = 2^e`. The original
`PageN ε x e` has lower bound `x^(2+8ε) ≤ 2^e`. Hence `n ≥ x` for
`x ≥ 1`. This argument applies to **every** exponent satisfying `PageN`;
it preserves the exponent selected by `nativeDyadicHost_windows` and the
prime pair used by `nativeConstructedDyadicGzPayment`.

## A necessary restriction on any alternative host

The new theorem `AlpogeNativeRestSize.source_scale_le_host_sq` proves

\[
\boxed{x\le n^2}
\]

from the existing size regime and `x > 0`, without extra density or
positivity assumptions. Indeed,

\[
x\,x^{1/2-\varepsilon}\le xm\le k
\le n^2x^{1/2-\varepsilon},
\]

and the common real power is positive. A fixed small host cannot satisfy
this size regime on arbitrarily large windows. The constructed dyadic host
has sufficient size; a replacement square-block module must retain enough
host capacity or prove a genuinely different normalization and budget.

## Exact remaining inputs of the size supplier

`alpogeNativeSquareMultiplicity_pageN_of_largeX` retains:

* `0 < b`;
* the actual height/cost inequality `aE ≤ 2xb`;
* the actual top count `x^(-ε/8) n / 2 ≤ |TT|`;
* the actual thick density `x^(-ε) ≤ |T2|/n`.

It supplies the other four fields with `m=R`, `k=xR`. The eventual theorem
`alpogeNativeSquareMultiplicity_pageN_eventually` uses exactly
`alpogeNativeLargeXThreshold ε`.

There is no replacement of measured `aE` by a chosen formula, no replacement
of geometric rank by a cardinality, and no assignment of the desired source
bound to a field. The result is intentionally universal in the actual counts
and actual `aE` condition. Selecting the full host as both top and thick set,
or assigning constant heights, would be only a scalar consistency example
until those choices were proved compatible with the recovery maps and global
cost object; that example is not used as a physical supplier here.

## Window and source audit

The attachment's final analytic implication matches the existing source
types, with these requirements retained:

1. `alpogeNativeGz_windows_of_witnesses` first fixes the exponent constant
   `C` and positive admissible `ε₁`; for each desired `η>0` it chooses a
   sufficiently small `ε`. Its source bound is conditional on actual
   witnesses on complete windows.
2. `riemannHypothesis_of_Gz_windows` requires a fixed `δ>0`, then for each
   `η>0` a constant uniform in every point of arbitrarily late windows
   `[Y,Y^(1+δ)]`. Isolated good scales do not satisfy that type.
3. `riemannHypothesis_of_squareClock_Gz_windows` requires every integer
   radius in the corresponding root window. Its interpolation preserves
   the one-sided sign and charges the complete between-square correction.
4. `nativeConstructedDyadicGzPayment` constructs the arithmetic host and
   selected pair, and pays its analytic remainder. The output still
   contains the **literal complete physical top excess divided by Q**.
   It does not estimate that surviving quantity.
5. The constructed payment theorem controls the mean of
   `Gz(a_t/b)`. It requires every selected height to lie in the same
   selected pair's window. Comparing this mean with a prescribed `Gz(x)`
   still requires the actual height localization and its movement charge.
6. The local recovery, IO loss, global capacity, counts, heights, and widths
   must coexist on one family. Separate existence of a good local profile
   and a good global profile does not prove this. A combined average can
   select one profile only after the combined native cost is bounded with
   all necessary signs and nonnegativity conditions.

The finite weighted candidate identity and the complete NNS history retain
proper prime powers and the initial-site correction. No bare prime-count
bound was substituted for this completed arithmetic source.

## Acceptance capsule

```text
descent_payment_ack=ALPOGE_NATIVE_DESCENT_PAYMENT_V1
tractability_ack=ALPOGE_VIOLE_TRACTABLE_RH_V1
SOURCE=native x=R²−1, existing PageN host, unchanged RestSize predicates
SUPPLIERS=alpogeNativeDyadicH_card; PageN lower bound; existing LargeX threshold
CONSTRUCTION=m=R; k=xR, on every existing admissible dyadic host
PROVED_CONTENT=integer multiplicity bounds; lattice parameter bounds; x≤n² necessity
RETAINED_INPUTS=actual top/thick counts, b>0, actual aE bound
FIRST_UNPAID=physical recovery and capacity object realizing those same parameters
FORMAL_STATUS=proof text supplied; containing PR owns hosted Lean/axiom verification
T_C_P=smaller scalar witness burden / elementary reusable restriction / RH open
```

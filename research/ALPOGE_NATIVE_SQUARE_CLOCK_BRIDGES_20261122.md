# Native signed-source bridges on the existing square clock

The active scalar target stays on the native coordinate

\[
X_R=R^2-1,\qquad
G_z(N)=N\sum_{d\le N}\frac{\Lambda(d)}d-\psi(N)
       -N\log N+(1+\gamma)N.
\]

The quantitative input remains **OPEN**:

\[
\forall\eta>0\;\exists C_\eta\ge0,R_\eta\;
\forall R\ge\max(2,R_\eta),\qquad
G_z(R^2-1)\le C_\eta R^{1+\eta}.
\]

The new results below are identities, interpolation estimates, and a conditional
consumer of this input. They do not supply the complete signed-source bound.

## 1. Direct consumer of the native R-coordinate bound

[AlpogeNativeSquareClockCriterion.lean](../RHLean/Analysis/AlpogeNativeSquareClockCriterion.lean)
proves `riemannHypothesis_of_eventual_squareClock_Gz_rpow` from exactly the
eventual bound above. Constants and thresholds may depend on the positive
exponent, but are uniform in the radius. A fixed eventual bound
`Gz(R²-1) ≤ C R` also suffices, by
`riemannHypothesis_of_eventual_squareClock_Gz_linear`.
The stronger absolute `R²` bound is also connected explicitly by
`riemannHypothesis_of_square_lattice_Gz_critical`, using the existing signed
square interpolation theorem before passing to the `R²-1` consumer.

The proof consumes the existing
`riemannHypothesis_of_squareClock_Gz_windows` in
[AlpogeNativeWindowLandau.lean](../RHLean/Analysis/AlpogeNativeWindowLandau.lean).
For `R ≥ 2`, the elementary comparison is

\[
R^{1+2\eta}=(R^2)^{1/2+\eta}
\le 2^{1/2+\eta}(R^2-1)^{1/2+\eta}.
\]

An eventual all-radius estimate supplies every sufficiently late root window.
The existing native square sampler, real-source bridge, and Landau theorem
then give Mathlib's `RiemannHypothesis`. This needs only the one-sided upper
bound on the complete original source. No ordinary-prime sign condition or
new prime-window target is introduced.

## 2. Exact auxiliary prime-power window

[AlpogeNativeDyadicWindow.lean](../RHLean/Analysis/AlpogeNativeDyadicWindow.lean)
defines the genuine finite von Mangoldt sum

\[
W(N)=\sum_{N<d<4N}\Lambda(d)w_N(d),\qquad
w_N(d)=
\begin{cases}
2(1-N/d),&N<d\le2N,\\
4N/d-1,&2N<d<4N,\\
0,&\text{otherwise}.
\end{cases}
\]

For `N ≥ 1`, `nativeAlpogeDyadicDifference_eq_primePowerWindow` proves

\[
-G_z(4N)+3G_z(2N)-2G_z(N)=2N\log2-W(N).
\]

The proof combines the existing reciprocal-Lambda and psi sums on a common
finite cutoff, cancels every old-prefix coefficient, and evaluates the smooth
centering terms. It keeps all prime powers. The exterior endpoint weights are
zero and the middle weight is one. The two multiplier factorizations are
proved as elementary polynomial identities.

This is an auxiliary source identity. Its interval has length `3N`, and the
coefficients `(-1, 3, -2)` are mixed signs. An upper bound on `Gz` cannot be
substituted into all three terms to obtain an upper bound on this difference.
Neither the identity nor its polynomial factorization proves the missing
quantitative cancellation.

## 3. Native integer-to-real interpolation

[AlpogeNativeGzRealInterpolation.lean](../RHLean/Analysis/AlpogeNativeGzRealInterpolation.lean)
works with the existing real source `alpogeNativeGzArithmetic`. Its restriction
to natural arguments is already identified with `nativeAlpogeGz` on main.

On a closed unit cell `x = n + t`, with `n ≥ 1` and `0 ≤ t ≤ 1`, the arithmetic
ramp is affine, including the prime-power endpoint cancellation at `n+1`.
The exact source interpolation has the form

\[
G_z(x)=(1-t)G_z(n)+tG_z(n+1)+J_n(x).
\]

The logarithmic defect has the sufficient, non-sharp bound

\[
0\le J_n(x)\le\frac1n.
\]

Together with the existing native integer increment bound, this gives a
uniform two-sided real/floor interpolation error and transfers an integer
`O(sqrt N)` estimate to a real `O(sqrt x)` estimate without a logarithmic loss.
Writing `L = alpogeGzInterpolationSlope`, the explicit bounds are

\[
|G_z(x)-G_z(\lfloor x\rfloor)|\le L+1\quad(x\ge1),
\]

and, under `|Gz(R²)| ≤ C R` for every integer `R ≥ 2`,

\[
|G_z(x)|\le(2C+4L+1)\sqrt x\quad(x\ge4).
\]

The exported consumers are
`alpogeNativeGzArithmetic_abs_le_of_integer_sqrt_bound_from` and
`alpogeNativeGzArithmetic_abs_le_of_square_lattice_bound`.
The original absolute square-lattice theorem at `R²` remains the existing
result in
[AlpogeSignedSquareInterpolation.lean](../RHLean/Analysis/AlpogeSignedSquareInterpolation.lean).
Its coordinate is distinct from the active one-sided `R²-1` criterion above.

## Verification and scope

The root import manifest includes the new modules. The focused
[terminal-axiom audit](ALPOGE_NATIVE_SQUARE_CLOCK_BRIDGES_AUDIT_20261122.lean)
checks the public proof roots against the standard logical axioms only.
Hosted native Lean compilation, the changed research import closure, source
audits, and declaration-graph checks provide the verification gates.

The proofs use existing RH_Lean and Mathlib declarations. No new external Lean
project, terminal RH theorem, or precompiled artifact is imported. The existing
dependency pins and CI workflows are unchanged.
A checked conditional RH consumer establishes the implication, not its open
quantitative premise. The complete signed geometric and analytic payment
remains the substantive research task.

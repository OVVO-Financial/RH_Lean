# Direct positive moments of the complete native Gz

## Result and remaining estimate

The Landau argument has been factored to accept a weighted positive first
moment of the **complete** native source. The original one-sided logarithmic
window hypothesis also implies this moment hypothesis, with every window
and tail cost accounted for. The existing public window theorem keeps its
original type.

The native Mertens-first estimate supplies an unconditional bound for these
moments at exponent one. The inspected partial-moment and semivariance
suppliers do not yet provide the critical growth rate at exponent
`theta = 1/2 + eta < 1`. The new RH theorem therefore retains that quantitative
moment bound as an explicit hypothesis. This report does not claim RH, a
critical source-bound supplier, or an equivalence between the new moment
hypothesis and a pointwise bound.

This change is based directly on main commit
`fde7ea71ed88f540a8829554a8ab4602bda96f4d`, which includes the human merge
of PR #1205. The new module uses the pre-existing native window and exact
history APIs without requiring the additional handoff module. Lean
verification is performed by the repository's hosted CI;
no local Lean or Lake execution is used.

## Exact observable and centering

For `N >= 1`, put

\[
s_n=\frac{\psi(n)-n}{n(n+1)},\quad
U_N=\sum_{1\le n<N}(s_n)_+,\quad
L_N=\sum_{1\le n<N}(-s_n)_+.
\]

The existing exact history identity, and the new positive-part bridge, give

\[
E_N=U_N-L_N+H_N-\log N+\gamma,\qquad
G_z(N)=NE_N,\qquad (G_z(N))_+=N(E_N)_+.
\]

The new declaration `nativeAlpogeGz_posPart_eq_NNSHistory` keeps all terms
inside the maximum. The source is not replaced by the separate upper mass
`U_N`. The lower mass is subtracted before taking a positive part.

The exponent one half is a target, not a consequence of this definition.
A pointwise bound `G_z(N) <= C N^(1/2+eta)` requires the quantitative estimate

\[
(E_N)_+\le C N^{-1/2+\eta}.
\]

The identity specifies the quantity whose positive remainder must decay;
it does not prove that rate. Nor may the centering simply be discarded:
`H_N - log N + gamma = 2 gamma + e_N`, where the existing future-tail module
proves `0 <= e_N <= 1/N` for
`e_N = H_N - log N - gamma`. Cancellation with the signed history is essential.

At real endpoints the new theorem
`alpogeNativeGzArithmetic_posPart_le_floorHistory` proves

\[
(G_z(x))_+\le
\lfloor x\rfloor(E_{\lfloor x\rfloor})_+
+L\,(x-\lfloor x\rfloor),\qquad x\ge1,
\]

with the already proved nonnegative `nativeAlpogeSafeSlope` as `L`. This
retains the full centered history and pays the floor movement explicitly.

## Direct moment consumed by Landau

For `sigma > 2` and natural `k`, define

\[
P_k(\sigma)=\int_0^\infty
\bigl(G_z(e^u)\bigr)_+\,
\frac{u^k e^{-\sigma u}}{k!}\,du.
\]

The source moment has degree **one**. The index `k` is the order of the
factorial-normalized Laplace kernel; it is not the degree of a power of
the positive source. This kernel has total mass `sigma^(-k-1)` and is not
being described as a probability density.

`weightedPositiveMoment_integrable` proves integrability at every such
`sigma,k` from the existing `PoleData` growth and measurability. For the
actual source these are supplied by
`alpogeNativeGzArithmetic_poleData`. No conclusion uses Lean's value for
a nonintegrable Bochner integral.

For any fixed `0 < theta < 1`, the direct sufficient input is

\[
\exists\sigma>2\;\exists C\ge0\;\forall k_0\in\mathbb N\;
\exists k\ge k_0:\quad
P_k(\sigma)\le \frac C{(\sigma-\theta)^k}.
\]

Both `sigma` and `C` precede the requested order `k_0`. A different
constant at each selected order would not satisfy this condition. Only
arbitrarily large orders are required; all orders are unnecessary.

With `A_k(s)=(-1)^k Phi^(k)(s)/k!`, the new analytic bridge is

\[
|A_k(\sigma+it)|+\Re A_k(\sigma)\le2P_k(\sigma).
\]

It follows from `|g| + g = 2 g_+`, with `g(u)=G_z(exp u)`. The signed
real-axis coefficient is retained, so the negative-source contribution
is compensated. The original nearest-pole contradiction consumes this
joint estimate; it is not replaced by an absolute estimate on each
coefficient separately.

The resulting native declarations are
`riemannZeta_ne_zero_of_nativeGz_positiveMoments` and
`riemannHypothesis_of_nativeGz_positiveMoments`. The latter has the
complete quantitative input

```lean
{η₀ : ℝ} (hη₀ : 0 < η₀)
(hM : ∀ η : ℝ, 0 < η → η < η₀ →
  ∃ σ : ℝ, 2 < σ ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ k₀ : ℕ, ∃ k ≥ k₀,
      alpogeNativeGzPositiveMoment σ k ≤
        C / (σ - (1 / 2 + η)) ^ k) :
RiemannHypothesis
```

The constants can depend on `eta`. The proof chooses a sufficiently small
`eta` for each putative zero to the right of one half, uses the existing
native pole data, and uses the zeta functional equation for the other side.
There is no additional assumed native pole package, pointwise source
bound, or geometric-payment hypothesis in this native consumer.

## Translation of the original supplied one-sided bound

The source of this refactoring is the existing
`RHLean.Analysis.WindowLandau.landau_window` in
`RHLean/Analysis/AlpogeWindowLandauCriterion.lean`. Its complete original
input/output type remains:

```lean
{g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ}
(hP : PoleData g Φ Z)
{θ δ B : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
(hδ : 0 < δ) (hB : 0 ≤ B)
(hW : ∀ U₀ : ℝ, ∃ U ≥ U₀,
  ∀ u ∈ Icc U ((1 + δ) * U), g u ≤ B * Real.exp (θ * u)) :
∀ ρ ∈ Z, ρ.re ≤ θ
```

`positiveMoment_bound_of_windows` takes exactly these hypotheses and
returns the direct cofinal moment input. On the selected window, its
positive integral is at most `B / (sigma-theta)^(k+1)`. On the complement,
the original growth estimate `|g(u)| <= C_0 exp(2u)` and `landau_tails`
pay both tails by `C_0 T / sigma^k`.

The proof chooses `sigma` and
`C = B/(sigma-theta) + C_0 |T|` first. For any requested `k_0`, it then
selects a sufficiently late window and an order `k >= U >= k_0`.
Thus the old supplied one-sided hypothesis translates directly to the
new positive-moment hypothesis. Conversely, a new proof of the moment
hypothesis can be consumed without first recovering a pointwise window
bound.

## Actual unconditional supplier and the quantitative gap

Set `B = log 4 + 3 + |gamma|`. Native Mertens-first arithmetic and
`psi >= 0` prove

\[
(G_z(x))_+\le Bx\quad(x\ge1).
\]

Integrating this one-sided upper bound against the kernel proves, for
every `sigma > 2` and every `k`,

\[
P_k(\sigma)\le\frac B{(\sigma-1)^{k+1}}.
\]

These are the new unconditional theorems
`alpogeNativeGzArithmetic_posPart_le_linear` and
`alpogeNativeGzPositiveMoment_le_linear`. They apply to the whole native
observable, including its centering.

For `theta < 1`, converting this particular majorant to the required form
would require a constant at least

\[
\frac B{\sigma-1}
\left(\frac{\sigma-\theta}{\sigma-1}\right)^k.
\]

The ratio exceeds one. Thus this available majorant does not establish
one constant for arbitrarily large orders. This calculation concerns the
limitation of the upper bound: it does **not** prove that the actual
moments grow at that rate or that the critical moment inequality is false.

## Inspected partial-moment and related suppliers

| Source declaration | What is proved | Remaining quantitative issue |
| --- | --- | --- |
| `nativePNTWeightedErrorMass_abs_le` in `NativePNTErrorMass.lean` | A uniform bound on the signed reciprocal Chebyshev history. | No centered decay at `N^(-1/2+eta)`; the resulting whole-source scale is linear. |
| `alpogeErdosGz_succ_le`, `alpogeErdosGz_le_of_le` in `AlpogeErdosHistoryDirectBound.lean` | Bounded upward movement of the complete `Gz`. | The accumulated starting level remains. |
| `alpogeErdosHistorySquareIncrementUPM2_le` in `AlpogeErdosHistoryIncrementNNS2.lean` | Upper second partial mass `O(H^3)` for square **increments** of `Gz`. | It does not bound the accumulated square-endpoint levels. Generic levels `F_R=R^2` already have increments of order `R` and this increment-mass scale. |
| `alpogeGz_eq_NNS_futureTail_and_terminal`, `alpogeGz_NNS_futureTail_oneSided_le` in `AlpogeGzNNSFutureTail.lean` | Exact signed tail plus terminal identity, with a paid endpoint collar. | The terminal observable minus the full signed future tail is still unbounded at the critical scale. |
| `alpogeNativeSquareNegativeLPM2Endpoint_of_dyadicChebyshev` in `AlpogeNativeLPM2Endpoint.lean` | Critical negative second moment of the square Chebyshev error, conditional on `NativeSquareDyadicChebyshevBound`. | That supplier remains explicit; the source and sign also differ from the completed positive `Gz` moment. |
| `alpogeNNSCompleteSelberg_oneSided_le_principalOvershoot` in `AlpogeNNSCompleteSelbergCovariance.lean` | The selected band correction is paid with the complete signed complement retained. | The positive principal overshoot remains explicit and needs an estimate. |
| `finiteTargetScaledSchur_target_invariant`, `physicalTRowTargetDegreeOneFirstMoment_eq_zeroTarget_sub` | Exact target-change and physical-row identities. | The displaced first moment remains in the rank-one correction. |
| `nativeNNSCenteredSchur_cannot_pay_positive_lengths` | A constant positive population can have zero centered covariance. | Centered covariance alone cannot bound an arbitrary positive first moment. |
| Native PNT contraction and iteration budgets | Arbitrarily small affine slopes with a slope-dependent intercept. | No uniform intercept/onset law giving a fixed power saving is supplied. |
| `nativePNTError_abs_le_two_sqrt_of_reciprocalInterceptLaw` | A square-root bound assuming `NativePNTReciprocalInterceptLaw`. | The required global intercept law remains a hypothesis. |
| `strongNativeMertensSubexp` in `StrongMertensLogNineBalance.lean` | An unconditional bound `|sum mu| <= C N exp(-c (log N)^(1/10))`. | Different source and no fixed exponent below one; no inspected critical completed-source bridge. |

The inspection also covered finite partial-moment signed-sum identities,
the native ASK--MAIN partial-moment map, finite cochain/class-group counts,
and the conditional canonical Mobius square-block partial-moment route.
These preserve useful algebra or supply their stated finite estimates;
none of the inspected declarations provides the critical `P_k` estimate.
This is a scoped source audit, not a claim that further reasoning from
other repository results is impossible.

For the future-tail route specifically, with
`T(N,M) = sum_(N <= n < M) (psi(n)-n)/(n(n+1))`, the existing exact formula is

\[
\frac{G_z(N)}N=\frac{G_z(M)}M-T(N,M)+e_N-e_M,
\quad 0\le e_N\le1/N.
\]

It retains both signs and the terminal term. A critical lower bound for
that full signed tail relative to the terminal observable would be a
possible supplier, but the identity alone does not establish it.

## Validation contract

`research/ALPOGE_POSITIVE_MOMENT_LANDAU_AUDIT_20261123.lean` checks the
literal integrands, actual native integrability, signed coefficient
compensation, fixed-constant/cofinal-order telescope, original-window to
moment translation, unchanged old window theorem type, native zero
exclusion and actual Mathlib `RiemannHypothesis`, exact history and floor
bridges, and the separate unconditional coarse bound.

The audit checks the transitive axiom closure of 15 theorem roots and
rejects every axiom outside `propext`, `Classical.choice`, and `Quot.sound`.
Compilation, project warnings, and the full native dependency graph are
checked by the existing hosted Lean workflow. Source inspection and
static checks are not reported as a substitute for hosted kernel checks.

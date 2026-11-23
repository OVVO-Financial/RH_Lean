# Native physical supplier reductions

**Status:** the critical normalized signed-source estimate and RH remain open.
The organizing consumer is the original physical top excess divided by its
earned projection divisor. This work does not resume the full construction in
draft PR #1201, import an external RH theorem, or assign an arithmetic formula
to a metric, degree, gain, or period field.

Base: `main@014c68132ef5c48df861cb6c6d9909d2e48f7d1a`. Its mathematical
sources agree with `4b9881be8fcb2b0b817afe5008d29adbcd829a5c`; the intervening
merge is the proof-meaning and task-selection correction. The inspected
research snapshot is PR #1201 at
`6edf537f2c163c8c9e33fa72122c644cf06dbddc`.

## 1. The exact consumer and a weaker sufficient loss hypothesis

Write `T = card TT`, `n = card H`, `Delta = card T2 / n`, and
`Q = T*m*b*Delta/2`. The existing constructed dyadic comparison bounds the
mean of the actual `Gz(a_t/b)` by `physicalTopExcess/Q` plus its paid analytic
error, under its stated host, height, width, density, and window conditions.
Its construction supplies the host and selected primes; the required physical
height/width family is still subject to those conditions.

The physical comparison previously requested pointwise `LossBounds`, although
the native finite slope theorem `weighted_mean_bound_statement` already uses
only `Data.Losses`:

\[
\operatorname{umean}(\mathrm{ASK}-\mathrm{Ga})\le\mathrm{LoP},
\qquad
\operatorname{umean}(\mathrm{IO})\le\mathrm{LoP}.
\]

The new declarations in
[`AlpogeNativeSignedSlopeComparison.lean`](../RHLean/Analysis/AlpogeNativeSignedSlopeComparison.lean)
attach that weaker hypothesis directly to the original physical source:

- `physicalTopExcess_le_errorTerm_of_meanLoss`;
- `physicalTopExcess_div_le_normalizedGeometricCosts_of_meanLoss`.

The latter retains all three original costs and the exact positive divisor
`Q`. Existing pointwise-loss theorem signatures are preserved and specialize
the new results by `losses_of_losses5`. The source, gain, Frobenius, inertia,
prime-power cutoff, and partner widths are unchanged.

This is a reduction in the required strength of a supplier. Neither of the
two averaged inequalities is asserted to have been constructed for the
physical family.

## 2. A quantitative comparison on the original local arithmetic source

The new module
[`AlpogeNativeLocalGainSource.lean`](../RHLean/Analysis/AlpogeNativeLocalGainSource.lean)
reconstructs the finite first-return comparison used before Alpoge's local
restriction gain, using the existing native dyadic host. For an actual
inert Frobenius `g`, its reduced partner is

\[
((0,i(1+g_{0,2})),\ t+i g_H).
\]

It agrees with the original physical partner on odd exponents. The reduced
orbit's even steps are retained in the first-return predicate; equality of
the two partner maps at even exponents would be false and is not used.

Let `R_p` be the retained odd-power sum after the shifts
`a -> a-2*c` and `w -> w+c-heightShift`. Let `E_p` be the excluded original
atoms, restricted to the low central primes. The code proves that exclusions
vanish at signal primes and at primes `p >= a/bTop`, using the original
top-width lower bound. Thus `E_p` has exactly those remaining physical atoms,
not a newly assigned gain or an assumed estimate.

For `0 <= heightShift <= c`, the original positive-part comparison costs at
most `3*c` per active exponent. The sharp original cutoff implies that
exponents with `p^i > N` have zero physical source. The number of active
exponents is at most `Nat.log p N`. Consequently the new terminal theorem
`nativeDyadicDe_re_le_localRetainedSource` proves

\[
\operatorname{Re}(\mathrm{De})
\le \sum_{p\in\mathrm{Inert}(N)}2\log p\,
  \bigl(R_p+E_p+3c\lfloor\log_p N\rfloor\bigr)
 +\operatorname{Re}(\mathrm{ASK}_d)
 -\operatorname{Re}(\mathrm{MAIN}).
\]

The exact hypotheses retain `HostHyp`, positive physical widths, the same
cutoff `a/w <= N`, the actual top widths `w(top s) >= bTop > 0`, positive
amplitude, and the shift interval. All odd powers at the original inert
primes and every ramified `d`-power remain represented. The principal term
is subtracted unchanged. No absolute-value relaxation is applied to MAIN.

This discharges the elementary source-to-local-sum comparison, including
the vanishing exclusion cases and finite shift price. It does not show that
an actual restriction lattice realizes `R_p`, bound the remaining low
central sum, or pay the weighted shift sum after division by `Q`. Those
remain explicit quantitative obligations. In particular, the logarithmic
exponent count by itself is not a root-scale estimate after summing primes.

## 3. Reverse integrality suffices for the required norm direction

The new Mathlib-only module
[`NativeOneSidedIsogenyNorm.lean`](../RHLean/Geometry/NativeOneSidedIsogenyNorm.lean)
proves a nontrivial arithmetic inequality from an ideal inclusion.

Let `K` and `M` be number fields, `M/K` a field extension, `b` a nonzero
integral ideal of `O_K`, and `beta` a nonzero element of `M`. Assume only

\[
\beta^{-1}b\subseteq\mathcal O_M.
\]

The theorem proves

\[
|N_{M/\mathbb Q}(\beta)|\le N_K(b)^{[M:K]},
\qquad
\sum_{\sigma:M\hookrightarrow\mathbb C}\log|\sigma(\beta)|
\le [M:K]\log N_K(b).
\]

No integrality of `beta` is assumed. To see why the direction is correct,
write `beta = a/d` with `a,d` integral and `d` nonzero. Reverse integrality
gives the literal integral ideal inclusion

\[
(d)\,b\mathcal O_M\subseteq(a).
\]

The index/norm inequality therefore gives
`absNorm(a) <= absNorm(d)*absNorm(b O_M)`. Division by the nonzero denominator
norm and the extension-ideal norm formula prove the displayed estimate.
The proof does not identify an arbitrary height with the desired answer.

When `[K:Q]=2`, the derived theorem
`quadratic_period_row_correction_nonpos` proves

\[
\lambda_b:=\frac{2}{[M:\mathbb Q]}
  \sum_\sigma\log|\sigma(\beta)|-\log N_K(b)\le0.
\]

This is exactly the sign needed in the existing CM class-period row
calculation. Forward derivative integrality is needed for the opposite norm
inequality, but is unnecessary for this direction.

## 4. How the norm estimate would enter the period consumer

In the inspected PR #1201 period calculation, genuine analytic lattice
inclusions give, for each ideal class `C` and embedding `sigma`,

\[
\operatorname{covol}(L_{C,\sigma})
=\frac{|\sigma(\beta_C)|^2}{N(b_C)}
  \operatorname{covol}(L_{0,\sigma}).
\]

Unit discriminants and the product formula remove the discriminant row sum.
The row correction is `lambda_b` above. Exact ideal-class permutation gives
the column sum. Replacing the old equality of norm rows by `lambda_b <= 0`
therefore yields the useful direction `P >= Omega`, hence `rho = 0`, after
the same finite double sum and the original `log(pi)` normalization.

The tangent-coordinate identity
`NativeCMWeierstrassTangentCoordinatePeriods.tangentCoordinatePeriods_log_covolume`
retains the same integral model and identifies `log(covol(u^-1 L))-log(pi)`
with its original `latticeLogPeriod`. Thus the proposed period application
uses the actual coordinate normalization, including its scale.

This application still requires both analytic lattice inclusions and the
actual reverse derivative integrality on the same models. It removes only
forward derivative **integrality**, not the forward analytic lattice
inclusion. The present standalone norm module does not construct those
geometric inputs and does not claim that the physical period theorem or
`DIV` is now closed.

For a lower bound `P >= Omega-rho`, the original `DIV` coefficient gives the
exact normalized extra cost

\[
\frac{m\rho\sum_ta_t}{Tmb\Delta/2}
=\frac{2\rho\bar a}{b\Delta}.
\]

With `bar a/b <= x+1` and `Delta >= x^(-epsilon)`, the bill is at most
`2*rho*(x+1)*x^epsilon`. Thus a scale-independent positive error is too
large in this regime; an error of order `x^(-1/2)` is sufficient up to the
allowed epsilon loss. The reverse-integrality direction avoids this error
when its actual geometric premise is supplied.

## 5. Existing descent maps and the remaining physical attachment

`nativeAllPlaceDescent_of_regular_groupDet` already constructs the actual
unnormalized character-trace maps

\[
\phi_h(f)=\sum_g\chi(g)^{-1}\operatorname{st}_g
  (f\operatorname{st}_h(u))
\]

from one regular section `u`, on an integral source lattice `A` in `Vminus`.
Its target is the actual intersection `B=L intersect N_chi`, with the
restricted metric. Integral product closure and group stability prove
integrality. The group determinant proves joint injectivity. The collective
cost retains `q^3 exp(2*C*z^9)` at every embedding and the existing size
regime pays it.

The same construction proves `q*rank(B) <= dim(Vplus)`. The additional
near-rank statement `dim(Vplus) <= (1+delta)*rank(A)` remains a physical
input. `nativeAllPlaceDescent_of_constructed_petersson_section` derives its
multiplier norm from short-section data and the actual measured evaluation
tie. It still requires those data, the original source-slope bound, and the
near-rank comparison. Its output must be identified with the slopes used by
the physical signed-slope data; record-field assignment does not prove that
identification.

The current work therefore does not select an unrestricted reconstruction
of CM/Serre/cusp geometry. Further construction must discharge one of these
specific physical premises, with its normalized cost recorded.

## 6. Verification and proof meaning

Lean execution is hosted-only. The executable
[`ALPOGE_NATIVE_PHYSICAL_SUPPLIER_AUDIT_20261123.lean`](ALPOGE_NATIVE_PHYSICAL_SUPPLIER_AUDIT_20261123.lean)
checks the terminal axiom set of the new implications, allowing only
`propext`, `Classical.choice`, and `Quot.sound`.

The audit does not convert their hypotheses into supplied facts. The
unconditional physical critical bound remains open until the actual
compatible family supplies the mean losses, measured slope/degree inputs,
and their complete normalized cost.

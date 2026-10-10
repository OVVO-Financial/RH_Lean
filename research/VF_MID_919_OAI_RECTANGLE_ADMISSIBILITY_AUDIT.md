# Native owner-two coefficients and centered-row admissibility

The exact norm/character dictionary and native signed Gram are established at
`61faba6b90bf8366a60a13458bbd8e2539f81b04`. This audit narrows a proposed
analytic interface; it does not prove its uniform estimate. The weight below
is the native AMP common-clock weight, not the historical VF square-band
weight. Historical Sector Six reassembly remains a separate downstream task.

## What is centered

OpenAI's `normalized_input_difference` subtracts two product rows with the
same character, profiles, prime slots, masks and height, and requires
`Y₁ * Y₂ = X₁ * X₂`. It centers on a matched reference row, not on an
expectation. The common normalization is
`sqrt(X₁ * X₂ * ∏ i, P i)`.

The source coefficient is a regrouping over ideal tuples of a product of
prime-slot coefficients and the difference

\[
W_1(NA/X_1)W_2(NB/X_2)-W_1(NA/Y_1)W_2(NB/Y_2),
\]

with its actual coprimality and divisor masks. A scalar normalization match
does not identify this coefficient with a physical site weight.

Pinned upstream source:
[OriginalSource.lean](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/NumberTheory/DirichletL/Energy/OriginalSource.lean),
[CommonRadialData.lean](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/NumberTheory/DirichletL/Moments/CommonRadialData.lean),
[EligibleEnergy.lean](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/NumberTheory/DirichletL/Moments/EligibleEnergy.lean).
ProofCouncil extends the estimates while importing these arithmetic objects;
its [actual_uniform_moment](https://github.com/GTimG/QuasiRiemannTracker/blob/40844a7614b67840801e65b836b3da2e1f7ff029/proofs/qrh-20261009/formalization/QRH/Energy/UniformMoment.lean)
requires a fixed smooth supported profile and its stated masked source class.

## A finite obstruction attached to the native weight

For `X = R² - 1`, the existing `lowOwnerZeroFrequencyMobiusWeight R n` is

\[
w_R(n)=\mathbf1_{R\le n}+
\sum_{q\in\mathcal Q_R}\frac1q\mathbf1_{n\le\lfloor X/q^2\rfloor}.
\]

At `R = 317`, the native low owners are `3,5,7,11,13,17`, with product
`Q = 255255`. For `a = (7,13,19)`, `b = (31,37,61)`, the native coefficient
matrix is

\[
[Qw_{317}(a_i b_j)]_{i,j}=
\begin{pmatrix}
230456&230456&470696\\
470696&470696&451061\\
470696&451061&427856
\end{pmatrix}.
\]

Its determinant is `-2309174383131000`. All six primes are `1 mod 3`;
the nine sites are odd, squarefree, and inside both parent and doubled-child
cutoffs. A single difference `f_i g_j - u_i v_j` has determinant zero even
over complex numbers. Separable phases and a factor constant on these
occurrences can be absorbed into its four factors. Therefore this matrix
cannot equal a single such rectangle occurrence by occurrence.

[The Lean witness](VF_MID_919_OAI_RECTANGLE_RANK_OBSTRUCTION.lean) references
the literal existing AMP weight and proves the determinant obstruction.
[The independent rational check](../scripts/vf919_rectangle_rank_check.py)
reconstructs the owners and physical cutoffs and reproduces the matrix.
Dedicated native CI checks compilation and the seven new theorem axiom
audits. This note's source statements are research provenance; only a
successful Lean check certifies the new declarations.

The obstruction concerns this unmasked two-factor slice. A coupled mask can
alter matrix rank, and regrouping over factorizations can alter the coefficient
class. No obstruction to all permitted OAI sources is claimed. In particular,
the witness does not prove that every representation requires a number of
rectangles growing with `R`; it only excludes one centered rectangle here.

## The admissibility obligations

| Requirement | Native status / exact remaining obligation |
| --- | --- |
| Finite support | Both physical legs are finite, with their different sharp cutoffs retained. |
| Same arithmetic coefficients | The norm/character map is exact; a factorization-summed OAI source identity has not been proved. The single unmasked termwise rectangle fails the witness. |
| Rational dilation by two | It acts on the character leg. The inert prime ideal has norm four; an ideal of norm two cannot implement this dilation. |
| Prime-slot coefficient bounds | Reciprocal weights are individually bounded, but arbitrary residual norm coefficients are not permitted by that fact alone. An exact slot representation and uniform controls are needed. |
| Smoothing | The literal sharp physical comb is not a fixed smooth profile. Finite interpolation or exact recovery at each root does not establish uniform derivative/seminorm bounds for an analytic moment estimate. |
| Matched normalization | Product equality is necessary for this centered identity. Its conversion back to the unnormalized physical scalar must retain every volume factor. |
| Row extraction | A weighted row average must be connected to the actual principal row with explicit weights, row ranges and losses. |
| Uniformity | Constants must be independent of `R`. Allowing a profile or the slot type to change with `R` requires uniform control of their effect on the theorem constants. |

## The direction and scale of the required bound

Let `H_R` and `J_R` denote the two native amplitudes already identified with
constructed principal norm sums. The complete signed Gram satisfies

\[
2G_R=-2\Re(H_R\overline{J_R}).
\]

An upper budget `2G_R ≤ B_R` is equivalent to
`Re(H_R conjugate(J_R)) ≥ -B_R/2`. The sign cannot be replaced by an assumed
nonnegative correlation. Polarization yields the sufficient route

\[
2G_R=|H_R-J_R|^2-|H_R|^2-|J_R|^2\le |H_R-J_R|^2.
\]

Thus a centered-difference upper bound at the required root-square scale can
be useful, provided its physical source identity, row extraction and sharp
transfer are all proved with uniform constants. An upper bound on this
positive part does not control the negative part of the Gram. Separate
magnitude estimates or a bound above the required scale do not close the
budget.

Two possible analytic tasks remain: a uniformly controlled sum of admissible
centered sources with exact factorization regrouping, or a signed moment
extension for the existing physical divisor comb. Neither is established by
the rank witness or by the centered algebraic identity.

## Separate genuine-ideal semantic import

Upstream already contains genuine ideal fiber arithmetic in
[NormFiberCharacters.lean](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/NumberTheory/DirichletL/Hecke/NormFiberCharacters.lean)
and multiplicativity/prime-power uniqueness in
[LocalEulerIdentities.lean](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/NumberTheory/DirichletL/Hecke/LocalEulerIdentities.lean).
The unconditional `normFiberCoeff_baseChange_eq_pairInverseCoeff` is the
specific import target. At the trivial character of modulus one its weight
is genuine ideal Möbius, and its paired inverse coefficients give
`μ * (χ₋₃ μ)`. The zero-norm convention must also be matched.

This supplies an existing proof source for the three splitting cases, not an
imported theorem in RH_Lean. Upstream uses Lean/Mathlib 4.34; this repository
uses 4.24, whose pinned tree lacks the generalized UFD Möbius module used
upstream. The arithmetic dependency slice must be ported and connected to
`vf919EisensteinNormCoefficients`, then its excluded-six restriction must be
proved. No assumed coefficient equality completes this import.

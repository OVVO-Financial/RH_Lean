# Original 1 → 7/8 contraction through RHLean partial moments

## Scope and pins

This reconstruction puts native UPM/LPM energy states and native source moments inside the complete original contraction proof. The final theorem depends on those states and moments. It does not start from the original terminal seven-eighths nonvanishing theorem.

- RH_Lean base: `7790fb9f5ddda6eb9823899f2694d691756cd248`.
- Original OpenAI source: `1581d4cbdd69a0faf34b2089614fe2a814316a6a`.
- Lean: `leanprover/lean4:v4.34.1`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

The original analytic floor, successor, inverse-field and unmarked-field lemmas are reused. This is a faithful proof replay and an explicit uniformity audit, not an independent reproof of those analytic lemmas. It establishes the original exponent. It does not establish a further exponent gain or the additional sharp moving-window variance estimate.

The exact PR-head combined native/OAI workflow determines compilation status. Static mathematical review is not a substitute for that kernel check.

## Unconditional native conclusion

Write
\[
E(x)=D_x+2C_x=|M(x)|^2,
\]
where \(D_x\) is the exact squarefree diagonal and \(C_x\) is the native positive-lag signed pair sum. Both endpoints use the identical physical population:
\[
E(x)\le x^2,
\qquad
\forall\varepsilon>0\ \exists A_\varepsilon\ge0\
\forall x\ge1,\quad E(x)\le A_\varepsilon x^{7/4+\varepsilon}.
\]
Equivalently,
\[
\frac{E(x)}{x^2}\le A_\varepsilon x^{-1/4+\varepsilon}.
\]
The one-quarter energy saving is the one-eighth amplitude improvement \(1\to7/8\). The entire signed combination is bounded; no separate estimate on the two unsigned pair populations is asserted.

The declarations in namespace `RHLean.Analysis` are:

- `nativeReplay_initial_signed_energy`.
- `nativeReplay_signed_covariance`.
- `nativeReplay_mertens_growth`.
- `nativeReplay_signed_energy_seven_fourths`.
- `nativeReplay_normalized_signed_energy`.
- `nativeReplay_all_square_blocks`.

Their constants precede every physical prefix length or square endpoint.

## Complete proof route

| Stage | Mechanism retained in the native replay |
|---|---|
| Initial bound | Euler nonvanishing gives \(\beta_*\le1\); physical signed energy initially satisfies \(E(x)\le x^2\) |
| Row assembly | Full original positiveSlotRow, ideal labels, selected primes, masks and normalizers |
| Partial moments | UPM2 + LPM2 on both exact Phi channels, divided by two |
| Energy induction | Native certified band at every stage, using proved certified_floor and actual_successor |
| Inverse moments | Both inverse raw and inverse marked fields, with unchanged capacity conditions |
| Marked moments | Native source proof retains \(1+t/2\), explicitly relaxed to \(1+t\) for the current consumer |
| Unmarked moments | Actual zero-slot supplier, retaining \(U^{\max(1,2m)+t}\) |
| Source aggregation | All four native moment fields, with original rows, bins, labels, masks, selected subsets and height bounds |
| Height absorption | Choose \(\tau\) after the common degree \(J\), with \(2\tau(1+J)\le t\) |
| Common probe | Same compensated probe: low \(Z^{3/16+\omega}\), high error \(Z^{\beta_*-11/16-\sigma}\) |
| Supremum contradiction | Primitive zero arbitrarily near the supremum contradicts the two bounds |
| Physical return | Native zeta/Mertens converse and exact Green–Kubo covariance; all prefixes and complete square shells |

The pinned formal DAG handles both row-count branches directly. It does not require a separate imported \(11/12\) theorem, even though the manuscript describes a two-stage presentation.

## Literal NNS energy and preservation

For \(\Phi(z)=(\Re z-\Im z,\Re z+\Im z)\), define
\[
N_2(z)=\frac{
 U_2(0;\Phi_1(z))+L_2(0;\Phi_1(z))+
 U_2(0;\Phi_2(z))+L_2(0;\Phi_2(z))
}{2}.
\]
Here a single value has its pointwise upper/lower partial power. The proved identity is \(N_2(z)=\|z\|^2\).

The native energy is the original sum with this exact substitution:
\[
\sum_{z\in\mathcal O}
\mathbf1_{\mathrm{keep}(z)}
N_2(\mathrm{positiveSlotRow}(z))
\Re\Phi_{\rm radial}(\|\mathrm{eisEmbedding}(z)\|^2/K).
\]

The entire signed row is assembled before the partial moments. No phases, cross terms, masks, slot factors or scales are removed. Equality is proved pointwise inside the same infinite sum; no separate convergence assertion is introduced.

The general radial real weight can have either sign. The replay preserves it. A probability-measure interpretation requires nonnegative radial weights, as in the later positive radial majorant.

## Original uniformity mechanism

The original recursion is finite descent in admissible width. It is not an assumed recurrence in the physical scale.

For width cap \(M\), loss budget \(\epsilon>0\), and original source budget \(B_*\), the schedule includes
\[
a=\min(1,\epsilon/16000),\quad
n=\lceil2M/a\rceil_{\mathbb N}+1,
\]
\[
r=\min\left(a/100,\frac{\epsilon}{10^6(n+M+10B_*+30)}\right),
\quad \mathrm{mesh}=\frac r{\kappa+1},
\]
\[
w_k=\min(M,r/16+ka/2),\quad
e_k=\epsilon/1000+(1+64k)r.
\]
The source budget comes from the original finite length-envelope recursion; it is not an omitted arbitrary constant. The original schedule proves
\[
20r\le a/2,\qquad w_n=M,\qquad e_n\le\epsilon/500.
\]
Every child loses at least \(a/2\) in width and therefore belongs to the preceding stage. The actual successor pays exceptional, reflected, zero-slot and profile-transport costs.

The full native quantifier order is
\[
\exists\,\mathrm{degree},S\
\forall\,\eta_0,Q\text{ admissible}\
\exists\,C_0,C_+>0\
\forall^{\mathrm{eventually}}Z\
\forall\,\text{admissible states/profiles/slots}.
\]
The detector source then has
\[
\exists J\ge0\
\forall\eta\
\exists C_\eta>0\
\forall\tau\in(0,1]\
\exists Z_0\
\forall Z\ge Z_0\
\forall\,\text{admissible rows/batches/bins/subsets}.
\]

The constant precedes every moving row, batch and subset choice. \(J\) precedes the character; \(C_\eta\) precedes \(\tau\). The threshold may depend on \(\tau\), and the constant may depend on the character and fixed source data. Arbitrary growing conductors and arbitrary scale-dependent profile seminorms have not been declared free.

### Contradiction family and unconditional output

The source-uniformity theorem explicitly assumes \(7/8<\beta_*\) and the corresponding HighData. It records the family used during the contradiction. After the endpoint proves \(\beta_*\le7/8\), that hypothesis is false.

It is therefore not an unconditional new source-family estimate usable with arbitrary sharp windows. The unconditional, nonvacuous all-scale outputs are the physical prefix covariance, Mertens growth, normalized energy and complete-square-shell bounds.

## Why the endpoint is seven eighths

The original geometry is
\[
h=13/16,\quad b=1/8,\quad\ell=1/6,\quad
\ell_x=17/48,\quad\ell_y=23/48.
\]
Its principal Mellin exponent is \(C(s)=s-11/16\), with \(C(7/8)=3/16\).

Assuming \(\beta_*>7/8\), the construction chooses the same positive margins before the primitive target:
\[
0<\omega<\beta_*-7/8,\qquad \sigma>0.
\]
For each target the same masked probe and analytic correction satisfy
\[
J_\eta(Z)=O_\eta(Z^{3/16+\omega}),\qquad
J_\eta(Z)-f_\eta(Z)
=O_\eta(Z^{\beta_*-11/16-\sigma}),
\]
with \(\|H_\eta(s)-1\|\le1/2\) on the admitted half-plane. Both exponents lie below the signal at a sufficiently near-supremum zero. The reconstructed continuation argument excludes that zero and proves \(\beta_*\le7/8\).

## Formal files and acceptance

- `research/oai_434/VF919NativeEnergyInduction.lean`.
- `research/oai_434/VF919NativeSourceMoments.lean`.
- `research/oai_434/VF919NativeSevenEighthsReplay.lean`.

The existing retained-width marked-source theorem is a live dependency.

The combined native/OAI workflow emits the modules under the pinned environment, compiles warning-fatally, and prints terminal axioms. The audit
`scripts/lean/NativeSevenEighthsReplayAudit.lean`
requires live proof-value dependence on the native induction and moment assembly and forbids original terminal shortcuts. It removes unused administrative bindings in new proof values before collecting dependencies.

Permitted terminal axioms remain propext, Classical.choice and Quot.sound. No theorem statement or existing validation gate is weakened.

## Remaining stronger claim

A full prefix covariance is a square of a signed sum. The additional sharp-window target is a sum of window squares. This replay establishes the original uniform contraction on its exact admitted families and the physical prefix consequence; it does not equate those different quantities.

A further gain requires improving an estimate used by the complete return while preserving its uniformity and complementary terms. The marked improvement is exposed and consumed, but the present final consumer retains its original budget. No further endpoint gain is claimed.

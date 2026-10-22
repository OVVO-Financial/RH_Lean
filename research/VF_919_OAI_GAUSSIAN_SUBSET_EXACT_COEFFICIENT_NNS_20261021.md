# Exact GaussianSubset coefficient correspondence → signed NNS source-moment seam

**Authority pinned:** original OAI [GaussianSubset.lean](https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Detector/GaussianSubset.lean) (`compensation_subset_common`), [GaussianCommon.lean](https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Detector/GaussianCommon.lean) (`compensatedPhysicalProbe_common_gaussian`), [PhysicalRows.lean](https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Detector/PhysicalRows.lean), [GaussianCompensation.lean](https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Detector/GaussianCompensation.lean), [Moments/DetectorPlainFiberSource.lean](https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Moments/DetectorPlainFiberSource.lean), and [DetectorPlainMarkedFineField.lean](https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Detector/DetectorPlainMarkedFineField.lean). Date 2026-10-21.

## Exact OAI index and coefficient — no norm-only proxy

Fix a **genuine** selected ideal-prime tuple `p : Fin K → O`, a subset `J ⊆ Fin K`, a physical row `r : PhysicalRowIndex`, a dyadic index `j : ℕ` and real height `t`. Write `q_i=elementNorm(p_i)`, `q_J=∏_{i∈J} q_i`, `q_Jc=∏_{i∉J}q_i`. Define the original finite slot coefficient

```text
c_J(p)=(-1)^|J| * q_J^(-3/2) *
       star(elementCoeff η (slotProduct p (univ\J))).

w_i(p)=slotWindow_i(q_i/slotScale_i)
lambda_i(p,t)=logPhase(-t, Real.log(q_i/slotScale_i))

D_J(p) = Ideal.span {slotProduct p (univ\J)}
X_J = X/q_J
Y_J = Y/q_J

B_{J,p,r}(j,t) =
  physicalRowWeight C W0 W1 X_J Y_J r
  * correctedCompletedT C.excluded D_J
      (physicalRowMonoid η C r)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) (2^j)

rho_J(j,t)=gaussianJointDensity (V J) (hV J)
                 (2^j/(Z*∏_{i∉J}slotScale_i)) t

a_{J,p,r}(j,t)= c_J(p) * (∏_i w_i(p))
               * B_{J,p,r}(j,t)
               * (∏_{i∉J}lambda_i(p,t))
               * rho_J(j,t).
```

This is the fully unexpanded OAI row coefficient **as already supplied upstream** by `compensation_subset_common` after the Gaussian reassembly, including the exact `W0/W1` weights inside `B` and all internal sextic Gauss phases. It is NOT a same-`m` marked/rescaled cofactor equality.

The literal original OAI selected-factor layout is

```text
a_{J,p,r} =
 ( c_J(p) * ∏_{i∈J} w_i(p) )
 * B_{J,p,r}
 * ( ∏_{i∉J} [w_i(p)*lambda_i(p,t)] )
 * rho_J(j,t).
```

The Lean theorem `gaussianSubset_coefficient_exact` proves this **pointwise for every indexed label and every complex coefficient** using the finite product complement law, not character orthogonality or Gauss normalization. The theorem `gaussianIndexed_source_sum_exact` proves the full finite labelled sum, including duplicate rational norms. To instantiate `core` faithfully, include `B*rho_J` in it; neither component can be dropped or normed before forming the complex sum.

**Important source-library boundary:** the compiled RH_Lean theorem is a coefficient-level specialization of the original *formula*, not an imported OAI type-specialized theorem (the OAI and RH_Lean Lake environments are different). The full original `∑_j ∫_t` identity is already kernel-proved upstream by `compensation_subset_common` and `compensatedPhysicalProbe_common_gaussian`, so do **not** replace either with a finite quadrature or pretend that a per-height moment controls the final integrated probe without uniform Fubini/Minkowski and cross-height estimates.

## Exact NNS quadratic form on precisely these original labels

For a fixed source evaluation `u` (including whichever spectral/height/parameter indices are legitimately fixed), write `A_u=Σ_{J,p,r}a_{u;J,p,r}`. Use the actual complex coefficient from above and `Phi(z)=(Re(z)-Im(z),Re(z)+Im(z))`. On the full **product carrier** `subset × labelledPrimeTuple × PhysicalRowIndex`:

```text
D = Σ_u omega_u * Σ_a |a_{u,a}|^2
C_off = (1/2) Σ_u omega_u * Σ_{a≠b}
          [Co0(x_{u,a},x_{u,b})+Co0(y_{u,a},y_{u,b})]
V_off = (1/2) Σ_u omega_u * Σ_{a≠b}
          [Div0(x_{u,a},x_{u,b})+Div0(y_{u,a},y_{u,b})]

M = Σ_u omega_u * |A_u|^2 = D + C_off - V_off.
```

The compiled theorem `gaussianIndexed_signed_NNS_moment_exact` proves the full `M=Co_all-Div_all` without dropping cross-J, cross-prime, inter-fibre, or real/imaginary terms; a second theorem preserves original `1/D_U` weighting where it genuinely applies. Use **one** source normalization: if the actual `fiberCoefficient` already contains selected W, it must not be externally multiplied by a second `|W(u)|²`.

## The only remaining analytic estimate (OPEN)

To obtain a **NEW** uniform gain, source-level arithmetic must yield for some fixed `sigma>0` and for the appropriate original OAI row, height, mask, and slot quantifiers:

```text
M_jk(U) = D_U + C_off(U) - V_off(U)
         <= C*(1+height)^J * U^(1+D.t-sigma),
for all j+k <= 2 and all admitted selected slots.
```

This is equivalent to an independent lower bound
`V_off(U)-C_off(U) >= D_U-C*(1+height)^J*U^(1+D.t-sigma)`.
**Do not use this same bound as the source hypothesis and then call its NNS restatement a new proof.**

OAI's already-verified `source_batch_plain_marked_fine` supplies the original weaker `U^(1+D.t)` bound under `PositiveFineSourceInput` and its exact capacity conditions; `detector_row_eq_source` supplies the literal `fiberCoefficient * rowWeight` sum with `D_U^(-1/2)`. Those results support **exact NNS rewriting** but do not automatically identify `GaussianSubset` theta/Poisson physical-row tuples with `fiberCoefficient` detector columns. The physical probe is a Gaussian-Mellin integral and the marked detector polynomial is a different indexed representation; a source-level commutation/intertwining theorem is required if applying the same covariance bound to both.

### Next proof insertion (no other research branch)

Prove the original-type intertwining theorem using the *actual* Gaussian reassembly and detector column expansion, preserving the `(u,J,p,r,j,t)` indices and all `W0/W1`, D-masks, completed ideal phases and Gaussian densities. Then derive the required **uniform quantitative** Co/Div payment with original rows, all heights, all j+k<=2, including cross-height/cross-J terms, using specific OAI Poisson and character moment estimates. If the existing source estimates furnish only `U^(1+D.t)`, report that exponent exactly; do not claim an independent `sigma`.

**What this PR certifies:** original-form coefficient splitting + full labelled finite complex moment identity, warning-fatal Lean subject to CI. **What it does NOT certify:** an original OAI↔RH_Lean type import, an independently stronger moment estimate, or any new zero-free/RH result.

## Whole integrated probe and true uniform signed bound (post-integration theorem)

The important `GaussianCommon.compensatedPhysicalProbe_common_gaussian` theorem already identifies the *complete* physical probe with the **finite subset sum** `Σ_{J⊆Fin K} A_J`, where every `A_J` is the original `∑'_{j:ℕ} ∫_{t:ℝ}` of the exact original `compensationSubsetWeight * compensationRowTest * selectedSlotFactor * gaussianJointDensity`. No extra rearrangement inside `A_J` is needed to take its norm.

The corresponding actual residual in OAI's `HighFromMoments.actual_high_probe_from_raw_moments` is `Σ_J A_J - principalSignal`. We introduce the distinct original source labels `Some J` and `None`, the latter with complex coefficient `-principalSignal`. The theorems `gaussianIntegrated_source_minus_principal_exact` and `gaussianIntegrated_principal_signed_NNS_moment_exact` give

```text
Σ_u omega_u * |Σ_J A_J(u) - principalSignal(u)|²
 = Co_all({Some J, None}) - Div_all({Some J, None}).
```

All cross-J covariance, cross-dyad and cross-height terms now remain *inside* the integrated complex coefficients before squaring. The principal cross terms have the original negative sign and appear in the NNS quadratic rather than being silently excluded. `gaussianIntegrated_uniform_signed_NNS_of_original_bound` then proves the exact, genuinely uniform implication

```text
OAI pointwise estimate |Σ_J A_J(u)-principalSignal(u)| <= B(u)
  for every admitted source row u
=> Co_all - Div_all <= Σ_u omega_u * B(u)^2
  for every omega_u >= 0.
```

This consumes OpenAI's **actual** high-row analytic estimate (with all its hypotheses and its published exponent) rather than assuming the *same* NNS moment inequality as an input. It produces no additional exponent improvement. To get a new positive gain, one must independently improve the original high-row/source moment bound itself; the NNS decomposition cannot do that automatically.

For exact OAI-type integration, instantiate `A_J` from `compensatedPhysicalProbe_common_gaussian` and `B(u)` from the conclusion of `actual_high_probe_from_raw_moments` (including its full signed principal term and conductor-dependent constants). This native algebra file cannot yet import the OpenAI Lean theorem types into RH_Lean; the quantitative estimate here is verified as an implication, not advertised as a new arithmetic proof.

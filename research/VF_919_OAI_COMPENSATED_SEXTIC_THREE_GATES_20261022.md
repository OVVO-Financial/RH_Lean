# Original OpenAI compensation → resonant fibers → sextic moment: three non-circular gates

**Research status (Oct 22, 2026):** exact native bounded-valuation arithmetic, genuine OAI prime-local order-six character injection, actual OAI two-bill compensation, and finite **post-grouping** Holder are now authored in PR #1005 and must be warning-fatal kernel-checked. The genuinely original-source global resonance, power-saving grouped fiber norm and Gauss/Poisson sixth-moment estimate remain **OPEN**. Nothing below imports the original terminal `actual_high_probe_from_raw_moments` bound as its own proof.

**Source pins:** `openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a`; Lean v4.34.1 and shared Mathlib. Audited actual sources:
- `lean/OAI/NumberTheory/DirichletL/Moments/Canonical.lean::actualSextic_order_six`
- `lean/OAI/NumberTheory/DirichletL/Detector/Sextic.lean::actualSextic_pow_eq_one_iff`
- `lean/OAI/NumberTheory/DirichletL/Detector/Local.lean::normalized_cancellation`
- `lean/OAI/NumberTheory/DirichletL/Moments/DetectorPlainFiberSource.lean::fiberPool / fiberCoefficient / detector_row_eq_source`
- `lean/OAI/NumberTheory/DirichletL/Detector/GaussianCommon.lean::compensatedPhysicalProbe_common_gaussian`
- `lean/OAI/NumberTheory/DirichletL/Hecke/Signal.lean::signal`
- `lean/OAI/NumberTheory/DirichletL/PrimeRows/HighFromMoments.lean::actual_high_probe_from_raw_moments`

## 1. Resonance classification: proved conditional finite arithmetic, true OAI local character

**Native theorem:** `research/VF_919_OAI_EFFECTIVE_SEXTIC_VALUATION_CLASSIFICATION_20261022.lean::oai_effective_ideal_resonance_iff_eq`.

For formal Eisenstein prime-ideal exponent vectors (v,w:P\to_0\mathbb N), each value (\le 2),
[
  [\forall\mathfrak p:\ 6\mid(v_{\mathfrak p}-w_{\mathfrak p})]
  \Longleftrightarrow v=w.
]
This theorem preserves distinct labels above split rational primes. The corresponding distinct-vector witness identifies at least one prime with an exponent difference **not divisible by 6**.

**OAI-typed theorem:** `research/oai_434/VF919ActualSexticLocalResonanceAndCompensation.lean::oai_actualSextic_bounded_local_resonance_iff_eq` and `oai_actualSextic_finite_family_local_resonance_iff_eq`. Original `actualSextic` has order exactly 6 for a **good maximal Eisenstein prime ideal** (lambda not in P and residue ring characteristic not 2). Thus (\chi_P^r=\chi_P^s\iff r=s) for (r,s\le2), and coordinatewise for a family of such prime ideals. This is a genuine original-OAI theorem, not a character invented from a rational norm.

**Still required on ORIGINAL complete GaussianSubset source:**
1. Construct a lossless original source label (I\mapsto v_I\in(\mathrm{PrimeIdeal}\to_0\mathbb N)), including the actual dyadic/Mellin source and all compensation subset masks and negative signal correction.
2. Prove (v_I(\mathfrak p)\le2) for **every nonzero admitted source occurrence**, or partition higher-valuation contributions into their own accounted remainder. The original finite detector `fiberPool` is a `completePool` of TWO polynomial profiles and a selected-slot family; cap-2 is not a theorem of this file.
3. Prove the exact source coefficient factorization (a_{u,I}=b_{u,I}\chi_{v_I}(u)) and completeness/CRT faithfulness over the *required* coprime residue universe. A nonprincipal character may still take the value (+1) at individual rows; incomplete high-row boxes may sample those rows disproportionately.
4. The separately subtracted `HeckeSignal.signal (eta.excludePrimes S ...) (sourceCorrection eta S) (-11/16) Z` is an **inverse Mellin transform**, not inherently a coefficient with trivial (\chi_{(1)}\). Its principal-residue match must be proved via the original `PrincipalResidueActual/PrincipalNormalized` arguments, with tail error, before assigning its effective class. Keep the current distinct negative signal atom.

## 2. Compensated fiber energy: exact local two-bill norm, global exponent OPEN

**Original-OAI-typed theorem:** `oai_actual_local_compensation_two_bills_le` applies the ORIGINAL `ProbeLocal.normalized_cancellation`. In the source's original symbols:
[
|\operatorname{CompReplacement}+v^{-1}\operatorname{LocalCorrection}|
\le\left|\frac{(1-V)(1-W)}{1-D}\right|
\left(|v^{-1}-q|\,\left|\frac V{1-V}-D\right|
       +|B+v^{-1}-q|\,|P^\star+D|\right).
]
The RHS has **TWO independent charges**. It is *not* identically (|1-\chi_P(u)^2N(P)^{-2s}|\) or (|E_P-1|\). All extra smoothing, normalization and Mellin contributions must be paid. Native `nativeLocalCompensation_equation_5_13b` makes the same two-bill structure explicit.

**Principal identity** `oai_principal_residue_normalized_cancel` proves that if *actual* `raw=residue+tail`, `residue=normer*signal`, and `normer != 0`, then `raw/normer - signal = tail/normer`. This is algebra under the **visible residue-identification premise**, not a proof of `tail=O(Z^alpha)`. The source's `sourceResidueConstant * principalScalar` need NOT be close to 1.

**Global proof still required:** For actual grouped fibers `resonantFiberSum`, prove
[
  D_{\mathrm{comp}}
     =\sum_u\omega_u\sum_{\mathcal C}
       |B_{u,\mathcal C}|^2
     \le c_1 Z^{2\alpha}\sum_u\omega_u B_u^2
]
with all principal tails, non-principal two-bill local remainders, finite number of classes, and original row weights. Local (N(P)^{-2\Re s}) bounds *alone* do not imply a global (Z^{-\sigma}) after summation over many ideals. A contour shift requires verified zero-free/holomorphic premises and uniform tail estimates; removal of the residue alone does not justify a shift to `Re s = 1/2-sigma`.

## 3. Non-resonant moment: only on grouped amplitudes

**Native proof:** `research/VF_919_OAI_GROUPED_HOLDER_SIXTH_SOURCE_20261022.lean::oai_grouped_resonant_fibers_sixth_holder` applies the genuine Mathlib finite Holder inequality with conjugate exponents `6/5,6` to the ALREADY grouped
[
  B_{u,\mathcal C}=\sum_{I:class(I)=\mathcal C}a_{u,I}
]
and a test `T_C`. Thus
[
\left|\sum_\mathcal C B_{u,\mathcal C} T_\mathcal C\right|
\le \left(\sum_\mathcal C|B_{u,\mathcal C}|^{6/5}\right)^{5/6}
     \left(\sum_\mathcal C|T_\mathcal C|^{6}\right)^{1/6}.
]
`oai_grouped_sixth_holder_of_two_analytic_bounds` separately consumes a **proved** coefficient-norm bound and **proved** sixth-moment-root bound; it does not assert them.

For a genuine sixth-moment result
[
  \sum_{\mathfrak m}|T_{\mathfrak m}|^6\le C(DU^{1/2}+U^3),
]
the resulting squared-energy RHS has the **cube root**:
[
  \left|\sum b_{\mathfrak m}T_{\mathfrak m}\right|^2
  \le \|b\|_{6/5}^2\,C^{1/3}(DU^{1/2}+U^3)^{1/3}.
]
The (\ell^{6/5}) estimate MUST be proven on the post-compensation coefficients. In the original Gauss/Poisson statement the above moments, the scaling (D^{5/3}Z^{-2\sigma}), the sixth-frequency diagonal and each boundary term require ORIGINAL source-specific theorems. An upstream original Lean declaration named `SexticPoissonGaussBound` was **not found** in the pinned code audit; it must not be assumed already available merely because the original project contains Gauss and quadratic-sieve primitives. `vf919FiniteIdealRow_sixthPower_column` is a finite subset-mask identity; its own documentation says arbitrary physical weights survive at their product norm.

## Source-true final certificate (still open)

Using PR #1005's already formally regrouped `originalOAI_gaussian_fiber_equals_sextic_defect`, establish original effective ideal classes and the actual phase gate. Then prove **two separate** estimates
[
D_{\rm comp}\le c_1\mathcal T(Z),\quad
|\mathcal D_{\rm 6-sec}|\le c_2\mathcal T(Z),
\quad c_1+c_2\le1,
\]
where (\mathcal T(Z)=Z^{2(\beta-11/16-\sigma)}\sum_u\omega_uB_u^2).
The native budget theorem then yields (E\le\mathcal T(Z)).
The finite algebra is now explicit; the two required uniform arithmetic savings are not to be imported from the terminal desired high-row bound.

## 2A. Stronger source-backed principal payment via the actual OAI bound

The earlier generic `raw=residue+tail` identity is NOT the strongest available source statement. Original `Detector/PrincipalNormalized.lean::actual_ray_principal_comparison` already bounds the NORMALIZED principal-row source against the actual `HeckeSignal.signal` by
\[
 C\left(Z^{\beta-11/16-17/48000+\nu}
          +Z^{\beta-11/16+e-(7/8)\ell_{\min}}\right)
\]
under its fully explicit original source window, ray-ideal, Schwartz and beta geometry hypotheses. Do NOT replace those hypotheses with a fictitious shift to real part (1/2-\sigma).

New native theorems in `research/VF_919_OAI_PRINCIPAL_SOURCE_EXPONENT_BUDGET_20261022.lean` prove that both original terms fit (2C Z^{\beta-11/16-\sigma}) for (Z\ge1) **exactly when the sufficient margin constraints**
\[
 \sigma+\nu\le17/48000,
 \qquad \sigma+e\le(7/8)\ell_{\min}
\]
are supplied. The new theorem `oai_original_principal_source_error_fits_high_row` consumes the original source estimate as a VISIBLE hypothesis and pays the explicit factor 2. This is a valid, noncircular source-level principal comparison under original source prerequisites. The remaining proof must instantiate the original `actual_ray_principal_comparison` with the selected PR #1005 parameters and account for its principal source vs grouped-fiber identification, rather than assuming its own analytic estimate.

## 4. Separate principal residual, exact NNS mixed covariance and source-honest l65 cost (Oct 22)

New Lean sources:
- `research/VF_919_OAI_NNS_PRINCIPAL_NONPRINCIPAL_CROSS_20261022.lean`:
  `nns_energy_principal_nonprincipal_exact`, `nns_principal_nonprincipal_cross_le_geometric`, `nns_energy_principal_nonprincipal_root_bound`, and
  `nns_energy_principal_nonprincipal_bound`.
- `research/VF_919_OAI_COMPENSATED_TWO_BILL_L65_20261022.lean`:
  `oai_grouped_fiber_l65_bound` and `oai_grouped_fiber_l65_power_budget`.
- `research/VF_919_OAI_NNS_POST_GROUPED_SEXTIC_DUAL_20261022.lean`:
  `oai_nonprincipal_energy_eq_grouped_dual`, `oaiUniformCompensatedSixthMoment`, and `oai_nonprincipal_energy_bound`.

**Principal cross:** with the original row-constant normalized physical principal source (P_u/\mathrm{normer}), the actual inverse-Mellin signal (S_u), and the already compensated nonprincipal source (H_u), let (R_u=P_u/\mathrm{normer}-S_u). For nonnegative original weights \(\omega\),
\[
 E(R+H)=E_R+E_H+2\Re\sum_u\omega_u R_u\overline{H_u}
 \le(\sqrt{E_R}+\sqrt{E_H})^2.
\]
The norm bounds have to be `E_R <= cR²*T`, `E_H <= cH²*T`, and `cR+cH <= 1`. Merely `E_R <= cR*T`, `E_H <= cH*T`, `cR+cH <= 1` does NOT suffice in general. The source-level principal comparison bounds one physical normalized signal norm at parameter Z; a theorem that turns it into the whole `sum_u omega_u |R_u|²` is still required wherever the rows index a separate source family.

**Two-bill l65:** for each effective compensated ideal \(\mathfrak m\), define the original source-identifiable shift and Euler residuals (b_{\rm shift}, b_{\rm Euler}). Suppose \(\tau_S\) is the actual nonnegative representation multiplicity and source-specific estimates prove
\[
 |b_{\rm shift}(\mathfrak m)|\le A_{\rm shift}\tau_S(\mathfrak m),\quad
 |b_{\rm Euler}(\mathfrak m)|\le A_{\rm Euler}\tau_S(\mathfrak m).
\]
The kernel theorem then proves, by actual rpow algebra,
\[
\|b_{\rm shift}+b_{\rm Euler}\|_{6/5}
\le(A_{\rm shift}+A_{\rm Euler})\|\tau_S\|_{6/5}.
\]
Under the further **independent arithmetic inputs**
\[
 A_{\rm shift}+A_{\rm Euler}\le D^{-1/2}Z^{-\sigma},
 \qquad\|\tau_S\|_{6/5}\le D^{5/6+c},
\]
it gives \(\|b\|_{6/5}\le D^{1/3+c}Z^{-\sigma}\). Neither the local compensation identity nor the ideal-ball counting lemma establishes these two inputs alone.

**Critical original window audit:** original `ProbePrincipalNormalized.actual_ray_principal_comparison` assumes `support (W j) ⊆ Ioo c d` for fixed `0<c≤d` and slot norms \(N(P)\asymp Z^{\ell_j}\) in \([c Z^{\ell_j},d Z^{\ell_j}]\). This is **not** automatically a narrow band of relative width \(O(Z^{-\sigma})\). A mean value theorem gives a factor (\eta_P\) only if the actual parent-child window-alignment displacement is independently shown \(\ll\eta_P=O(Z^{-\sigma})\) uniformly, including derivatives and all normalization factors. That source theorem is OPEN.

**Counting/multiplicity audit:** `CenteredMomentCounting.norm_tsum_ideal_ball` is an absolute IDEAL SUM NORM bound `‖∑' f‖≤128 M H`, proved by invoking `DescentFiberCost.finite_ideal_count_real` internally. Its conclusion is NOT a ready-made sixth-power bound on the representation multiplicities. The additional `sum tau^(6/5)` moment must be proved from the original marked-prime pool geometry (or bounded via a separate maximum-multiplicity/count argument), not replaced with the ordinary mean of tau, since \(x\mapsto x^{6/5}\) is convex.

**Post-compensation sixth-moment dual:** for a row-INDEPENDENT grouped coefficient (b(\mathcal C)\) and a fully source-admitted complex character phase \(\psi_{\mathcal C}(u)\), the exact dual energy is
\[
E_H=\sum_{\mathcal C}b(\mathcal C)
    \sum_u\omega_u\psi_{\mathcal C}(u)\overline{H_u}.
\]
The duality theorem proves an (E_H\le (A K)^2) estimate from the grouped (\ell^{6/5}\) bound (A) and **uniform** sixth-root moment operator bound
\[
\left(\sum_{\mathcal C}
\left|\sum_u\omega_u\psi_{\mathcal C}(u)\overline{\gamma_u}\right|^6\right)^{1/6}
\le K\left(\sum_u\omega_u|\gamma_u|^2\right)^{1/2}
\quad\text{for ALL }\gamma.
\]
This exact proof does not require (R_u\) to admit any sextic phase decomposition and keeps every original weight. It makes explicit that actual OAI physical coefficients must first be grouped and factored into (u\)-independent (b(\mathcal C)\) and the phase \(\psi_{\mathcal C}(u)\) (possibly via genuine sixth-power mask expansion) before applying the uniform moment estimate. The Gauss/Poisson bound for the actual family remains open and is NOT imported from the final high-row target.

**CI acceptance:** Both native and mixed OAI Lean workflows now include these three new modules. Do not mark them kernel-proved until warning-fatal GitHub Actions accepts their exact versions.

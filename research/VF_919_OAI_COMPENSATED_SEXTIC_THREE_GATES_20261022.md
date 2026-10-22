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

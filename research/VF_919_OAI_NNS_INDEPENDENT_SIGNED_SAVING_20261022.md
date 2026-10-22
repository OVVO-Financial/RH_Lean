# OpenAI high-row saving in signed NNS coordinates: exact closure target and independent finite payment

**Reference authority:** upstream OpenAI `PrimeRows/HighFromMoments.lean`, `Detector/GaussianCommon.lean`, `Moments/DetectorPlainFiberSource.lean`, `Detector/DetectorPlainMarkedFineField.lean`. RH_Lean PR #1004 already kernel-compiles the type-correct complete Gaussian-to-NNS identity with original OAI source.

## 1. What must be proved (with ORIGINAL source)

Let (Z>1), (eta=mathrm{HeckeZeroSupremum.beta}), (sigma>0), and (alpha=eta-11/16-sigma). For each original high-row datum (u), the exact OpenAI complete source is
[
F_u=sum_{Jsubseteqmathrm{Fin},N}
  rac{A_{J,u}}{mathrm{normer}_u} - mathrm{principalSignal}_u,
]
where (A_{J,u}) includes the **entire** `compensationSubsetWeight * compensationRowTest * selectedSlotFactor * gaussianJointDensity` sum over labelled selected tuples, all original masks, (sum_j'int_t), and vertical phases.

With original nonnegative weights (omega_u), set
[
D=sum_uomega_usum_ell |a_{u,ell}|^2,quad
C_{mathrm{off}}=rac12sum_uomega_usum_{ell
e m}
 left[mathrm{Co}_0(x_{u,ell},x_{u,m})+
       mathrm{Co}_0(y_{u,ell},y_{u,m})ight],quad
V_{mathrm{off}}=rac12sum_uomega_usum_{ell
e m}
 left[mathrm{Div}_0(x_{u,ell},x_{u,m})+
       mathrm{Div}_0(y_{u,ell},y_{u,m})ight],
]
where (Phi(a)=(Re a-Im a,Re a+Im a)), including the separate principal correction as one source label. Then #1004 has
[
oxed{E:=sum_uomega_u|F_u|^2=D+C_{mathrm{off}}-V_{mathrm{off}}.}
]

OpenAI's original result is the pointwise (|F_u|le B_u Z^alpha) **under its actual SourceMomentsAt, geometric and conductor assumptions**. Its exact signed NNS consequence is
[
oxed{V_{mathrm{off}}-C_{mathrm{off}}ge
D-Z^{2alpha}sum_uomega_u B_u^2.}
]

This is the **exact desired signed-moment payment**: the positive saving (sigma) in the complex probe becomes a (2sigma) improvement in the second-moment budget. Algebraically this equivalence is proved by `nns_original_sigma_saving_iff_payment` in the new file. It is **not** an independent bound by itself.

## 2. Independent, non-circular cancellation actually proved

The source file `VF_919_OAI_NNS_INDEPENDENT_SIGNED_SAVING_20261022.lean` proves for any complex source atoms (a,b) and both (pm1) character phases, fully in native NNS Co-minus-Div:
[
sum_{	hetain{+1,-1}}
  left(mathrm{Co}_{	heta,mathrm{all}}-
        mathrm{Div}_{	heta,mathrm{all}}ight)
=|a+b|^2+|a-b|^2
=2(|a|^2+|b|^2).
]
This is a **genuinely derived exact cancellation of offdiagonal covariance** from a fully admitted two-phase orbit; no OAI moment inequality or RH hypothesis is used. The same file proves a coherent obstruction: (n) phase-aligned atoms can have energy (n^2), hence NNS realification cannot yield sublinear energy uniformly for arbitrary OAI coefficient families. This is why character orthogonality must be established from original arithmetic admissions and weights.

**Scope:** The two-phase proof is not the original OAI sextic Hecke selected-row family, whose phases and weights are not generally a complete uniform character orbit. It does not supply a global (Z^{-2sigma}) budget, and we cannot claim the original independent 7/8 proof from this module. The original OAI local compensation residual, phase mismatch, dyadic boundary and high-row conductor geometry still have to be paid.

## 3. Specific missing arithmetic lemma, and no substitutions

The substantive missing theorem is
[
sum_uomega_u
 sum_{ell
e m}Re(a_{u,ell}overline{a_{u,m}})
;le;
Z^{2alpha}sum_uomega_uB_u^2-
sum_uomega_usum_ell|a_{u,ell}|^2
]
**directly** from OpenAI's original actual Hecke and Poisson coefficients, with admissible labelled ideals and exact selected masks, using neither `actual_high_probe_from_raw_moments` nor the equivalent `SourceMomentsAt` moment bound as an independent hypothesis. In NNS form this is (V_{mathrm{off}}-C_{mathrm{off}}) payment. All ((j,k)), (j+kle2), all dyadic/high rows, and the partial Gaussian Mellin sources must have uniform constants. A two-slot root-of-unity isometry or a variance on a different rational Möbius carrier does not prove this.

The actual OAI row source `detector_row_eq_source` admits a *different* labelled finite ideal polynomial than the completed smooth Gaussian source; do not equate them without a verified intertwining theorem.

## 4. Acceptance

The native independent partial result is accepted only upon warning-fatal Lean 4.34.1 CI with printed axioms and zero `sorryAx`; the global OAI arithmetic saving remains OPEN until the original labelled weighted signed covariance bound is actually proved, without importing an analytically equivalent high-row conclusion. Keep this PR a draft.

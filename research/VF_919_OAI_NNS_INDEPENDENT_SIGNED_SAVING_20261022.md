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


## 5. Independently re-derived original marked analytic input WITH NNS and a sharper exponent

The same PR now contains `research/oai_434/VF919OriginalMarkedSharpenedSignedNNS.lean`, whose proof directly reproduces (rather than invoking) the proof of original OAI `Detector/DetectorPlainMarkedFineField.lean::source_batch_plain_marked_fine`. It uses precisely the original `PositiveFineSourceInput S mesh`, the original `source_batch_marked_initial`, `CenteredMomentDetectorPlainRelativeClass.energy_eq`, and original profile and height estimates, then inserts RH_Lean's exact real `vf919ActualMarkedMoment_eq_realEnergies` before the analytic comparison.

The original proof relaxes the state exponent `state.width + stageError D` to `1+D.t`. But its `marked_state_admission` proves `state.width=1+delta D`; both `delta D` and `stageError D` are DEFINED as `D.t/4`. Thus the *source-proved exponent* can be retained exactly at

```
state.width + stageError D = 1 + D.t/2
```

and the strengthened native-OAI moment statement is

```
sum_{u in F.rows}
  E_NNS(P_j(u)) * E_NNS(P_k(u)) * E_NNS(physicalProduct(selected,u))
  <= C*(1+height)^J*(Z^d)^(1+D.t/2),
j+k<=2, same original positive fine input, masks, labels, and geometry.
```

This is a **genuine stronger intermediate original-source estimate** if it passes the dedicated combined OAI/RHLean warning-fatal kernel check, and it does not assume `source_batch_plain_marked_fine` or the terminal high-row saving. The improvement is from retaining OpenAI's *original analytic width budget*, **not from an independently proved NNS offdiagonal imbalance**. In particular `PositiveFineSourceInput` remains the stated original analytic premise, and the original OAI transport / inverse / final high-row geometry still must be re-proved if using the stronger intermediate exponent to alter the final (7/8) outcome. Do NOT call this RH or a `Z^{-sigma}` global bound until the entire dependency is closed.

Dedicated CI in `.github/workflows/oai-gaussian-nns-typed-434.yml` checks this theorem inside the combined pinned OAI/RHLean environment and prints axioms.


## 6. No source-admission hypothesis: original detector ideal columns in Co/Div

The PR also introduces `research/oai_434/VF919OriginalDetectorSignedNNS.lean`, importing **both** original OAI `Moments/DetectorPlainFiberSource.lean::detector_row_eq_source` and RHLean `vf919NormalizedColumnSource_NNSCovariance`.

For an actual original OAI `Fiber` and every original (j,k,sigma,t), it defines (Q=mathrm{finiteColumns}(mathrm{fiberPool},F,selected)), (D_U=(U^{F.m})^2prod_{sin selected} U^{F.widths(s)}), and the **genuine** column coefficient
[
a_u(I)=mathrm{fiberCoefficient}(F,eta,selected,j,k,sigma,t,I)cdot
  mathrm{CenteredMomentHeckeExpansion.rowWeight}(eta,mathrm{fixedBadMask},1,u.val,0,I).
]
It then proves directly from OAI's **compiled source equality**, not from a premise asserting arbitrary atoms match,
[
oxed{sum_{uin F.rows}|mathrm{detectorPositiveRow}(u)|^2
=rac1{D_U}sum_usum_{I,Jin Q}
 left[mathrm{Co}_0(Phi(a_u(I)),Phi(a_u(J)))
       -mathrm{Div}_0(Phi(a_u(I)),Phi(a_u(J)))ight]/2.}
]
This preserves all ideal and row labels, original conductor-sensitive Hecke phases, `fixedBadMask`, and normalization. It is a separately sourced detector-polynomial correspondence; **it does not assert** these columns are termwise the same as the completed GaussianSubset height-integrated source of PR #1004.

The dedicated original OAI 4.34.1 combined-kernel CI checks this exact ideal-column theorem and the sharpened refined marked-moment theorem separately. Both remain subject to Lean acceptance at the latest head.

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

## 7. Six-sector mean-defect: exact and nonuniform

Formal Lean: research/VF_919_SEXTIC_SECTOR_MEAN_DEFECT_20261022.lean.

Choose a sixth root zeta with zeta^6=1 and zeta != 1. For a particular genuine ideal pair (a,b), an actual OAI row u may have relative phase zeta^k or zero. Use phase_ab(u): Option (Fin 6); none means zero, not a seventh phase. The row-dependent complex amplitude c_ab(u) retains every selected mask, conductor condition, physical weight and compensated coefficient. Define

  W_ab(k) = sum_{u in rows, phase_ab(u)=some(k)} omega(u) c_ab(u),
  Wbar_ab = (sum_{k=0}^5 W_ab(k))/6.

Then the exact, unconditional finite algebra is

  sum_{u in rows} omega(u)c_ab(u)*phase_ab(u)
    = sum_{k=0}^5 [W_ab(k)-Wbar_ab]*zeta^k.

The mean contribution vanishes because the complete sextic geometric sum is zero. This is an IDENTITY, not a bound on the right-hand side. The proof also aggregates all distinct ordered ideal-pair labels and explicitly retains zero and constant-phase (resonant) cases. For a trivial relative phase, the full mass survives: complete-sector subtraction cannot make it small.

Lean theorem names: sextic_nontrivial_root_geometric_sum_zero, sextic_sector_mean_subtraction, sextic_weighted_sector_reassembly, sextic_weighted_nonuniform_defect_exact, sextic_trivial_character_retains_full_weight, sextic_zero_characters_contribute_zero, sextic_all_labelled_pairs_defect_exact. The real NNS identification is sextic_NNS_cross_pair_eq_real_Hecke_Gram: its Co0-minus-Div0 Hermitian cross-term equals Re(a * conjugate(b)).

The theorem sextic_admitted_offdiagonal_Hecke_pair_defect retains a VISIBLE original-phase-factorization hypothesis: for each actual row and ideal pair, a(u)*conjugate(b(u)) = c(u)*phase(u). It does not infer this factorization from rational ideal norms, and is NOT a proof that the entire Gaussian-Mellin source admits a uniform sextic splitting. That arithmetic identification must be proved from original OAI source declarations.

## 8. Critical source-level normalizer correction

OpenAI's authoritative PrimeRows/HighFromMoments.lean defines the final normalized probe denominator as

  normer = sourceResidueConstant W0 W1 (product of excluded ideals)
           * (Probe.principalScalar Finset.univ Z (1/6)
                (slotMass T (residueWeights W Yp)) : Complex).

Neither expression depends on the internal row u: the actual_high_probe_from_raw_moments conclusion is a SINGLE scalar compensatedPhysicalProbe(eta,...)/normer minus the principal Hecke signal, while u indexes internal moment-source rows. It is INCORRECT to identify normer with a row-dependent product of Stage-II factors G_p + chi_p(u)^(-1) H_p. This also means a high-row scalar normer can be pulled through any complete weighted row-sector sum, rather than charged as row-dependent equidistribution error.

The exact reciprocal identity is source/normer-principal = (source-principal)+(normer^(-1)-1)*source. The source module proves this and proves the corresponding conditional remainder norm inequality; it does NOT assert normer near 1. A claimed local factor bound |E_p-1| <= Norm(p)^(-2*sigma), even if established for some different Stage-II Euler factors, does NOT bound this final normalizer without an exact product identification and nonvanishing control.

At the QUADRATIC level, each normalized ideal pair contributes a(I)*conjugate(a(J)) / |normer|^2, not just 1/normer; the principal subtraction creates additional mixed pairs. Consequently no scalar first-order approximation may silently discard principal/normalizer covariance.

## 9. Analytic acceptance contract

The exact remaining inequality is a bound on SUMS OF ACTUAL signed, row-dependent sector defects, plus the resonant/principal/unpaired boundary terms, sufficient to yield D + Co_off - Div_off <= target(Z). It requires genuine arithmetic control of the actual Hecke relative phases and weights over incomplete conductor boxes. Neither an exact mean-subtraction identity nor arbitrary chosen phases nor a complete uniform toy orbit constitutes the needed power saving.

Proof status: native Lean compilation and OAI combined typechecks are required; global uniform arithmetic saving remains OPEN.

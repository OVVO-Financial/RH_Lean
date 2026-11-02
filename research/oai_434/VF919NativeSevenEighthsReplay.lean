import «research.oai_434.VF919NativeSourceMoments»
import OAI.NumberTheory.DirichletL.Moments.DetectorPlainSlotProfile
import «research.VF_919_SEVEN_EIGHTHS_SIGNED_COVARIANCE_20261019»
import «research.VF_919_SEVEN_EIGHTHS_SQUARE_SHELL_BRIDGE_20261019»

/-!
# The complete original one-to-seven-eighths contraction through RHLean NNS

The terminal conclusion is reconstructed from the original proved analytic
floor/successor, now connected through native UPM/LPM energy states and the
actual native inverse/marked/unmarked moment assembly. No original terminal
nonvanishing result is imported or used as a premise.

The final common-probe and supremum arguments are reproduced below. They keep
the same source, principal signal, positive margins, conductor dependence and
height choices. The uniform source theorem exposes its actual quantifier order.

This is a source-faithful replay using the original analytic lemmas. It does
not independently reprove every imported analytic lemma, improve seven eighths,
or claim a new sharp-window L2 estimate.
-/

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Filter Asymptotics

namespace SevenEighths.RHLeanNativeSevenEighthsReplay

open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
open ProbeFinalAssembly ProbeFinalAssemblyCertifiedBands
open CenteredMomentDetectorPlainMomentParameters
open CenteredMomentDetectorPlainSlotProfile
open CenteredMomentEnergyWidthSchedule
open PrincipalSignalComparison

/-- Same detector family, with the complete native certified band as output. -/
def NNSDetectorCertifiedBands : Prop :=
  ∀ _hβ : (7 / 8 : ℝ) < HeckeZeroSupremum.beta,
  ∀ D : HighData (HeckeZeroSupremum.beta - 7 / 8),
    (∀ j, D.ell j ≤ detectorMesh (HeckeZeroSupremum.beta - 7 / 8) D.t / 200) →
  ∀ F : SourceData D, ∀ bΦ : ℝ, 0 < bΦ →
    NNSCertifiedBand (α := Fin D.N) F.modulus ⊤ le_top
      (fun x => conj (F.W x)) 2 (1 / 4) (9 / 4) bΦ 0 1
      (33 / 50) (33 / 50) 2 (kappaPlain D) (stageError D)
      (count 2 (stageError D))

theorem nnsDetectorCertifiedBands_iff :
    NNSDetectorCertifiedBands ↔ DetectorCertifiedBands := by
  simp only [NNSDetectorCertifiedBands, DetectorCertifiedBands, nnsCertifiedBand_iff]

/-- The native floor and every native successor are live dependencies here.
All original parameter inequalities are discharged, not supplied by a user. -/
theorem native_detector_bands : NNSDetectorCertifiedBands := by
  intro hβ D _hfine F bΦ hbΦ
  have hp := fixed_parameters D
  apply nns_terminal_certificate (α := Fin D.N) F.modulus ⊤ le_top
    (fun x => conj (F.W x)) 1 2 (1 / 4) (9 / 4) bΦ 0 1
    (33 / 50) (33 / 50) 2 (kappaPlain D) (stageError D)
  · norm_num
  · exact conjugate_source_support F
  · exact Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hbΦ
  · norm_num
  · norm_num
  · exact hp.2.2.2.2.1.le
  · exact hp.2.2.1
  · linarith
  · unfold kappaPlain
    linarith

/-- Native source moments, with all analytic input discharged by the actual
induction. The positive and zero slots remain jointly accounted for. -/
theorem native_fine_moments : NativeFineMomentInput :=
  native_fine_moments_of_certified
    (nnsDetectorCertifiedBands_iff.mp native_detector_bands)

/-- Explicit uniformity: J precedes eta, C precedes tau, and the threshold
precedes every moving row, batch, bin, selected subset and height argument
inside NativeSourceMomentBound. C may depend on eta; Z0 may depend on tau. -/
theorem native_uniform_source_moments
    (hβ : (7 / 8 : ℝ) < HeckeZeroSupremum.beta)
    (D : HighData (HeckeZeroSupremum.beta - 7 / 8))
    (hfine : ∀ j, D.ell j ≤
      detectorMesh (HeckeZeroSupremum.beta - 7 / 8) D.t / 200)
    (F : SourceData D) (counts : CountParameters F.modulus ⊤ D.t) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ η : Character, ∃ C : ℝ, 0 < C ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∃ Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
        NativeSourceMomentBound F counts η Z τ
          (C * (1 + Z ^ (2 * τ)) ^ J) (Z ^ (2 * τ)) := by
  have hcert := (nnsDetectorCertifiedBands_iff.mp native_detector_bands) hβ D hfine F
  obtain ⟨hp, hz⟩ := plain_inputs F hcert
  have hΔ : 0 < HeckeZeroSupremum.beta - 7 / 8 := by linarith
  obtain ⟨J, hJ, hsource⟩ := native_source_moments F counts
    (detectorMesh (HeckeZeroSupremum.beta - 7 / 8) D.t)
    (detectorMesh_pos hΔ D.t_pos) hfine hp hz
  refine ⟨J, hJ, ?_⟩
  intro η
  obtain ⟨C, hC, hb⟩ := hsource η
  refine ⟨C, hC, ?_⟩
  intro τ hτ hτ1
  obtain ⟨Z₀, hZ₀⟩ := Filter.eventually_atTop.mp (hb τ hτ hτ1)
  refine ⟨max 1 Z₀, le_max_left _ _, ?_⟩
  intro Z hZ
  exact hZ₀ Z ((le_max_right _ _).trans hZ)

/-- Reconstruct both estimates of the SAME compensated probe from native
moments. The height is chosen after the polynomial degree, as required. -/
theorem native_uniform_common_probe : HeckeCommonProbe.UniformCommonProbe := by
  intro hβ
  have hchosen := chosen_input_of_fine (nativeFineMomentInput_iff.mp native_fine_moments)
  obtain ⟨D, F, counts, J, hJ, hmom⟩ := hchosen hβ
  obtain ⟨τ, hτ, hτd, hτcost, hτt, hτ2, hτeps, hsource⟩ :=
    chosen_data_height D F counts J hJ hmom
  obtain ⟨C, hC, hhigh⟩ :=
    fixed_high_bound hβ D F counts τ hτ hτd hτcost hτt hτ2 hτeps
  let loss := (HeckeZeroSupremum.beta - 7 / 8) / 2
  have hloss : 0 < loss := by dsimp [loss]; linarith
  have hlossgap : loss < HeckeZeroSupremum.beta - 7 / 8 := by
    dsimp [loss]; linarith
  refine ⟨loss, D.sigma, hloss, hlossgap, D.sigma_pos, ?_⟩
  intro η _hprimitive
  obtain ⟨hmask, hH, hHbound⟩ := actual_source_analytic F.S F.exclusions η
  refine ⟨η.excludePrimes F.S F.exclusions.prime, sourceCorrection η F.S,
    F.probe η, hmask, hH, hHbound, F.probe_low loss hloss η, ?_⟩
  obtain ⟨Ct, hCt, hhigh⟩ := hhigh η
  obtain ⟨Cm, hCm, hsource⟩ := hsource η
  apply isBigO_rpow_of_eventual_norm_bound
  refine ⟨Ct + C * Cm * (η.modulus.absNorm : ℝ) ^ (2 * D.eps),
    by positivity, ?_⟩
  filter_upwards [hhigh, hsource] with Z hh hs
  exact hh Cm hCm.le hs

/-- The actual contraction: the initial beta <= 1 is used only in the
original signal theorem; the conclusion beta <= 7/8 is proved here from
the native common probe and a zero arbitrarily near the supremum. -/
theorem native_beta_le_seven_eighths : HeckeZeroSupremum.beta ≤ 7 / 8 := by
  by_contra hn
  obtain ⟨omegaMargin, σ, hω0, hω, hσ, hcontract⟩ :=
    native_uniform_common_probe (lt_of_not_ge hn)
  have hmargin := Supremum.continuationMargin_pos hω hσ
  have hboundary :=
    Supremum.continuation_boundary_gt (β := HeckeZeroSupremum.beta) (σ := σ) hω0
  obtain ⟨η, ρ, hp, hhalf, _hstrip, hpole, hz, hnear⟩ :=
    HeckePrimitiveSupremum.exists_primitive_zero_near_beta hmargin (by linarith)
  obtain ⟨χ, H, J, hmask, hH, hb, hJ, herr⟩ := hcontract η hp
  have hχpole : ρ ≠ 1 ∨ χ.residue ≠ 1 := by
    rcases hpole with h1 | hη
    · exact Or.inl h1
    · exact Or.inr
        (fun hc => hη ((HeckeFiniteDeletion.principal_iff_of_mask χ η hmask).mp hc))
  have hzχ : LFunction χ ρ = 0 := by
    rw [HeckeFiniteDeletion.LFunction_eq_of_mask_nonpole χ η hmask
      (by linarith) hχpole, hz, zero_mul]
  apply (HeckeSignal.nonzero_of_probe_bounds χ H J HeckeZeroSupremum.beta omegaMargin σ
    (-11 / 16) HeckeZeroSupremum.beta_le_one hω0 hω hσ hH hb
    ?_ ?_ hnear hχpole) hzχ
  · convert hJ using 1 <;> ring_nf
  · convert herr using 1 <;> ring_nf

theorem native_hecke_nonzero (χ : Character) (s : ℂ)
    (hs : (7 / 8 : ℝ) < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    LFunction χ s ≠ 0 :=
  HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ
    (native_beta_le_seven_eighths.trans_lt hs) hpole

theorem native_dirichlet_nonzero (q : ℕ) (hq : q ≠ 0)
    (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : (7 / 8 : ℝ) < s.re) (hexc : ¬ (χ = 1 ∧ s = 1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction χ s ≠ 0 := by
  let : NeZero q := ⟨hq⟩
  exact HeckeDirichlet.dirichlet_seven_eighths_of_hecke native_hecke_nonzero χ s hs hexc

theorem native_zeta_nonzero (s : ℂ) (hs : (7 / 8 : ℝ) < s.re) :
    riemannZeta s ≠ 0 :=
  HeckeDirichlet.zeta_seven_eighths_of_hecke native_hecke_nonzero s hs

#print axioms native_detector_bands
#print axioms native_fine_moments
#print axioms native_uniform_source_moments
#print axioms native_uniform_common_probe
#print axioms native_beta_le_seven_eighths
#print axioms native_hecke_nonzero
#print axioms native_dirichlet_nonzero
#print axioms native_zeta_nonzero

end SevenEighths.RHLeanNativeSevenEighthsReplay
end
end OAI

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

open MertensExponent
open OAI.SevenEighths.RHLeanNativeSevenEighthsReplay

/-- The initial native exponent one, on the identical physical carrier. -/
theorem nativeReplay_initial_signed_energy (x : ℕ) :
    realMertensDiagonal (x + 1) + 2 * realMertensPositiveLagPairSum (x + 1) ≤
      (x : ℝ) ^ 2 := by
  rw [← vf919_mertens_sq_eq_signedPair]
  exact pow_le_pow_left₀ (norm_nonneg _) (mertens_norm_le x) 2

/-- No analytic hypothesis remains: the proof above supplies nonvanishing. -/
theorem nativeReplay_signed_covariance : VF919SevenEighthsSignedCovarianceBound :=
  vf919_sevenEighthsSignedCovariance_of_zetaNonzero native_zeta_nonzero

theorem nativeReplay_mertens_growth : MertensGrowthAtMost ((7 : ℝ) / 8) :=
  vf919_sevenEighthsSignedCovariance_iff_mertensGrowth.mp nativeReplay_signed_covariance

/-- Explicit native quadratic contraction x^2 -> x^(7/4+epsilon), uniform
over ALL physical prefix lengths. The exact squarefree diagonal is retained. -/
theorem nativeReplay_signed_energy_seven_fourths (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : ℕ, 1 ≤ x →
      realMertensDiagonal (x + 1) + 2 * realMertensPositiveLagPairSum (x + 1) ≤
        A * (x : ℝ) ^ ((7 : ℝ) / 4 + ε) := by
  obtain ⟨C, hC, hbound⟩ := nativeReplay_signed_covariance (ε / 2) (by positivity)
  refine ⟨C ^ 2, sq_nonneg C, ?_⟩
  intro x hx
  calc
    _ ≤ (C * (x : ℝ) ^ ((7 : ℝ) / 8 + ε / 2)) ^ 2 := hbound x hx
    _ = C ^ 2 * (x : ℝ) ^ ((7 : ℝ) / 4 + ε) := by
      rw [mul_pow, show (7 : ℝ) / 4 + ε = ((7 : ℝ) / 8 + ε / 2) * 2 by ring,
        Real.rpow_mul (Nat.cast_nonneg x), Real.rpow_two]

/-- Unit-scale version of the same contraction; both normalization factors
are restored exactly, so this is a power saving of one quarter in energy. -/
theorem nativeReplay_normalized_signed_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : ℕ, 1 ≤ x →
      (realMertensDiagonal (x + 1) + 2 * realMertensPositiveLagPairSum (x + 1)) /
          (x : ℝ) ^ 2 ≤ A * (x : ℝ) ^ (-(1 : ℝ) / 4 + ε) := by
  obtain ⟨A, hA, hbound⟩ := nativeReplay_signed_energy_seven_fourths ε hε
  refine ⟨A, hA, ?_⟩
  intro x hx
  have hxpos : 0 < (x : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hx)
  apply (div_le_iff₀ (sq_pos_of_pos hxpos)).mpr
  calc
    _ ≤ A * (x : ℝ) ^ ((7 : ℝ) / 4 + ε) := hbound x hx
    _ = (A * (x : ℝ) ^ (-(1 : ℝ) / 4 + ε)) * (x : ℝ) ^ 2 := by
      rw [show (7 : ℝ) / 4 + ε = (-(1 : ℝ) / 4 + ε) + 2 by ring,
        Real.rpow_add hxpos, Real.rpow_two]
      ring

/-- All square shells below K, with every cross-shell covariance inside the
square; the all-scale constant is independent of K. -/
theorem nativeReplay_all_square_blocks (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℕ, 2 ≤ K →
      (∑ R ∈ Finset.range K, vf919SquareShellSum R) ^ 2 ≤
        (C * Real.rpow (((K ^ 2 - 1 : ℕ) : ℝ))
          ((7 : ℝ) / 8 + ε)) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := nativeReplay_signed_covariance ε hε
  refine ⟨C, hC, ?_⟩
  intro K hK
  have hKsq : 2 ≤ K ^ 2 := by nlinarith
  have hX : 1 ≤ K ^ 2 - 1 := by omega
  have hsucc : (K ^ 2 - 1 : ℕ) + 1 = K ^ 2 := by omega
  have hb := hbound (K ^ 2 - 1) hX
  rw [hsucc] at hb
  calc
    _ = realMertensLength (K ^ 2) ^ 2 := by rw [vf919SquareShell_telescope]
    _ = realMertensDiagonal (K ^ 2) +
        2 * realMertensPositiveLagPairSum (K ^ 2) :=
      realMertensLength_sq_eq_diagonal_add_two_mul_positiveLagPairSum _
    _ ≤ _ := hb

#print axioms nativeReplay_initial_signed_energy
#print axioms nativeReplay_signed_covariance
#print axioms nativeReplay_mertens_growth
#print axioms nativeReplay_signed_energy_seven_fourths
#print axioms nativeReplay_normalized_signed_energy
#print axioms nativeReplay_all_square_blocks

end RHLean.Analysis


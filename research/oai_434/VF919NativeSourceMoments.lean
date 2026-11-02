import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCertifiedBands
import «research.oai_434.VF919OriginalMarkedSharpenedSignedNNS»
import «research.oai_434.VF919NativeEnergyInduction»

/-!
Native real/NNS moments on the literal original arithmetic rows. The marked
supplier is RHLean's retained-width source proof. Other analytic suppliers
are the original source theorems, transported without changing their rows,
profiles, normalization, or quantifier order. No terminal nonvanishing
theorem or FinalAssemblyUnconditional import is used.
-/

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter Set

namespace SevenEighths.RHLeanNativeSevenEighthsReplay

open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorCoefficientTransfer
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open ProbeHighRowFamily ProbeFinalAssembly Parameters
open CenteredMomentEnergyBands CenteredMomentEnergyState
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyWidthSchedule CenteredMomentDetectorPlainMomentParameters
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open ProbeDetectorPlainMarkedFineField ProbeDetectorPlainUnmarkedField
open ProbeFinalAssemblyCertifiedBands
open RHLean.Analysis

local notation "O" => HeckeFamily.O

def NativeRawMoment (data : RowData) (W : ℝ → ℂ) (c κ C : ℝ) : Prop :=
  ∀ H D : ℝ, 1 ≤ H → 0 < D → D ^ (1 + c) ≤ H →
    ∀ rows : Finset NonzeroElement,
      (∀ v ∈ rows, ((Ideal.span {v.val}).absNorm : ℝ) ≤ H) →
      (∑ v ∈ rows,
        nativePartialSecond (polynomial (data.character v) true W D 0 0)) ≤
          C * H * (H * max 1 D) ^ κ

theorem nativeRawMoment_iff (data : RowData) (W : ℝ → ℂ) (c κ C : ℝ) :
    NativeRawMoment data W c κ C ↔ RawMoment data W c κ C := by
  simp only [NativeRawMoment, RawMoment, nativePartialSecond_eq_normSq]

section FiberMoments

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

structure NativeMoments (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (Δ c κ C height εm : ℝ) : Prop where
  inverse_raw : ∀ n : ℕ, n ≤ 2 → ∀ s ∈ Icc (0 : ℝ) 1,
    ∀ t ∈ Icc (-height) height,
    let W := twistProfile (logTest (orientedProfile F.reverse F.inverseProfile) n) s t
    NativeRawMoment F.rowData W c κ C ∧
      NativeRawMoment F.rowData (scaleProfile W) c κ C
  inverse_marked : ∀ selected : Finset Slot, selected ⊆ F.slots →
    F.r + 2 * (∑ s ∈ selected, F.widths s) < 1 →
    2 * F.r + 8 * (∑ s ∈ selected, F.widths s) < 3 →
    ∀ n : ℕ, n ≤ 2 → ∀ s ∈ Icc (0 : ℝ) 1,
    ∀ t ∈ Icc (-height) height,
      (∑ u ∈ F.rows,
        nativePartialSecond
          (polynomial (F.family u F.label) true
            ((logProfile^[n]) F.inverseProfile) (U ^ F.r) s t *
              F.physicalProduct selected u)) ≤ C * U ^ (1 + εm)
  plain_marked : ∀ selected : Finset Slot, selected ⊆ F.slots →
    2 * F.m + 6 * (3 / 4 + 2 * Δ) * (∑ s ∈ selected, F.widths s) ≤ 1 →
    ∀ j k : ℕ, j + k ≤ 2 → ∀ s ∈ Icc (0 : ℝ) 1,
    ∀ t ∈ Icc (-height) height,
      (∑ u ∈ F.rows,
        nativePartialSecond
          (polynomial (F.family u F.label) false
            ((logProfile^[j]) positiveAnnular) (U ^ F.m) s t *
           polynomial (F.family u F.label) false
            ((logProfile^[k]) positiveAnnular) (U ^ F.m) s t *
           F.physicalProduct selected u)) ≤ C * U ^ (1 + εm)
  plain_unmarked : ∀ j k : ℕ, j + k ≤ 2 → ∀ s ∈ Icc (0 : ℝ) 1,
    ∀ t ∈ Icc (-height) height,
      (∑ u ∈ F.rows,
        nativePartialSecond
          (polynomial (F.family u F.label) false
            ((logProfile^[j]) positiveAnnular) (U ^ F.m) s t *
           polynomial (F.family u F.label) false
            ((logProfile^[k]) positiveAnnular) (U ^ F.m) s t)) ≤
              C * U ^ (max 1 (2 * F.m) + εm)

theorem nativeMoments_iff (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (Δ c κ C height εm : ℝ) :
    NativeMoments F Δ c κ C height εm ↔ Moments F Δ c κ C height εm := by
  constructor
  · intro h
    constructor
    · intro n hn s hs t ht
      obtain ⟨h₁, h₂⟩ := h.inverse_raw n hn s hs t ht
      exact ⟨(nativeRawMoment_iff _ _ _ _ _).mp h₁,
        (nativeRawMoment_iff _ _ _ _ _).mp h₂⟩
    · intro selected hselected hfirst hsecond n hn s hs t ht
      simpa only [nativePartialSecond_eq_normSq] using
        h.inverse_marked selected hselected hfirst hsecond n hn s hs t ht
    · intro selected hselected hcap j k hjk s hs t ht
      simpa only [nativePartialSecond_eq_normSq] using
        h.plain_marked selected hselected hcap j k hjk s hs t ht
    · intro j k hjk s hs t ht
      simpa only [nativePartialSecond_eq_normSq] using
        h.plain_unmarked j k hjk s hs t ht
  · intro h
    constructor
    · intro n hn s hs t ht
      obtain ⟨h₁, h₂⟩ := h.inverse_raw n hn s hs t ht
      exact ⟨(nativeRawMoment_iff _ _ _ _ _).mpr h₁,
        (nativeRawMoment_iff _ _ _ _ _).mpr h₂⟩
    · intro selected hselected hfirst hsecond n hn s hs t ht
      simpa only [nativePartialSecond_eq_normSq] using
        h.inverse_marked selected hselected hfirst hsecond n hn s hs t ht
    · intro selected hselected hcap j k hjk s hs t ht
      simpa only [nativePartialSecond_eq_normSq] using
        h.plain_marked selected hselected hcap j k hjk s hs t ht
    · intro j k hjk s hs t ht
      simpa only [nativePartialSecond_eq_normSq] using
        h.plain_unmarked j k hjk s hs t ht

end FiberMoments

section SourceMoments

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

def NativeSourceMomentsAt {N : ℕ} (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (η : Character) (rows : Finset FreeRow) (ell : Fin N → ℝ) (W : Fin N → ℝ → ℂ)
    (Z d a ε τ dmax b slotMesh binWidth : ℝ) (i : ℕ) (z : ℂ)
    (Δ c κ C height εm : ℝ) : Prop :=
  ∀ q : ℝ, ∀ B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
      (Z ^ d) a ε (HeckeDetectorAdaptiveCutoff.cutoff (2 * a - 1) q)
      (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) i,
    B.rows ⊆ rows → B.data = sourceMomentData M H hH S hS η →
    B.reverse = sourceMomentReverse M H → B.slots = Finset.univ →
    B.widths = (fun j => ell j / d) → B.profile = W →
    B.upper = (fun _ => b) → B.external = (fun _ => z) →
    B.mesh = slotMesh → B.binWidth = binWidth →
    (∀ u ∈ B.rows, ∀ j,
      B.family u j = sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j) →
    ∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
      NativeMoments (B.fiber bin j J K hne) Δ c κ C height εm

theorem nativeSourceMomentsAt_iff {N : ℕ} (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (η : Character) (rows : Finset FreeRow)
    (ell : Fin N → ℝ) (W : Fin N → ℝ → ℂ)
    (Z d a ε τ dmax b slotMesh binWidth : ℝ) (i : ℕ) (z : ℂ)
    (Δ c κ C height εm : ℝ) :
    NativeSourceMomentsAt M H hH S hS η rows ell W
      Z d a ε τ dmax b slotMesh binWidth i z Δ c κ C height εm ↔
    SourceMomentsAt M H hH S hS η rows ell W
      Z d a ε τ dmax b slotMesh binWidth i z Δ c κ C height εm := by
  simp only [NativeSourceMomentsAt, SourceMomentsAt, nativeMoments_iff]

end SourceMoments

def NativeSourceMomentBound {Δ : ℝ} {D : HighData Δ} (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t) (η : Character)
    (Z τ C height : ℝ) : Prop :=
  ∀ rows : Finset FreeRow, ∀ d a : ℝ,
    (1 / 200 : ℝ) ≤ d → d ≤ 7 / 8 → 51 / 100 < a → a ≤ 1 →
    (∀ u ∈ rows, u.val ≠ 1 ∧ Z ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
      (ProbePhysical.calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧
      rowNorm u ≤ Z ^ (d - D.t)) →
    ∀ i : ℕ, ∀ z : ℂ, z.re = 17 / 50 → |z.im| ≤ height →
    NativeSourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell
      (fun _ y => (F.w y : ℂ)) Z d a D.ε τ (7 / 8) 2 D.t D.t i z Δ
      (if 2 * a - 1 ≤ 5 / 6 then counts.cB else counts.cH)
      (if 2 * a - 1 ≤ 5 / 6 then counts.kB else counts.kH) C height D.t

theorem nativeSourceMomentBound_iff {Δ : ℝ} {D : HighData Δ} (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t) (η : Character)
    (Z τ C height : ℝ) :
    NativeSourceMomentBound F counts η Z τ C height ↔
      SourceMomentBound F counts η Z τ C height := by
  simp only [NativeSourceMomentBound, SourceMomentBound, nativeSourceMomentsAt_iff]

/-- This is the original FineMomentInput quantifier order, with the native
real/NNS source moments as the actual supplied conclusion. -/
def NativeFineMomentInput : Prop :=
  ∀ _hβ : (7 / 8 : ℝ) < HeckeZeroSupremum.beta,
    ∃ mesh : ℝ → ℝ, (∀ t : ℝ, 0 < t → 0 < mesh t) ∧
    ∀ D : HighData (HeckeZeroSupremum.beta - 7 / 8),
      (∀ j, D.ell j ≤ mesh D.t / 200) →
    ∀ F : SourceData D, ∀ counts : CountParameters F.modulus ⊤ D.t,
    ∃ J : ℝ, 0 ≤ J ∧ ∀ η : Character, ∃ C : ℝ, 0 < C ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ᶠ Z : ℝ in atTop,
        NativeSourceMomentBound F counts η Z τ
          (C * (1 + Z ^ (2 * τ)) ^ J) (Z ^ (2 * τ))

theorem nativeFineMomentInput_iff : NativeFineMomentInput ↔ FineMomentInput := by
  simp only [NativeFineMomentInput, FineMomentInput, nativeSourceMomentBound_iff]

/-- Actual three-supplier assembly. The retained-width RHLean marked proof
is consumed here; its conclusion is used in the final NativeMoments field.
No original final source_moments/fine_moments theorem is invoked. -/
theorem native_source_moments {Δ : ℝ} {D : HighData Δ} (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t) (mesh : ℝ) (hmesh : 0 < mesh)
    (hfine : ∀ j, D.ell j ≤ mesh / 200)
    (hpositive : PositiveFineSourceInput F mesh)
    (hzero : ∃ degree : ℕ, ∃ control : Finset (ℕ × ℕ),
      ∀ η₀ : Character, ∃ A : ℝ, 0 < A ∧ ∀ᶠ U : ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal F) η₀) (1 / 4) (9 / 4)
        radialSupportUpper 0 1 2 (D.t / 4) U degree control A) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ η : Character, ∃ C : ℝ, 0 < C ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ᶠ Z : ℝ in atTop,
        NativeSourceMomentBound F counts η Z τ
          (C * (1 + Z ^ (2 * τ)) ^ J) (Z ^ (2 * τ)) := by
  obtain ⟨Ji, hi⟩ := ProbeDetectorInverseFields.source_batch_inverse_fields
    F.modulus ⊤ le_top F counts
  obtain ⟨Jm, hm⟩ :=
    source_batch_plain_marked_fine_sharper_signed_NNS F mesh hmesh hfine hpositive
  obtain ⟨Ju, hu⟩ :=
    ProbeDetectorPlainUnmarkedRestrictedField.source_batch_plain_unmarked D F hzero
  refine ⟨(Ji + Jm + Ju : ℕ), by positivity, ?_⟩
  intro η
  obtain ⟨Ci, hCi, hi⟩ := hi η
  obtain ⟨Cm, hCm, hm⟩ := hm η
  obtain ⟨Cu, hCu, hu⟩ := hu η
  refine ⟨Ci + Cm + Cu, by positivity, ?_⟩
  intro τ hτ hτ1
  filter_upwards [hi, hm, hu] with Z hi hm hu
  have hZ : 0 < Z := zero_lt_one.trans hi.1
  let height : ℝ := Z ^ (2 * τ)
  have hh : 0 ≤ height := Real.rpow_nonneg hZ.le _
  have hbase : 1 ≤ 1 + height := by linarith
  have hCi' : Ci * (1 + height) ^ Ji ≤
      (Ci + Cm + Cu) * (1 + height) ^ (Ji + Jm + Ju) := by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega))
      (by positivity) (by positivity)
  have hCm' : Cm * (1 + height) ^ Jm ≤
      (Ci + Cm + Cu) * (1 + height) ^ (Ji + Jm + Ju) := by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega))
      (by positivity) (by positivity)
  have hCu' : Cu * (1 + height) ^ Ju ≤
      (Ci + Cm + Cu) * (1 + height) ^ (Ji + Jm + Ju) := by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega))
      (by positivity) (by positivity)
  simp only [Real.rpow_natCast]
  intro rows d a hd hdmax ha hamax hrows i z hz hzim q B
    hB hdata hreverse hslots hwidth hprofile hupper hexternal hslotMesh hbinWidth hfamily
    bin label left right hne
  have hrows' : ∀ u ∈ rows, Z ^ (1 / 100 : ℝ) ≤ rowNorm u :=
    fun u hu => (hrows u hu).2.1
  have hext : ∀ s, (B.external s).re = 17 / 50 := by
    intro s
    rw [hexternal]
    exact hz
  have hheight : ∀ s, |(B.external s).im| ≤ height := by
    intro s
    rw [hexternal]
    exact hzim
  have hinv := hi.2 d hd a D.ε _ _ _ i B hdata hprofile hupper hwidth hext
    bin label left right hne height hh
  have hmarked := hm.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    (fun s => by rw [hupper]) hext bin label left right hne height hh hheight
  have hunmarked := hu.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    bin label left right hne height hh
  have hU : 0 ≤ Z ^ d := Real.rpow_nonneg hZ.le _
  have hUone : 1 ≤ Z ^ d := (source_base_gt_one D Z d hi.1 hd).le
  constructor
  · intro n hn σ hσ t ht
    exact ⟨(nativeRawMoment_iff _ _ _ _ _).mpr
        (rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).1 hCi'),
      (nativeRawMoment_iff _ _ _ _ _).mpr
        (rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).2 hCi')⟩
  · intro selected hselected hfirst hsecond n hn σ hσ t ht
    have hb := (hinv.2 selected hselected hfirst hsecond n hn σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCi' (Real.rpow_nonneg hU _))
    simpa only [nativePartialSecond_eq_normSq] using hb
  · intro selected hselected hcap j k hjk σ hσ t ht
    have hpow : (Z ^ d) ^ (1 + D.t / 2) ≤ (Z ^ d) ^ (1 + D.t) :=
      Real.rpow_le_rpow_of_exponent_le hUone (by linarith [D.t_pos])
    have hb₀ := hmarked selected hselected hcap j k hjk σ hσ t ht
    have hb₁ := hb₀.trans
      (mul_le_mul_of_nonneg_left hpow
        (show 0 ≤ Cm * (1 + height) ^ Jm by positivity))
    have hb₂ := hb₁.trans
      (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg hU _))
    simpa only [nativePartialSecond_eq_normSq, vf919MarkedRealEnergy_eq_normSq,
      norm_mul, mul_pow] using hb₂
  · intro j k hjk σ hσ t ht
    have hb := (hunmarked j k hjk σ hσ t ht).1.trans
      (mul_le_mul_of_nonneg_right hCu' (Real.rpow_nonneg hU _))
    simpa only [nativePartialSecond_eq_normSq] using hb

theorem native_fine_moments_of_certified (h : DetectorCertifiedBands) :
    NativeFineMomentInput := by
  intro hβ
  let Δ := HeckeZeroSupremum.beta - 7 / 8
  have hΔ : 0 < Δ := by dsimp [Δ]; linarith
  refine ⟨detectorMesh Δ, fun t ht => detectorMesh_pos hΔ ht, ?_⟩
  intro D hfine F counts
  obtain ⟨hp, hz⟩ := plain_inputs F (h hβ D hfine F)
  exact native_source_moments F counts (detectorMesh Δ D.t)
    (detectorMesh_pos hΔ D.t_pos) hfine hp hz

theorem native_chosen_moments_of_certified (h : DetectorCertifiedBands) :
    ChosenMomentInput :=
  chosen_input_of_fine
    (nativeFineMomentInput_iff.mp (native_fine_moments_of_certified h))

#print axioms nativeRawMoment_iff
#print axioms nativeMoments_iff
#print axioms nativeSourceMomentBound_iff
#print axioms native_source_moments
#print axioms native_fine_moments_of_certified

end SevenEighths.RHLeanNativeSevenEighthsReplay

end
end OAI

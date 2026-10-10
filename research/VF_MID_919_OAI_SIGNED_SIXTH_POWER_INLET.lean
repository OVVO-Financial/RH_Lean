import Mathlib
import «research.VF_MID_919_OAI_PRINCIPAL_COEFFICIENT_MAP»

/-!
# Finite occurrence-preserving sixth-power inlet

Prime labels remain distinct even when their norms agree.  Thus two prime
ideals above a split rational prime contribute as TWO labels, not one.
The finite free-prime carrier is the squarefree ideal factorization model;
no analytic character estimate or Eisenstein ideal dictionary is assumed.

The amplifier partitions a squarefree column uniquely into the prime labels
meeting the amplifier and the labels avoiding it.  Both complex legs are
expanded before the mixed Gram is formed.  The principal sixth-power rows
are exactly coprimality masks, with no new oscillating phase.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

variable {ι : Type*} [DecidableEq ι]

def vf919IdealLabelNorm (norm : ι → ℕ) (s : Finset ι) : ℕ := ∏ p ∈ s, norm p
def vf919IdealLabelCoefficient (phase : ι → ℂ) (s : Finset ι) : ℂ :=
  ∏ p ∈ s, -phase p
def vf919FiniteIdealRow (P : Finset ι) (norm : ι → ℕ)
    (phase : ι → ℂ) (b : ℕ → ℂ) : ℂ :=
  ∑ s ∈ P.powerset, vf919IdealLabelCoefficient phase s * b (vf919IdealLabelNorm norm s)
def vf919SixthPowerMaskedRow (P A : Finset ι) (norm : ι → ℕ)
    (phase : ι → ℂ) (b : ℕ → ℂ) : ℂ :=
  ∑ s ∈ P.powerset, if Disjoint s A then
    vf919IdealLabelCoefficient phase s * b (vf919IdealLabelNorm norm s) else 0
def vf919NormDilatedWeight (norm : ι → ℕ) (s : Finset ι) (b : ℕ → ℂ) : ℕ → ℂ :=
  fun m => b (vf919IdealLabelNorm norm s * m)

theorem vf919IdealLabelCoefficient_principal (s : Finset ι) :
    vf919IdealLabelCoefficient (fun _ => 1) s = (-1 : ℂ) ^ s.card := by
  simp [vf919IdealLabelCoefficient]

/-- This records the literal sixth-power character effect, including zero
on a prime meeting the amplifier. -/
theorem vf919SixthPower_prime_phase_is_mask (phase z : ℂ) (hit : Prop)
    [Decidable hit] (hz : z ^ 6 = 1) :
    (if hit then 0 else phase * z ^ 6) = if hit then 0 else phase := by
  simp [hz]

theorem vf919SixthPowerMaskedRow_eq_survivorRow
    (P A : Finset ι) (norm : ι → ℕ) (phase : ι → ℂ) (b : ℕ → ℂ) :
    vf919SixthPowerMaskedRow P A norm phase b =
      vf919FiniteIdealRow (P \ A) norm phase b := by
  unfold vf919SixthPowerMaskedRow vf919FiniteIdealRow
  have hsub : (P \ A).powerset ⊆ P.powerset := by
    intro s hs
    exact Finset.mem_powerset.mpr
      ((Finset.mem_powerset.mp hs).trans Finset.sdiff_subset)
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro s hs
    have hdis : Disjoint s A := by
      apply Finset.disjoint_left.mpr
      intro p hp hpA
      exact (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hs hp)).2 hpA
    simp [hdis]
  · intro s hs hsnot
    have hdis : ¬ Disjoint s A := by
      intro h
      apply hsnot
      apply Finset.mem_powerset.mpr
      intro p hp
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_powerset.mp hs hp, fun hpA => Finset.disjoint_left.mp h hp hpA⟩
    simp [hdis]

/-- Exact sixth-power column factorization on the finite squarefree carrier.
The selected divisor and surviving child are recovered uniquely by inter
and sdiff; arbitrary physical weights remain at the product norm. -/
theorem vf919FiniteIdealRow_sixthPower_column
    (P A : Finset ι) (hA : A ⊆ P) (norm : ι → ℕ)
    (phase : ι → ℂ) (b : ℕ → ℂ) :
    vf919FiniteIdealRow P norm phase b =
      ∑ d ∈ A.powerset, vf919IdealLabelCoefficient phase d *
        vf919SixthPowerMaskedRow P A norm phase (vf919NormDilatedWeight norm d b) := by
  simp_rw [vf919SixthPowerMaskedRow_eq_survivorRow]
  unfold vf919FiniteIdealRow vf919NormDilatedWeight
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product]
  apply Finset.sum_bij (fun s _ => (s ∩ A, s \ A))
  · intro s hs
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_powerset.mpr Finset.inter_subset_right
    · apply Finset.mem_powerset.mpr
      intro p hp
      rcases Finset.mem_sdiff.mp hp with ⟨hps, hpA⟩
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_powerset.mp hs hps, hpA⟩
  · intro s hs t ht heq
    have hi := congrArg Prod.fst heq
    have hd := congrArg Prod.snd heq
    ext p
    by_cases hp : p ∈ A
    · have hh := Finset.ext_iff.mp hi p
      simpa [hp] using hh
    · have hh := Finset.ext_iff.mp hd p
      simpa [hp] using hh
  · intro x hx
    rcases Finset.mem_product.mp hx with ⟨hxd, hxm⟩
    have hd : x.1 ⊆ A := Finset.mem_powerset.mp hxd
    have hm : x.2 ⊆ P \ A := Finset.mem_powerset.mp hxm
    refine ⟨x.1 ∪ x.2, Finset.mem_powerset.mpr ?_, ?_⟩
    · intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact hA (hd hp)
      · exact (Finset.mem_sdiff.mp (hm hp)).1
    · apply Prod.ext
      · ext p
        have hnot : p ∈ x.2 → p ∉ A := fun hp => (Finset.mem_sdiff.mp (hm hp)).2
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hp | hp, hpA⟩
          · exact hp
          · exact (hnot hp hpA).elim
        · intro hp
          exact ⟨Or.inl hp, hd hp⟩
      · ext p
        have hnot : p ∈ x.2 → p ∉ A := fun hp => (Finset.mem_sdiff.mp (hm hp)).2
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hp | hp, hpA⟩
          · exact (hpA (hd hp)).elim
          · exact hp
        · intro hp
          exact ⟨Or.inr hp, hnot hp⟩
  · intro s _hs
    have hsplit : s = (s ∩ A) ∪ (s \ A) := by
      ext p
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      tauto
    have hdis : Disjoint (s ∩ A) (s \ A) := by
      apply Finset.disjoint_left.mpr
      intro p hp hq
      exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_inter.mp hp).2
    have hc : vf919IdealLabelCoefficient phase s =
        vf919IdealLabelCoefficient phase (s ∩ A) *
          vf919IdealLabelCoefficient phase (s \ A) := by
      unfold vf919IdealLabelCoefficient
      rw [hsplit, Finset.prod_union hdis]
    have hn : vf919IdealLabelNorm norm s =
        vf919IdealLabelNorm norm (s ∩ A) * vf919IdealLabelNorm norm (s \ A) := by
      unfold vf919IdealLabelNorm
      rw [hsplit, Finset.prod_union hdis]
    rw [hc, hn]
    ring

/-- At the principal row the amplified character contributes ONLY the
survivor mask.  Its surviving Mobius signs remain unchanged. -/
theorem vf919PrincipalSixthPowerRow_eq_maskedMobius
    (P A : Finset ι) (norm : ι → ℕ) (b : ℕ → ℂ) :
    vf919SixthPowerMaskedRow P A norm (fun _ => 1) b =
      ∑ s ∈ P.powerset, if Disjoint s A then
        (-1 : ℂ) ^ s.card * b (vf919IdealLabelNorm norm s) else 0 := by
  simp [vf919SixthPowerMaskedRow, vf919IdealLabelCoefficient_principal]

/-- Retain the ENTIRE complex d,e matrix.  No coefficient mass, absolute
square, supremum, or independent treatment of the legs is used. -/
theorem vf919SignedMixedGram_sixthPower_divisorMatrix
    (P A : Finset ι) (hA : A ⊆ P) (norm : ι → ℕ)
    (phase : ι → ℂ) (H J : ℕ → ℂ) :
    -2 * (vf919FiniteIdealRow P norm phase H *
      star (vf919FiniteIdealRow P norm phase J)).re =
    -2 * (∑ d ∈ A.powerset, ∑ e ∈ A.powerset,
      vf919IdealLabelCoefficient phase d * star (vf919IdealLabelCoefficient phase e) *
      vf919SixthPowerMaskedRow P A norm phase (vf919NormDilatedWeight norm d H) *
      star (vf919SixthPowerMaskedRow P A norm phase (vf919NormDilatedWeight norm e J))).re := by
  have heq : vf919FiniteIdealRow P norm phase H *
      star (vf919FiniteIdealRow P norm phase J) =
      ∑ d ∈ A.powerset, ∑ e ∈ A.powerset,
      vf919IdealLabelCoefficient phase d * star (vf919IdealLabelCoefficient phase e) *
      vf919SixthPowerMaskedRow P A norm phase (vf919NormDilatedWeight norm d H) *
      star (vf919SixthPowerMaskedRow P A norm phase (vf919NormDilatedWeight norm e J)) := by
    rw [vf919FiniteIdealRow_sixthPower_column P A hA norm phase H,
      vf919FiniteIdealRow_sixthPower_column P A hA norm phase J]
    simp only [star_sum, star_mul, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro d _hd
    apply Finset.sum_congr rfl
    intro e _he
    ring
  rw [heq]

end RHLean.Analysis

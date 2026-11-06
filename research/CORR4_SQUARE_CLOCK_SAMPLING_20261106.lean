import Mathlib
import «research.CANONICAL_ROUGH_Q2_TAIL_REDUCTION»

/-!
# Source-faithful CORR4 square-clock sampling

This formalizes the sampling part of 20261106-wheel-1/CP1, independently
accepted in 20261106-referee-1. The actual Mertens prefix, historical prefix,
literal daughter cutoff and strict moving owner mask are retained.

The bounds hold already for x >= 3. The daughter estimate needs only a
positive integer q; the original odd-prime owner specialization is explicit.
These are rounding-error bounds, not the CP2 integrated comparison, the
diagonal estimate, or an upper bound for the full signed CORR4 bill.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- The root whose actual endpoint precedes x, including partial blocks. -/
def corr4SquareClock (x : ℝ) : ℕ := ⌊Real.sqrt (x + 1)⌋₊

private theorem corr4_endpoint_cast {R : ℕ} (hR : 2 ≤ R) :
    (squareRootEndpoint R : ℝ) = (R : ℝ) ^ 2 - 1 := by
  have hsq : 1 ≤ R ^ 2 := by nlinarith
  simp only [squareRootEndpoint, Nat.cast_sub hsq, Nat.cast_pow, Nat.cast_one]

/-- Exact square-clock geometry, with the upper boundary strictly excluded. -/
theorem corr4SquareClock_bounds {x : ℝ} (hx : 3 ≤ x) :
    2 ≤ corr4SquareClock x ∧
      (corr4SquareClock x : ℝ) ^ 2 - 1 ≤ x ∧
      x < ((corr4SquareClock x : ℝ) + 1) ^ 2 - 1 := by
  have hs0 := Real.sqrt_nonneg (x + 1)
  have hs2 := Real.sq_sqrt (show 0 ≤ x + 1 by linarith)
  have hlo := Nat.floor_le hs0
  have hhi := Nat.lt_floor_add_one (Real.sqrt (x + 1))
  change (corr4SquareClock x : ℝ) ≤ Real.sqrt (x + 1) at hlo
  change Real.sqrt (x + 1) < (corr4SquareClock x : ℝ) + 1 at hhi
  have hr0 : (0 : ℝ) ≤ corr4SquareClock x := Nat.cast_nonneg _
  have hsqlo := (sq_le_sq₀ hr0 hs0).mpr hlo
  have hsqhi := (sq_lt_sq₀ hs0 (by positivity)).mpr hhi
  have hr2 : 2 ≤ corr4SquareClock x := by
    by_contra h
    have hr1 : (corr4SquareClock x : ℝ) ≤ 1 := by
      exact_mod_cast (show corr4SquareClock x ≤ 1 by omega)
    have hslt : Real.sqrt (x + 1) < 2 := by linarith
    have hsq : Real.sqrt (x + 1) ^ 2 < (2 : ℝ) ^ 2 :=
      (sq_lt_sq₀ hs0 (by norm_num)).mpr hslt
    nlinarith
  refine ⟨hr2, ?_, ?_⟩
  · nlinarith
  · nlinarith

private theorem corr4_root_scale {R : ℕ} {x : ℝ}
    (hR : 2 ≤ R) (hlo : (R : ℝ) ^ 2 - 1 ≤ x) :
    3 * (R : ℝ) ≤ 4 * Real.sqrt x := by
  have hr : (2 : ℝ) ≤ R := by exact_mod_cast hR
  have hx : 0 ≤ x := by nlinarith
  have hs := Real.sq_sqrt hx
  have hs0 := Real.sqrt_nonneg x
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  nlinarith [sq_nonneg ((R : ℝ) - 2)]

private theorem corr4_real_mertens_variation (a b : ℕ) (hab : a ≤ b) :
    |(mertensSummatoryInt b : ℝ) - (mertensSummatoryInt a : ℝ)| ≤
      ((b - a : ℕ) : ℝ) := by
  have h := norm_mertensSummatory_sub_le a b hab
  rw [← mertensSummatoryInt_cast b, ← mertensSummatoryInt_cast a,
    ← Int.cast_sub, Complex.norm_intCast] at h
  simpa only [Int.cast_sub] using h

private theorem corr4_floor_endpoint_gap {R : ℕ} {x : ℝ}
    (hR : 2 ≤ R) (hlo : (R : ℝ) ^ 2 - 1 ≤ x)
    (hhi : x < ((R : ℝ) + 1) ^ 2 - 1) :
    squareRootEndpoint R ≤ ⌊x⌋₊ ∧
      ⌊x⌋₊ - squareRootEndpoint R ≤ 2 * R := by
  have hX := corr4_endpoint_cast hR
  have hx : 0 ≤ x := (Nat.cast_nonneg (squareRootEndpoint R)).trans (by linarith)
  have hlow : squareRootEndpoint R ≤ ⌊x⌋₊ := Nat.le_floor (by linarith)
  have hfloor := Nat.floor_le hx
  have hu : (⌊x⌋₊ : ℝ) < ((squareRootEndpoint R + 2 * R + 1 : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hun : ⌊x⌋₊ < squareRootEndpoint R + 2 * R + 1 := by exact_mod_cast hu
  exact ⟨hlow, by omega⟩

/-- The historical parent differs from the genuine floor prefix by at most
four square roots. The history M(r-1) is not discarded. -/
theorem corr4_parent_sampling_le {x : ℝ} (hx : 3 ≤ x) :
    |(mertensSummatoryInt (squareRootEndpoint (corr4SquareClock x)) : ℝ) -
        (mertensSummatoryInt (corr4SquareClock x - 1) : ℝ) -
        (mertensSummatoryInt ⌊x⌋₊ : ℝ)| ≤ 4 * Real.sqrt x := by
  let R := corr4SquareClock x
  obtain ⟨hR, hlo, hhi⟩ := corr4SquareClock_bounds hx
  obtain ⟨hX, hgap⟩ := corr4_floor_endpoint_gap hR hlo hhi
  have hv := corr4_real_mertens_variation (squareRootEndpoint R) ⌊x⌋₊ hX
  have hh := corr4_real_mertens_variation 0 (R - 1) (Nat.zero_le _)
  have hm0 : mertensSummatoryInt 0 = 0 := by simp [mertensSummatoryInt]
  simp only [hm0, Int.cast_zero, sub_zero, Nat.sub_zero] at hh
  have hgapR : ((⌊x⌋₊ - squareRootEndpoint R : ℕ) : ℝ) ≤ 2 * (R : ℝ) := by
    exact_mod_cast hgap
  have hhist : ((R - 1 : ℕ) : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast (Nat.sub_le R 1)
  have htri :
      |((mertensSummatoryInt (squareRootEndpoint R) : ℝ) -
          (mertensSummatoryInt ⌊x⌋₊ : ℝ)) -
          (mertensSummatoryInt (R - 1) : ℝ)| ≤
        |(mertensSummatoryInt (squareRootEndpoint R) : ℝ) -
          (mertensSummatoryInt ⌊x⌋₊ : ℝ)| +
          |(mertensSummatoryInt (R - 1) : ℝ)| := by
    simpa only [sub_zero, zero_sub, abs_neg] using
      abs_sub_le ((mertensSummatoryInt (squareRootEndpoint R) : ℝ) -
        (mertensSummatoryInt ⌊x⌋₊ : ℝ)) (0 : ℝ) (mertensSummatoryInt (R - 1) : ℝ)
  rw [abs_sub_comm (mertensSummatoryInt (squareRootEndpoint R) : ℝ)] at htri
  have hscale := corr4_root_scale hR hlo
  change |(mertensSummatoryInt (squareRootEndpoint R) : ℝ) -
      (mertensSummatoryInt (R - 1) : ℝ) -
      (mertensSummatoryInt ⌊x⌋₊ : ℝ)| ≤ _
  have heq : (mertensSummatoryInt (squareRootEndpoint R) : ℝ) -
      (mertensSummatoryInt (R - 1) : ℝ) - (mertensSummatoryInt ⌊x⌋₊ : ℝ) =
      ((mertensSummatoryInt (squareRootEndpoint R) : ℝ) -
        (mertensSummatoryInt ⌊x⌋₊ : ℝ)) -
        (mertensSummatoryInt (R - 1) : ℝ) := by ring
  rw [heq]
  linarith

/-- A literal daughter and the continuously dilated prefix have a controlled
rounding error. The strict cutoff absorbs the division remainder. -/
theorem corr4_daughter_sampling_le {x : ℝ} {q : ℕ}
    (hx : 3 ≤ x) (hq : 0 < q) (hactive : q * q < corr4SquareClock x) :
    |(mertensSummatoryInt (rawQ2ChildCutoff (corr4SquareClock x) q) : ℝ) -
        (mertensSummatoryInt ⌊x / (q : ℝ) ^ 2⌋₊ : ℝ)| ≤
      4 * Real.sqrt x / (q : ℝ) ^ 2 := by
  let R := corr4SquareClock x
  let X := squareRootEndpoint R
  let d := q * q
  let Y := X / d
  let n := ⌊x / (d : ℝ)⌋₊
  have hx0 : 0 ≤ x := by linarith
  have hd : 0 < d := Nat.mul_pos hq hq
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨hR, hlo, hhi⟩ := corr4SquareClock_bounds hx
  have hX : (X : ℝ) = (R : ℝ) ^ 2 - 1 := corr4_endpoint_cast hR
  have hXd : (Y : ℝ) ≤ (X : ℝ) / (d : ℝ) := Nat.cast_div_le
  have hY : Y ≤ n := Nat.le_floor (hXd.trans (div_le_div_of_nonneg_right
    (by linarith : (X : ℝ) ≤ x) hdr.le))
  have hn : (n : ℝ) * (d : ℝ) ≤ x :=
    (le_div_iff₀ hdr).mp (Nat.floor_le (by positivity : 0 ≤ x / (d : ℝ)))
  have hmod := Nat.mod_lt X hd
  have hdiv := Nat.div_add_mod X d
  have hrem : (X : ℝ) < (Y : ℝ) * (d : ℝ) + (d : ℝ) := by
    have hnat : X < Y * d + d := by
      dsimp [Y]
      nlinarith
    exact_mod_cast hnat
  have hact : (d : ℝ) + 1 ≤ R := by
    exact_mod_cast (show d + 1 ≤ R by omega)
  have hvar := corr4_real_mertens_variation Y n hY
  rw [Nat.cast_sub hY] at hvar
  have hgap : (n : ℝ) - (Y : ℝ) ≤ 3 * (R : ℝ) / (d : ℝ) := by
    apply (le_div_iff₀ hdr).mpr
    nlinarith
  have hscale := corr4_root_scale hR hlo
  have hbound := hvar.trans (hgap.trans (div_le_div_of_nonneg_right hscale hdr.le))
  rw [abs_sub_comm] at hbound
  simpa only [Y, n, X, d, R, rawQ2ChildCutoff, Nat.cast_mul, pow_two] using hbound

/-- The moving mask stays literal: an inactive daughter contributes zero on
both sides, including the boundary q*q = r. -/
theorem corr4_masked_daughter_sampling_le {x : ℝ} {q : ℕ}
    (hx : 3 ≤ x) (hq : 0 < q) :
    |(if q * q < corr4SquareClock x then
        (mertensSummatoryInt (rawQ2ChildCutoff (corr4SquareClock x) q) : ℝ)
      else 0) -
      (if q * q < corr4SquareClock x then
        (mertensSummatoryInt ⌊x / (q : ℝ) ^ 2⌋₊ : ℝ) else 0)| ≤
      if q * q < corr4SquareClock x then
        4 * Real.sqrt x / (q : ℝ) ^ 2 else 0 := by
  by_cases h : q * q < corr4SquareClock x
  · simpa only [h, ite_true] using corr4_daughter_sampling_le hx hq h
  · simp only [h, ite_false, sub_self, abs_zero, le_refl]

/-- The original odd-prime owner set is exactly the strict square mask. -/
theorem corr4_mem_lowOwners_iff {R q : ℕ} (hq : Nat.Prime q) (hq2 : q ≠ 2) :
    q ∈ canonicalRoughLowQ2Owners R ↔ q * q < R := by
  constructor
  · intro h
    obtain ⟨hb, hh⟩ := Finset.mem_sdiff.mp h
    exact lt_of_not_ge fun hge => hh (Finset.mem_filter.mpr ⟨hb, hge⟩)
  · intro h
    have hqq : q ≤ q * q := by nlinarith [hq.two_le]
    have hqR : q ≤ R - 1 := by omega
    have hb : q ∈ (primesUpTo (R - 1)).erase 2 :=
      Finset.mem_erase.mpr ⟨hq2, mem_primesUpTo.mpr ⟨hq, hqR⟩⟩
    exact Finset.mem_sdiff.mpr ⟨hb, fun hh =>
      (not_le_of_gt h) (Finset.mem_filter.mp hh).2⟩

/-- Specialization to the actual admitted CORR4 owner population. -/
theorem corr4_lowOwner_sampling_le {x : ℝ} {q : ℕ} (hx : 3 ≤ x)
    (hq : q ∈ canonicalRoughLowQ2Owners (corr4SquareClock x)) :
    |(mertensSummatoryInt (rawQ2ChildCutoff (corr4SquareClock x) q) : ℝ) -
        (mertensSummatoryInt ⌊x / (q : ℝ) ^ 2⌋₊ : ℝ)| ≤
      4 * Real.sqrt x / (q : ℝ) ^ 2 := by
  have hb := Finset.mem_erase.mp (Finset.mem_sdiff.mp hq).1
  have hp := (mem_primesUpTo.mp hb.2).1
  exact corr4_daughter_sampling_le hx hp.pos ((corr4_mem_lowOwners_iff hp hb.1).mp hq)

/-- Exact daughter endpoint at a divisible root; no primality is needed. -/
theorem rawQ2ChildCutoff_eq_squareEndpoint_of_dvd {R q : ℕ}
    (hq : 0 < q) (hdiv : q ∣ R) :
    rawQ2ChildCutoff R q = squareRootEndpoint (R / q) := by
  by_cases hR : R = 0
  · subst R
    simp [rawQ2ChildCutoff, squareRootEndpoint]
  have hRpos : 0 < R := Nat.pos_of_ne_zero hR
  have hd : 0 < q * q := Nat.mul_pos hq hq
  have hr : q * (R / q) = R := by
    simpa only [Nat.mod_eq_zero_of_dvd hdiv, Nat.add_zero] using Nat.div_add_mod R q
  have hk : 0 < R / q := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, mul_zero] at hr
    exact hR hr.symm
  have hsq : R ^ 2 = (R / q) ^ 2 * (q * q) := by
    calc
      R ^ 2 = (q * (R / q)) ^ 2 := by rw [hr]
      _ = (R / q) ^ 2 * (q * q) := by ring
  have hRpred := Nat.sub_add_cancel (show 1 ≤ R ^ 2 by nlinarith)
  have hkpred := Nat.sub_add_cancel (show 1 ≤ (R / q) ^ 2 by nlinarith)
  rw [← hkpred] at hsq
  have heq : R ^ 2 - 1 = ((R / q) ^ 2 - 1) * (q * q) + (q * q) - 1 := by
    have hsum : R ^ 2 - 1 + 1 = ((R / q) ^ 2 - 1) * (q * q) + (q * q) := by
      nlinarith
    omega
  unfold rawQ2ChildCutoff squareRootEndpoint
  apply (Nat.div_eq_iff hd).mpr
  rw [heq]
  constructor
  · omega
  · exact le_rfl

/-- The strict mask excludes q*q and admits the next root. -/
theorem corr4_lowOwner_first_admission {q : ℕ} (hq : Nat.Prime q) (hq2 : q ≠ 2) :
    q ∉ canonicalRoughLowQ2Owners (q * q) ∧
      q ∈ canonicalRoughLowQ2Owners (q * q + 1) := by
  simp only [corr4_mem_lowOwners_iff hq hq2, lt_self_iff_false, not_false_eq_true,
    Nat.lt_succ_self, and_self]

/-- The first admitted daughter's cutoff includes the two restored sites. -/
theorem rawQ2ChildCutoff_first_admission {q : ℕ} (hq : 0 < q) :
    rawQ2ChildCutoff (q * q + 1) q = q * q + 2 := by
  have hd : 0 < q * q := Nat.mul_pos hq hq
  have hs : (q * q + 1) ^ 2 = (q * q + 2) * (q * q) + 1 := by ring
  unfold rawQ2ChildCutoff squareRootEndpoint
  rw [hs, Nat.add_sub_cancel]
  apply (Nat.div_eq_iff hd).mpr
  constructor
  · exact le_rfl
  · omega

end RHLean.Proof

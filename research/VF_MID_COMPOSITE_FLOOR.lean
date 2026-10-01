import Mathlib
import «research.VF_MID_MIDPOINT_COMPLEMENT_DISPERSION»
import RHLean.Analysis.RoughWheelFiniteCounting

/-!
# VF-mid composite-floor attack

This file runs the square-block prime/composite complement in the reverse
direction: prove that sufficiently many sites are composite, and infer an upper
bound on the prime/common-wheel survivor remainder.

For the open square carrier

  R^2 < n < (R+1)^2

there are exactly 2R integer sites and prime/composite sites partition them.
Hence a composite floor and a prime ceiling are literally equivalent.

The second layer uses the repository's finite rough-wheel interval count.
Every prime in the square carrier is coprime to any fixed wheel whose prime
coordinates are at most R.  Thus the 6-, 30-, and 210-wheels give unconditional
composite floors with explicit incomplete-period costs.

These are diagnostic one-sided bounds.  They do not yet have the shrinking
prime-density scale required to match the VF midpoint demand.
-/

noncomputable section

namespace RHLean.Analysis

open RHLean.Proof

/-! ## Exact reverse-complement dictionary -/

/-- A real composite floor on the 2R-site carrier is exactly the complementary
real prime ceiling. -/
theorem vfMidSquareWheel_composite_floor_iff_prime_ceiling
    (R : ℕ) (A : ℝ) :
    (2 * (R : ℝ) - A ≤
        ((vfMidSquareWheelComposites R).card : ℝ)) ↔
      (((vfMidSquareWheelPrimes R).card : ℝ) ≤ A) := by
  have hcardNat := vfMidSquareWheel_prime_card_add_composite_card R
  rw [vfMidSquareWheelSites_card] at hcardNat
  have hcard :
      ((vfMidSquareWheelPrimes R).card : ℝ) +
          ((vfMidSquareWheelComposites R).card : ℝ) =
        2 * (R : ℝ) := by
    exact_mod_cast hcardNat
  constructor <;> intro h <;> linarith

/-- The same dictionary in centered form: lower-bounding composites by their
VF-complement target is identical to upper-bounding prime supply. -/
theorem vfMidSquareWheel_composite_floor_centered_iff
    (R : ℕ) (Q E : ℝ) :
    (2 * (R : ℝ) - Q - E ≤
        ((vfMidSquareWheelComposites R).card : ℝ)) ↔
      (((vfMidSquareWheelPrimes R).card : ℝ) ≤ Q + E) := by
  simpa [sub_sub] using
    (vfMidSquareWheel_composite_floor_iff_prime_ceiling R (Q + E))

/-- **Real VF-mid reverse bridge.**  A composite floor at the midpoint-demand
level is exactly a one-sided upper bound on the signed real band error.  This
is the direct analytic interface for the backwards attack. -/
theorem vfMidSquareWheel_compositeFloor_iff_directBandError_le
    (R : ℕ) (E : ℝ) :
    (2 * (R : ℝ) - vfMidBandMass R - E ≤
        ((vfMidSquareWheelComposites R).card : ℝ)) ↔
      vfMidDirectBandError R ≤ E := by
  have hiff :=
    vfMidSquareWheel_composite_floor_centered_iff
      R (vfMidBandMass R) E
  rw [vfMidDirectBandError, vfMidDirectPrimeBandCount,
    vfMidDirectPrimeBand_eq_squareWheelPrimes]
  constructor
  · intro h
    have hp := hiff.mp h
    linarith
  · intro h
    apply hiff.mpr
    linarith

/-! ## Generic fixed-wheel upper bound on prime survivors -/

/-- The last integer strictly below the upper square. -/
def vfMidSquareWheelLast (R : ℕ) : ℕ :=
  (R + 1) ^ 2 - 1

/-- The open square carrier is exactly the half-open integer interval ending at
the last integer below the upper square. -/
theorem vfMidSquareWheelSites_eq_Ioc_last (R : ℕ) :
    vfMidSquareWheelSites R =
      Finset.Ioc (R ^ 2) (vfMidSquareWheelLast R) := by
  ext n
  simp only [vfMidSquareWheelSites, vfMidSquareWheelLast,
    Finset.mem_Ioo, Finset.mem_Ioc]
  omega

/-- The physical length from the lower square to the last interior integer is
exactly 2R. -/
theorem vfMidSquareWheelLast_sub_sq (R : ℕ) :
    vfMidSquareWheelLast R - R ^ 2 = 2 * R := by
  unfold vfMidSquareWheelLast
  have hsq : (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by ring
  omega

/-- If all prime sites in the square block are coprime to W, then the prime
population injects into the W-rough interval on the same physical carrier. -/
theorem vfMidSquareWheelPrimes_subset_roughWheelInterval
    (R W : ℕ)
    (hcop :
      ∀ n ∈ vfMidSquareWheelPrimes R, Nat.Coprime n W) :
    vfMidSquareWheelPrimes R ⊆
      roughWheelInterval W (R ^ 2) (vfMidSquareWheelLast R) := by
  intro n hn
  have hnSite : n ∈ vfMidSquareWheelSites R :=
    (Finset.mem_filter.mp hn).1
  rw [vfMidSquareWheelSites_eq_Ioc_last R] at hnSite
  exact Finset.mem_filter.mpr ⟨hnSite, hcop n hn⟩

/-- Generic fixed-wheel survivor bound on one square block.  The leading term
is wheel density times 2R; the explicit cost is two incomplete residue
periods. -/
theorem vfMidSquareWheelPrime_card_le_roughWheel
    (R W : ℕ) (hW : 0 < W)
    (hcop :
      ∀ n ∈ vfMidSquareWheelPrimes R, Nat.Coprime n W) :
    ((vfMidSquareWheelPrimes R).card : ℝ) ≤
      ((roughWheelResidues W).card : ℝ) / W * (2 * (R : ℝ)) +
        2 * (roughWheelResidues W).card := by
  have hsub :=
    vfMidSquareWheelPrimes_subset_roughWheelInterval R W hcop
  have hcardNat := Finset.card_le_card hsub
  have hcard :
      ((vfMidSquareWheelPrimes R).card : ℝ) ≤
        ((roughWheelInterval W (R ^ 2)
          (vfMidSquareWheelLast R)).card : ℝ) := by
    exact_mod_cast hcardNat
  have hab : R ^ 2 ≤ vfMidSquareWheelLast R := by
    unfold vfMidSquareWheelLast
    have hsq : (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by ring
    omega
  have hrough :=
    card_roughWheelInterval_le_density
      (W := W) (a := R ^ 2) (b := vfMidSquareWheelLast R) hW hab
  have hwidth :
      ((vfMidSquareWheelLast R : ℕ) : ℝ) - ((R ^ 2 : ℕ) : ℝ) =
        2 * (R : ℝ) := by
    have hnat := vfMidSquareWheelLast_sub_sq R
    have hle : R ^ 2 ≤ vfMidSquareWheelLast R := hab
    exact_mod_cast hnat
  rw [hwidth] at hrough
  exact hcard.trans hrough

/-! ## Fixed wheels 6, 30, 210 -/

private theorem vfMidSquareWheelPrime_coprime_smallPrime
    {R n p : ℕ} (hR : 1 ≤ R) (hpR : p ≤ R)
    (hp : p.Prime) (hn : n ∈ vfMidSquareWheelPrimes R) :
    Nat.Coprime n p := by
  have hnPrime : n.Prime := (Finset.mem_filter.mp hn).2
  have hnSite : n ∈ vfMidSquareWheelSites R :=
    (Finset.mem_filter.mp hn).1
  have hnI := Finset.mem_Ioo.mp hnSite
  have hRsq : R ≤ R ^ 2 := by nlinarith
  have hRn : R < n := lt_of_le_of_lt hRsq hnI.1
  have hnot : ¬ p ∣ n := by
    intro hpd
    have heq : p = n :=
      (Nat.prime_dvd_prime_iff_eq hp hnPrime).mp hpd
    omega
  have hcop : Nat.Coprime p n := (hp.coprime_iff_not_dvd).2 hnot
  exact hcop.symm

private theorem vfMidSquareWheelPrime_coprime_six
    {R n : ℕ} (hR : 3 ≤ R)
    (hn : n ∈ vfMidSquareWheelPrimes R) :
    Nat.Coprime n 6 := by
  have h2 := vfMidSquareWheelPrime_coprime_smallPrime
    (R := R) (n := n) (p := 2) (by omega) (by omega) Nat.prime_two hn
  have h3 := vfMidSquareWheelPrime_coprime_smallPrime
    (R := R) (n := n) (p := 3) (by omega) (by omega) (by norm_num) hn
  simpa using Nat.Coprime.mul_right h2 h3

private theorem vfMidSquareWheelPrime_coprime_thirty
    {R n : ℕ} (hR : 5 ≤ R)
    (hn : n ∈ vfMidSquareWheelPrimes R) :
    Nat.Coprime n 30 := by
  have h6 := vfMidSquareWheelPrime_coprime_six (R := R) (n := n)
    (by omega) hn
  have h5 := vfMidSquareWheelPrime_coprime_smallPrime
    (R := R) (n := n) (p := 5) (by omega) (by omega) (by norm_num) hn
  simpa using Nat.Coprime.mul_right h6 h5

private theorem vfMidSquareWheelPrime_coprime_twoTen
    {R n : ℕ} (hR : 7 ≤ R)
    (hn : n ∈ vfMidSquareWheelPrimes R) :
    Nat.Coprime n 210 := by
  have h30 := vfMidSquareWheelPrime_coprime_thirty (R := R) (n := n)
    (by omega) hn
  have h7 := vfMidSquareWheelPrime_coprime_smallPrime
    (R := R) (n := n) (p := 7) (by omega) (by omega) (by norm_num) hn
  simpa using Nat.Coprime.mul_right h30 h7

/-- The 6-wheel leaves at most 2R/3 + 4 possible prime sites. -/
theorem vfMidSquareWheelPrime_card_le_six
    (R : ℕ) (hR : 3 ≤ R) :
    ((vfMidSquareWheelPrimes R).card : ℝ) ≤
      (2 / 3 : ℝ) * R + 4 := by
  have h := vfMidSquareWheelPrime_card_le_roughWheel
    R 6 (by norm_num)
    (fun n hn => vfMidSquareWheelPrime_coprime_six hR hn)
  rw [roughWheelResidues_card_six] at h
  norm_num at h ⊢
  linarith

/-- Therefore the 6-wheel forces at least 4R/3 - 4 composites. -/
theorem vfMidSquareWheelComposite_card_ge_six
    (R : ℕ) (hR : 3 ≤ R) :
    (4 / 3 : ℝ) * R - 4 ≤
      ((vfMidSquareWheelComposites R).card : ℝ) := by
  have hp := vfMidSquareWheelPrime_card_le_six R hR
  have hc :=
    (vfMidSquareWheel_composite_floor_iff_prime_ceiling
      R ((2 / 3 : ℝ) * R + 4)).2 hp
  linarith

/-- The 30-wheel leaves at most 8R/15 + 16 possible prime sites. -/
theorem vfMidSquareWheelPrime_card_le_thirty
    (R : ℕ) (hR : 5 ≤ R) :
    ((vfMidSquareWheelPrimes R).card : ℝ) ≤
      (8 / 15 : ℝ) * R + 16 := by
  have h := vfMidSquareWheelPrime_card_le_roughWheel
    R 30 (by norm_num)
    (fun n hn => vfMidSquareWheelPrime_coprime_thirty hR hn)
  rw [roughWheelResidues_card_thirty] at h
  norm_num at h ⊢
  linarith

/-- Therefore the 30-wheel forces at least 22R/15 - 16 composites. -/
theorem vfMidSquareWheelComposite_card_ge_thirty
    (R : ℕ) (hR : 5 ≤ R) :
    (22 / 15 : ℝ) * R - 16 ≤
      ((vfMidSquareWheelComposites R).card : ℝ) := by
  have hp := vfMidSquareWheelPrime_card_le_thirty R hR
  have hc :=
    (vfMidSquareWheel_composite_floor_iff_prime_ceiling
      R ((8 / 15 : ℝ) * R + 16)).2 hp
  linarith

/-- The 210-wheel leaves at most 16R/35 + 96 possible prime sites. -/
theorem vfMidSquareWheelPrime_card_le_twoTen
    (R : ℕ) (hR : 7 ≤ R) :
    ((vfMidSquareWheelPrimes R).card : ℝ) ≤
      (16 / 35 : ℝ) * R + 96 := by
  have h := vfMidSquareWheelPrime_card_le_roughWheel
    R 210 (by norm_num)
    (fun n hn => vfMidSquareWheelPrime_coprime_twoTen hR hn)
  rw [roughWheelResidues_card_twoTen] at h
  norm_num at h ⊢
  linarith

/-- **Explicit reversed composite floor.**  The 210-wheel proves
C_R >= 54R/35 - 96 unconditionally. -/
theorem vfMidSquareWheelComposite_card_ge_twoTen
    (R : ℕ) (hR : 7 ≤ R) :
    (54 / 35 : ℝ) * R - 96 ≤
      ((vfMidSquareWheelComposites R).card : ℝ) := by
  have hp := vfMidSquareWheelPrime_card_le_twoTen R hR
  have hc :=
    (vfMidSquareWheel_composite_floor_iff_prime_ceiling
      R ((16 / 35 : ℝ) * R + 96)).2 hp
  linarith

/-- The same 210-wheel ceiling written on the exact #828 prime supply. -/
theorem vfMidIntegerBlockPrimeSupply_le_twoTen
    (R : ℕ) (hR : 7 ≤ R) :
    (vfMidIntegerBlockPrimeSupply R : ℝ) ≤
      (16 / 35 : ℝ) * R + 96 := by
  unfold vfMidIntegerBlockPrimeSupply
  rw [vfMidDirectPrimeBand_eq_squareWheelPrimes]
  exact vfMidSquareWheelPrime_card_le_twoTen R hR

/-- One-sided drift consequence for the exact backlog recurrence.  The 210
composite floor prevents the backlog increment from being more negative than
integer demand minus the explicit survivor ceiling. -/
theorem vfMidIntegerBlockBacklog_increment_ge_twoTen
    (R : ℕ) (hR : 7 ≤ R) :
    ((vfMidIntegerBlockDemand R : ℤ) : ℝ) -
        ((16 / 35 : ℝ) * R + 96) ≤
      (((vfMidIntegerBlockBacklog (R + 1) -
          vfMidIntegerBlockBacklog R : ℤ)) : ℝ) := by
  have hrec := vfMidIntegerBlockBacklog_succ R
  have hrecZ :
      vfMidIntegerBlockBacklog (R + 1) -
          vfMidIntegerBlockBacklog R =
        vfMidIntegerBlockDemand R -
          (vfMidIntegerBlockPrimeSupply R : ℤ) := by
    omega
  have hp := vfMidIntegerBlockPrimeSupply_le_twoTen R hR
  rw [hrecZ]
  push_cast
  linarith

end RHLean.Analysis

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


/-! ## Backward transport of a future prime-count floor

A lower bound for the prime count at a later square endpoint can be transported
backward exactly once an upper envelope for every intervening square-block
prime supply is supplied.  This is the precise interface for testing whether a
global PNT floor plus the already-proved wheel ceilings can control the
one-sided VF deficit.
-/

/-- Exact cumulative prime supply between square endpoints. -/
def vfMidIntegerPrimeSupplyWindow (R T : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico R T, (vfMidIntegerBlockPrimeSupply r : ℝ)

/-- Generic finite-difference telescope, kept local to the backward-floor
attack so it has no dependency on the direct signed-dynamics file. -/
private theorem vfMidCompositeFloor_sum_increment_Ico
    (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ k ∈ Finset.Ico a b, (f (k + 1) - f k)) =
      f b - f a := by
  rw [Finset.sum_Ico_eq_sub _ hab, Finset.sum_range_sub f b,
    Finset.sum_range_sub f a]
  abel

/-- The cumulative exact square-block supply is literally the difference of
prime counts at the two square endpoints. -/
theorem vfMidIntegerPrimeSupplyWindow_eq_primeCounting_sub
    {R T : ℕ} (hRT : R ≤ T) :
    vfMidIntegerPrimeSupplyWindow R T =
      (Nat.primeCounting (T ^ 2) : ℝ) -
        (Nat.primeCounting (R ^ 2) : ℝ) := by
  unfold vfMidIntegerPrimeSupplyWindow
  calc
    (∑ r ∈ Finset.Ico R T, (vfMidIntegerBlockPrimeSupply r : ℝ)) =
        ∑ r ∈ Finset.Ico R T,
          ((Nat.primeCounting ((r + 1) ^ 2) : ℝ) -
            (Nat.primeCounting (r ^ 2) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro r _hr
      have h :=
        vfMidIntegerBlockPrimeSupply_add_primeCounting r
      have hreal :
          (vfMidIntegerBlockPrimeSupply r : ℝ) +
              (Nat.primeCounting (r ^ 2) : ℝ) =
            (Nat.primeCounting ((r + 1) ^ 2) : ℝ) := by
        exact_mod_cast h
      linarith
    _ = (Nat.primeCounting (T ^ 2) : ℝ) -
          (Nat.primeCounting (R ^ 2) : ℝ) := by
      exact vfMidCompositeFloor_sum_increment_Ico
        (fun r => (Nat.primeCounting (r ^ 2) : ℝ)) hRT

/-- **Backward floor transport.**  If a later square endpoint has prime count
at least L, and every intervening square block has supply at most U(r), then
the earlier square endpoint has prime count at least L minus the total allowed
intervening supply.  No asymptotic input occurs in this theorem. -/
theorem vfMidPrimeCounting_sq_ge_of_future_floor_and_supply_ceiling
    {R T : ℕ} (hRT : R ≤ T) (L : ℝ) (U : ℕ → ℝ)
    (hfuture : L ≤ (Nat.primeCounting (T ^ 2) : ℝ))
    (hupper :
      ∀ r ∈ Finset.Ico R T,
        (vfMidIntegerBlockPrimeSupply r : ℝ) ≤ U r) :
    L - ∑ r ∈ Finset.Ico R T, U r ≤
      (Nat.primeCounting (R ^ 2) : ℝ) := by
  have hsum :
      vfMidIntegerPrimeSupplyWindow R T ≤
        ∑ r ∈ Finset.Ico R T, U r := by
    unfold vfMidIntegerPrimeSupplyWindow
    apply Finset.sum_le_sum
    intro r hr
    exact hupper r hr
  have htel :=
    vfMidIntegerPrimeSupplyWindow_eq_primeCounting_sub hRT
  linarith

/-- Specialization of backward floor transport to the compiled 210-wheel
ceiling P_r <= 16 r / 35 + 96. -/
theorem vfMidPrimeCounting_sq_ge_of_future_floor_twoTen
    {R T : ℕ} (hR : 7 ≤ R) (hRT : R ≤ T) (L : ℝ)
    (hfuture : L ≤ (Nat.primeCounting (T ^ 2) : ℝ)) :
    L -
        ∑ r ∈ Finset.Ico R T,
          ((16 / 35 : ℝ) * (r : ℝ) + 96) ≤
      (Nat.primeCounting (R ^ 2) : ℝ) := by
  apply vfMidPrimeCounting_sq_ge_of_future_floor_and_supply_ceiling
    hRT L (fun r => (16 / 35 : ℝ) * (r : ℝ) + 96) hfuture
  intro r hr
  have hrR : R ≤ r := (Finset.mem_Ico.mp hr).1
  exact vfMidIntegerBlockPrimeSupply_le_twoTen r (hR.trans hrR)

/-- The same 210-wheel transport written directly as a one-sided VF-mid
endpoint deficit bound.  This theorem makes the cost of the proposed
"PNT floor + block ceiling" strategy explicit. -/
theorem vfMidSquareEndpointDeficit_le_of_future_floor_twoTen
    {R T : ℕ} (hR : 7 ≤ R) (hRT : R ≤ T) (L : ℝ)
    (hfuture : L ≤ (Nat.primeCounting (T ^ 2) : ℝ)) :
    vfMidFinishedMass R - (Nat.primeCounting (R ^ 2) : ℝ) ≤
      vfMidFinishedMass R - L +
        ∑ r ∈ Finset.Ico R T,
          ((16 / 35 : ℝ) * (r : ℝ) + 96) := by
  have hback :=
    vfMidPrimeCounting_sq_ge_of_future_floor_twoTen
      hR hRT L hfuture
  linarith

end RHLean.Analysis

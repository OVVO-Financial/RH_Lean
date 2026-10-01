import Mathlib
import «research.VF_MID_DYADIC_PREFIX_OWNER»

/-!
# Exact chronological-owner form of the VF dyadic late correction

This file completes the combinatorial side of the VF-only dyadic reduction.
The four-endpoint prefix supply is proved equal to the sum of physical prefix
survivors over the adjacent square blocks.  The difference between those
survivors and the actual primes is then partitioned exactly by least prime
factor.  Thus the dyadic late-removal term T is not an abstract residual:
it is literally the cumulative chronological owner census.

No Li/PNT approximation or asymptotic input is used.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-! ## Endpoint counting really is the sum of physical square-block survivors -/

/-- Prefix-wheel survivors in an arbitrary natural interval (A,B]. -/
def vfMidPrefixWheelIntervalCounting (z A B : ℕ) : ℕ := by
  classical
  exact ((Finset.Ioc A B).filter (lowWheelHighSurvivor z)).card

/-- Splitting (0,B] at A exactly splits the fixed-prefix survivor count. -/
theorem vfMidPrefixWheelCounting_add_intervalCounting
    (z A B : ℕ) (hAB : A ≤ B) :
    vfMidPrefixWheelCounting z A +
        vfMidPrefixWheelIntervalCounting z A B =
      vfMidPrefixWheelCounting z B := by
  classical
  let SA : Finset ℕ :=
    (Finset.Ioc 0 A).filter (lowWheelHighSurvivor z)
  let SAB : Finset ℕ :=
    (Finset.Ioc A B).filter (lowWheelHighSurvivor z)
  let SB : Finset ℕ :=
    (Finset.Ioc 0 B).filter (lowWheelHighSurvivor z)
  have hdisj : Disjoint SA SAB := by
    rw [Finset.disjoint_left]
    intro n hnA hnAB
    have hnAI := (Finset.mem_filter.mp hnA).1
    have hnABI := (Finset.mem_filter.mp hnAB).1
    have hna := (Finset.mem_Ioc.mp hnAI).2
    have han := (Finset.mem_Ioc.mp hnABI).1
    omega
  have hunion : SA ∪ SAB = SB := by
    ext n
    simp only [SA, SAB, SB, Finset.mem_union, Finset.mem_filter,
      Finset.mem_Ioc]
    constructor
    · rintro (⟨⟨h0n, hnA⟩, hs⟩ | ⟨⟨hAn, hnB⟩, hs⟩)
      · exact ⟨⟨h0n, hnA.trans hAB⟩, hs⟩
      · exact ⟨⟨by omega, hnB⟩, hs⟩
    · rintro ⟨⟨h0n, hnB⟩, hs⟩
      by_cases hnA : n ≤ A
      · exact Or.inl ⟨⟨h0n, hnA⟩, hs⟩
      · exact Or.inr ⟨⟨lt_of_not_ge hnA, hnB⟩, hs⟩
  change SA.card + SAB.card = SB.card
  calc
    SA.card + SAB.card = (SA ∪ SAB).card := by
      symm
      exact Finset.card_union_of_disjoint hdisj
    _ = SB.card := by rw [hunion]

/-- A square survives a fixed low-prime wheel exactly when its root survives. -/
theorem lowWheelHighSurvivor_sq_iff
    (z n : ℕ) :
    lowWheelHighSurvivor z (n ^ 2) ↔
      lowWheelHighSurvivor z n := by
  constructor
  · intro hs p hp hpd
    apply hs p hp
    rw [pow_two]
    exact dvd_mul_of_dvd_left hpd n
  · intro hs p hp hpd
    have hpPrime := prime_of_mem_primesUpTo hp
    apply hs p hp
    exact hpPrime.dvd_of_dvd_pow hpd

/-- The closed square interval consists of the open physical square carrier
plus its upper square; the corresponding root interval carries exactly the
same one-site survival indicator. -/
theorem vfMidPrefixWheelIntervalCounting_square_eq_block_add_root
    (z R : ℕ) :
    vfMidPrefixWheelIntervalCounting z (R ^ 2) ((R + 1) ^ 2) =
      (vfMidSquarePrefixWheelSurvivors z R).card +
        vfMidPrefixWheelIntervalCounting z R (R + 1) := by
  classical
  have hsquareExpand :
      (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by
    ring
  have hsqIoc :
      Finset.Ioc (R ^ 2) ((R + 1) ^ 2) =
        insert ((R + 1) ^ 2)
          (Finset.Ioo (R ^ 2) ((R + 1) ^ 2)) := by
    rw [hsquareExpand]
    ext n
    simp
    omega
  have hrootIoc :
      Finset.Ioc R (R + 1) = {R + 1} := by
    ext n
    simp
  unfold vfMidPrefixWheelIntervalCounting
    vfMidSquarePrefixWheelSurvivors vfMidSquareWheelSites
  rw [hsqIoc, hrootIoc]
  have hupperNot :
      (R + 1) ^ 2 ∉
        (Finset.Ioo (R ^ 2) ((R + 1) ^ 2)).filter
          (lowWheelHighSurvivor z) := by
    simp
  by_cases hroot : lowWheelHighSurvivor z (R + 1)
  · have hsquare :
        lowWheelHighSurvivor z ((R + 1) ^ 2) :=
      (lowWheelHighSurvivor_sq_iff z (R + 1)).2 hroot
    have hrootFilter :
        ({R + 1} : Finset ℕ).filter (lowWheelHighSurvivor z) =
          {R + 1} := by
      ext n
      simp [hroot]
    rw [Finset.filter_insert]
    simp only [hsquare, if_true]
    rw [Finset.card_insert_of_notMem hupperNot, hrootFilter]
    simp
  · have hsquare :
        ¬ lowWheelHighSurvivor z ((R + 1) ^ 2) := by
      intro h
      exact hroot ((lowWheelHighSurvivor_sq_iff z (R + 1)).1 h)
    have hrootFilter :
        ({R + 1} : Finset ℕ).filter (lowWheelHighSurvivor z) =
          ∅ := by
      ext n
      simp [hroot]
    rw [Finset.filter_insert]
    simp only [hsquare, if_false]
    rw [hrootFilter]
    simp

/-- One physical square-block prefix survivor count is exactly the four
endpoint difference F_z((R+1)^2)-F_z(R^2)-F_z(R+1)+F_z(R). -/
theorem vfMidSquarePrefixWheelSurvivors_card_eq_fourEndpoints
    (z R : ℕ) :
    ((vfMidSquarePrefixWheelSurvivors z R).card : ℝ) =
      (vfMidPrefixWheelCounting z ((R + 1) ^ 2) : ℝ) -
      (vfMidPrefixWheelCounting z (R ^ 2) : ℝ) -
      (vfMidPrefixWheelCounting z (R + 1) : ℝ) +
      (vfMidPrefixWheelCounting z R : ℝ) := by
  have hsq :=
    vfMidPrefixWheelCounting_add_intervalCounting
      z (R ^ 2) ((R + 1) ^ 2)
        (Nat.pow_le_pow_left (by omega : R ≤ R + 1) 2)
  have hroot :=
    vfMidPrefixWheelCounting_add_intervalCounting
      z R (R + 1) (by omega)
  have hsplit :=
    vfMidPrefixWheelIntervalCounting_square_eq_block_add_root z R
  have hsqR :
      (vfMidPrefixWheelCounting z (R ^ 2) : ℝ) +
          (vfMidPrefixWheelIntervalCounting z (R ^ 2) ((R + 1) ^ 2) : ℝ) =
        (vfMidPrefixWheelCounting z ((R + 1) ^ 2) : ℝ) := by
    exact_mod_cast hsq
  have hrootR :
      (vfMidPrefixWheelCounting z R : ℝ) +
          (vfMidPrefixWheelIntervalCounting z R (R + 1) : ℝ) =
        (vfMidPrefixWheelCounting z (R + 1) : ℝ) := by
    exact_mod_cast hroot
  have hsplitR :
      (vfMidPrefixWheelIntervalCounting z (R ^ 2) ((R + 1) ^ 2) : ℝ) =
        (vfMidSquarePrefixWheelSurvivors z R).card +
          (vfMidPrefixWheelIntervalCounting z R (R + 1) : ℝ) := by
    exact_mod_cast hsplit
  linarith

/-- Endpoint potential whose discrete derivative is one square-block prefix
survivor population. -/
def vfMidPrefixWheelSquarePotential (z R : ℕ) : ℝ :=
  (vfMidPrefixWheelCounting z (R ^ 2) : ℝ) -
    (vfMidPrefixWheelCounting z R : ℝ)

theorem vfMidSquarePrefixWheelSurvivors_card_eq_potential_increment
    (z R : ℕ) :
    ((vfMidSquarePrefixWheelSurvivors z R).card : ℝ) =
      vfMidPrefixWheelSquarePotential z (R + 1) -
        vfMidPrefixWheelSquarePotential z R := by
  rw [vfMidSquarePrefixWheelSurvivors_card_eq_fourEndpoints]
  unfold vfMidPrefixWheelSquarePotential
  ring

/-- The four-endpoint prefix expression telescopes exactly across adjacent
square blocks.  This is the physical version of the endpoint cancellation. -/
theorem vfMidDyadicPrefixSupply_eq_sum_prefixWheelCards
    (z A B : ℕ) (hAB : A ≤ B) :
    vfMidDyadicPrefixSupply z A B =
      ∑ r ∈ Finset.Ico A B,
        ((vfMidSquarePrefixWheelSurvivors z r).card : ℝ) := by
  calc
    vfMidDyadicPrefixSupply z A B =
        vfMidPrefixWheelSquarePotential z B -
          vfMidPrefixWheelSquarePotential z A := by
            unfold vfMidDyadicPrefixSupply
              vfMidPrefixWheelSquarePotential
            ring
    _ = ∑ r ∈ Finset.Ico A B,
          (vfMidPrefixWheelSquarePotential z (r + 1) -
            vfMidPrefixWheelSquarePotential z r) := by
          symm
          exact Finset.sum_Ico_sub
            (vfMidPrefixWheelSquarePotential z) hAB
    _ = ∑ r ∈ Finset.Ico A B,
          ((vfMidSquarePrefixWheelSurvivors z r).card : ℝ) := by
          apply Finset.sum_congr rfl
          intro r _hr
          symm
          exact
            vfMidSquarePrefixWheelSurvivors_card_eq_potential_increment z r

/-! ## The prime endpoint difference telescopes over the same square blocks -/

def vfMidPrimeSquarePotential (R : ℕ) : ℝ :=
  (Nat.primeCounting (R ^ 2) : ℝ)

theorem vfMidIntegerBlockPrimeSupply_cast_eq_potential_increment
    (R : ℕ) :
    (vfMidIntegerBlockPrimeSupply R : ℝ) =
      vfMidPrimeSquarePotential (R + 1) -
        vfMidPrimeSquarePotential R := by
  have h := vfMidIntegerBlockPrimeSupply_add_primeCounting R
  have hR :
      (vfMidIntegerBlockPrimeSupply R : ℝ) +
          (Nat.primeCounting (R ^ 2) : ℝ) =
        (Nat.primeCounting ((R + 1) ^ 2) : ℝ) := by
    exact_mod_cast h
  unfold vfMidPrimeSquarePotential
  linarith

theorem vfMidDyadicPrimeSupply_eq_sum_blockPrimeSupply
    (A B : ℕ) (hAB : A ≤ B) :
    vfMidDyadicPrimeSupply A B =
      ∑ r ∈ Finset.Ico A B,
        (vfMidIntegerBlockPrimeSupply r : ℝ) := by
  calc
    vfMidDyadicPrimeSupply A B =
        vfMidPrimeSquarePotential B -
          vfMidPrimeSquarePotential A := by
            rfl
    _ = ∑ r ∈ Finset.Ico A B,
          (vfMidPrimeSquarePotential (r + 1) -
            vfMidPrimeSquarePotential r) := by
          symm
          exact Finset.sum_Ico_sub vfMidPrimeSquarePotential hAB
    _ = ∑ r ∈ Finset.Ico A B,
          (vfMidIntegerBlockPrimeSupply r : ℝ) := by
          apply Finset.sum_congr rfl
          intro r _hr
          symm
          exact vfMidIntegerBlockPrimeSupply_cast_eq_potential_increment r

/-- Before invoking least-prime-factor ownership, T is already the signed sum
of the physical per-block excess prefix survivors over actual primes. -/
theorem vfMidDyadicLateRemoval_eq_sum_blockExcess
    (z A B : ℕ) (hAB : A ≤ B) :
    vfMidDyadicLateRemoval z A B =
      ∑ r ∈ Finset.Ico A B,
        (((vfMidSquarePrefixWheelSurvivors z r).card : ℝ) -
          (vfMidIntegerBlockPrimeSupply r : ℝ)) := by
  unfold vfMidDyadicLateRemoval
  rw [vfMidDyadicPrefixSupply_eq_sum_prefixWheelCards z A B hAB,
    vfMidDyadicPrimeSupply_eq_sum_blockPrimeSupply A B hAB,
    ← Finset.sum_sub_distrib]

/-! ## Exact least-prime-factor ownership of the remaining removals -/

/-- Composite prefix survivors in one physical square block. -/
def vfMidSquareBandPrefixCompositeSurvivors (z R : ℕ) : Finset ℕ :=
  (vfMidSquareBandComposites R).filter (lowWheelHighSurvivor z)

/-- On a genuine square-band composite, surviving the fixed prefix through z
is exactly the statement that its least prime factor is larger than z. -/
theorem vfMidSquareBandComposite_survives_prefix_iff_minFac_gt
    {z R n : ℕ} (hR : 2 ≤ R)
    (hn : n ∈ vfMidSquareBandComposites R) :
    lowWheelHighSurvivor z n ↔ z < n.minFac := by
  have hnSite := (Finset.mem_filter.mp hn).1
  have hnI := Finset.mem_Ioo.mp hnSite
  have hnOne : n ≠ 1 := by
    have hR2 : 1 < R ^ 2 := by nlinarith
    omega
  have hminPrime : n.minFac.Prime := Nat.minFac_prime hnOne
  have hminDvd : n.minFac ∣ n := Nat.minFac_dvd n
  constructor
  · intro hs
    by_contra hnot
    have hminz : n.minFac ≤ z := by omega
    have hmem :
        n.minFac ∈ primesUpTo z :=
      mem_primesUpTo_of_prime_le hminPrime hminz
    exact hs n.minFac hmem hminDvd
  · intro hz p hpMem hpDvd
    have hpPrime := prime_of_mem_primesUpTo hpMem
    have hpz := (mem_primesUpTo.mp hpMem).2
    have hminle : n.minFac ≤ p :=
      Nat.minFac_le_of_dvd hpPrime.two_le hpDvd
    omega

/-- Owners that remain after the fixed prefix: precisely least-prime owners
larger than z. -/
def vfMidSquareBandLateOwnerPrimes (z R : ℕ) : Finset ℕ :=
  (vfMidSquareBandOwnerPrimes R).filter (fun p => z < p)

@[simp] theorem mem_vfMidSquareBandLateOwnerPrimes
    {z R p : ℕ} :
    p ∈ vfMidSquareBandLateOwnerPrimes z R ↔
      p ∈ vfMidSquareBandOwnerPrimes R ∧ z < p := by
  simp [vfMidSquareBandLateOwnerPrimes]

/-- Filtered owner Fubini: the composite survivors after the fixed prefix are
exactly the disjoint sum of owner fibres with owner p>z. -/
theorem vfMidSquareBandPrefixComposite_card_eq_sum_lateOwnerCards
    (z R : ℕ) (hR : 2 ≤ R) :
    (vfMidSquareBandPrefixCompositeSurvivors z R).card =
      ∑ p ∈ vfMidSquareBandLateOwnerPrimes z R,
        (vfMidSquareBandCompositeOwner R p).card := by
  let S : Finset ℕ := vfMidSquareBandPrefixCompositeSurvivors z R
  let O : Finset ℕ := vfMidSquareBandLateOwnerPrimes z R
  let owner : ℕ → ℕ := fun n => n.minFac
  have hmaps : ∀ n ∈ S, owner n ∈ O := by
    intro n hn
    have hnData := Finset.mem_filter.mp hn
    have hnComp : n ∈ vfMidSquareBandComposites R := hnData.1
    have hnSurv : lowWheelHighSurvivor z n := hnData.2
    have howner :=
      vfMidSquareBandComposite_minFac_mem_ownerPrimes hR hnComp
    have hzlt :=
      (vfMidSquareBandComposite_survives_prefix_iff_minFac_gt
        hR hnComp).1 hnSurv
    exact Finset.mem_filter.mpr ⟨howner, hzlt⟩
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to
      (s := S) (t := O) (g := owner) hmaps (fun _ => (1 : ℕ))
  have hraw :
      (∑ n ∈ S, (1 : ℕ)) =
        ∑ p ∈ O, ∑ n ∈ S with owner n = p, (1 : ℕ) :=
    hfiber.symm
  calc
    (vfMidSquareBandPrefixCompositeSurvivors z R).card =
        ∑ n ∈ S, (1 : ℕ) := by
          rw [Finset.card_eq_sum_ones]
    _ = ∑ p ∈ O, ∑ n ∈ S with owner n = p, (1 : ℕ) := hraw
    _ = ∑ p ∈ vfMidSquareBandLateOwnerPrimes z R,
          (vfMidSquareBandCompositeOwner R p).card := by
      dsimp [O, S, owner]
      apply Finset.sum_congr rfl
      intro p hp
      have hpLate : z < p := (Finset.mem_filter.mp hp).2
      have hset :
          ((vfMidSquareBandComposites R).filter
              (lowWheelHighSurvivor z)).filter
                (fun n => n.minFac = p) =
            vfMidSquareBandCompositeOwner R p := by
        ext n
        simp only [vfMidSquareBandCompositeOwner, Finset.mem_filter]
        constructor
        · rintro ⟨⟨hnComp, _hnSurv⟩, hmin⟩
          exact ⟨hnComp, hmin⟩
        · rintro ⟨hnComp, hmin⟩
          have hs :
              lowWheelHighSurvivor z n :=
            (vfMidSquareBandComposite_survives_prefix_iff_minFac_gt
              hR hnComp).2 (by simpa [hmin] using hpLate)
          exact ⟨⟨hnComp, hs⟩, hmin⟩
      rw [Finset.card_eq_sum_ones, ← hset]
      rfl

/-- Prime survivors and composite survivors partition every partial-prefix
survivor population in the square block. -/
theorem vfMidSquarePrefixWheelSurvivors_card_eq_prime_add_prefixComposite
    (z R : ℕ) (hR : 2 ≤ R) (hzR : z ≤ R) :
    (vfMidSquarePrefixWheelSurvivors z R).card =
      vfMidIntegerBlockPrimeSupply R +
        (vfMidSquareBandPrefixCompositeSurvivors z R).card := by
  classical
  let P : Finset ℕ := vfMidSquareWheelPrimes R
  let C : Finset ℕ := vfMidSquareBandPrefixCompositeSurvivors z R
  let S : Finset ℕ := vfMidSquarePrefixWheelSurvivors z R
  have hpart : P ∪ C = S := by
    ext n
    simp only [P, C, S, vfMidSquareWheelPrimes,
      vfMidSquareBandPrefixCompositeSurvivors,
      vfMidSquareBandComposites, vfMidSquareBandSites,
      vfMidSquarePrefixWheelSurvivors, vfMidSquareWheelSites,
      Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hnSite, hnPrime⟩ | ⟨⟨hnSite, _hnPrime⟩, hnSurv⟩)
      · have hnPrimeMem : n ∈ vfMidSquareWheelPrimes R :=
          Finset.mem_filter.mpr ⟨hnSite, hnPrime⟩
        have hnPref :=
          vfMidSquareWheelPrimes_subset_prefixWheelSurvivors
            hR hzR hnPrimeMem
        exact Finset.mem_filter.mp hnPref
      · exact ⟨hnSite, hnSurv⟩
    · rintro ⟨hnSite, hnSurv⟩
      by_cases hnPrime : n.Prime
      · exact Or.inl ⟨hnSite, hnPrime⟩
      · exact Or.inr ⟨⟨hnSite, hnPrime⟩, hnSurv⟩
  have hdisj : Disjoint P C := by
    rw [Finset.disjoint_left]
    intro n hnP hnC
    have hp := (Finset.mem_filter.mp hnP).2
    have hc0 := (Finset.mem_filter.mp hnC).1
    have hc := (Finset.mem_filter.mp hc0).2
    exact hc hp
  have hcard := congrArg Finset.card hpart
  have hprime :
      P.card = vfMidIntegerBlockPrimeSupply R := by
    dsimp [P]
    unfold vfMidIntegerBlockPrimeSupply
    rw [vfMidDirectPrimeBand_eq_squareWheelPrimes]
  rw [Finset.card_union_of_disjoint hdisj, hprime] at hcard
  exact hcard.symm

/-- One prefix survivor excess over the exact prime supply is literally the
number of composites whose least-prime owner has not yet acted. -/
theorem vfMidSquarePrefixWheelExcess_eq_sum_lateOwnerCards
    (z R : ℕ) (hR : 2 ≤ R) (hzR : z ≤ R) :
    ((vfMidSquarePrefixWheelSurvivors z R).card : ℝ) -
        (vfMidIntegerBlockPrimeSupply R : ℝ) =
      ∑ p ∈ vfMidSquareBandLateOwnerPrimes z R,
        ((vfMidSquareBandCompositeOwner R p).card : ℝ) := by
  have hpart :=
    vfMidSquarePrefixWheelSurvivors_card_eq_prime_add_prefixComposite
      z R hR hzR
  have howners :=
    vfMidSquareBandPrefixComposite_card_eq_sum_lateOwnerCards z R hR
  have hpartR :
      ((vfMidSquarePrefixWheelSurvivors z R).card : ℝ) =
        (vfMidIntegerBlockPrimeSupply R : ℝ) +
          ((vfMidSquareBandPrefixCompositeSurvivors z R).card : ℝ) := by
    exact_mod_cast hpart
  have hownersR :
      ((vfMidSquareBandPrefixCompositeSurvivors z R).card : ℝ) =
        ∑ p ∈ vfMidSquareBandLateOwnerPrimes z R,
          ((vfMidSquareBandCompositeOwner R p).card : ℝ) := by
    exact_mod_cast howners
  rw [hownersR] at hpartR
  linarith

/-- Literal chronological owner census over the whole dyadic square range. -/
def vfMidDyadicOwnerLateRemoval (z A B : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico A B,
    ∑ p ∈ vfMidSquareBandLateOwnerPrimes z r,
      ((vfMidSquareBandCompositeOwner r p).card : ℝ)

/-- **Exact T identity.**  On A<=r<B with z<=A and A>=2, the dyadic
late-removal term is exactly the cumulative least-prime-factor owner census. -/
theorem vfMidDyadicLateRemoval_eq_ownerCensus
    (z A B : ℕ) (hA : 2 ≤ A) (hzA : z ≤ A) (hAB : A ≤ B) :
    vfMidDyadicLateRemoval z A B =
      vfMidDyadicOwnerLateRemoval z A B := by
  rw [vfMidDyadicLateRemoval_eq_sum_blockExcess z A B hAB]
  unfold vfMidDyadicOwnerLateRemoval
  apply Finset.sum_congr rfl
  intro r hr
  have hAr : A ≤ r := (Finset.mem_Ico.mp hr).1
  have hr2 : 2 ≤ r := hA.trans hAr
  have hzr : z ≤ r := hzA.trans hAr
  exact vfMidSquarePrefixWheelExcess_eq_sum_lateOwnerCards
    z r hr2 hzr

end RHLean.Analysis

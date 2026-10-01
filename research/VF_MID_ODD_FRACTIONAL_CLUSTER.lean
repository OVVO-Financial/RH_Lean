import Mathlib
import «research.VF_MID_DYADIC_OWNER_EXACT»
import «research.VF_MID_DIRECT_ROUGH_CHILD»

/-!
# Parity-aligned VF fractional cluster

This file places the VF reference on the same physical carrier used by the
chronological least-prime owner census.

After the fixed prime 2 has acted, the R-th open square block contains exactly
R odd candidate seats.  We spread the complete VF prime mass V_R uniformly
over those R seats.  Equivalently the VF-implied composite mass is exactly

  R - V_R.

The actual composite mass on the same carrier is R - P_R, and FTA partitions
it exactly by least-prime owners p > 2.  Hence the actual-minus-VF composite
tracking defect is

  (R - P_R) - (R - V_R) = V_R - P_R = -e_R.

No Li state occurs in any definition or theorem below.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- The physical odd candidate seats after the exact parity prefix. -/
def vfMidOddCandidateSeats (R : ℕ) : Finset ℕ :=
  vfMidSquarePrefixWheelSurvivors 2 R

/-- **Exact parity population.**  The open R-th square block has exactly R
survivors after removing the even sites. -/
theorem vfMidOddCandidateSeats_card
    (R : ℕ) :
    (vfMidOddCandidateSeats R).card = R := by
  have hsum :=
    vfMidDyadicPrefixSupply_eq_sum_prefixWheelCards
      2 R (R + 1) (by omega)
  rw [vfMidDyadicPrefixSupply_two_eq_half_interior] at hsum
  have hlen :
      vfMidDyadicInteriorLength R (R + 1) =
        2 * (R : ℝ) := by
    unfold vfMidDyadicInteriorLength
    push_cast
    ring
  rw [hlen] at hsum
  have hsingle :
      (∑ r ∈ Finset.Ico R (R + 1),
        ((vfMidSquarePrefixWheelSurvivors 2 r).card : ℝ)) =
      ((vfMidSquarePrefixWheelSurvivors 2 R).card : ℝ) := by
    rw [Finset.sum_Ico_succ_top (by omega)]
    simp
  rw [hsingle] at hsum
  unfold vfMidOddCandidateSeats
  have hcast :
      (((vfMidSquarePrefixWheelSurvivors 2 R).card : ℕ) : ℝ) =
        (R : ℝ) := by
    nlinarith
  exact_mod_cast hcast

/-- Uniform fractional VF prime mass on each odd candidate seat. -/
def vfMidOddFractionalPrimeSeatWeight (R : ℕ) : ℝ :=
  vfMidBandMass R / (R : ℝ)

/-- The complete VF mass is preserved exactly after moving from the full open
integer block to the parity-reduced odd candidate carrier. -/
theorem vfMidOddFractionalPrimeSeatWeight_sum
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ _n ∈ vfMidOddCandidateSeats R,
      vfMidOddFractionalPrimeSeatWeight R) =
      vfMidBandMass R := by
  rw [Finset.sum_const, nsmul_eq_mul, vfMidOddCandidateSeats_card]
  unfold vfMidOddFractionalPrimeSeatWeight
  have hR0 : (R : ℝ) ≠ 0 := by positivity
  field_simp

/-- The VF-implied composite mass remaining after parity. -/
def vfMidOddFractionalCompositeReference (R : ℕ) : ℝ :=
  (R : ℝ) - vfMidBandMass R

/-- Actual parity-surviving composites plus actual primes exhaust exactly the
R odd candidate seats. -/
theorem vfMidOddActualComposite_card_add_primeSupply
    (R : ℕ) (hR : 2 ≤ R) :
    (vfMidSquareBandPrefixCompositeSurvivors 2 R).card +
      vfMidIntegerBlockPrimeSupply R = R := by
  have hpart :=
    vfMidSquarePrefixWheelSurvivors_card_eq_prime_add_prefixComposite
      2 R hR (by omega)
  rw [← vfMidOddCandidateSeats, vfMidOddCandidateSeats_card] at hpart
  omega

/-- The two repository prime-band carriers have the same cardinality. -/
theorem vfMidSquareBandPrimes_card_eq_integerBlockPrimeSupply
    (R : ℕ) :
    (vfMidSquareBandPrimes R).card =
      vfMidIntegerBlockPrimeSupply R := by
  have hOpen :=
    vfMidSquareBand_prime_card_add_primeCounting_sq R
  have hDirect :=
    vfMidIntegerBlockPrimeSupply_add_primeCounting R
  omega

/-- Per-block actual-minus-VF composite tracking defect on the parity carrier. -/
def vfMidOddCompositeTrackingDefect (R : ℕ) : ℝ :=
  ((vfMidSquareBandPrefixCompositeSurvivors 2 R).card : ℝ) -
    vfMidOddFractionalCompositeReference R

/-- **The parity-cluster defect is exactly minus the VF prime-band error.** -/
theorem vfMidOddCompositeTrackingDefect_eq_neg_bandError
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidOddCompositeTrackingDefect R =
      -vfMidSquareBandError R := by
  have hpart :=
    vfMidOddActualComposite_card_add_primeSupply R hR
  have hpartR :
      ((vfMidSquareBandPrefixCompositeSurvivors 2 R).card : ℝ) +
        (vfMidIntegerBlockPrimeSupply R : ℝ) = (R : ℝ) := by
    exact_mod_cast hpart
  have hPrime :=
    vfMidSquareBandPrimes_card_eq_integerBlockPrimeSupply R
  have hPrimeR :
      ((vfMidSquareBandPrimes R).card : ℝ) =
        (vfMidIntegerBlockPrimeSupply R : ℝ) := by
    exact_mod_cast hPrime
  unfold vfMidOddCompositeTrackingDefect
    vfMidOddFractionalCompositeReference
    vfMidSquareBandError
  rw [hPrimeR]
  linarith

/-- Dyadic accumulation of the parity-aligned per-block defects. -/
def vfMidOddDyadicCompositeTrackingDefect (A B : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico A B, vfMidOddCompositeTrackingDefect r

/-- **Exact identification with the canonical #846 VF tracking defect.**
The parity-aligned seat formulation and the native chronological-owner
formulation are literally the same signed dyadic object. -/
theorem vfMidOddDyadicCompositeTrackingDefect_eq_vfTrackingDefect
    {A B : ℕ} (hA : 2 ≤ A) (hB : 2 ≤ B) (hAB : A ≤ B) :
    vfMidOddDyadicCompositeTrackingDefect A B =
      vfMidDyadicVFTrackingDefect A B := by
  have hsum :
      (∑ r ∈ Finset.Ico A B, vfMidSquareBandError r) =
        vfMidSquareEndpointError B - vfMidSquareEndpointError A := by
    calc
      (∑ r ∈ Finset.Ico A B, vfMidSquareBandError r) =
          ∑ r ∈ Finset.Ico A B,
            (vfMidSquareEndpointError (r + 1) -
              vfMidSquareEndpointError r) := by
            apply Finset.sum_congr rfl
            intro r hr
            have hr2 : 2 ≤ r :=
              hA.trans (Finset.mem_Ico.mp hr).1
            have hstep := vfMidSquareEndpointError_succ r hr2
            linarith
      _ = vfMidSquareEndpointError B -
          vfMidSquareEndpointError A :=
        Finset.sum_Ico_sub vfMidSquareEndpointError hAB
  have hendpoint :
      vfMidSquareEndpointError B - vfMidSquareEndpointError A =
        vfMidPrimeError ((B : ℝ) ^ 2) -
          vfMidPrimeError ((A : ℝ) ^ 2) := by
    change
      vfMidDirectSquareEndpointError B -
          vfMidDirectSquareEndpointError A =
        vfMidPrimeError ((B : ℝ) ^ 2) -
          vfMidPrimeError ((A : ℝ) ^ 2)
    rw [vfMidDirectSquareEndpointError_eq_vfMidPrimeError hB,
      vfMidDirectSquareEndpointError_eq_vfMidPrimeError hA]
  rw [vfMidDyadicVFTrackingDefect_eq_neg_primeError_increment hA hB hAB]
  unfold vfMidOddDyadicCompositeTrackingDefect
  calc
    (∑ r ∈ Finset.Ico A B, vfMidOddCompositeTrackingDefect r) =
        ∑ r ∈ Finset.Ico A B, (-vfMidSquareBandError r) := by
          apply Finset.sum_congr rfl
          intro r hr
          have hr2 : 2 ≤ r :=
            hA.trans (Finset.mem_Ico.mp hr).1
          rw [vfMidOddCompositeTrackingDefect_eq_neg_bandError r hr2]
    _ = -(∑ r ∈ Finset.Ico A B, vfMidSquareBandError r) := by
          rw [Finset.sum_neg_distrib]
    _ = -(vfMidSquareEndpointError B -
          vfMidSquareEndpointError A) := by rw [hsum]
    _ = -(vfMidPrimeError ((B : ℝ) ^ 2) -
          vfMidPrimeError ((A : ℝ) ^ 2)) := by rw [hendpoint]

/-- The same defect written on the exact chronological least-prime owner
census.  This is the native object to recurse on. -/
theorem vfMidOddCompositeTrackingDefect_eq_ownerCensus_sub_reference
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidOddCompositeTrackingDefect R =
      (∑ p ∈ vfMidSquareBandLateOwnerPrimes 2 R,
        ((vfMidSquareBandCompositeOwner R p).card : ℝ)) -
      vfMidOddFractionalCompositeReference R := by
  have howners :=
    vfMidSquareBandPrefixComposite_card_eq_sum_lateOwnerCards
      2 R hR
  have hownersR :
      ((vfMidSquareBandPrefixCompositeSurvivors 2 R).card : ℝ) =
        ∑ p ∈ vfMidSquareBandLateOwnerPrimes 2 R,
          ((vfMidSquareBandCompositeOwner R p).card : ℝ) := by
    exact_mod_cast howners
  unfold vfMidOddCompositeTrackingDefect
  rw [hownersR]

/-! ## Terminal / recursive split on the parity owner carrier -/

/-- Late owners whose stripped child is forced prime. -/
def vfMidSquareBandLateTerminalOwners (R : ℕ) : Finset ℕ :=
  (vfMidSquareBandLateOwnerPrimes 2 R).filter
    (fun p => (R + 1) ^ 2 ≤ p ^ 3)

/-- Late owners whose stripped child remains genuinely recursive. -/
def vfMidSquareBandLateRecursiveOwners (R : ℕ) : Finset ℕ :=
  (vfMidSquareBandLateOwnerPrimes 2 R).filter
    (fun p => p ^ 3 < (R + 1) ^ 2)

theorem vfMidSquareBandLateOwnerPrimes_eq_terminal_union_recursive
    (R : ℕ) :
    vfMidSquareBandLateOwnerPrimes 2 R =
      vfMidSquareBandLateTerminalOwners R ∪
        vfMidSquareBandLateRecursiveOwners R := by
  ext p
  by_cases h : (R + 1) ^ 2 ≤ p ^ 3
  · simp [vfMidSquareBandLateTerminalOwners,
      vfMidSquareBandLateRecursiveOwners, h, Nat.not_lt.mpr h]
  · have hlt : p ^ 3 < (R + 1) ^ 2 := Nat.lt_of_not_ge h
    simp [vfMidSquareBandLateTerminalOwners,
      vfMidSquareBandLateRecursiveOwners, h, hlt]

theorem vfMidSquareBandLateTerminal_recursive_disjoint
    (R : ℕ) :
    Disjoint (vfMidSquareBandLateTerminalOwners R)
      (vfMidSquareBandLateRecursiveOwners R) := by
  rw [Finset.disjoint_left]
  intro p hpT hpR
  have hT := (Finset.mem_filter.mp hpT).2
  have hRec := (Finset.mem_filter.mp hpR).2
  omega

/-- Exact terminal/recursive split of the parity-aligned owner census. -/
theorem vfMidOddCompositeTrackingDefect_eq_terminal_add_recursive_sub_reference
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidOddCompositeTrackingDefect R =
      (∑ p ∈ vfMidSquareBandLateTerminalOwners R,
        ((vfMidSquareBandCompositeOwner R p).card : ℝ)) +
      (∑ p ∈ vfMidSquareBandLateRecursiveOwners R,
        ((vfMidSquareBandCompositeOwner R p).card : ℝ)) -
      vfMidOddFractionalCompositeReference R := by
  rw [vfMidOddCompositeTrackingDefect_eq_ownerCensus_sub_reference R hR,
    vfMidSquareBandLateOwnerPrimes_eq_terminal_union_recursive,
    Finset.sum_union
      (vfMidSquareBandLateTerminal_recursive_disjoint R)]

/-- A parity-late terminal owner has a prime stripped child. -/
theorem vfMidLateTerminalOwner_child_prime
    {R p n : ℕ} (hR : 2 ≤ R)
    (hpT : p ∈ vfMidSquareBandLateTerminalOwners R)
    (hn : n ∈ vfMidSquareBandCompositeOwner R p) :
    (n / p).Prime := by
  have hpOwner :
      p ∈ vfMidSquareBandOwnerPrimes R :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hpT).1).1
  have hterminal :
      (R + 1) ^ 2 ≤ p ^ 3 :=
    (Finset.mem_filter.mp hpT).2
  have hpFullTerminal :
      p ∈ vfMidSquareBandTerminalOwners R :=
    Finset.mem_filter.mpr ⟨hpOwner, hterminal⟩
  have hchild :
      n / p ∈ vfMidSquareBandCompositeOwnerChildren R p := by
    unfold vfMidSquareBandCompositeOwnerChildren
    exact Finset.mem_image.mpr ⟨n, hn, rfl⟩
  exact vfMidSquareBand_terminalOwner_child_prime
    hR hpFullTerminal hchild

/-- Every composite stripped child in the recursive parity sector has a second
prime owner q >= p and satisfies the strict scale compression p*q^2 < (R+1)^2. -/
theorem vfMidLateRecursiveOwner_secondOwner_geometry
    {R p m : ℕ}
    (_hpRec : p ∈ vfMidSquareBandLateRecursiveOwners R)
    (hm : m ∈ vfMidSquareBandOwnerRoughChildren R p)
    (hmComp : ¬ m.Prime) :
    let q := m.minFac
    p ≤ q ∧ p * q ^ 2 < (R + 1) ^ 2 := by
  exact vfMidSquareBandOwnerRoughChild_secondOwner_geometry
    hm hmComp

end RHLean.Analysis

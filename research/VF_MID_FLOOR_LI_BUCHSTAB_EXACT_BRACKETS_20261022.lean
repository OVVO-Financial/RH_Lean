import Mathlib
import RHLean.Analysis.PrimeSieveCollapseIdentity
import «research.VF_MID_FLOOR_LI_CRITICAL_BALANCE»

/-!
# Corrected floor-Li Buchstab brackets: ACTUAL Möbius source

Only source-exact identities. The imported smooth/rough collapse requires
Nat.sqrt x < y; literal y=Nat.sqrt x needs a one-prime boundary adjustment.
No analytic rate, random independence or RH-level estimate is assumed.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Analysis

/-- Deterministic integer floor-Li events weighted by true smaller
Mertens prefixes, before taking norms. -/
def buchstabFloorLiPrimeTail (y x : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc y x,
    vfMidFloorLiSingletonWeight q * mertensSummatory (x / q)

/-- Physical prime-minus-floor-Li innovations, signed and weighted. -/
def buchstabFloorLiMismatchTail (y x : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc y x,
    vfMidFloorLiMismatchFrequencyWeight q * mertensSummatory (x / q)

def buchstabFloorLiSmoothBracket (y x : ℕ) : ℂ :=
  primeSieveSmoothMobiusMass y x - buchstabFloorLiPrimeTail y x

def buchstabFloorLiInnovationBracket (y x : ℕ) : ℂ :=
  -buchstabFloorLiMismatchTail y x

/-- The genuine high-prime contribution is floor-Li reference PLUS
the genuine weighted signed mismatches. -/
theorem buchstab_actualPrimeTail_eq_floorLi_add_mismatch
    (y x : ℕ) :
    primeSieveReciprocalMertensSignedSum y x =
      buchstabFloorLiPrimeTail y x + buchstabFloorLiMismatchTail y x := by
  rw [primeSieveReciprocalMertensSignedSum_eq_mertensPrimeTail]
  unfold primeSieveMertensPrimeTail
    buchstabFloorLiPrimeTail buchstabFloorLiMismatchTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _hq
  have hweight :
      vfMidFloorLiSingletonWeight q +
          vfMidFloorLiMismatchFrequencyWeight q =
        primeSievePrimeIndicator q := by
    unfold vfMidFloorLiMismatchFrequencyWeight
    ring
  rw [← add_mul, hweight]
  by_cases hp : q.Prime <;> simp [primeSievePrimeIndicator, hp]

/-- Exact actual sharp Mertens identity with the two physical brackets.
It is explicitly NOT an independently proved cancellation estimate. -/
theorem buchstab_mertens_eq_floorLi_smooth_add_innovation
    (y x : ℕ) (hroot : Nat.sqrt x < y) :
    mertensSummatory x =
      buchstabFloorLiSmoothBracket y x +
        buchstabFloorLiInnovationBracket y x := by
  calc
    mertensSummatory x =
        -primeSieveReciprocalMertensSignedSum y x +
          primeSieveSmoothMobiusMass y x :=
      mertensSummatory_eq_neg_signedSum_add_smoothMass y x hroot
    _ = buchstabFloorLiSmoothBracket y x +
          buchstabFloorLiInnovationBracket y x := by
      rw [buchstab_actualPrimeTail_eq_floorLi_add_mismatch]
      unfold buchstabFloorLiSmoothBracket
        buchstabFloorLiInnovationBracket
      ring

/-- Retain the genuine cofactor M(floor(x/q)) in each high-prime
innovation; neither signs nor quotient intervals are discarded. -/
theorem buchstab_innovation_eq_signed_high_prime_cofactor
    (y x : ℕ) :
    buchstabFloorLiInnovationBracket y x =
      -(∑ q ∈ Finset.Ioc y x,
          vfMidFloorLiMismatchFrequencyWeight q *
            mertensSummatory (x / q)) := rfl

/-- Exact reciprocal-quotient reindexing, with the max(y,x/(d+1))
physical lower cutoff inherited from the source. -/
theorem buchstab_floorLiPrimeTail_eq_reciprocalQuotient
    (y x : ℕ) :
    buchstabFloorLiPrimeTail y x =
      ∑ d ∈ primeSieveQuotientSupport y x,
        (∑ q ∈ primeSieveReciprocalInterval y x d,
            vfMidFloorLiSingletonWeight q) * mertensSummatory d := by
  unfold buchstabFloorLiPrimeTail
  exact sum_mertens_div_eq_reciprocalIntervals
    y x vfMidFloorLiSingletonWeight

/-- Floor-Li integer steps telescope, exactly and not just up to O(1). -/
theorem buchstab_floorLiStep_Ioc {a b : ℕ} (hab : a ≤ b) :
    (∑ q ∈ Finset.Ioc a b, vfMidFloorLiSingletonWeight q) =
      (((vfMidFloorLiIntegerPotential b -
          vfMidFloorLiIntegerPotential a : ℤ)) : ℂ) := by
  induction b generalizing a with
  | zero =>
      have ha : a = 0 := Nat.eq_zero_of_le_zero hab
      subst a
      simp
  | succ b ih =>
      by_cases h : a ≤ b
      · rw [Finset.sum_Ioc_succ_top h, ih h]
        simp only [vfMidFloorLiSingletonWeight, Nat.succ_eq_add_one,
          Nat.add_sub_cancel]
        push_cast
        ring
      · have ha : a = b + 1 := by omega
        subst a
        simp

/-- The precise L(u_d)-L(ell_d) charge, with empty intervals zeroed. -/
def buchstabFloorLiReciprocalIntervalMass (y x d : ℕ) : ℂ :=
  if primeSieveReciprocalLower y x d ≤
       primeSieveReciprocalUpper x d then
    (((vfMidFloorLiIntegerPotential (primeSieveReciprocalUpper x d) -
       vfMidFloorLiIntegerPotential
         (primeSieveReciprocalLower y x d) : ℤ)) : ℂ)
  else 0

theorem buchstab_floorLiReciprocalInterval_eq_discretePotential
    (y x d : ℕ) :
    (∑ q ∈ primeSieveReciprocalInterval y x d,
       vfMidFloorLiSingletonWeight q) =
      buchstabFloorLiReciprocalIntervalMass y x d := by
  unfold primeSieveReciprocalInterval
    buchstabFloorLiReciprocalIntervalMass
  by_cases h : primeSieveReciprocalLower y x d ≤
      primeSieveReciprocalUpper x d
  · simp only [if_pos h]
    exact buchstab_floorLiStep_Ioc h
  · have hreverse :
        primeSieveReciprocalUpper x d ≤
          primeSieveReciprocalLower y x d := by omega
    rw [Finset.Ioc_eq_empty_of_le hreverse]
    simp [h]

theorem buchstab_floorLiPrimeTail_eq_discretePotential
    (y x : ℕ) :
    buchstabFloorLiPrimeTail y x =
      ∑ d ∈ primeSieveQuotientSupport y x,
        buchstabFloorLiReciprocalIntervalMass y x d *
          mertensSummatory d := by
  rw [buchstab_floorLiPrimeTail_eq_reciprocalQuotient]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [buchstab_floorLiReciprocalInterval_eq_discretePotential]

#print axioms buchstab_actualPrimeTail_eq_floorLi_add_mismatch
#print axioms buchstab_mertens_eq_floorLi_smooth_add_innovation
#print axioms buchstab_innovation_eq_signed_high_prime_cofactor
#print axioms buchstab_floorLiPrimeTail_eq_reciprocalQuotient
#print axioms buchstab_floorLiStep_Ioc
#print axioms buchstab_floorLiReciprocalInterval_eq_discretePotential
#print axioms buchstab_floorLiPrimeTail_eq_discretePotential

end RHLean.Analysis

import Mathlib
import RHLean.Analysis.PrimeSieveCollapseIdentity
import «research.VF_MID_FLOOR_LI_CRITICAL_BALANCE»

/-!
# Corrected floor-Li Buchstab brackets: ACTUAL Möbius source

Only source-exact identities. The imported smooth/rough collapse requires
Nat.sqrt x <= y, including literal y=Nat.sqrt x with no boundary term.
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
theorem buchstab_mertens_eq_floorLi_smooth_add_innovation_of_sqrt_le
    (y x : ℕ) (hy : 1 ≤ y) (hroot : Nat.sqrt x ≤ y) :
    mertensSummatory x =
      buchstabFloorLiSmoothBracket y x +
        buchstabFloorLiInnovationBracket y x := by
  calc
    mertensSummatory x =
        -primeSieveReciprocalMertensSignedSum y x +
          primeSieveSmoothMobiusMass y x :=
      mertensSummatory_eq_neg_signedSum_add_smoothMass_of_sqrt_le y x hy hroot
    _ = buchstabFloorLiSmoothBracket y x +
          buchstabFloorLiInnovationBracket y x := by
      rw [buchstab_actualPrimeTail_eq_floorLi_add_mismatch]
      unfold buchstabFloorLiSmoothBracket
        buchstabFloorLiInnovationBracket
      ring

/-- Preserve the original strict-root interface. -/
theorem buchstab_mertens_eq_floorLi_smooth_add_innovation
    (y x : ℕ) (hroot : Nat.sqrt x < y) :
    mertensSummatory x =
      buchstabFloorLiSmoothBracket y x +
        buchstabFloorLiInnovationBracket y x :=
  buchstab_mertens_eq_floorLi_smooth_add_innovation_of_sqrt_le
    y x (by omega) hroot.le

/-- Literal y=floor sqrt x: exact for every x>=1, no boundary term. -/
theorem buchstab_mertens_eq_floorLi_smooth_add_innovation_at_root
    (x : ℕ) (hx : 1 ≤ x) :
    mertensSummatory x =
      buchstabFloorLiSmoothBracket (Nat.sqrt x) x +
        buchstabFloorLiInnovationBracket (Nat.sqrt x) x := by
  have hy : 1 ≤ Nat.sqrt x := Nat.le_sqrt.mpr (by simpa using hx)
  exact buchstab_mertens_eq_floorLi_smooth_add_innovation_of_sqrt_le
    (Nat.sqrt x) x hy le_rfl

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

/-- Exact three-moment reciprocal-log kernel, WITHOUT an analytic claim. -/
theorem buchstab_reciprocal_log_three_term_kernel
    (H v : ℝ) (hH : H ≠ 0) (hHv : H - v ≠ 0) :
    1 / (H - v) =
      1 / H + v / H ^ 2 + v ^ 2 / H ^ 3 +
        v ^ 3 / (H ^ 3 * (H - v)) := by
  field_simp
  <;> ring


/-! ## Fixed-wheel square-shell difference: the same y=R at both endpoints -/

/-- Left endpoint of the square shell [R^2, (R+1)^2). -/
def buchstabSquareShellLower (R : ℕ) : ℕ := R ^ 2 - 1

/-- Right endpoint inclusive of the shell [R^2, (R+1)^2). -/
def buchstabSquareShellUpper (R : ℕ) : ℕ := (R + 1) ^ 2 - 1

/-- The small-prime wheel is FIXED at y=R throughout this shell. -/
def buchstabFloorLiSquareShellSmoothDelta (R : ℕ) : ℂ :=
  buchstabFloorLiSmoothBracket R (buchstabSquareShellUpper R) -
    buchstabFloorLiSmoothBracket R (buchstabSquareShellLower R)

/-- The high-prime innovation is centered BEFORE the shell difference. -/
def buchstabFloorLiSquareShellInnovationDelta (R : ℕ) : ℂ :=
  buchstabFloorLiInnovationBracket R (buchstabSquareShellUpper R) -
    buchstabFloorLiInnovationBracket R (buchstabSquareShellLower R)

/-- The lower endpoint is strictly below R^2. -/
theorem buchstab_squareShell_lower_sqrt_lt
    (R : ℕ) (hR : 2 ≤ R) :
    Nat.sqrt (buchstabSquareShellLower R) < R := by
  unfold buchstabSquareShellLower
  apply (Nat.sqrt_lt').2
  have hpos : 0 < R ^ 2 := pow_pos (by omega) 2
  omega

/-- The upper endpoint is strictly below (R+1)^2 and hence
has integer square root at most R. -/
theorem buchstab_squareShell_upper_sqrt_le
    (R : ℕ) (hR : 2 ≤ R) :
    Nat.sqrt (buchstabSquareShellUpper R) ≤ R := by
  unfold buchstabSquareShellUpper
  have hlt : Nat.sqrt ((R + 1) ^ 2 - 1) < R + 1 := by
    apply (Nat.sqrt_lt').2
    have hpos : 0 < (R + 1) ^ 2 := pow_pos (by omega) 2
    omega
  omega

/-- Exact shell identity: same prime-wheel cutoff y=R at BOTH
endpoints, no gate migration within the shell and no RH estimate. -/
theorem buchstab_fixedRootSquareShell_signed_delta
    (R : ℕ) (hR : 2 ≤ R) :
    mertensSummatory (buchstabSquareShellUpper R) -
        mertensSummatory (buchstabSquareShellLower R) =
      buchstabFloorLiSquareShellSmoothDelta R +
        buchstabFloorLiSquareShellInnovationDelta R := by
  have hlo := buchstab_mertens_eq_floorLi_smooth_add_innovation_of_sqrt_le
    R (buchstabSquareShellLower R) (by omega)
    (le_of_lt (buchstab_squareShell_lower_sqrt_lt R hR))
  have hhi := buchstab_mertens_eq_floorLi_smooth_add_innovation_of_sqrt_le
    R (buchstabSquareShellUpper R) (by omega)
    (buchstab_squareShell_upper_sqrt_le R hR)
  unfold buchstabFloorLiSquareShellSmoothDelta
    buchstabFloorLiSquareShellInnovationDelta
  rw [hhi, hlo]
  ring

/-- Literal centered smooth mass, with the same wheel on each endpoint.
This is the source-algebraic main-term subtraction; it gives no bound. -/
theorem buchstab_fixedRootSquareShell_smoothDelta_eq
    (R : ℕ) :
    buchstabFloorLiSquareShellSmoothDelta R =
      (primeSieveSmoothMobiusMass R (buchstabSquareShellUpper R) -
        primeSieveSmoothMobiusMass R (buchstabSquareShellLower R)) -
      (buchstabFloorLiPrimeTail R (buchstabSquareShellUpper R) -
        buchstabFloorLiPrimeTail R (buchstabSquareShellLower R)) := by
  unfold buchstabFloorLiSquareShellSmoothDelta
    buchstabFloorLiSmoothBracket
  ring

/-- Physical centered high-prime innovations, keeping the sign and the
actual small-scale Mertens cofactor inside each q-fiber. -/
theorem buchstab_fixedRootSquareShell_innovationDelta_eq
    (R : ℕ) :
    buchstabFloorLiSquareShellInnovationDelta R =
      -(buchstabFloorLiMismatchTail R (buchstabSquareShellUpper R) -
        buchstabFloorLiMismatchTail R (buchstabSquareShellLower R)) := by
  unfold buchstabFloorLiSquareShellInnovationDelta
    buchstabFloorLiInnovationBracket
  ring

#print axioms buchstab_fixedRootSquareShell_signed_delta
#print axioms buchstab_fixedRootSquareShell_smoothDelta_eq
#print axioms buchstab_fixedRootSquareShell_innovationDelta_eq

#print axioms buchstab_mertens_eq_floorLi_smooth_add_innovation_at_root
#print axioms buchstab_reciprocal_log_three_term_kernel
#print axioms buchstab_actualPrimeTail_eq_floorLi_add_mismatch
#print axioms buchstab_mertens_eq_floorLi_smooth_add_innovation
#print axioms buchstab_innovation_eq_signed_high_prime_cofactor
#print axioms buchstab_floorLiPrimeTail_eq_reciprocalQuotient
#print axioms buchstab_floorLiStep_Ioc
#print axioms buchstab_floorLiReciprocalInterval_eq_discretePotential
#print axioms buchstab_floorLiPrimeTail_eq_discretePotential

end RHLean.Analysis

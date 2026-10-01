import Mathlib
import RHLean.Proof.LowWheelSurvivorFloorExpansion
import «research.VF_MID_SQUARE_WHEEL_BACKLOG»
import «research.VF_MID_DIRECT_ROUGH_CHILD»

/-!
# VF-mid dyadic prefix-wheel / chronological-owner reduction

This file keeps the dyadic square-range argument entirely in the native
VF-mid geometry.  There is no Li replacement or Li centering here.

For a fixed low-prime wheel through z, the cumulative survivor count over
adjacent square interiors has only four endpoint rounding errors.  The
remaining discrepancy is then isolated as a signed late-removal correction,
and the existing least-prime-factor owner machinery supplies its exact
chronological factor-pair interpretation.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-! ## Fixed-prefix counting function and exact Boolean expansion -/

/-- Number of positive integers at most N surviving every prime coordinate
through z.  This is the finite counting function F_z(N). -/
def vfMidPrefixWheelCounting (z N : ℕ) : ℕ := by
  classical
  exact ((Finset.Ioc 0 N).filter (lowWheelHighSurvivor z)).card

/-- Exact Boolean-face floor expansion of F_z(N). -/
theorem vfMidPrefixWheelCounting_cast_int_eq_faceFloorSum
    (z N : ℕ) :
    (vfMidPrefixWheelCounting z N : ℤ) =
      ∑ t ∈ (primesUpTo z).powerset,
        booleanCubeSign t * ((N / primeFaceProduct t : ℕ) : ℤ) := by
  classical
  unfold vfMidPrefixWheelCounting
  calc
    ((((Finset.Ioc 0 N).filter (lowWheelHighSurvivor z)).card : ℕ) : ℤ) =
        ∑ q ∈ Finset.Ioc 0 N, lowWheelDivisorFaceSum z q := by
          calc
            ((((Finset.Ioc 0 N).filter (lowWheelHighSurvivor z)).card : ℕ) : ℤ) =
                ∑ q ∈ (Finset.Ioc 0 N).filter (lowWheelHighSurvivor z), (1 : ℤ) := by
                  simp
            _ = ∑ q ∈ Finset.Ioc 0 N,
                  if lowWheelHighSurvivor z q then (1 : ℤ) else 0 := by
                    rw [Finset.sum_filter]
            _ = ∑ q ∈ Finset.Ioc 0 N, lowWheelDivisorFaceSum z q := by
                  apply Finset.sum_congr rfl
                  intro q _hq
                  rw [lowWheelDivisorFaceSum_eq_survivorIndicator]
    _ = ∑ t ∈ (primesUpTo z).powerset,
        ∑ q ∈ Finset.Ioc 0 N,
          if primeFaceProduct t ∣ q then booleanCubeSign t else 0 := by
            unfold lowWheelDivisorFaceSum
            rw [Finset.sum_comm]
    _ = ∑ t ∈ (primesUpTo z).powerset,
        booleanCubeSign t * ((N / primeFaceProduct t : ℕ) : ℤ) := by
          apply Finset.sum_congr rfl
          intro t ht
          have hd :
              0 < primeFaceProduct t :=
            primeFaceProduct_pos_of_mem_powerset ht
          calc
            (∑ q ∈ Finset.Ioc 0 N,
                if primeFaceProduct t ∣ q then booleanCubeSign t else 0) =
              ∑ q ∈ (Finset.Ioc 0 N).filter
                  (fun q => primeFaceProduct t ∣ q),
                booleanCubeSign t := by
                  rw [Finset.sum_filter]
            _ = booleanCubeSign t *
                ((((Finset.Ioc 0 N).filter
                    (fun q => primeFaceProduct t ∣ q)).card : ℕ) : ℤ) := by
                  simp [mul_comm]
            _ = booleanCubeSign t * ((N / primeFaceProduct t : ℕ) : ℤ) := by
                  rw [card_Ioc_filter_dvd_eq_div_sub_div 0 N
                    (primeFaceProduct t) hd]
                  simp

/-- Real form of the exact Boolean-face floor expansion. -/
theorem vfMidPrefixWheelCounting_cast_real_eq_faceFloorSum
    (z N : ℕ) :
    (vfMidPrefixWheelCounting z N : ℝ) =
      ∑ t ∈ (primesUpTo z).powerset,
        (booleanCubeSign t : ℝ) *
          ((N / primeFaceProduct t : ℕ) : ℝ) := by
  have h := vfMidPrefixWheelCounting_cast_int_eq_faceFloorSum z N
  exact_mod_cast h

/-- Natural Euler density of the fixed prefix wheel. -/
def vfMidPrefixWheelDensity (z : ℕ) : ℝ :=
  ∏ p ∈ primesUpTo z, (1 - (p : ℝ)⁻¹)

/-- The Euler product is exactly the complete Boolean-face reciprocal sum. -/
theorem vfMidPrefixWheelDensity_eq_faceReciprocalSum
    (z : ℕ) :
    vfMidPrefixWheelDensity z =
      ∑ t ∈ (primesUpTo z).powerset,
        (booleanCubeSign t : ℝ) / (primeFaceProduct t : ℝ) := by
  classical
  have h :=
    Finset.prod_sub
      (fun _p : ℕ => (1 : ℝ))
      (fun p : ℕ => (p : ℝ)⁻¹)
      (primesUpTo z)
  simpa [vfMidPrefixWheelDensity, booleanCubeSign, primeFaceProduct,
    div_eq_mul_inv] using h

/-- A natural floor differs from the corresponding real quotient by less
than one. -/
theorem abs_natDiv_cast_sub_realDiv_lt_one
    (N d : ℕ) (hd : 0 < d) :
    |((N / d : ℕ) : ℝ) - (N : ℝ) / (d : ℝ)| < 1 := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hlowNat : (N / d) * d ≤ N :=
    Nat.div_mul_le_self N d
  have huppNat : N < (N / d + 1) * d := by
    exact (Nat.div_lt_iff_lt_mul hd).1 (Nat.lt_succ_self (N / d))
  have hlow :
      ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hdR]
    exact_mod_cast hlowNat
  have hupp :
      (N : ℝ) / (d : ℝ) < ((N / d : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hdR]
    exact_mod_cast huppNat
  rw [abs_lt]
  constructor <;> linarith

/-- Exact decomposition of one prefix-wheel counting error into the complete
signed Boolean cube of floor errors. -/
theorem vfMidPrefixWheelCounting_sub_density_mul_eq_faceFloorErrors
    (z N : ℕ) :
    (vfMidPrefixWheelCounting z N : ℝ) -
        vfMidPrefixWheelDensity z * (N : ℝ) =
      ∑ t ∈ (primesUpTo z).powerset,
        (booleanCubeSign t : ℝ) *
          (((N / primeFaceProduct t : ℕ) : ℝ) -
            (N : ℝ) / (primeFaceProduct t : ℝ)) := by
  rw [vfMidPrefixWheelCounting_cast_real_eq_faceFloorSum]
  rw [vfMidPrefixWheelDensity_eq_faceReciprocalSum]
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _ht
  ring

/-- Pointwise inclusion-exclusion error: at most one unit per Boolean face. -/
theorem abs_vfMidPrefixWheelCounting_sub_density_mul_le
    (z N : ℕ) :
    |(vfMidPrefixWheelCounting z N : ℝ) -
        vfMidPrefixWheelDensity z * (N : ℝ)| ≤
      (2 : ℝ) ^ (primesUpTo z).card := by
  rw [vfMidPrefixWheelCounting_sub_density_mul_eq_faceFloorErrors]
  calc
    |∑ t ∈ (primesUpTo z).powerset,
        (booleanCubeSign t : ℝ) *
          (((N / primeFaceProduct t : ℕ) : ℝ) -
            (N : ℝ) / (primeFaceProduct t : ℝ))| ≤
      ∑ t ∈ (primesUpTo z).powerset,
        |(booleanCubeSign t : ℝ) *
          (((N / primeFaceProduct t : ℕ) : ℝ) -
            (N : ℝ) / (primeFaceProduct t : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ (primesUpTo z).powerset, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      have hd :
          0 < primeFaceProduct t :=
        primeFaceProduct_pos_of_mem_powerset ht
      have herr :=
        abs_natDiv_cast_sub_realDiv_lt_one
          N (primeFaceProduct t) hd
      have hsign : |(booleanCubeSign t : ℝ)| = 1 := by
        simp [booleanCubeSign]
      rw [abs_mul, hsign, one_mul]
      exact le_of_lt herr
    _ = (2 : ℝ) ^ (primesUpTo z).card := by
      simp

/-! ## Dyadic square-range prefix cancellation -/

/-- Native VF square-interior carrier length on the root interval [A,B). -/
def vfMidDyadicInteriorLength (A B : ℕ) : ℝ :=
  (B : ℝ) ^ 2 - (A : ℝ) ^ 2 - (B : ℝ) + (A : ℝ)

/-- Four-endpoint cumulative prefix supply.  The subtraction of root counts
removes precisely the surviving boundary squares. -/
def vfMidDyadicPrefixSupply (z A B : ℕ) : ℝ :=
  (vfMidPrefixWheelCounting z (B ^ 2) : ℝ) -
    (vfMidPrefixWheelCounting z (A ^ 2) : ℝ) -
    (vfMidPrefixWheelCounting z B : ℝ) +
    (vfMidPrefixWheelCounting z A : ℝ)

/-- Exact four-endpoint decomposition: all prefix rounding remains at the two
square endpoints and two root endpoints. -/
theorem vfMidDyadicPrefixSupply_sub_density_eq_four_endpoint_errors
    (z A B : ℕ) :
    vfMidDyadicPrefixSupply z A B -
        vfMidPrefixWheelDensity z * vfMidDyadicInteriorLength A B =
      ((vfMidPrefixWheelCounting z (B ^ 2) : ℝ) -
          vfMidPrefixWheelDensity z * ((B : ℝ) ^ 2)) -
      ((vfMidPrefixWheelCounting z (A ^ 2) : ℝ) -
          vfMidPrefixWheelDensity z * ((A : ℝ) ^ 2)) -
      ((vfMidPrefixWheelCounting z B : ℝ) -
          vfMidPrefixWheelDensity z * (B : ℝ)) +
      ((vfMidPrefixWheelCounting z A : ℝ) -
          vfMidPrefixWheelDensity z * (A : ℝ)) := by
  unfold vfMidDyadicPrefixSupply vfMidDyadicInteriorLength
  push_cast
  ring

/-- The cumulative small-wheel error over any adjacent square range has only
four endpoint errors, independent of the number of blocks. -/
theorem abs_vfMidDyadicPrefixSupply_sub_density_le_four_pow
    (z A B : ℕ) :
    |vfMidDyadicPrefixSupply z A B -
        vfMidPrefixWheelDensity z * vfMidDyadicInteriorLength A B| ≤
      4 * ((2 : ℝ) ^ (primesUpTo z).card) := by
  rw [vfMidDyadicPrefixSupply_sub_density_eq_four_endpoint_errors]
  let M : ℝ := (2 : ℝ) ^ (primesUpTo z).card
  let eB2 : ℝ :=
    (vfMidPrefixWheelCounting z (B ^ 2) : ℝ) -
      vfMidPrefixWheelDensity z * ((B : ℝ) ^ 2)
  let eA2 : ℝ :=
    (vfMidPrefixWheelCounting z (A ^ 2) : ℝ) -
      vfMidPrefixWheelDensity z * ((A : ℝ) ^ 2)
  let eB : ℝ :=
    (vfMidPrefixWheelCounting z B : ℝ) -
      vfMidPrefixWheelDensity z * (B : ℝ)
  let eA : ℝ :=
    (vfMidPrefixWheelCounting z A : ℝ) -
      vfMidPrefixWheelDensity z * (A : ℝ)
  have hB2 : |eB2| ≤ M := by
    dsimp [eB2, M]
    simpa using
      abs_vfMidPrefixWheelCounting_sub_density_mul_le z (B ^ 2)
  have hA2 : |eA2| ≤ M := by
    dsimp [eA2, M]
    simpa using
      abs_vfMidPrefixWheelCounting_sub_density_mul_le z (A ^ 2)
  have hB : |eB| ≤ M := by
    dsimp [eB, M]
    simpa using abs_vfMidPrefixWheelCounting_sub_density_mul_le z B
  have hA : |eA| ≤ M := by
    dsimp [eA, M]
    simpa using abs_vfMidPrefixWheelCounting_sub_density_mul_le z A
  change |eB2 - eA2 - eB + eA| ≤ 4 * M
  calc
    |eB2 - eA2 - eB + eA| ≤
        |eB2 - eA2 - eB| + |eA| := by
          simpa using abs_add_le (eB2 - eA2 - eB) eA
    _ ≤ (|eB2 - eA2| + |eB|) + |eA| := by
          gcongr
          simpa [sub_eq_add_neg] using abs_add_le (eB2 - eA2) (-eB)
    _ ≤ ((|eB2| + |eA2|) + |eB|) + |eA| := by
          gcongr
          simpa [sub_eq_add_neg] using abs_add_le eB2 (-eA2)
    _ ≤ 4 * M := by linarith

/-- User-scale form of the prefix theorem.  If the complete Boolean cube has
at most A faces, the entire cumulative prefix rounding is at most 4A. -/
theorem abs_vfMidDyadicPrefixSupply_sub_density_le_four_mul_A
    {z A B : ℕ}
    (hfaces : 2 ^ (primesUpTo z).card ≤ A) :
    |vfMidDyadicPrefixSupply z A B -
        vfMidPrefixWheelDensity z * vfMidDyadicInteriorLength A B| ≤
      4 * (A : ℝ) := by
  have hfacesR :
      (2 : ℝ) ^ (primesUpTo z).card ≤ (A : ℝ) := by
    exact_mod_cast hfaces
  exact
    (abs_vfMidDyadicPrefixSupply_sub_density_le_four_pow z A B).trans
      (by nlinarith)

/-! ## Exact VF-centered signed late correction -/

/-- Exact prime population gained between the square endpoints A^2 and B^2. -/
def vfMidDyadicPrimeSupply (A B : ℕ) : ℝ :=
  (Nat.primeCounting (B ^ 2) : ℝ) -
    (Nat.primeCounting (A ^ 2) : ℝ)

/-- Exact native VF mass gained between the same square endpoints. -/
def vfMidDyadicVFMass (A B : ℕ) : ℝ :=
  vfMidFinishedMass B - vfMidFinishedMass A

/-- Total late removal after the fixed prefix, defined before any absolute
value is taken. -/
def vfMidDyadicLateRemoval (z A B : ℕ) : ℝ :=
  vfMidDyadicPrefixSupply z A B - vfMidDyadicPrimeSupply A B

/-- Exact VF-centered reference value that the late-removal total must track. -/
def vfMidDyadicLateReference (z A B : ℕ) : ℝ :=
  vfMidPrefixWheelDensity z * vfMidDyadicInteriorLength A B -
    vfMidDyadicVFMass A B

/-- Canonical signed identity.  The dyadic prime-minus-VF increment equals the
harmless prefix rounding minus the centered late-removal discrepancy. -/
theorem vfMidDyadicPrimeVFError_eq_prefixError_sub_lateCorrection
    (z A B : ℕ) :
    vfMidDyadicPrimeSupply A B - vfMidDyadicVFMass A B =
      (vfMidDyadicPrefixSupply z A B -
        vfMidPrefixWheelDensity z * vfMidDyadicInteriorLength A B) -
      (vfMidDyadicLateRemoval z A B -
        vfMidDyadicLateReference z A B) := by
  unfold vfMidDyadicPrimeSupply vfMidDyadicVFMass
    vfMidDyadicLateRemoval vfMidDyadicLateReference
  ring

/-- At square endpoints, the native VF error increment is exactly the dyadic
prime-minus-VF increment above. -/
theorem vfMidPrimeError_sq_sub_sq_eq_dyadicPrimeVFError
    {A B : ℕ} (hA : 2 ≤ A) (hB : 2 ≤ B) :
    vfMidPrimeError ((B : ℝ) ^ 2) -
        vfMidPrimeError ((A : ℝ) ^ 2) =
      vfMidDyadicPrimeSupply A B - vfMidDyadicVFMass A B := by
  unfold vfMidPrimeError vfMidPrimeCount vfMidDyadicPrimeSupply
    vfMidDyadicVFMass
  rw [vfMid_sq hA, vfMid_sq hB]
  simp only [Real.natFloor_natCast, Nat.cast_pow]
  ring

/-- The exact dyadic VF endpoint increment split into the four-endpoint prefix
rounding and the signed late-removal correction. -/
theorem vfMidPrimeError_sq_sub_sq_eq_prefixError_sub_lateCorrection
    (z : ℕ) {A B : ℕ} (hA : 2 ≤ A) (hB : 2 ≤ B) :
    vfMidPrimeError ((B : ℝ) ^ 2) -
        vfMidPrimeError ((A : ℝ) ^ 2) =
      (vfMidDyadicPrefixSupply z A B -
        vfMidPrefixWheelDensity z * vfMidDyadicInteriorLength A B) -
      (vfMidDyadicLateRemoval z A B -
        vfMidDyadicLateReference z A B) := by
  rw [vfMidPrimeError_sq_sub_sq_eq_dyadicPrimeVFError hA hB]
  exact vfMidDyadicPrimeVFError_eq_prefixError_sub_lateCorrection z A B

/-! ## Chronological high-owner terminal reduction -/

/-- A global terminal cutoff p^3 >= B^2 works simultaneously on every square
block r in [A,B): the existing owner child is then prime. -/
theorem vfMidDyadicTerminalOwner_child_prime
    {A B r p n : ℕ}
    (hr : r ∈ Finset.Ico A B)
    (hn : n ∈ vfMidSquareBandCompositeOwner r p)
    (hterminal : B ^ 2 ≤ p ^ 3) :
    (n / p).Prime := by
  have hrB : r + 1 ≤ B := by
    have := (Finset.mem_Ico.mp hr).2
    omega
  have hsquares : (r + 1) ^ 2 ≤ B ^ 2 :=
    Nat.pow_le_pow_left hrB 2
  exact
    vfMidSquareBandCompositeOwner_child_prime_of_upperSquare_le_cube
      hn (hsquares.trans hterminal)

/-- In that terminal range the chronological owner decomposition is literally
a product of two distinct primes: p is the least prime factor and n/p is a
strictly larger prime. -/
theorem vfMidDyadicTerminalOwner_eq_distinctPrimePair
    {A B r p n : ℕ}
    (hr : r ∈ Finset.Ico A B)
    (hn : n ∈ vfMidSquareBandCompositeOwner r p)
    (hterminal : B ^ 2 ≤ p ^ 3) :
    p.Prime ∧ (n / p).Prime ∧ p < n / p ∧ p * (n / p) = n := by
  have hp := vfMidSquareBandCompositeOwner_owner_prime hn
  have hchildPrime :=
    vfMidDyadicTerminalOwner_child_prime hr hn hterminal
  have hreconstruct :=
    vfMidSquareBandCompositeOwner_reconstruct hn
  have hchildGe :=
    vfMidSquareBandCompositeOwner_child_ge_owner hn
  have hpLeR :=
    vfMidSquareBandCompositeOwner_owner_le_r hn
  have hnSite :=
    (Finset.mem_filter.mp hn).1
  have hnI := Finset.mem_Ioo.mp hnSite
  have hne : p ≠ n / p := by
    intro heq
    have hsq : p ^ 2 = n := by
      calc
        p ^ 2 = p * p := by ring
        _ = p * (n / p) := by rw [heq]
        _ = n := hreconstruct
    have hpSqLe : p ^ 2 ≤ r ^ 2 :=
      Nat.pow_le_pow_left hpLeR 2
    omega
  refine ⟨hp, hchildPrime, ?_, hreconstruct⟩
  exact lt_of_le_of_ne hchildGe (Ne.symm hne)

/-- The single arithmetic theorem left by the dyadic reduction: the signed
late-removal total must track its exact native VF reference before absolute
values are taken. -/
def VFMidDyadicSignedLateCorrectionStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ A B : ℕ, 2 ≤ A → A < B → B ≤ 2 * A →
      |vfMidDyadicLateRemoval 2 A B -
          vfMidDyadicLateReference 2 A B| ≤
        C * (A : ℝ) * Real.log A

/-- A signed late-correction estimate immediately yields the corresponding
native VF dyadic increment bound.  The prefix term contributes only 4A. -/
theorem abs_vfMidPrimeError_sq_sub_sq_le_of_signedLateCorrection
    (hcor : VFMidDyadicSignedLateCorrectionStatement) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ A B : ℕ, 2 ≤ A → A < B → B ≤ 2 * A →
        |vfMidPrimeError ((B : ℝ) ^ 2) -
            vfMidPrimeError ((A : ℝ) ^ 2)| ≤
          4 * (A : ℝ) + C * (A : ℝ) * Real.log A := by
  rcases hcor with ⟨C, hC0, hC⟩
  refine ⟨C, hC0, ?_⟩
  intro A B hA hAB hBA
  rw [vfMidPrimeError_sq_sub_sq_eq_prefixError_sub_lateCorrection
    2 hA (hA.trans hAB.le)]
  have hprefix :
      |vfMidDyadicPrefixSupply 2 A B -
          vfMidPrefixWheelDensity 2 * vfMidDyadicInteriorLength A B| ≤
        4 * (A : ℝ) := by
    apply abs_vfMidDyadicPrefixSupply_sub_density_le_four_mul_A
    have hcard : (primesUpTo 2).card = 1 := by native_decide
    rw [hcard]
    norm_num
    omega
  have hlate := hC A B hA hAB hBA
  calc
    |(vfMidDyadicPrefixSupply 2 A B -
          vfMidPrefixWheelDensity 2 * vfMidDyadicInteriorLength A B) -
        (vfMidDyadicLateRemoval 2 A B -
          vfMidDyadicLateReference 2 A B)| ≤
      |vfMidDyadicPrefixSupply 2 A B -
          vfMidPrefixWheelDensity 2 * vfMidDyadicInteriorLength A B| +
      |vfMidDyadicLateRemoval 2 A B -
          vfMidDyadicLateReference 2 A B| := by
        simpa [sub_eq_add_neg] using
          abs_add_le
            (vfMidDyadicPrefixSupply 2 A B -
              vfMidPrefixWheelDensity 2 * vfMidDyadicInteriorLength A B)
            (-(vfMidDyadicLateRemoval 2 A B -
              vfMidDyadicLateReference 2 A B))
    _ ≤ 4 * (A : ℝ) + C * (A : ℝ) * Real.log A :=
      add_le_add hprefix hlate

end RHLean.Analysis

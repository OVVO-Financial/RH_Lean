import «research.VF_MID_DYADIC_OWNER_EXACT»

/-!
# Weighted integral recovery on the actual dyadic square survivors

For `3 ≤ A ≤ R < 2*A`, the existing arithmetic classification says that
every starting-wheel survivor in `(R²,(R+1)²)` is either a prime, with
Möbius value `-1`, or a distinct semiprime, with Möbius value `1`.
This file retains an arbitrary real weight at every site. In particular,
one may substitute `log n * (N/n - 1)` without losing the kernel or the
actual composite removal.

The resulting two-channel recovery is integral with multiplier two. Its
matrix has determinant two, its squared Euclidean cost is exactly two,
and it has no integral inverse with multiplier one. These are concrete
finite recovery statements. They do not supply a chain of order `R`,
the physical finite-place gain `Ga`, or an estimate for the recovered
prime channel. Proper prime powers remain separate from this prime-site
decoder and must be restored by the complete `G_z` source.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- Actual weighted population surviving the wheel through `A`. -/
def nativeSquareSurvivorWeight (A R : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ vfMidSquarePrefixWheelSurvivors A R, w n

/-- Actual signed Möbius channel, with the same site weights. -/
def nativeSquareSurvivorMobiusWeight (A R : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ vfMidSquarePrefixWheelSurvivors A R, (μ n : ℝ) * w n

/-- Prime contribution on the actual open square block. -/
def nativeSquarePrimeWeight (R : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ vfMidSquareWheelPrimes R, w n

/-- Composite removal from precisely the same starting-wheel carrier. -/
def nativeSquareCompositeWeight (A R : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ vfMidSquareBandPrefixCompositeSurvivors A R, w n

theorem nativeSquareSurvivorWeight_eq_prime_add_composite
    {A R : ℕ} (hR : 2 ≤ R) (hAR : A ≤ R) (w : ℕ → ℝ) :
    nativeSquareSurvivorWeight A R w =
      nativeSquarePrimeWeight R w + nativeSquareCompositeWeight A R w := by
  rw [nativeSquareSurvivorWeight,
    vfMidSquarePrefixWheelSurvivors_eq_prime_union_prefixComposite hR hAR,
    Finset.sum_union (vfMidSquareWheelPrimes_disjoint_prefixComposite A R)]
  rfl

/-- The dyadic sign classification survives arbitrary weights; no absolute
values, probability law, or replacement coefficient field is introduced. -/
theorem nativeSquareSurvivorMobiusWeight_eq_composite_sub_prime
    {A R : ℕ} (hA : 3 ≤ A) (hAR : A ≤ R) (hRlt : R < 2 * A)
    (w : ℕ → ℝ) :
    nativeSquareSurvivorMobiusWeight A R w =
      nativeSquareCompositeWeight A R w - nativeSquarePrimeWeight R w := by
  rw [nativeSquareSurvivorMobiusWeight,
    vfMidSquarePrefixWheelSurvivors_eq_prime_union_prefixComposite
      (by omega : 2 ≤ R) hAR,
    Finset.sum_union (vfMidSquareWheelPrimes_disjoint_prefixComposite A R)]
  have hp : (∑ n ∈ vfMidSquareWheelPrimes R, (μ n : ℝ) * w n) =
      -nativeSquarePrimeWeight R w := by
    rw [nativeSquarePrimeWeight, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnPrime : n.Prime := (Finset.mem_filter.mp hn).2
    rw [ArithmeticFunction.moebius_apply_prime hnPrime]
    simp
  have hc : (∑ n ∈ vfMidSquareBandPrefixCompositeSurvivors A R,
      (μ n : ℝ) * w n) = nativeSquareCompositeWeight A R w := by
    unfold nativeSquareCompositeWeight
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [vfMidSquareBandPrefixComposite_moebius_eq_one_of_subdoubling
      hA hAR hRlt hn]
    simp
  rw [hp, hc]
  ring

/-- Exact weighted recovery of both arithmetic channels by one common
integer matrix. The sign information is retained until recovery. -/
theorem nativeSquareWeightedRecovery
    {A R : ℕ} (hA : 3 ≤ A) (hAR : A ≤ R) (hRlt : R < 2 * A)
    (w : ℕ → ℝ) :
    2 * nativeSquarePrimeWeight R w =
        nativeSquareSurvivorWeight A R w - nativeSquareSurvivorMobiusWeight A R w ∧
      2 * nativeSquareCompositeWeight A R w =
        nativeSquareSurvivorWeight A R w + nativeSquareSurvivorMobiusWeight A R w := by
  rw [nativeSquareSurvivorWeight_eq_prime_add_composite (by omega) hAR w,
    nativeSquareSurvivorMobiusWeight_eq_composite_sub_prime hA hAR hRlt w]
  constructor <;> ring

/-- The total squared cost belongs to the same recovered channels and
the same weights. It is exactly twice their squared energy. -/
theorem nativeSquareWeightedRecovery_energy
    {A R : ℕ} (hA : 3 ≤ A) (hAR : A ≤ R) (hRlt : R < 2 * A)
    (w : ℕ → ℝ) :
    nativeSquareSurvivorWeight A R w ^ 2 +
        nativeSquareSurvivorMobiusWeight A R w ^ 2 =
      2 * (nativeSquarePrimeWeight R w ^ 2 +
        nativeSquareCompositeWeight A R w ^ 2) := by
  rw [nativeSquareSurvivorWeight_eq_prime_add_composite (by omega) hAR w,
    nativeSquareSurvivorMobiusWeight_eq_composite_sub_prime hA hAR hRlt w]
  ring

/-- The resulting Euclidean estimate is an exact cost accounting for the
two channels. It contains no factor proportional to the square clock. -/
theorem nativeSquarePrimeWeight_sq_le_half_energy
    {A R : ℕ} (hA : 3 ≤ A) (hAR : A ≤ R) (hRlt : R < 2 * A)
    (w : ℕ → ℝ) :
    nativeSquarePrimeWeight R w ^ 2 ≤
      (nativeSquareSurvivorWeight A R w ^ 2 +
        nativeSquareSurvivorMobiusWeight A R w ^ 2) / 2 := by
  rw [nativeSquareWeightedRecovery_energy hA hAR hRlt w]
  nlinarith [sq_nonneg (nativeSquareCompositeWeight A R w)]

/-- At the actual full cutoff the survivor channel is exactly the prime
channel, with every original weight retained. -/
theorem nativeSquareSurvivorWeight_full
    {R : ℕ} (hR : 2 ≤ R) (w : ℕ → ℝ) :
    nativeSquareSurvivorWeight R R w = nativeSquarePrimeWeight R w := by
  rw [nativeSquareSurvivorWeight, vfMidSquarePrefixWheelSurvivors_full,
    vfMidSquareWheelSurvivors_eq_primes R hR]
  rfl

theorem nativeSquareCompositeWeight_full
    {R : ℕ} (hR : 2 ≤ R) (w : ℕ → ℝ) :
    nativeSquareCompositeWeight R R w = 0 := by
  have h := nativeSquareSurvivorWeight_eq_prime_add_composite hR (le_refl R) w
  rw [nativeSquareSurvivorWeight_full hR w] at h
  linarith

/-- Sharpness on the genuine arithmetic carrier: the full cutoff has no
semiprime channel, so the uncentered norm estimate is exactly saturated. -/
theorem nativeSquarePrimeWeight_full_energy_equality
    {R : ℕ} (hR : 3 ≤ R) (w : ℕ → ℝ) :
    nativeSquarePrimeWeight R w ^ 2 =
      (nativeSquareSurvivorWeight R R w ^ 2 +
        nativeSquareSurvivorMobiusWeight R R w ^ 2) / 2 := by
  rw [nativeSquareWeightedRecovery_energy hR (le_refl R) (by omega) w,
    nativeSquareCompositeWeight_full (by omega : 2 ≤ R) w]
  ring

/-- The complete kernel weight is a permitted specialization. This is
still a prime-site identity, with proper prime powers kept separate. -/
theorem nativeSquareWeightedRecovery_completeKernel
    {A R : ℕ} (hA : 3 ≤ A) (hAR : A ≤ R) (hRlt : R < 2 * A) (N : ℝ) :
    2 * nativeSquarePrimeWeight R (fun n => Real.log n * (N / n - 1)) =
      nativeSquareSurvivorWeight A R (fun n => Real.log n * (N / n - 1)) -
        nativeSquareSurvivorMobiusWeight A R (fun n => Real.log n * (N / n - 1)) :=
  (nativeSquareWeightedRecovery hA hAR hRlt _).1

end RHLean.Analysis

namespace RHLean.Geometry

/-- Columns are the actual `(unsigned, Möbius)` signatures of a prime
and a distinct semiprime on a subdoubling survivor block. -/
def nativeSquareRecoveryMatrix : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 1; -1, 1]

/-- Integral recovery numerator. Division by two is accounted for below. -/
def nativeSquareRecoveryNumerator : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, -1; 1, 1]

theorem nativeSquareRecoveryMatrix_det :
    nativeSquareRecoveryMatrix.det = 2 := by
  norm_num [nativeSquareRecoveryMatrix, Matrix.det_fin_two]

theorem nativeSquareRecoveryNumerator_mul_matrix :
    nativeSquareRecoveryNumerator * nativeSquareRecoveryMatrix =
      2 • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nativeSquareRecoveryNumerator, nativeSquareRecoveryMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- The multiplier two is forced over the integer lattice; merely naming
the decoder an integral equivalence would discard a genuine index cost. -/
theorem nativeSquareRecoveryMatrix_no_integral_left_inverse :
    ¬ ∃ M : Matrix (Fin 2) (Fin 2) ℤ,
      M * nativeSquareRecoveryMatrix = 1 := by
  rintro ⟨M, hM⟩
  have h00 := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℤ => X 0 0) hM
  have h01 := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℤ => X 0 1) hM
  norm_num [nativeSquareRecoveryMatrix, Matrix.mul_apply,
    Fin.sum_univ_succ] at h00 h01
  omega

/-- The source of this recovery has exactly two scalar coordinates.
This dimension is independent of the native square clock. -/
theorem nativeSquareRecovery_finrank :
    Module.finrank ℚ (Fin 2 → ℚ) = 2 := by
  simp

end RHLean.Geometry

#print axioms RHLean.Analysis.nativeSquareWeightedRecovery
#print axioms RHLean.Analysis.nativeSquareWeightedRecovery_energy
#print axioms RHLean.Analysis.nativeSquareWeightedRecovery_completeKernel
#print axioms RHLean.Geometry.nativeSquareRecoveryNumerator_mul_matrix
#print axioms RHLean.Geometry.nativeSquareRecoveryMatrix_no_integral_left_inverse

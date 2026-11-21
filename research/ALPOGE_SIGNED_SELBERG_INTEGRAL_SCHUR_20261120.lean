import Mathlib
import RHLean.Analysis.NativePNTSignedSecondSelbergFrontierCharge

/-!
# Signed Selberg prime-band lattice: complete square + mixed face

Select genuinely prime owners p_i in the band 3R/4 <= p_i < R.
All physical pair products p_i*p_j, INCLUDING prime squares, live in
(R^2-1)/2 < p_i*p_j <= R^2-1, hence have reciprocal quotient exactly 1.

The FULL signed K2 face in this band (ordered off-diagonal entries each
carrying half the coefficient K2(pq)) is D*(2I-J)*D, D_ii=log p_i.

This is the source-native replacement for the unimodular lower-prefix
incidence matrix. Its centered integer lattice has the exact action 2I,
while the scalar mean direction is the separately retained principal charge.

There is NO claim here that the remaining full signed Selberg source is
controlled, that logarithms are p-adic integers, that the automorphic
geometric error hypotheses hold, or that RH follows.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- The coefficient lattice of the COMPLETE signed K2 prime-square and
distinct-prime face: diagonals +1 and off-diagonals -1. -/
def alpogeSelbergBandIntegerMatrix (m : ℕ) :
    Matrix (Fin m) (Fin m) ℤ :=
  fun i j => if i = j then 1 else -1

/-- Integer response of the full signed band matrix. -/
def alpogeSelbergBandIntegerResponse {m : ℕ}
    (v : Fin m → ℤ) (i : Fin m) : ℤ :=
  ∑ j : Fin m, alpogeSelbergBandIntegerMatrix m i j * v j

/-- Exact row formula S=2I-J, with the principal return retained. -/
theorem alpogeSelbergBandIntegerResponse_eq_principal
    {m : ℕ} (v : Fin m → ℤ) (i : Fin m) :
    alpogeSelbergBandIntegerResponse v i =
      2 * v i - ∑ j : Fin m, v j := by
  unfold alpogeSelbergBandIntegerResponse
  calc
    (∑ j : Fin m, alpogeSelbergBandIntegerMatrix m i j * v j) =
        ∑ j : Fin m, ((if i = j then (2 : ℤ) else 0) * v j - v j) := by
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hij : i = j
      · subst j
        simp [alpogeSelbergBandIntegerMatrix]
        ring
      · simp [alpogeSelbergBandIntegerMatrix, hij]
    _ = 2 * v i - ∑ j : Fin m, v j := by
      rw [Finset.sum_sub_distrib]
      simp

/-- All centered integral directions acquire exact divisibility by TWO. -/
theorem alpogeSelbergBandCentered_integer_double
    {m : ℕ} (v : Fin m → ℤ)
    (hzero : (∑ j : Fin m, v j) = 0) (i : Fin m) :
    alpogeSelbergBandIntegerResponse v i = 2 * v i := by
  rw [alpogeSelbergBandIntegerResponse_eq_principal, hzero, sub_zero]

/-- Even without centering, every pairwise response difference is even.
This is the source-native congruence inherited from 2I-J. -/
theorem alpogeSelbergBandResponseDifference
    {m : ℕ} (v : Fin m → ℤ) (i j : Fin m) :
    alpogeSelbergBandIntegerResponse v i -
        alpogeSelbergBandIntegerResponse v j =
      2 * (v i - v j) := by
  rw [alpogeSelbergBandIntegerResponse_eq_principal,
      alpogeSelbergBandIntegerResponse_eq_principal]
  ring

/-- The centered source has no growing upper/lower operator-norm tax:
its squared response energy equals FOUR times its squared input energy. -/
theorem alpogeSelbergBandCentered_energy
    {m : ℕ} (v : Fin m → ℝ)
    (hzero : (∑ j : Fin m, v j) = 0) :
    (∑ i : Fin m, (2 * v i - ∑ j : Fin m, v j) ^ 2) =
      4 * ∑ i : Fin m, (v i) ^ 2 := by
  calc
    (∑ i : Fin m, (2 * v i - ∑ j : Fin m, v j) ^ 2) =
        ∑ i : Fin m, 4 * (v i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [hzero]
      ring
    _ = 4 * ∑ i : Fin m, (v i) ^ 2 := by
      rw [Finset.mul_sum]

/-- The three-prime normalized block has nonunit integral determinant.
Its eigenvalues are 2, 2, -1, so its singular-value condition number is 2.
This is an exact formal coefficient lattice, NOT a p-adic bound on log p. -/
theorem alpogeSelbergBandThree_det :
    (alpogeSelbergBandIntegerMatrix 3).det = (-4 : ℤ) := by
  norm_num [Matrix.det_fin_three, alpogeSelbergBandIntegerMatrix]

/-- A rational, source-preserving prime interval: each owner lies in
[3R/4, R). This band is populated at near-square-root multiplicity
by the ordinary PNT (not asserted as a new Lean theorem here). -/
def AlpogeSelbergPrimeBand (R p : ℕ) : Prop :=
  p.Prime ∧ 3 * R ≤ 4 * p ∧ p < R

/-- EVERY pair product, including a prime square, has EXACT quotient one.
This avoids the earlier high-prime prefix's uncontrolled response depth. -/
theorem alpogeSelbergPrimeBand_quotient_one
    (R p q : ℕ) (hR : 4 ≤ R)
    (hp : AlpogeSelbergPrimeBand R p)
    (hq : AlpogeSelbergPrimeBand R q) :
    (R ^ 2 - 1) / (p * q) = 1 := by
  have hRpos : 0 < R := by omega
  have hupper : p * q < R ^ 2 := by
    have hpq : p * q ≤ p * R :=
      Nat.mul_le_mul_left p (Nat.le_of_lt hq.2.2)
    have hpR : p * R < R * R :=
      Nat.mul_lt_mul_of_pos_right hp.2.2 hRpos
    nlinarith
  have hmul : (3 * R) * (3 * R) ≤ (4 * p) * (4 * q) :=
    Nat.mul_le_mul hp.2.1 hq.2.1
  have hlower : R ^ 2 ≤ 2 * (p * q) := by
    nlinarith
  have hlo : 1 * (p * q) ≤ R ^ 2 - 1 := by omega
  have hhi : R ^ 2 - 1 < (1 + 1) * (p * q) := by omega
  exact Nat.div_eq_of_lt_le hlo hhi

/-- The exact prime-square K2 term has POSITIVE sign after E(1)=-1. -/
theorem alpogeSelbergPrimeBand_square_source
    (R p : ℕ) (hR : 4 ≤ R)
    (hp : AlpogeSelbergPrimeBand R p) :
    nativePNTSignedSecondSelbergKernel (p ^ 2) *
        nativePNTError ((R ^ 2 - 1) / (p ^ 2)) =
      (Real.log (p : ℝ)) ^ 2 := by
  have hq : (R ^ 2 - 1) / (p ^ 2) = 1 := by
    simpa [pow_two] using alpogeSelbergPrimeBand_quotient_one R p p hR hp hp
  rw [hq, nativePNTSignedSecondSelbergKernel_prime_sq p hp.1,
      nativePNTError_one]
  ring

/-- The exact DISTINCT semiprime K2 term has NEGATIVE sign after E(1)=-1.
Both square and mixed faces must be summed before claiming any gain. -/
theorem alpogeSelbergPrimeBand_distinct_source
    (R p q : ℕ) (hR : 4 ≤ R)
    (hp : AlpogeSelbergPrimeBand R p)
    (hq : AlpogeSelbergPrimeBand R q)
    (hpq : p ≠ q) :
    nativePNTSignedSecondSelbergKernel (p * q) *
        nativePNTError ((R ^ 2 - 1) / (p * q)) =
      -(2 * Real.log (p : ℝ) * Real.log (q : ℝ)) := by
  rw [alpogeSelbergPrimeBand_quotient_one R p q hR hp hq,
      nativePNTSignedSecondSelbergKernel_mul_distinct_primes
        p q hp.1 hq.1 hpq, nativePNTError_one]
  ring

/-- Symmetric source matrix: a distinct product contributes half to each
ordered orientation, so that the double sum counts it exactly ONCE. -/
def alpogeSelbergPrimeBandRealMatrix {m : ℕ}
    (R : ℕ) (p : Fin m → ℕ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j =>
    if i = j then
      nativePNTSignedSecondSelbergKernel ((p i) ^ 2) *
        nativePNTError ((R ^ 2 - 1) / ((p i) ^ 2))
    else
      (1 / 2 : ℝ) *
        nativePNTSignedSecondSelbergKernel ((p i) * (p j)) *
        nativePNTError ((R ^ 2 - 1) / ((p i) * (p j)))

/-- Complete actual-source matrix factorizes as D*(2I-J)*D, where
D_ii=log(p_i). The integer matrix arises from *both* K2 source faces,
not from an arbitrarily chosen prime incidence labeling. -/
theorem alpogeSelbergPrimeBandRealMatrix_eq_schur
    {m : ℕ} (R : ℕ) (p : Fin m → ℕ)
    (hR : 4 ≤ R)
    (hp : ∀ i, AlpogeSelbergPrimeBand R (p i))
    (hinj : Function.Injective p) (i j : Fin m) :
    alpogeSelbergPrimeBandRealMatrix R p i j =
      Real.log (p i : ℝ) *
      (if i = j then (1 : ℝ) else -1) *
      Real.log (p j : ℝ) := by
  by_cases hij : i = j
  · subst j
    simp only [alpogeSelbergPrimeBandRealMatrix]
    simp only [ite_true]
    rw [alpogeSelbergPrimeBand_square_source R (p i) hR (hp i)]
    ring
  · have hpq : p i ≠ p j := fun heq => hij (hinj heq)
    simp [alpogeSelbergPrimeBandRealMatrix, hij]
    rw [mul_assoc, alpogeSelbergPrimeBand_distinct_source R (p i) (p j)
      hR (hp i) (hp j) hpq]
    ring

end RHLean.Analysis

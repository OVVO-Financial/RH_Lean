import Mathlib
import RHLean.Analysis.NativePNTMertens
import RHLean.Arithmetic.PrimorialReciprocalMobiusFactorization

/-!
# Truncated primorial wheel boundary decomposition

This module keeps the reciprocal Möbius cancellation finite and exact while
allowing an ordinary prefix cutoff to truncate the Boolean prime cube.

For a finite prime set `P`, the truncated wheel profile is

`T_P(X) = sum_{t subset P, prod(t) <= X} mu(prod(t)) / prod(t)`.

It has two key properties.

* Once `X` reaches the full wheel product, `T_P(X)` is the complete signed
  contraction factor `prod_{p in P} (1 - 1/p)`.
* Adjoining one fresh prime gives the exact recurrence
  `T_{insert p P}(X) = T_P(X) - (1/p) T_P(X/p)`.

No asymptotic prime distribution, infinite Euler product, or Mertens product
theorem is used.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Arithmetic

/-- Product of all prime coordinates in a finite wheel. -/
def primorialWheelProduct (P : Finset ℕ) : ℕ := P.prod id

/-- Truncated signed reciprocal Boolean-cube profile. -/
def primorialTruncatedSignedReciprocalCube (P : Finset ℕ) (X : ℕ) : ℝ :=
  ∑ t ∈ P.powerset.filter (fun t => primeFaceProduct t ≤ X),
    ((booleanCubeSign t : ℤ) : ℝ) / (primeFaceProduct t : ℝ)

/-- Möbius form of the truncated signed reciprocal cube. -/
theorem primorialTruncatedSignedReciprocalCube_eq_moebius
    (P : Finset ℕ) (X : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) :
    primorialTruncatedSignedReciprocalCube P X =
      ∑ t ∈ P.powerset.filter (fun t => primeFaceProduct t ≤ X),
        (ArithmeticFunction.moebius (primeFaceProduct t) : ℝ) /
          (primeFaceProduct t : ℝ) := by
  unfold primorialTruncatedSignedReciprocalCube
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_filter] at ht
  rw [moebius_primeFaceProduct_eq_booleanCubeSign t]
  intro p hp
  exact hprime p (Finset.mem_of_mem_powerset ht.1 hp)

/-- Every face product divides the full wheel product. -/
theorem primeFaceProduct_dvd_primorialWheelProduct
    {P t : Finset ℕ} (ht : t ⊆ P) :
    primeFaceProduct t ∣ primorialWheelProduct P := by
  classical
  unfold primeFaceProduct primorialWheelProduct
  exact Finset.prod_dvd_prod_of_subset ht

/-- Every face product is at most the full wheel product when all wheel entries
are positive. -/
theorem primeFaceProduct_le_primorialWheelProduct
    {P t : Finset ℕ} (ht : t ⊆ P) (hpos : ∀ p ∈ P, 1 ≤ p) :
    primeFaceProduct t ≤ primorialWheelProduct P := by
  have hdvd := primeFaceProduct_dvd_primorialWheelProduct ht
  have hfullpos : 0 < primorialWheelProduct P := by
    unfold primorialWheelProduct
    exact Finset.prod_pos fun p hp => by omega
  exact Nat.le_of_dvd hfullpos hdvd

/-- Once the cutoff reaches the full wheel product, the truncated cube is the
complete signed reciprocal cube. -/
theorem primorialTruncatedSignedReciprocalCube_eq_complete
    (P : Finset ℕ) (X : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hX : primorialWheelProduct P ≤ X) :
    primorialTruncatedSignedReciprocalCube P X =
      primorialSignedReciprocalCube P := by
  unfold primorialTruncatedSignedReciprocalCube primorialSignedReciprocalCube
  have hfilter : P.powerset.filter (fun t => primeFaceProduct t ≤ X) = P.powerset := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro ht
      exact ht.1
    · intro ht
      refine ⟨ht, ?_⟩
      exact le_trans
        (primeFaceProduct_le_primorialWheelProduct ht
          (fun p hp => (hprime p hp).one_le)) hX
  rw [hfilter]

/-- Therefore the stabilized truncated profile is exactly the finite signed
contraction product. -/
theorem primorialTruncatedSignedReciprocalCube_eq_factor
    (P : Finset ℕ) (X : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hX : primorialWheelProduct P ≤ X) :
    primorialTruncatedSignedReciprocalCube P X =
      primorialSignedContractionFactor P := by
  rw [primorialTruncatedSignedReciprocalCube_eq_complete P X hprime hX]
  exact primorialSignedReciprocalCube_eq_factor P hprime

/-- Exact fresh-prime recurrence for the truncated wheel profile. -/
theorem primorialTruncatedSignedReciprocalCube_insert
    {P : Finset ℕ} {p X : ℕ}
    (hp : p ∉ P) (hpPrime : p.Prime) :
    primorialTruncatedSignedReciprocalCube (insert p P) X =
      primorialTruncatedSignedReciprocalCube P X -
        (1 / (p : ℝ)) * primorialTruncatedSignedReciprocalCube P (X / p) := by
  classical
  unfold primorialTruncatedSignedReciprocalCube
  rw [Finset.sum_powerset_insert hp]
  have hpR0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpPrime.ne_zero
  have hsecond :
      (∑ t ∈ P.powerset.filter
          (fun t => primeFaceProduct (insert p t) ≤ X),
        ((booleanCubeSign (insert p t) : ℤ) : ℝ) /
          (primeFaceProduct (insert p t) : ℝ)) =
        -(1 / (p : ℝ)) *
          ∑ t ∈ P.powerset.filter (fun t => primeFaceProduct t ≤ X / p),
            ((booleanCubeSign t : ℤ) : ℝ) / (primeFaceProduct t : ℝ) := by
    have hfilter :
        P.powerset.filter (fun t => primeFaceProduct (insert p t) ≤ X) =
          P.powerset.filter (fun t => primeFaceProduct t ≤ X / p) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_powerset]
      constructor
      · rintro ⟨ht, hle⟩
        have hpt : p ∉ t := Finset.notMem_of_mem_powerset_of_notMem ht hp
        have hprod : primeFaceProduct (insert p t) = p * primeFaceProduct t := by
          simp [primeFaceProduct, hpt]
        rw [hprod] at hle
        exact ⟨ht, Nat.le_div_iff_mul_le hpPrime.pos |>.2 hle⟩
      · rintro ⟨ht, hle⟩
        have hpt : p ∉ t := Finset.notMem_of_mem_powerset_of_notMem ht hp
        have hprod : primeFaceProduct (insert p t) = p * primeFaceProduct t := by
          simp [primeFaceProduct, hpt]
        refine ⟨ht, ?_⟩
        rw [hprod]
        exact (Nat.le_div_iff_mul_le hpPrime.pos).1 hle
    rw [hfilter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_filter] at ht
    have hpt : p ∉ t := Finset.notMem_of_mem_powerset_of_notMem ht.1 hp
    have hsign :
        ((booleanCubeSign (insert p t) : ℤ) : ℝ) =
          -((booleanCubeSign t : ℤ) : ℝ) := by
      unfold booleanCubeSign
      rw [Finset.card_insert_of_notMem hpt, pow_succ]
      push_cast
      ring
    rw [hsign]
    simp only [primeFaceProduct]
    rw [Finset.prod_insert hpt]
    push_cast
    simp only [id_eq]
    field_simp [hpR0]
  rw [hsecond]
  ring

/-- Complete-plus-boundary decomposition of a truncated wheel profile. -/
theorem primorialTruncatedSignedReciprocalCube_complete_boundary
    (P : Finset ℕ) (X : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) :
    primorialTruncatedSignedReciprocalCube P X =
      primorialSignedContractionFactor P +
        (primorialTruncatedSignedReciprocalCube P X -
          primorialSignedContractionFactor P) := by
  ring

/-- The ordinary reciprocal Mertens sum is itself the degenerate empty-wheel
truncated profile. This anchors the wheel recurrence at the exact prefix sum. -/
theorem primorialTruncatedSignedReciprocalCube_empty (X : ℕ) :
    primorialTruncatedSignedReciprocalCube ∅ X = 1 := by
  simp [primorialTruncatedSignedReciprocalCube, primeFaceProduct, booleanCubeSign]

end RHLean.Arithmetic

import Mathlib

/-!
# Exact frozen-root prime-two high/high floor reduction

The only arithmetic input is the ACTUAL Möbius function at odd indices
strictly below R. This is an unconditional all-roots identity, not an
asymptotic estimate. The complete high/high floor kernel has a square
principal term and exactly two residual hyperbola masks (quotients 2,3).

No post-root Möbius value, prime count, zeta-zero hypothesis, or desired
signed-energy estimate appears in any premise.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- The root-adjacent odd historical parents R/2 <= m < R. -/
def frozenOddHighSet (R : ℕ) : Finset ℕ :=
  (Finset.Ico 1 R).filter (fun m => Odd m ∧ R ≤ 2 * m)

/-- Literal actual Möbius mass on the odd root-adjacent parents. -/
def frozenOddHighMass (R : ℕ) : ℤ :=
  ∑ m ∈ frozenOddHighSet R, (μ m : ℤ)

/-- Original square-root floor, without a model or rounding approximation. -/
def frozenRootFloor (R m n : ℕ) : ℕ :=
  (R ^ 2 - 1) / (m * n)

/-- The exact high/high channel of the historical bilinear form. -/
def frozenOddHighHigh (R : ℕ) : ℤ :=
  ∑ m ∈ frozenOddHighSet R, ∑ n ∈ frozenOddHighSet R,
    (μ m : ℤ) * (μ n : ℤ) * (frozenRootFloor R m n : ℤ)

/-- The only two nontrivial high/high reciprocal quotient masks. -/
def frozenOddHighMask (R q : ℕ) : ℤ :=
  ∑ m ∈ frozenOddHighSet R, ∑ n ∈ frozenOddHighSet R,
    (μ m : ℤ) * (μ n : ℤ) *
      (if q ≤ frozenRootFloor R m n then (1 : ℤ) else 0)

private theorem frozenOddHigh_mem_iff {R m : ℕ} :
    m ∈ frozenOddHighSet R ↔
      1 ≤ m ∧ m < R ∧ Odd m ∧ R ≤ 2 * m := by
  simp [frozenOddHighSet, Finset.mem_filter, Finset.mem_Ico, and_assoc]

/-- The root-adjacent high/high quotient is always 1, 2, or 3. -/
theorem frozenOddHigh_floor_bounds
    (R : ℕ) (hR : 2 ≤ R)
    {m n : ℕ} (hm : m ∈ frozenOddHighSet R)
      (hn : n ∈ frozenOddHighSet R) :
    1 ≤ frozenRootFloor R m n ∧ frozenRootFloor R m n ≤ 3 := by
  obtain ⟨hmpos, hmR, _hmodd, hmhalf⟩ := frozenOddHigh_mem_iff.mp hm
  obtain ⟨hnpos, hnR, _hnodd, hnhalf⟩ := frozenOddHigh_mem_iff.mp hn
  have hden : 0 < m * n := Nat.mul_pos (by omega) (by omega)
  have hlt1 : m * n < R * n :=
    Nat.mul_lt_mul_of_pos_right hmR (by omega)
  have hle2 : R * n ≤ R * R :=
    Nat.mul_le_mul_left R hnR.le
  have hfit : m * n ≤ R ^ 2 - 1 := by
    have hlt : m * n < R ^ 2 := by
      calc
        m * n < R * n := hlt1
        _ ≤ R * R := hle2
        _ = R ^ 2 := by ring
    omega
  have hlarge : R * R ≤ (2 * m) * (2 * n) :=
    Nat.mul_le_mul hmhalf hnhalf
  have hlarge' : R ^ 2 ≤ 4 * (m * n) := by
    nlinarith only [hlarge]
  have hfar : R ^ 2 - 1 < 4 * (m * n) := by
    have hRpos : 0 < R ^ 2 := by positivity
    omega
  have hlow : 1 ≤ frozenRootFloor R m n := by
    unfold frozenRootFloor
    exact Nat.div_pos hfit hden
  have hhigh : frozenRootFloor R m n < 4 := by
    unfold frozenRootFloor
    exact (Nat.div_lt_iff_lt_mul hden).mpr (by nlinarith [hfar])
  omega

/-- Exact three-level floor staircase, for every admissible odd high pair. -/
theorem frozenOddHigh_floor_three (R : ℕ) (hR : 2 ≤ R)
    {m n : ℕ} (hm : m ∈ frozenOddHighSet R)
      (hn : n ∈ frozenOddHighSet R) :
    (frozenRootFloor R m n : ℤ) =
      1 + (if 2 ≤ frozenRootFloor R m n then 1 else 0) +
        (if 3 ≤ frozenRootFloor R m n then 1 else 0) := by
  obtain ⟨hlo, hhi⟩ := frozenOddHigh_floor_bounds R hR hm hn
  split_ifs <;> omega

/-- Every all-roots high/high sum is one exact historical square plus the
two fully signed quotient masks. Neither mask has been bounded separately. -/
theorem frozenOddHighHigh_eq_square_add_two_masks
    (R : ℕ) (hR : 2 ≤ R) :
    frozenOddHighHigh R =
      frozenOddHighMass R ^ 2 +
        frozenOddHighMask R 2 + frozenOddHighMask R 3 := by
  have hsq :
      (∑ m ∈ frozenOddHighSet R,
        ∑ n ∈ frozenOddHighSet R,
          (μ m : ℤ) * (μ n : ℤ)) =
        frozenOddHighMass R ^ 2 := by
    unfold frozenOddHighMass
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _hm
    apply Finset.sum_congr rfl
    intro n _hn
    ring
  calc
    frozenOddHighHigh R =
      (∑ m ∈ frozenOddHighSet R,
        ∑ n ∈ frozenOddHighSet R,
          (μ m : ℤ) * (μ n : ℤ)) +
      frozenOddHighMask R 2 + frozenOddHighMask R 3 := by
      unfold frozenOddHighHigh frozenOddHighMask
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      rw [frozenOddHigh_floor_three R hR hm hn]
      ring
    _ = _ := by rw [hsq]

#print axioms frozenOddHigh_floor_bounds
#print axioms frozenOddHigh_floor_three
#print axioms frozenOddHighHigh_eq_square_add_two_masks

end RHLean.Proof

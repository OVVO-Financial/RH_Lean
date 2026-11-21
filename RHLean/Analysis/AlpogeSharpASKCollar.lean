import Mathlib

open scoped ArithmeticFunction.vonMangoldt BigOperators

/-!
# Sharp midpoint collar for Alpoge's genuine ASK positive-part kernel

This is a quantitative, *unconditional* improvement over charging the
entire prime-power mass by a global width-Lipschitz estimate.

For two widths b<=B, their midpoint m=(b+B)/2, and the exact sharp
kernel K(z,w)=(z-w)_+, the Jensen gap

  J(z;b,B) = (K(z,b)+K(z,B))/2 - K(z,m)

is nonnegative, vanishes for z outside [b,B], and is <=(B-b)/4.
The 1/4 constant is sharp (z=m). Thus only prime powers in the
physical collar a/B < n < a/b can incur movement cost.

These theorems apply directly to the principal character, whose
coefficient on every prime power is 1, including ramified primes.
For the full ASK, nonprincipal character/width covariance must be
paid separately: this file asserts NO such cancellation and no RH.
-/

noncomputable section
namespace RHLean.Analysis

/-- The literal positive-part kernel in Alpoge's sharp ASK. -/
def alpogeASKPos (z w : ℝ) : ℝ := max (z - w) 0

/-- Two equally weighted site widths and the midpoint reference width. -/
def alpogeASKMidpointGap (z b B : ℝ) : ℝ :=
  (alpogeASKPos z b + alpogeASKPos z B) / 2 -
    alpogeASKPos z ((b + B) / 2)

/-- The sharp positive-part Jensen gap is exactly ZERO below the lower
width. No prime-power term outside the crossing collar is charged. -/
theorem alpogeASKMidpointGap_eq_zero_of_le
    (z b B : ℝ) (hbB : b ≤ B) (hz : z ≤ b) :
    alpogeASKMidpointGap z b B = 0 := by
  have h1 : z - b ≤ (0 : ℝ) := by linarith
  have h2 : z - B ≤ (0 : ℝ) := by linarith
  have h3 : z - (b + B) / 2 ≤ (0 : ℝ) := by linarith
  unfold alpogeASKMidpointGap alpogeASKPos
  rw [max_eq_right h1, max_eq_right h2, max_eq_right h3]
  ring

/-- The Jensen gap is exactly ZERO above the upper width too. In
this region the sharp kernel is affine, so centering removes the
entire first-order width cost. -/
theorem alpogeASKMidpointGap_eq_zero_of_ge
    (z b B : ℝ) (hbB : b ≤ B) (hz : B ≤ z) :
    alpogeASKMidpointGap z b B = 0 := by
  have h1 : 0 ≤ z - b := by linarith
  have h2 : (0 : ℝ) ≤ z - B := by linarith
  have h3 : (0 : ℝ) ≤ z - (b + B) / 2 := by linarith
  unfold alpogeASKMidpointGap alpogeASKPos
  rw [max_eq_left h1, max_eq_left h2, max_eq_left h3]
  ring

/-- Quantitative SHARP source estimate: midpoint Jensen discrepancy
has no sign loss and costs at most ONE QUARTER of the actual width,
not a full width at every prime power. -/
theorem alpogeASKMidpointGap_nonneg_le_quarter
    (z b B : ℝ) (hbB : b ≤ B) :
    0 ≤ alpogeASKMidpointGap z b B ∧
    alpogeASKMidpointGap z b B ≤ (B - b) / 4 := by
  by_cases hlow : z ≤ b
  · rw [alpogeASKMidpointGap_eq_zero_of_le z b B hbB hlow]
    constructor <;> linarith
  by_cases hhigh : B ≤ z
  · rw [alpogeASKMidpointGap_eq_zero_of_ge z b B hbB hhigh]
    constructor <;> linarith
  have hbz : b < z := lt_of_not_ge hlow
  have hzB : z < B := lt_of_not_ge hhigh
  have h1 : (0 : ℝ) ≤ z - b := by linarith
  have h2 : z - B ≤ (0 : ℝ) := by linarith
  by_cases hmid : z ≤ (b + B) / 2
  · have h3 : z - (b + B) / 2 ≤ (0 : ℝ) := by linarith
    unfold alpogeASKMidpointGap alpogeASKPos
    rw [max_eq_left h1, max_eq_right h2, max_eq_right h3]
    constructor <;> linarith
  · have h3 : (0 : ℝ) ≤ z - (b + B) / 2 := by linarith
    unfold alpogeASKMidpointGap alpogeASKPos
    rw [max_eq_left h1, max_eq_right h2, max_eq_left h3]
    constructor <;> linarith

/-- The full genuine principal von Mangoldt source incurs a Jensen
cost at two widths only inside the sharp prime-power crossing collar.
The ordinary principal character coefficient is 1 even at ramified
prime powers. No nonprincipal estimate is asserted. -/
def alpogeASKPrimePowerMidpointGap
    (N : ℕ) (a b B : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N,
    Λ n * alpogeASKMidpointGap (a / (n : ℝ)) b B

/-- The literal collider consists of precisely those prime powers
whose a/n ratio lies strictly between the two site widths. -/
def alpogeASKPrimePowerCollarMass
    (N : ℕ) (a b B : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc 2 N).filter
    (fun n => b < a / (n : ℝ) ∧ a / (n : ℝ) < B),
    Λ n

/-- A new unconditional arithmetic saving in the principal sharp ASK
source. All n outside the *actual* prime-power crossing collar have
exactly zero Jensen cost. Within the collar each mass pays at most
(B-b)/4, not a global width-Lipschitz charge. -/
theorem alpogeASKPrimePowerMidpointGap_le_collar
    (N : ℕ) (a b B : ℝ) (hbB : b ≤ B) :
    0 ≤ alpogeASKPrimePowerMidpointGap N a b B ∧
    alpogeASKPrimePowerMidpointGap N a b B ≤
      ((B - b) / 4) * alpogeASKPrimePowerCollarMass N a b B := by
  constructor
  · unfold alpogeASKPrimePowerMidpointGap
    apply Finset.sum_nonneg
    intro n hn
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (alpogeASKMidpointGap_nonneg_le_quarter
        (a / (n : ℝ)) b B hbB).1
  · unfold alpogeASKPrimePowerMidpointGap
      alpogeASKPrimePowerCollarMass
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro n hn
    let z : ℝ := a / (n : ℝ)
    by_cases hlo : z ≤ b
    · have hz := alpogeASKMidpointGap_eq_zero_of_le z b B hbB hlo
      have hnot : ¬(b < z ∧ z < B) := by
        intro hh
        linarith
      simp [z, hz, hnot]
    by_cases hhi : B ≤ z
    · have hz := alpogeASKMidpointGap_eq_zero_of_ge z b B hbB hhi
      have hnot : ¬(b < z ∧ z < B) := by
        intro hh
        linarith
      simp [z, hz, hnot]
    have hmem : b < z ∧ z < B := by
      constructor <;> linarith
    simp only [z] at hmem
    simp only [if_pos hmem]
    exact mul_le_mul_of_nonneg_left
      (alpogeASKMidpointGap_nonneg_le_quarter
        (a / (n : ℝ)) b B hbB).2
      ArithmeticFunction.vonMangoldt_nonneg

end RHLean.Analysis

import Mathlib
import «research.SQUARE_SHELL_DIVISOR_SYNTHESIS_20261030»

/-! Uniform energy of the COMPLETE original Euler source on physical squareful
masks. The primitive h=1 and remaining squarefree source are not bounded here. -/
noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators
namespace RHLean.Proof
attribute [local instance] Classical.propDecidable

private lemma masked_impulse_sum (I : Finset ℕ) (h q : ℕ) (v : ℤ)
    (hq : q ∈ I) :
    (∑ n ∈ I, if h ∣ n then (if n=q then v else 0) else 0) =
      if h ∣ q then v else 0 := by
  rw [Finset.sum_eq_single q]
  · simp
  · intro n _hn hnq
    simp [hnq]
  · intro hn
    exact False.elim (hn hq)

/-- Exactly the three original physical corner sites; no boundary assumption. -/
theorem synthesisDivisorCornerWindow_explicit
    (R h : ℕ) (hR : 3 ≤ R) :
    synthesisDivisorCornerWindow R h =
      (if h ∣ R*R then (μ R : ℤ)^2 else 0) +
      (if h ∣ R*(R+1) then 2*(μ R : ℤ)*μ (R+1) else 0) +
      (if h ∣ R*(R+2) then 2*(μ R : ℤ)*μ (R+2) else 0) := by
  let I := Finset.Ico (R*R) ((R+1)*(R+1))
  have h0 : R*R ∈ I := Finset.mem_Ico.mpr ⟨by omega, by nlinarith⟩
  have h1 : R*(R+1) ∈ I := Finset.mem_Ico.mpr ⟨by nlinarith, by nlinarith⟩
  have h2 : R*(R+2) ∈ I := Finset.mem_Ico.mpr ⟨by nlinarith, by nlinarith⟩
  have hsplit (n : ℕ) :
      (if h ∣ n then synthesisCornerCoefficient R n else 0) =
      (if h ∣ n then (if n=R*R then (μ R : ℤ)^2 else 0) else 0) +
      (if h ∣ n then (if n=R*(R+1) then 2*(μ R : ℤ)*μ (R+1) else 0) else 0) +
      (if h ∣ n then (if n=R*(R+2) then 2*(μ R : ℤ)*μ (R+2) else 0) else 0) := by
    unfold synthesisCornerCoefficient
    split_ifs <;> ring
  change (∑ n ∈ I, if h ∣ n then synthesisCornerCoefficient R n else 0) = _
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [masked_impulse_sum I h (R*R) _ h0,
    masked_impulse_sum I h (R*(R+1)) _ h1,
    masked_impulse_sum I h (R*(R+2)) _ h2]

private lemma synthesis_square_abs (z : ℤ) (hz : |z| ≤ 1) : |z^2| ≤ 1 := by
  rw [abs_of_nonneg (sq_nonneg z)]
  have hl := (abs_le.mp hz).1
  have hu := (abs_le.mp hz).2
  nlinarith only [hl, hu]

private lemma synthesis_mu_pair_abs (a b : ℕ) :
    |2*(μ a : ℤ)*μ b| ≤ 2 := by
  have ha : |(μ a : ℤ)| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
  have hb : |(μ b : ℤ)| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
  have hp : |(μ a : ℤ)| * |(μ b : ℤ)| ≤ 1 := by
    simpa using mul_le_mul ha hb (abs_nonneg _) (by norm_num : (0 : ℤ) ≤ 1)
  calc
    |2*(μ a : ℤ)*μ b| = 2*(|(μ a : ℤ)| * |(μ b : ℤ)|) := by
      rw [abs_mul, abs_mul]
      norm_num
      ring
    _ ≤ 2 := by linarith only [hp]

private lemma synthesis_mask_abs_generic
    (P : Prop) [Decidable P] (x B : ℤ) (hB : 0 ≤ B) (hx : |x| ≤ B) :
    |if P then x else 0| ≤ B := by
  by_cases h : P
  · simpa only [ite_eq_left h] using hx
  · simpa only [ite_eq_right h, abs_zero] using hB

private lemma synthesis_three_masks_abs
    (P Q T : Prop) [Decidable P] [Decidable Q] [Decidable T]
    (x y z : ℤ) (hx : |x| ≤ 1) (hy : |y| ≤ 2) (hz : |z| ≤ 2) :
    |(if P then x else 0)+(if Q then y else 0)+(if T then z else 0)| ≤ 5 := by
  have hp := synthesis_mask_abs_generic P x 1 (by norm_num) hx
  have hq := synthesis_mask_abs_generic Q y 2 (by norm_num) hy
  have ht := synthesis_mask_abs_generic T z 2 (by norm_num) hz
  calc
    _ ≤ |(if P then x else 0)+(if Q then y else 0)| +
        |if T then z else 0| := abs_add_le _ _
    _ ≤ |if P then x else 0| + |if Q then y else 0| +
        |if T then z else 0| := add_le_add_right (abs_add_le _ _) _
    _ ≤ (1+2)+2 := add_le_add (add_le_add hp hq) ht
    _ = 5 := rfl

lemma synthesisDivisorCornerWindow_abs_le_five
    (R h : ℕ) (hR : 3 ≤ R) :
    |synthesisDivisorCornerWindow R h| ≤ 5 := by
  rw [synthesisDivisorCornerWindow_explicit R h hR]
  exact synthesis_three_masks_abs
    (h ∣ R*R) (h ∣ R*(R+1)) (h ∣ R*(R+2))
    ((μ R : ℤ)^2) (2*(μ R : ℤ)*μ (R+1)) (2*(μ R : ℤ)*μ (R+2))
    (synthesis_square_abs (μ R) ArithmeticFunction.abs_moebius_le_one)
    (synthesis_mu_pair_abs R (R+1)) (synthesis_mu_pair_abs R (R+2))

/-- Covers all original completed and partially admitted factor pairs. -/
theorem synthesisSquarefulEuler_abs_le_five
    (R h : ℕ) (hR : 3 ≤ R) (hh : ¬ Squarefree h) :
    |synthesisDivisorEulerWindow R h| ≤ 5 := by
  rw [synthesisSquarefulEuler_eq_corner R h hR hh]
  exact synthesisDivisorCornerWindow_abs_le_five R h hR

/-- The physical squareful mask may change arbitrarily with R. -/
theorem synthesisSquarefulEuler_energy_le
    (I : Finset ℕ) (mask : ℕ → ℕ)
    (hR : ∀ R ∈ I, 3 ≤ R)
    (hmask : ∀ R ∈ I, ¬ Squarefree (mask R)) :
    (∑ R ∈ I, synthesisDivisorEulerWindow R (mask R) ^ 2) ≤
      25 * (I.card : ℤ) := by
  calc
    _ ≤ ∑ _R ∈ I, (25 : ℤ) := by
      apply Finset.sum_le_sum
      intro R hmem
      have h := synthesisSquarefulEuler_abs_le_five R (mask R)
        (hR R hmem) (hmask R hmem)
      have hl := (abs_le.mp h).1
      have hu := (abs_le.mp h).2
      nlinarith only [hl, hu, mul_nonneg (sub_nonneg.mpr hu) (by linarith only [hl] :
        0 ≤ synthesisDivisorEulerWindow R (mask R) + 5)]
    _ = 25 * (I.card : ℤ) := by simp; ring

/-- No signed cross-divisor term is erased by the physical-source identity. -/
theorem synthesisCorrectedEuler_gram
    (I S : Finset ℕ) (weight : ℕ → ℤ)
    (hR : ∀ R ∈ I, 3 ≤ R) :
    (∑ R ∈ I,
      (∑ h ∈ S, weight h *
        (synthesisDivisorEulerWindow R h - synthesisDivisorCornerWindow R h)) ^ 2) =
    (∑ R ∈ I,
      (∑ h ∈ S, weight h * synthesisDivisorMobiusWindow R h) ^ 2) := by
  apply Finset.sum_congr rfl
  intro R hr
  have hsum :
      (∑ h ∈ S, weight h *
        (synthesisDivisorEulerWindow R h - synthesisDivisorCornerWindow R h)) =
      -(∑ h ∈ S, weight h * synthesisDivisorMobiusWindow R h) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro h _hh
    rw [synthesisDivisorEuler_eq_neg_mobius_add_corner R h (hR R hr)]
    ring
  rw [hsum]
  ring

#print axioms synthesisDivisorCornerWindow_explicit
#print axioms synthesisSquarefulEuler_energy_le
#print axioms synthesisCorrectedEuler_gram
end RHLean.Proof

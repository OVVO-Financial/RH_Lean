import Mathlib
import «research.SQUARE_SHELL_DIVISOR_SYNTHESIS_20261030»

/-!
# A complete physical sector, not a generic centered proxy

Squareful physical divisor masks annihilate the true Mobius incidence.
The ENTIRE original historical Euler coefficient family (all completed and
partially admitted factor pairs) then collapses to the three original corners.
This proves a uniform O(number of roots) energy bound on this proper sector.
It does not bound the primitive h=1 or squarefree residual.
-/
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

/-- No disguised boundary assumption: the divisor-resolved correction is
exactly the original three physical sites. -/
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

lemma synthesisDivisorCornerWindow_abs_le_five
    (R h : ℕ) (hR : 3 ≤ R) :
    |synthesisDivisorCornerWindow R h| ≤ 5 := by
  rw [synthesisDivisorCornerWindow_explicit R h hR]
  have h0 : |if h ∣ R*R then (μ R : ℤ)^2 else 0| ≤ 1 := by
    split_ifs <;> rcases ArithmeticFunction.moebius_eq_or R with hr | hr | hr <;>
      norm_num [hr]
  have h1 : |if h ∣ R*(R+1) then 2*(μ R : ℤ)*μ (R+1) else 0| ≤ 2 := by
    split_ifs <;>
      rcases ArithmeticFunction.moebius_eq_or R with hr | hr | hr <;>
      rcases ArithmeticFunction.moebius_eq_or (R+1) with hs | hs | hs <;>
      norm_num [hr,hs]
  have h2 : |if h ∣ R*(R+2) then 2*(μ R : ℤ)*μ (R+2) else 0| ≤ 2 := by
    split_ifs <;>
      rcases ArithmeticFunction.moebius_eq_or R with hr | hr | hr <;>
      rcases ArithmeticFunction.moebius_eq_or (R+2) with hs | hs | hs <;>
      norm_num [hr,hs]
  calc
    _ ≤ |(if h ∣ R*R then (μ R : ℤ)^2 else 0) +
          (if h ∣ R*(R+1) then 2*(μ R : ℤ)*μ (R+1) else 0)| +
        |if h ∣ R*(R+2) then 2*(μ R : ℤ)*μ (R+2) else 0| := abs_add_le _ _
    _ ≤ |if h ∣ R*R then (μ R : ℤ)^2 else 0| +
        |if h ∣ R*(R+1) then 2*(μ R : ℤ)*μ (R+1) else 0| +
        |if h ∣ R*(R+2) then 2*(μ R : ℤ)*μ (R+2) else 0| :=
      add_le_add_right (abs_add_le _ _) _
    _ ≤ 5 := by omega

/-- Entire original Euler source on any squareful divisor mask is O(1),
not just a termwise inequality on individual completed packets. -/
theorem synthesisSquarefulEuler_abs_le_five
    (R h : ℕ) (hR : 3 ≤ R) (hh : ¬ Squarefree h) :
    |synthesisDivisorEulerWindow R h| ≤ 5 := by
  rw [synthesisSquarefulEuler_eq_corner R h hR hh]
  exact synthesisDivisorCornerWindow_abs_le_five R h hR

/-- Uniform genuine source energy. The physical squareful mask may change
arbitrarily with R; neither stationarity nor independent signs are assumed. -/
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
      nlinarith [mul_nonneg (sub_nonneg.mpr hu) (by linarith :
        0 ≤ synthesisDivisorEulerWindow R (mask R) + 5)]
    _ = 25 * (I.card : ℤ) := by simp; ring

/-- No cross-divisor correlation is erased. This is the full signed Gram of
the physical corrected Euler windows, exactly the Mobius divisor Gram. -/
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

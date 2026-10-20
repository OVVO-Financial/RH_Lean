import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# Finite exterior-spill Abel identity and NNS signed Green--Kubo energy

This file uses no continuous integrals, measures, or analytic moment
assumptions. Its endpoint profile is an arbitrary function H : Nat -> Real,
and its exact discrete Abel weight is nu n = H n - H (n+1).

At X = K^2 and B = ceil((32/25)*X), specialize f to the original
integer Moebius coefficients and H n to the exterior profile H(n/X).

The interval is Finset.Ioo X B (X < n < B). The discrete weight mass
over this interval is H(X+1), NOT H(X)=1. The upper bound H(X+1) <= 1
is sufficient for the exact Cauchy--Schwarz inequality.

The terminal signed covariance estimate is NOT assumed or proved here.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

private theorem vf919_Ioo_eq_Ico_succ (X B : ℕ) :
    Finset.Ioo X B = Finset.Ico (X + 1) B := by
  ext n
  simp only [Finset.mem_Ioo, Finset.mem_Ico]
  omega

/-- Signed cumulative physical mass through site n, strictly after X. -/
def vf919ExteriorSignedPrefix (X n : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.Ico (X + 1) (n + 1), f m

/-- Zero-target positive partial first moment. -/
def vf919ExteriorUpperPartial (X n : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.Ico (X + 1) (n + 1), posPart (f m)

/-- Zero-target negative partial first moment, as a positive magnitude. -/
def vf919ExteriorLowerPartial (X n : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.Ico (X + 1) (n + 1), negPart (f m)

/-- Exact NNS UPM-LPM reconstruction, before averaging or squaring. -/
theorem vf919ExteriorSignedPrefix_eq_upper_sub_lower
    (X n : ℕ) (f : ℕ → ℝ) :
    vf919ExteriorSignedPrefix X n f =
      vf919ExteriorUpperPartial X n f -
        vf919ExteriorLowerPartial X n f := by
  unfold vf919ExteriorSignedPrefix vf919ExteriorUpperPartial
    vf919ExteriorLowerPartial
  rw [← Finset.sum_sub_distrib]
  simp only [posPart_sub_negPart]

/-- Exact finite Abel kernel. -/
def vf919ExteriorAbelWeight (H : ℕ → ℝ) (n : ℕ) : ℝ :=
  H n - H (n + 1)

private theorem vf919_sum_Ico_adjacent_differences
    (a b : ℕ) (hab : a ≤ b) (H : ℕ → ℝ) :
    (∑ n ∈ Finset.Ico a b, (H n - H (n + 1))) = H a - H b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
      rw [Finset.sum_Ico_succ_top hb, ih]
      ring

/-- Abel summation with upper endpoint retained, on finite Nat intervals. -/
private theorem vf919_discrete_abel_with_endpoint
    (a b : ℕ) (hab : a ≤ b) (f H : ℕ → ℝ) :
    (∑ n ∈ Finset.Ico a b, f n * H n) =
      (∑ n ∈ Finset.Ico a b,
        (∑ m ∈ Finset.Ico a (n + 1), f m) * (H n - H (n + 1))) +
      (∑ n ∈ Finset.Ico a b, f n) * H b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
      calc
        (∑ n ∈ Finset.Ico a (b + 1), f n * H n) =
            (∑ n ∈ Finset.Ico a b, f n * H n) + f b * H b := by
              rw [Finset.sum_Ico_succ_top hb]
        _ = (∑ n ∈ Finset.Ico a b,
              (∑ m ∈ Finset.Ico a (n + 1), f m) * (H n - H (n + 1))) +
              (∑ n ∈ Finset.Ico a b, f n) * H b + f b * H b := by
              rw [ih]
        _ = (∑ n ∈ Finset.Ico a (b + 1),
              (∑ m ∈ Finset.Ico a (n + 1), f m) * (H n - H (n + 1))) +
              (∑ n ∈ Finset.Ico a (b + 1), f n) * H (b + 1) := by
              simp only [Finset.sum_Ico_succ_top hb]
              ring

/-- Theorem 1a: exterior spill is an EXACT weighted sum of the original
    signed cumulative integer prefixes. No integrals or analytic estimates. -/
theorem vf919ExteriorSpill_eq_discreteAbel
    (X B : ℕ) (hXB : X + 1 ≤ B)
    (f H : ℕ → ℝ) (hB : H B = 0) :
    (∑ n ∈ Finset.Ioo X B, f n * H n) =
      ∑ n ∈ Finset.Ioo X B,
        vf919ExteriorSignedPrefix X n f * vf919ExteriorAbelWeight H n := by
  rw [vf919_Ioo_eq_Ico_succ]
  have h := vf919_discrete_abel_with_endpoint (X + 1) B hXB f H
  simpa only [vf919ExteriorSignedPrefix, vf919ExteriorAbelWeight,
    hB, mul_zero, add_zero] using h

/-- The finite total mass equals H(X+1), not H(X). -/
theorem vf919ExteriorAbelWeight_mass
    (X B : ℕ) (hXB : X + 1 ≤ B)
    (H : ℕ → ℝ) (hB : H B = 0) :
    (∑ n ∈ Finset.Ioo X B, vf919ExteriorAbelWeight H n) = H (X + 1) := by
  rw [vf919_Ioo_eq_Ico_succ]
  have h := vf919_sum_Ico_adjacent_differences (X + 1) B hXB H
  simpa only [vf919ExteriorAbelWeight, hB, sub_zero] using h

/-- Every terminal tail sum telescopes to H(m). -/
theorem vf919ExteriorAbelWeight_tail
    (m B : ℕ) (hmB : m ≤ B) (H : ℕ → ℝ) (hB : H B = 0) :
    (∑ n ∈ Finset.Ico m B, vf919ExteriorAbelWeight H n) = H m := by
  simpa only [vf919ExteriorAbelWeight, hB, sub_zero] using
    vf919_sum_Ico_adjacent_differences m B hmB H

/-- Theorem 1b: sharply truncated original integer prefix equals a
    finite smooth sum minus the one exterior signed Abel spill.
    The finite smooth profile is only required to match the actual
    log-partition on the interior and exterior physical integers. -/
theorem vf919SharpPrefix_eq_smooth_sub_discreteSpill
    (X B : ℕ) (hXB : X + 1 ≤ B)
    (f profile H : ℕ → ℝ) (hB : H B = 0)
    (hInside : ∀ n ∈ Finset.Icc 1 X, profile n = 1)
    (hOutside : ∀ n ∈ Finset.Ioo X B, profile n = H n) :
    (∑ n ∈ Finset.Icc 1 X, f n) =
      (∑ n ∈ Finset.Ico 1 B, f n * profile n) -
      (∑ n ∈ Finset.Ioo X B,
        vf919ExteriorSignedPrefix X n f * vf919ExteriorAbelWeight H n) := by
  have hSplit : Finset.Ico 1 B =
      Finset.Icc 1 X ∪ Finset.Ioo X B := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_Icc,
      Finset.mem_Ioo]
    omega
  have hDisjoint : Disjoint (Finset.Icc 1 X) (Finset.Ioo X B) := by
    apply Finset.disjoint_left.mpr
    intro n hnI hnO
    have hhI := Finset.mem_Icc.mp hnI
    have hhO := Finset.mem_Ioo.mp hnO
    omega
  have hProfile :
      (∑ n ∈ Finset.Ico 1 B, f n * profile n) =
        (∑ n ∈ Finset.Icc 1 X, f n) +
        (∑ n ∈ Finset.Ioo X B, f n * H n) := by
    rw [hSplit, Finset.sum_union hDisjoint]
    congr 1
    · apply Finset.sum_congr rfl
      intro n hn
      rw [hInside n hn, mul_one]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [hOutside n hn]
  rw [vf919ExteriorSpill_eq_discreteAbel X B hXB f H hB] at hProfile
  linarith

/-- Weighted true-integer squarefree diagonal. -/
def vf919ExteriorDiagonal (X B : ℕ) (f H : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioo X B, (f n) ^ 2 * H n

/-- Ordered positive-lag covariance with terminal weight H(n).
    It retains every original pair sign, with no independence hypothesis. -/
def vf919ExteriorPositiveLag (X B : ℕ) (f H : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioo X B,
    f n * (∑ m ∈ Finset.Ico (X + 1) n, f m) * H n

/-- A full finite-prefix square, resolved into diagonal and signed lag
    increments without any analytic assumptions. -/
private theorem vf919_square_prefix_as_increments
    (a b : ℕ) (hab : a ≤ b) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.Ico a b, f n) ^ 2 =
      ∑ n ∈ Finset.Ico a b,
        ((f n) ^ 2 + 2 * f n * (∑ m ∈ Finset.Ico a n, f m)) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
      simp only [Finset.sum_Ico_succ_top hb]
      calc
        ((∑ n ∈ Finset.Ico a b, f n) + f b) ^ 2 =
            (∑ n ∈ Finset.Ico a b, f n) ^ 2 +
              (f b) ^ 2 + 2 * f b * (∑ n ∈ Finset.Ico a b, f n) := by
                ring
        _ = _ := by rw [ih]; ring

/-- Theorem 2a: exact signed weighted Green--Kubo equality for the
    original physical finite prefix and every pair in the exterior. -/
theorem vf919ExteriorAbelEnergy_eq_diagonal_add_covariance
    (X B : ℕ) (hXB : X + 1 ≤ B)
    (f H : ℕ → ℝ) (hB : H B = 0) :
    (∑ n ∈ Finset.Ioo X B,
      vf919ExteriorAbelWeight H n * (vf919ExteriorSignedPrefix X n f) ^ 2) =
      vf919ExteriorDiagonal X B f H +
        2 * vf919ExteriorPositiveLag X B f H := by
  let g : ℕ → ℝ := fun m =>
    (f m) ^ 2 + 2 * f m * (∑ k ∈ Finset.Ico (X + 1) m, f k)
  have hInc : ∀ n ∈ Finset.Ico (X + 1) B,
      (vf919ExteriorSignedPrefix X n f) ^ 2 =
        (∑ m ∈ Finset.Ico (X + 1) (n + 1), g m) := by
    intro n hn
    have hn0 : X + 1 ≤ n + 1 := by
      have hh := Finset.mem_Ico.mp hn
      omega
    simpa only [vf919ExteriorSignedPrefix, g] using
      vf919_square_prefix_as_increments (X + 1) (n + 1) hn0 f
  have hAbel := vf919_discrete_abel_with_endpoint (X + 1) B hXB g H
  have hAbel' :
      (∑ n ∈ Finset.Ico (X + 1) B, g n * H n) =
        ∑ n ∈ Finset.Ico (X + 1) B,
          (∑ m ∈ Finset.Ico (X + 1) (n + 1), g m) *
            vf919ExteriorAbelWeight H n := by
    simpa only [vf919ExteriorAbelWeight, hB, mul_zero, add_zero] using hAbel
  rw [vf919_Ioo_eq_Ico_succ]
  calc
    (∑ n ∈ Finset.Ico (X + 1) B,
      vf919ExteriorAbelWeight H n * (vf919ExteriorSignedPrefix X n f) ^ 2) =
        ∑ n ∈ Finset.Ico (X + 1) B,
          (∑ m ∈ Finset.Ico (X + 1) (n + 1), g m) *
            vf919ExteriorAbelWeight H n := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [hInc n hn]
          ring
    _ = (∑ n ∈ Finset.Ico (X + 1) B, g n * H n) := hAbel'.symm
    _ = vf919ExteriorDiagonal X B f H +
          2 * vf919ExteriorPositiveLag X B f H := by
          unfold vf919ExteriorDiagonal vf919ExteriorPositiveLag
          rw [vf919_Ioo_eq_Ico_succ]
          calc
            (∑ n ∈ Finset.Ico (X + 1) B, g n * H n) =
              (∑ n ∈ Finset.Ico (X + 1) B, (f n) ^ 2 * H n) +
              (∑ n ∈ Finset.Ico (X + 1) B,
                (2 * f n * (∑ m ∈ Finset.Ico (X + 1) n, f m)) * H n) := by
                  simp only [g, add_mul, Finset.sum_add_distrib]
            _ = _ := by
                  rw [Finset.mul_sum]
                  congr 1
                  apply Finset.sum_congr rfl
                  intro n hn
                  ring

/-- Theorem 2b: finite weighted Cauchy--Schwarz. The only mass
    hypothesis is H(X+1)<=1, which is the exact discrete normalization. -/
theorem vf919ExteriorSpill_sq_le_AbelEnergy
    (X B : ℕ) (hXB : X + 1 ≤ B)
    (f H : ℕ → ℝ) (hB : H B = 0)
    (hNu : ∀ n ∈ Finset.Ioo X B, 0 ≤ vf919ExteriorAbelWeight H n)
    (hMass : H (X + 1) ≤ 1) :
    (∑ n ∈ Finset.Ioo X B, f n * H n) ^ 2 ≤
      ∑ n ∈ Finset.Ioo X B,
        vf919ExteriorAbelWeight H n * (vf919ExteriorSignedPrefix X n f) ^ 2 := by
  rw [vf919ExteriorSpill_eq_discreteAbel X B hXB f H hB]
  let s := Finset.Ioo X B
  let nu := vf919ExteriorAbelWeight H
  let D := fun n => vf919ExteriorSignedPrefix X n f
  have hnu : ∀ n ∈ s, 0 ≤ nu n := hNu
  have henergy : 0 ≤ (∑ n ∈ s, nu n * (D n) ^ 2) :=
    Finset.sum_nonneg (fun n hn => mul_nonneg (hnu n hn) (sq_nonneg _))
  have hCS :
      (∑ n ∈ s, nu n * D n) ^ 2 ≤
        (∑ n ∈ s, nu n) *
          (∑ n ∈ s, nu n * (D n) ^ 2) := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (fun n hn => hnu n hn)
      (fun n hn => mul_nonneg (hnu n hn) (sq_nonneg _))
      (fun n hn => by ring)
  have htotal : (∑ n ∈ s, nu n) = H (X + 1) :=
    vf919ExteriorAbelWeight_mass X B hXB H hB
  have hsum_swap :
      (∑ n ∈ s, D n * nu n) = (∑ n ∈ s, nu n * D n) := by
    apply Finset.sum_congr rfl
    intro n hn
    ring
  change (∑ n ∈ s, D n * nu n) ^ 2 ≤
    ∑ n ∈ s, nu n * (D n) ^ 2
  rw [hsum_swap]
  calc
    (∑ n ∈ s, nu n * D n) ^ 2 ≤
        (∑ n ∈ s, nu n) *
          (∑ n ∈ s, nu n * (D n) ^ 2) := hCS
    _ ≤ (1 : ℝ) * (∑ n ∈ s, nu n * (D n) ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ henergy
          rw [htotal]
          exact hMass
    _ = _ := by ring

/-- Theorem 2c: NNS upper and lower zero-target partial moments combine
    to exactly the SAME signed covariance, retaining the mixed term. -/
theorem vf919ExteriorUpperLowerEnergy_eq_signedCovariance
    (X B : ℕ) (hXB : X + 1 ≤ B)
    (f H : ℕ → ℝ) (hB : H B = 0) :
    (∑ n ∈ Finset.Ioo X B,
      vf919ExteriorAbelWeight H n *
        ((vf919ExteriorUpperPartial X n f) ^ 2 +
         (vf919ExteriorLowerPartial X n f) ^ 2 -
         2 * vf919ExteriorUpperPartial X n f *
             vf919ExteriorLowerPartial X n f)) =
      vf919ExteriorDiagonal X B f H +
        2 * vf919ExteriorPositiveLag X B f H := by
  rw [← vf919ExteriorAbelEnergy_eq_diagonal_add_covariance X B hXB f H hB]
  apply Finset.sum_congr rfl
  intro n hn
  rw [vf919ExteriorSignedPrefix_eq_upper_sub_lower]
  ring

#print axioms vf919ExteriorSignedPrefix_eq_upper_sub_lower
#print axioms vf919ExteriorSpill_eq_discreteAbel
#print axioms vf919ExteriorAbelWeight_mass
#print axioms vf919SharpPrefix_eq_smooth_sub_discreteSpill
#print axioms vf919ExteriorAbelEnergy_eq_diagonal_add_covariance
#print axioms vf919ExteriorSpill_sq_le_AbelEnergy
#print axioms vf919ExteriorUpperLowerEnergy_eq_signedCovariance

end RHLean.Analysis

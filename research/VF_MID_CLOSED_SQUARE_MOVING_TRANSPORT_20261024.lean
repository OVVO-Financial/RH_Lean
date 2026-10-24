import Mathlib
import «research.VF_MID_CLOSED_SQUARE_BIRTH_TIME_20261024»

/-!
# Moving square-window telescopes

Finite algebra with literal two-factor square prefixes and both ordered
birth legs. The generic telescopes must be specialized to the actual
Mobius-weighted floor before claiming a physical source payment.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Analysis

/-- Expand a finite square into the old square, two border legs,
and a single corner. No factor occurrences are dropped. -/
theorem closedSquareShell_doubleSum_square_succ
    (F : ℕ → ℕ → ℤ) (r : ℕ) :
    (∑ a ∈ Finset.Icc 1 (r + 1),
      ∑ b ∈ Finset.Icc 1 (r + 1), F a b) =
      (∑ a ∈ Finset.Icc 1 r,
        ∑ b ∈ Finset.Icc 1 r, F a b) +
      (∑ a ∈ Finset.Icc 1 r, F a (r + 1)) +
      (∑ b ∈ Finset.Icc 1 r, F (r + 1) b) +
      F (r + 1) (r + 1) := by
  have hp : (1 : ℕ) ≤ r + 1 := by omega
  calc
    (∑ a ∈ Finset.Icc 1 (r + 1),
      ∑ b ∈ Finset.Icc 1 (r + 1), F a b) =
      ∑ a ∈ Finset.Icc 1 (r + 1),
        ((∑ b ∈ Finset.Icc 1 r, F a b) + F a (r + 1)) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_Icc_succ_top hp]
    _ = (∑ a ∈ Finset.Icc 1 (r + 1),
            ∑ b ∈ Finset.Icc 1 r, F a b) +
          (∑ a ∈ Finset.Icc 1 (r + 1), F a (r + 1)) := by
            rw [Finset.sum_add_distrib]
    _ = ((∑ a ∈ Finset.Icc 1 r,
            ∑ b ∈ Finset.Icc 1 r, F a b) +
          (∑ b ∈ Finset.Icc 1 r, F (r + 1) b)) +
          ((∑ a ∈ Finset.Icc 1 r, F a (r + 1)) +
            F (r + 1) (r + 1)) := by
              rw [Finset.sum_Icc_succ_top hp, Finset.sum_Icc_succ_top hp]
    _ = _ := by abel

/-- The full moving-source window telescopes once the exact root
birth relation is supplied. This is a finite formal implication. -/
theorem closedSquareShell_generic_movingBoundary_telescope
    (H : ℕ → ℕ → ℤ) (bill : ℕ → ℤ)
    (A B : ℕ) (hAB : A ≤ B)
    (hbirth : ∀ r ∈ Finset.Ico A B,
      H (r + 1) ((r + 1) ^ 2) =
        H r ((r + 1) ^ 2) + bill (r + 1)) :
    (∑ r ∈ Finset.Ico A B,
      (H r ((r + 1) ^ 2) - H r (r ^ 2))) =
      H B (B ^ 2) - H A (A ^ 2) -
        (∑ r ∈ Finset.Ico A B, bill (r + 1)) := by
  calc
    (∑ r ∈ Finset.Ico A B,
      (H r ((r + 1) ^ 2) - H r (r ^ 2))) =
      ∑ r ∈ Finset.Ico A B,
        ((H (r + 1) ((r + 1) ^ 2) - H r (r ^ 2)) -
          bill (r + 1)) := by
          apply Finset.sum_congr rfl
          intro r hr
          have hb := hbirth r hr
          omega
    _ = (∑ r ∈ Finset.Ico A B,
            (H (r + 1) ((r + 1) ^ 2) - H r (r ^ 2))) -
          (∑ r ∈ Finset.Ico A B, bill (r + 1)) := by
            rw [Finset.sum_sub_distrib]
    _ = H B (B ^ 2) - H A (A ^ 2) -
          (∑ r ∈ Finset.Ico A B, bill (r + 1)) := by
            rw [Finset.sum_Ico_sub (fun r => H r (r ^ 2)) hAB]

/-- The fixed lower square cancels by telescoping *separately*.
Only the final moving boundary and the actual birth bills remain. -/
theorem closedSquareShell_generic_movingComplement_telescope
    (H : ℕ → ℕ → ℤ) (bill : ℕ → ℤ)
    (A B : ℕ) (hAB : A ≤ B)
    (hbirth : ∀ r ∈ Finset.Ico A B,
      H (r + 1) ((r + 1) ^ 2) =
        H r ((r + 1) ^ 2) + bill (r + 1)) :
    (∑ r ∈ Finset.Ico A B,
       ((H r ((r + 1) ^ 2) - H A ((r + 1) ^ 2)) -
        (H r (r ^ 2) - H A (r ^ 2)))) =
       (H B (B ^ 2) - H A (B ^ 2)) -
         (∑ r ∈ Finset.Ico A B, bill (r + 1)) := by
  have hfull := closedSquareShell_generic_movingBoundary_telescope
    H bill A B hAB hbirth
  have hfix := Finset.sum_Ico_sub (fun r => H A (r ^ 2)) hAB
  calc
    (∑ r ∈ Finset.Ico A B,
       ((H r ((r + 1) ^ 2) - H A ((r + 1) ^ 2)) -
        (H r (r ^ 2) - H A (r ^ 2)))) =
      (∑ r ∈ Finset.Ico A B,
        (H r ((r + 1) ^ 2) - H r (r ^ 2))) -
      (∑ r ∈ Finset.Ico A B,
        (H A ((r + 1) ^ 2) - H A (r ^ 2))) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro r _
          ring
    _ = (H B (B ^ 2) - H A (B ^ 2)) -
         (∑ r ∈ Finset.Ico A B, bill (r + 1)) := by
           rw [hfull, hfix]
           ring


/-- The actual signed double-floor square with every ordered factor pair. -/
def closedSquareShellPhysicalFloor (R X : ℕ) : ℤ :=
  ∑ a ∈ Finset.Icc 1 R,
    ∑ b ∈ Finset.Icc 1 R,
      closedSquareShellMu a * closedSquareShellMu b *
        (((X / (a * b) : ℕ) : ℤ))

/-- Literal newly admitted row, column and corner at root k. -/
def closedSquareShellPhysicalBorder (k : ℕ) : ℤ :=
  (∑ a ∈ Finset.Icc 1 (k - 1),
    closedSquareShellMu a * closedSquareShellMu k *
      (((k ^ 2 / (a * k) : ℕ) : ℤ))) +
  (∑ b ∈ Finset.Icc 1 (k - 1),
    closedSquareShellMu k * closedSquareShellMu b *
      (((k ^ 2 / (k * b) : ℕ) : ℤ))) +
  closedSquareShellMu k * closedSquareShellMu k *
    (((k ^ 2 / (k * k) : ℕ) : ℤ))

/-- The physical square grows by exactly one signed border bill. -/
theorem closedSquareShell_physicalFloor_square_birth
    (k : ℕ) (hk : 1 ≤ k) :
    closedSquareShellPhysicalFloor k (k ^ 2) =
      closedSquareShellPhysicalFloor (k - 1) (k ^ 2) +
        closedSquareShellPhysicalBorder k := by
  have hpred : k - 1 + 1 = k := by omega
  have h := closedSquareShell_doubleSum_square_succ
    (fun a b : ℕ =>
      closedSquareShellMu a * closedSquareShellMu b *
        (((k ^ 2 / (a * b) : ℕ) : ℤ))) (k - 1)
  rw [hpred] at h
  unfold closedSquareShellPhysicalFloor closedSquareShellPhysicalBorder
  convert h using 1 <;> ring


#print axioms closedSquareShell_doubleSum_square_succ
#print axioms closedSquareShell_physicalFloor_square_birth
#print axioms closedSquareShell_generic_movingBoundary_telescope
#print axioms closedSquareShell_generic_movingComplement_telescope
end RHLean.Analysis

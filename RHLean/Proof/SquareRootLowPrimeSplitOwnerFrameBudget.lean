import Mathlib
import RHLean.Proof.SquareRootLowPrimeSharpFrameBudget

/-!
# Split exceptional/generic q-square owner budget

The selected prime-11 T-sector cannot simultaneously be an outside q-square
owner: the exact 11/q^2 tensor theorem requires the owner square to be coprime
to 11^2, and the selected zero-free carrier deletes 11^2 hits.  The natural
outside-owner schedule therefore splits into the finite exceptional block
`{3,5,7}` and the generic tail `q >= 13`.

This file records the quantitative advantage of keeping that split.  The
exceptional block spends exactly the elementary reciprocal-square budget
`1/3^2 + 1/5^2 + 1/7^2 = 1891/11025`.  The generic prime tail is dominated by
all odd integers from 13 onward, whose finite reciprocal-square telescope costs
at most `1/24`.

Consequently the final induction does not need an arbitrarily small generic
cross-owner error.  A sharp universal exceptional frame `3` together with any
generic frame at most `5` remains subcritical after the exact `(19/23)^2`
prime-11 factor.  The theorem below is conditional only on those two signed
frame inequalities and the already-existing global boundary estimate; it does
not assert the missing physical/recovered intertwining.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Proof
open RHLean.Arithmetic RHLean.Analysis
attribute [local instance] Classical.propDecidable

/-- The three small odd q-square owners not covered by the generic prime-11
layer. -/
def q2ExceptionalOwners (N : ℕ) : Finset ℕ :=
  (primesUpTo N).filter fun q => q = 3 ∨ q = 5 ∨ q = 7

/-- Outside q-square owners beyond the selected prime `11`. -/
def q2GenericOwners (N : ℕ) : Finset ℕ :=
  (primesUpTo N).filter fun q => 13 ≤ q

/-- The exceptional schedule is contained in the ambient prime schedule. -/
theorem q2ExceptionalOwners_subset_primesUpTo (N : ℕ) :
    q2ExceptionalOwners N ⊆ primesUpTo N :=
  Finset.filter_subset _ _

/-- The generic schedule is contained in the ambient prime schedule. -/
theorem q2GenericOwners_subset_primesUpTo (N : ℕ) :
    q2GenericOwners N ⊆ primesUpTo N :=
  Finset.filter_subset _ _

/-- The finite exceptional reciprocal-square budget. -/
theorem q2ExceptionalOwnerReciprocalSquareBudget_le (N : ℕ) :
    (∑ q ∈ q2ExceptionalOwners N, (1 : ℚ) / (q : ℚ) ^ 2) ≤
      (1891 : ℚ) / 11025 := by
  have hsub : q2ExceptionalOwners N ⊆ ({3, 5, 7} : Finset ℕ) := by
    intro q hq
    rcases (Finset.mem_filter.mp hq).2 with h | h | h <;> simp [h]
  calc
    (∑ q ∈ q2ExceptionalOwners N, (1 : ℚ) / (q : ℚ) ^ 2) ≤
        ∑ q ∈ ({3, 5, 7} : Finset ℕ), (1 : ℚ) / (q : ℚ) ^ 2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
      intro q _hqNew _hqOld
      positivity
    _ = (1891 : ℚ) / 11025 := by norm_num

/-- One odd reciprocal-square term in the tail from `13` is dominated by a
one-step telescope. -/
theorem oddReciprocalSquareThirteenTailTerm_le_telescope (k : ℕ) :
    (1 : ℚ) / ((2 * k + 13 : ℕ) : ℚ) ^ 2 ≤
      1 / (4 * ((k : ℚ) + 6)) - 1 / (4 * ((k : ℚ) + 7)) := by
  have h6 : (0 : ℚ) < (k : ℚ) + 6 := by positivity
  have h7 : (0 : ℚ) < (k : ℚ) + 7 := by positivity
  rw [show (1 : ℚ) / (4 * ((k : ℚ) + 6)) -
      1 / (4 * ((k : ℚ) + 7)) =
      1 / (4 * ((k : ℚ) + 6) * ((k : ℚ) + 7)) by
    field_simp
    ring]
  apply (div_le_div_iff₀
    (by positivity : (0 : ℚ) < ((2 * k + 13 : ℕ) : ℚ) ^ 2)
    (by positivity : (0 : ℚ) < 4 * ((k : ℚ) + 6) * ((k : ℚ) + 7))).2
  push_cast
  nlinarith

/-- Finite odd-integer tail telescope starting at `13`. -/
theorem sum_oddReciprocalSquares_thirteenTail_le_sub (N : ℕ) :
    (∑ k ∈ Finset.range N,
      (1 : ℚ) / ((2 * k + 13 : ℕ) : ℚ) ^ 2) ≤
        1 / 24 - 1 / (4 * ((N : ℚ) + 6)) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ]
    calc
      _ ≤ (1 / 24 - 1 / (4 * ((N : ℚ) + 6))) +
          (1 / (4 * ((N : ℚ) + 6)) -
            1 / (4 * ((N : ℚ) + 7))) :=
        add_le_add ih (oddReciprocalSquareThirteenTailTerm_le_telescope N)
      _ = 1 / 24 - 1 / (4 * ((((N + 1 : ℕ) : ℚ)) + 6)) := by
        push_cast
        ring

/-- All finite odd integers from `13` onward have reciprocal-square mass at most
`1/24`. -/
theorem sum_oddReciprocalSquares_thirteenTail_le (N : ℕ) :
    (∑ k ∈ Finset.range N,
      (1 : ℚ) / ((2 * k + 13 : ℕ) : ℚ) ^ 2) ≤ 1 / 24 := by
  have h := sum_oddReciprocalSquares_thirteenTail_le_sub N
  have hp : (0 : ℚ) ≤ 1 / (4 * ((N : ℚ) + 6)) := by positivity
  linarith

private theorem q2GenericOwners_subset_oddTailImage (N : ℕ) :
    q2GenericOwners N ⊆
      (Finset.range N).image (fun k : ℕ => 2 * k + 13) := by
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨hqUp, hq13⟩
  have hdata := mem_primesUpTo.mp hqUp
  have hne : q ≠ 2 := by omega
  obtain ⟨k, hk⟩ := hdata.1.odd_of_ne_two hne
  have hk6 : 6 ≤ k := by omega
  refine Finset.mem_image.mpr ⟨k - 6, Finset.mem_range.mpr (by omega), ?_⟩
  omega

/-- The generic prime owner tail has reciprocal-square budget at most `1/24`. -/
theorem q2GenericOwnerReciprocalSquareBudget_le_one_over_twentyfour (N : ℕ) :
    (∑ q ∈ q2GenericOwners N, (1 : ℚ) / (q : ℚ) ^ 2) ≤ 1 / 24 := by
  have hsum :
      (∑ q ∈ q2GenericOwners N, (1 : ℚ) / (q : ℚ) ^ 2) ≤
        ∑ q ∈ (Finset.range N).image (fun k : ℕ => 2 * k + 13),
          (1 : ℚ) / (q : ℚ) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (q2GenericOwners_subset_oddTailImage N) ?_
    intro q _hqNew _hqOld
    positivity
  rw [Finset.sum_image] at hsum
  · exact hsum.trans (sum_oddReciprocalSquares_thirteenTail_le N)
  · intro a _ha b _hb hab
    omega

/-- Exceptional q-square daughter cutoffs consume at most `1891/11025` of the
parent scale. -/
theorem sum_q2ExceptionalOwners_squareDilatedCutoffs_le
    (N X : ℕ) :
    (∑ q ∈ q2ExceptionalOwners N, ((X / (q * q) : ℕ) : ℚ)) ≤
      ((1891 : ℚ) / 11025) * (X : ℚ) := by
  have h := sum_squareDilatedCutoffs_le_scale_mul_budget
    (q2ExceptionalOwners N) X
    (fun q hq => (mem_primesUpTo.mp
      (q2ExceptionalOwners_subset_primesUpTo N hq)).1)
  have hb := mul_le_mul_of_nonneg_left
    (q2ExceptionalOwnerReciprocalSquareBudget_le N)
    (by positivity : (0 : ℚ) ≤ X)
  nlinarith

/-- Generic q-square daughter cutoffs from `13` onward consume at most `1/24`
of the parent scale. -/
theorem sum_q2GenericOwners_squareDilatedCutoffs_le_one_over_twentyfour
    (N X : ℕ) :
    (∑ q ∈ q2GenericOwners N, ((X / (q * q) : ℕ) : ℚ)) ≤
      (1 / 24 : ℚ) * (X : ℚ) := by
  have h := sum_squareDilatedCutoffs_le_scale_mul_budget
    (q2GenericOwners N) X
    (fun q hq => (mem_primesUpTo.mp
      (q2GenericOwners_subset_primesUpTo N hq)).1)
  have hb := mul_le_mul_of_nonneg_left
    (q2GenericOwnerReciprocalSquareBudget_le_one_over_twentyfour N)
    (by positivity : (0 : ℚ) ≤ X)
  nlinarith

/-- **Split-owner induction gate.**  A universal frame `3` on the finite
exceptional owner block and a generic frame `5` on the legal outside owners
`q >= 13` are already enough.  The two signed interiors are combined by the
`5/3, 5/2` Young split; the global endpoint boundary uses the existing
`60/59, 60` split.  The resulting exact renormalization coefficient is below
one, and `1400 * B * X` is a convenient explicit linear envelope.

This theorem deliberately asks only for the two frame inequalities.  It does
not identify the physical compensated interior with the recovered q-square
daughters. -/
theorem elevenQ2_split_exceptionalThree_genericFive_implies_linear
    {E Iexc Igen b : ℕ → ℚ} {B : ℚ}
    (hB : 0 ≤ B)
    (hdecomp : ∀ X, E X ≤ (Iexc X + Igen X + b X) ^ 2)
    (hexceptional : ∀ X, (Iexc X) ^ 2 ≤
      3 * elevenWeightOneEnergyFactor *
        ∑ q ∈ q2ExceptionalOwners X, E (X / (q * q)))
    (hgeneric : ∀ X, (Igen X) ^ 2 ≤
      5 * elevenWeightOneEnergyFactor *
        ∑ q ∈ q2GenericOwners X, E (X / (q * q)))
    (hboundary : ∀ X, (b X) ^ 2 ≤ B * (X : ℚ)) :
    ∀ X, E X ≤ (1400 * B) * (X : ℚ) := by
  intro X
  induction X using Nat.strong_induction_on with
  | h X ih =>
      by_cases hX : X = 0
      · subst X
        have hexcEmpty : q2ExceptionalOwners 0 = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro q hq
          have hp := mem_primesUpTo.mp
            (q2ExceptionalOwners_subset_primesUpTo 0 hq)
          omega
        have hgenEmpty : q2GenericOwners 0 = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro q hq
          have hp := mem_primesUpTo.mp
            (q2GenericOwners_subset_primesUpTo 0 hq)
          omega
        have he := hexceptional 0
        have hg := hgeneric 0
        have hb := hboundary 0
        have hd := hdecomp 0
        rw [hexcEmpty] at he
        rw [hgenEmpty] at hg
        simp at he hg hb ⊢
        nlinarith
      · have hK : 0 ≤ 1400 * B := by positivity
        have hexcChildren :
            (∑ q ∈ q2ExceptionalOwners X, E (X / (q * q))) ≤
              (1400 * B) *
                ∑ q ∈ q2ExceptionalOwners X,
                  ((X / (q * q) : ℕ) : ℚ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro q hq
          have hp := (mem_primesUpTo.mp
            (q2ExceptionalOwners_subset_primesUpTo X hq)).1
          exact ih (X / (q * q))
            (Nat.div_lt_self (Nat.pos_of_ne_zero hX)
              (by nlinarith [hp.two_le]))
        have hgenChildren :
            (∑ q ∈ q2GenericOwners X, E (X / (q * q))) ≤
              (1400 * B) *
                ∑ q ∈ q2GenericOwners X,
                  ((X / (q * q) : ℕ) : ℚ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro q hq
          have hp := (mem_primesUpTo.mp
            (q2GenericOwners_subset_primesUpTo X hq)).1
          exact ih (X / (q * q))
            (Nat.div_lt_self (Nat.pos_of_ne_zero hX)
              (by nlinarith [hp.two_le]))
        have hexcScale := sum_q2ExceptionalOwners_squareDilatedCutoffs_le X X
        have hgenScale :=
          sum_q2GenericOwners_squareDilatedCutoffs_le_one_over_twentyfour X X
        have hexcChildren' :
            (∑ q ∈ q2ExceptionalOwners X, E (X / (q * q))) ≤
              (1400 * B) * (((1891 : ℚ) / 11025) * (X : ℚ)) :=
          hexcChildren.trans (mul_le_mul_of_nonneg_left hexcScale hK)
        have hgenChildren' :
            (∑ q ∈ q2GenericOwners X, E (X / (q * q))) ≤
              (1400 * B) * ((1 / 24 : ℚ) * (X : ℚ)) :=
          hgenChildren.trans (mul_le_mul_of_nonneg_left hgenScale hK)
        have he := hexceptional X
        have hg := hgeneric X
        have hpair :
            (Iexc X + Igen X) ^ 2 ≤
              (5 : ℚ) / 3 * (Iexc X) ^ 2 +
                (5 : ℚ) / 2 * (Igen X) ^ 2 := by
          nlinarith [sq_nonneg (2 * Iexc X - 3 * Igen X)]
        have hinner :
            (Iexc X + Igen X) ^ 2 ≤
              5 * elevenWeightOneEnergyFactor *
                  (∑ q ∈ q2ExceptionalOwners X, E (X / (q * q))) +
                (25 : ℚ) / 2 * elevenWeightOneEnergyFactor *
                  (∑ q ∈ q2GenericOwners X, E (X / (q * q))) := by
          calc
            (Iexc X + Igen X) ^ 2 ≤
                (5 : ℚ) / 3 * (Iexc X) ^ 2 +
                  (5 : ℚ) / 2 * (Igen X) ^ 2 := hpair
            _ ≤ (5 : ℚ) / 3 *
                    (3 * elevenWeightOneEnergyFactor *
                      ∑ q ∈ q2ExceptionalOwners X, E (X / (q * q))) +
                  (5 : ℚ) / 2 *
                    (5 * elevenWeightOneEnergyFactor *
                      ∑ q ∈ q2GenericOwners X, E (X / (q * q))) := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left he (by norm_num))
                (mul_le_mul_of_nonneg_left hg (by norm_num))
            _ = 5 * elevenWeightOneEnergyFactor *
                    (∑ q ∈ q2ExceptionalOwners X, E (X / (q * q))) +
                  (25 : ℚ) / 2 * elevenWeightOneEnergyFactor *
                    (∑ q ∈ q2GenericOwners X, E (X / (q * q))) := by ring
        have hcoefExc : 0 ≤ 5 * elevenWeightOneEnergyFactor :=
          mul_nonneg (by norm_num) elevenWeightOneEnergyFactor_nonneg
        have hcoefGen : 0 ≤ (25 : ℚ) / 2 * elevenWeightOneEnergyFactor :=
          mul_nonneg (by norm_num) elevenWeightOneEnergyFactor_nonneg
        have hinner' :
            (Iexc X + Igen X) ^ 2 ≤
              5 * elevenWeightOneEnergyFactor *
                  ((1400 * B) * (((1891 : ℚ) / 11025) * (X : ℚ))) +
                (25 : ℚ) / 2 * elevenWeightOneEnergyFactor *
                  ((1400 * B) * ((1 / 24 : ℚ) * (X : ℚ))) :=
          hinner.trans (add_le_add
            (mul_le_mul_of_nonneg_left hexcChildren' hcoefExc)
            (mul_le_mul_of_nonneg_left hgenChildren' hcoefGen))
        have hb := hboundary X
        have hd := hdecomp X
        have hy :
            (Iexc X + Igen X + b X) ^ 2 ≤
              (60 : ℚ) / 59 * (Iexc X + Igen X) ^ 2 +
                60 * (b X) ^ 2 := by
          nlinarith [sq_nonneg ((Iexc X + Igen X) - 59 * b X)]
        have hinnerWeighted :=
          mul_le_mul_of_nonneg_left hinner' (by norm_num : (0 : ℚ) ≤ 60 / 59)
        have hbWeighted :=
          mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℚ) ≤ 60)
        have hcoef :
            (60 : ℚ) +
                (60 : ℚ) / 59 * (361 / 529 : ℚ) * 1400 *
                  (5 * ((1891 : ℚ) / 11025) +
                    (25 : ℚ) / 2 * (1 / 24 : ℚ)) ≤ 1400 := by
          norm_num
        have hBX : 0 ≤ B * (X : ℚ) := mul_nonneg hB (by positivity)
        calc
          E X ≤ (Iexc X + Igen X + b X) ^ 2 := hd
          _ ≤ (60 : ℚ) / 59 * (Iexc X + Igen X) ^ 2 +
                60 * (b X) ^ 2 := hy
          _ ≤ (60 : ℚ) / 59 *
                (5 * elevenWeightOneEnergyFactor *
                    ((1400 * B) * (((1891 : ℚ) / 11025) * (X : ℚ))) +
                  (25 : ℚ) / 2 * elevenWeightOneEnergyFactor *
                    ((1400 * B) * ((1 / 24 : ℚ) * (X : ℚ)))) +
                60 * (B * (X : ℚ)) :=
            add_le_add hinnerWeighted hbWeighted
          _ = ((60 : ℚ) +
                (60 : ℚ) / 59 * (361 / 529 : ℚ) * 1400 *
                  (5 * ((1891 : ℚ) / 11025) +
                    (25 : ℚ) / 2 * (1 / 24 : ℚ))) *
                (B * (X : ℚ)) := by
            rw [elevenWeightOneEnergyFactor_eq]
            ring
          _ ≤ 1400 * (B * (X : ℚ)) :=
            mul_le_mul_of_nonneg_right hcoef hBX
          _ = (1400 * B) * (X : ℚ) := by ring

end RHLean.Proof

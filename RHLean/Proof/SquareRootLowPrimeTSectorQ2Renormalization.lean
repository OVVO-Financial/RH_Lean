import Mathlib
import RHLean.Analysis.FinitePrimeTMixing
import RHLean.Proof.SquareRootLowPrimeGoSecondContactSources

/-!
# T-sector spectral damping times q^2 scale descent

The old finite-prime T-sector calculation and the new Go second-contact scale
flux are complementary rather than competing mechanisms.

* At the first generic prime `11`, the Mertens-visible weight-one Walsh mode is
  multiplied by `19/23`, so its square-energy factor is `(19/23)^2 < 3/4`.
* Every second-contact owner `q` sends its unresolved daughter to the cutoff
  `X / q^2`.  Summed over all possible prime owners, these daughter scales have
  total reciprocal-square budget strictly below the parent scale.

The second fact is proved here with an elementary finite telescoping estimate;
no PNT or infinite-series evaluation is used.  Combining the two gives a
strictly subcritical energy branching coefficient.  The final theorem packages
the resulting strong-induction engine: any nonnegative energy profile whose
one-step arithmetic recurrence has the exact `11`-sector factor and the `q^2`
daughters is automatically linear in the arithmetic scale.

This module does **not** assert that the physical Mobius endpoint already
satisfies that recurrence.  Its purpose is to make the remaining intertwining
statement exact and quantitatively sufficient: once the physical degree-one
mode is transported through the existing `11`-state law before the Go daughters
are separated, no further analytic estimate is needed to close the energy
induction.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Finite reciprocal-square prefix, including the terms `2,...,N`. -/
def reciprocalSquarePrefix (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range (N + 1),
    if 2 ≤ n then (1 : ℚ) / (n : ℚ) ^ 2 else 0

/-- The elementary summand comparison behind the reciprocal-square telescope:
`1/n^2 <= 1/(n-1) - 1/n` for `n >= 2`. -/
theorem reciprocalSquareTerm_le_telescope
    {n : ℕ} (hn : 2 ≤ n) :
    (1 : ℚ) / (n : ℚ) ^ 2 ≤
      1 / ((n : ℚ) - 1) - 1 / (n : ℚ) := by
  have hnq : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hn0 : (0 : ℚ) < (n : ℚ) := by linarith
  have hnm10 : (0 : ℚ) < (n : ℚ) - 1 := by linarith
  rw [show 1 / ((n : ℚ) - 1) - 1 / (n : ℚ) =
      1 / (((n : ℚ) - 1) * (n : ℚ)) by
        field_simp [ne_of_gt hn0, ne_of_gt hnm10]
        ring]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  simp only [one_mul]
  exact (inv_le_inv₀ (by positivity : (0 : ℚ) < (n : ℚ) ^ 2)
    (mul_pos hnm10 hn0)).2 (by nlinarith)

/-- The finite reciprocal-square prefix is bounded by the elementary telescoping
majorant `1 - 1/N`. -/
theorem reciprocalSquarePrefix_le_one_sub_inv
    (k : ℕ) :
    reciprocalSquarePrefix (k + 2) ≤
      1 - 1 / ((k + 2 : ℕ) : ℚ) := by
  induction k with
  | zero =>
      norm_num [reciprocalSquarePrefix, Finset.sum_range_succ]
  | succ k ih =>
      have hterm := reciprocalSquareTerm_le_telescope
        (n := k + 3) (by omega)
      have hsplit :
          reciprocalSquarePrefix (k + 3) =
            reciprocalSquarePrefix (k + 2) +
              (1 : ℚ) / ((k + 3 : ℕ) : ℚ) ^ 2 := by
        unfold reciprocalSquarePrefix
        rw [show k + 3 + 1 = (k + 2 + 1) + 1 by omega,
          Finset.sum_range_succ]
        simp only [show 2 ≤ k + 3 by omega, if_true]
      rw [hsplit]
      calc
        reciprocalSquarePrefix (k + 2) +
            (1 : ℚ) / ((k + 3 : ℕ) : ℚ) ^ 2 ≤
          (1 - 1 / ((k + 2 : ℕ) : ℚ)) +
            (1 : ℚ) / ((k + 3 : ℕ) : ℚ) ^ 2 :=
              add_le_add_right ih _
        _ ≤ (1 - 1 / ((k + 2 : ℕ) : ℚ)) +
            (1 / (((k + 3 : ℕ) : ℚ) - 1) -
              1 / ((k + 3 : ℕ) : ℚ)) :=
              add_le_add_left hterm _
        _ = 1 - 1 / ((k + 3 : ℕ) : ℚ) := by
          have hkcast : (((k + 3 : ℕ) : ℚ) - 1) =
              ((k + 2 : ℕ) : ℚ) := by
            push_cast
            ring
          rw [hkcast]
          ring

/-- In particular every finite reciprocal-square prefix from `2` onward has
budget at most one. -/
theorem reciprocalSquarePrefix_le_one (N : ℕ) :
    reciprocalSquarePrefix N ≤ 1 := by
  by_cases hN : N < 2
  · interval_cases N <;>
      norm_num [reciprocalSquarePrefix, Finset.sum_range_succ]
  · obtain ⟨k, rfl⟩ : ∃ k, N = k + 2 := by
      exact ⟨N - 2, by omega⟩
    have h := reciprocalSquarePrefix_le_one_sub_inv k
    have hnonneg : (0 : ℚ) ≤ 1 / (((k + 2 : ℕ) : ℚ)) := by positivity
    linarith

/-- Reciprocal-square budget of the prime owners through `N`. -/
def primeOwnerReciprocalSquareBudget (N : ℕ) : ℚ :=
  ∑ q ∈ primesUpTo N, (1 : ℚ) / (q : ℚ) ^ 2

/-- Prime owners consume no more reciprocal-square budget than all integers.
The bound is finite and elementary; no Euler product or zeta value is used. -/
theorem primeOwnerReciprocalSquareBudget_le_one (N : ℕ) :
    primeOwnerReciprocalSquareBudget N ≤ 1 := by
  have hsub : primesUpTo N ⊆ Finset.range (N + 1) := by
    intro q hq
    exact Finset.mem_range.mpr (by
      have hqN := (mem_primesUpTo.mp hq).2
      omega)
  have hsum :
      primeOwnerReciprocalSquareBudget N ≤ reciprocalSquarePrefix N := by
    unfold primeOwnerReciprocalSquareBudget reciprocalSquarePrefix
    calc
      (∑ q ∈ primesUpTo N, (1 : ℚ) / (q : ℚ) ^ 2) =
          ∑ q ∈ primesUpTo N,
            (if 2 ≤ q then (1 : ℚ) / (q : ℚ) ^ 2 else 0) := by
        apply Finset.sum_congr rfl
        intro q hq
        have hq2 := (mem_primesUpTo.mp hq).1.two_le
        simp [hq2]
      _ ≤ ∑ q ∈ Finset.range (N + 1),
            (if 2 ≤ q then (1 : ℚ) / (q : ℚ) ^ 2 else 0) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro q _hqRange hqNot
        split_ifs
        · positivity
        · norm_num
  exact hsum.trans (reciprocalSquarePrefix_le_one N)

/-- The sum of the literal square-dilated daughter cutoffs is at most the parent
scale.  This is the finite `q^2` branching budget in the exact arithmetic units
used by the Go recursion. -/
theorem sum_primeOwner_squareDilatedCutoffs_le_parent
    (N X : ℕ) :
    (∑ q ∈ primesUpTo N, ((X / (q * q) : ℕ) : ℚ)) ≤ (X : ℚ) := by
  have hterm : ∀ q ∈ primesUpTo N,
      ((X / (q * q) : ℕ) : ℚ) ≤
        (X : ℚ) * ((1 : ℚ) / (q : ℚ) ^ 2) := by
    intro q hq
    have hqPrime := (mem_primesUpTo.mp hq).1
    have hqqPosNat : 0 < q * q := Nat.mul_pos hqPrime.pos hqPrime.pos
    have hmulNat : (X / (q * q)) * (q * q) ≤ X :=
      Nat.div_mul_le_self X (q * q)
    have hmul :
        (((X / (q * q) : ℕ) : ℚ) * ((q * q : ℕ) : ℚ)) ≤ (X : ℚ) := by
      exact_mod_cast hmulNat
    have hqqPos : (0 : ℚ) < ((q * q : ℕ) : ℚ) := by exact_mod_cast hqqPosNat
    have hdiv := (le_div_iff₀ hqqPos).2 hmul
    calc
      ((X / (q * q) : ℕ) : ℚ) ≤
          (X : ℚ) / ((q * q : ℕ) : ℚ) := hdiv
      _ = (X : ℚ) * ((1 : ℚ) / (q : ℚ) ^ 2) := by
        push_cast
        rw [pow_two]
        field_simp
  calc
    (∑ q ∈ primesUpTo N, ((X / (q * q) : ℕ) : ℚ)) ≤
        ∑ q ∈ primesUpTo N,
          (X : ℚ) * ((1 : ℚ) / (q : ℚ) ^ 2) := by
      apply Finset.sum_le_sum
      intro q hq
      exact hterm q hq
    _ = (X : ℚ) * primeOwnerReciprocalSquareBudget N := by
      unfold primeOwnerReciprocalSquareBudget
      rw [Finset.mul_sum]
    _ ≤ (X : ℚ) * 1 := by
      exact mul_le_mul_of_nonneg_left
        (primeOwnerReciprocalSquareBudget_le_one N) (by positivity)
    _ = (X : ℚ) := by ring

/-- Exact energy multiplier of the first generic `T`-sector prime on the
Mertens-visible weight-one Walsh mode. -/
def elevenWeightOneEnergyFactor : ℚ :=
  (onePrimeWalshFactor 11 1) ^ 2

@[simp] theorem elevenWeightOneEnergyFactor_eq :
    elevenWeightOneEnergyFactor = (19 : ℚ) ^ 2 / 23 ^ 2 := by
  rw [elevenWeightOneEnergyFactor, onePrimeWalshFactor_eleven_one]
  ring

/-- One `11`-layer already dissipates more than one quarter of weight-one
energy. -/
theorem elevenWeightOneEnergyFactor_lt_three_quarters :
    elevenWeightOneEnergyFactor < (3 : ℚ) / 4 := by
  rw [elevenWeightOneEnergyFactor_eq]
  norm_num

/-- The spectral factor is nonnegative. -/
theorem elevenWeightOneEnergyFactor_nonneg :
    0 ≤ elevenWeightOneEnergyFactor := by
  unfold elevenWeightOneEnergyFactor
  positivity

/-- The numerical renormalization constant obtained by combining the crude
unit `q^2` daughter budget with the exact `11` weight-one energy factor. -/
def elevenQ2RenormalizationCoefficient : ℚ :=
  elevenWeightOneEnergyFactor

/-- The combined T-sector / `q^2` branching coefficient is strictly
subcritical. -/
theorem elevenQ2RenormalizationCoefficient_lt_one :
    elevenQ2RenormalizationCoefficient < 1 := by
  unfold elevenQ2RenormalizationCoefficient
  exact elevenWeightOneEnergyFactor_lt_three_quarters.trans (by norm_num)

/-- One-step recurrence required of an arithmetic energy profile.  The
coefficient is not a hypothesis: it is the exact compiled `11` weight-one
factor.  The only daughters are the square-dilated cutoffs already present in
the Go recursion. -/
def ElevenQ2EnergyStep (E : ℕ → ℚ) (C : ℚ) : Prop :=
  ∀ X : ℕ,
    E X ≤ C * (X : ℚ) +
      elevenWeightOneEnergyFactor *
        ∑ q ∈ primesUpTo X, E (X / (q * q))

/-- **Subcritical energy induction.**  Once the physical arithmetic supplies
the preceding one-step recurrence, the endpoint energy is automatically linear
in scale.  The factor `4` is deliberately coarse: `11` contributes less than
`3/4`, while all `q^2` daughters together consume at most one parent scale.

This is the quantitative closure that the old growing-CRT route lacked: a fixed
finite spectral contraction can now be reused at every strict multiplicative
scale descent. -/
theorem elevenQ2EnergyStep_implies_linear
    {E : ℕ → ℚ} {C : ℚ}
    (hC : 0 ≤ C)
    (hstep : ElevenQ2EnergyStep E C) :
    ∀ X : ℕ, E X ≤ 4 * C * (X : ℚ) := by
  intro X
  induction X using Nat.strong_induction_on with
  | h X ih =>
      by_cases hX : X = 0
      · subst X
        have hs := hstep 0
        simpa [ElevenQ2EnergyStep] using hs
      · have hXpos : 0 < X := Nat.pos_of_ne_zero hX
        have hchildren :
            (∑ q ∈ primesUpTo X, E (X / (q * q))) ≤
              4 * C *
                (∑ q ∈ primesUpTo X, ((X / (q * q) : ℕ) : ℚ)) := by
          calc
            (∑ q ∈ primesUpTo X, E (X / (q * q))) ≤
                ∑ q ∈ primesUpTo X,
                  4 * C * ((X / (q * q) : ℕ) : ℚ) := by
              apply Finset.sum_le_sum
              intro q hq
              have hqPrime := (mem_primesUpTo.mp hq).1
              have hqq : 1 < q * q := by nlinarith [hqPrime.two_le]
              have hchild : X / (q * q) < X :=
                Nat.div_lt_self hXpos hqq
              exact ih (X / (q * q)) hchild
            _ = 4 * C *
                (∑ q ∈ primesUpTo X, ((X / (q * q) : ℕ) : ℚ)) := by
              rw [Finset.mul_sum]
        have hscale := sum_primeOwner_squareDilatedCutoffs_le_parent X X
        have hchildrenParent :
            (∑ q ∈ primesUpTo X, E (X / (q * q))) ≤
              4 * C * (X : ℚ) := by
          exact hchildren.trans
            (mul_le_mul_of_nonneg_left hscale (by positivity))
        have hs := hstep X
        have hlambda :
            elevenWeightOneEnergyFactor ≤ (3 : ℚ) / 4 :=
          le_of_lt elevenWeightOneEnergyFactor_lt_three_quarters
        have hweighted :
            elevenWeightOneEnergyFactor *
                (∑ q ∈ primesUpTo X, E (X / (q * q))) ≤
              ((3 : ℚ) / 4) * (4 * C * (X : ℚ)) := by
          calc
            elevenWeightOneEnergyFactor *
                (∑ q ∈ primesUpTo X, E (X / (q * q))) ≤
              elevenWeightOneEnergyFactor * (4 * C * (X : ℚ)) := by
                exact mul_le_mul_of_nonneg_left hchildrenParent
                  elevenWeightOneEnergyFactor_nonneg
            _ ≤ ((3 : ℚ) / 4) * (4 * C * (X : ℚ)) := by
                exact mul_le_mul_of_nonneg_right hlambda (by positivity)
        calc
          E X ≤ C * (X : ℚ) +
              elevenWeightOneEnergyFactor *
                ∑ q ∈ primesUpTo X, E (X / (q * q)) := hs
          _ ≤ C * (X : ℚ) +
              ((3 : ℚ) / 4) * (4 * C * (X : ℚ)) :=
                add_le_add_left hweighted _
          _ = 4 * C * (X : ℚ) := by ring

end RHLean.Proof

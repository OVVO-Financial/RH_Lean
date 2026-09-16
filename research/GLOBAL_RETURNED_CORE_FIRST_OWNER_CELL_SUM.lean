import Mathlib
import «research.GLOBAL_RETURNED_CORE_SIGNED_CELL_TELESCOPE»

/-!
# Global first-owner cell Fubini

This file performs the finite regrouping from lower-signature cells to the
actual oriented p-free / p-divisible cross-pair carrier.  It is the global
counterpart of the local signed cell telescope.

The carrier orientation is arithmetic, not numerical: the first coordinate is
p-free and the second is p-divisible.  Thus every pair in one cell is counted
once even when the p-divisible integer is numerically smaller.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- All nonzero common-clock pairs lying in opposite p-branches of one lower
signature.  The p-free coordinate is placed first. -/
def lowOwnerFirstOwnerOrientedCrossPairCarrier
    (R p : ℕ) : Finset (ℕ × ℕ) :=
  ((lowOwnerNonzeroMobiusCarrier R).product
      (lowOwnerNonzeroMobiusCarrier R)).filter fun ab =>
    squarefreeLowerPrimeSignature p ab.1 =
        squarefreeLowerPrimeSignature p ab.2 ∧
      ¬ p ∣ ab.1 ∧ p ∣ ab.2

/-- One signature fibre of the oriented cross-pair carrier is exactly the
Cartesian product of that cell's base and child branches. -/
theorem lowOwnerFirstOwnerOrientedCrossPairCarrier_filter_signature_eq_product
    (R p : ℕ) (sig : Finset ℕ) :
    (lowOwnerFirstOwnerOrientedCrossPairCarrier R p).filter
        (fun ab => squarefreeLowerPrimeSignature p ab.1 = sig) =
      (lowOwnerFirstOwnerBaseFiber R p sig).product
        (lowOwnerFirstOwnerChildFiber R p sig) := by
  ext ab
  rcases ab with ⟨a, b⟩
  constructor
  · intro hab
    rcases Finset.mem_filter.mp hab with ⟨hcross, hsigA⟩
    rcases Finset.mem_filter.mp hcross with ⟨hprod, hdata⟩
    rcases Finset.mem_product.mp hprod with ⟨haCar, hbCar⟩
    have hsigB : squarefreeLowerPrimeSignature p b = sig := by
      rw [← hdata.1, hsigA]
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨haCar, ⟨hsigA, hdata.2.1⟩⟩,
       Finset.mem_filter.mpr ⟨hbCar, ⟨hsigB, hdata.2.2⟩⟩⟩
  · intro hab
    rcases Finset.mem_product.mp hab with ⟨haBase, hbChild⟩
    rcases Finset.mem_filter.mp haBase with ⟨haCar, hbase⟩
    rcases Finset.mem_filter.mp hbChild with ⟨hbCar, hchild⟩
    have hsame : squarefreeLowerPrimeSignature p a =
        squarefreeLowerPrimeSignature p b := by
      rw [hbase.1, hchild.1]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨haCar, hbCar⟩,
          ⟨hsame, hbase.2, hchild.2⟩⟩,
        hbase.1⟩

/-- A cell Gram is literally the double sum over its oriented base/child pair
product. -/
theorem lowOwnerFirstOwnerCellGram_eq_sum_product
    (R p : ℕ) (sig : Finset ℕ) :
    lowOwnerFirstOwnerCellGram R p sig =
      ∑ ab ∈ (lowOwnerFirstOwnerBaseFiber R p sig).product
          (lowOwnerFirstOwnerChildFiber R p sig),
        lowOwnerZeroFrequencyMobiusSite R ab.1 *
          lowOwnerZeroFrequencyMobiusSite R ab.2 := by
  unfold lowOwnerFirstOwnerCellGram
    lowOwnerFirstOwnerBaseAmplitude lowOwnerFirstOwnerChildAmplitude
  calc
    (∑ a ∈ lowOwnerFirstOwnerBaseFiber R p sig,
        lowOwnerZeroFrequencyMobiusSite R a) *
        (∑ b ∈ lowOwnerFirstOwnerChildFiber R p sig,
          lowOwnerZeroFrequencyMobiusSite R b) =
      ∑ a ∈ lowOwnerFirstOwnerBaseFiber R p sig,
        ∑ b ∈ lowOwnerFirstOwnerChildFiber R p sig,
          lowOwnerZeroFrequencyMobiusSite R a *
            lowOwnerZeroFrequencyMobiusSite R b := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.mul_sum]
    _ = ∑ ab ∈ (lowOwnerFirstOwnerBaseFiber R p sig).product
          (lowOwnerFirstOwnerChildFiber R p sig),
        lowOwnerZeroFrequencyMobiusSite R ab.1 *
          lowOwnerZeroFrequencyMobiusSite R ab.2 := by
      symm
      simpa only using
        (Finset.sum_product
          (s := lowOwnerFirstOwnerBaseFiber R p sig)
          (t := lowOwnerFirstOwnerChildFiber R p sig)
          (f := fun ab : ℕ × ℕ =>
            lowOwnerZeroFrequencyMobiusSite R ab.1 *
              lowOwnerZeroFrequencyMobiusSite R ab.2))

/-- **Global signature Fubini.**  Summing the cell Grams is exactly summing the
actual oriented p-free/p-divisible first-separation cross pairs. -/
theorem sum_lowOwnerFirstOwnerCellGram_eq_orientedCrossPairs
    (R p : ℕ) :
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerCellGram R p sig) =
      ∑ ab ∈ lowOwnerFirstOwnerOrientedCrossPairCarrier R p,
        lowOwnerZeroFrequencyMobiusSite R ab.1 *
          lowOwnerZeroFrequencyMobiusSite R ab.2 := by
  let S := lowOwnerFirstOwnerOrientedCrossPairCarrier R p
  let T := lowOwnerFirstOwnerSignatureSet R p
  let g : ℕ × ℕ → Finset ℕ := fun ab =>
    squarefreeLowerPrimeSignature p ab.1
  let f : ℕ × ℕ → ℝ := fun ab =>
    lowOwnerZeroFrequencyMobiusSite R ab.1 *
      lowOwnerZeroFrequencyMobiusSite R ab.2
  have hmaps : ∀ ab ∈ S, g ab ∈ T := by
    intro ab hab
    have hcross : ab ∈ lowOwnerFirstOwnerOrientedCrossPairCarrier R p := hab
    rcases Finset.mem_filter.mp hcross with ⟨hprod, _hdata⟩
    have haCar := (Finset.mem_product.mp hprod).1
    exact Finset.mem_image.mpr ⟨ab.1, haCar, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := T) (g := g) hmaps f
  calc
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        lowOwnerFirstOwnerCellGram R p sig) =
      ∑ sig ∈ T,
        ∑ ab ∈ (lowOwnerFirstOwnerBaseFiber R p sig).product
            (lowOwnerFirstOwnerChildFiber R p sig), f ab := by
          apply Finset.sum_congr rfl
          intro sig _hsig
          exact lowOwnerFirstOwnerCellGram_eq_sum_product R p sig
    _ = ∑ sig ∈ T,
        ∑ ab ∈ S with g ab = sig, f ab := by
          apply Finset.sum_congr rfl
          intro sig _hsig
          have hfiberSet :=
            lowOwnerFirstOwnerOrientedCrossPairCarrier_filter_signature_eq_product
              R p sig
          change
            (∑ ab ∈ (lowOwnerFirstOwnerBaseFiber R p sig).product
                (lowOwnerFirstOwnerChildFiber R p sig), f ab) =
              ∑ ab ∈ S.filter (fun ab => g ab = sig), f ab
          rw [show S.filter (fun ab => g ab = sig) =
              (lowOwnerFirstOwnerBaseFiber R p sig).product
                (lowOwnerFirstOwnerChildFiber R p sig) by
            simpa [S, g] using hfiberSet]
    _ = ∑ ab ∈ S, f ab := hfiber
    _ = _ := rfl

end RHLean.Proof

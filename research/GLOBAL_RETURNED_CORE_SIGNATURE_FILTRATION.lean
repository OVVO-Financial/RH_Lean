import Mathlib
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_SIGNATURE_FUBINI»

/-!
# First-owner Gram as an exact prime-filtration energy decrement

For fixed `p`, the lower-prime signature partitions the actual nonzero AMP
carrier.  The full amplitude of one signature cell is exactly its p-free branch
plus its p-divisible branch, hence exactly the Dirichlet incidence amplitude
constructed in the kernel lift.

Therefore splitting every lower-signature cell by the p-coordinate changes the
sum of cell squares by exactly twice the first-owner cell Gram:

  Energy(before p) = Energy(after splitting p) + 2 * FirstOwnerGram(p).

This is the finite Hilbert-space filtration behind the first-owner expansion.
No estimate appears; it is a polarization identity on the literal carrier.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Full nonzero AMP carrier in one lower-prime signature cell. -/
def lowOwnerFirstOwnerSignatureCellCarrier
    (R p : ℕ) (sig : Finset ℕ) : Finset ℕ :=
  (lowOwnerNonzeroMobiusCarrier R).filter fun n =>
    squarefreeLowerPrimeSignature p n = sig

/-- Full AMP amplitude in one lower-prime signature cell. -/
def lowOwnerFirstOwnerSignatureCellAmplitude
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  ∑ n ∈ lowOwnerFirstOwnerSignatureCellCarrier R p sig,
    lowOwnerZeroFrequencyMobiusSite R n

/-- The p-free half of a signature cell is exactly the existing base fibre. -/
theorem lowOwnerFirstOwnerSignatureCellCarrier_filter_not_dvd_eq_base
    (R p : ℕ) (sig : Finset ℕ) :
    (lowOwnerFirstOwnerSignatureCellCarrier R p sig).filter
        (fun n => ¬ p ∣ n) =
      lowOwnerFirstOwnerBaseFiber R p sig := by
  ext n
  simp [lowOwnerFirstOwnerSignatureCellCarrier,
    lowOwnerFirstOwnerBaseFiber, and_assoc, and_left_comm, and_comm]

/-- The p-divisible half is exactly the existing child fibre. -/
theorem lowOwnerFirstOwnerSignatureCellCarrier_filter_dvd_eq_child
    (R p : ℕ) (sig : Finset ℕ) :
    (lowOwnerFirstOwnerSignatureCellCarrier R p sig).filter
        (fun n => p ∣ n) =
      lowOwnerFirstOwnerChildFiber R p sig := by
  ext n
  simp [lowOwnerFirstOwnerSignatureCellCarrier,
    lowOwnerFirstOwnerChildFiber, and_assoc, and_left_comm, and_comm]

/-- A signature-cell amplitude is its p-free plus p-divisible branch. -/
theorem lowOwnerFirstOwnerSignatureCellAmplitude_eq_base_add_child
    (R p : ℕ) (sig : Finset ℕ) :
    lowOwnerFirstOwnerSignatureCellAmplitude R p sig =
      lowOwnerFirstOwnerBaseAmplitude R p sig +
        lowOwnerFirstOwnerChildAmplitude R p sig := by
  unfold lowOwnerFirstOwnerSignatureCellAmplitude
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := lowOwnerFirstOwnerSignatureCellCarrier R p sig)
    (p := fun n => p ∣ n)
    (f := lowOwnerZeroFrequencyMobiusSite R)
  rw [lowOwnerFirstOwnerSignatureCellCarrier_filter_dvd_eq_child,
    lowOwnerFirstOwnerSignatureCellCarrier_filter_not_dvd_eq_base] at hsplit
  unfold lowOwnerFirstOwnerBaseAmplitude lowOwnerFirstOwnerChildAmplitude
  linarith

/-- The kernel-lift Dirichlet incidence is not a new cell amplitude: it is
literally the full lower-signature cell amplitude. -/
theorem lowOwnerFirstOwnerDirichletIncidenceAmplitude_eq_signatureCellAmplitude
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerDirichletIncidenceAmplitude R p sig =
      lowOwnerFirstOwnerSignatureCellAmplitude R p sig := by
  rw [lowOwnerFirstOwnerDirichletIncidenceAmplitude_eq_base_add_child hp,
    lowOwnerFirstOwnerSignatureCellAmplitude_eq_base_add_child]

/-- Energy of the lower-prime-signature filtration immediately before splitting
the p-coordinate. -/
def lowOwnerFirstOwnerSignatureEnergy (R p : ℕ) : ℝ :=
  ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
    lowOwnerFirstOwnerSignatureCellAmplitude R p sig ^ 2

/-- Energy after splitting every current signature cell into its p-free and
p-divisible halves. -/
def lowOwnerFirstOwnerSignatureSplitEnergy (R p : ℕ) : ℝ :=
  ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
    (lowOwnerFirstOwnerBaseAmplitude R p sig ^ 2 +
      lowOwnerFirstOwnerChildAmplitude R p sig ^ 2)

/-- Pointwise filtration decrement equals twice the first-owner cell Gram. -/
theorem lowOwnerFirstOwnerSignatureCellEnergy_sub_split_eq_twoGram
    (R p : ℕ) (sig : Finset ℕ) :
    lowOwnerFirstOwnerSignatureCellAmplitude R p sig ^ 2 -
        (lowOwnerFirstOwnerBaseAmplitude R p sig ^ 2 +
          lowOwnerFirstOwnerChildAmplitude R p sig ^ 2) =
      2 * lowOwnerFirstOwnerCellGram R p sig := by
  rw [lowOwnerFirstOwnerSignatureCellAmplitude_eq_base_add_child]
  unfold lowOwnerFirstOwnerCellGram
  ring

/-- **Exact filtration telescope at one owner.** -/
theorem lowOwnerFirstOwnerSignatureEnergy_eq_split_add_two_cellGrams
    (R p : ℕ) :
    lowOwnerFirstOwnerSignatureEnergy R p =
      lowOwnerFirstOwnerSignatureSplitEnergy R p +
        2 * ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          lowOwnerFirstOwnerCellGram R p sig := by
  unfold lowOwnerFirstOwnerSignatureEnergy
    lowOwnerFirstOwnerSignatureSplitEnergy
  calc
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerSignatureCellAmplitude R p sig ^ 2) =
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        ((lowOwnerFirstOwnerBaseAmplitude R p sig ^ 2 +
            lowOwnerFirstOwnerChildAmplitude R p sig ^ 2) +
          2 * lowOwnerFirstOwnerCellGram R p sig) := by
            apply Finset.sum_congr rfl
            intro sig _hsig
            have h :=
              lowOwnerFirstOwnerSignatureCellEnergy_sub_split_eq_twoGram
                R p sig
            linarith
    _ = (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          (lowOwnerFirstOwnerBaseAmplitude R p sig ^ 2 +
            lowOwnerFirstOwnerChildAmplitude R p sig ^ 2)) +
        (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          2 * lowOwnerFirstOwnerCellGram R p sig) := by
            rw [Finset.sum_add_distrib]
    _ = (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          (lowOwnerFirstOwnerBaseAmplitude R p sig ^ 2 +
            lowOwnerFirstOwnerChildAmplitude R p sig ^ 2)) +
        2 * ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          lowOwnerFirstOwnerCellGram R p sig := by
            rw [Finset.mul_sum]

end RHLean.Proof

import Mathlib
import «research.GLOBAL_RETURNED_CORE_COMPENSATED_OWNER_BLOCK»

/-!
# Signed first-owner cell telescope

The compensated block must not be bounded by its parent square: doing so would
create an artificial clipped-square term.  Instead retain the two branch
squares exactly.

For one owner/signature cell write

* `L` for the admitted p-free base amplitude;
* `J` for the admitted child amplitude returned to its p-free parent coordinate
  before the fresh-prime Moebius sign flip;
* `C` for the clipped p-free base amplitude.

Then the actual p-divisible branch is `-J`, the full p-free branch is `L + C`,
and the mixed first-owner Gram is

  G = -(L + C) J.

The compiled AMP owner difference identifies `L - J` with the literal
`daughterCrossing - rootCrossing` amplitude.  Therefore

  2 G = (L - J)^2 - L^2 - J^2 - 2 C J.

This is the desired signed telescope.  The complete population transfers energy
through `L - J`; the two branch energies remain with favorable sign; and the
only untelescoped boundary is the mixed admitted/clipped term `C J`.  In
particular there is no `C^2` loss.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- AMP amplitude on the admitted p-free parent side of one cell. -/
def lowOwnerFirstOwnerAdmittedBaseAmplitude
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  ∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
    lowOwnerZeroFrequencyMobiusSite R a

/-- Child amplitude returned to its p-free parent coordinate, before the
fresh-prime Moebius sign reversal. -/
def lowOwnerFirstOwnerReturnedChildParentAmplitude
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  ∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
    lowOwnerZeroFrequencyMobiusWeight R (p * a) * realMoebiusStep a

/-- The actual p-divisible child branch is the negative of its returned parent
amplitude. -/
theorem lowOwnerFirstOwnerChildAmplitude_eq_neg_returnedParent
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerChildAmplitude R p sig =
      -lowOwnerFirstOwnerReturnedChildParentAmplitude R p sig := by
  rw [lowOwnerFirstOwnerChildAmplitude_eq_neg_returnedAdmitted hp]
  unfold lowOwnerFirstOwnerReturnedChildParentAmplitude
  rw [Finset.sum_neg_distrib]

/-- The full p-free branch is admitted base plus the literal clipped exit. -/
theorem lowOwnerFirstOwnerBaseAmplitude_eq_admittedBase_add_clipped
    (R p : ℕ) (sig : Finset ℕ) :
    lowOwnerFirstOwnerBaseAmplitude R p sig =
      lowOwnerFirstOwnerAdmittedBaseAmplitude R p sig +
        lowOwnerFirstOwnerClippedAmplitude R p sig := by
  simpa [lowOwnerFirstOwnerAdmittedBaseAmplitude,
    lowOwnerFirstOwnerClippedAmplitude] using
      lowOwnerFirstOwnerBaseAmplitude_eq_admitted_add_clipped R p sig

/-- The compiled daughter/root crossing amplitude is exactly `L - J`. -/
theorem lowOwnerFirstOwnerCompensatedInterior_eq_admitted_sub_returned
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerCompensatedInteriorAmplitude R p sig =
      lowOwnerFirstOwnerAdmittedBaseAmplitude R p sig -
        lowOwnerFirstOwnerReturnedChildParentAmplitude R p sig := by
  unfold lowOwnerFirstOwnerCompensatedInteriorAmplitude
    lowOwnerFirstOwnerAdmittedBaseAmplitude
    lowOwnerFirstOwnerReturnedChildParentAmplitude
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  unfold lowOwnerZeroFrequencyMobiusSite
  rw [← lowOwnerZeroFrequencyMobiusWeight_sub_mul
    (R := R) (p := p) (n := a) hp.one_le]
  ring

/-- The cell Gram itself has only one clipped occurrence: the clipped p-free
base multiplies the admitted returned child. -/
theorem lowOwnerFirstOwnerCellGram_eq_neg_basePlusClipped_mul_returned
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerCellGram R p sig =
      -(lowOwnerFirstOwnerAdmittedBaseAmplitude R p sig +
          lowOwnerFirstOwnerClippedAmplitude R p sig) *
        lowOwnerFirstOwnerReturnedChildParentAmplitude R p sig := by
  unfold lowOwnerFirstOwnerCellGram
  rw [lowOwnerFirstOwnerBaseAmplitude_eq_admittedBase_add_clipped,
    lowOwnerFirstOwnerChildAmplitude_eq_neg_returnedParent hp]
  ring

/-- **Exact signed cell telescope.**  No clipped square survives.  The complete
owner population is the energy increment `(L-J)^2 - L^2 - J^2`; the sole
untelescoped term is the mixed clipped/admitted cross term. -/
theorem two_mul_lowOwnerFirstOwnerCellGram_eq_completeTelescope_sub_clippedCross
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    2 * lowOwnerFirstOwnerCellGram R p sig =
      lowOwnerFirstOwnerCompensatedInteriorAmplitude R p sig ^ 2 -
        lowOwnerFirstOwnerAdmittedBaseAmplitude R p sig ^ 2 -
        lowOwnerFirstOwnerReturnedChildParentAmplitude R p sig ^ 2 -
        2 * lowOwnerFirstOwnerClippedAmplitude R p sig *
          lowOwnerFirstOwnerReturnedChildParentAmplitude R p sig := by
  rw [lowOwnerFirstOwnerCellGram_eq_neg_basePlusClipped_mul_returned hp,
    lowOwnerFirstOwnerCompensatedInterior_eq_admitted_sub_returned hp]
  ring

end RHLean.Proof

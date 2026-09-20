import Mathlib
import «research.GLOBAL_RETURNED_CORE_STOKES_BOUNDARY_IDENTIFICATION»

/-!
# Simultaneous physical-core support of the Stokes clip

The remaining Stokes clip must be studied after the owner chronology has been
removed. This file works directly on the common nonzero Mobius carrier
1 <= n <= X_R.

For one active prime toggle, the already-compiled Stokes identity says that the
finite difference of the simultaneous zero-frequency weight is exactly a
threshold-crossing defect. We package that pointwise defect, define the
physical cores on which some active prime sees a nonzero defect, and prove:

* every squarefree physical core outside that fracture carrier has exact zero
  toggle difference for every active prime;
* the fracture carrier is a literal subset of the square clock and hence has
  cardinality at most R^2.

No magnitude is taken over prime owners and no owner-count factor appears.
The remaining quantitative task is to identify the fully iterated mixed
Boolean-cube coefficient carried by each fractured core.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Exact signed threshold defect seen by toggling prime r at a squarefree
physical core n. -/
def lowOwnerStokesToggleCrossingDefect
    (R r n : ℕ) : ℝ :=
  if r ∣ n then
    -(lowOwnerDaughterCrossingWeight R r (n / r) -
      lowOwnerRootCrossingIndicator R r (n / r))
  else
    lowOwnerDaughterCrossingWeight R r n -
      lowOwnerRootCrossingIndicator R r n

/-- On the actual squarefree physical carrier, the toggle finite difference is
literally the signed threshold defect. -/
theorem lowOwnerZeroFrequencyMobiusWeight_sub_toggle_eq_toggleCrossingDefect
    {R r n : ℕ}
    (hr : r.Prime)
    (hn : n ∈ lowOwnerNonzeroMobiusCarrier R) :
    lowOwnerZeroFrequencyMobiusWeight R n -
        lowOwnerZeroFrequencyMobiusWeight R (primeCarrierToggle r n) =
      lowOwnerStokesToggleCrossingDefect R r n := by
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hn with
    ⟨hnSq, _hnPos⟩
  simpa [lowOwnerStokesToggleCrossingDefect] using
    (lowOwnerZeroFrequencyMobiusWeight_sub_toggle_eq_signedCrossing
      (R := R) (r := r) (n := n) hr hnSq)

/-- Physical squarefree cores at which at least one active prime toggle sees a
nonzero threshold defect. -/
def lowOwnerStokesFracturedCoreCarrier (R : ℕ) : Finset ℕ :=
  (lowOwnerNonzeroMobiusCarrier R).filter fun n =>
    ∃ r ∈ primesUpTo (squareRootEndpoint R),
      lowOwnerStokesToggleCrossingDefect R r n ≠ 0

theorem lowOwnerStokesFracturedCoreCarrier_subset_nonzeroCarrier
    (R : ℕ) :
    lowOwnerStokesFracturedCoreCarrier R ⊆
      lowOwnerNonzeroMobiusCarrier R := by
  intro n hn
  exact (Finset.mem_filter.mp hn).1

theorem lowOwnerStokesFracturedCoreCarrier_subset_clock
    (R : ℕ) :
    lowOwnerStokesFracturedCoreCarrier R ⊆
      Finset.Icc 1 (squareRootEndpoint R) := by
  intro n hn
  have hnCar :=
    lowOwnerStokesFracturedCoreCarrier_subset_nonzeroCarrier R hn
  exact (Finset.mem_filter.mp hnCar).1

theorem mem_lowOwnerStokesFracturedCoreCarrier_iff
    {R n : ℕ} :
    n ∈ lowOwnerStokesFracturedCoreCarrier R ↔
      n ∈ lowOwnerNonzeroMobiusCarrier R ∧
        ∃ r ∈ primesUpTo (squareRootEndpoint R),
          lowOwnerStokesToggleCrossingDefect R r n ≠ 0 := by
  simp [lowOwnerStokesFracturedCoreCarrier]

/-- Exact interior annihilation at first finite-difference level. -/
theorem clip_toggle_difference_eq_zero_of_not_fractured
    {R r n : ℕ}
    (hn : n ∈ lowOwnerNonzeroMobiusCarrier R)
    (hr : r ∈ primesUpTo (squareRootEndpoint R))
    (hnfract : n ∉ lowOwnerStokesFracturedCoreCarrier R) :
    lowOwnerZeroFrequencyMobiusWeight R n -
        lowOwnerZeroFrequencyMobiusWeight R (primeCarrierToggle r n) = 0 := by
  have hrPrime : r.Prime := (mem_primesUpTo.mp hr).1
  rw [lowOwnerZeroFrequencyMobiusWeight_sub_toggle_eq_toggleCrossingDefect
    hrPrime hn]
  by_contra hne
  apply hnfract
  exact Finset.mem_filter.mpr
    ⟨hn, ⟨r, hr, hne⟩⟩

/-- Equivalently, every active prime threshold defect vanishes off the fracture
carrier. -/
theorem toggleCrossingDefect_eq_zero_of_not_fractured
    {R r n : ℕ}
    (hn : n ∈ lowOwnerNonzeroMobiusCarrier R)
    (hr : r ∈ primesUpTo (squareRootEndpoint R))
    (hnfract : n ∉ lowOwnerStokesFracturedCoreCarrier R) :
    lowOwnerStokesToggleCrossingDefect R r n = 0 := by
  have hrPrime : r.Prime := (mem_primesUpTo.mp hr).1
  have h :=
    clip_toggle_difference_eq_zero_of_not_fractured
      (R := R) (r := r) (n := n) hn hr hnfract
  rwa [lowOwnerZeroFrequencyMobiusWeight_sub_toggle_eq_toggleCrossingDefect
    hrPrime hn] at h

/-- The sum of all active-prime first differences at one unfractured physical
core is exactly zero. -/
theorem sum_toggleCrossingDefect_eq_zero_of_not_fractured
    {R n : ℕ}
    (hn : n ∈ lowOwnerNonzeroMobiusCarrier R)
    (hnfract : n ∉ lowOwnerStokesFracturedCoreCarrier R) :
    (∑ r ∈ primesUpTo (squareRootEndpoint R),
      lowOwnerStokesToggleCrossingDefect R r n) = 0 := by
  apply Finset.sum_eq_zero
  intro r hr
  exact toggleCrossingDefect_eq_zero_of_not_fractured hn hr hnfract

/-- The geometric fracture support is automatically at most the size of the
square clock. -/
theorem card_lowOwnerStokesFracturedCoreCarrier_le_endpoint
    (R : ℕ) :
    (lowOwnerStokesFracturedCoreCarrier R).card ≤ squareRootEndpoint R := by
  have hcard :=
    Finset.card_le_card
      (lowOwnerStokesFracturedCoreCarrier_subset_clock R)
  simpa [Nat.card_Icc] using hcard

/-- Boundary area bound. Since X_R = R^2 - 1, the simultaneous fracture
carrier contains at most R^2 physical cores. -/
theorem card_fractured_clip_boundary_le_R_sq
    (R : ℕ) :
    (lowOwnerStokesFracturedCoreCarrier R).card ≤ R ^ 2 := by
  exact (card_lowOwnerStokesFracturedCoreCarrier_le_endpoint R).trans
    (by
      unfold squareRootEndpoint
      omega)

/-- Every fractured site is squarefree and positive. -/
theorem lowOwnerStokesFracturedCoreCarrier_squarefree_pos
    {R n : ℕ}
    (hn : n ∈ lowOwnerStokesFracturedCoreCarrier R) :
    Squarefree n ∧ 0 < n := by
  exact lowOwnerNonzeroMobiusCarrier_squarefree_pos
    (lowOwnerStokesFracturedCoreCarrier_subset_nonzeroCarrier R hn)

end RHLean.Proof

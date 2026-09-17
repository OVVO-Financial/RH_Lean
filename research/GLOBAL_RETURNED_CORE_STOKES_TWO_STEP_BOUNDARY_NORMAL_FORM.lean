import Mathlib
import «research.GLOBAL_RETURNED_CORE_STOKES_TERMINAL_CLASSIFICATION»

/-!
# Two-step normal form of the final signed Stokes boundary

The terminal-classification theorem already proves that the first canonical
remaining owner lies above half the physical clock and that the complete
interior after the first two distinct owners is empty.

This file records the corresponding statement for the accumulated boundary,
not just the residual: once the second interior is empty, every later boundary
step is literally zero.  Hence a cell with at least two remaining owners has an
exact boundary consisting of only

  step(q) + 1/4 * step(s after q).

No estimate is introduced.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- An empty carrier produces no later Stokes boundary, for any remaining
schedule and scalar weight. -/
theorem iteratedPairWeightedStokesBoundary_empty :
    ∀ (ps : List ℕ) (f : ℕ × ℕ → ℝ),
      iteratedPairWeightedStokesBoundary ps ∅ f = 0 := by
  intro ps
  induction ps with
  | nil =>
      intro f
      simp [iteratedPairWeightedStokesBoundary]
  | cons q qs ih =>
      intro f
      simp [iteratedPairWeightedStokesBoundary,
        pairWeightedStokesBoundaryStep,
        pairPrimeLeftEscapePart, pairPrimeRightEscapeAfterLeft,
        pairPrimeLeftInteriorPart, weightedOthelloEscapePart,
        weightedOthelloInteriorPart, ih]

/-- **Exact two-step boundary normal form.**

If the canonical remaining-owner schedule begins `q,s`, then for `R ≥ 2` the
entire canonical cell boundary is the first boundary step plus one quarter of
the second boundary step.  Every later term is zero by exact carrier emptiness. -/
theorem lowOwnerFirstOwnerCanonicalStokesBoundary_eq_twoSteps_of_twoOwners
    {R p q s : ℕ} {sig : Finset ℕ} {rest : List ℕ}
    (hR : 2 ≤ R)
    (hps : lowOwnerFirstOwnerCanonicalStokesSchedule R p = q :: s :: rest) :
    lowOwnerFirstOwnerCanonicalStokesBoundary R p sig =
      pairWeightedStokesBoundaryStep q
        (lowOwnerFirstOwnerSignedCellPairCarrier R p sig)
        (lowOwnerFirstOwnerDirichletPolarizationScalar R p) +
      (1 / 4 : ℝ) *
        pairWeightedStokesBoundaryStep s
          (pairPrimeTwoCoordinateInterior q
            (lowOwnerFirstOwnerSignedCellPairCarrier R p sig))
          (pairPrimeMixedDifference q
            (lowOwnerFirstOwnerDirichletPolarizationScalar R p)) := by
  have hqMem : q ∈ lowOwnerFirstOwnerCanonicalStokesSchedule R p := by
    rw [hps]
    simp
  have hsMem : s ∈ lowOwnerFirstOwnerCanonicalStokesSchedule R p := by
    rw [hps]
    simp
  have hqPrime := lowOwnerFirstOwnerCanonicalStokesSchedule_prime R p q hqMem
  have hsPrime := lowOwnerFirstOwnerCanonicalStokesSchedule_prime R p s hsMem
  have hqTop :=
    lowOwnerFirstOwnerCanonicalStokesSchedule_head_gt_half
      hR (show lowOwnerFirstOwnerCanonicalStokesSchedule R p = q :: (s :: rest)
        from hps)
  have hqne := lowOwnerFirstOwnerCanonicalStokesSchedule_first_two_ne hps
  have hcarrier :=
    lowOwnerFirstOwner_twoPrimePairInterior_eq_empty_of_top
      (R := R) (p := p) (q := q) (s := s) (sig := sig)
      hqPrime hsPrime hqne hqTop
  unfold lowOwnerFirstOwnerCanonicalStokesBoundary
  rw [hps]
  simp only [iteratedPairWeightedStokesBoundary]
  rw [hcarrier, iteratedPairWeightedStokesBoundary_empty]
  ring

/-- The physically identified clip ledger has the same exact two-step form. -/
theorem lowOwnerFirstOwnerCanonicalStokesClipBoundary_eq_twoSteps_of_twoOwners
    {R p q s : ℕ} {sig : Finset ℕ} {rest : List ℕ}
    (hR : 2 ≤ R)
    (hps : lowOwnerFirstOwnerCanonicalStokesSchedule R p = q :: s :: rest) :
    lowOwnerFirstOwnerCanonicalStokesClipBoundary R p sig =
      pairWeightedStokesBoundaryStep q
        (lowOwnerFirstOwnerSignedCellPairCarrier R p sig)
        (lowOwnerFirstOwnerDirichletPolarizationScalar R p) +
      (1 / 4 : ℝ) *
        pairWeightedStokesBoundaryStep s
          (pairPrimeTwoCoordinateInterior q
            (lowOwnerFirstOwnerSignedCellPairCarrier R p sig))
          (pairPrimeMixedDifference q
            (lowOwnerFirstOwnerDirichletPolarizationScalar R p)) := by
  rw [← lowOwnerFirstOwnerCanonicalStokesBoundary_eq_clipBoundary]
  exact lowOwnerFirstOwnerCanonicalStokesBoundary_eq_twoSteps_of_twoOwners
    hR hps

/-- For two or more remaining owners the top-terminal contribution itself is
zero, so the full cell contribution is exactly the same two boundary steps. -/
theorem lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary_eq_zero_of_twoOwners
    {R p q s : ℕ} {sig : Finset ℕ} {rest : List ℕ}
    (hps : lowOwnerFirstOwnerCanonicalStokesSchedule R p = q :: s :: rest) :
    lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary R p sig = 0 := by
  simp [lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary, hps]

end RHLean.Proof

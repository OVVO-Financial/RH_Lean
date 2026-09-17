import Mathlib
import «research.GLOBAL_RETURNED_CORE_ITERATED_PAIR_STOKES»
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_POLARIZATION_OWNER_CUBE»

/-!
# Direct signed-cell bridge into the iterated Othello/Stokes telescope

This is the anti-cycle entry point.

The returned-core signed cell telescope is already exactly the sum of its
Dirichlet polarization atoms on the full p-free base square.  Each atom is
Möbius pair sign times a scalar polarization.  Therefore the cell telescope is
literally an instance of `pairWeightedStokesMass`, with no gate, square, norm,
or positive-energy carrier inserted in between.

Consequently, for any finite list of prime owner toggles,

  SignedCellTelescope = iterated signed boundary + terminal signed residual.

The boundary is made only of literal escape faces of the successive pair
involutions.  The residual is the fully iterated mixed finite difference on the
remaining complete interior.  This file introduces no inequality.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Scalar part of the Dirichlet polarization atom before the Möbius pair sign. -/
def lowOwnerFirstOwnerDirichletPolarizationScalar
    (R p : ℕ) (ab : ℕ × ℕ) : ℝ :=
  lowOwnerDirichletIncidenceCoefficient R p ab.1 *
      lowOwnerDirichletIncidenceCoefficient R p ab.2 -
    lowOwnerDirichletBaseCoefficient R ab.1 *
      lowOwnerDirichletBaseCoefficient R ab.2 -
    lowOwnerDirichletReturnedCoefficient R p ab.1 *
      lowOwnerDirichletReturnedCoefficient R p ab.2

/-- Full pair carrier of one first-owner/signature cell. -/
def lowOwnerFirstOwnerSignedCellPairCarrier
    (R p : ℕ) (sig : Finset ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerBaseFiber R p sig).product
    (lowOwnerFirstOwnerBaseFiber R p sig)

/-- **Exact anti-cycle bridge.**  The signed cell telescope itself, not an
inherited energy, is the weighted pair mass fed into Othello/Stokes. -/
theorem lowOwnerFirstOwnerSignedCellTelescope_eq_pairWeightedStokesMass
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerSignedCellTelescope R p sig =
      pairWeightedStokesMass
        (lowOwnerFirstOwnerSignedCellPairCarrier R p sig)
        (lowOwnerFirstOwnerDirichletPolarizationScalar R p) := by
  rw [lowOwnerFirstOwnerSignedCellTelescope_eq_sum_dirichletPolarizationAtoms hp]
  unfold lowOwnerFirstOwnerSignedCellPairCarrier pairWeightedStokesMass
  apply Finset.sum_congr rfl
  intro ab _hab
  rw [lowOwnerFirstOwnerDirichletPolarizationAtom_eq_scalar]
  unfold lowOwnerFirstOwnerDirichletPolarizationScalar
    othelloRealMoebiusPair othelloRealMoebius
    RHLean.Analysis.realMoebiusStep
  ring

/-- **Exact signed cell Stokes decomposition for an arbitrary prime schedule.**

This is the cell-level `D + B` theorem demanded by the signed-first route.
Nothing has been estimated: `iteratedPairWeightedStokesBoundary` is the literal
signed escape ledger and `iteratedPairWeightedStokesResidual` is the fully
transported signed interior. -/
theorem lowOwnerFirstOwnerSignedCellTelescope_eq_iteratedStokesBoundary_add_residual
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime)
    (ps : List ℕ) (hps : ∀ r ∈ ps, r.Prime) :
    lowOwnerFirstOwnerSignedCellTelescope R p sig =
      iteratedPairWeightedStokesBoundary ps
        (lowOwnerFirstOwnerSignedCellPairCarrier R p sig)
        (lowOwnerFirstOwnerDirichletPolarizationScalar R p) +
      iteratedPairWeightedStokesResidual ps
        (lowOwnerFirstOwnerSignedCellPairCarrier R p sig)
        (lowOwnerFirstOwnerDirichletPolarizationScalar R p) := by
  rw [lowOwnerFirstOwnerSignedCellTelescope_eq_pairWeightedStokesMass hp]
  exact pairWeightedStokesMass_eq_iteratedBoundary_add_residual
    ps hps
    (lowOwnerFirstOwnerSignedCellPairCarrier R p sig)
    (lowOwnerFirstOwnerDirichletPolarizationScalar R p)

end RHLean.Proof

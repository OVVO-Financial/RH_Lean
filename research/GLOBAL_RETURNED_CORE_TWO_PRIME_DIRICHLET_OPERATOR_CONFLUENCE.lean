import Mathlib
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_POLARIZATION_OWNER_CUBE»

/-!
# Two-prime Dirichlet operator confluence

The completed polarization already uses one common Dirichlet zero extension on
its base, returned-child, and incidence coordinates.  Hence the signed part of
the local-confluence problem is an abelian finite-difference identity.

For

  Delta_r f(n) = f(n) - f(r*n),

distinctness is not even needed:

  Delta_s (Delta_r f) = Delta_r (Delta_s f).

Applying this identity independently to the three polarization coordinates
`d`, `ell`, and `j` proves that the full two-owner Dirichlet polarization scalar
is independent of reveal order.  Clipped Excess is not discarded here: it is
encoded by the returned-child coordinate becoming zero while the physical base
coordinate remains live.  Outside is the separate case in which the common
Dirichlet extension vanishes.
-/

noncomputable section

namespace RHLean.Proof

/-- Two multiplicative Dirichlet owner differences commute exactly. -/
theorem lowOwnerDirichletOwnerDifference_comm
    (r s : ℕ) (f : ℕ → ℝ) (n : ℕ) :
    lowOwnerDirichletOwnerDifference s
        (fun m => lowOwnerDirichletOwnerDifference r f m) n =
      lowOwnerDirichletOwnerDifference r
        (fun m => lowOwnerDirichletOwnerDifference s f m) n := by
  unfold lowOwnerDirichletOwnerDifference
  have hmul : r * (s * n) = s * (r * n) := by ring
  rw [hmul]
  ring

/-- The completed two-owner scalar difference. -/
def lowOwnerDirichletTwoOwnerDifference
    (r s : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  lowOwnerDirichletOwnerDifference s
    (fun m => lowOwnerDirichletOwnerDifference r f m) n

@[simp] theorem lowOwnerDirichletTwoOwnerDifference_comm
    (r s : ℕ) (f : ℕ → ℝ) (n : ℕ) :
    lowOwnerDirichletTwoOwnerDifference r s f n =
      lowOwnerDirichletTwoOwnerDifference s r f n := by
  unfold lowOwnerDirichletTwoOwnerDifference
  exact lowOwnerDirichletOwnerDifference_comm r s f n

/-- Polarization scalar after two owner reveals on the completed Dirichlet
carrier. -/
def lowOwnerDirichletTwoOwnerPolarizationScalar
    (R p r s a b : ℕ) : ℝ :=
  lowOwnerDirichletTwoOwnerDifference r s
      (lowOwnerDirichletIncidenceCoefficient R p) a *
    lowOwnerDirichletTwoOwnerDifference r s
      (lowOwnerDirichletIncidenceCoefficient R p) b -
  lowOwnerDirichletTwoOwnerDifference r s
      (lowOwnerDirichletBaseCoefficient R) a *
    lowOwnerDirichletTwoOwnerDifference r s
      (lowOwnerDirichletBaseCoefficient R) b -
  lowOwnerDirichletTwoOwnerDifference r s
      (lowOwnerDirichletReturnedCoefficient R p) a *
    lowOwnerDirichletTwoOwnerDifference r s
      (lowOwnerDirichletReturnedCoefficient R p) b

/-- **Signed two-prime Dirichlet diamond.**  The complete polarization scalar is
literally independent of the order in which the two owner coordinates are
revealed. -/
theorem lowOwnerDirichletTwoOwnerPolarizationScalar_comm
    (R p r s a b : ℕ) :
    lowOwnerDirichletTwoOwnerPolarizationScalar R p r s a b =
      lowOwnerDirichletTwoOwnerPolarizationScalar R p s r a b := by
  unfold lowOwnerDirichletTwoOwnerPolarizationScalar
  rw [lowOwnerDirichletTwoOwnerDifference_comm r s
        (lowOwnerDirichletIncidenceCoefficient R p) a,
      lowOwnerDirichletTwoOwnerDifference_comm r s
        (lowOwnerDirichletIncidenceCoefficient R p) b,
      lowOwnerDirichletTwoOwnerDifference_comm r s
        (lowOwnerDirichletBaseCoefficient R) a,
      lowOwnerDirichletTwoOwnerDifference_comm r s
        (lowOwnerDirichletBaseCoefficient R) b,
      lowOwnerDirichletTwoOwnerDifference_comm r s
        (lowOwnerDirichletReturnedCoefficient R p) a,
      lowOwnerDirichletTwoOwnerDifference_comm r s
        (lowOwnerDirichletReturnedCoefficient R p) b]

end RHLean.Proof

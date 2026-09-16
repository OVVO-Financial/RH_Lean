import Mathlib
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_PAIR_POLARIZATION»

/-!
# Fresh-owner cube closure of the Dirichlet polarization

The induction state is the signed polarization atom itself.  It is closed under
revealing any fresh prime coordinate.

Write scalar Dirichlet coefficients

  ell(n) = wD(n),
  j_p(n) = wD(p*n),
  d_p(n) = ell(n) - j_p(n).

Then

  Pi_p(a,b) = mu(a)mu(b)
    [d_p(a)d_p(b) - ell(a)ell(b) - j_p(a)j_p(b)].

For a fresh prime r the complete r-square of `Pi_p` is exactly

  mu(a)mu(b)
    [Delta_r d_p(a) Delta_r d_p(b)
      - Delta_r ell(a) Delta_r ell(b)
      - Delta_r j_p(a) Delta_r j_p(b)].

Thus the polarization form reproduces itself after one owner reveal.  Equally,
the sum of the two mixed r-children is the next polarization minus the parent
and double child.  The latter two have r removed from their fresh set, so this
is the exact rank-dropping telescope used by the unique-owner assembly.

All three scalar coordinates now use the same Dirichlet zero extension, so the
identity remains valid even when one or more child corners leave the physical
clock.  No boundary norm is introduced.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Scalar base coefficient, before the Mobius sign. -/
def lowOwnerDirichletBaseCoefficient (R n : ℕ) : ℝ :=
  lowOwnerPhysicalDirichletWeight R n

/-- Scalar returned p-child coefficient, before the Mobius sign. -/
def lowOwnerDirichletReturnedCoefficient (R p n : ℕ) : ℝ :=
  lowOwnerPhysicalDirichletWeight R (p * n)

/-- Scalar p-incidence coefficient. -/
def lowOwnerDirichletIncidenceCoefficient (R p n : ℕ) : ℝ :=
  lowOwnerDirichletBaseCoefficient R n -
    lowOwnerDirichletReturnedCoefficient R p n

/-- One multiplicative r-difference of a scalar coefficient. -/
def lowOwnerDirichletOwnerDifference
    (r : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  f n - f (r * n)

/-- Polarization scalar after one r-difference has been applied to all three
p-coordinates. -/
def lowOwnerDirichletNextPolarizationScalar
    (R p r a b : ℕ) : ℝ :=
  lowOwnerDirichletOwnerDifference r
      (lowOwnerDirichletIncidenceCoefficient R p) a *
    lowOwnerDirichletOwnerDifference r
      (lowOwnerDirichletIncidenceCoefficient R p) b -
  lowOwnerDirichletOwnerDifference r
      (lowOwnerDirichletBaseCoefficient R) a *
    lowOwnerDirichletOwnerDifference r
      (lowOwnerDirichletBaseCoefficient R) b -
  lowOwnerDirichletOwnerDifference r
      (lowOwnerDirichletReturnedCoefficient R p) a *
    lowOwnerDirichletOwnerDifference r
      (lowOwnerDirichletReturnedCoefficient R p) b

/-- The pointwise pair atom is exactly Mobius pair weight times its scalar
polarization. -/
theorem lowOwnerFirstOwnerDirichletPolarizationAtom_eq_scalar
    (R p a b : ℕ) :
    lowOwnerFirstOwnerDirichletPolarizationAtom R p (a, b) =
      realMoebiusStep a * realMoebiusStep b *
        (lowOwnerDirichletIncidenceCoefficient R p a *
            lowOwnerDirichletIncidenceCoefficient R p b -
          lowOwnerDirichletBaseCoefficient R a *
            lowOwnerDirichletBaseCoefficient R b -
          lowOwnerDirichletReturnedCoefficient R p a *
            lowOwnerDirichletReturnedCoefficient R p b) := by
  unfold lowOwnerFirstOwnerDirichletPolarizationAtom
    lowOwnerFirstOwnerDirichletIncidenceSite
    lowOwnerFirstOwnerDirichletBaseSite
    lowOwnerFirstOwnerDirichletReturnedChildSite
    lowOwnerDirichletIncidenceCoefficient
    lowOwnerDirichletBaseCoefficient
    lowOwnerDirichletReturnedCoefficient
    lowOwnerPhysicalDirichletIncidenceWeight
  ring

/-- **Fresh-owner cube closure.** -/
theorem lowOwnerDirichletPolarization_fourCorner_eq_nextPolarization
    {R p r a b : ℕ}
    (hr : r.Prime) (hra : ¬ r ∣ a) (hrb : ¬ r ∣ b) :
    lowOwnerFirstOwnerDirichletPolarizationAtom R p (a, b) +
      lowOwnerFirstOwnerDirichletPolarizationAtom R p (r * a, b) +
      lowOwnerFirstOwnerDirichletPolarizationAtom R p (a, r * b) +
      lowOwnerFirstOwnerDirichletPolarizationAtom R p (r * a, r * b) =
      realMoebiusStep a * realMoebiusStep b *
        lowOwnerDirichletNextPolarizationScalar R p r a b := by
  rw [lowOwnerFirstOwnerDirichletPolarizationAtom_eq_scalar,
    lowOwnerFirstOwnerDirichletPolarizationAtom_eq_scalar,
    lowOwnerFirstOwnerDirichletPolarizationAtom_eq_scalar,
    lowOwnerFirstOwnerDirichletPolarizationAtom_eq_scalar]
  rw [realMoebiusStep_mul_prime_eq_neg hr hra,
    realMoebiusStep_mul_prime_eq_neg hr hrb]
  unfold lowOwnerDirichletNextPolarizationScalar
    lowOwnerDirichletOwnerDifference
  ring

/-- **Mixed-child rank telescope.**  The two r-mixed children are next-owner
polarization minus the same-branch parent and double child. -/
theorem lowOwnerDirichletPolarization_mixedChildren_eq_next_sub_sameBranches
    {R p r a b : ℕ}
    (hr : r.Prime) (hra : ¬ r ∣ a) (hrb : ¬ r ∣ b) :
    lowOwnerFirstOwnerDirichletPolarizationAtom R p (r * a, b) +
        lowOwnerFirstOwnerDirichletPolarizationAtom R p (a, r * b) =
      realMoebiusStep a * realMoebiusStep b *
          lowOwnerDirichletNextPolarizationScalar R p r a b -
        lowOwnerFirstOwnerDirichletPolarizationAtom R p (a, b) -
        lowOwnerFirstOwnerDirichletPolarizationAtom R p (r * a, r * b) := by
  have h := lowOwnerDirichletPolarization_fourCorner_eq_nextPolarization
    (R := R) (p := p) hr hra hrb
  linear_combination h

/-- The next polarization is again purely mixed: the incidence difference is
the base difference minus the returned-child difference. -/
theorem lowOwnerDirichletNextPolarizationScalar_eq_mixed
    (R p r a b : ℕ) :
    lowOwnerDirichletNextPolarizationScalar R p r a b =
      -(lowOwnerDirichletOwnerDifference r
          (lowOwnerDirichletBaseCoefficient R) a *
        lowOwnerDirichletOwnerDifference r
          (lowOwnerDirichletReturnedCoefficient R p) b) -
      lowOwnerDirichletOwnerDifference r
          (lowOwnerDirichletReturnedCoefficient R p) a *
        lowOwnerDirichletOwnerDifference r
          (lowOwnerDirichletBaseCoefficient R) b := by
  unfold lowOwnerDirichletNextPolarizationScalar
    lowOwnerDirichletOwnerDifference
    lowOwnerDirichletIncidenceCoefficient
    lowOwnerDirichletBaseCoefficient
    lowOwnerDirichletReturnedCoefficient
  ring

end RHLean.Proof

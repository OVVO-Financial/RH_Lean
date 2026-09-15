import Mathlib
import «research.STABLE_FAR_OWNER_FIRST_COLLAPSE»

/-!
# Owner-first child plus crossing reassembly

At fixed low owner `q` and fixed far prime `p`, the q^2 child-far cofactors are
the lower q-smooth prefix

  d <= X_R / (q^2 p),

while the strict-crossing cofactors are exactly the complementary window up to

  d <= X_R / (q p).

Thus the completed q^2 children and the returned strict crossings must be
reassembled before any norm: together they are one predecessor-prime prefix at
the first-contact cutoff.  This is the owner-first form needed by the amplitude
transport, because the far-prime coordinate `p` is retained throughout.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Lower q^2 child cofactor fibre at fixed old owner `q` and far prime `p`. -/
def stableFarOldOwnerChildCofactors (R q p : ℕ) : Finset ℕ :=
  squareRootLowPrimeGoSmoothCofactors q
    (squareRootEndpoint R / (q * q * p))

/-- Signed lower-child mass at fixed `(q,p)`. -/
def stableFarOldOwnerChildCofactorMass (R q p : ℕ) : ℤ :=
  ∑ d ∈ stableFarOldOwnerChildCofactors R q p, μ d

/-- The lower child is literally the frozen predecessor-prime prefix at the
q^2 cutoff. -/
theorem stableFarOldOwnerChildCofactorMass_eq_predecessorPrefix
    {R q p : ℕ} (hq : q.Prime) :
    stableFarOldOwnerChildCofactorMass R q p =
      frozenPrimeUniverseMass (primesUpTo (q - 1))
        (squareRootEndpoint R / (q * q * p)) := by
  unfold stableFarOldOwnerChildCofactorMass stableFarOldOwnerChildCofactors
  symm
  exact frozenPrimeUniverseMass_eq_goSmoothCofactorSum
    (r := q) (Y := squareRootEndpoint R / (q * q * p)) hq

/-- **Owner-first signed reassembly.**  The q^2 child prefix plus its strict
crossing renewal window is exactly the whole q-predecessor prefix at the
first-contact cutoff `X_R/(q*p)`.  No multiplicity or norm remains. -/
theorem stableFarOldOwnerChild_add_crossing_eq_predecessorParent
    {R q p : ℕ} (hq : q.Prime) (hp : p.Prime) :
    stableFarOldOwnerChildCofactorMass R q p +
        stableFarOldOwnerCrossingCofactorMass R q p =
      frozenPrimeUniverseMass (primesUpTo (q - 1))
        (squareRootEndpoint R / (q * p)) := by
  have hsub := stableFarOldOwnerCrossingCofactors_lower_subset_upper
    (R := R) (q := q) (p := p) hq hp
  have hsum := Finset.sum_sdiff hsub (f := fun d => μ d)
  have hUpper := frozenPrimeUniverseMass_eq_goSmoothCofactorSum
    (r := q) (Y := squareRootEndpoint R / (q * p)) hq
  unfold stableFarOldOwnerChildCofactorMass stableFarOldOwnerChildCofactors
    stableFarOldOwnerCrossingCofactorMass stableFarOldOwnerCrossingCofactors
  rw [hUpper, add_comm]
  exact hsum

/-- Equivalent Euler-step form: the crossing window alone advances the
predecessor prefix from the q^2 cutoff to the admitted-q prefix. -/
theorem stableFarOldOwnerCrossing_eq_predecessorParent_sub_child
    {R q p : ℕ} (hq : q.Prime) (hp : p.Prime) :
    stableFarOldOwnerCrossingCofactorMass R q p =
      frozenPrimeUniverseMass (primesUpTo (q - 1))
          (squareRootEndpoint R / (q * p)) -
        stableFarOldOwnerChildCofactorMass R q p := by
  have h := stableFarOldOwnerChild_add_crossing_eq_predecessorParent
    (R := R) (q := q) (p := p) hq hp
  omega

end RHLean.Proof

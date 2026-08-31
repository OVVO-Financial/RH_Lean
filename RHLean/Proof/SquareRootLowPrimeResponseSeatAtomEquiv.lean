import Mathlib
import RHLean.Proof.SquareRootLowPrimeResponseSeatCarrier
import RHLean.Proof.SquareRootLowPrimeDeepResponseAtoms

/-!
# Response seats are literal prime partners

Beyond the shallow cutoff, `CombinedFreshResponse(R,K,j,c)` is exactly the
cardinality of `DeepPartnerSet(R,c)`. Hence the abstract unit-seat coordinate
used by the canonical creation-response map is the increasing enumeration of
the literal born/post-root prime partners already used by the response forest.

The equivalence below is canonical: seat `s` is sent to the `s`-th element of
`DeepPartnerSet(R,c)` in the natural prime order.  No arbitrary
`Finset.equivOfCardEq`, estimate, or analytic input is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Natural seat indices over one deep response cofactor. -/
def squareRootLowPrimeResponseSeatIndexSet
    (R K j c : ℕ) : Finset ℕ :=
  Finset.range (squareRootLowPrimeCombinedFreshResponse R K j c)

@[simp] theorem mem_squareRootLowPrimeResponseSeatIndexSet
    {R K j c s : ℕ} :
    s ∈ squareRootLowPrimeResponseSeatIndexSet R K j c ↔
      s < squareRootLowPrimeCombinedFreshResponse R K j c := by
  simp [squareRootLowPrimeResponseSeatIndexSet]

/-- **Canonical seat/partner equivalence on one deep cofactor fibre.**
Seat `s` is the `s`-th actual deep partner in increasing order. -/
noncomputable def squareRootLowPrimeResponseSeatPartnerEquiv
    (R K j c : ℕ) (hR : 1 ≤ R) (hc : 0 < c) (hKc : K < c) :
    ↥(squareRootLowPrimeResponseSeatIndexSet R K j c) ≃
      ↥(squareRootLowPrimeDeepPartnerSet R c) := by
  let hcard :
      (squareRootLowPrimeDeepPartnerSet R c).card =
        squareRootLowPrimeCombinedFreshResponse R K j c :=
    card_squareRootLowPrimeDeepPartnerSet_eq_combinedFreshResponse hR hc hKc
  let e :
      Fin (squareRootLowPrimeCombinedFreshResponse R K j c) ≃o
        ↥(squareRootLowPrimeDeepPartnerSet R c) :=
    (squareRootLowPrimeDeepPartnerSet R c).orderIsoOfFin hcard
  refine
    { toFun := fun s => e ⟨s.1, by
        simpa [squareRootLowPrimeResponseSeatIndexSet] using s.2⟩
      invFun := fun q =>
        ⟨((e.symm q : Fin
          (squareRootLowPrimeCombinedFreshResponse R K j c)) : ℕ), by
          simpa [squareRootLowPrimeResponseSeatIndexSet] using
            (e.symm q : Fin
              (squareRootLowPrimeCombinedFreshResponse R K j c)).2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro s
    apply Subtype.ext
    exact congrArg Fin.val (e.left_inv ⟨s.1, by
      simpa [squareRootLowPrimeResponseSeatIndexSet] using s.2⟩)
  · intro q
    exact e.right_inv q

/-- The chosen partner of a valid seat is genuinely in the deep partner set. -/
theorem squareRootLowPrimeResponseSeatPartnerEquiv_mem
    (R K j c : ℕ) (hR : 1 ≤ R) (hc : 0 < c) (hKc : K < c)
    (s : ↥(squareRootLowPrimeResponseSeatIndexSet R K j c)) :
    (squareRootLowPrimeResponseSeatPartnerEquiv R K j c hR hc hKc s : ℕ) ∈
      squareRootLowPrimeDeepPartnerSet R c :=
  (squareRootLowPrimeResponseSeatPartnerEquiv R K j c hR hc hKc s).property

/-- Every literal deep partner is represented by exactly one response seat. -/
theorem squareRootLowPrimeResponseSeatPartnerEquiv_surjective
    (R K j c : ℕ) (hR : 1 ≤ R) (hc : 0 < c) (hKc : K < c)
    (q : ↥(squareRootLowPrimeDeepPartnerSet R c)) :
    ∃ s : ↥(squareRootLowPrimeResponseSeatIndexSet R K j c),
      squareRootLowPrimeResponseSeatPartnerEquiv R K j c hR hc hKc s = q := by
  exact (squareRootLowPrimeResponseSeatPartnerEquiv
    R K j c hR hc hKc).surjective q

end RHLean.Proof
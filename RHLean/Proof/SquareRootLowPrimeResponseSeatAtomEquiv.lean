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

/-- Membership in the global response-seat carrier is exactly signed-cofactor
membership together with a valid absolute seat index. -/
@[simp] theorem mem_squareRootLowPrimeOwnedResponseSeatCarrier_iff
    {R K j U : ℕ} {z : ℕ × ℕ} :
    z ∈ squareRootLowPrimeOwnedResponseSeatCarrier R K j U ↔
      z.1 ∈ squareRootLowPrimeOwnedSignedCofactors R K U ∧
        z.2 < squareRootLowPrimeCombinedFreshResponse R K j z.1 := by
  unfold squareRootLowPrimeOwnedResponseSeatCarrier
  constructor
  · intro hz
    rcases Finset.mem_biUnion.mp hz with ⟨c, hc, hzc⟩
    have hdata := mem_squareRootLowPrimeCombinedSeatFiber.mp hzc
    rw [hdata.1]
    exact ⟨hc, hdata.2⟩
  · rintro ⟨hc, hs⟩
    exact Finset.mem_biUnion.mpr
      ⟨z.1, hc, mem_squareRootLowPrimeCombinedSeatFiber.mpr ⟨rfl, hs⟩⟩

/-- **Global canonical response-seat/atom equivalence.**  It preserves the
cofactor and replaces the abstract absolute seat by the corresponding actual
partner prime in increasing order. -/
noncomputable def squareRootLowPrimeOwnedResponseSeatAtomEquiv
    (R K j U : ℕ) (hR : 1 ≤ R) :
    ↥(squareRootLowPrimeOwnedResponseSeatCarrier R K j U) ≃
      ↥(squareRootLowPrimeOwnedResponseAtoms R K U) where
  toFun z := by
    have hz := mem_squareRootLowPrimeOwnedResponseSeatCarrier_iff.mp z.2
    have hcData := squareRootLowPrimeOwnedSignedCofactor_data hz.1
    let s : ↥(squareRootLowPrimeResponseSeatIndexSet R K j z.1.1) :=
      ⟨z.1.2, by
        simpa [squareRootLowPrimeResponseSeatIndexSet] using hz.2⟩
    let q := squareRootLowPrimeResponseSeatPartnerEquiv
      R K j z.1.1 hR hcData.1 hcData.2.1 s
    exact ⟨(z.1.1, (q : ℕ)),
      mem_squareRootLowPrimeOwnedResponseAtoms_iff.mpr ⟨hz.1, q.2⟩⟩
  invFun z := by
    have hz := mem_squareRootLowPrimeOwnedResponseAtoms_iff.mp z.2
    have hcData := squareRootLowPrimeOwnedSignedCofactor_data hz.1
    let q : ↥(squareRootLowPrimeDeepPartnerSet R z.1.1) := ⟨z.1.2, hz.2⟩
    let s := (squareRootLowPrimeResponseSeatPartnerEquiv
      R K j z.1.1 hR hcData.1 hcData.2.1).symm q
    exact ⟨(z.1.1, (s : ℕ)),
      mem_squareRootLowPrimeOwnedResponseSeatCarrier_iff.mpr
        ⟨hz.1, by
          simpa [squareRootLowPrimeResponseSeatIndexSet] using s.2⟩⟩
  left_inv := by
    intro z
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hz := mem_squareRootLowPrimeOwnedResponseSeatCarrier_iff.mp z.2
      have hcData := squareRootLowPrimeOwnedSignedCofactor_data hz.1
      let s : ↥(squareRootLowPrimeResponseSeatIndexSet R K j z.1.1) :=
        ⟨z.1.2, by
          simpa [squareRootLowPrimeResponseSeatIndexSet] using hz.2⟩
      exact congrArg Subtype.val
        ((squareRootLowPrimeResponseSeatPartnerEquiv
          R K j z.1.1 hR hcData.1 hcData.2.1).left_inv s)
  right_inv := by
    intro z
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hz := mem_squareRootLowPrimeOwnedResponseAtoms_iff.mp z.2
      have hcData := squareRootLowPrimeOwnedSignedCofactor_data hz.1
      let q : ↥(squareRootLowPrimeDeepPartnerSet R z.1.1) := ⟨z.1.2, hz.2⟩
      exact congrArg Subtype.val
        ((squareRootLowPrimeResponseSeatPartnerEquiv
          R K j z.1.1 hR hcData.1 hcData.2.1).right_inv q)

@[simp] theorem squareRootLowPrimeOwnedResponseSeatAtomEquiv_fst
    (R K j U : ℕ) (hR : 1 ≤ R)
    (z : ↥(squareRootLowPrimeOwnedResponseSeatCarrier R K j U)) :
    (squareRootLowPrimeOwnedResponseSeatAtomEquiv R K j U hR z : ℕ × ℕ).1 =
      z.1.1 := by
  rfl

end RHLean.Proof
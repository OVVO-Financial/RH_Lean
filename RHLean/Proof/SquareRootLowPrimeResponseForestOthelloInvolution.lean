import Mathlib
import RHLean.Proof.CreationResponseOthelloInvolution
import RHLean.Proof.SquareRootLowPrimeResponseForest

/-!
# Response forest as a finite Othello involution

Internal born response atoms are paired with their arithmetic child cofactors.
The child map is injective and reverses the Mobius orientation.  Completing the
partial matching by fixed points gives a genuine involution whose stable set is
exactly the born exit, post-root, and response-root boundary.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Tagged atom/cofactor universe of the response forest. -/
def squareRootLowPrimeResponseForestOthelloCarrier
    (R K U : ℕ) : Finset (Sum (ℕ × ℕ) ℕ) :=
  creationResponseOthelloCarrier
    (squareRootLowPrimeOwnedResponseAtoms R K U)
    (squareRootLowPrimeOwnedResponseCofactors R K U)

/-- Atom side carries the negative child weight; cofactor side its native weight. -/
def squareRootLowPrimeResponseForestOthelloWeight : Sum (ℕ × ℕ) ℕ → ℤ
  | .inl z => -μ (squareRootLowPrimeBadAtomChild z)
  | .inr c => μ c

/-- Internal-born atom to its unique arithmetic child cofactor. -/
def squareRootLowPrimeResponseForestOthelloMate
    (R K U : ℕ) : Sum (ℕ × ℕ) ℕ → Sum (ℕ × ℕ) ℕ :=
  creationResponseOthelloMate
    (squareRootLowPrimeBornInternalAtoms R K U)
    squareRootLowPrimeBadAtomChild

/-- The response-forest mate preserves its complete tagged carrier. -/
theorem squareRootLowPrimeResponseForestOthelloMate_mem
    {R K U : ℕ} (hUR : U < R)
    {x : Sum (ℕ × ℕ) ℕ}
    (hx : x ∈ squareRootLowPrimeResponseForestOthelloCarrier R K U) :
    squareRootLowPrimeResponseForestOthelloMate R K U x ∈
      squareRootLowPrimeResponseForestOthelloCarrier R K U := by
  unfold squareRootLowPrimeResponseForestOthelloCarrier
    squareRootLowPrimeResponseForestOthelloMate
  apply creationResponseOthelloMate_mem
    (squareRootLowPrimeOwnedResponseAtoms R K U)
    (squareRootLowPrimeBornInternalAtoms R K U)
    (squareRootLowPrimeOwnedResponseCofactors R K U)
    squareRootLowPrimeBadAtomChild
  · intro z hz
    exact (mem_squareRootLowPrimeBornInternalAtoms.mp hz).1
  · intro z hz
    exact squareRootLowPrimeBornInternalChildren_subset_ownedResponseCofactors
      hUR (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
  · exact hx

/-- The response-forest mate is involutive. -/
theorem squareRootLowPrimeResponseForestOthelloMate_involutive
    {R K U : ℕ} (hUR : U < R) (x : Sum (ℕ × ℕ) ℕ) :
    squareRootLowPrimeResponseForestOthelloMate R K U
        (squareRootLowPrimeResponseForestOthelloMate R K U x) = x := by
  unfold squareRootLowPrimeResponseForestOthelloMate
  exact creationResponseOthelloMate_involutive
    (squareRootLowPrimeBornInternalAtoms R K U)
    squareRootLowPrimeBadAtomChild
    (squareRootLowPrimeBadAtomChild_injOn_bornInternalAtoms hUR) x

/-- Every moved response-forest edge reverses the tagged integer weight. -/
theorem squareRootLowPrimeResponseForestOthelloMate_weight_neg
    {R K U : ℕ} (hUR : U < R)
    (x : Sum (ℕ × ℕ) ℕ)
    (hne : squareRootLowPrimeResponseForestOthelloMate R K U x ≠ x) :
    squareRootLowPrimeResponseForestOthelloWeight
        (squareRootLowPrimeResponseForestOthelloMate R K U x) =
      -squareRootLowPrimeResponseForestOthelloWeight x := by
  unfold squareRootLowPrimeResponseForestOthelloMate
    squareRootLowPrimeResponseForestOthelloWeight
  apply creationResponseOthelloMate_weight_neg
    (squareRootLowPrimeBornInternalAtoms R K U)
    squareRootLowPrimeBadAtomChild
    (fun z => -μ (squareRootLowPrimeBadAtomChild z))
    (fun c => μ c)
    (squareRootLowPrimeBadAtomChild_injOn_bornInternalAtoms hUR)
  · intro z _hz
    simp
  · exact hne

/-- Explicit stable boundary of the response forest. -/
def squareRootLowPrimeResponseForestOthelloBoundary
    (R K U : ℕ) : Finset (Sum (ℕ × ℕ) ℕ) :=
  ((squareRootLowPrimeBornFrontierAtoms R K U ∪
      squareRootLowPrimePostRootResponseAtoms R K U).map
        ⟨Sum.inl, Sum.inl_injective⟩) ∪
    (squareRootLowPrimeResponseRootCofactors R K U).map
      ⟨Sum.inr, Sum.inr_injective⟩

private theorem squareRootLowPrimeOwnedResponseAtoms_sdiff_internal_eq_boundaryAtoms
    (R K U : ℕ) :
    squareRootLowPrimeOwnedResponseAtoms R K U \
        squareRootLowPrimeBornInternalAtoms R K U =
      squareRootLowPrimeBornFrontierAtoms R K U ∪
        squareRootLowPrimePostRootResponseAtoms R K U := by
  ext z
  constructor
  · intro hz
    rcases Finset.mem_sdiff.mp hz with ⟨hzOwned, hzNotInternal⟩
    rw [squareRootLowPrimeOwnedResponseAtoms_eq_born_union_postRoot] at hzOwned
    rcases Finset.mem_union.mp hzOwned with hzBorn | hzPost
    · rw [squareRootLowPrimeBornResponseAtoms_eq_internal_union_frontier]
        at hzBorn
      rcases Finset.mem_union.mp hzBorn with hzInternal | hzFront
      · exact (hzNotInternal hzInternal).elim
      · exact Finset.mem_union.mpr (Or.inl hzFront)
    · exact Finset.mem_union.mpr (Or.inr hzPost)
  · intro hz
    rcases Finset.mem_union.mp hz with hzFront | hzPost
    · have hzBorn := (mem_squareRootLowPrimeBornFrontierAtoms.mp hzFront)
      apply Finset.mem_sdiff.mpr
      constructor
      · exact hzBorn.1
      · exact (Finset.disjoint_left.mp
          (squareRootLowPrimeBornInternalAtoms_disjoint_frontier R K U))
          |>.2 hzFront
    · apply Finset.mem_sdiff.mpr
      constructor
      · rw [squareRootLowPrimeOwnedResponseAtoms_eq_born_union_postRoot]
        exact Finset.mem_union.mpr (Or.inr hzPost)
      · intro hzInternal
        have hzBorn : z ∈ squareRootLowPrimeBornResponseAtoms R K U :=
          (mem_squareRootLowPrimeBornInternalAtoms.mp hzInternal).1 |> fun h =>
            mem_squareRootLowPrimeBornResponseAtoms.mpr
              ⟨h, (mem_squareRootLowPrimeBornInternalAtoms.mp hzInternal).2.1⟩
        exact (Finset.disjoint_left.mp
          (squareRootLowPrimeBornResponseAtoms_disjoint_postRoot R K U))
          hzBorn hzPost

/-- The stable set is exactly the three explicit arithmetic endpoint classes. -/
theorem finiteOthelloStablePart_responseForest_eq_boundary
    {R K U : ℕ} (hUR : U < R) :
    finiteOthelloStablePart
        (squareRootLowPrimeResponseForestOthelloCarrier R K U)
        (squareRootLowPrimeResponseForestOthelloMate R K U) =
      squareRootLowPrimeResponseForestOthelloBoundary R K U := by
  unfold squareRootLowPrimeResponseForestOthelloCarrier
    squareRootLowPrimeResponseForestOthelloMate
  rw [finiteOthelloStablePart_creationResponse_eq_frontier
    (squareRootLowPrimeOwnedResponseAtoms R K U)
    (squareRootLowPrimeBornInternalAtoms R K U)
    (squareRootLowPrimeOwnedResponseCofactors R K U)
    squareRootLowPrimeBadAtomChild]
  · unfold squareRootLowPrimeResponseForestOthelloBoundary
      creationResponseTaggedFrontier
      creationResponseMatchedImage
      squareRootLowPrimeResponseRootCofactors
    rw [squareRootLowPrimeOwnedResponseAtoms_sdiff_internal_eq_boundaryAtoms]
    rfl
  · intro z hz
    exact (mem_squareRootLowPrimeBornInternalAtoms.mp hz).1
  · exact squareRootLowPrimeBadAtomChild_injOn_bornInternalAtoms hUR

/-- The complete tagged mass equals the signed mass of the stable boundary. -/
theorem squareRootLowPrimeResponseForestOthello_mass_eq_boundary
    {R K U : ℕ} (hUR : U < R) :
    (∑ x ∈ squareRootLowPrimeResponseForestOthelloCarrier R K U,
        squareRootLowPrimeResponseForestOthelloWeight x) =
      ∑ x ∈ squareRootLowPrimeResponseForestOthelloBoundary R K U,
        squareRootLowPrimeResponseForestOthelloWeight x := by
  rw [← finiteOthelloStablePart_responseForest_eq_boundary hUR]
  exact sum_finiteOthelloRegion_eq_stable
    (squareRootLowPrimeResponseForestOthelloCarrier R K U)
    (squareRootLowPrimeResponseForestOthelloMate R K U)
    squareRootLowPrimeResponseForestOthelloWeight
    (fun x hx => squareRootLowPrimeResponseForestOthelloMate_mem hUR hx)
    (fun x _hx => squareRootLowPrimeResponseForestOthelloMate_involutive hUR x)
    (fun x _hx hne =>
      squareRootLowPrimeResponseForestOthelloMate_weight_neg hUR x hne)

end RHLean.Proof

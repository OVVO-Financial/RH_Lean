import Mathlib
import RHLean.Proof.SquareWheelSurvivorProcessedResponseBridge

/-!
# Survivor owner-window residual and degree-of-freedom reduction

The physical survivor/processed-response bridge identifies the matched survivor
atoms whose canonical cofactor owner lies in the processed window `(K,U]`.
This file records what is left, before taking any norm.

For the endpoint survivor carrier `S` write

`S = D ⊔ W ⊔ P`,

where

* `D` is the processed-compatible matched sector `K < P+(c) <= U`;
* `W` is the matched owner-window residual `P+(c) <= K` or `U < P+(c)`;
* `P` is the complementary positive orientation `c < q <= R`.

The owner residual itself splits as

`W = W_shallow ⊔ W_above`

when `K <= U`.  Consequently the signed mass of the positive orientation is a
dependent coordinate:

`mass(P) = mass(S) - mass(D) - mass(W)`.

Equivalently, after splitting `W`,

`mass(P) = mass(S) - mass(D) - mass(W_shallow) - mass(W_above)`.

Thus a later proof need not construct a separate positive-orientation carrier
bridge merely to identify its signed mass.  No estimate or norm is used here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Matched survivor atoms whose cofactor owner is at or below the packet depth. -/
noncomputable def squareWheelSurvivorShallowMatchedPairSet
    (R K : ℕ) : Finset (ℕ × ℕ) :=
  (squareWheelSurvivorEndpointMatchedPairSet R).filter fun cq =>
    canonicalLargestPrimeFactor cq.1 ≤ K

/-- Matched survivor atoms whose cofactor owner lies strictly above cutoff `U`. -/
noncomputable def squareWheelSurvivorAboveCutoffMatchedPairSet
    (R U : ℕ) : Finset (ℕ × ℕ) :=
  (squareWheelSurvivorEndpointMatchedPairSet R).filter fun cq =>
    U < canonicalLargestPrimeFactor cq.1

/-- The matched survivor atoms not represented by the processed deep owner
window `(K,U]`. -/
noncomputable def squareWheelSurvivorOwnerResidualPairSet
    (R K U : ℕ) : Finset (ℕ × ℕ) :=
  (squareWheelSurvivorEndpointMatchedPairSet R).filter fun cq =>
    canonicalLargestPrimeFactor cq.1 ≤ K ∨
      U < canonicalLargestPrimeFactor cq.1

@[simp] theorem mem_squareWheelSurvivorShallowMatchedPairSet
    {R K : ℕ} {cq : ℕ × ℕ} :
    cq ∈ squareWheelSurvivorShallowMatchedPairSet R K ↔
      cq ∈ squareWheelSurvivorEndpointMatchedPairSet R ∧
        canonicalLargestPrimeFactor cq.1 ≤ K := by
  simp [squareWheelSurvivorShallowMatchedPairSet]

@[simp] theorem mem_squareWheelSurvivorAboveCutoffMatchedPairSet
    {R U : ℕ} {cq : ℕ × ℕ} :
    cq ∈ squareWheelSurvivorAboveCutoffMatchedPairSet R U ↔
      cq ∈ squareWheelSurvivorEndpointMatchedPairSet R ∧
        U < canonicalLargestPrimeFactor cq.1 := by
  simp [squareWheelSurvivorAboveCutoffMatchedPairSet]

@[simp] theorem mem_squareWheelSurvivorOwnerResidualPairSet
    {R K U : ℕ} {cq : ℕ × ℕ} :
    cq ∈ squareWheelSurvivorOwnerResidualPairSet R K U ↔
      cq ∈ squareWheelSurvivorEndpointMatchedPairSet R ∧
        (canonicalLargestPrimeFactor cq.1 ≤ K ∨
          U < canonicalLargestPrimeFactor cq.1) := by
  simp [squareWheelSurvivorOwnerResidualPairSet]

/-- **Exact matched-sector degree split.**  Every matched survivor is either in
the processed deep owner window or in its owner residual. -/
theorem squareWheelSurvivorEndpointMatchedPairSet_eq_deep_union_ownerResidual
    (R K U : ℕ) :
    squareWheelSurvivorEndpointMatchedPairSet R =
      squareWheelSurvivorProcessedDeepPairSet R K U ∪
        squareWheelSurvivorOwnerResidualPairSet R K U := by
  ext cq
  simp only [Finset.mem_union,
    mem_squareWheelSurvivorProcessedDeepPairSet,
    mem_squareWheelSurvivorOwnerResidualPairSet]
  constructor
  · intro hm
    by_cases hK : canonicalLargestPrimeFactor cq.1 ≤ K
    · exact Or.inr ⟨hm, Or.inl hK⟩
    · have hK' : K < canonicalLargestPrimeFactor cq.1 := by omega
      by_cases hU : canonicalLargestPrimeFactor cq.1 ≤ U
      · exact Or.inl ⟨hm, hK', hU⟩
      · exact Or.inr ⟨hm, Or.inr (by omega)⟩
  · rintro (⟨hm, _hK, _hU⟩ | ⟨hm, _howner⟩)
    · exact hm
    · exact hm

/-- The processed deep sector and owner residual cannot overlap. -/
theorem squareWheelSurvivorProcessedDeep_disjoint_ownerResidual
    (R K U : ℕ) :
    Disjoint (squareWheelSurvivorProcessedDeepPairSet R K U)
      (squareWheelSurvivorOwnerResidualPairSet R K U) := by
  rw [Finset.disjoint_left]
  intro cq hd hw
  have hd' := (mem_squareWheelSurvivorProcessedDeepPairSet.mp hd).2
  have hw' := (mem_squareWheelSurvivorOwnerResidualPairSet.mp hw).2
  rcases hw' with hshallow | habove
  · omega
  · omega

/-- The owner residual is exactly its shallow and above-cutoff pieces. -/
theorem squareWheelSurvivorOwnerResidualPairSet_eq_shallow_union_above
    (R K U : ℕ) :
    squareWheelSurvivorOwnerResidualPairSet R K U =
      squareWheelSurvivorShallowMatchedPairSet R K ∪
        squareWheelSurvivorAboveCutoffMatchedPairSet R U := by
  ext cq
  simp only [Finset.mem_union,
    mem_squareWheelSurvivorOwnerResidualPairSet,
    mem_squareWheelSurvivorShallowMatchedPairSet,
    mem_squareWheelSurvivorAboveCutoffMatchedPairSet]
  constructor
  · rintro ⟨hm, howner⟩
    rcases howner with hshallow | habove
    · exact Or.inl ⟨hm, hshallow⟩
    · exact Or.inr ⟨hm, habove⟩
  · rintro (⟨hm, hshallow⟩ | ⟨hm, habove⟩)
    · exact ⟨hm, Or.inl hshallow⟩
    · exact ⟨hm, Or.inr habove⟩

/-- At an ordered owner window the shallow and above-cutoff residual pieces are
disjoint. -/
theorem squareWheelSurvivorShallow_disjoint_above
    (R K U : ℕ) (hKU : K ≤ U) :
    Disjoint (squareWheelSurvivorShallowMatchedPairSet R K)
      (squareWheelSurvivorAboveCutoffMatchedPairSet R U) := by
  rw [Finset.disjoint_left]
  intro cq hs ha
  have hs' := (mem_squareWheelSurvivorShallowMatchedPairSet.mp hs).2
  have ha' := (mem_squareWheelSurvivorAboveCutoffMatchedPairSet.mp ha).2
  omega

/-- Signed mass of any finite survivor-pair population. -/
def squareWheelSurvivorPairSetMassReal (S : Finset (ℕ × ℕ)) : ℝ :=
  ∑ cq ∈ S, squareWheelSurvivorPairWeightReal cq

/-- Total endpoint survivor-pair mass. -/
def squareWheelSurvivorEndpointPairMassReal (R : ℕ) : ℝ :=
  squareWheelSurvivorPairSetMassReal (squareWheelSurvivorEndpointPairSet R)

/-- Matched endpoint survivor-pair mass. -/
def squareWheelSurvivorMatchedPairMassReal (R : ℕ) : ℝ :=
  squareWheelSurvivorPairSetMassReal
    (squareWheelSurvivorEndpointMatchedPairSet R)

/-- Positive-orientation endpoint survivor-pair mass. -/
def squareWheelSurvivorPositivePairMassReal (R : ℕ) : ℝ :=
  squareWheelSurvivorPairSetMassReal
    (squareWheelSurvivorEndpointPositivePairSet R)

/-- Processed-compatible deep survivor-pair mass. -/
def squareWheelSurvivorProcessedDeepPairMassReal
    (R K U : ℕ) : ℝ :=
  squareWheelSurvivorPairSetMassReal
    (squareWheelSurvivorProcessedDeepPairSet R K U)

/-- Matched owner-window residual mass. -/
def squareWheelSurvivorOwnerResidualPairMassReal
    (R K U : ℕ) : ℝ :=
  squareWheelSurvivorPairSetMassReal
    (squareWheelSurvivorOwnerResidualPairSet R K U)

/-- Shallow matched survivor residual mass. -/
def squareWheelSurvivorShallowMatchedPairMassReal
    (R K : ℕ) : ℝ :=
  squareWheelSurvivorPairSetMassReal
    (squareWheelSurvivorShallowMatchedPairSet R K)

/-- Above-cutoff matched survivor residual mass. -/
def squareWheelSurvivorAboveCutoffMatchedPairMassReal
    (R U : ℕ) : ℝ :=
  squareWheelSurvivorPairSetMassReal
    (squareWheelSurvivorAboveCutoffMatchedPairSet R U)

/-- Endpoint survivor mass is exactly matched plus positive-orientation mass. -/
theorem squareWheelSurvivorEndpointPairMassReal_eq_matched_add_positive
    (R : ℕ) :
    squareWheelSurvivorEndpointPairMassReal R =
      squareWheelSurvivorMatchedPairMassReal R +
        squareWheelSurvivorPositivePairMassReal R := by
  unfold squareWheelSurvivorEndpointPairMassReal
    squareWheelSurvivorMatchedPairMassReal
    squareWheelSurvivorPositivePairMassReal
    squareWheelSurvivorPairSetMassReal
  rw [squareWheelSurvivorEndpointPairSet_eq_matched_union_positive]
  rw [Finset.sum_union
    (squareWheelSurvivorEndpointMatched_disjoint_positive R)]

/-- Matched mass is exactly processed-compatible deep mass plus the owner
residual mass. -/
theorem squareWheelSurvivorMatchedPairMassReal_eq_deep_add_ownerResidual
    (R K U : ℕ) :
    squareWheelSurvivorMatchedPairMassReal R =
      squareWheelSurvivorProcessedDeepPairMassReal R K U +
        squareWheelSurvivorOwnerResidualPairMassReal R K U := by
  unfold squareWheelSurvivorMatchedPairMassReal
    squareWheelSurvivorProcessedDeepPairMassReal
    squareWheelSurvivorOwnerResidualPairMassReal
    squareWheelSurvivorPairSetMassReal
  rw [squareWheelSurvivorEndpointMatchedPairSet_eq_deep_union_ownerResidual]
  rw [Finset.sum_union
    (squareWheelSurvivorProcessedDeep_disjoint_ownerResidual R K U)]

/-- **Degree-of-freedom identity.**  Once the total survivor mass, the processed
compatible deep mass, and the owner residual mass are known, the positive
orientation is forced. -/
theorem squareWheelSurvivorPositivePairMassReal_eq_residual
    (R K U : ℕ) :
    squareWheelSurvivorPositivePairMassReal R =
      squareWheelSurvivorEndpointPairMassReal R -
        squareWheelSurvivorProcessedDeepPairMassReal R K U -
          squareWheelSurvivorOwnerResidualPairMassReal R K U := by
  rw [squareWheelSurvivorEndpointPairMassReal_eq_matched_add_positive,
    squareWheelSurvivorMatchedPairMassReal_eq_deep_add_ownerResidual]
  ring

/-- At an ordered owner window the owner residual mass is exactly shallow plus
above-cutoff mass. -/
theorem squareWheelSurvivorOwnerResidualPairMassReal_eq_shallow_add_above
    (R K U : ℕ) (hKU : K ≤ U) :
    squareWheelSurvivorOwnerResidualPairMassReal R K U =
      squareWheelSurvivorShallowMatchedPairMassReal R K +
        squareWheelSurvivorAboveCutoffMatchedPairMassReal R U := by
  unfold squareWheelSurvivorOwnerResidualPairMassReal
    squareWheelSurvivorShallowMatchedPairMassReal
    squareWheelSurvivorAboveCutoffMatchedPairMassReal
    squareWheelSurvivorPairSetMassReal
  rw [squareWheelSurvivorOwnerResidualPairSet_eq_shallow_union_above]
  rw [Finset.sum_union
    (squareWheelSurvivorShallow_disjoint_above R K U hKU)]

/-- Four-sector form of the degree-of-freedom identity.  The positive sector is
not an additional independent mass once the other three sectors and the total
are fixed. -/
theorem squareWheelSurvivorPositivePairMassReal_eq_fourSectorResidual
    (R K U : ℕ) (hKU : K ≤ U) :
    squareWheelSurvivorPositivePairMassReal R =
      squareWheelSurvivorEndpointPairMassReal R -
        squareWheelSurvivorProcessedDeepPairMassReal R K U -
          squareWheelSurvivorShallowMatchedPairMassReal R K -
            squareWheelSurvivorAboveCutoffMatchedPairMassReal R U := by
  rw [squareWheelSurvivorPositivePairMassReal_eq_residual,
    squareWheelSurvivorOwnerResidualPairMassReal_eq_shallow_add_above R K U hKU]
  ring

end RHLean.Proof

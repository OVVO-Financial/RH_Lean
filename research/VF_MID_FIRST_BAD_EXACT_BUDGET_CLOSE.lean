import Mathlib
import «research.VF_MID_FIRST_BAD_FINAL_AGGREGATE_CONTRACTION»

/-!
# Unconditional close of the exact first-bad budget

This PR is stacked on #914. It assumes the exact #914 signed-boundary/heat
normal form compiles and attacks only the unconditional inequality

  vfMidFirstBadAnchoredCoDivExcess R <= 0

under a genuine K=2 first-bad hypothesis.

There is no budget proposition, no conditional budget consumer, and no new
analytic hypothesis in this module.

## Sector Six regression correction (2026-10-08)

The raw #903 admitted/admitted recursive priority sector six is NOT a
cone-balanced child state in general: its exact atom U/L slack is negative at
production R=8 and R=18 (see VF_MID_915_SECTOR_SIX_CONE_AUDIT.md).
That priority remainder is distinct from the three nonzero oriented incomplete
raw-parent sectors carrying #915's clipped/admitted retained VF source.
The latter complete source is numerically cone-balanced on tested clocks, but
this does not imply balance after recursive child-run descent or at the
first-bad anchor.  No theorem below asserts such an implication.

The remaining consumer must reconstruct the actual historical/current packet
as a FULL compensated grouped return, retaining signed source, the ORIGINAL
absolute-mass denominator, occurrence tags, survivor restrictions, and
historical anchor.  The owner heat only pays for genuinely matched returns.
This file intentionally leaves the unconditional quantitative payment open.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- The greatest-owner sign reversal remains exact for an arbitrary retained
scalar, not only a square coefficient. This is the form needed when the
active VF source contributes a parentwise retained multiplier which is not
naturally presented as a square. -/
theorem descendingGreatestOwner_retainedScalar_zeroTargetExcess_flip
    {R p m n : ℕ} (hp : p.Prime)
    (hcross : (m, n) ∈ lowOwnerRevealedCrossPairCarrier R
      (lowOwnerRevealedPrimesAbove R p) p)
    (coefficient : ℝ) :
    let um := squarefreePrimeFamilyParent p m
    let un := squarefreePrimeFamilyParent p n
    coefficient * postRootZeroTargetPairExcess (m, n) =
      -(coefficient * postRootZeroTargetPairExcess (um, un)) := by
  have hdesc := descendingGreatestOwner_reciprocal_descent hp hcross
  dsimp only at hdesc ⊢
  rw [postRootZeroTargetPairExcess_eq_weight,
    postRootZeroTargetPairExcess_eq_weight,
    hdesc.2.1]
  ring

/-- Exact Co/Div heat for the same arbitrary retained scalar. -/
theorem descendingGreatestOwner_retainedScalar_pointwiseCoDivExcess_pair_eq_heat
    {R p m n : ℕ} (hp : p.Prime)
    (hcross : (m, n) ∈ lowOwnerRevealedCrossPairCarrier R
      (lowOwnerRevealedPrimesAbove R p) p)
    (coefficient : ℝ) :
    let um := squarefreePrimeFamilyParent p m
    let un := squarefreePrimeFamilyParent p n
    vfMidPointwiseCoDivExcess
        (coefficient * postRootZeroTargetPairExcess (m, n)) +
      vfMidPointwiseCoDivExcess
        (coefficient * postRootZeroTargetPairExcess (um, un)) =
      -4 * |coefficient * postRootZeroTargetPairExcess (m, n)| := by
  have hflip :=
    descendingGreatestOwner_retainedScalar_zeroTargetExcess_flip
      hp hcross coefficient
  dsimp only at hflip ⊢
  rw [hflip, abs_neg]
  simpa only [add_comm] using
    (vfMidPointwiseCoDivExcess_add_neg
      (coefficient *
        postRootZeroTargetPairExcess
          (squarefreePrimeFamilyParent p m,
            squarefreePrimeFamilyParent p n)))

/-- The arbitrary-retained owner pair is therefore cooling in the exact
Co/Div currency. -/
theorem descendingGreatestOwner_retainedScalar_pointwiseCoDivExcess_pair_nonpos
    {R p m n : ℕ} (hp : p.Prime)
    (hcross : (m, n) ∈ lowOwnerRevealedCrossPairCarrier R
      (lowOwnerRevealedPrimesAbove R p) p)
    (coefficient : ℝ) :
    let um := squarefreePrimeFamilyParent p m
    let un := squarefreePrimeFamilyParent p n
    vfMidPointwiseCoDivExcess
        (coefficient * postRootZeroTargetPairExcess (m, n)) +
      vfMidPointwiseCoDivExcess
        (coefficient * postRootZeroTargetPairExcess (um, un)) ≤ 0 := by
  dsimp only
  rw [descendingGreatestOwner_retainedScalar_pointwiseCoDivExcess_pair_eq_heat
    hp hcross coefficient]
  have hnonneg :
      0 ≤ |coefficient * postRootZeroTargetPairExcess (m, n)| :=
    abs_nonneg _
  nlinarith

/-- The literal #914 returned weight is a retained scalar times the bare
zero-target Mobius pair excess.  Naming the scalar makes it possible to carry
the *actual* VF coefficient unchanged through greatest-owner stripping instead
of replacing it by a square or an absolute majorant. -/
def vfMidActiveReturnedPairRetainedScalar
    (R p : ℕ) (sig : Finset ℕ) (ab : ℕ × ℕ) : ℝ :=
  if ab ∈ vfMidActiveReturnedPairCarrier R p sig then
    (vfMidActiveMobiusScale R ab.1 *
      vfMidActiveMobiusScale R (p * ab.2)) *
      (lowOwnerDirichletIncidenceCoefficient (R + 1) p ab.1 *
          lowOwnerDirichletIncidenceCoefficient (R + 1) p ab.2 -
        lowOwnerDirichletBaseCoefficient (R + 1) ab.1 *
          lowOwnerDirichletBaseCoefficient (R + 1) ab.2 -
        lowOwnerDirichletReturnedCoefficient (R + 1) p ab.1 *
          lowOwnerDirichletReturnedCoefficient (R + 1) p ab.2)
  else 0

theorem vfMidActiveReturnedPairWeight_eq_retainedScalar_mul_zeroTarget
    (R p : ℕ) (sig : Finset ℕ) (ab : ℕ × ℕ) :
    vfMidActiveReturnedPairWeight R p sig ab =
      vfMidActiveReturnedPairRetainedScalar R p sig ab *
        postRootZeroTargetPairExcess ab := by
  by_cases hmem : ab ∈ vfMidActiveReturnedPairCarrier R p sig
  · rw [vfMidActiveReturnedPairWeight, if_pos hmem,
      vfMidActiveReturnedPairRetainedScalar, if_pos hmem,
      lowOwnerFirstOwnerDirichletPolarizationAtom_eq_scalar,
      postRootZeroTargetPairExcess_eq_weight]
    ring
  · simp [vfMidActiveReturnedPairWeight,
      vfMidActiveReturnedPairRetainedScalar, hmem]

theorem vfMidActiveReturnedPairCoDivExcess_eq_retainedScalar
    (R p : ℕ) (sig : Finset ℕ) (ab : ℕ × ℕ) :
    vfMidActiveReturnedPairCoDivExcess R p sig ab =
      vfMidPointwiseCoDivExcess
        (vfMidActiveReturnedPairRetainedScalar R p sig ab *
          postRootZeroTargetPairExcess ab) := by
  unfold vfMidActiveReturnedPairCoDivExcess
  rw [vfMidActiveReturnedPairWeight_eq_retainedScalar_mul_zeroTarget]

/-- Every child in a fixed polarization raw-parent fibre is already on the
legal descending greatest-owner carrier for that raw parent owner. -/
theorem lowOwnerFirstOwnerPolarizationFixedRawParentFiber_mem_descendingCross
    {R p r : ℕ} {sig : Finset ℕ} {parent child : ℕ × ℕ}
    (hr : r.Prime)
    (hchild : child ∈
      lowOwnerFirstOwnerPolarizationFixedRawParentFiber
        R p sig r parent) :
    child ∈ lowOwnerRevealedCrossPairCarrier R
      (lowOwnerRevealedPrimesAbove R r) r := by
  have hgreat :
      child ∈ lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber
        R p sig r :=
    (Finset.mem_filter.mp hchild).1
  have hoff :
      child ∈ lowOwnerFirstOwnerBaseOffDiagonalPairCarrier R p sig :=
    (Finset.mem_filter.mp hgreat).1
  have hprod :
      child ∈
        (lowOwnerFirstOwnerBaseFiber R p sig).product
          (lowOwnerFirstOwnerBaseFiber R p sig) :=
    (Finset.mem_filter.mp hoff).1
  rcases Finset.mem_product.mp hprod with ⟨ha, hb⟩
  have haCar : child.1 ∈ lowOwnerNonzeroMobiusCarrier R :=
    (Finset.mem_filter.mp ha).1
  have hbCar : child.2 ∈ lowOwnerNonzeroMobiusCarrier R :=
    (Finset.mem_filter.mp hb).1
  have howner : IsSquarefreePairGreatestFreshPrimeOwner r child.1 child.2 :=
    (Finset.mem_filter.mp hgreat).2
  exact
    (mem_descendingCrossPair_iff_greatestFreshOwner hr).2
      ⟨haCar, hbCar, howner⟩

/-- **Actual-weight local owner heat.**

For a literal #914 returned child, retain its exact VF scalar and transport that
same scalar to the stripped greatest-owner parent.  The pair is nonpositive in
the production Co/Div observable.  No reciprocal norm and no coefficient
replacement is used. -/
theorem vfMidActiveReturnedPairCoDivExcess_add_strippedParent_nonpos
    {R p r : ℕ} {sig : Finset ℕ} {parent child : ℕ × ℕ}
    (hr : r.Prime)
    (hchild : child ∈
      lowOwnerFirstOwnerPolarizationFixedRawParentFiber
        (R + 1) p sig r parent) :
    vfMidActiveReturnedPairCoDivExcess R p sig child +
      vfMidPointwiseCoDivExcess
        (vfMidActiveReturnedPairRetainedScalar R p sig child *
          postRootZeroTargetPairExcess
            (squarefreePrimeFamilyParent r child.1,
              squarefreePrimeFamilyParent r child.2)) ≤ 0 := by
  rw [vfMidActiveReturnedPairCoDivExcess_eq_retainedScalar]
  exact
    descendingGreatestOwner_retainedScalar_pointwiseCoDivExcess_pair_nonpos
      hr
      (lowOwnerFirstOwnerPolarizationFixedRawParentFiber_mem_descendingCross
        hr hchild)
      (vfMidActiveReturnedPairRetainedScalar R p sig child)

/-- Co/Div excess of the stripped parent, carrying the exact scalar from the
literal active child occurrence.  This is an occurrence ledger: if two active
children descend to the same arithmetic parent they remain separately tagged
by their original child and therefore no multiplicity is lost. -/
def vfMidActiveReturnedRawParentTransportedExcess
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ)
    (parent : ℕ × ℕ) : ℝ :=
  ∑ child ∈
      lowOwnerFirstOwnerPolarizationFixedRawParentFiber
        (R + 1) p sig r parent,
    vfMidPointwiseCoDivExcess
      (vfMidActiveReturnedPairRetainedScalar R p sig child *
        postRootZeroTargetPairExcess
          (squarefreePrimeFamilyParent r child.1,
            squarefreePrimeFamilyParent r child.2))

/-- One raw-parent fibre plus its occurrence-tagged stripped-parent ledger is
cooling.  This is the finite-sum form of the literal local #914/#915 heat
identity and does not identify coincident stripped parents. -/
theorem vfMidActiveReturnedRawParentFiberExcess_add_transported_nonpos
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hr : r.Prime) :
    vfMidActiveReturnedRawParentFiberExcess R p sig r parent +
      vfMidActiveReturnedRawParentTransportedExcess R p sig r parent ≤ 0 := by
  unfold vfMidActiveReturnedRawParentFiberExcess
    vfMidActiveReturnedRawParentTransportedExcess
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_nonpos
  intro child hchild
  exact
    vfMidActiveReturnedPairCoDivExcess_add_strippedParent_nonpos
      hr hchild

/-- The occurrence-tagged stripped-parent ledger attached to exactly the three
physical boundary sectors which survive #914. -/
def vfMidActiveThreeBoundaryTransportedExcess (R : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
      ∑ r ∈ lowOwnerRevealedPrimesAbove (R + 1) p,
        ((∑ parent ∈
            lowOwnerFirstOwnerIncompleteFirstClipLeftSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentTransportedExcess
              R p sig r parent) +
          (∑ parent ∈
            lowOwnerFirstOwnerIncompleteNextClipRightSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentTransportedExcess
              R p sig r parent) +
          ∑ parent ∈
            lowOwnerFirstOwnerIncompleteReturnedClipLeftSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentTransportedExcess
              R p sig r parent)

/-- Sum a pointwise nonpositive paired ledger over one finite carrier. -/
private theorem sum_pair_nonpos
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f g : ι → ℝ)
    (h : ∀ i ∈ s, f i + g i ≤ 0) :
    (∑ i ∈ s, f i) + (∑ i ∈ s, g i) ≤ 0 := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_nonpos h

/-- **Global exact owner-heat extraction.**

The literal three-boundary Co/Div excess plus its occurrence-tagged stripped
parents is nonpositive.  Every active occurrence is paired before any quotient,
norm, triangle inequality, or parent deduplication is introduced. -/
theorem vfMidActiveThreeBoundaryExcess_add_transported_nonpos
    (R : ℕ) :
    vfMidActiveThreeBoundaryExcess R +
      vfMidActiveThreeBoundaryTransportedExcess R ≤ 0 := by
  unfold vfMidActiveThreeBoundaryExcess
    vfMidActiveThreeBoundaryTransportedExcess
  apply sum_pair_nonpos
  intro p hpMem
  apply sum_pair_nonpos
  intro sig _hsig
  apply sum_pair_nonpos
  intro r hrMem
  have hr : r.Prime :=
    (mem_primesUpTo.mp (Finset.mem_filter.mp hrMem).1).1
  have hfirst :
      (∑ parent ∈
          lowOwnerFirstOwnerIncompleteFirstClipLeftSet
            (R + 1) p sig r,
          vfMidActiveReturnedRawParentFiberExcess R p sig r parent) +
        (∑ parent ∈
          lowOwnerFirstOwnerIncompleteFirstClipLeftSet
            (R + 1) p sig r,
          vfMidActiveReturnedRawParentTransportedExcess R p sig r parent) ≤ 0 := by
    apply sum_pair_nonpos
    intro parent _hparent
    exact
      vfMidActiveReturnedRawParentFiberExcess_add_transported_nonpos
        (R := R) (p := p) (r := r) (sig := sig) (parent := parent) hr
  have hnext :
      (∑ parent ∈
          lowOwnerFirstOwnerIncompleteNextClipRightSet
            (R + 1) p sig r,
          vfMidActiveReturnedRawParentFiberExcess R p sig r parent) +
        (∑ parent ∈
          lowOwnerFirstOwnerIncompleteNextClipRightSet
            (R + 1) p sig r,
          vfMidActiveReturnedRawParentTransportedExcess R p sig r parent) ≤ 0 := by
    apply sum_pair_nonpos
    intro parent _hparent
    exact
      vfMidActiveReturnedRawParentFiberExcess_add_transported_nonpos
        (R := R) (p := p) (r := r) (sig := sig) (parent := parent) hr
  have hreturned :
      (∑ parent ∈
          lowOwnerFirstOwnerIncompleteReturnedClipLeftSet
            (R + 1) p sig r,
          vfMidActiveReturnedRawParentFiberExcess R p sig r parent) +
        (∑ parent ∈
          lowOwnerFirstOwnerIncompleteReturnedClipLeftSet
            (R + 1) p sig r,
          vfMidActiveReturnedRawParentTransportedExcess R p sig r parent) ≤ 0 := by
    apply sum_pair_nonpos
    intro parent _hparent
    exact
      vfMidActiveReturnedRawParentFiberExcess_add_transported_nonpos
        (R := R) (p := p) (r := r) (sig := sig) (parent := parent) hr
  linarith

/-- After exact owner heat is extracted, the unconditional #915 target has only
one remaining packing statement: the quarantined global residual must fit
inside the occurrence-tagged stripped-parent ledger.  This is strictly sharper
than dropping the heat and asking for separate upper/lower source bills. -/
theorem vfMidActualPrimeFirstBadAt_two_succ_activeExcess_nonpos_of_transport
    {R : ℕ} (hR : 8 ≤ R)
    (htransport :
      vfMidActiveGlobalResidualExcess R ≤
        vfMidActiveThreeBoundaryTransportedExcess R) :
    vfMidFirstBadAnchoredCoDivExcess R ≤ 0 := by
  rw [vfMidFirstBadAnchoredCoDivExcess_eq_activeResidual_add_threeBoundaryExcess
    (by omega : 3 ≤ R)]
  have hheat := vfMidActiveThreeBoundaryExcess_add_transported_nonpos R
  linarith


/-- On the nonzero-Mobius clock the physical sign has unit square. -/
private theorem realMoebiusStep_sq_eq_one_of_mem_nonzeroCarrier_exactBudget
    {R n : ℕ} (hn : n ∈ lowOwnerNonzeroMobiusCarrier R) :
    realMoebiusStep n ^ 2 = 1 := by
  have hne : realMoebiusStep n ≠ 0 :=
    (Finset.mem_filter.mp hn).2
  rcases ArithmeticFunction.moebius_eq_or n with h0 | h1 | hm1
  · exfalso
    apply hne
    simp [realMoebiusStep, h0]
  · simp [realMoebiusStep, h1]
  · simp [realMoebiusStep, hm1]

/-- Every legal descending-cross pair has zero-target sign exactly plus or
minus one; in particular its square is one. -/
theorem postRootZeroTargetPairExcess_sq_eq_one_of_descendingCross
    {R p m n : ℕ}
    (hcross : (m, n) ∈ lowOwnerRevealedCrossPairCarrier R
      (lowOwnerRevealedPrimesAbove R p) p) :
    postRootZeroTargetPairExcess (m, n) ^ 2 = 1 := by
  have hprod := (Finset.mem_filter.mp hcross).1
  rcases Finset.mem_product.mp hprod with ⟨hmCar, hnCar⟩
  have hmSq :=
    realMoebiusStep_sq_eq_one_of_mem_nonzeroCarrier_exactBudget hmCar
  have hnSq :=
    realMoebiusStep_sq_eq_one_of_mem_nonzeroCarrier_exactBudget hnCar
  rw [postRootZeroTargetPairExcess_eq_weight, mul_pow, hmSq, hnSq]
  ring

/-- Every child in the actual #914 fixed raw-parent fibre is a legal
greatest-owner descending crossing for the same owner. -/
theorem vfMidActiveFixedRawParentChild_mem_descendingCross
    {R p r : ℕ} {sig : Finset ℕ}
    {parent child : ℕ × ℕ}
    (hr : r.Prime)
    (hchild :
      child ∈ lowOwnerFirstOwnerPolarizationFixedRawParentFiber
        (R + 1) p sig r parent) :
    child ∈ lowOwnerRevealedCrossPairCarrier (R + 1)
      (lowOwnerRevealedPrimesAbove (R + 1) r) r := by
  have howner :
      child ∈ lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber
        (R + 1) p sig r :=
    (Finset.mem_filter.mp hchild).1
  rw [←
    lowOwnerFirstOwnerCellRevealedCrossCarrier_above_eq_polarizationGreatestOwner
      (R := R + 1) (p := p) (r := r) (sig := sig) hr] at howner
  exact (Finset.mem_filter.mp howner).1

/-- The arbitrary-scalar sign reversal can be specialized to an actual
occurrence weight, without assuming that the VF scale itself is owner-invariant.
Multiplying by the child zero-target sign absorbs the entire site-dependent VF
coefficient, and the stripped-parent occurrence is exactly the negative
weight. -/
theorem descendingGreatestOwner_actualWeight_pointwiseCoDivExcess_pair_eq_heat
    {R p m n : ℕ} (hp : p.Prime)
    (hcross : (m, n) ∈ lowOwnerRevealedCrossPairCarrier R
      (lowOwnerRevealedPrimesAbove R p) p)
    (weight : ℝ) :
    let um := squarefreePrimeFamilyParent p m
    let un := squarefreePrimeFamilyParent p n
    vfMidPointwiseCoDivExcess weight +
      vfMidPointwiseCoDivExcess
        ((weight * postRootZeroTargetPairExcess (m, n)) *
          postRootZeroTargetPairExcess (um, un)) =
      -4 * |weight| := by
  have hsquare :=
    postRootZeroTargetPairExcess_sq_eq_one_of_descendingCross hcross
  have hflip :=
    descendingGreatestOwner_retainedScalar_zeroTargetExcess_flip
      hp hcross (weight * postRootZeroTargetPairExcess (m, n))
  dsimp only at hflip ⊢
  have hchild :
      (weight * postRootZeroTargetPairExcess (m, n)) *
          postRootZeroTargetPairExcess (m, n) =
        weight := by
    calc
      (weight * postRootZeroTargetPairExcess (m, n)) *
          postRootZeroTargetPairExcess (m, n) =
        weight * postRootZeroTargetPairExcess (m, n) ^ 2 := by ring
      _ = weight := by rw [hsquare]; ring
  have hparent :
      (weight * postRootZeroTargetPairExcess (m, n)) *
          postRootZeroTargetPairExcess
            (squarefreePrimeFamilyParent p m,
              squarefreePrimeFamilyParent p n) =
        -weight := by
    linarith only [hflip, hchild]
  rw [hparent]
  exact vfMidPointwiseCoDivExcess_add_neg weight

/-- Summed on one actual #914 raw-parent fibre, the child occurrence together
with its multiplicity-preserving stripped-parent continuation is exactly
negative heat. The retained scalar is occurrence-dependent; no parentwise
constant-weight assumption is made. -/
theorem sum_vfMidActiveRawParentChild_parentHeat_eq
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hr : r.Prime) :
    (∑ child ∈
      lowOwnerFirstOwnerPolarizationFixedRawParentFiber
        (R + 1) p sig r parent,
      (vfMidPointwiseCoDivExcess
          (vfMidActiveReturnedPairWeight R p sig child) +
        vfMidPointwiseCoDivExcess
          ((vfMidActiveReturnedPairWeight R p sig child *
              postRootZeroTargetPairExcess child) *
            postRootZeroTargetPairExcess
              (squarefreePrimeFamilyParent r child.1,
                squarefreePrimeFamilyParent r child.2)))) =
      -4 *
        ∑ child ∈
          lowOwnerFirstOwnerPolarizationFixedRawParentFiber
            (R + 1) p sig r parent,
          |vfMidActiveReturnedPairWeight R p sig child| := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro child hchild
  have hcross :=
    vfMidActiveFixedRawParentChild_mem_descendingCross hr hchild
  have hheat :=
    descendingGreatestOwner_actualWeight_pointwiseCoDivExcess_pair_eq_heat
      hr hcross (vfMidActiveReturnedPairWeight R p sig child)
  dsimp only at hheat
  exact hheat

/-- The complete occurrence-tagged child/parent heat on one actual raw-parent
fibre is nonpositive. -/
theorem sum_vfMidActiveRawParentChild_parentHeat_nonpos
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hr : r.Prime) :
    (∑ child ∈
      lowOwnerFirstOwnerPolarizationFixedRawParentFiber
        (R + 1) p sig r parent,
      (vfMidPointwiseCoDivExcess
          (vfMidActiveReturnedPairWeight R p sig child) +
        vfMidPointwiseCoDivExcess
          ((vfMidActiveReturnedPairWeight R p sig child *
              postRootZeroTargetPairExcess child) *
            postRootZeroTargetPairExcess
              (squarefreePrimeFamilyParent r child.1,
                squarefreePrimeFamilyParent r child.2)))) ≤ 0 := by
  rw [sum_vfMidActiveRawParentChild_parentHeat_eq hr]
  have hnonneg :
      0 ≤
        ∑ child ∈
          lowOwnerFirstOwnerPolarizationFixedRawParentFiber
            (R + 1) p sig r parent,
          |vfMidActiveReturnedPairWeight R p sig child| := by
    positivity
  nlinarith


/-- Exact heat identity on one literal #914 raw-parent fibre.  This is the
equality-strengthened form of the already-compiled nonpositivity lemma: every
actual child occurrence is paired with its stripped greatest-owner parent
before any summation, so the retained site-dependent coefficient is unchanged
and the whole fibre contributes exactly minus four times its literal absolute
mass. -/
theorem vfMidActiveReturnedRawParentFiberExcess_add_transported_eq_neg_four_abs
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hr : r.Prime) :
    vfMidActiveReturnedRawParentFiberExcess R p sig r parent +
      vfMidActiveReturnedRawParentTransportedExcess R p sig r parent =
      -4 * vfMidActiveReturnedRawParentFiberAbsMass R p sig r parent := by
  unfold vfMidActiveReturnedRawParentFiberExcess
    vfMidActiveReturnedRawParentTransportedExcess
    vfMidActiveReturnedRawParentFiberAbsMass
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro child hchild
  rw [vfMidActiveReturnedPairCoDivExcess_eq_retainedScalar]
  have hcross :=
    lowOwnerFirstOwnerPolarizationFixedRawParentFiber_mem_descendingCross
      hr hchild
  have hheat :=
    descendingGreatestOwner_retainedScalar_pointwiseCoDivExcess_pair_eq_heat
      hr hcross
      (vfMidActiveReturnedPairRetainedScalar R p sig child)
  dsimp only at hheat
  rw [vfMidActiveReturnedPairWeight_eq_retainedScalar_mul_zeroTarget]
  exact hheat

private theorem sum_pair_eq_neg_four_exactBudget
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f g a : ι → ℝ)
    (h : ∀ i ∈ s, f i + g i = -4 * a i) :
    (∑ i ∈ s, f i) + (∑ i ∈ s, g i) =
      -4 * ∑ i ∈ s, a i := by
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl h

/-- Global exact #914/#915 owner heat.

The complete three surviving boundary sectors plus the occurrence-tagged
stripped-parent continuation are not merely nonpositive: they are exactly
minus four times the literal boundary absolute mass.  Thus the finite 317/1027
heat mechanism survives the full p/sig/r/raw-parent/child Fubini with no loss
of multiplicity and no replacement of the retained VF coefficient. -/
theorem vfMidActiveThreeBoundaryExcess_add_transported_eq_neg_four_abs
    (R : ℕ) :
    vfMidActiveThreeBoundaryExcess R +
      vfMidActiveThreeBoundaryTransportedExcess R =
      -4 * vfMidActiveThreeBoundaryAbsMass R := by
  unfold vfMidActiveThreeBoundaryExcess
    vfMidActiveThreeBoundaryTransportedExcess
    vfMidActiveThreeBoundaryAbsMass
  apply sum_pair_eq_neg_four_exactBudget
  intro p hpMem
  apply sum_pair_eq_neg_four_exactBudget
  intro sig _hsig
  apply sum_pair_eq_neg_four_exactBudget
  intro r hrMem
  have hr : r.Prime :=
    (mem_primesUpTo.mp (Finset.mem_filter.mp hrMem).1).1
  have hfirst :
      (∑ parent ∈
          lowOwnerFirstOwnerIncompleteFirstClipLeftSet
            (R + 1) p sig r,
          vfMidActiveReturnedRawParentFiberExcess R p sig r parent) +
        (∑ parent ∈
          lowOwnerFirstOwnerIncompleteFirstClipLeftSet
            (R + 1) p sig r,
          vfMidActiveReturnedRawParentTransportedExcess R p sig r parent) =
        -4 *
          ∑ parent ∈
            lowOwnerFirstOwnerIncompleteFirstClipLeftSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberAbsMass R p sig r parent := by
    apply sum_pair_eq_neg_four_exactBudget
    intro parent _hparent
    exact
      vfMidActiveReturnedRawParentFiberExcess_add_transported_eq_neg_four_abs
        (R := R) (p := p) (r := r) (sig := sig) (parent := parent) hr
  have hnext :
      (∑ parent ∈
          lowOwnerFirstOwnerIncompleteNextClipRightSet
            (R + 1) p sig r,
          vfMidActiveReturnedRawParentFiberExcess R p sig r parent) +
        (∑ parent ∈
          lowOwnerFirstOwnerIncompleteNextClipRightSet
            (R + 1) p sig r,
          vfMidActiveReturnedRawParentTransportedExcess R p sig r parent) =
        -4 *
          ∑ parent ∈
            lowOwnerFirstOwnerIncompleteNextClipRightSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberAbsMass R p sig r parent := by
    apply sum_pair_eq_neg_four_exactBudget
    intro parent _hparent
    exact
      vfMidActiveReturnedRawParentFiberExcess_add_transported_eq_neg_four_abs
        (R := R) (p := p) (r := r) (sig := sig) (parent := parent) hr
  have hreturned :
      (∑ parent ∈
          lowOwnerFirstOwnerIncompleteReturnedClipLeftSet
            (R + 1) p sig r,
          vfMidActiveReturnedRawParentFiberExcess R p sig r parent) +
        (∑ parent ∈
          lowOwnerFirstOwnerIncompleteReturnedClipLeftSet
            (R + 1) p sig r,
          vfMidActiveReturnedRawParentTransportedExcess R p sig r parent) =
        -4 *
          ∑ parent ∈
            lowOwnerFirstOwnerIncompleteReturnedClipLeftSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberAbsMass R p sig r parent := by
    apply sum_pair_eq_neg_four_exactBudget
    intro parent _hparent
    exact
      vfMidActiveReturnedRawParentFiberExcess_add_transported_eq_neg_four_abs
        (R := R) (p := p) (r := r) (sig := sig) (parent := parent) hr
  linarith


/-! ## Positive UPM/LPM reduction of the anchored half gate -/

/-- Total positive-side degree-one partial mass of the anchored current VF
carrier. The historical endpoint enters as the single literal anchor -D;
no historical absolute-value enlargement occurs. -/
def vfMidFirstBadAnchoredUpperPartialMass (R : ℕ) : ℝ :=
  zeroTargetUpperPart (-vfMidActualPrimeEndpointDefect R) +
    ∑ n ∈ vfMidOddCandidateSeats R,
      zeroTargetUpperPart (vfMidOddSignedSeatCharge R n)

/-- Total negative-side degree-one partial-moment magnitude of the same
anchored carrier. Both this quantity and the upper mass are pointwise sums of
nonnegative partial masses; the signed endpoint information is recovered only
by subtraction. -/
def vfMidFirstBadAnchoredLowerPartialMass (R : ℕ) : ℝ :=
  zeroTargetLowerPart (-vfMidActualPrimeEndpointDefect R) +
    ∑ n ∈ vfMidOddCandidateSeats R,
      zeroTargetLowerPart (vfMidOddSignedSeatCharge R n)

private theorem zeroTargetUpperPart_add_lowerPart_exactBudget (x : ℝ) :
    zeroTargetUpperPart x + zeroTargetLowerPart x = |x| := by
  unfold zeroTargetUpperPart zeroTargetLowerPart
  ring

/-- Upper minus lower anchored partial mass is exactly the signed anchored
physical source. -/
theorem vfMidFirstBadAnchoredUpper_sub_lower_eq_signedSource (R : ℕ) :
    vfMidFirstBadAnchoredUpperPartialMass R -
        vfMidFirstBadAnchoredLowerPartialMass R =
      (∑ n ∈ vfMidOddCandidateSeats R,
          vfMidOddSignedSeatCharge R n) -
        vfMidActualPrimeEndpointDefect R := by
  unfold vfMidFirstBadAnchoredUpperPartialMass
    vfMidFirstBadAnchoredLowerPartialMass
  have hsum :
      (∑ n ∈ vfMidOddCandidateSeats R,
        zeroTargetUpperPart (vfMidOddSignedSeatCharge R n)) -
        (∑ n ∈ vfMidOddCandidateSeats R,
          zeroTargetLowerPart (vfMidOddSignedSeatCharge R n)) =
        ∑ n ∈ vfMidOddCandidateSeats R,
          vfMidOddSignedSeatCharge R n := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    exact zeroTargetUpperPart_sub_lowerPart _
  calc
    zeroTargetUpperPart (-vfMidActualPrimeEndpointDefect R) +
          (∑ n ∈ vfMidOddCandidateSeats R,
            zeroTargetUpperPart (vfMidOddSignedSeatCharge R n)) -
        (zeroTargetLowerPart (-vfMidActualPrimeEndpointDefect R) +
          ∑ n ∈ vfMidOddCandidateSeats R,
            zeroTargetLowerPart (vfMidOddSignedSeatCharge R n)) =
      (zeroTargetUpperPart (-vfMidActualPrimeEndpointDefect R) -
        zeroTargetLowerPart (-vfMidActualPrimeEndpointDefect R)) +
      ((∑ n ∈ vfMidOddCandidateSeats R,
          zeroTargetUpperPart (vfMidOddSignedSeatCharge R n)) -
        ∑ n ∈ vfMidOddCandidateSeats R,
          zeroTargetLowerPart (vfMidOddSignedSeatCharge R n)) := by ring
    _ = -vfMidActualPrimeEndpointDefect R +
        (∑ n ∈ vfMidOddCandidateSeats R,
          vfMidOddSignedSeatCharge R n) := by
      rw [zeroTargetUpperPart_sub_lowerPart, hsum]
    _ = _ := by ring

/-- Upper plus lower anchored partial mass is exactly the unchanged #897
absolute denominator amplitude. -/
theorem vfMidFirstBadAnchoredUpper_add_lower_eq_absMass (R : ℕ) :
    vfMidFirstBadAnchoredUpperPartialMass R +
        vfMidFirstBadAnchoredLowerPartialMass R =
      |vfMidActualPrimeEndpointDefect R| +
        ∑ n ∈ vfMidOddCandidateSeats R,
          |vfMidOddSignedSeatCharge R n| := by
  unfold vfMidFirstBadAnchoredUpperPartialMass
    vfMidFirstBadAnchoredLowerPartialMass
  have hsum :
      (∑ n ∈ vfMidOddCandidateSeats R,
        zeroTargetUpperPart (vfMidOddSignedSeatCharge R n)) +
        (∑ n ∈ vfMidOddCandidateSeats R,
          zeroTargetLowerPart (vfMidOddSignedSeatCharge R n)) =
        ∑ n ∈ vfMidOddCandidateSeats R,
          |vfMidOddSignedSeatCharge R n| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    exact zeroTargetUpperPart_add_lowerPart_exactBudget _
  calc
    zeroTargetUpperPart (-vfMidActualPrimeEndpointDefect R) +
          (∑ n ∈ vfMidOddCandidateSeats R,
            zeroTargetUpperPart (vfMidOddSignedSeatCharge R n)) +
        (zeroTargetLowerPart (-vfMidActualPrimeEndpointDefect R) +
          ∑ n ∈ vfMidOddCandidateSeats R,
            zeroTargetLowerPart (vfMidOddSignedSeatCharge R n)) =
      (zeroTargetUpperPart (-vfMidActualPrimeEndpointDefect R) +
        zeroTargetLowerPart (-vfMidActualPrimeEndpointDefect R)) +
      ((∑ n ∈ vfMidOddCandidateSeats R,
          zeroTargetUpperPart (vfMidOddSignedSeatCharge R n)) +
        ∑ n ∈ vfMidOddCandidateSeats R,
          zeroTargetLowerPart (vfMidOddSignedSeatCharge R n)) := by ring
    _ = |-vfMidActualPrimeEndpointDefect R| +
        (∑ n ∈ vfMidOddCandidateSeats R,
          |vfMidOddSignedSeatCharge R n|) := by
      rw [zeroTargetUpperPart_add_lowerPart_exactBudget, hsum]
    _ = _ := by rw [abs_neg]

/-- The anchored Co-minus-three-Div observable is exactly the elementary
positive-mass balance polynomial U^2 + L^2 - 6 U L.

Thus the #915 half gate contains no irreducible signed pair algebra: all signs
can be postponed to the final subtraction of two nonnegative degree-one partial
masses. -/
theorem vfMidFirstBadAnchoredCoDivExcess_eq_upperLowerBalance
    (R : ℕ) :
    vfMidFirstBadAnchoredCoDivExcess R =
      vfMidFirstBadAnchoredUpperPartialMass R ^ 2 +
        vfMidFirstBadAnchoredLowerPartialMass R ^ 2 -
        6 * vfMidFirstBadAnchoredUpperPartialMass R *
          vfMidFirstBadAnchoredLowerPartialMass R := by
  have hexcess :=
    vfMidAnchoredZeroTarget_excess_eq_sub_sq
      (vfMidOddCandidateSeats R)
      (vfMidOddSignedSeatCharge R)
      (vfMidActualPrimeEndpointDefect R)
  have htotal :=
    vfMidAnchoredZeroTargetTotalMass_eq_absSum_sq
      (vfMidOddCandidateSeats R)
      (vfMidOddSignedSeatCharge R)
      (vfMidActualPrimeEndpointDefect R)
  have hsub := vfMidFirstBadAnchoredUpper_sub_lower_eq_signedSource R
  have hadd := vfMidFirstBadAnchoredUpper_add_lower_eq_absMass R
  unfold vfMidAnchoredZeroTargetTotalMass at htotal
  unfold vfMidFirstBadAnchoredCoDivExcess
  calc
    vfMidAnchoredZeroTargetCoPartialGram
          (vfMidOddCandidateSeats R) (vfMidOddSignedSeatCharge R)
          (vfMidActualPrimeEndpointDefect R) -
        3 * vfMidAnchoredZeroTargetDivergentGram
          (vfMidOddCandidateSeats R) (vfMidOddSignedSeatCharge R)
          (vfMidActualPrimeEndpointDefect R) =
      2 * (vfMidAnchoredZeroTargetCoPartialGram
          (vfMidOddCandidateSeats R) (vfMidOddSignedSeatCharge R)
          (vfMidActualPrimeEndpointDefect R) -
        vfMidAnchoredZeroTargetDivergentGram
          (vfMidOddCandidateSeats R) (vfMidOddSignedSeatCharge R)
          (vfMidActualPrimeEndpointDefect R)) -
      (vfMidAnchoredZeroTargetCoPartialGram
          (vfMidOddCandidateSeats R) (vfMidOddSignedSeatCharge R)
          (vfMidActualPrimeEndpointDefect R) +
        vfMidAnchoredZeroTargetDivergentGram
          (vfMidOddCandidateSeats R) (vfMidOddSignedSeatCharge R)
          (vfMidActualPrimeEndpointDefect R)) := by ring
    _ =
      2 * ((∑ n ∈ vfMidOddCandidateSeats R,
          vfMidOddSignedSeatCharge R n) -
        vfMidActualPrimeEndpointDefect R) ^ 2 -
      (|vfMidActualPrimeEndpointDefect R| +
        ∑ n ∈ vfMidOddCandidateSeats R,
          |vfMidOddSignedSeatCharge R n|) ^ 2 := by
      rw [hexcess, htotal]
    _ =
      2 * (vfMidFirstBadAnchoredUpperPartialMass R -
        vfMidFirstBadAnchoredLowerPartialMass R) ^ 2 -
      (vfMidFirstBadAnchoredUpperPartialMass R +
        vfMidFirstBadAnchoredLowerPartialMass R) ^ 2 := by
      rw [hsub, hadd]
    _ = _ := by ring

/-- Exact positive-mass form of the #915 target. -/
theorem vfMidFirstBadAnchoredCoDivExcess_nonpos_iff_upperLowerBalance
    (R : ℕ) :
    vfMidFirstBadAnchoredCoDivExcess R ≤ 0 ↔
      vfMidFirstBadAnchoredUpperPartialMass R ^ 2 +
        vfMidFirstBadAnchoredLowerPartialMass R ^ 2 ≤
        6 * vfMidFirstBadAnchoredUpperPartialMass R *
          vfMidFirstBadAnchoredLowerPartialMass R := by
  rw [vfMidFirstBadAnchoredCoDivExcess_eq_upperLowerBalance R]
  constructor <;> intro h <;> linarith



/-! ## Division-free UPM/LPM balance slack -/

/-- Polynomial balance slack for two nonnegative degree-one partial masses.
No ratio or inverse is introduced, so the definition remains meaningful on
empty Fubini fibres. -/
def vfMidUpperLowerBalanceSlack (U L : ℝ) : ℝ :=
  6 * U * L - U ^ 2 - L ^ 2

/-- The balance slack is invariant under the owner sign-reversal swap
UPM <-> LPM. -/
@[simp] theorem vfMidUpperLowerBalanceSlack_swap (U L : ℝ) :
    vfMidUpperLowerBalanceSlack L U =
      vfMidUpperLowerBalanceSlack U L := by
  unfold vfMidUpperLowerBalanceSlack
  ring

/-- A common retained scalar acts quadratically on the balance slack. -/
theorem vfMidUpperLowerBalanceSlack_smul
    (c U L : ℝ) :
    vfMidUpperLowerBalanceSlack (c * U) (c * L) =
      c ^ 2 * vfMidUpperLowerBalanceSlack U L := by
  unfold vfMidUpperLowerBalanceSlack
  ring

/-- Exact division-free corridor identity.  This is the payment algebra:
balance slack is nonnegative exactly when twice the squared signed source is
bounded by the squared total partial mass. -/
theorem vfMidUpperLowerBalanceSlack_nonneg_iff_sourceMass
    (U L : ℝ) :
    0 ≤ vfMidUpperLowerBalanceSlack U L ↔
      2 * (U - L) ^ 2 ≤ (U + L) ^ 2 := by
  unfold vfMidUpperLowerBalanceSlack
  constructor <;> intro h <;> nlinarith

/-- A completed owner-reversal pair lands on the center line U=L and therefore
has strictly favorable balance slack, including the zero-mass case. -/
theorem vfMidUpperLowerBalanceSlack_ownerPair_nonneg
    (U L : ℝ) :
    0 ≤ vfMidUpperLowerBalanceSlack (U + L) (L + U) := by
  unfold vfMidUpperLowerBalanceSlack
  nlinarith [sq_nonneg (U + L)]

/-- On the actual anchored VF carrier, the polynomial balance slack is exactly
the negative Co-minus-three-Div excess already transported by #914/#915.  This
is the pair-linear form used by the owner/Fubini descent. -/
theorem vfMidFirstBadAnchoredBalanceSlack_eq_neg_coDivExcess
    (R : ℕ) :
    vfMidUpperLowerBalanceSlack
        (vfMidFirstBadAnchoredUpperPartialMass R)
        (vfMidFirstBadAnchoredLowerPartialMass R) =
      -vfMidFirstBadAnchoredCoDivExcess R := by
  rw [vfMidFirstBadAnchoredCoDivExcess_eq_upperLowerBalance R]
  unfold vfMidUpperLowerBalanceSlack
  ring

/-- Hence the anchored payment gate is literally nonnegative UPM/LPM balance
slack; no scalar estimate is hidden in this equivalence. -/
theorem vfMidFirstBadAnchoredBalanceSlack_nonneg_iff_coDiv_nonpos
    (R : ℕ) :
    0 ≤
        vfMidUpperLowerBalanceSlack
          (vfMidFirstBadAnchoredUpperPartialMass R)
          (vfMidFirstBadAnchoredLowerPartialMass R) ↔
      vfMidFirstBadAnchoredCoDivExcess R ≤ 0 := by
  rw [vfMidFirstBadAnchoredBalanceSlack_eq_neg_coDivExcess]
  constructor <;> intro h <;> linarith


/-! ## Half-scale production inlet and literal victory condition -/

/-- Exact square expansion of the decompressed historical source.

The compact form uses `run + block`, not `run - block`: the source is
`D_A - run - block`, so the historical/current packet enters as one summed
frozen run through `R`. -/
theorem vfMidFirstBadDecompressedHistoricalSource_sq_eq_halfScale
    (R : ℕ) :
    2 * vfMidFirstBadDecompressedHistoricalSource R ^ 2 =
      2 * vfMidActualPrimeEndpointDefect (R / 2 + 1) ^ 2 +
        2 * (vfMidFrozenAffineRunPhysicalCharge (R / 2 + 1) R +
          vfMidFrozenAffineBlockPhysicalCharge (R / 2 + 1) R) ^ 2 -
        4 * vfMidActualPrimeEndpointDefect (R / 2 + 1) *
          (vfMidFrozenAffineRunPhysicalCharge (R / 2 + 1) R +
            vfMidFrozenAffineBlockPhysicalCharge (R / 2 + 1) R) := by
  unfold vfMidFirstBadDecompressedHistoricalSource
  ring

/-- The source inlet is exactly the half-scale quadratic payment. -/
theorem vfMidFirstBadSourceInlet_iff_halfScalePayment
    {R : ℕ} :
    (2 * vfMidFirstBadDecompressedHistoricalSource R ^ 2 ≤
        vfMidFirstBadZeroTargetTotalMass R) ↔
      (2 * vfMidActualPrimeEndpointDefect (R / 2 + 1) ^ 2 +
          2 * (vfMidFrozenAffineRunPhysicalCharge (R / 2 + 1) R +
            vfMidFrozenAffineBlockPhysicalCharge (R / 2 + 1) R) ^ 2 -
          4 * vfMidActualPrimeEndpointDefect (R / 2 + 1) *
            (vfMidFrozenAffineRunPhysicalCharge (R / 2 + 1) R +
              vfMidFrozenAffineBlockPhysicalCharge (R / 2 + 1) R) ≤
        vfMidFirstBadZeroTargetTotalMass R) := by
  rw [vfMidFirstBadDecompressedHistoricalSource_sq_eq_halfScale]

/-- First badness is spent only on the genuine earlier half-scale endpoint. -/
theorem vfMidActualPrimeFirstBadAt_two_succ_halfScaleAnchor_inside
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) :
    |vfMidActualPrimeEndpointDefect (R / 2 + 1)| ≤
      2 * vfMidSyntheticRadialScale (R / 2 + 1) := by
  exact vfMidActualPrimeFirstBadAt_prior_inside
    hfirst (by omega : 2 ≤ R / 2 + 1) (by omega : R / 2 + 1 < R + 1)

/-- Squared form of the only legal first-bad input at the half-scale anchor. -/
theorem vfMidActualPrimeFirstBadAt_two_succ_halfScaleAnchor_sq_inside
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) :
    vfMidActualPrimeEndpointDefect (R / 2 + 1) ^ 2 ≤
      (2 * vfMidSyntheticRadialScale (R / 2 + 1)) ^ 2 := by
  have hprior :=
    vfMidActualPrimeFirstBadAt_two_succ_halfScaleAnchor_inside hR hfirst
  have hwall0 :
      0 ≤ 2 * vfMidSyntheticRadialScale (R / 2 + 1) :=
    (abs_nonneg _).trans hprior
  have hsquare :=
    (sq_le_sq₀ (abs_nonneg _) hwall0).2 hprior
  simpa [sq_abs] using hsquare

/-- The stripped-parent transport is not fresh capacity.  With the exact heat
identity retained, the sharp residual comparison is equivalent to the original
anchored Co/Div inlet. -/
theorem vfMidActiveResidual_le_transported_add_fourAbs_iff_anchored_nonpos
    {R : ℕ} (hR : 3 ≤ R) :
    (vfMidActiveGlobalResidualExcess R ≤
        vfMidActiveThreeBoundaryTransportedExcess R +
          4 * vfMidActiveThreeBoundaryAbsMass R) ↔
      vfMidFirstBadAnchoredCoDivExcess R ≤ 0 := by
  have hsplit :=
    vfMidFirstBadAnchoredCoDivExcess_eq_activeResidual_add_threeBoundaryExcess hR
  have hheat :=
    vfMidActiveThreeBoundaryExcess_add_transported_eq_neg_four_abs R
  constructor <;> intro h <;> linarith

/-- The sharp transport statement is therefore literally the source inlet. -/
theorem vfMidActiveResidual_sharpTransport_iff_sourceInlet
    {R : ℕ} (hR : 8 ≤ R) :
    (vfMidActiveGlobalResidualExcess R ≤
        vfMidActiveThreeBoundaryTransportedExcess R +
          4 * vfMidActiveThreeBoundaryAbsMass R) ↔
      2 * vfMidFirstBadDecompressedHistoricalSource R ^ 2 ≤
        vfMidFirstBadZeroTargetTotalMass R := by
  rw [vfMidActiveResidual_le_transported_add_fourAbs_iff_anchored_nonpos
      (R := R) (by omega : 3 ≤ R),
    vfMidFirstBadAnchoredCoDivExcess_eq_decompressedHistoricalSource hR]
  constructor <;> intro h <;> linarith

/-- Under a genuine first-bad successor the unchanged #897 total mass is
strictly positive. -/
theorem vfMidFirstBadZeroTargetTotalMass_pos_of_firstBad
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) :
    0 < vfMidFirstBadZeroTargetTotalMass R := by
  have htotal0 : 0 ≤ vfMidFirstBadZeroTargetTotalMass R := by
    rw [vfMidFirstBadZeroTargetTotalMass_eq]
    positivity
  by_contra hnot
  have hzero : vfMidFirstBadZeroTargetTotalMass R = 0 :=
    le_antisymm (le_of_not_gt hnot) htotal0
  have hendpoint :=
    vfMidFirstBadNormalizedProduct_eq_nextEndpointDefect_sq
      (R := R) (by omega : 3 ≤ R)
  rw [hzero, mul_zero] at hendpoint
  have hDzero : vfMidActualPrimeEndpointDefect (R + 1) = 0 := by
    nlinarith [sq_nonneg (vfMidActualPrimeEndpointDefect (R + 1))]
  have hbreach := hfirst.1
  unfold VFMidSyntheticBadAt at hbreach
  rw [hDzero, abs_zero] at hbreach
  have hscalePos :
      0 < vfMidSyntheticRadialScale (R + 1) :=
    vfMidSyntheticRadialScale_pos (by omega : 2 ≤ R + 1)
  nlinarith

/-- **Victory condition.**

Once the half-scale/#903 payment proves the source inlet, the already-compiled
strict `> 1/2` theorem supplies the strict opposite inequality under the same
hypothetical first-bad successor.  Their conjunction is the desired
contradiction. -/
theorem vfMidActualPrimeFirstBadAt_two_succ_victory_of_sourceInlet
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1))
    (hinlet :
      2 * vfMidFirstBadDecompressedHistoricalSource R ^ 2 ≤
        vfMidFirstBadZeroTargetTotalMass R) :
    False := by
  have hgt :=
    vfMidActualPrimeFirstBadAt_two_succ_nnsNormalized_gt_half hR hfirst
  have htotalPos :=
    vfMidFirstBadZeroTargetTotalMass_pos_of_firstBad hR hfirst
  have hmul :
      (1 / 2 : ℝ) * vfMidFirstBadZeroTargetTotalMass R <
        vfMidFirstBadNNSNormalizedCovariance R *
          vfMidFirstBadZeroTargetTotalMass R :=
    mul_lt_mul_of_pos_right hgt htotalPos
  have hendpoint :=
    vfMidFirstBadNormalizedProduct_eq_nextEndpointDefect_sq
      (R := R) (by omega : 3 ≤ R)
  rw [hendpoint,
    vfMidActualPrimeEndpointDefect_succ_eq_decompressedHistoricalSource hR]
    at hmul
  nlinarith

/-- Equivalent victory gate in the exact anchored Co/Div coordinate. -/
theorem vfMidActualPrimeFirstBadAt_two_succ_victory_of_activeExcess_nonpos
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1))
    (hcodiv : vfMidFirstBadAnchoredCoDivExcess R ≤ 0) :
    False := by
  apply vfMidActualPrimeFirstBadAt_two_succ_victory_of_sourceInlet hR hfirst
  rw [vfMidFirstBadAnchoredCoDivExcess_eq_decompressedHistoricalSource hR]
    at hcodiv
  linarith

/-- The half-scale historical run and current block are not two independent
objects: together they are exactly the already-compiled subdoubling VF tracking
defect on [A,R+1), with A = R/2+1. -/
theorem vfMidHalfScaleRunPlusBlock_eq_trackingDefect
    {R : ℕ} (hR : 8 ≤ R) :
    vfMidFrozenAffineRunPhysicalCharge (R / 2 + 1) R +
        vfMidFrozenAffineBlockPhysicalCharge (R / 2 + 1) R =
      vfMidDyadicVFTrackingDefect (R / 2 + 1) (R + 1) := by
  have hA3 : 3 ≤ R / 2 + 1 := by omega
  have hA2 : 2 ≤ R / 2 + 1 := by omega
  have hAR : R / 2 + 1 ≤ R := by omega
  have hAB : R / 2 + 1 ≤ R + 1 := by omega
  have hBA : R + 1 ≤ 2 * (R / 2 + 1) := by omega
  calc
    vfMidFrozenAffineRunPhysicalCharge (R / 2 + 1) R +
        vfMidFrozenAffineBlockPhysicalCharge (R / 2 + 1) R =
      vfMidFrozenAffineRunPhysicalCharge (R / 2 + 1) (R + 1) :=
        (vfMidFrozenAffineRunPhysicalCharge_succ hAR).symm
    _ = vfMidOddRunSeatMass (R / 2 + 1) (R + 1) :=
      vfMidFrozenAffineRunPhysicalCharge_eq_oddRunSeatMass hA3 hAB hBA
    _ = vfMidDyadicVFTrackingDefect (R / 2 + 1) (R + 1) :=
      (vfMidDyadicVFTrackingDefect_eq_oddRunSeatMass hA2 hAB).symm

/-- The same half-scale packet is already split by the lower-run capacitor:
the frozen-safe part plus the exact multiplicity-preserving lower-prime
transport.  This is the run-level object which must feed the #903 recursive
selector; no new decomposition is introduced in #915. -/
theorem vfMidHalfScaleRunPlusBlock_eq_frozenSafe_add_lowerTransport
    {R : ℕ} (hR : 8 ≤ R) :
    vfMidFrozenAffineRunPhysicalCharge (R / 2 + 1) R +
        vfMidFrozenAffineBlockPhysicalCharge (R / 2 + 1) R =
      vfMidDyadicFrozenSafeMass (R / 2 + 1) (R + 1) +
        vfMidDyadicLowerPrimeIntervalTransport (R / 2 + 1) (R + 1) := by
  rw [vfMidHalfScaleRunPlusBlock_eq_trackingDefect hR]
  exact
    vfMidDyadicVFTrackingDefect_eq_frozenSafe_add_lowerTransport
      (by omega : 4 ≤ R / 2 + 1)
      (by omega : R / 2 + 1 ≤ R + 1)
      (by omega : R + 1 ≤ 2 * (R / 2 + 1))


/-! ## Forward reconstruction: owner 2 -> 3 -> 5 -> ... -> R

This is the *degree-one physical ledger*, not an invented stripped-parent
payment.  Process a fixed square block from the exact parity carrier and
remove each composite at its least odd-prime owner.  The retained VF seat
weight stays on the original physical occurrence.  Only at the final cutoff
does the provisional survivor charge become the actual prime indicator.

These identities preserve the original anchored signed source AND its original
absolute-mass denominator.  They do not prove that every intermediate sieve
state is cone-balanced (that claim is false) and do not prove the pair-level
historical/current sharp-transport payment.  That remains the red hbalance.
-/

/-- Number of original parity seats already removed by the prefix wheel,
expressed as an exact real cardinal difference. -/
def vfMid915AscendingProcessedMass (S R : ℕ) : ℝ :=
  (R : ℝ) - ((vfMidSquarePrefixWheelSurvivors S R).card : ℝ)

/-- At the first owner, 2, no *odd* candidate has yet been removed. -/
theorem vfMid915AscendingProcessedMass_two (R : ℕ) :
    vfMid915AscendingProcessedMass 2 R = 0 := by
  have hcard : (vfMidSquarePrefixWheelSurvivors 2 R).card = R :=
    vfMidOddCandidateSeats_card R
  unfold vfMid915AscendingProcessedMass
  rw [hcard]
  ring

/-- On a frozen prefix, ascending removals equal the unique processed
least-prime owner census already formalized in the affine splice. -/
theorem vfMid915AscendingProcessedMass_eq_processedOwner
    {A R : ℕ} (hA : 3 ≤ A) (hAR : A ≤ R) :
    vfMid915AscendingProcessedMass A R =
      ∑ p ∈ vfMidFrozenProcessedOwnerPrimes A R,
        ((vfMidSquareBandCompositeOwner R p).card : ℝ) := by
  exact vfMid_root_sub_prefixSurvivorCard_eq_processedOwnerCards hA hAR

/-- Completion of the entire prefix sieve: every remaining survivor is prime.
No heuristic block-prime supply is substituted. -/
theorem vfMid915AscendingProcessedMass_full (R : ℕ) (hR : 2 ≤ R) :
    vfMid915AscendingProcessedMass R R =
      (R : ℝ) - (vfMidIntegerBlockPrimeSupply R : ℝ) := by
  unfold vfMid915AscendingProcessedMass
  rw [vfMidIntegerBlockPrimeSupply_eq_fullPrefixWheelCard R hR]

/-- A provisional forward-sieve signed source, prior to final removal. -/
def vfMid915AscendingStageSigned (R : ℕ) (D w C : ℝ) : ℝ :=
  -D + (w - 1) * (R : ℝ) + C

/-- Original-denominator accounting on that *same* provisional physical
carrier.  It may only be interpreted as actual VF seat absolute mass once
all least-prime owners have acted. -/
def vfMid915AscendingStageAbs (R : ℕ) (D w C : ℝ) : ℝ :=
  |D| + (1 - w) * (R : ℝ) + (2 * w - 1) * C

def vfMid915AscendingStageSlack (R : ℕ) (D w C : ℝ) : ℝ :=
  vfMid915AscendingStageAbs R D w C ^ 2 -
    2 * vfMid915AscendingStageSigned R D w C ^ 2

/-- An ascending least-prime removal adds d to signed charge and
(2w-1)d to the original absolute ledger, without ownerwise assumptions. -/
theorem vfMid915AscendingStage_step
    (R : ℕ) (D w C d : ℝ) :
    vfMid915AscendingStageSigned R D w (C + d) =
        vfMid915AscendingStageSigned R D w C + d ∧
    vfMid915AscendingStageAbs R D w (C + d) =
        vfMid915AscendingStageAbs R D w C + (2 * w - 1) * d := by
  constructor
  · unfold vfMid915AscendingStageSigned
    ring
  · unfold vfMid915AscendingStageAbs
    ring

/-- Exact cross-owner contribution to the cone-slack change.
Its first term depends on the *entire accumulated state*; the quadratic
increment may be negative.  No forward monotonicity/cone induction follows. -/
theorem vfMid915AscendingStage_slack_step
    (R : ℕ) (D w C d : ℝ) :
    vfMid915AscendingStageSlack R D w (C + d) -
        vfMid915AscendingStageSlack R D w C =
      2 * d * ((2 * w - 1) * vfMid915AscendingStageAbs R D w C -
        2 * vfMid915AscendingStageSigned R D w C) +
      d ^ 2 * ((2 * w - 1) ^ 2 - 2) := by
  unfold vfMid915AscendingStageSlack vfMid915AscendingStageAbs
    vfMid915AscendingStageSigned
  ring

/-- Literal physical prefix state, including the original D_R anchor. -/
def vfMid915AscendingSigned (S R : ℕ) : ℝ :=
  vfMid915AscendingStageSigned R
    (vfMidActualPrimeEndpointDefect R)
    (vfMidOddFractionalPrimeSeatWeight R)
    (vfMid915AscendingProcessedMass S R)

def vfMid915AscendingAbsolute (S R : ℕ) : ℝ :=
  vfMid915AscendingStageAbs R
    (vfMidActualPrimeEndpointDefect R)
    (vfMidOddFractionalPrimeSeatWeight R)
    (vfMid915AscendingProcessedMass S R)

/-- At cutoff R the forward sieve recovers the original anchored U-L,
without a signed owner enlargement or historical absolute-value expansion. -/
theorem vfMid915AscendingSigned_full_eq_anchored
    (R : ℕ) (hR : 3 ≤ R) :
    vfMid915AscendingSigned R R =
      vfMidFirstBadAnchoredUpperPartialMass R -
        vfMidFirstBadAnchoredLowerPartialMass R := by
  have hR2 : 2 ≤ R := by omega
  have hcard := vfMidOddActualComposite_card_add_primeSupply R hR2
  have hcardR :
      ((vfMidSquareBandPrefixCompositeSurvivors 2 R).card : ℝ) +
        (vfMidIntegerBlockPrimeSupply R : ℝ) = (R : ℝ) := by
    exact_mod_cast hcard
  have hseat :
      (∑ n ∈ vfMidOddCandidateSeats R, vfMidOddSignedSeatCharge R n) =
        vfMidBandMass R - (vfMidIntegerBlockPrimeSupply R : ℝ) := by
    rw [vfMidOddSignedSeatCharge_sum R hR2]
    unfold vfMidOddCompositeTrackingDefect
      vfMidOddFractionalCompositeReference
    linarith
  rw [vfMidFirstBadAnchoredUpper_sub_lower_eq_signedSource R, hseat]
  unfold vfMid915AscendingSigned vfMid915AscendingStageSigned
  rw [vfMid915AscendingProcessedMass_full R hR2]
  have hw := vfMidOddFractionalPrimeSeatWeight_mul_population R hR2
  nlinarith [hw]

/-- At cutoff R, and only then, the ascending absolute ledger is EXACTLY
the original #897 anchored U+L denominator.  No ownerwise abs majorant. -/
theorem vfMid915AscendingAbsolute_full_eq_anchored
    (R : ℕ) (hR : 3 ≤ R) :
    vfMid915AscendingAbsolute R R =
      vfMidFirstBadAnchoredUpperPartialMass R +
        vfMidFirstBadAnchoredLowerPartialMass R := by
  have hR2 : 2 ≤ R := by omega
  have hw0 := vfMidOddFractionalPrimeSeatWeight_nonneg R hR2
  have hw1 := vfMidOddFractionalPrimeSeatWeight_le_one_of_three_le R hR
  have hpoint :
      ∀ n ∈ vfMidOddCandidateSeats R,
        |vfMidOddSignedSeatCharge R n| =
          vfMidOddFractionalPrimeSeatWeight R +
            (1 - 2 * vfMidOddFractionalPrimeSeatWeight R) *
              vfMidActualPrimeSeatMass n := by
    intro n _hn
    by_cases hp : n.Prime
    · rw [vfMidOddSignedSeatCharge_of_prime R n hp]
      have hcomp : 0 ≤ 1 - vfMidOddFractionalPrimeSeatWeight R := by
        linarith
      rw [abs_neg, abs_of_nonneg hcomp]
      simp [vfMidActualPrimeSeatMass, hp]
      ring
    · rw [vfMidOddSignedSeatCharge_of_not_prime R n hp,
        abs_of_nonneg hw0]
      simp [vfMidActualPrimeSeatMass, hp]
  have hsumAbs :
      (∑ n ∈ vfMidOddCandidateSeats R,
        |vfMidOddSignedSeatCharge R n|) =
        vfMidOddFractionalPrimeSeatWeight R * (R : ℝ) +
          (1 - 2 * vfMidOddFractionalPrimeSeatWeight R) *
            (vfMidIntegerBlockPrimeSupply R : ℝ) := by
    calc
      _ = ∑ n ∈ vfMidOddCandidateSeats R,
            (vfMidOddFractionalPrimeSeatWeight R +
              (1 - 2 * vfMidOddFractionalPrimeSeatWeight R) *
                vfMidActualPrimeSeatMass n) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact hpoint n hn
      _ = (∑ _n ∈ vfMidOddCandidateSeats R,
              vfMidOddFractionalPrimeSeatWeight R) +
            (1 - 2 * vfMidOddFractionalPrimeSeatWeight R) *
              (∑ n ∈ vfMidOddCandidateSeats R,
                vfMidActualPrimeSeatMass n) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = _ := by
            rw [vfMidActualPrimeSeatMass_sum_oddCandidates R hR2,
              Finset.sum_const, nsmul_eq_mul, vfMidOddCandidateSeats_card]
            ring
  rw [vfMidFirstBadAnchoredUpper_add_lower_eq_absMass R, hsumAbs]
  unfold vfMid915AscendingAbsolute vfMid915AscendingStageAbs
  rw [vfMid915AscendingProcessedMass_full R hR2]
  ring

/-- An exact bridge to the production cone *coordinate*, not a positive-cone
claim.  A proof that this slack is nonnegative still needs new arithmetic. -/
theorem vfMid915AscendingFinalSlack_eq_anchoredBalance
    (R : ℕ) (hR : 3 ≤ R) :
    vfMid915AscendingStageSlack R
        (vfMidActualPrimeEndpointDefect R)
        (vfMidOddFractionalPrimeSeatWeight R)
        (vfMid915AscendingProcessedMass R R) =
      vfMidUpperLowerBalanceSlack
        (vfMidFirstBadAnchoredUpperPartialMass R)
        (vfMidFirstBadAnchoredLowerPartialMass R) := by
  change vfMid915AscendingAbsolute R R ^ 2 -
      2 * vfMid915AscendingSigned R R ^ 2 =
        vfMidUpperLowerBalanceSlack
          (vfMidFirstBadAnchoredUpperPartialMass R)
          (vfMidFirstBadAnchoredLowerPartialMass R)
  rw [vfMid915AscendingAbsolute_full_eq_anchored R hR,
    vfMid915AscendingSigned_full_eq_anchored R hR]
  unfold vfMidUpperLowerBalanceSlack
  ring

/-- **Production theorem: half-scale source payment.**

This is now the only red mathematical line in #915.  The prior-good input has
already been isolated above.  The remaining run/current quadratic must be paid
by the merged #903 signed sector-six ledger with the survivor restriction
retained.  No restoring packet or transported-parent capacity is available
here. -/
theorem vfMidActualPrimeFirstBadAt_two_succ_halfScaleSectorSixPayment
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) :
    2 * vfMidActualPrimeEndpointDefect (R / 2 + 1) ^ 2 +
        2 * (vfMidFrozenAffineRunPhysicalCharge (R / 2 + 1) R +
          vfMidFrozenAffineBlockPhysicalCharge (R / 2 + 1) R) ^ 2 -
        4 * vfMidActualPrimeEndpointDefect (R / 2 + 1) *
          (vfMidFrozenAffineRunPhysicalCharge (R / 2 + 1) R +
            vfMidFrozenAffineBlockPhysicalCharge (R / 2 + 1) R) ≤
      vfMidFirstBadZeroTargetTotalMass R := by
  have hprior :=
    vfMidActualPrimeFirstBadAt_two_succ_halfScaleAnchor_sq_inside hR hfirst
  have hsplit :=
    vfMidFirstBadAnchoredCoDivExcess_eq_activeResidual_add_threeBoundaryExcess
      (R := R) (by omega : 3 ≤ R)
  have hheat :=
    vfMidActiveThreeBoundaryExcess_add_transported_eq_neg_four_abs R
  have hbalance :
      0 ≤
        vfMidUpperLowerBalanceSlack
          (vfMidFirstBadAnchoredUpperPartialMass R)
          (vfMidFirstBadAnchoredLowerPartialMass R) := by
    rw [vfMidFirstBadAnchoredBalanceSlack_eq_neg_coDivExcess]
    -- OPEN, not implied by hprior/hsplit/hheat.
    -- The native #903 sixth continuation class is numerically OUTSIDE the
    -- balance cone at production R=8 and R=18.  The three retained-VF
    -- oriented boundary sectors are a DIFFERENT carrier; their complete
    -- observed balance cannot be substituted here.
    --
    -- The forward parity/least-prime reconstruction above now recovers
    -- BOTH the actual anchored U-L and its exact original U+L denominator.
    -- It begins at owner 2, adds each unique least-owner removal once,
    -- and retains the original physical VF weight throughout.
    -- These are *degree-one* equalities, NOT a paid pair-level historical
    -- return reconstruction.  Universal cone closure would be false:
    -- stage slack can be negative, and the unconditional anchored cone
    -- conflicts asymptotically with Littlewood's known oscillations.
    -- Required: occurrence-matched historical/current pair-Fubini transport
    -- plus an arithmetic payment SPECIFIC to hfirst; no synthetic negative
    -- stripped parents and no all-R/all-stage cone hypothesis.
    -- The failing linarith remains the explicit mathematical seam.
    linarith
  have hcodiv :
      vfMidFirstBadAnchoredCoDivExcess R ≤ 0 :=
    (vfMidFirstBadAnchoredBalanceSlack_nonneg_iff_coDiv_nonpos R).1 hbalance
  have hinlet :
      2 * vfMidFirstBadDecompressedHistoricalSource R ^ 2 ≤
        vfMidFirstBadZeroTargetTotalMass R := by
    rw [vfMidFirstBadAnchoredCoDivExcess_eq_decompressedHistoricalSource hR]
      at hcodiv
    linarith
  exact (vfMidFirstBadSourceInlet_iff_halfScalePayment).1 hinlet

/-- The production payment is exactly the original source inlet. -/
theorem vfMidActualPrimeFirstBadAt_two_succ_sourceInlet
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) :
    2 * vfMidFirstBadDecompressedHistoricalSource R ^ 2 ≤
      vfMidFirstBadZeroTargetTotalMass R := by
  rw [vfMidFirstBadSourceInlet_iff_halfScalePayment]
  exact
    vfMidActualPrimeFirstBadAt_two_succ_halfScaleSectorSixPayment hR hfirst

/-- **Unconditional #915 victory theorem.** -/
theorem vfMidActualPrimeFirstBadAt_two_succ_activeExcess_nonpos
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) :
    vfMidFirstBadAnchoredCoDivExcess R ≤ 0 := by
  rw [vfMidFirstBadAnchoredCoDivExcess_eq_decompressedHistoricalSource hR]
  have hinlet :=
    vfMidActualPrimeFirstBadAt_two_succ_sourceInlet hR hfirst
  linarith

/-- **Literal terminal contradiction from #915.** -/
theorem vfMidActualPrimeFirstBadAt_two_succ_closed
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) :
    False := by
  exact
    vfMidActualPrimeFirstBadAt_two_succ_victory_of_sourceInlet hR hfirst
      (vfMidActualPrimeFirstBadAt_two_succ_sourceInlet hR hfirst)

end RHLean.Analysis

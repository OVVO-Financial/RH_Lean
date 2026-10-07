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

/-- Production target: unconditional exact first-bad budget close.

The proof starts from the endpoint-sign restoring decomposition while retaining
all already-compiled cooling. The remaining unsolved goals are therefore the
source-side owner-orbit inequalities themselves, not another conditional
interface. -/
theorem vfMidActualPrimeFirstBadAt_two_succ_activeExcess_nonpos
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) :
    vfMidFirstBadAnchoredCoDivExcess R ≤ 0 := by
  have h3 : 3 ≤ R := by omega
  by_cases hB : 0 ≤ vfMidActualPrimeEndpointDefect (R + 1)
  · rw [vfMidFirstBadAnchoredCoDivExcess_eq_upper_restoring_slack h3]
    have hcool :=
      vfMidFirstBadUpperRestoringAnchorSlack_nonpos h3 hfirst hB
    nlinarith
  · have hB' : vfMidActualPrimeEndpointDefect (R + 1) ≤ 0 :=
      le_of_not_ge hB
    rw [vfMidFirstBadAnchoredCoDivExcess_eq_lower_restoring_slack h3]
    have hcool :=
      vfMidFirstBadLowerRestoringAnchorSlack_nonpos h3 hfirst hB'
    nlinarith

end RHLean.Analysis

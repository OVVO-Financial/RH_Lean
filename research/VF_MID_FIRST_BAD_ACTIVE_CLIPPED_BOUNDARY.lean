import Mathlib
import «research.VF_MID_FIRST_BAD_ACTIVE_EXCESS_LEDGER»
import «research.VF_MID_CENTERED_GREATEST_OWNER_RANK_TELESCOPE»
import «research.VF_MID_FINAL_SIGNED_RANK_CONTRACTION»

/-!
# First-bad active physical source on the clipped boundary

The #911 active source is already root-free.  This module identifies its exact
location in the first-owner polarization topology before any estimate is used.

At the physical clock `R + 1`, an active square-block site that occurs on the
p-free base side of a first-owner cell is necessarily clipped: multiplying it
by the first owner p leaves the common clock.  Consequently the actual active
oriented cell Gram has no admitted-base contribution.  Its entire nonzero
support is the clipped-base x child boundary.

The pointwise physical product is then welded to the already-compiled
Dirichlet-polarization atom with the literal site-dependent VF scale retained.
No norm, triangle inequality, packet-to-scale inheritance, or analytic input is
used here.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Root-free retained Möbius scale of the active physical site. -/
def vfMidActiveMobiusScale (R n : ℕ) : ℝ :=
  vfMidOneBlockActivePhysicalSite R n * realMoebiusStep n

/-- On the nonzero-Möbius clock, multiplying the retained active scale back by
Möbius recovers the active physical site exactly. -/
theorem vfMidActiveMobiusScale_mul_moebius
    {R n : ℕ}
    (hn : n ∈ lowOwnerNonzeroMobiusCarrier (R + 1)) :
    vfMidActiveMobiusScale R n * realMoebiusStep n =
      vfMidOneBlockActivePhysicalSite R n := by
  have hmu : realMoebiusStep n ≠ 0 :=
    (Finset.mem_filter.mp hn).2
  have hsq : realMoebiusStep n ^ 2 = 1 := by
    rcases ArithmeticFunction.moebius_eq_or n with h0 | h1 | hm1
    · exfalso
      apply hmu
      simp [realMoebiusStep, h0]
    · simp [realMoebiusStep, h1]
    · simp [realMoebiusStep, hm1]
  unfold vfMidActiveMobiusScale
  calc
    (vfMidOneBlockActivePhysicalSite R n * realMoebiusStep n) *
        realMoebiusStep n =
      vfMidOneBlockActivePhysicalSite R n *
        realMoebiusStep n ^ 2 := by ring
    _ = vfMidOneBlockActivePhysicalSite R n := by
      rw [hsq]
      ring

/-- An admitted p-free base site cannot itself be an active site of the current
physical square block.  Active base sites are clipped by the already-compiled
physical geometry theorem. -/
theorem vfMidOneBlockActivePhysicalSite_eq_zero_of_admittedBase
    {R p a : ℕ} {sig : Finset ℕ}
    (hR : 3 ≤ R) (hp : p.Prime)
    (haAdm : a ∈ lowOwnerFirstOwnerAdmittedBaseFiber (R + 1) p sig) :
    vfMidOneBlockActivePhysicalSite R a = 0 := by
  unfold vfMidOneBlockActivePhysicalSite
  by_cases haActive : a ∈ vfMidOneBlockActivePhysicalCarrier R
  · have haBase :
        a ∈ lowOwnerFirstOwnerBaseFiber (R + 1) p sig :=
      (Finset.mem_filter.mp haAdm).1
    have haClip :=
      vfMidOneBlockActivePhysical_mem_clippedBase
        hR hp haActive haBase
    have hadmLe :
        p * a ≤ squareRootEndpoint (R + 1) :=
      (Finset.mem_filter.mp haAdm).2
    have hclipGt :
        squareRootEndpoint (R + 1) < p * a :=
      (Finset.mem_filter.mp haClip).2
    omega
  · simp [haActive]

/-- Hence the retained active scale itself vanishes on the admitted p-free
base side. -/
theorem vfMidActiveMobiusScale_eq_zero_of_admittedBase
    {R p a : ℕ} {sig : Finset ℕ}
    (hR : 3 ≤ R) (hp : p.Prime)
    (haAdm : a ∈ lowOwnerFirstOwnerAdmittedBaseFiber (R + 1) p sig) :
    vfMidActiveMobiusScale R a = 0 := by
  unfold vfMidActiveMobiusScale
  rw [vfMidOneBlockActivePhysicalSite_eq_zero_of_admittedBase hR hp haAdm]
  ring

/-- **Pointwise root-free physical/polarization weld.**

For any base/child pair in one first-owner cell, including sites on which the
active physical field vanishes, the physical product is the Dirichlet
polarization atom multiplied by the two literal retained active VF scales. -/
theorem vfMidActivePhysicalPair_eq_scaledDirichletPolarizationAtom
    {R p a b : ℕ} {sig : Finset ℕ}
    (hR : 3 ≤ R) (hp : p.Prime)
    (haBase : a ∈ lowOwnerFirstOwnerBaseFiber (R + 1) p sig)
    (hbChild : b ∈ lowOwnerFirstOwnerChildFiber (R + 1) p sig) :
    vfMidOneBlockActivePhysicalSite R a *
        vfMidOneBlockActivePhysicalSite R b =
      (vfMidActiveMobiusScale R a *
        vfMidActiveMobiusScale R b) *
        lowOwnerFirstOwnerDirichletPolarizationAtom
          (R + 1) p (a, b / p) := by
  by_cases haActive : a ∈ vfMidOneBlockActivePhysicalCarrier R
  · by_cases hbActive : b ∈ vfMidOneBlockActivePhysicalCarrier R
    · have ha1 : a ≠ 1 := by
        intro ha
        subst a
        exact one_not_mem_vfMidOneBlockActivePhysicalCarrier
          (by omega : 1 ≤ R) haActive
      have hb1 : b ≠ 1 := by
        intro hb
        subst b
        exact one_not_mem_vfMidOneBlockActivePhysicalCarrier
          (by omega : 1 ≤ R) hbActive
      have h :=
        vfMidAnchoredUpperActivePair_eq_scaledDirichletPolarizationAtom
          hR hp haActive hbActive haBase hbChild
      simpa [vfMidActiveMobiusScale,
        vfMidAnchoredUpperMobiusScale,
        vfMidOneBlockAnchoredUpperPhysicalSite,
        vfMidOneBlockActivePhysicalSite,
        haActive, hbActive, ha1, hb1] using h
    · simp [vfMidActiveMobiusScale, vfMidOneBlockActivePhysicalSite,
        hbActive]
  · simp [vfMidActiveMobiusScale, vfMidOneBlockActivePhysicalSite,
      haActive]

/-- The weighted active polarization mass on the full oriented first-owner cell
in the original base x child coordinates. -/
def vfMidActiveScaledPolarizationCellMass
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  ∑ ab ∈
      (lowOwnerFirstOwnerBaseFiber (R + 1) p sig).product
        (lowOwnerFirstOwnerChildFiber (R + 1) p sig),
    (vfMidActiveMobiusScale R ab.1 *
      vfMidActiveMobiusScale R ab.2) *
      lowOwnerFirstOwnerDirichletPolarizationAtom
        (R + 1) p (ab.1, ab.2 / p)

/-- Exact weight-preserving source weld at one cell. -/
theorem vfMidActiveCellGram_eq_scaledPolarizationCellMass
    {R p : ℕ} {sig : Finset ℕ}
    (hR : 3 ≤ R) (hp : p.Prime) :
    lowOwnerFirstOwnerCellGramWith
        (R + 1) p sig (vfMidOneBlockActivePhysicalSite R) =
      vfMidActiveScaledPolarizationCellMass R p sig := by
  unfold lowOwnerFirstOwnerCellGramWith
    vfMidActiveScaledPolarizationCellMass
  apply Finset.sum_congr rfl
  intro ab hab
  have haBase :
      ab.1 ∈ lowOwnerFirstOwnerBaseFiber (R + 1) p sig :=
    (Finset.mem_product.mp hab).1
  have hbChild :
      ab.2 ∈ lowOwnerFirstOwnerChildFiber (R + 1) p sig :=
    (Finset.mem_product.mp hab).2
  exact
    vfMidActivePhysicalPair_eq_scaledDirichletPolarizationAtom
      hR hp haBase hbChild

/-- The part of the scaled physical polarization mass whose first coordinate
is admitted.  The theorem below shows this entire piece is identically zero. -/
def vfMidActiveScaledAdmittedBaseCellMass
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  ∑ ab ∈
      (lowOwnerFirstOwnerAdmittedBaseFiber (R + 1) p sig).product
        (lowOwnerFirstOwnerChildFiber (R + 1) p sig),
    (vfMidActiveMobiusScale R ab.1 *
      vfMidActiveMobiusScale R ab.2) *
      lowOwnerFirstOwnerDirichletPolarizationAtom
        (R + 1) p (ab.1, ab.2 / p)

/-- The admitted-base contribution is exactly zero, not merely bounded. -/
theorem vfMidActiveScaledAdmittedBaseCellMass_eq_zero
    {R p : ℕ} {sig : Finset ℕ}
    (hR : 3 ≤ R) (hp : p.Prime) :
    vfMidActiveScaledAdmittedBaseCellMass R p sig = 0 := by
  unfold vfMidActiveScaledAdmittedBaseCellMass
  apply Finset.sum_eq_zero
  intro ab hab
  have haAdm :
      ab.1 ∈ lowOwnerFirstOwnerAdmittedBaseFiber (R + 1) p sig :=
    (Finset.mem_product.mp hab).1
  rw [vfMidActiveMobiusScale_eq_zero_of_admittedBase hR hp haAdm]
  ring

/-- Literal weighted clipped-base x child mass.  This is where the entire
nonzero #911 active first-owner source actually lives. -/
def vfMidActiveScaledClippedBaseCellMass
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  ∑ ab ∈
      (lowOwnerFirstOwnerClippedBaseFiber (R + 1) p sig).product
        (lowOwnerFirstOwnerChildFiber (R + 1) p sig),
    (vfMidActiveMobiusScale R ab.1 *
      vfMidActiveMobiusScale R ab.2) *
      lowOwnerFirstOwnerDirichletPolarizationAtom
        (R + 1) p (ab.1, ab.2 / p)

/-- **Active source support theorem.**

The complete active cell Gram equals the clipped-base boundary mass exactly.
There is no admitted-base / greatest-owner Sector-6 contribution at this first
physical Fubini layer. -/
theorem vfMidActiveCellGram_eq_scaledClippedBaseCellMass
    {R p : ℕ} {sig : Finset ℕ}
    (hR : 3 ≤ R) (hp : p.Prime) :
    lowOwnerFirstOwnerCellGramWith
        (R + 1) p sig (vfMidOneBlockActivePhysicalSite R) =
      vfMidActiveScaledClippedBaseCellMass R p sig := by
  rw [vfMidActiveCellGram_eq_scaledPolarizationCellMass hR hp]
  unfold vfMidActiveScaledPolarizationCellMass
    vfMidActiveScaledClippedBaseCellMass
  let F : ℕ → ℝ := fun a =>
    ∑ b ∈ lowOwnerFirstOwnerChildFiber (R + 1) p sig,
      (vfMidActiveMobiusScale R a *
        vfMidActiveMobiusScale R b) *
        lowOwnerFirstOwnerDirichletPolarizationAtom
          (R + 1) p (a, b / p)
  have hsplit :
      (∑ a ∈ lowOwnerFirstOwnerBaseFiber (R + 1) p sig, F a) =
        (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber (R + 1) p sig, F a) +
          ∑ a ∈ lowOwnerFirstOwnerClippedBaseFiber (R + 1) p sig, F a := by
    unfold lowOwnerFirstOwnerAdmittedBaseFiber
      lowOwnerFirstOwnerClippedBaseFiber
    simpa only [not_le] using
      (Finset.sum_filter_add_sum_filter_not
        (s := lowOwnerFirstOwnerBaseFiber (R + 1) p sig)
        (p := fun a => p * a ≤ squareRootEndpoint (R + 1))
        (f := F)).symm
  have hadm :
      (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber (R + 1) p sig, F a) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    unfold F
    rw [vfMidActiveMobiusScale_eq_zero_of_admittedBase hR hp ha]
    simp
  rw [Finset.product_eq_sprod, Finset.sum_product]
  change (∑ a ∈ lowOwnerFirstOwnerBaseFiber (R + 1) p sig, F a) =
    ∑ a ∈ lowOwnerFirstOwnerClippedBaseFiber (R + 1) p sig, F a
  rw [hsplit, hadm, zero_add]


/-! ## Return the child coordinate to the admitted parent -/

/-- The same clipped physical mass after returning every p-divisible child
`b` to its unique admitted parent `c = b / p`.  The physical VF scale stays
attached to the actual child site `p*c`. -/
def vfMidActiveScaledReturnedClippedCellMass
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  ∑ ac ∈
      (lowOwnerFirstOwnerClippedBaseFiber (R + 1) p sig).product
        (lowOwnerFirstOwnerAdmittedBaseFiber (R + 1) p sig),
    (vfMidActiveMobiusScale R ac.1 *
      vfMidActiveMobiusScale R (p * ac.2)) *
      lowOwnerFirstOwnerDirichletPolarizationAtom
        (R + 1) p ac

/-- Exact child-to-returned-parent reindexing.  No multiplicity is discarded:
multiplication by p and division by p are inverse on the actual child fibre. -/
theorem vfMidActiveScaledClippedBaseCellMass_eq_returned
    {R p : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) :
    vfMidActiveScaledClippedBaseCellMass R p sig =
      vfMidActiveScaledReturnedClippedCellMass R p sig := by
  unfold vfMidActiveScaledClippedBaseCellMass
    vfMidActiveScaledReturnedClippedCellMass
  rw [Finset.product_eq_sprod, Finset.sum_product,
    Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _ha
  refine Finset.sum_bij
    (fun b _hb => b / p)
    (fun b hb => lowOwnerFirstOwner_div_mem_admitted_of_child hp hb)
    ?_ ?_ ?_
  · intro b hb d hd heq
    have hbDvd := (Finset.mem_filter.mp hb).2.2
    have hdDvd := (Finset.mem_filter.mp hd).2.2
    change b / p = d / p at heq
    calc
      b = p * (b / p) := (Nat.mul_div_cancel' hbDvd).symm
      _ = p * (d / p) := by rw [heq]
      _ = d := Nat.mul_div_cancel' hdDvd
  · intro d hd
    refine ⟨p * d, lowOwnerFirstOwner_mul_mem_child_of_admitted hp hd, ?_⟩
    change (p * d) / p = d
    simpa [Nat.mul_comm] using Nat.mul_div_left d hp.pos
  · intro b hb
    have hbDvd := (Finset.mem_filter.mp hb).2.2
    have hcancel : p * (b / p) = b := Nat.mul_div_cancel' hbDvd
    rw [hcancel]

/-- Returned-coordinate version of the exact active cell support theorem. -/
theorem vfMidActiveCellGram_eq_scaledReturnedClippedCellMass
    {R p : ℕ} {sig : Finset ℕ}
    (hR : 3 ≤ R) (hp : p.Prime) :
    lowOwnerFirstOwnerCellGramWith
        (R + 1) p sig (vfMidOneBlockActivePhysicalSite R) =
      vfMidActiveScaledReturnedClippedCellMass R p sig := by
  rw [vfMidActiveCellGram_eq_scaledClippedBaseCellMass hR hp,
    vfMidActiveScaledClippedBaseCellMass_eq_returned hp]


end RHLean.Analysis

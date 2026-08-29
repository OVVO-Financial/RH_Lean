import Mathlib
import RHLean.Proof.CreationResponseOthelloInvolution
import RHLean.Proof.SquareRootLowPrimeCanonicalToggleRootCharge
import RHLean.Proof.SquareRootLowPrimeCanonicalLiberty
import RHLean.Proof.SquareRootLowPrimeGoGlobalPartner
import RHLean.Proof.SquareRootLowPrimeNoTogglePopulationBound
import RHLean.Proof.LowWheelCanonicalRepeatedParentClassification

/-!
# Opposite-fixed endpoint classification

This is the kernel-checking surface for the two-direction square-root Othello
closure.  The first new classification fact below closes the apparent
"frozen cofactor" case from the repeated-parent coordinate: such a state is
not fixed at all on the full physical transport carrier.  Its cofactor contains
a prime strictly above the canonical downcross pivot.  Removing that prime from
the cofactor and placing it in the quotient is the repository's existing
fixed-prime transport toggle, hence stays physical and reverses the signed
weight exactly.

Thus a genuinely fixed opposite endpoint cannot be a repeated frozen state with
nontrivial cofactor.  The remaining repeated terminal shape is the literal
Euler first-crossing boundary `c = 1`, `k = p`, with every face prime below `p`.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Sanity check that the canonical toggle carrier and the actual canonical
terminal carrier coexist in one current import graph. -/
theorem squareRootLowPrimeOppositeFixed_import_sanity
    (R K j U : ℕ) :
    squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier R K j U =
      squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier R K j U := by
  rfl

/-- **Frozen repeated-parent states are not opposite-fixed.**

If a repeated downcross has frozen quotient shape but nontrivial cofactor,
choose the least prime factor `q` of the cofactor.  The canonical downcross
pivot `p` cannot divide the cofactor, while `p = minFac(c*k)` is no larger than
`q`; hence `p < q`.  Moving `q` out of the squarefree cofactor and into the
quotient is an already-proved physical transport move, and it reverses the
Möbius/Boolean signed weight exactly.
-/
theorem lowWheelCanonicalRepeatedFrozenCofactor_has_opposite_transport_mate
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    ∃ q : ℕ,
      q.Prime ∧
      lowWheelTaggedDowncrossPivot y < q ∧
      q ∣ y.2.1 ∧
      LowWheelTransportPairCarrier R y.1
        (lowWheelCofactorQuotientToggleAt q y.2) ∧
      canonicalMoebiusWeight
          (lowWheelCofactorQuotientToggleAt q y.2).1 *
          (booleanCubeSign y.1 : ℂ) =
        -(canonicalMoebiusWeight y.2.1 *
          (booleanCubeSign y.1 : ℂ)) := by
  have hfrozen : y ∈ lowWheelCanonicalRepeatedFrozenPart R :=
    (Finset.mem_filter.mp hy).1
  have hcgt : 1 < y.2.1 := (Finset.mem_filter.mp hy).2
  have hrepeated : y ∈ lowWheelCanonicalDowncrossRepeatedParentPart R :=
    (Finset.mem_filter.mp hfrozen).1
  have htagged : y ∈ lowWheelCanonicalTaggedDowncrossCarrier R :=
    (Finset.mem_filter.mp hrepeated).1
  have hdowncross := (mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged).2
  have hshell := lowWheelCanonicalDowncrossPart_adjacent_shell hdowncross
  have hp : (lowWheelTaggedDowncrossPivot y).Prime := by
    simpa [lowWheelTaggedDowncrossPivot] using hshell.1
  have hpNotC : ¬ lowWheelTaggedDowncrossPivot y ∣ y.2.1 := by
    simpa [lowWheelTaggedDowncrossPivot] using hshell.2.1
  let q := Nat.minFac y.2.1
  have hqPrime : q.Prime := by
    simpa [q] using Nat.minFac_prime (by omega : y.2.1 ≠ 1)
  have hqDvdC : q ∣ y.2.1 := by
    simpa [q] using Nat.minFac_dvd y.2.1
  have hqDvdProd : q ∣ y.2.1 * y.2.2 :=
    dvd_mul_of_dvd_left hqDvdC y.2.2
  have hpLeQ : lowWheelTaggedDowncrossPivot y ≤ q := by
    have hmin := Nat.minFac_le_of_dvd hqPrime.two_le hqDvdProd
    simpa [lowWheelTaggedDowncrossPivot,
      lowWheelCanonicalCofactorQuotientPivot] using hmin
  have hpNeQ : lowWheelTaggedDowncrossPivot y ≠ q := by
    intro heq
    apply hpNotC
    rw [heq]
    exact hqDvdC
  have hpLtQ : lowWheelTaggedDowncrossPivot y < q :=
    lt_of_le_of_ne hpLeQ hpNeQ
  have hphysical : y.2 ∈ lowWheelCanonicalPhysicalStateSet R y.1 :=
    (mem_lowWheelCanonicalDowncrossPart.mp hdowncross).1
  have hsq : Squarefree y.2.1 :=
    (mem_lowWheelCanonicalPhysicalStateSet.mp hphysical).2.2.1
  have hcarrier : LowWheelTransportPairCarrier R y.1 y.2 :=
    (mem_lowWheelCanonicalPhysicalStateSet.mp hphysical).2.2.2
  have hmate : LowWheelTransportPairCarrier R y.1
      (lowWheelCofactorQuotientToggleAt q y.2) := by
    rcases y.2 with ⟨c, k⟩
    exact lowWheelCofactorQuotientToggleAt_preserves_of_dvd_cofactor
      hqPrime hcarrier hqDvdC
  have hneg :
      canonicalMoebiusWeight
          (lowWheelCofactorQuotientToggleAt q y.2).1 *
          (booleanCubeSign y.1 : ℂ) =
        -(canonicalMoebiusWeight y.2.1 *
          (booleanCubeSign y.1 : ℂ)) := by
    rcases y.2 with ⟨c, k⟩
    exact lowWheelCofactorQuotientToggleAt_weight_neg
      (t := y.1) hqPrime hsq (Or.inl hqDvdC)
  exact ⟨q, hqPrime, hpLtQ, hqDvdC, hmate, hneg⟩

end RHLean.Proof

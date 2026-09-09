import Mathlib
import RHLean.Proof.LowWheelCanonicalRepeatedTerminalCutoff
import RHLean.Proof.SquareRootLowPrimeGoCrossingMateLedger
import RHLean.Proof.LowWheelCanonicalFrozenReduction

/-!
# Existing physical mate for the internal repeated-parent terminal boundary

For a terminal state `y = (t,(1,p))` with `p <= R`, the prime `p` is still a
literal coordinate of the inclusive low-wheel cube.  Move that fresh prime into
the Boolean face and collapse the quotient:

`(t,(1,p)) -> (insert p t,(1,1))`.

The first-crossing inequalities are exactly what is needed for the mate to lie
in the already-existing physical transport ledger.  The cofactor remains one
and the Boolean sign flips once.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Terminal low-wheel mate obtained by moving the fresh prime into the Boolean
face. -/
def lowWheelCanonicalRepeatedTerminalInternalMate
    (y : LowWheelTaggedDowncrossState) : LowWheelTaggedCofactorQuotientState :=
  (insert (lowWheelTaggedDowncrossPivot y) y.1, (1, 1))

/-- On the internal terminal part, the fresh pivot is absent from the old face. -/
theorem lowWheelCanonicalRepeatedTerminalInternal_pivot_not_mem_face
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedTerminalInternalPart R) :
    lowWheelTaggedDowncrossPivot y ∉ y.1 := by
  have hterminal := (Finset.mem_filter.mp hy).1
  have hgeom := lowWheelCanonicalRepeatedTerminalBoundary_geometry hterminal
  intro hpMem
  have hlt := hgeom.2.2.2.1 _ hpMem
  exact Nat.lt_irrefl _ hlt

/-- The terminal mate is a literal occurrence of the existing physical
transport ledger. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMate_mem_transport
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedTerminalInternalPart R) :
    lowWheelCanonicalRepeatedTerminalInternalMate y ∈
      lowWheelCanonicalTaggedPhysicalCarrier R := by
  let p := lowWheelTaggedDowncrossPivot y
  have hterminal := (Finset.mem_filter.mp hy).1
  have hgeom := lowWheelCanonicalRepeatedTerminalBoundary_geometry hterminal
  have hp : p.Prime := by simpa [p] using hgeom.2.2.1
  have hpMem : p ∈ primesUpTo R := by
    simpa [p] using lowWheelCanonicalRepeatedTerminalInternal_pivot_mem_primesUpTo hy
  have hpNotFace : p ∉ y.1 := by
    simpa [p] using lowWheelCanonicalRepeatedTerminalInternal_pivot_not_mem_face hy
  have hfrozen := (Finset.mem_filter.mp hterminal).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have htag := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged
  have hfaceMate : insert p y.1 ∈ (primesUpTo R).powerset := by
    apply Finset.mem_powerset.mpr
    exact Finset.insert_subset hpMem (Finset.mem_powerset.mp htag.1)
  have hphysSource := (mem_lowWheelCanonicalDowncrossPart.mp htag.2).1
  have hsourceCarrier :=
    (mem_lowWheelCanonicalPhysicalStateSet.mp hphysSource).2.2.2
  have hRgt : 1 < R := by
    have hcR := hsourceCarrier.2.1
    simpa [hgeom.1] using hcR
  have hprodInsert : primeFaceProduct (insert p y.1) = p * primeFaceProduct y.1 := by
    simp [primeFaceProduct, hpNotFace]
  have hmateCarrier : LowWheelTransportPairCarrier R (insert p y.1) (1, 1) := by
    refine ⟨by simp, hRgt, ?_, ?_⟩
    · rw [hprodInsert]
      simpa [Nat.mul_comm] using hgeom.2.2.2.2.2
    · have htop := hsourceCarrier.2.2.2
      rw [hgeom.1, hgeom.2.1] at htop
      rw [hprodInsert]
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using htop
  have hranges := lowWheelTransportPairCarrier_mem_ranges hmateCarrier
  have hmatePhysical : (1, 1) ∈
      lowWheelCanonicalPhysicalStateSet R (insert p y.1) := by
    exact mem_lowWheelCanonicalPhysicalStateSet.mpr
      ⟨hranges.1, hranges.2, squarefree_one, hmateCarrier⟩
  apply mem_lowWheelCanonicalTaggedPhysicalCarrier.mpr
  simpa [lowWheelCanonicalRepeatedTerminalInternalMate, p] using
    And.intro hfaceMate hmatePhysical

/-- Moving the fresh prime into the Boolean face reverses exactly one Boolean
sign, hence the terminal source and existing mate have opposite weights. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMate_weight_neg
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedTerminalInternalPart R) :
    lowWheelTaggedCanonicalWeight
        (lowWheelCanonicalRepeatedTerminalInternalMate y) =
      -lowWheelTaggedCanonicalWeight (y.1, y.2) := by
  let p := lowWheelTaggedDowncrossPivot y
  have hterminal := (Finset.mem_filter.mp hy).1
  have hgeom := lowWheelCanonicalRepeatedTerminalBoundary_geometry hterminal
  have hpNotFace : p ∉ y.1 := by
    simpa [p] using lowWheelCanonicalRepeatedTerminalInternal_pivot_not_mem_face hy
  have hc : y.2.1 = 1 := hgeom.1
  have hsign : booleanCubeSign (insert p y.1) = -booleanCubeSign y.1 := by
    simp [booleanCubeSign, hpNotFace, pow_succ]
  simp [lowWheelTaggedCanonicalWeight,
    lowWheelCanonicalRepeatedTerminalInternalMate, hc, p, hsign]

/-- The mate is pointwise distinct from the terminal source because the fresh
prime was not already in the old Boolean face. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMate_ne
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedTerminalInternalPart R) :
    lowWheelCanonicalRepeatedTerminalInternalMate y ≠ (y.1, y.2) := by
  let p := lowWheelTaggedDowncrossPivot y
  have hpNotFace : p ∉ y.1 := by
    simpa [p] using lowWheelCanonicalRepeatedTerminalInternal_pivot_not_mem_face hy
  intro heq
  have hface := congrArg Prod.fst heq
  change insert p y.1 = y.1 at hface
  have hpInsert : p ∈ insert p y.1 := Finset.mem_insert_self p y.1
  rw [hface] at hpInsert
  exact hpNotFace hpInsert

/-! ## Global reassembly of the internal terminal mates -/

/-- The pointwise internal-terminal mate loses no multiplicity.  The fresh
pivot is the unique largest prime in the inserted face, so equality of mate
faces recovers both the pivot and the old face. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMate_injOn
    (R : ℕ) :
    Set.InjOn lowWheelCanonicalRepeatedTerminalInternalMate
      (lowWheelCanonicalRepeatedTerminalInternalPart R) := by
  intro y hy z hz heq
  let p := lowWheelTaggedDowncrossPivot y
  let q := lowWheelTaggedDowncrossPivot z
  have hyTerminal := (Finset.mem_filter.mp hy).1
  have hzTerminal := (Finset.mem_filter.mp hz).1
  have hyGeom := lowWheelCanonicalRepeatedTerminalBoundary_geometry hyTerminal
  have hzGeom := lowWheelCanonicalRepeatedTerminalBoundary_geometry hzTerminal
  have hpNot : p ∉ y.1 := by
    simpa [p] using lowWheelCanonicalRepeatedTerminalInternal_pivot_not_mem_face hy
  have hqNot : q ∉ z.1 := by
    simpa [q] using lowWheelCanonicalRepeatedTerminalInternal_pivot_not_mem_face hz
  have hface : insert p y.1 = insert q z.1 := by
    simpa [lowWheelCanonicalRepeatedTerminalInternalMate, p, q] using
      congrArg Prod.fst heq
  have hpRight : p ∈ insert q z.1 := by
    rw [← hface]
    exact Finset.mem_insert_self p y.1
  have hqLeft : q ∈ insert p y.1 := by
    rw [hface]
    exact Finset.mem_insert_self q z.1
  have hpq : p = q := by
    rcases Finset.mem_insert.mp hpRight with hpq | hpz
    · exact hpq
    · rcases Finset.mem_insert.mp hqLeft with hqp | hqy
      · exact hqp.symm
      · have hpLtQ : p < q := by
          simpa [q] using hzGeom.2.2.2.1 p hpz
        have hqLtP : q < p := by
          simpa [p] using hyGeom.2.2.2.1 q hqy
        omega
  have hfaceSame : insert p y.1 = insert p z.1 := by
    simpa [hpq] using hface
  have hbase : y.1 = z.1 := by
    have herase := congrArg (fun s : Finset ℕ => s.erase p) hfaceSame
    have hpNotZ : p ∉ z.1 := by simpa [hpq] using hqNot
    simpa [hpNot, hpNotZ] using herase
  have hstate : y.2 = z.2 := by
    apply Prod.ext
    · exact hyGeom.1.trans hzGeom.1.symm
    · calc
        y.2.2 = p := by simpa [p] using hyGeom.2.1
        _ = q := hpq
        _ = z.2.2 := by simpa [q] using hzGeom.2.1.symm
  exact Prod.ext hbase hstate

/-- Image of the internal repeated terminal boundary inside the existing tagged
physical transport carrier. -/
def lowWheelCanonicalRepeatedTerminalInternalMateImage
    (R : ℕ) : Finset LowWheelTaggedCofactorQuotientState :=
  (lowWheelCanonicalRepeatedTerminalInternalPart R).image
    lowWheelCanonicalRepeatedTerminalInternalMate

/-- Every image occurrence is a literal pre-existing transport occurrence. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMateImage_subset_transport
    (R : ℕ) :
    lowWheelCanonicalRepeatedTerminalInternalMateImage R ⊆
      lowWheelCanonicalTaggedPhysicalCarrier R := by
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  exact lowWheelCanonicalRepeatedTerminalInternalMate_mem_transport hy

/-- Signed mate ledger, kept on the source indexing until injectivity is used. -/
def lowWheelCanonicalRepeatedTerminalInternalMateLedger
    (R : ℕ) : ℂ :=
  ∑ y ∈ lowWheelCanonicalRepeatedTerminalInternalPart R,
    lowWheelTaggedCanonicalWeight
      (lowWheelCanonicalRepeatedTerminalInternalMate y)

/-- Injectivity turns the source-indexed mate ledger into the literal image
subledger of the global physical transport carrier. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMateLedger_eq_imageSum
    (R : ℕ) :
    lowWheelCanonicalRepeatedTerminalInternalMateLedger R =
      ∑ z ∈ lowWheelCanonicalRepeatedTerminalInternalMateImage R,
        lowWheelTaggedCanonicalWeight z := by
  unfold lowWheelCanonicalRepeatedTerminalInternalMateLedger
    lowWheelCanonicalRepeatedTerminalInternalMateImage
  rw [Finset.sum_image]
  intro a ha b hb hab
  exact lowWheelCanonicalRepeatedTerminalInternalMate_injOn R ha hb hab

/-- **Exact signed reassembly.**  The complete internal repeated-terminal
ledger cancels against its already-present transport mate subledger before any
norm is taken. -/
theorem sum_lowWheelCanonicalRepeatedTerminalInternal_add_mate_eq_zero
    (R : ℕ) :
    (∑ y ∈ lowWheelCanonicalRepeatedTerminalInternalPart R,
        lowWheelTaggedDowncrossWeight y) +
      lowWheelCanonicalRepeatedTerminalInternalMateLedger R = 0 := by
  unfold lowWheelCanonicalRepeatedTerminalInternalMateLedger
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro y hy
  have hneg := lowWheelCanonicalRepeatedTerminalInternalMate_weight_neg hy
  have hsame :
      lowWheelTaggedCanonicalWeight (y.1, y.2) =
        lowWheelTaggedDowncrossWeight y := by
    rfl
  rw [hneg, hsame]
  ring

/-- Existing frozen-reduction notation for the internal ledger, rewritten as
the negative of its concrete transport mate subledger. -/
theorem lowWheelCanonicalRepeatedTerminalInternalLedger_eq_neg_mateLedger
    (R : ℕ) :
    lowWheelCanonicalRepeatedTerminalInternalLedger R =
      -lowWheelCanonicalRepeatedTerminalInternalMateLedger R := by
  have h := sum_lowWheelCanonicalRepeatedTerminalInternal_add_mate_eq_zero R
  unfold lowWheelCanonicalRepeatedTerminalInternalLedger at h
  linear_combination h

/-- **Transport-only normal form of the frozen/top/far residual.**  The old
internal terminal term is absorbed by its already-present transport mates, and
the far survivor is restored to the equivalent far-prime transport coordinate.
No norm is taken:

`FrozenTopFarResidual = FarTransport - InternalMate - TopImage`. -/
theorem lowWheelFrozenTopFarResidual_eq_farTransport_sub_internalMate_sub_topImage
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelFrozenTopFarResidual R =
      squareRootFarPrimeTransport R -
        lowWheelCanonicalRepeatedTerminalInternalMateLedger R -
        lowWheelFrozenCofactorTopImageLedger R := by
  unfold lowWheelFrozenTopFarResidual
  rw [lowWheelCanonicalRepeatedTerminalInternalLedger_eq_neg_mateLedger R,
    survivorSixteenFarUpperPrimeMass_pred_eq_neg_farTransport R hR]
  ring

end RHLean.Proof

import Mathlib
import RHLean.Proof.LowWheelCanonicalRepeatedMovableToggle

/-!
# Exact cancellation of movable repeated-parent downcross fibres

The lifted face/tail toggle preserves the canonical pivot and root-side parent.
This file proves that it also preserves the literal downcross carrier.  Because
the canonical mover is selected only from those two invariant coordinates, the
same mover is selected after the first flip.  The resulting self-map is therefore
a genuine fixed-point-free sign-reversing involution on the entire movable
repeated-parent population.

Hence that whole population has signed mass exactly zero.  The repeated-parent
obstruction is reduced, before any norm is taken, to the two frozen classes from
`LowWheelCanonicalRepeatedParentClassification`.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The full high coordinate `P(t)*k` is invariant under every legal lifted
face/tail transfer. -/
theorem lowWheelTaggedDowncrossFaceTailToggleAt_faceQuotientProduct
    {R q : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalTaggedDowncrossCarrier R)
    (_hq : LowWheelDowncrossMovablePrime y q) :
    primeFaceProduct (lowWheelTaggedDowncrossFaceTailToggleAt q y).1 *
        (lowWheelTaggedDowncrossFaceTailToggleAt q y).2.2 =
      primeFaceProduct y.1 * y.2.2 := by
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hy with ⟨_ht, hx⟩
  rcases lowWheelCanonicalDowncrossPart_adjacent_shell hx with
    ⟨_hp, _hpc, hpk, _hdown, _hup⟩
  let p := lowWheelTaggedDowncrossPivot y
  have hpk' : p ∣ y.2.2 := by
    simpa [p, lowWheelTaggedDowncrossPivot] using hpk
  have hlocal := lowWheelFaceTailToggleAt_product q
    (y.1, y.2.2 / p)
  change
    primeFaceProduct
        (lowWheelFaceTailToggleAt q (y.1, y.2.2 / p)).1 *
      (p * (lowWheelFaceTailToggleAt q (y.1, y.2.2 / p)).2) =
    primeFaceProduct y.1 * y.2.2
  calc
    primeFaceProduct
          (lowWheelFaceTailToggleAt q (y.1, y.2.2 / p)).1 *
        (p * (lowWheelFaceTailToggleAt q (y.1, y.2.2 / p)).2) =
      p *
        (primeFaceProduct
          (lowWheelFaceTailToggleAt q (y.1, y.2.2 / p)).1 *
          (lowWheelFaceTailToggleAt q (y.1, y.2.2 / p)).2) := by ring
    _ = p * (primeFaceProduct y.1 * (y.2.2 / p)) := by rw [hlocal]
    _ = primeFaceProduct y.1 * (p * (y.2.2 / p)) := by ring
    _ = primeFaceProduct y.1 * y.2.2 := by
      rw [Nat.mul_div_cancel' hpk']

/-- A legal lifted transfer keeps the Boolean face inside the global low-prime
cube. -/
theorem lowWheelTaggedDowncrossFaceTailToggleAt_face_mem
    {R q : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalTaggedDowncrossCarrier R)
    (hq : LowWheelDowncrossMovablePrime y q) :
    (lowWheelTaggedDowncrossFaceTailToggleAt q y).1 ∈
      (primesUpTo R).powerset := by
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hy with ⟨ht, _hx⟩
  have hqCandidate := lowWheelDowncrossMovablePrime_mem_candidateSet hy hq
  have hqGlobal :=
    (mem_lowWheelCanonicalDowncrossMovablePrimeSet.mp hqCandidate).1
  have htSub := Finset.mem_powerset.mp ht
  change
    (lowWheelFaceTailToggleAt q
      (y.1, y.2.2 / lowWheelTaggedDowncrossPivot y)).1 ∈
      (primesUpTo R).powerset
  by_cases hqt : q ∈ y.1
  · simp only [lowWheelFaceTailToggleAt, hqt, if_true]
    apply Finset.mem_powerset.mpr
    intro r hr
    exact htSub (Finset.mem_of_mem_erase hr)
  · have hqm : q ∣ y.2.2 / lowWheelTaggedDowncrossPivot y :=
      hq.2.2.resolve_left hqt
    simp only [lowWheelFaceTailToggleAt, hqt, if_false, hqm, if_true]
    apply Finset.mem_powerset.mpr
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact hqGlobal
    · exact htSub hr

/-- The physical transport state remains physical: cofactor is unchanged and
the complete face/quotient product is invariant. -/
theorem lowWheelTaggedDowncrossFaceTailToggleAt_mem_physical
    {R q : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalTaggedDowncrossCarrier R)
    (hq : LowWheelDowncrossMovablePrime y q) :
    (lowWheelTaggedDowncrossFaceTailToggleAt q y).2 ∈
      lowWheelCanonicalPhysicalStateSet R
        (lowWheelTaggedDowncrossFaceTailToggleAt q y).1 := by
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hy with ⟨_ht, hx⟩
  rcases mem_lowWheelCanonicalDowncrossPart.mp hx with
    ⟨hxPhysical, _hpc, _hdown⟩
  rcases mem_lowWheelCanonicalPhysicalStateSet.mp hxPhysical with
    ⟨hcRange, _hkRange, hsq, hcarrier⟩
  have hprod :=
    lowWheelTaggedDowncrossFaceTailToggleAt_faceQuotientProduct hy hq
  have hcEq := lowWheelTaggedDowncrossFaceTailToggleAt_cofactor q y
  have hcarrierNew :
      LowWheelTransportPairCarrier R
        (lowWheelTaggedDowncrossFaceTailToggleAt q y).1
        (lowWheelTaggedDowncrossFaceTailToggleAt q y).2 := by
    rcases hcarrier with ⟨hc1, hcR, hhigh, htop⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [hcEq] using hc1
    · simpa [hcEq] using hcR
    · rw [hprod]
      exact hhigh
    · calc
        ((lowWheelTaggedDowncrossFaceTailToggleAt q y).2.1 *
            primeFaceProduct
              (lowWheelTaggedDowncrossFaceTailToggleAt q y).1) *
            (lowWheelTaggedDowncrossFaceTailToggleAt q y).2.2 =
          y.2.1 *
            (primeFaceProduct
              (lowWheelTaggedDowncrossFaceTailToggleAt q y).1 *
              (lowWheelTaggedDowncrossFaceTailToggleAt q y).2.2) := by
                rw [hcEq]
                ring
        _ = y.2.1 * (primeFaceProduct y.1 * y.2.2) := by rw [hprod]
        _ = (y.2.1 * primeFaceProduct y.1) * y.2.2 := by ring
        _ ≤ squareRootEndpoint R := htop
  have hranges := lowWheelTransportPairCarrier_mem_ranges hcarrierNew
  apply mem_lowWheelCanonicalPhysicalStateSet.mpr
  refine ⟨hranges.1, hranges.2, ?_, hcarrierNew⟩
  simpa [hcEq] using hsq

/-- A legal lifted move stays on the literal canonical downcross carrier. -/
theorem lowWheelTaggedDowncrossFaceTailToggleAt_mem
    {R q : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalTaggedDowncrossCarrier R)
    (hq : LowWheelDowncrossMovablePrime y q) :
    lowWheelTaggedDowncrossFaceTailToggleAt q y ∈
      lowWheelCanonicalTaggedDowncrossCarrier R := by
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hy with ⟨_ht, hx⟩
  rcases mem_lowWheelCanonicalDowncrossPart.mp hx with
    ⟨_hxPhysical, hpc, hdown⟩
  have hpivot := lowWheelTaggedDowncrossFaceTailToggleAt_pivot hy hq
  have hparent := lowWheelTaggedDowncrossFaceTailToggleAt_parent hy hq
  apply mem_lowWheelCanonicalTaggedDowncrossCarrier.mpr
  refine ⟨lowWheelTaggedDowncrossFaceTailToggleAt_face_mem hy hq, ?_⟩
  apply mem_lowWheelCanonicalDowncrossPart.mpr
  refine ⟨lowWheelTaggedDowncrossFaceTailToggleAt_mem_physical hy hq, ?_, ?_⟩
  · intro hdiv
    apply hpc
    rw [← hpivot]
    simpa using hdiv
  · change lowWheelCanonicalDowncrossParent
        (lowWheelTaggedDowncrossFaceTailToggleAt q y) ≤ R
    rw [hparent]
    exact hdown

/-- The same coordinate remains movable after the lifted move. -/
theorem lowWheelTaggedDowncrossFaceTailToggleAt_movable
    {R q : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalTaggedDowncrossCarrier R)
    (hq : LowWheelDowncrossMovablePrime y q) :
    LowWheelDowncrossMovablePrime
      (lowWheelTaggedDowncrossFaceTailToggleAt q y) q := by
  have hpivot := lowWheelTaggedDowncrossFaceTailToggleAt_pivot hy hq
  have hyData := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hy
  have hshell := lowWheelCanonicalDowncrossPart_adjacent_shell hyData.2
  have hp : (lowWheelTaggedDowncrossPivot y).Prime := by
    simpa [lowWheelTaggedDowncrossPivot] using hshell.1
  have hactive := lowWheelFaceTailToggleAt_active hq.2.2
  refine ⟨hq.1, ?_, ?_⟩
  · rw [hpivot]
    exact hq.2.1
  · change q ∈
        (lowWheelFaceTailToggleAt q
          (y.1, y.2.2 / lowWheelTaggedDowncrossPivot y)).1 ∨
      q ∣
        (lowWheelTaggedDowncrossPivot y *
          (lowWheelFaceTailToggleAt q
            (y.1, y.2.2 / lowWheelTaggedDowncrossPivot y)).2) /
          lowWheelTaggedDowncrossPivot
            (lowWheelTaggedDowncrossFaceTailToggleAt q y)
    rw [hpivot, Nat.mul_div_left _ hp.pos]
    exact hactive

/-- Every legal lifted transfer is nontrivial because it changes the Boolean
face. -/
theorem lowWheelTaggedDowncrossFaceTailToggleAt_ne
    {R q : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalTaggedDowncrossCarrier R)
    (hq : LowWheelDowncrossMovablePrime y q) :
    lowWheelTaggedDowncrossFaceTailToggleAt q y ≠ y := by
  intro heq
  have hface := congrArg Prod.fst heq
  change
    (lowWheelFaceTailToggleAt q
      (y.1, y.2.2 / lowWheelTaggedDowncrossPivot y)).1 = y.1 at hface
  exact (lowWheelFaceTailToggleAt_fst_ne_of_active hq.2.2) hface

/-- A movable repeated-parent state remains repeated after the lifted move,
because the original state is a distinct state with the same parent. -/
theorem lowWheelTaggedDowncrossFaceTailToggleAt_mem_repeated
    {R q : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedMovablePart R)
    (hq : LowWheelDowncrossMovablePrime y q) :
    lowWheelTaggedDowncrossFaceTailToggleAt q y ∈
      lowWheelCanonicalDowncrossRepeatedParentPart R := by
  have hyRepeated := (Finset.mem_filter.mp hy).1
  have hyCarrier := (Finset.mem_filter.mp hyRepeated).1
  have hnewCarrier := lowWheelTaggedDowncrossFaceTailToggleAt_mem hyCarrier hq
  have hparent := lowWheelTaggedDowncrossFaceTailToggleAt_parent hyCarrier hq
  have hne := lowWheelTaggedDowncrossFaceTailToggleAt_ne hyCarrier hq
  apply Finset.mem_filter.mpr
  refine ⟨hnewCarrier, ?_⟩
  intro huniq
  have hback : y = lowWheelTaggedDowncrossFaceTailToggleAt q y :=
    huniq y hyCarrier hparent.symm
  exact hne hback.symm

/-- Therefore the lifted move preserves the movable repeated-parent region. -/
theorem lowWheelTaggedDowncrossFaceTailToggleAt_mem_movablePart
    {R q : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedMovablePart R)
    (hq : LowWheelDowncrossMovablePrime y q) :
    lowWheelTaggedDowncrossFaceTailToggleAt q y ∈
      lowWheelCanonicalRepeatedMovablePart R := by
  apply Finset.mem_filter.mpr
  exact ⟨lowWheelTaggedDowncrossFaceTailToggleAt_mem_repeated hy hq,
    ⟨q, lowWheelTaggedDowncrossFaceTailToggleAt_movable
      (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).1 hq⟩⟩

/-- The invariant candidate set is unchanged by a legal lifted move. -/
theorem lowWheelCanonicalDowncrossMovablePrimeSet_toggle
    {R q : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalTaggedDowncrossCarrier R)
    (hq : LowWheelDowncrossMovablePrime y q) :
    lowWheelCanonicalDowncrossMovablePrimeSet R
        (lowWheelTaggedDowncrossFaceTailToggleAt q y) =
      lowWheelCanonicalDowncrossMovablePrimeSet R y := by
  have hpivot := lowWheelTaggedDowncrossFaceTailToggleAt_pivot hy hq
  have hparent := lowWheelTaggedDowncrossFaceTailToggleAt_parent hy hq
  unfold lowWheelCanonicalDowncrossMovablePrimeSet
  rw [hpivot, hparent]

/-- Consequently the canonical least mover is itself invariant. -/
theorem lowWheelCanonicalDowncrossMover_toggle
    {R q : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalTaggedDowncrossCarrier R)
    (hq : LowWheelDowncrossMovablePrime y q) :
    lowWheelCanonicalDowncrossMover R
        (lowWheelTaggedDowncrossFaceTailToggleAt q y) =
      lowWheelCanonicalDowncrossMover R y := by
  unfold lowWheelCanonicalDowncrossMover
  rw [lowWheelCanonicalDowncrossMovablePrimeSet_toggle hy hq]

/-- The lifted fixed-coordinate move is an involution on a genuine downcross
state. -/
theorem lowWheelTaggedDowncrossFaceTailToggleAt_involutive
    {R q : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalTaggedDowncrossCarrier R)
    (hq : LowWheelDowncrossMovablePrime y q) :
    lowWheelTaggedDowncrossFaceTailToggleAt q
        (lowWheelTaggedDowncrossFaceTailToggleAt q y) = y := by
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hy with ⟨_ht, hx⟩
  rcases lowWheelCanonicalDowncrossPart_adjacent_shell hx with
    ⟨hpRaw, _hpc, hpkRaw, _hdown, _hup⟩
  let p := lowWheelTaggedDowncrossPivot y
  let x : LowWheelFaceTailState := (y.1, y.2.2 / p)
  have hp : p.Prime := by
    simpa [p, lowWheelTaggedDowncrossPivot] using hpRaw
  have hpk : p ∣ y.2.2 := by
    simpa [p, lowWheelTaggedDowncrossPivot] using hpkRaw
  have hpivot :
      lowWheelTaggedDowncrossPivot
          (lowWheelTaggedDowncrossFaceTailToggleAt q y) = p := by
    simpa [p] using lowWheelTaggedDowncrossFaceTailToggleAt_pivot hy hq
  have hinv := lowWheelFaceTailToggleAt_involutive hq.1.pos x
  have hcancel : p * (y.2.2 / p) = y.2.2 := Nat.mul_div_cancel' hpk
  change
    (let p' := lowWheelTaggedDowncrossPivot
        (lowWheelTaggedDowncrossFaceTailToggleAt q y)
      let z' := lowWheelFaceTailToggleAt q
        ((lowWheelTaggedDowncrossFaceTailToggleAt q y).1,
          (lowWheelTaggedDowncrossFaceTailToggleAt q y).2.2 / p')
      (z'.1,
        ((lowWheelTaggedDowncrossFaceTailToggleAt q y).2.1, p' * z'.2))) = y
  rw [hpivot]
  change
    (let z' := lowWheelFaceTailToggleAt q
        ((lowWheelFaceTailToggleAt q x).1,
          (p * (lowWheelFaceTailToggleAt q x).2) / p)
      (z'.1, (y.2.1, p * z'.2))) = y
  rw [Nat.mul_div_left _ hp.pos]
  change
    (let z' := lowWheelFaceTailToggleAt q
        (lowWheelFaceTailToggleAt q x)
      (z'.1, (y.2.1, p * z'.2))) = y
  rw [hinv]
  change (x.1, (y.2.1, p * x.2)) = y
  dsimp [x]
  rw [hcancel]

/-- The lifted move reverses the signed tagged-downcross weight. -/
theorem lowWheelTaggedDowncrossFaceTailToggleAt_weight_neg
    {R q : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalTaggedDowncrossCarrier R)
    (hq : LowWheelDowncrossMovablePrime y q) :
    lowWheelTaggedDowncrossWeight
        (lowWheelTaggedDowncrossFaceTailToggleAt q y) =
      -lowWheelTaggedDowncrossWeight y := by
  unfold lowWheelTaggedDowncrossWeight
  have hcEq := lowWheelTaggedDowncrossFaceTailToggleAt_cofactor q y
  rw [hcEq]
  change canonicalMoebiusWeight y.2.1 *
      (booleanCubeSign
        (lowWheelFaceTailToggleAt q
          (y.1, y.2.2 / lowWheelTaggedDowncrossPivot y)).1 : ℂ) =
    -(canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ))
  exact lowWheelFaceTailToggleAt_weight_neg
    (canonicalMoebiusWeight y.2.1) hq.2.2

/-- Canonical opposite mate on the movable repeated-parent population. -/
noncomputable def lowWheelCanonicalRepeatedMovableMate
    (R : ℕ) (y : LowWheelTaggedDowncrossState) :
    LowWheelTaggedDowncrossState :=
  lowWheelTaggedDowncrossFaceTailToggleAt
    (lowWheelCanonicalDowncrossMover R y) y

/-- The canonical mate preserves the movable repeated-parent carrier. -/
theorem lowWheelCanonicalRepeatedMovableMate_mem
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedMovablePart R) :
    lowWheelCanonicalRepeatedMovableMate R y ∈
      lowWheelCanonicalRepeatedMovablePart R := by
  unfold lowWheelCanonicalRepeatedMovableMate
  exact lowWheelTaggedDowncrossFaceTailToggleAt_mem_movablePart hy
    (lowWheelCanonicalDowncrossMover_movable hy)

/-- The canonical mate is fixed-point-free. -/
theorem lowWheelCanonicalRepeatedMovableMate_ne
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedMovablePart R) :
    lowWheelCanonicalRepeatedMovableMate R y ≠ y := by
  unfold lowWheelCanonicalRepeatedMovableMate
  have hyCarrier := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).1
  exact lowWheelTaggedDowncrossFaceTailToggleAt_ne hyCarrier
    (lowWheelCanonicalDowncrossMover_movable hy)

/-- The canonical mover is the same after the first mate, so the mate is a true
involution. -/
theorem lowWheelCanonicalRepeatedMovableMate_involutive
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedMovablePart R) :
    lowWheelCanonicalRepeatedMovableMate R
        (lowWheelCanonicalRepeatedMovableMate R y) = y := by
  let q := lowWheelCanonicalDowncrossMover R y
  have hyCarrier := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).1
  have hq := lowWheelCanonicalDowncrossMover_movable hy
  have hmover :
      lowWheelCanonicalDowncrossMover R
          (lowWheelTaggedDowncrossFaceTailToggleAt q y) = q := by
    simpa [q] using lowWheelCanonicalDowncrossMover_toggle hyCarrier hq
  unfold lowWheelCanonicalRepeatedMovableMate
  change lowWheelTaggedDowncrossFaceTailToggleAt
      (lowWheelCanonicalDowncrossMover R
        (lowWheelTaggedDowncrossFaceTailToggleAt q y))
      (lowWheelTaggedDowncrossFaceTailToggleAt q y) = y
  rw [hmover]
  exact lowWheelTaggedDowncrossFaceTailToggleAt_involutive hyCarrier hq

/-- The canonical mate reverses the signed weight. -/
theorem lowWheelCanonicalRepeatedMovableMate_weight_neg
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedMovablePart R) :
    lowWheelTaggedDowncrossWeight (lowWheelCanonicalRepeatedMovableMate R y) =
      -lowWheelTaggedDowncrossWeight y := by
  unfold lowWheelCanonicalRepeatedMovableMate
  have hyCarrier := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).1
  exact lowWheelTaggedDowncrossFaceTailToggleAt_weight_neg hyCarrier
    (lowWheelCanonicalDowncrossMover_movable hy)

/-- **Exact movable-fibre cancellation.**  Every non-frozen repeated-parent
state disappears under the canonical opposite Othello involution. -/
theorem sum_lowWheelCanonicalRepeatedMovablePart_eq_zero
    (R : ℕ) :
    (∑ y ∈ lowWheelCanonicalRepeatedMovablePart R,
      lowWheelTaggedDowncrossWeight y) = 0 := by
  exact Finset.sum_involution
    (s := lowWheelCanonicalRepeatedMovablePart R)
    (f := lowWheelTaggedDowncrossWeight)
    (fun y _hy => lowWheelCanonicalRepeatedMovableMate R y)
    (fun y hy => by
      rw [lowWheelCanonicalRepeatedMovableMate_weight_neg hy]
      simp)
    (fun y hy _ => lowWheelCanonicalRepeatedMovableMate_ne hy)
    (fun y hy => lowWheelCanonicalRepeatedMovableMate_mem hy)
    (fun y hy => lowWheelCanonicalRepeatedMovableMate_involutive hy)

end RHLean.Proof

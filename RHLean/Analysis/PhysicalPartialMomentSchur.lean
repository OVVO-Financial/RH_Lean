import Mathlib
import RHLean.Analysis.PartialMomentSchurTarget
import RHLean.Analysis.PhysicalDegreeOneTransitionEstimate
import RHLean.Analysis.PhysicalSquareCRTPeriodNoGo

/-!
# Physical T-row partial moments and Schur target invariance

This module instantiates the arbitrary-target partial-moment identity on the
actual eight-state zero-free physical transition rows.  The observations are
the three Mobius sign coordinates of the destination state and the weights are
the exact transition counts `N_{u,v}(K)`.

The resulting target second moment therefore admits the exact four-block
reassembly for every target, while its scaled Schur covariance is independent
of target.  The final statements identify the Mertens-visible degree-one row
mass with the corresponding first-moment projection and show exactly where a
target shift goes: into the rank-one first-moment term, not into the Schur
covariance.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

/-- Three physical Mobius coordinates of a ternary state, cast to `ℝ`. -/
def physicalThreeCoordinateVector (v : Fin 27) : Fin 3 → ℝ :=
  fun i =>
    if i.1 = 0 then ((chiA v : ℤ) : ℝ)
    else if i.1 = 1 then ((chiB v : ℤ) : ℝ)
    else ((chiC v : ℤ) : ℝ)

@[simp] theorem physicalThreeCoordinateVector_zero (v : Fin 27) :
    physicalThreeCoordinateVector v 0 = ((chiA v : ℤ) : ℝ) := by
  simp [physicalThreeCoordinateVector]

@[simp] theorem physicalThreeCoordinateVector_one (v : Fin 27) :
    physicalThreeCoordinateVector v 1 = ((chiB v : ℤ) : ℝ) := by
  simp [physicalThreeCoordinateVector]

@[simp] theorem physicalThreeCoordinateVector_two (v : Fin 27) :
    physicalThreeCoordinateVector v 2 = ((chiC v : ℤ) : ℝ) := by
  simp [physicalThreeCoordinateVector]

/-- Exact transition-count weight in one physical source row. -/
def physicalTRowWeight (K : ℕ) (u v : Fin 27) : ℝ :=
  (physicalTransitionN K u v : ℝ)

/-- Arbitrary-target first moment of one physical zero-free destination row. -/
def physicalTRowTargetFirstMoment
    (K : ℕ) (u : Fin 27) (t : Fin 3 → ℝ) : Fin 3 → ℝ :=
  finiteTargetFirstMoment physicalThreeSlotNonzeroStates
    (physicalTRowWeight K u) physicalThreeCoordinateVector t

/-- Arbitrary-target second-moment matrix of one physical zero-free destination row. -/
def physicalTRowTargetSecondMoment
    (K : ℕ) (u : Fin 27) (t : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  finiteTargetSecondMoment physicalThreeSlotNonzeroStates
    (physicalTRowWeight K u) physicalThreeCoordinateVector t

/-- Physical row co-lower partial moment. -/
def physicalTRowCLPM
    (K : ℕ) (u : Fin 27) (t : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  finiteCLPM physicalThreeSlotNonzeroStates
    (physicalTRowWeight K u) physicalThreeCoordinateVector t

/-- Physical row co-upper partial moment. -/
def physicalTRowCUPM
    (K : ℕ) (u : Fin 27) (t : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  finiteCUPM physicalThreeSlotNonzeroStates
    (physicalTRowWeight K u) physicalThreeCoordinateVector t

/-- Physical row divergent lower-to-upper partial moment. -/
def physicalTRowDLPM
    (K : ℕ) (u : Fin 27) (t : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  finiteDLPM physicalThreeSlotNonzeroStates
    (physicalTRowWeight K u) physicalThreeCoordinateVector t

/-- Physical row divergent upper-to-lower partial moment. -/
def physicalTRowDUPM
    (K : ℕ) (u : Fin 27) (t : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  finiteDUPM physicalThreeSlotNonzeroStates
    (physicalTRowWeight K u) physicalThreeCoordinateVector t

/-- **Physical arbitrary-target PM reassembly.** -/
theorem physicalTRowTargetSecondMoment_eq_partial_reassembly
    (K : ℕ) (u : Fin 27) (t : Fin 3 → ℝ) :
    physicalTRowTargetSecondMoment K u t =
      physicalTRowCLPM K u t + physicalTRowCUPM K u t -
        physicalTRowDLPM K u t - physicalTRowDUPM K u t := by
  exact finiteTargetSecondMoment_eq_partial_reassembly
    physicalThreeSlotNonzeroStates (physicalTRowWeight K u)
      physicalThreeCoordinateVector t

/-- Scaled Schur covariance of one physical destination row. -/
def physicalTRowScaledSchur
    (K : ℕ) (u : Fin 27) (t : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  finiteTargetScaledSchur physicalThreeSlotNonzeroStates
    (physicalTRowWeight K u) physicalThreeCoordinateVector t

/-- **The physical row Schur covariance is exactly target invariant.** -/
theorem physicalTRowScaledSchur_target_invariant
    (K : ℕ) (u : Fin 27) (s t : Fin 3 → ℝ) :
    physicalTRowScaledSchur K u t = physicalTRowScaledSchur K u s := by
  exact finiteTargetScaledSchur_target_invariant
    physicalThreeSlotNonzeroStates (physicalTRowWeight K u)
      physicalThreeCoordinateVector s t

/-- Mertens-visible degree-one functional on the three physical coordinates. -/
def physicalDegreeOneFunctional (z : Fin 3 → ℝ) : ℝ :=
  z 0 + z 1 + z 2

/-- The physical coordinate vector recombines to the repository's degree-one
 observable. -/
theorem physicalDegreeOneFunctional_coordinateVector (v : Fin 27) :
    physicalDegreeOneFunctional (physicalThreeCoordinateVector v) =
      ((threeSlotDegreeOneValue v : ℤ) : ℝ) := by
  simp [physicalDegreeOneFunctional, physicalThreeCoordinateVector,
    threeSlotDegreeOneValue]

/-- Apply the degree-one functional to a physical row first moment. -/
def physicalTRowTargetDegreeOneFirstMoment
    (K : ℕ) (u : Fin 27) (t : Fin 3 → ℝ) : ℝ :=
  physicalDegreeOneFunctional (physicalTRowTargetFirstMoment K u t)

/-- The zero-target degree-one first moment is exactly the physical row
 transition moment against `threeSlotDegreeOneValue`. -/
theorem physicalTRowTargetDegreeOneFirstMoment_zero
    (K : ℕ) (u : Fin 27) :
    physicalTRowTargetDegreeOneFirstMoment K u (fun _ => 0) =
      ((threeSlotTransitionMomentOn
          (Finset.range K) u threeSlotDegreeOneValue : ℤ) : ℝ) := by
  unfold physicalTRowTargetDegreeOneFirstMoment physicalDegreeOneFunctional
    physicalTRowTargetFirstMoment finiteTargetFirstMoment physicalTRowWeight
  simp only [physicalThreeCoordinateVector_zero,
    physicalThreeCoordinateVector_one, physicalThreeCoordinateVector_two,
    sub_zero]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  simp [physicalThreeSlotNonzeroStates, physicalTransitionN,
    threeSlotTransitionCount, threeSlotTransitionMomentOn,
    threeSlotDegreeOneValue]
  ring

/-- **Exact target-shift law for the hard degree-one row mass.**  The Schur
 covariance is target invariant, but the Mertens-visible first moment is not
 discarded: shifting target by `t` moves precisely row-mass times the degree-one
 target projection into the rank-one first-moment block. -/
theorem physicalTRowTargetDegreeOneFirstMoment_eq_zeroTarget_sub
    (K : ℕ) (u : Fin 27) (t : Fin 3 → ℝ) :
    physicalTRowTargetDegreeOneFirstMoment K u t =
      physicalTRowTargetDegreeOneFirstMoment K u (fun _ => 0) -
        finiteTotalWeight physicalThreeSlotNonzeroStates
          (physicalTRowWeight K u) * physicalDegreeOneFunctional t := by
  have h0 := finiteTargetFirstMoment_target_shift
    physicalThreeSlotNonzeroStates (physicalTRowWeight K u)
      physicalThreeCoordinateVector (fun _ : Fin 3 => 0) t
  unfold physicalTRowTargetDegreeOneFirstMoment physicalTRowTargetFirstMoment
    physicalDegreeOneFunctional
  have hzero := h0 (0 : Fin 3)
  have hone := h0 (1 : Fin 3)
  have htwo := h0 (2 : Fin 3)
  simp at hzero hone htwo
  linarith

/-! ## Finite q^2 affine-contact incidence frame

This section deliberately proves only the finite tag geometry.  It does not
identify the tag-dependent affine pullback field with the recovered Mobius
daughter.  That reconstruction is the separate arithmetic seam exposed by the
q=3 no-go result.
-/

/-- The four residue labels seen by the six affine offsets modulo four. -/
abbrev Q2AffineResidue := Fin 4

/-- Residue label attached to one of the six physical contact offsets. -/
def q2AffineContactResidue (a : ℕ) : Q2AffineResidue :=
  ⟨a % 4, Nat.mod_lt _ (by norm_num)⟩

/-- Incidence pullback of a four-coordinate test field by one affine tag. -/
def q2AffineTagPullback (a : ℕ) (x : Q2AffineResidue → ℚ) : ℚ :=
  x (q2AffineContactResidue a)

/-- Energy after all six affine tags read the finite incidence field. -/
def q2AffineTagEnergy (x : Q2AffineResidue → ℚ) : ℚ :=
  ∑ a ∈ physicalTransitionActiveOffsets, (q2AffineTagPullback a x) ^ 2

/-- Ambient energy on the four residue labels. -/
def q2AffineResidueEnergy (x : Q2AffineResidue → ℚ) : ℚ :=
  ∑ r : Q2AffineResidue, (x r) ^ 2

/-- Finite incidence Gram of the six affine tags. -/
def q2AffineGram : Matrix Q2AffineResidue Q2AffineResidue ℚ := fun r s =>
  ∑ a ∈ physicalTransitionActiveOffsets,
    (if q2AffineContactResidue a = r then (1 : ℚ) else 0) *
      (if q2AffineContactResidue a = s then (1 : ℚ) else 0)

/-- The six offsets occupy exactly the three nonzero residue labels. -/
theorem physicalTransitionActiveOffsets_contactResidues :
    physicalTransitionActiveOffsets.image q2AffineContactResidue =
      ({(1 : Q2AffineResidue), (2 : Q2AffineResidue), (3 : Q2AffineResidue)} :
        Finset Q2AffineResidue) := by
  native_decide

/-- Every finite residue label is represented by at most two of the six tags. -/
theorem physicalTransitionActiveOffsets_residueFiber_card_le_two
    (r : Q2AffineResidue) :
    (physicalTransitionActiveOffsets.filter fun a =>
      q2AffineContactResidue a = r).card ≤ 2 := by
  fin_cases r <;> native_decide

/-- Explicit finite Gram: zero residue is absent and each nonzero residue occurs twice. -/
theorem q2AffineGram_entries (r s : Q2AffineResidue) :
    q2AffineGram r s =
      if r = s then (if r = (0 : Q2AffineResidue) then 0 else 2) else 0 := by
  fin_cases r <;> fin_cases s <;> native_decide

/-- The six-tag incidence energy is exactly twice the energy on residues 1,2,3. -/
theorem q2AffineTagEnergy_eq
    (x : Q2AffineResidue → ℚ) :
    q2AffineTagEnergy x =
      2 * ((x (1 : Q2AffineResidue)) ^ 2 +
        (x (2 : Q2AffineResidue)) ^ 2 +
        (x (3 : Q2AffineResidue)) ^ 2) := by
  simp [q2AffineTagEnergy, q2AffineTagPullback,
    q2AffineContactResidue, physicalTransitionActiveOffsets]
  ring

/-- The ambient four-residue energy is the sum of four coordinate squares. -/
theorem q2AffineResidueEnergy_eq
    (x : Q2AffineResidue → ℚ) :
    q2AffineResidueEnergy x =
      (x (0 : Q2AffineResidue)) ^ 2 +
      (x (1 : Q2AffineResidue)) ^ 2 +
      (x (2 : Q2AffineResidue)) ^ 2 +
      (x (3 : Q2AffineResidue)) ^ 2 := by
  simp [q2AffineResidueEnergy, Fin.sum_univ_succ]
  ring

/-- The pure six-tag incidence Gram has squared operator norm at most two. -/
theorem q2AffineTagEnergy_le_two_residueEnergy
    (x : Q2AffineResidue → ℚ) :
    q2AffineTagEnergy x ≤ 2 * q2AffineResidueEnergy x := by
  rw [q2AffineTagEnergy_eq, q2AffineResidueEnergy_eq]
  nlinarith [sq_nonneg (x (0 : Q2AffineResidue))]

/-- In particular the finite incidence geometry lies below the factor four
accepted by the odd-owner energy induction. -/
theorem q2AffineTagEnergy_le_four_residueEnergy
    (x : Q2AffineResidue → ℚ) :
    q2AffineTagEnergy x ≤ 4 * q2AffineResidueEnergy x := by
  have h2 := q2AffineTagEnergy_le_two_residueEnergy x
  have hE : 0 ≤ q2AffineResidueEnergy x := by
    unfold q2AffineResidueEnergy
    positivity
  nlinarith

end RHLean.Analysis

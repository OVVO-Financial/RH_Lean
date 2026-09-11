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

/-! ## Finite q^2 affine-contact frame

The six physical square-contact sites are `4k+a` for
`a in {1,2,3,5,6,7}`. For an odd square owner `q`, a contact has daughter
`d=(4k+a)/q^2`. Since `q^2 = 1 mod 4`, the daughter residue is `a mod 4`.
Thus the six tags occupy the three pairs `(1,5)`, `(2,6)`, `(3,7)` and the
finite residue Gram is diagonal `(0,2,2,2)`.

This is only the finite tag geometry. It does not identify the tag-dependent
affine pullback field with the recovered Mobius daughter.
-/

/-- The four residue coordinates seen after dividing an odd-square contact by `q^2`. -/
abbrev Q2AffineResidue := Fin 4

/-- Residue coordinate attached to one of the six physical contact offsets. -/
def q2AffineContactResidue (a : ℕ) : Q2AffineResidue :=
  ⟨a % 4, Nat.mod_lt _ (by norm_num)⟩

/-- Analysis of a four-coordinate daughter field by one physical contact tag. -/
def q2AffineTagPullback (a : ℕ) (x : Q2AffineResidue → ℚ) : ℚ :=
  x (q2AffineContactResidue a)

/-- Energy after all six affine contact tags are read from the daughter residue field. -/
def q2AffineTagEnergy (x : Q2AffineResidue → ℚ) : ℚ :=
  ∑ a ∈ physicalTransitionActiveOffsets, (q2AffineTagPullback a x) ^ 2

/-- Ambient energy of the four daughter residue coordinates. -/
def q2AffineResidueEnergy (x : Q2AffineResidue → ℚ) : ℚ :=
  ∑ r : Q2AffineResidue, (x r) ^ 2

/-- The finite Gram matrix of the six tag pullbacks. -/
def q2AffineGram : Matrix Q2AffineResidue Q2AffineResidue ℚ := fun r s =>
  ∑ a ∈ physicalTransitionActiveOffsets,
    (if q2AffineContactResidue a = r then (1 : ℚ) else 0) *
      (if q2AffineContactResidue a = s then (1 : ℚ) else 0)

/-- The six offsets really have only the three nonzero residue coordinates. -/
theorem physicalTransitionActiveOffsets_contactResidues :
    physicalTransitionActiveOffsets.image q2AffineContactResidue =
      ({(1 : Q2AffineResidue), (2 : Q2AffineResidue), (3 : Q2AffineResidue)} :
        Finset Q2AffineResidue) := by
  native_decide

/-- Every daughter residue is represented by at most two physical affine tags. -/
theorem physicalTransitionActiveOffsets_residueFiber_card_le_two
    (r : Q2AffineResidue) :
    (physicalTransitionActiveOffsets.filter fun a =>
      q2AffineContactResidue a = r).card ≤ 2 := by
  fin_cases r <;> native_decide

/-- Explicit Gram computation: the zero residue is absent and each of the other
three residue coordinates occurs exactly twice. -/
theorem q2AffineGram_entries (r s : Q2AffineResidue) :
    q2AffineGram r s =
      if r = s then (if r = (0 : Q2AffineResidue) then 0 else 2) else 0 := by
  fin_cases r <;> fin_cases s <;> native_decide

/-- The six-tag energy is exactly twice the energy on the three nonzero residues. -/
theorem q2AffineTagEnergy_eq
    (x : Q2AffineResidue → ℚ) :
    q2AffineTagEnergy x =
      2 * ((x (1 : Q2AffineResidue)) ^ 2 +
        (x (2 : Q2AffineResidue)) ^ 2 +
        (x (3 : Q2AffineResidue)) ^ 2) := by
  simp [q2AffineTagEnergy, q2AffineTagPullback,
    q2AffineContactResidue, physicalTransitionActiveOffsets]
  ring

/-- The ambient four-residue energy is the sum of the four coordinate squares. -/
theorem q2AffineResidueEnergy_eq
    (x : Q2AffineResidue → ℚ) :
    q2AffineResidueEnergy x =
      (x (0 : Q2AffineResidue)) ^ 2 +
      (x (1 : Q2AffineResidue)) ^ 2 +
      (x (2 : Q2AffineResidue)) ^ 2 +
      (x (3 : Q2AffineResidue)) ^ 2 := by
  fin_cases x <;> simp [q2AffineResidueEnergy]

/-- **Finite affine frame bound.** The squared norm of the six-tag analysis
operator is at most `2`, hence in particular below the factor `4` accepted by
the odd-owner energy induction. -/
theorem q2AffineTagEnergy_le_two_residueEnergy
    (x : Q2AffineResidue → ℚ) :
    q2AffineTagEnergy x ≤ 2 * q2AffineResidueEnergy x := by
  rw [q2AffineTagEnergy_eq]
  unfold q2AffineResidueEnergy
  fin_cases x
  all_goals simp

/-- The weaker factor-four estimate needed by the current sharp-frame consumer. -/
theorem q2AffineTagEnergy_le_four_residueEnergy
    (x : Q2AffineResidue → ℚ) :
    q2AffineTagEnergy x ≤ 4 * q2AffineResidueEnergy x := by
  have h2 := q2AffineTagEnergy_le_two_residueEnergy x
  have hE : 0 ≤ q2AffineResidueEnergy x := by
    unfold q2AffineResidueEnergy
    positivity
  nlinarith

/-- An odd prime square is `1 mod 4`. -/
theorem oddPrime_square_mod_four
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    (q * q) % 4 = 1 := by
  have hodd : q % 2 = 1 := (hq.eq_two_or_odd).resolve_left hq2
  have hmod : q % 4 = 1 ∨ q % 4 = 3 := by omega
  rw [Nat.mul_mod]
  rcases hmod with h | h <;> omega

/-- On an actual odd-prime square contact, the arithmetic daughter has the
residue coordinate predicted by its affine tag. -/
theorem qSquareOffsetDaughter_mod_four_eq_contactResidue
    {q a k : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdiv : q * q ∣ 4 * k + a) :
    qSquareOffsetDaughter q a k % 4 = a % 4 := by
  have hexact := qSquareOffsetDaughter_exact hdiv
  have hsq : (q * q) % 4 = 1 := oddPrime_square_mod_four hq hq2
  have hleft :
      (q * q * qSquareOffsetDaughter q a k) % 4 =
        qSquareOffsetDaughter q a k % 4 := by
    rw [Nat.mul_mod, hsq]
    simp
  have hright : (4 * k + a) % 4 = a % 4 := by omega
  have hmod := congrArg (fun n : ℕ => n % 4) hexact
  rwa [hleft, hright] at hmod

/-- For one odd square owner and one physical edge there is at most one active
offset hit. Thus the six tags are a bounded finite geometry, not a multiplicity
that can grow with `q`. -/
theorem physicalSquareContact_activeOffset_unique
    {q k a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : a ∈ physicalTransitionActiveOffsets)
    (hb : b ∈ physicalTransitionActiveOffsets)
    (hda : q * q ∣ 4 * k + a)
    (hdb : q * q ∣ 4 * k + b) :
    a = b := by
  have hma : 4 * k + a ≡ 0 [MOD q * q] := Nat.modEq_zero_iff_dvd.mpr hda
  have hmb : 4 * k + b ≡ 0 [MOD q * q] := Nat.modEq_zero_iff_dvd.mpr hdb
  have hsamed : 4 * k + a ≡ 4 * k + b [MOD q * q] := hma.trans hmb.symm
  have hsamed' : a + 4 * k ≡ b + 4 * k [MOD q * q] := by
    simpa [Nat.add_comm] using hsamed
  have hab : a ≡ b [MOD q * q] := Nat.ModEq.add_right_cancel' (4 * k) hsamed'
  have hqge : 3 ≤ q := by
    have htwo := hq.two_le
    omega
  have hmodge : 9 ≤ q * q := by nlinarith
  have hale : a ≤ 7 := by
    simp [physicalTransitionActiveOffsets] at ha
    omega
  have hble : b ≤ 7 := by
    simp [physicalTransitionActiveOffsets] at hb
    omega
  have halt : a < q * q := by omega
  have hblt : b < q * q := by omega
  change a % (q * q) = b % (q * q) at hab
  rw [Nat.mod_eq_of_lt halt, Nat.mod_eq_of_lt hblt] at hab
  exact hab

end RHLean.Analysis

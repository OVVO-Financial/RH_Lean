import Mathlib
import RHLean.Analysis.PhysicalSquareCRTPeriodNoGo

/-!
# Finite q^2 affine-contact frame

The six physical square-contact sites on one three-slot edge are

`4k+1, 4k+2, 4k+3, 4k+5, 4k+6, 4k+7`.

For an odd square owner `q`, a contact `q^2 | 4k+a` has daughter
`d = (4k+a)/q^2`. Since an odd square is `1 mod 4`, the daughter residue is
`d mod 4 = a mod 4`. Therefore the six tags collapse into the three pairs

`(1,5), (2,6), (3,7)`

on the daughter residue coordinate. The finite tag-analysis operator consequently
has Gram diagonal `(0,2,2,2)` and squared operator norm at most `2`.

This module proves only that finite affine-tag frame fact. It does not identify
the transported selected field with the recovered Mobius daughter; that remains
the separate physical/recovered intertwining step.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

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
  simp [q2AffineResidueEnergy, Fin.sum_univ_succ]
  ring

/-- **Finite affine frame bound.** The squared norm of the six-tag analysis
operator is at most `2`, hence in particular is below the factor `4` accepted by
the odd-owner energy induction. -/
theorem q2AffineTagEnergy_le_two_residueEnergy
    (x : Q2AffineResidue → ℚ) :
    q2AffineTagEnergy x ≤ 2 * q2AffineResidueEnergy x := by
  rw [q2AffineTagEnergy_eq, q2AffineResidueEnergy_eq]
  nlinarith [sq_nonneg (x (0 : Q2AffineResidue))]

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

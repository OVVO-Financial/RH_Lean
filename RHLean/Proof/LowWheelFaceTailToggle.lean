import Mathlib
import RHLean.Arithmetic.PrimeFaceMoebius

/-!
# Prime transfer between a Boolean face and a residual tail

Fix one prime coordinate `q`.  A state consists of a Boolean face `t` and a
positive residual tail `m`.  The `q`-move transfers one copy of `q` between
these two coordinates:

* if `q ∈ t`, delete it from the face and replace `m` by `q*m`;
* otherwise, if `q ∣ m`, insert it into the face and replace `m` by `m/q`;
* otherwise fix the state.

The represented integer `P(t)*m` is invariant.  On every active state the move
is an involution and reverses the Boolean sign.  This is the local opposite
Othello move used on canonical downcross parent fibres; no square-root geometry
or estimate appears here.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

abbrev LowWheelFaceTailState := Finset ℕ × ℕ

/-- Transfer one fixed prime coordinate between the Boolean face and tail. -/
def lowWheelFaceTailToggleAt (q : ℕ) (x : LowWheelFaceTailState) :
    LowWheelFaceTailState :=
  if q ∈ x.1 then
    (x.1.erase q, q * x.2)
  else if q ∣ x.2 then
    (insert q x.1, x.2 / q)
  else
    x

/-- Inserting a fresh Boolean coordinate reverses parity. -/
theorem booleanCubeSign_insert_eq_neg
    {q : ℕ} {t : Finset ℕ} (hq : q ∉ t) :
    booleanCubeSign (insert q t) = -booleanCubeSign t := by
  unfold booleanCubeSign
  rw [Finset.card_insert_of_notMem hq, pow_succ]
  ring

/-- Deleting a present Boolean coordinate reverses parity. -/
theorem booleanCubeSign_erase_eq_neg
    {q : ℕ} {t : Finset ℕ} (hq : q ∈ t) :
    booleanCubeSign (t.erase q) = -booleanCubeSign t := by
  have hnot : q ∉ t.erase q := Finset.notMem_erase q t
  have hsign := booleanCubeSign_insert_eq_neg (q := q) (t := t.erase q) hnot
  rw [Finset.insert_erase hq] at hsign
  omega

/-- Inserting a fresh coordinate multiplies the represented face product by
that coordinate. -/
theorem primeFaceProduct_insert_eq_mul
    {q : ℕ} {t : Finset ℕ} (hq : q ∉ t) :
    primeFaceProduct (insert q t) = q * primeFaceProduct t := by
  simp [primeFaceProduct, hq]

/-- A present coordinate factors from the represented face product. -/
theorem primeFaceProduct_erase_mul
    {q : ℕ} {t : Finset ℕ} (hq : q ∈ t) :
    q * primeFaceProduct (t.erase q) = primeFaceProduct t := by
  have hnot : q ∉ t.erase q := Finset.notMem_erase q t
  have h := primeFaceProduct_insert_eq_mul (q := q) (t := t.erase q) hnot
  rw [Finset.insert_erase hq] at h
  exact h.symm

/-- The face-times-tail parent integer is invariant under every fixed-coordinate
transfer. -/
theorem lowWheelFaceTailToggleAt_product
    (q : ℕ) (x : LowWheelFaceTailState) :
    primeFaceProduct (lowWheelFaceTailToggleAt q x).1 *
        (lowWheelFaceTailToggleAt q x).2 =
      primeFaceProduct x.1 * x.2 := by
  unfold lowWheelFaceTailToggleAt
  by_cases hqt : q ∈ x.1
  · simp only [hqt, if_true]
    have hface := primeFaceProduct_erase_mul hqt
    calc
      primeFaceProduct (x.1.erase q) * (q * x.2) =
          (q * primeFaceProduct (x.1.erase q)) * x.2 := by ring
      _ = primeFaceProduct x.1 * x.2 := by rw [hface]
  · simp only [hqt, if_false]
    by_cases hqm : q ∣ x.2
    · simp only [hqm, if_true]
      have hface := primeFaceProduct_insert_eq_mul hqt
      have htail : q * (x.2 / q) = x.2 := Nat.mul_div_cancel' hqm
      calc
        primeFaceProduct (insert q x.1) * (x.2 / q) =
            (q * primeFaceProduct x.1) * (x.2 / q) := by rw [hface]
        _ = primeFaceProduct x.1 * (q * (x.2 / q)) := by ring
        _ = primeFaceProduct x.1 * x.2 := by rw [htail]
    · simp [hqm]

/-- The fixed-coordinate face/tail move is an involution whenever the
coordinate is positive. -/
theorem lowWheelFaceTailToggleAt_involutive
    {q : ℕ} (hqpos : 0 < q) (x : LowWheelFaceTailState) :
    lowWheelFaceTailToggleAt q (lowWheelFaceTailToggleAt q x) = x := by
  by_cases hqt : q ∈ x.1
  · have hnot : q ∉ x.1.erase q := Finset.notMem_erase q x.1
    have hdiv : q ∣ q * x.2 := by exact dvd_mul_right q x.2
    simp [lowWheelFaceTailToggleAt, hqt, hnot, hdiv, hqpos.ne',
      Finset.insert_erase]
  · by_cases hqm : q ∣ x.2
    · have hmem : q ∈ insert q x.1 := Finset.mem_insert_self q x.1
      have htail : q * (x.2 / q) = x.2 := Nat.mul_div_cancel' hqm
      simp [lowWheelFaceTailToggleAt, hqt, hqm, hmem,
        Finset.erase_insert, htail]
    · simp [lowWheelFaceTailToggleAt, hqt, hqm]

/-- An active coordinate stays active after the transfer. -/
theorem lowWheelFaceTailToggleAt_active
    {q : ℕ} {x : LowWheelFaceTailState}
    (hactive : q ∈ x.1 ∨ q ∣ x.2) :
    q ∈ (lowWheelFaceTailToggleAt q x).1 ∨
      q ∣ (lowWheelFaceTailToggleAt q x).2 := by
  unfold lowWheelFaceTailToggleAt
  by_cases hqt : q ∈ x.1
  · simp only [hqt, if_true]
    right
    exact dvd_mul_right q x.2
  · have hqm : q ∣ x.2 := hactive.resolve_left hqt
    simp only [hqt, if_false, hqm, if_true]
    exact Or.inl (Finset.mem_insert_self q x.1)

/-- Every active transfer changes the Boolean face itself. -/
theorem lowWheelFaceTailToggleAt_fst_ne_of_active
    {q : ℕ} {x : LowWheelFaceTailState}
    (hactive : q ∈ x.1 ∨ q ∣ x.2) :
    (lowWheelFaceTailToggleAt q x).1 ≠ x.1 := by
  unfold lowWheelFaceTailToggleAt
  by_cases hqt : q ∈ x.1
  · simp only [hqt, if_true]
    intro heq
    have hmem : q ∈ x.1.erase q := by
      rw [heq]
      exact hqt
    exact (Finset.notMem_erase q x.1) hmem
  · have hqm : q ∣ x.2 := hactive.resolve_left hqt
    simp only [hqt, if_false, hqm, if_true]
    intro heq
    apply hqt
    rw [← heq]
    exact Finset.mem_insert_self q x.1

/-- Every active transfer genuinely changes the full face/tail state. -/
theorem lowWheelFaceTailToggleAt_ne_of_active
    {q : ℕ} {x : LowWheelFaceTailState}
    (hactive : q ∈ x.1 ∨ q ∣ x.2) :
    lowWheelFaceTailToggleAt q x ≠ x := by
  intro heq
  exact (lowWheelFaceTailToggleAt_fst_ne_of_active hactive)
    (congrArg Prod.fst heq)

/-- Every active fixed-coordinate transfer reverses the Boolean sign. -/
theorem lowWheelFaceTailToggleAt_sign_neg
    {q : ℕ} {x : LowWheelFaceTailState}
    (hactive : q ∈ x.1 ∨ q ∣ x.2) :
    booleanCubeSign (lowWheelFaceTailToggleAt q x).1 =
      -booleanCubeSign x.1 := by
  unfold lowWheelFaceTailToggleAt
  by_cases hqt : q ∈ x.1
  · simp only [hqt, if_true]
    exact booleanCubeSign_erase_eq_neg hqt
  · have hqm : q ∣ x.2 := hactive.resolve_left hqt
    simp only [hqt, if_false, hqm, if_true]
    exact booleanCubeSign_insert_eq_neg hqt

/-- Complex transport weights with any fixed cofactor amplitude reverse sign
under an active face/tail transfer. -/
theorem lowWheelFaceTailToggleAt_weight_neg
    {q : ℕ} {x : LowWheelFaceTailState} (a : ℂ)
    (hactive : q ∈ x.1 ∨ q ∣ x.2) :
    a * (booleanCubeSign (lowWheelFaceTailToggleAt q x).1 : ℂ) =
      -(a * (booleanCubeSign x.1 : ℂ)) := by
  rw [lowWheelFaceTailToggleAt_sign_neg hactive]
  push_cast
  ring

end RHLean.Proof

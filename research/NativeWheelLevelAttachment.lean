import «research.NativeLevelBranching»
import «research.NativeSignSchurHandoff»

/-! Exact attachment of the physical signed wheel to cyclic ramification.
The original slot address is used, with the negative copy supplied by
the integral signed kernel. No new arithmetic rank or signed gain is
claimed. The existing integral wheel left inverse is retained. -/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators
open MvPolynomial RHLean.Analysis.NativeLevelBranching

namespace RHLean.Analysis.AlpogeThin.SlotProjector.LevelAttachment

variable {J I R S : Type*} [Fintype J] [CommRing R] {N : ℕ}

/-- Zero extension of the original observations, at their literal
positive addresses in the level residue space. -/
def seed (e : J ↪ ZMod N) (X : Matrix J I R) : Matrix (ZMod N) I R :=
  fun z i => ∑ a : J, if e a = z then X a i else 0

theorem seed_at (e : J ↪ ZMod N) (X : Matrix J I R) (a : J) (i : I) :
    seed e X (e a) i = X a i := by
  classical
  unfold seed
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    exact if_neg (fun h => hb (e.injective h))
  · simp

theorem seed_at_neg (e : J ↪ ZMod N) (X : Matrix J I R)
    (apart : ∀ a b : J, e a ≠ -e b) (a : J) (i : I) :
    seed e X (-e a) i = 0 := by
  unfold seed
  exact Finset.sum_eq_zero fun b _ => if_neg (apart b a)

/-- The signed primitive channel, exactly the image of 1 minus
reflection. The unsigned channel is handled separately as in
NativeSignSchurHandoff. -/
def signed (e : J ↪ ZMod N) (X : Matrix J I R) : Matrix (ZMod N) I R :=
  fun z i => seed e X z i - seed e X (-z) i

theorem signed_at (e : J ↪ ZMod N) (X : Matrix J I R)
    (apart : ∀ a b : J, e a ≠ -e b) (a : J) (i : I) :
    signed e X (e a) i = X a i := by
  rw [signed, seed_at, seed_at_neg e X apart, sub_zero]

theorem signed_neg (e : J ↪ ZMod N) (X : Matrix J I R) (z : ZMod N) (i : I) :
    signed e X (-z) i = -signed e X z i := by
  simp only [signed, neg_neg, neg_sub]

/-- An exact pushforward pairing, including all off-diagonal
physical observations. -/
theorem seed_pair [NeZero N] (e : J ↪ ZMod N) (X : Matrix J I R)
    (i : I) (g : ZMod N → R) :
    (∑ z : ZMod N, seed e X z i * g z) = ∑ a : J, X a i * g (e a) := by
  classical
  calc
    _ = ∑ z : ZMod N, ∑ a : J, (if e a = z then X a i else 0) * g z := by
      simp only [seed, Finset.sum_mul]
    _ = ∑ a : J, ∑ z : ZMod N, (if e a = z then X a i else 0) * g z :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_eq_single (e a)]
      · simp
      · intro z _ hz
        simp [Ne.symm hz]
      · simp

/-- Reflection uses the existing signed pair, not additional
independent copies of the source rank. -/
theorem signed_gram [NeZero N] (e : J ↪ ZMod N) (X : Matrix J I ℝ)
    (apart : ∀ a b : J, e a ≠ -e b) :
    WheelNNS.coDiv (signed e X) = (2:ℝ) • WheelNNS.coDiv X := by
  classical
  rw [WheelNNS.coDiv_eq, WheelNNS.coDiv_eq]
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  have hneg :
      (∑ z : ZMod N, seed e X (-z) i * signed e X z j) =
        ∑ z : ZMod N, seed e X z i * signed e X (-z) j := by
    simpa only [Equiv.neg_apply, neg_neg] using
      (Equiv.sum_comp (Equiv.neg (ZMod N))
        (fun z => seed e X (-z) i * signed e X z j)).symm
  calc
    _ = (∑ z : ZMod N, seed e X z i * signed e X z j) -
        ∑ z : ZMod N, seed e X (-z) i * signed e X z j := by
      simp only [signed, sub_mul, Finset.sum_sub_distrib]
    _ = _ := by
      rw [hneg, seed_pair, seed_pair]
      simp only [signed_neg, signed_at e X apart, mul_neg, Finset.sum_neg_distrib]
      ring

theorem signed_det [NeZero N] [Fintype I] [DecidableEq I]
    (e : J ↪ ZMod N) (X : Matrix J I ℝ)
    (apart : ∀ a b : J, e a ≠ -e b) :
    (WheelNNS.coDiv (signed e X)).det =
      (2:ℝ)^Fintype.card I * (WheelNNS.coDiv X).det := by
  rw [signed_gram e X apart, Matrix.det_smul]

/-- The literal signed determinant ratio of any two profiles is
unchanged, including the original physical wheel profiles. -/
theorem signed_relative [NeZero N] [Fintype I] [DecidableEq I]
    (e : J ↪ ZMod N) (X Y : Matrix J I ℝ)
    (apart : ∀ a b : J, e a ≠ -e b)
    (hx : (WheelNNS.coDiv X).det ≠ 0) (hy : (WheelNNS.coDiv Y).det ≠ 0) :
    Real.log (WheelNNS.coDiv (signed e X)).det -
      Real.log (WheelNNS.coDiv (signed e Y)).det =
    Real.log (WheelNNS.coDiv X).det - Real.log (WheelNNS.coDiv Y).det := by
  rw [signed_det e X apart, signed_det e Y apart,
    Real.log_mul (by positivity) hx, Real.log_mul (by positivity) hy]
  ring

/-- The actual quotient integers are injected at the level, rather
than being relabelled as arbitrary polynomial coordinates. -/
def levelAddress (N : ℕ) (e : J ↪ ℕ) (hlt : ∀ a, e a < N) : J ↪ ZMod N where
  toFun a := (e a : ZMod N)
  inj' := by
    intro a b hab
    apply e.injective
    have h := congrArg ZMod.val hab
    simpa only [ZMod.val_natCast_of_lt (hlt a), ZMod.val_natCast_of_lt (hlt b)] using h

theorem levelAddress_apart (N : ℕ) (e : J ↪ ℕ) (hlt : ∀ a, e a < N)
    (hpos : ∀ a, 0 < e a) (hhalf : ∀ a, 2 * e a < N)
    (a b : J) : levelAddress N e hlt a ≠ -levelAddress N e hlt b := by
  intro hab
  have hsum : e a + e b < N := by
    have := hhalf a
    have := hhalf b
    omega
  have hz : ((e a + e b : ℕ) : ZMod N) = 0 := by
    push_cast
    change levelAddress N e hlt a + levelAddress N e hlt b = 0
    rw [hab, neg_add_cancel]
  have hzero := congrArg ZMod.val hz
  rw [ZMod.val_natCast_of_lt hsum, ZMod.val_zero] at hzero
  have := hpos a
  omega

/-- Construct the residue address from the proved original physical
interval equivalence. The collar 2*floor(h_0)<N makes the negative
copy disjoint; no shift or artificial slots are introduced. -/
theorem exists_physical_levelAddress {r : ℕ} (h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) (hN : 2 * ⌊h 0⌋₊ < N) :
    ∃ e : Address (bands h v) ↪ ZMod N,
      (∀ a, e a = (a.2.val : ZMod N)) ∧ (∀ a b, e a ≠ -e b) := by
  obtain ⟨E, hE⟩ := original_addresses h v hne
  let e : Address (bands h v) ↪ ℕ :=
    ⟨fun a => (E a).val, fun a b hab => E.injective (Subtype.ext hab)⟩
  have hpos a : 0 < e a := (Nat.zero_le _).trans_lt (Finset.mem_Ioc.mp (E a).property).1
  have hhalf a : 2 * e a < N :=
    (Nat.mul_le_mul_left 2 (Finset.mem_Ioc.mp (E a).property).2).trans_lt hN
  have hlt a : e a < N := by have := hhalf a; omega
  refine ⟨levelAddress N e hlt, ?_, levelAddress_apart N e hlt hpos hhalf⟩
  intro a
  change ((E a).val : ZMod N) = (a.2.val : ZMod N)
  rw [hE]

/-- A constant or homogeneous monomial embedding on the same
physical rows. The ramification is the actual cyclic unit -1. -/
def polySeed (e : J ↪ ZMod N) (X : Matrix J I ℂ) (a : S →₀ ℕ) (i : I)
    (z : ZMod N) : MvPolynomial S ℂ := monomial a (seed e X z i)

theorem poly_ramified (e : J ↪ ZMod N) (X : Matrix J I ℂ) (a : S →₀ ℕ)
    (i : I) (z : ZMod N) :
    ramifiedResidue (-1 : (ZMod N)ˣ) (polySeed e X a i) z =
      monomial a (signed e X z i) := by
  classical
  ext b
  simp [ramifiedResidue, polySeed, signed, coeff_monomial, apply_ite]

/-- A scalar dilation on the original wheel can be cancelled
integrally using its actual CRT left inverse. This applies to all
columns simultaneously and does not use an assigned height. -/
theorem original_star_dilation_cancel {r : ℕ}
    (A : Fin (r+1) → Finset ℕ) (D : Fin (r+1) → ℕ)
    (hA : ∀ i, (A i).Nonempty) (hD : ∀ i, 0 < D i)
    (hc : Pairwise (fun i j => (D i).Coprime (D j)))
    (d : ℤ) (C : Matrix (Fin r) I ℤ) (Z : Matrix (Address A) I ℤ)
    (he : columns A D * C = d • Z) :
    ∃ V : Matrix (Fin r) I ℤ, C = d • V := by
  obtain ⟨Y, hY⟩ := left_inverse A D hA hD hc
  refine ⟨Y * Z, ?_⟩
  calc
    C = Y * (columns A D * C) := by rw [← Matrix.mul_assoc, hY, Matrix.one_mul]
    _ = _ := by rw [he, Matrix.mul_smul]

/-- On the same positive degree the cleared preimage, followed by
restriction, retains the integral companion factor u^h. In particular
the bare embedding cannot be advertised as a net real saving. -/
theorem positive_degree_preimage_readout [NeZero N] (t : S) (q h : ℕ)
    (hh : 0 < h) (u v : ℂ) (hv : v ≠ 0) (hN : u*v = N)
    (f : ZMod N → MvPolynomial S ℂ) (j : ZMod N) :
    restrictDegree t h v
      (((pairedFourier N t)^[q]
        (fun i => reweight (fun b => (N : ℂ)^pairedClearingDegree t q b) (f i))) j) =
    reweight (fun b => if b t = h then u^h else 0)
      (f ((Neg.neg : ZMod N → ZMod N)^[q] j)) := by
  rw [pairedFourier_preimage, restriction_dilate t h u v (N:ℂ) hv hN]
  ext a
  simp only [coeff_reweight]
  by_cases ha : a t = h
  · have hle : q ≤ 2 * a t * q + a t := by
      have h2 : 1 ≤ 2 * a t := by omega
      calc
        q = 1*q := by simp
        _ ≤ (2 * a t)*q := Nat.mul_le_mul_right q h2
        _ ≤ _ := Nat.le_add_right _ _
    simp [ha, Nat.sub_eq_zero_of_le hle]
  · simp [ha]

end RHLean.Analysis.AlpogeThin.SlotProjector.LevelAttachment

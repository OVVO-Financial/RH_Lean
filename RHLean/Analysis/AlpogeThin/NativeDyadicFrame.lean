import RHLean.Analysis.AlpogeNativeDyadicHostSize
import RHLean.Analysis.AlpogeThin.Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection

/-!
# The original finite frame on the actual native dyadic quotient

The frame is constructed by transporting the existing group `H_e` through
`Fintype.equivFin`. Its projection is an equivalence. Its distinguished
element is the original class of `5`, whose order is proved to be `2^e`.
Thus the source generator and the full arithmetic host are retained.

The full-host equivalence explicitly converts native additive sign bits
`(d,q)` into the source's multiplicative integer-unit signs `(q,d)`.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`FrameCyclicGenerator.lean`, declarations `Frame.ofEquiv`, `Frame.ofGroup`,
and `cyclicFrame_order`. The order calculation uses the native pinned
Mathlib theorem `ZMod.orderOf_five` and reduction modulo four.
No field, geometric witness or analytic estimate is assumed here.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false

noncomputable section

namespace RHLean.Analysis.AlpogeThin

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

/-- The authentic dyadic generator is the class of the residue unit `5`. -/
def nativeDyadicGenerator (e : ℕ) : AlpogeNativeDyadicH e :=
  Additive.ofMul (hcl e (u5 (e + 2)))

private theorem nativeDyadic_five_pow_ne_neg_one (e k : ℕ) :
    u5 (e + 2) ^ k ≠ -1 := by
  intro h
  have h4 : 4 ∣ 2 ^ (e + 2) := by
    change 2 ^ 2 ∣ 2 ^ (e + 2)
    exact pow_dvd_pow 2 (by omega)
  have hv : ((u5 (e + 2) : (ZMod (2 ^ (e + 2)))ˣ) :
      ZMod (2 ^ (e + 2))) = 5 := ZMod.coe_unitOfCoprime _ _
  have hval := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, hv, Units.val_neg, Units.val_one] at hval
  have hmod : (5 : ZMod 4) ^ k = -1 := by
    simpa only [map_pow, map_ofNat, map_neg, map_one] using
      congrArg (ZMod.castHom h4 (ZMod 4)) hval
  rw [show (5 : ZMod 4) = 1 by decide, one_pow] at hmod
  exact (by decide : (1 : ZMod 4) ≠ -1) hmod

/-- Quotienting by `±1` preserves the full order of the genuine residue `5`;
none of its powers is `-1`, as seen already modulo four. -/
theorem nativeDyadicGenerator_order (e : ℕ) :
    addOrderOf (nativeDyadicGenerator e) = 2 ^ e := by
  have hu : orderOf (u5 (e + 2)) = 2 ^ e := by
    rw [← orderOf_units]
    simpa only [u5, ZMod.coe_unitOfCoprime, Nat.cast_ofNat] using ZMod.orderOf_five e
  change orderOf (hcl e (u5 (e + 2))) = 2 ^ e
  rw [← hu]
  apply orderOf_eq_orderOf_iff.mpr
  intro k
  change (QuotientGroup.mk (u5 (e + 2)) : HGrp e) ^ k = 1 ↔
    u5 (e + 2) ^ k = 1
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, hn⟩
    rcases Int.even_or_odd n with hnEven | hnOdd
    · rw [hnEven.neg_one_zpow] at hn
      exact hn.symm
    · rw [hnOdd.neg_one_zpow] at hn
      exact (nativeDyadic_five_pow_ne_neg_one e k hn.symm).elim
  · intro h
    exact ⟨0, by simpa only [zpow_zero] using h.symm⟩

/-- The finite source frame is a transported copy of the complete native
dyadic quotient, with the original class-of-five generator. -/
def nativeDyadicFrame (e : ℕ) : Formalism.HC.Frame :=
  let ε : Formalism.HC.Idx (Fintype.card (AlpogeNativeDyadicH e)) ≃
      AlpogeNativeDyadicH e := (Fintype.equivFin (AlpogeNativeDyadicH e)).symm
  let : AddCommGroup (Formalism.HC.Idx (Fintype.card (AlpogeNativeDyadicH e))) :=
    ε.addCommGroup
  { e := e
    ord := Fintype.card (AlpogeNativeDyadicH e)
    grp := ε.addCommGroup
    h0 :=
      { toFun := ε
        map_zero' := ε.apply_symm_apply 0
        map_add' := fun x y => ε.apply_symm_apply (ε x + ε y) }
    projection_surjective_field := ε.surjective
    gen0 := ε.symm (nativeDyadicGenerator e)
    zsmul_generator_eq_zero_of_projection := fun _ hk =>
      ε.injective (hk.trans (ε.apply_symm_apply 0).symm) }

/-- The coordinate transport is an additive equivalence, not only a count. -/
def nativeDyadicFrameEquiv (e : ℕ) :
    (nativeDyadicFrame e).A ≃+ AlpogeNativeDyadicH e :=
  let ε : Formalism.HC.Idx (Fintype.card (AlpogeNativeDyadicH e)) ≃
      AlpogeNativeDyadicH e := (Fintype.equivFin (AlpogeNativeDyadicH e)).symm
  let : AddCommGroup (Formalism.HC.Idx (Fintype.card (AlpogeNativeDyadicH e))) :=
    ε.addCommGroup
  ε.addEquiv

theorem nativeDyadicFrame_e (e : ℕ) : (nativeDyadicFrame e).e = e := rfl

theorem nativeDyadicFrame_ord (e : ℕ) : (nativeDyadicFrame e).ord = 2 ^ e :=
  alpogeNativeDyadicH_card e

theorem nativeDyadicFrame_h (e : ℕ) (t : (nativeDyadicFrame e).A) :
    (nativeDyadicFrame e).h t = nativeDyadicFrameEquiv e t := rfl

theorem nativeDyadicFrame_h_injective (e : ℕ) :
    Function.Injective (nativeDyadicFrame e).h := (nativeDyadicFrameEquiv e).injective

theorem nativeDyadicFrame_generator (e : ℕ) :
    nativeDyadicFrameEquiv e (nativeDyadicFrame e).a0 = nativeDyadicGenerator e :=
  (Fintype.equivFin (AlpogeNativeDyadicH e)).symm.apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
/-- The selected source generator has the full source frame order. -/
theorem nativeDyadicFrame_n0 (e : ℕ) : (nativeDyadicFrame e).n0 = 2 ^ e := by
  have h := AddEquiv.addOrderOf_eq
    (G := (nativeDyadicFrame e).A) (H := AlpogeNativeDyadicH e)
    (nativeDyadicFrameEquiv e) (nativeDyadicFrame e).a0
  exact h.symm.trans
    ((congrArg (fun x : AlpogeNativeDyadicH e => addOrderOf x)
      (nativeDyadicFrame_generator e)).trans (nativeDyadicGenerator_order e))

/-- The original distinguished cyclic subgroup is the complete dyadic frame. -/
theorem nativeDyadicFrame_A0 (e : ℕ) : (nativeDyadicFrame e).A0 = ⊤ := by
  apply (AddSubgroup.card_eq_iff_eq_top ((nativeDyadicFrame e).A0)).mp
  change Nat.card (AddSubgroup.zmultiples (nativeDyadicFrame e).a0) =
    Nat.card (nativeDyadicFrame e).A
  rw [Nat.card_zmultiples]
  change (nativeDyadicFrame e).n0 = Nat.card (nativeDyadicFrame e).A
  rw [nativeDyadicFrame_n0, Formalism.HC.Frame.natCard_A, nativeDyadicFrame_ord]

theorem nativeDyadicFrame_index (e : ℕ) : (nativeDyadicFrame e).o = 1 := by
  change (nativeDyadicFrame e).ord / (nativeDyadicFrame e).n0 = 1
  rw [nativeDyadicFrame_ord, nativeDyadicFrame_n0]
  exact Nat.div_self (pow_pos (by decide) e)

theorem nativeDyadicFrame_twoGroup (e : ℕ) : (nativeDyadicFrame e).TwoGroup :=
  ⟨e, nativeDyadicFrame_ord e⟩

/-- Integer unit signs and native bits are genuinely equivalent groups. -/
def nativeDyadicSignEquiv : ℤˣ ≃* Multiplicative (ZMod 2) :=
  MulEquiv.ofBijective alpogeNativeSign2 (by decide)

theorem nativeDyadicSignEquiv_apply (s : ℤˣ) :
    nativeDyadicSignEquiv s = alpogeNativeSign2 s := rfl

theorem nativeDyadicSignEquiv_symm_zero :
    nativeDyadicSignEquiv.symm (Multiplicative.ofAdd (0 : ZMod 2)) = 1 :=
  nativeDyadicSignEquiv.symm.map_one

theorem nativeDyadicSignEquiv_symm_one :
    nativeDyadicSignEquiv.symm (Multiplicative.ofAdd (1 : ZMod 2)) = -1 := by
  apply (MulEquiv.symm_apply_eq nativeDyadicSignEquiv).mpr
  change Multiplicative.ofAdd (1 : ZMod 2) =
    Multiplicative.ofAdd (if (-1 : ℤˣ) = 1 then 0 else 1)
  norm_num

theorem nativeDyadicSignEquiv_symm_eq_one_iff (b : ZMod 2) :
    nativeDyadicSignEquiv.symm (Multiplicative.ofAdd b) = 1 ↔ b = 0 :=
  nativeDyadicSignEquiv.symm.map_eq_one_iff

/-- The recovered unit has the explicit integer sign used by the actual
quadratic root's Galois-action theorem. -/
theorem nativeDyadicSignEquiv_symm_val (b : ZMod 2) :
    ((nativeDyadicSignEquiv.symm (Multiplicative.ofAdd b) : ℤˣ) : ℤ) =
      if b = 0 then 1 else -1 := by
  have hb : b = 0 ∨ b = 1 := by
    have h : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    exact h b
  rcases hb with rfl | rfl
  · rw [nativeDyadicSignEquiv_symm_zero]
    norm_num
  · rw [nativeDyadicSignEquiv_symm_one]
    norm_num

/-- The two quadratic factors are explicitly swapped from native `(d,q)`
bits into source `(q,d)` unit signs. -/
def nativeDyadicTwoBitEquiv : Multiplicative AlpogeNativeE0 ≃* (ℤˣ × ℤˣ) :=
  (MulEquiv.prodMultiplicative (ZMod 2) (ZMod 2) : Multiplicative (ZMod 2 × ZMod 2) ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 2)).trans
    ((MulEquiv.prodComm :
      Multiplicative (ZMod 2) × Multiplicative (ZMod 2) ≃*
        Multiplicative (ZMod 2) × Multiplicative (ZMod 2)).trans
      (nativeDyadicSignEquiv.symm.prodCongr nativeDyadicSignEquiv.symm))

/-- Full arithmetic-host transport to the actual original frame. -/
def nativeDyadicFullHostEquiv (e : ℕ) :
    Multiplicative (AlpogeNativeE0 × AlpogeNativeDyadicH e) ≃*
      (nativeDyadicFrame e).GG :=
  let εH : Multiplicative (AlpogeNativeDyadicH e) ≃* (nativeDyadicFrame e).MA :=
    AddEquiv.toMultiplicative
      (G := AlpogeNativeDyadicH e) (H := (nativeDyadicFrame e).A)
      (nativeDyadicFrameEquiv e).symm
  let εP : Multiplicative AlpogeNativeE0 × Multiplicative (AlpogeNativeDyadicH e) ≃*
      (ℤˣ × ℤˣ) × (nativeDyadicFrame e).MA :=
    MulEquiv.prodCongr
      (M := Multiplicative AlpogeNativeE0) (M' := ℤˣ × ℤˣ)
      (N := Multiplicative (AlpogeNativeDyadicH e)) (N' := (nativeDyadicFrame e).MA)
      nativeDyadicTwoBitEquiv εH
  (MulEquiv.prodMultiplicative AlpogeNativeE0 (AlpogeNativeDyadicH e) :
    Multiplicative (AlpogeNativeE0 × AlpogeNativeDyadicH e) ≃*
      Multiplicative AlpogeNativeE0 × Multiplicative (AlpogeNativeDyadicH e)).trans εP

theorem nativeDyadicFullHostEquiv_apply
    (e : ℕ) (g : Multiplicative (AlpogeNativeE0 × AlpogeNativeDyadicH e)) :
    nativeDyadicFullHostEquiv e g =
      ((nativeDyadicSignEquiv.symm (Multiplicative.ofAdd g.toAdd.1.2),
        nativeDyadicSignEquiv.symm (Multiplicative.ofAdd g.toAdd.1.1)),
       Multiplicative.ofAdd ((nativeDyadicFrameEquiv e).symm g.toAdd.2)) := rfl

theorem nativeDyadicFullHostEquiv_chD_val
    (e : ℕ) (g : Multiplicative (AlpogeNativeE0 × AlpogeNativeDyadicH e)) :
    (((nativeDyadicFullHostEquiv e g).1.2 : ℤˣ) : ℤ) =
      if g.toAdd.1.1 = 0 then 1 else -1 :=
  nativeDyadicSignEquiv_symm_val _

theorem nativeDyadicFullHostEquiv_hH
    (e : ℕ) (g : Multiplicative (AlpogeNativeE0 × AlpogeNativeDyadicH e)) :
    (nativeDyadicFrame e).hH (nativeDyadicFullHostEquiv e g).2 = g.toAdd.2.toMul := by
  change ((nativeDyadicFrameEquiv e)
    ((nativeDyadicFrameEquiv e).symm g.toAdd.2)).toMul = _
  rw [AddEquiv.apply_symm_apply]

theorem nativeDyadicFullHostEquiv_cconj (e : ℕ) :
    nativeDyadicFullHostEquiv e
      (Multiplicative.ofAdd (alpogeNativeCconj (AlpogeNativeDyadicH e))) =
        (nativeDyadicFrame e).cc := by
  rw [nativeDyadicFullHostEquiv_apply]
  change ((nativeDyadicSignEquiv.symm (Multiplicative.ofAdd (1 : ZMod 2)),
    nativeDyadicSignEquiv.symm (Multiplicative.ofAdd (1 : ZMod 2))),
      Multiplicative.ofAdd ((nativeDyadicFrameEquiv e).symm 0)) = ((-1, -1), 1)
  simp only [nativeDyadicSignEquiv_symm_one, map_zero, ofAdd_zero]

theorem nativeDyadicFullHostEquiv_mem_Psi_iff
    (e : ℕ) (g : Multiplicative (AlpogeNativeE0 × AlpogeNativeDyadicH e)) :
    nativeDyadicFullHostEquiv e g ∈ (nativeDyadicFrame e).Psi ↔
      alpogeNativeInPhi g.toAdd := by
  rw [Formalism.HC.Frame.mem_Psi_iff]
  exact nativeDyadicSignEquiv_symm_eq_one_iff _

end RHLean.Analysis.AlpogeThin

end

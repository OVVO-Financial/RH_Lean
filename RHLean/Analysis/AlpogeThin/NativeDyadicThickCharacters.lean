import RHLean.Analysis.AlpogeThin.NativeDyadicPayment
import RHLean.Analysis.AlpogeNativePrincipalProjection

/-!
# The same selected pair pays the three nonprincipal thick characters

Source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`CharacterBoxes/BoundedTw.lean`, `PrimitiveCosets/SigALe.lean`, and
`PrimitiveCosets/GmAEq.lean`.

The existing `PairGood.bounds` controls the three nonzero q/d twists on
the actual selection window. This file identifies those twists with the
three two-bit characters of RH_Lean's constructed dyadic reciprocity map,
after passage to their primitive characters. It then pays the exact difference
between the complete signed Gsig and scalar native Gz, at each original
height a_t/b. The exponentially large thin-response regime is not used at
these thick arguments.

No character bound is introduced as an additional premise. The `PairGood`
witness is the same witness already constructed in the native pair theorem.
The complete geometric top excess and the compatible height/window
construction still require their genuine suppliers.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open scoped BigOperators Classical

namespace RHLean.Analysis.AlpogeThin

private theorem dyadicSign_recover (s : ℤˣ) :
    (if Multiplicative.toAdd (alpogeNativeSign2 s) = 0 then (1 : ℂ) else -1) =
      ((s : ℤ) : ℂ) := by
  rcases Int.units_eq_one_or s with rfl | rfl <;>
    norm_num [alpogeNativeSign2]

private theorem dyadicLegU_nat
    (N p a : ℕ) [Fact p.Prime] (hp : p ∣ N) (ha : a.Coprime N) :
    ((alpogeNativeLegU N p hp (ZMod.unitOfCoprime a ha) : ℤˣ) : ℤ) =
      jacobiSym (a : ℤ) p := by
  change (((quadraticChar (ZMod p)).toUnitHom
    (ZMod.unitsMap hp (ZMod.unitOfCoprime a ha)) : ℤˣ) : ℤ) = _
  rw [MulChar.coe_toUnitHom, ZMod.unitsMap_val, ZMod.coe_unitOfCoprime,
    ZMod.cast_natCast hp, ← jacobiSym.legendreSym.to_jacobiSym]
  simp only [legendreSym, Int.cast_natCast]

private theorem dyadicCoprime
    (e q d a : ℕ) (ha : a.Coprime (2 * 1 * q * d)) :
    a.Coprime (alpogeNativeHostN e q d) := by
  have ha' : a.Coprime (2 * q * d) := by simpa using ha
  have h2 : a.Coprime 2 :=
    Nat.Coprime.coprime_dvd_right ⟨q * d, by ring⟩ ha'
  have hq : a.Coprime q :=
    Nat.Coprime.coprime_dvd_right ⟨2 * d, by ring⟩ ha'
  have hd : a.Coprime d :=
    Nat.Coprime.coprime_dvd_right ⟨2 * q, by ring⟩ ha'
  exact ((h2.pow_right (e + 2)).mul_right hq).mul_right hd

/-- The q and d exponents label the two actual host characters. -/
def nativeDyadicTwoBitCharacter (e : ℕ) (i j : Fin 2) :
    AddChar (AlpogeNativeE0 × AlpogeNativeDyadicH e) ℂ :=
  (i : ℕ) • alpogeNativePsC (AlpogeNativeDyadicH e) +
    (j : ℕ) • alpogeNativeChC (AlpogeNativeDyadicH e)

/-- Exact primitive-character induction identity with the selected pair's Jacobi
twist. The dyadic quotient is retained and its character here is trivial. -/
theorem nativeDyadicTwoBitCharacter_induces
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (i j : Fin 2) :
    Formalism.HC.An.Induces
      (alpogeNativeDirChar (H := AlpogeNativeDyadicH e) (alpogeNativeRecMap e q d)
        (nativeDyadicTwoBitCharacter e i j)).primitiveCharacter
      (UpperTheory.Top.tw
        (fun a => (1 : DirichletCharacter ℂ 1) (a : ZMod 1)) q d i j)
      (2 * 1 * q * d) := by
  let χ := alpogeNativeDirChar (H := AlpogeNativeDyadicH e) (alpogeNativeRecMap e q d)
    (nativeDyadicTwoBitCharacter e i j)
  refine ⟨DirichletCharacter.primitiveCharacter_isPrimitive χ, ?_⟩
  intro a ha
  have hc := dyadicCoprime e q d a ha
  have hprim := (Formalism.HC.An.induces_of χ).2 a hc
  change χ.primitiveCharacter (a : ZMod χ.conductor) = χ (a : ZMod _) at hprim
  rw [hprim]
  let v := ZMod.unitOfCoprime a hc
  have hv : (v : ZMod (alpogeNativeHostN e q d)) = a :=
    ZMod.coe_unitOfCoprime a hc
  have hq : alpogeNativePsC (AlpogeNativeDyadicH e)
      (Multiplicative.toAdd (alpogeNativeRecMap e q d v)) =
      ((jacobiSym (a : ℤ) q : ℤ) : ℂ) := by
    change (if Multiplicative.toAdd
      (alpogeNativeSign2 (alpogeNativeLegU _ q (alpogeNativeQ_dvd_hostN e q d) v))
        = 0 then (1 : ℂ) else -1) = _
    rw [dyadicSign_recover, dyadicLegU_nat]
  have hd : alpogeNativeChC (AlpogeNativeDyadicH e)
      (Multiplicative.toAdd (alpogeNativeRecMap e q d v)) =
      ((jacobiSym (a : ℤ) d : ℤ) : ℂ) := by
    change (if Multiplicative.toAdd
      (alpogeNativeSign2 (alpogeNativeLegU _ d (alpogeNativeD_dvd_hostN e q d) v))
        = 0 then (1 : ℂ) else -1) = _
    rw [dyadicSign_recover, dyadicLegU_nat]
  change alpogeNativeDirChar (H := AlpogeNativeDyadicH e) (alpogeNativeRecMap e q d)
    (nativeDyadicTwoBitCharacter e i j) (a : ZMod _) = _
  rw [← hv, alpogeNativeDirChar_unit]
  simp only [nativeDyadicTwoBitCharacter, AddChar.add_apply, AddChar.nsmul_apply,
    hq, hd, UpperTheory.Top.tw,
    MulChar.one_apply (isUnit_of_subsingleton (a : ZMod 1)), one_mul]

/-- The genuine selected-pair estimate, at its original Y-to-X scale, on
each nonprincipal two-bit character of the same native dyadic host. -/
theorem nativePairGood_dyadicTwist_bound
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    {eps Y X : ℝ} (hG : UpperTheory.Top.PairGood 1 eps Y X q d)
    (i j : Fin 2) (hij : i ≠ 0 ∨ j ≠ 0)
    (y : ℝ) (hyY : Y ≤ y) (hyX : y ≤ X) :
    ‖alpogeNativeFrobInertiaGPsi
        (alpogeNativeHostData e q d).inertia
        (alpogeNativeHostData e q d).frob
        (alpogeNativeCanonicalHostEll (alpogeNativeRecMap e q d))
        (nativeDyadicTwoBitCharacter e i j) y‖ ≤
      y ^ ((1 : ℝ) / 2 + eps / 2) := by
  let χ := alpogeNativeDirChar (H := AlpogeNativeDyadicH e) (alpogeNativeRecMap e q d)
    (nativeDyadicTwoBitCharacter e i j)
  let : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  have hq2 : q ≠ 2 := by have := hG.pair.q_mod; omega
  have hd2 : d ≠ 2 := by have := hG.pair.d_mod; omega
  have hqd : q ≠ d := by
    have := hG.pair.q_mod
    have := hG.pair.d_mod
    omega
  have hsurj := alpogeNativeRecMap_surjective e q d hq2 hd2 hqd
  have hb := (hG.bounds (1 : DirichletCharacter ℂ 1) i j hij χ.conductor
    χ.primitiveCharacter (nativeDyadicTwoBitCharacter_induces e q d i j)
    y hyY hyX).1
  rw [hostResponse_eq_nativeResponse] at hb
  have hresponse := nativeCftGPsi_eq_nativeResponse
    (H := AlpogeNativeDyadicH e) (N := alpogeNativeHostN e q d)
    q d (alpogeNativeRecMap e q d) hsurj (nativeDyadicTwoBitCharacter e i j) y
  rw [← hresponse] at hb
  simpa only [alpogeNativeHostData] using hb

/-- All three excluded thick characters are paid by the same selected pair.
The complete signal retains its original `1+B-A-AB` signs before this bound. -/
theorem nativePairGood_dyadicGsig_sub_Gz_norm_le
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    {eps Y X : ℝ} (hG : UpperTheory.Top.PairGood 1 eps Y X q d)
    (y : ℝ) (hyY : Y ≤ y) (hyX : y ≤ X) :
    ‖alpogeNativeFrobInertiaGsig
        (alpogeNativeHostData e q d).inertia
        (alpogeNativeHostData e q d).frob
        (alpogeNativeCanonicalHostEll (alpogeNativeRecMap e q d))
        (alpogeNativeChC (AlpogeNativeDyadicH e))
        (alpogeNativePsC (AlpogeNativeDyadicH e)) y -
      (alpogeNativeGzArithmetic y : ℂ)‖ ≤
      3 * y ^ ((1 : ℝ) / 2 + eps / 2) := by
  let F := alpogeNativeFrobInertiaGPsi
    (alpogeNativeHostData e q d).inertia
    (alpogeNativeHostData e q d).frob
    (alpogeNativeCanonicalHostEll (alpogeNativeRecMap e q d))
  let A := alpogeNativeChC (AlpogeNativeDyadicH e)
  let B := alpogeNativePsC (AlpogeNativeDyadicH e)
  have hB : ‖F B y‖ ≤ y ^ ((1 : ℝ) / 2 + eps / 2) := by
    simpa [nativeDyadicTwoBitCharacter, F, B] using
      nativePairGood_dyadicTwist_bound e q d hG 1 0
        (Or.inl (by decide)) y hyY hyX
  have hA : ‖F A y‖ ≤ y ^ ((1 : ℝ) / 2 + eps / 2) := by
    simpa [nativeDyadicTwoBitCharacter, F, A] using
      nativePairGood_dyadicTwist_bound e q d hG 0 1
        (Or.inr (by decide)) y hyY hyX
  have hAB : ‖F (A + B) y‖ ≤ y ^ ((1 : ℝ) / 2 + eps / 2) := by
    simpa [nativeDyadicTwoBitCharacter, F, A, B, add_comm] using
      nativePairGood_dyadicTwist_bound e q d hG 1 1
        (Or.inl (by decide)) y hyY hyX
  have hidentity : alpogeNativeFrobInertiaGsig
      (alpogeNativeHostData e q d).inertia
      (alpogeNativeHostData e q d).frob
      (alpogeNativeCanonicalHostEll (alpogeNativeRecMap e q d)) A B y -
      (alpogeNativeGzArithmetic y : ℂ) =
        F B y - F A y - F (A + B) y := by
    unfold alpogeNativeFrobInertiaGsig
    rw [alpogeNativeFrobInertiaGPsi_principal]
    change (alpogeNativeGzArithmetic y : ℂ) + F B y - F A y - F (A + B) y -
      (alpogeNativeGzArithmetic y : ℂ) = _
    ring
  change ‖alpogeNativeFrobInertiaGsig
    (alpogeNativeHostData e q d).inertia
    (alpogeNativeHostData e q d).frob
    (alpogeNativeCanonicalHostEll (alpogeNativeRecMap e q d)) A B y -
    (alpogeNativeGzArithmetic y : ℂ)‖ ≤ _
  rw [hidentity]
  calc
    ‖F B y - F A y - F (A + B) y‖ ≤
        ‖F B y‖ + ‖F A y‖ + ‖F (A + B) y‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ 3 * y ^ ((1 : ℝ) / 2 + eps / 2) := by linarith

/-- Scalar native Gz is recovered at the original varying heights. This
estimate supplies the three-character charge, rather than assuming it.
It can be composed directly with `nativeSelectedDyadicCompleteProjection`.
Only membership of these actual arguments in the same selected window is
required; the height is not silently replaced by the window parameter. -/
theorem nativePairGood_dyadicGz_average_le_projection
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    {eps Y X : ℝ} (hG : UpperTheory.Top.PairGood 1 eps Y X q d)
    (TT : Finset (AlpogeNativeDyadicH e))
    (a : AlpogeNativeDyadicH e → ℝ) (b : ℝ)
    (hwindow : ∀ t ∈ TT, a t / b ∈ Set.Icc Y X) :
    (1 / (TT.card : ℝ)) * ∑ t ∈ TT, alpogeNativeGzArithmetic (a t / b) ≤
      alpogeNativeProjectedSignal (⊤ : AddSubgroup (AlpogeNativeDyadicH e))
        (alpogeNativeFrobInertiaGPsi
          (alpogeNativeHostData e q d).inertia
          (alpogeNativeHostData e q d).frob
          (alpogeNativeCanonicalHostEll (alpogeNativeRecMap e q d))) TT a b +
      (3 / (TT.card : ℝ)) * ∑ t ∈ TT,
        (a t / b) ^ ((1 : ℝ) / 2 + eps / 2) := by
  let S := alpogeNativeFrobInertiaGsig
    (alpogeNativeHostData e q d).inertia
    (alpogeNativeHostData e q d).frob
    (alpogeNativeCanonicalHostEll (alpogeNativeRecMap e q d))
    (alpogeNativeChC (AlpogeNativeDyadicH e))
    (alpogeNativePsC (AlpogeNativeDyadicH e))
  have hp : ∀ t ∈ TT, alpogeNativeGzArithmetic (a t / b) ≤
      (S (a t / b)).re + 3 * (a t / b) ^ ((1 : ℝ) / 2 + eps / 2) := by
    intro t ht
    have hn := nativePairGood_dyadicGsig_sub_Gz_norm_le e q d hG
      (a t / b) (hwindow t ht).1 (hwindow t ht).2
    have hl := (abs_le.mp ((Complex.abs_re_le_norm _).trans hn)).1
    change -(3 * (a t / b) ^ ((1 : ℝ) / 2 + eps / 2)) ≤
      (S (a t / b) - (alpogeNativeGzArithmetic (a t / b) : ℂ)).re at hl
    rw [Complex.sub_re, Complex.ofReal_re] at hl
    linarith
  rw [alpogeNativeProjectedSignal_top_eq_Gsig]
  calc
    (1 / (TT.card : ℝ)) * ∑ t ∈ TT, alpogeNativeGzArithmetic (a t / b) ≤
        (1 / (TT.card : ℝ)) * ∑ t ∈ TT,
          ((S (a t / b)).re + 3 * (a t / b) ^ ((1 : ℝ) / 2 + eps / 2)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hp) (by positivity)
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]; dsimp only [S]; ring

end RHLean.Analysis.AlpogeThin

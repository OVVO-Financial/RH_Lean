import RHLean.Analysis.AlpogeNativeSubgroupProjection
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Exact principal-host attachment of the complete native projection

The annihilator-cardinality argument reconstructs the finite quotient-character
proof in Levent Alpöge's (with Claude) PrimitiveCosets/CardPsiA.lean at
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4.
Source: src/Development/AutomorphicArithmetic/PrimitiveCosets/CardPsiA.lean.
The source archive/mirror states no license; attribution is retained without
assigning a new license to that source-derived argument.

For the principal target A0 is the full host subgroup. Its annihilator consists
of the actual four two-bit characters. The complete native signal is therefore
the TT-average of G0+Gq-Gd-Gqd, at the original variable heights. This file
removes no thin return, logarithmic derivative, or ramified prime power.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical

namespace RHLean.Analysis

private theorem alpogeNativeAddChar_descends
    {G Q M : Type*} [AddCommGroup G] [AddCommGroup Q]
    [CommGroupWithZero M] (π : G →+ Q)
    (hπ : Function.Surjective π) (ψ : AddChar G M)
    (h : ∀ x, π x = 0 → ψ x = 1) :
    ∃ χ : AddChar Q M, χ.compAddMonoidHom π = ψ := by
  have wd : ∀ x y, π x = π y → ψ x = ψ y := by
    intro x y hxy
    have h0 : π (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    calc ψ x = ψ (y + (x - y)) := by rw [add_sub_cancel]
      _ = ψ y * ψ (x - y) := AddChar.map_add_eq_mul ψ _ _
      _ = ψ y := by rw [h _ h0, mul_one]
  let s := Function.surjInv hπ
  have hs : ∀ q, π (s q) = q := Function.surjInv_eq hπ
  refine ⟨{ toFun := fun q => ψ (s q),
    map_zero_eq_one' := ?_, map_add_eq_mul' := ?_ }, ?_⟩
  · rw [wd (s 0) 0 (by rw [hs, map_zero]), AddChar.map_zero_eq_one]
  · intro a b
    rw [← AddChar.map_add_eq_mul,
      wd (s (a + b)) (s a + s b) (by rw [hs, map_add, hs, hs])]
  · ext x
    exact wd _ _ (hs _)

/-- An actual quotient-character bijection gives the native annihilator count. -/
theorem alpogeNativeProjectionChars_card_index
    {H : Type*} [AddCommGroup H] [Fintype H] (A0 : AddSubgroup H) :
    (alpogeNativeProjectionChars A0).card = 4 * A0.index := by
  classical
  let π : AlpogeNativeE0 × H →+ AlpogeNativeE0 × (H ⧸ A0) :=
    (AddMonoidHom.id AlpogeNativeE0).prodMap (QuotientAddGroup.mk' A0)
  have hπ : Function.Surjective π := by
    rintro ⟨a, q⟩
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective A0 q
    exact ⟨(a, b), rfl⟩
  have hinj : Function.Injective
      (fun χ : AddChar (AlpogeNativeE0 × (H ⧸ A0)) ℂ =>
        χ.compAddMonoidHom π) := by
    intro χ1 χ2 h
    ext q
    obtain ⟨x, rfl⟩ := hπ q
    exact DFunLike.congr_fun h x
  have himg : alpogeNativeProjectionChars A0 =
      Finset.univ.image
        (fun χ : AddChar (AlpogeNativeE0 × (H ⧸ A0)) ℂ =>
          χ.compAddMonoidHom π) := by
    ext ψ
    simp only [alpogeNativeProjectionChars, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      refine alpogeNativeAddChar_descends π hπ ψ fun x hx => ?_
      obtain ⟨a, b⟩ := x
      have ha : a = 0 := congrArg Prod.fst hx
      have hb : QuotientAddGroup.mk' A0 b = 0 := congrArg Prod.snd hx
      rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at hb
      subst ha
      exact h b hb
    · rintro ⟨χ, rfl⟩ s hs
      show χ (π (0, s)) = 1
      have hzero : π (0, s) = 0 := by
        simp [π, QuotientAddGroup.eq_zero_iff, hs]
      rw [hzero, AddChar.map_zero_eq_one]
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ,
    AddChar.card_eq, Fintype.card_prod, AddSubgroup.index_eq_card,
    Nat.card_eq_fintype_card]
  simp [AlpogeNativeE0]

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- The second-bit character, complementary to the existing first-bit chC.
In the literal arithmetic host the first bit is d and this second bit is q. -/
def alpogeNativePsC (H : Type*) [AddCommGroup H] [Fintype H] [DecidableEq H] :
    AddChar (AlpogeNativeE0 × H) ℂ :=
  (alpogeNativeChC H).compAddMonoidHom
    { toFun := fun g => ((g.1.2, g.1.1), g.2)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

theorem alpogeNativeChC_projectionE1 (t : H) :
    alpogeNativeChC H (alpogeNativeProjectionE1 t) = -1 := by
  change (if (1 : ZMod 2) = 0 then (1 : ℂ) else -1) = -1
  exact ite_eq_right (by decide)

theorem alpogeNativePsC_projectionE1 (t : H) :
    alpogeNativePsC H (alpogeNativeProjectionE1 t) = 1 := rfl

private theorem alpogeNativePrincipalFour_notmem :
    (0 : AddChar (AlpogeNativeE0 × H) ℂ) ∉
      ({alpogeNativePsC H, alpogeNativeChC H,
        alpogeNativeChC H + alpogeNativePsC H} : Finset _) ∧
    alpogeNativePsC H ∉
      ({alpogeNativeChC H, alpogeNativeChC H + alpogeNativePsC H} : Finset _) ∧
    alpogeNativeChC H ∉
      ({alpogeNativeChC H + alpogeNativePsC H} : Finset _) := by
  classical
  let A := alpogeNativeChC H
  let B := alpogeNativePsC H
  have hAd : A (alpogeNativeProjectionE1 (0 : H)) = -1 :=
    alpogeNativeChC_projectionE1 0
  have hBd : B (alpogeNativeProjectionE1 (0 : H)) = 1 :=
    alpogeNativePsC_projectionE1 0
  have hAq : A (((0, 1) : AlpogeNativeE0), (0 : H)) = 1 := rfl
  have hBq : B (((0, 1) : AlpogeNativeE0), (0 : H)) = -1 := by
    change (if (1 : ZMod 2) = 0 then (1 : ℂ) else -1) = -1
    exact ite_eq_right (by decide)
  have h0B : (0 : AddChar (AlpogeNativeE0 × H) ℂ) ≠ B := by
    intro h
    have hh := DFunLike.congr_fun h ((((0, 1) : AlpogeNativeE0), (0 : H)))
    rw [AddChar.zero_apply, hBq] at hh
    norm_num at hh
  have h0A : (0 : AddChar (AlpogeNativeE0 × H) ℂ) ≠ A := by
    intro h
    have hh := DFunLike.congr_fun h (alpogeNativeProjectionE1 (0 : H))
    rw [AddChar.zero_apply, hAd] at hh
    norm_num at hh
  have h0AB : (0 : AddChar (AlpogeNativeE0 × H) ℂ) ≠ A + B := by
    intro h
    have hh := DFunLike.congr_fun h (alpogeNativeProjectionE1 (0 : H))
    rw [AddChar.zero_apply, AddChar.add_apply, hAd, hBd] at hh
    norm_num at hh
  have hBA : B ≠ A := by
    intro h
    have hh := DFunLike.congr_fun h (alpogeNativeProjectionE1 (0 : H))
    rw [hBd, hAd] at hh
    norm_num at hh
  have hBAB : B ≠ A + B := by
    intro h
    have hh := DFunLike.congr_fun h (alpogeNativeProjectionE1 (0 : H))
    rw [hBd, AddChar.add_apply, hAd, hBd] at hh
    norm_num at hh
  have hAAB : A ≠ A + B := by
    intro h
    have hh := DFunLike.congr_fun h ((((0, 1) : AlpogeNativeE0), (0 : H)))
    rw [hAq, AddChar.add_apply, hAq, hBq] at hh
    norm_num at hh
  change (0 : AddChar (AlpogeNativeE0 × H) ℂ) ∉ ({B, A, A + B} : Finset _) ∧
    B ∉ ({A, A + B} : Finset _) ∧ A ∉ ({A + B} : Finset _)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨⟨h0B, h0A, h0AB⟩, ⟨hBA, hBAB⟩, hAAB⟩

/-- Full-host averaging retains exactly the four genuine two-bit characters.
The ambient host H is arbitrary and is not replaced by a one-element group. -/
theorem alpogeNativeProjectionChars_top :
    alpogeNativeProjectionChars (⊤ : AddSubgroup H) =
      {0, alpogeNativePsC H, alpogeNativeChC H,
        alpogeNativeChC H + alpogeNativePsC H} := by
  classical
  obtain ⟨h0, hB, hA⟩ := alpogeNativePrincipalFour_notmem (H := H)
  have hcard :
      ({0, alpogeNativePsC H, alpogeNativeChC H,
        alpogeNativeChC H + alpogeNativePsC H} :
        Finset (AddChar (AlpogeNativeE0 × H) ℂ)).card = 4 := by
    rw [Finset.card_insert_of_notMem h0, Finset.card_insert_of_notMem hB,
      Finset.card_insert_of_notMem hA, Finset.card_singleton]
  have hsub :
      ({0, alpogeNativePsC H, alpogeNativeChC H,
        alpogeNativeChC H + alpogeNativePsC H} :
        Finset (AddChar (AlpogeNativeE0 × H) ℂ)) ⊆
      alpogeNativeProjectionChars (⊤ : AddSubgroup H) := by
    intro ψ hψ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hψ
    rcases hψ with rfl | rfl | rfl | rfl
    · apply (alpogeNativeProjectionChars_mem _ _).2
      intro s _hs
      exact AddChar.zero_apply _
    · apply (alpogeNativeProjectionChars_mem _ _).2
      intro s _hs
      rfl
    · apply (alpogeNativeProjectionChars_mem _ _).2
      intro s _hs
      rfl
    · apply (alpogeNativeProjectionChars_mem _ _).2
      intro s _hs
      rw [AddChar.add_apply]
      change (1 : ℂ) * 1 = 1
      exact one_mul 1
  have hle : (alpogeNativeProjectionChars (⊤ : AddSubgroup H)).card ≤
      ({0, alpogeNativePsC H, alpogeNativeChC H,
        alpogeNativeChC H + alpogeNativePsC H} :
        Finset (AddChar (AlpogeNativeE0 × H) ℂ)).card := by
    rw [hcard, alpogeNativeProjectionChars_card_index]
    simp
  exact (Finset.eq_of_subset_of_card_le hsub hle).symm

/-- Complete signed projection, with the exact 1+B-A-AB signs. -/
theorem alpogeNativeProjection_top_sum
    (F : AddChar (AlpogeNativeE0 × H) ℂ → ℂ) (t : H) :
    (∑ ψ ∈ alpogeNativeProjectionChars (⊤ : AddSubgroup H),
      ψ (alpogeNativeProjectionE1 t) * F ψ) =
      F 0 + F (alpogeNativePsC H) - F (alpogeNativeChC H) -
        F (alpogeNativeChC H + alpogeNativePsC H) := by
  classical
  obtain ⟨h0, hB, hA⟩ := alpogeNativePrincipalFour_notmem (H := H)
  rw [alpogeNativeProjectionChars_top, Finset.sum_insert h0,
    Finset.sum_insert hB, Finset.sum_insert hA, Finset.sum_singleton]
  simp only [AddChar.zero_apply, AddChar.add_apply,
    alpogeNativeChC_projectionE1, alpogeNativePsC_projectionE1,
    one_mul, mul_one, neg_one_mul]
  ring

/-- The complete signal at the original heights, before any movement to x. -/
theorem alpogeNativeProjectedSignal_top
    (F : AddChar (AlpogeNativeE0 × H) ℂ → ℝ → ℂ)
    (TT : Finset H) (a : H → ℝ) (b : ℝ) :
    alpogeNativeProjectedSignal (⊤ : AddSubgroup H) F TT a b =
      (1 / (TT.card : ℝ)) * ∑ t ∈ TT,
        (F 0 (a t / b) + F (alpogeNativePsC H) (a t / b) -
          F (alpogeNativeChC H) (a t / b) -
          F (alpogeNativeChC H + alpogeNativePsC H) (a t / b)).re := by
  unfold alpogeNativeProjectedSignal
  simp_rw [alpogeNativeProjection_top_sum]

/-- Specialization to every prime power and the original inertia, Frobenius,
and ell terms: the output is the native Gsig itself, averaged over TT. -/
theorem alpogeNativeProjectedSignal_top_eq_Gsig
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (TT : Finset H) (a : H → ℝ) (b : ℝ) :
    alpogeNativeProjectedSignal (⊤ : AddSubgroup H)
      (alpogeNativeFrobInertiaGPsi inertia frob ell) TT a b =
      (1 / (TT.card : ℝ)) * ∑ t ∈ TT,
        (alpogeNativeFrobInertiaGsig inertia frob ell
          (alpogeNativeChC H) (alpogeNativePsC H) (a t / b)).re := by
  exact alpogeNativeProjectedSignal_top
    (alpogeNativeFrobInertiaGPsi inertia frob ell) TT a b

end RHLean.Analysis


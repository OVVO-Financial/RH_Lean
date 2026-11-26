import RHLean.Geometry.NativeCMWeierstrassOriginDivisor

/-!
# The actual origin bundle has exactly one global section over its base

Native declaration cut from Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

- `src/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/SpecMapAwayFnEquivAwayChart.lean`
- `src/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/ExistsUniqueEqConstMulOriginSec.lean`

An explicit pole-order calculation in the original affine coordinate ring
proves every global origin-bundle section is a unique base scalar times
the canonical section. The rings and restriction maps are the actual
scheme charts, over any commutative base ring. No section-dimension or
polarization-kernel premise is introduced. The source archive states no
license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

namespace RHLean.Geometry.NativeCM.SchemeTheory

open SectionPoints Cartier

theorem coeff_eq_zero_of_simple_pole {R B C κ : Type*} [CommRing R] [CommRing B] [CommRing C]
    (ρ : R →+* B) (ι : B →+* C) (hι : Function.Injective ι) (ε : B →+* R)
    (hρ : ∀ r, ε (ρ r) = r) (z : B) (hz : ε z = 0) (d : κ → ℕ) (hd : Function.Injective d)
    (e : κ → C) (v : κ → B) (hv : ∀ k, ι z ^ d k * e k = ι (v k)) (hε : ∀ k, ε (v k) = 1)
    (c : κ → R) (s : Finset κ) (b : B) (h : ι z * ∑ k ∈ s, ι (ρ (c k)) * e k = ι b) :
    ∀ k ∈ s, 2 ≤ d k → c k = 0 := by
  classical
  induction s using Finset.induction_on_max_value d with
  | empty => simp
  | insert a s ha hmax ih =>
    by_cases h2 : 2 ≤ d a
    · have hlt : ∀ k ∈ s, d k < d a := fun k hk =>
        lt_of_le_of_ne (hmax k hk) fun e => ha (hd e ▸ hk)
      have key : ρ (c a) * v a + ∑ k ∈ s, ρ (c k) * (z ^ (d a - d k) * v k) = z ^ (d a - 1) * b := by
        apply hι
        rw [map_mul ι (z ^ _), ← h, map_pow, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega),
          Finset.sum_insert ha, mul_add, map_add, map_sum, Finset.mul_sum, map_mul, ← hv]
        refine congrArg₂ (· + ·) (by ring) (Finset.sum_congr rfl fun k hk => ?_)
        obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (hlt k hk).le
        rw [map_mul, map_mul, map_pow, ← hv, hm, Nat.add_sub_cancel_left]
        ring
      have hca : c a = 0 := by
        have := congrArg ε key
        rw [map_add, map_sum, map_mul, map_mul, map_pow, hz, zero_pow (by omega), zero_mul, hρ, hε,
          mul_one, Finset.sum_eq_zero, add_zero] at this
        · exact this
        · intro k hk
          have := hlt k hk
          rw [map_mul, map_mul, map_pow, hz, zero_pow (by omega), zero_mul, mul_zero]
      rw [Finset.sum_insert ha, hca, map_zero, map_zero, zero_mul, zero_add] at h
      intro k hk
      rcases Finset.mem_insert.1 hk with rfl | hk
      · exact fun _ => hca
      · exact ih h k hk
    · intro k hk hk2
      rcases Finset.mem_insert.1 hk with rfl | hk
      · exact absurd hk2 h2
      · have := hmax k hk
        omega

namespace WeierstrassCurve

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

def affineFnEquiv : W.toAffine.CoordinateRing ≃+* Γ(scheme W, coordOpen W 2) :=
  (awayEquivAffine W).symm.trans (awayFnEquiv W 2)

@[simp] theorem affineFnEquiv_affineX : affineFnEquiv W (affineX W) = ratio W 2 0 := by
  have : awayEquivAffine W (awayCoord W 2 0) = affineX W :=
    (mul_one _).symm.trans (awayEval_awayCoord_mul W 2 (algebraMap R _) ![affineX W, affineY W, 1]
      (isUnimodularSol_some (equation_affineX_affineY W)).equation isUnit_one 0)
  simp [affineFnEquiv, ← this]

@[simp] theorem affineFnEquiv_affineY : affineFnEquiv W (affineY W) = ratio W 2 1 := by
  have : awayEquivAffine W (awayCoord W 2 1) = affineY W :=
    (mul_one _).symm.trans (awayEval_awayCoord_mul W 2 (algebraMap R _) ![affineX W, affineY W, 1]
      (isUnimodularSol_some (equation_affineX_affineY W)).equation isUnit_one 1)
  simp [affineFnEquiv, ← this]

@[simp] theorem affineFnEquiv_algebraMap (r : R) :
    affineFnEquiv W (algebraMap R _ r) = constOn W _ r := by
  have : awayEquivAffine W (awayConst W 2 r) = algebraMap R _ r :=
    awayEval_awayConst W 2 (algebraMap R _) ![affineX W, affineY W, 1]
      (isUnimodularSol_some (equation_affineX_affineY W)).equation isUnit_one r
  simp [affineFnEquiv, ← this]

theorem exists_eq_constOn (f₀ : Γ(scheme W, originOpen W)) (f₁ : Γ(scheme W, coordOpen W 2))
    (h : resG _ inf_le_left f₀ = (originUnit W : Γ(scheme W, originOpen W ⊓ coordOpen W 2)) *
      resG _ inf_le_right f₁) :
    ∃ c : R, f₀ = constOn W _ c * originParam W ∧ f₁ = constOn W _ c := by
  obtain ⟨b, rfl⟩ := (affineFnEquiv W).surjective f₁
  obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq b
  have h₀ : originOpen W ⊓ coordOpen W 2 ≤ originOpen W := inf_le_left
  have h₁ : originOpen W ⊓ coordOpen W 2 ≤ coordOpen W 1 := h₀.trans (originOpen_le W)
  have h₂ : originOpen W ⊓ coordOpen W 2 ≤ coordOpen W 2 := inf_le_right
  set z := ratioOn W _ 1 h₁ 0 with hz
  set x := ratioOn W _ 2 h₂ 0 with hx
  set y := ratioOn W _ 2 h₂ 1 with hy
  set u := originCofactor W _ h₁ with hu
  have ey : z ^ 3 * y = u := by
    rw [hz, ← ratioOn_mul_originCofactor, mul_right_comm, ratioOn_mul_ratioOn, ratioOn_self, one_mul]
  have ex : z ^ 2 * x = u := by
    refine (isUnit_ratioOn_one_zero h₀ h₂).mul_left_cancel ?_
    rw [← mul_assoc, ← pow_succ', ← ratioOn_mul_originCofactor, mul_right_comm, ratioOn_mul_ratioOn]
  let ψ : W.toAffine.CoordinateRing →+* _ := (resG _ h₂).comp (affineFnEquiv W).toRingHom
  have hψ : ∀ p : Polynomial R, ψ (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine
      (Polynomial.C p)) = ∑ i ∈ p.support, constOn W _ (p.coeff i) * x ^ i := fun p => by
    have : (ψ.comp (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine)).comp Polynomial.C =
        Polynomial.eval₂RingHom (constOn W _) x := by
      refine Polynomial.ringHom_ext (fun r => ?_) ?_
      · rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
        exact (congrArg (resG _ h₂) (affineFnEquiv_algebraMap W r)).trans (resG_constOn h₂ r)
      · rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
        exact congrArg (resG _ h₂) (affineFnEquiv_affineX W)
    exact (RingHom.congr_fun this p).trans (Polynomial.eval₂_eq_sum.trans (Polynomial.sum_def _ _))
  have hψy : ψ (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Polynomial.X) = y :=
    congrArg (resG _ h₂) (affineFnEquiv_affineY W)
  have key := coeff_eq_zero_of_simple_pole (constOn W (originOpen W)) (resG _ h₀)
    (resG_originOpen_injective W) (originValue W) (evalPt_zero_constOn _) (originParam W)
    (originValue_originParam W) (Sum.elim (fun i => 2 * i) (fun i => 2 * i + 3))
    (by rintro (i | i) (j | j) e <;> simp only [Sum.elim_inl, Sum.elim_inr] at e <;>
      (congr 1; omega))
    (Sum.elim (fun i => x ^ i) (fun i => x ^ i * y))
    (Sum.elim (fun i => originCofactor W _ (originOpen_le W) ^ i)
      (fun i => originCofactor W _ (originOpen_le W) ^ (i + 1)))
    (by
      rintro (i | i) <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
        rw [map_pow, resG_originCofactor, resG_ratioOn, ← hz, ← hu]
      · rw [← ex]; ring
      · rw [pow_succ u]
        nth_rw 2 [← ey]
        rw [← ex]; ring)
    (by rintro (i | i) <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
      rw [map_pow, evalPt_zero_originCofactor, one_pow])
    (Sum.elim p.coeff q.coeff) (p.support.disjSum q.support) f₀ (by
      rw [h, Finset.sum_disjSum]
      refine congrArg₂ (· * ·) rfl (Eq.symm ?_)
      change ψ _ = _
      rw [map_add, WeierstrassCurve.Affine.CoordinateRing.smul,
        WeierstrassCurve.Affine.CoordinateRing.smul, mul_one, map_mul, hψ, hψ, hψy, Finset.sum_mul]
      simp only [Sum.elim_inl, Sum.elim_inr, resG_constOn, mul_assoc])
  have hq : q = 0 := by
    ext i
    by_contra hi
    exact hi (key (.inr i) (Finset.inr_mem_disjSum.2 (Polynomial.mem_support_iff.2 hi))
      (by simp only [Sum.elim_inr]; omega))
  have hp : p = Polynomial.C (p.coeff 0) := by
    ext i
    rcases i with _ | i
    · simp
    · rw [Polynomial.coeff_C_succ]
      by_contra hi
      exact hi (key (.inl (i + 1)) (Finset.inl_mem_disjSum.2 (Polynomial.mem_support_iff.2 hi))
        (by simp only [Sum.elim_inl]; omega))
  have e₁ : affineFnEquiv W (p • (1 : W.toAffine.CoordinateRing) +
      q • WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Polynomial.X) =
      constOn W _ (p.coeff 0) := by
    rw [hq, zero_smul, add_zero, WeierstrassCurve.Affine.CoordinateRing.smul, mul_one]
    conv_lhs => rw [hp]
    exact affineFnEquiv_algebraMap W _
  refine ⟨p.coeff 0, resG_originOpen_injective W ?_, e₁⟩
  rw [h, e₁, map_mul, resG_constOn, resG_constOn, mul_comm]
  rfl

theorem constOn_coordOpen_two_injective : Function.Injective (constOn W (coordOpen W 2)) := by
  intro c c' h
  have h₁ := congrArg (resG _ (inf_le_right : originOpen W ⊓ coordOpen W 2 ≤ _)) h
  rw [resG_constOn, resG_constOn, ← resG_constOn inf_le_left, ← resG_constOn inf_le_left c'] at h₁
  have h₂ := congrArg (originValue W) (resG_originOpen_injective W h₁)
  rwa [evalPt_zero_constOn, evalPt_zero_constOn] at h₂

theorem existsUnique_eq_const_mul_originSec (s : (originLB W).Sec) :
    ∃! c : R, ∀ i, s.f i = constFn (toSpec W) _ c * (originSec W).f i := by
  obtain ⟨c, h₀, h₁⟩ := exists_eq_constOn W (s.f true) (s.f false) (s.compat true false)
  refine ⟨c, ?_, fun c' hc' => constOn_coordOpen_two_injective W ?_⟩
  · rintro (_ | _)
    · exact h₁.trans (mul_one _).symm
    · exact h₀
  · exact ((hc' false).trans (mul_one _)).symm.trans h₁


end WeierstrassCurve

end RHLean.Geometry.NativeCM.SchemeTheory

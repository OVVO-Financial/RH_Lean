import RHLean.Geometry.NativeThetaCuspFourier
import RHLean.Geometry.NativeThetaCuspPoissonCosets
import RHLean.Geometry.NativeThetaCuspSiegelAction
import RHLean.Geometry.NativeThetaCuspSeries

/-!
# Genuine unitary theta transformation for the Fourier generator

Poisson summation on the actual residue cosets is combined with the proved
finite Fourier transform. This yields the original theta transformation
law for J, with its determinant weight and exact power of I, together
with preservation of the original Haar inner product.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsUnitarySiegelThetaTransformationLawStandar.lean.
The source mirror states no license; attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Matrix Complex
open scoped ComplexConjugate Real BigOperators Classical

namespace RHLean.Geometry.NativeTheta.Cusp.FourierJ

variable {κ ι : Type} [Fintype κ] [Fintype ι]

theorem thS_eq [DecidableEq ι] (φ : Matrix κ ι ℚ → ℂ) (τ : Matrix ι ι ℂ) (ζ : κ → ι → ℂ) :
    thS φ τ ζ = ∑' x : Matrix κ ι ℚ, φ x * ∏ k, gs τ (ζ k) (x k) := by
  simp only [thS, gs, ← Complex.exp_sum, Finset.mul_sum]

omit [Fintype κ] [Fintype ι] in
theorem tsum_supp {R : ℕ} (hR : 0 < R) {ψ : Matrix κ ι ℚ → ℂ} (h : HasLevel R ψ)
    (G : Matrix κ ι ℚ → ℂ) :
    ∑' y, ψ y * G y = ∑' m : κ → ι → ℤ, ψ ((R : ℚ)⁻¹ • zm m) * G ((R : ℚ)⁻¹ • zm m) := by
  have hR0 : (R : ℚ) ≠ 0 := by exact_mod_cast hR.ne'
  have hinj : Function.Injective fun m : κ → ι → ℤ => (R : ℚ)⁻¹ • zm m := by
    intro m m' hm
    ext k i
    have := congrFun (congrFun hm k) i
    simpa [zm, hR.ne'] using this
  refine (hinj.tsum_eq (f := fun y => ψ y * G y) ?_).symm
  intro y hy
  obtain ⟨m, hm⟩ := (intM_iff _).1 (h.1 y (left_ne_zero_of_mul hy))
  exact ⟨m, by simp only [← hm, smul_smul, inv_mul_cancel₀ hR0, one_smul]⟩

theorem spDen_J [DecidableEq ι] (τ : Matrix ι ι ℂ) : spDen (Matrix.J ι ℚ) τ = τ := by
  have h1 : qm (1 : Matrix ι ι ℚ) = 1 := by
    ext i j; simp [qm, Matrix.one_apply]; split_ifs <;> simp
  have h0 : qm (0 : Matrix ι ι ℚ) = 0 := by ext i j; simp [qm]
  simp [spDen, Matrix.J, h1, h0]

omit [Fintype ι] in
theorem qm_J [DecidableEq ι] : qm (Matrix.J ι ℚ).toBlocks₂₁ = 1 := by
  ext i j; simp [qm, Matrix.J, Matrix.one_apply]; split_ifs <;> simp

theorem spAct_J [DecidableEq ι] (τ : Matrix ι ι ℂ) : spAct (Matrix.J ι ℚ) τ = -τ⁻¹ := by
  have h1 : qm (-1 : Matrix ι ι ℚ) = -1 := by
    ext i j; simp [qm, Matrix.one_apply]; split_ifs <;> simp
  have h0 : qm (0 : Matrix ι ι ℚ) = 0 := by ext i j; simp [qm]
  rw [spAct, spDen_J]
  simp [Matrix.J, h1, h0]

theorem trans_J [DecidableEq ι] {p : ℕ} (hp : Fintype.card κ = p + p) {R : ℕ} (hR : 0 < R)
    {φ : Matrix κ ι ℚ → ℂ} (h : HasLevel R φ) :
    TransS (Matrix.J ι ℚ) φ fun y => I ^ (Fintype.card ι * p) * ft φ y := by
  classical
  intro τ hτ ζ
  have hR0 : (R : ℚ) ≠ 0 := by exact_mod_cast hR.ne'
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  obtain ⟨hd, hs, -⟩ := SiegelAction.symplectic_action ι _ (SymplecticGroup.J_mem ι ℚ) τ hτ
  rw [spAct_J] at hs
  rw [spDen_J] at hd
  obtain ⟨c, hc, hrow⟩ := Row.poisson_class ι R hR τ hτ hs (Ne.isUnit hd)
  rw [spAct_J, spDen_J, qm_J, Matrix.mul_one, thS_eq, thS_eq,
    tsum_supp hR (ft_level hR h _)]
  have hsum : Summable fun x : Matrix κ ι ℚ => φ x * ∏ k, gs τ (ζ k) (x k) := by
    have := (RHLean.Geometry.NativeTheta.Cusp.SiegelSum.summable_norm_thetaTerm κ ι φ ⟨R, hR, h⟩ τ hτ ζ).of_norm
    simpa only [gs, ← Complex.exp_sum, Finset.mul_sum] using this
  rw [tsum_level_eq_sum_cosets κ ι R φ _ hR h hsum]
  set V : ℂ := (R : ℂ) ^ (Fintype.card κ * Fintype.card ι) with hV
  set T : (κ → ι → Fin (R * R)) → κ → (ι → ℤ) → ℂ := fun n k m =>
    ech (rep R n k ⬝ᵥ ((R : ℚ)⁻¹ • zv m)) * gs (-τ⁻¹) (ζ k ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • zv m) with hT
  have hTs : ∀ n k, Summable fun m => ‖T n k m‖ := fun n k => by
    simpa only [hT, norm_mul, norm_ech, one_mul] using (hrow 0 (ζ k)).2.1
  have hconst : τ.det ^ p * c ^ (p + p) = I ^ (Fintype.card ι * p) * V⁻¹ := by
    have hV0 : V ≠ 0 := pow_ne_zero _ hRc
    have h1 : (c ^ 2 * (((-I) * (R : ℂ) ^ 2) ^ Fintype.card ι * τ.det)) ^ p = 1 := by
      rw [hc, one_pow]
    have h2 : ((-I) * I) ^ (Fintype.card ι * p) = 1 := by simp
    rw [eq_mul_inv_iff_mul_eq₀ hV0, hV, hp]
    calc _ = τ.det ^ p * c ^ (p + p) * (R : ℂ) ^ ((p + p) * Fintype.card ι) *
          ((-I) * I) ^ (Fintype.card ι * p) := by rw [h2, mul_one]
      _ = I ^ (Fintype.card ι * p) *
          (c ^ 2 * (((-I) * (R : ℂ) ^ 2) ^ Fintype.card ι * τ.det)) ^ p := by
        simp only [mul_pow, ← pow_mul]; ring
      _ = _ := by rw [h1, mul_one]
  have hl : ∀ m : κ → ι → ℤ, I ^ (Fintype.card ι * p) * ft φ ((R : ℚ)⁻¹ • zm m) *
      ∏ k, gs (-τ⁻¹) (ζ k ᵥ* τ⁻¹) (((R : ℚ)⁻¹ • zm m) k) =
      ∑ n : κ → ι → Fin (R * R), (I ^ (Fintype.card ι * p) * V⁻¹ * φ (rep R n)) *
        ∏ k, T n k (m k) := by
    intro m
    have hm : IntM ((R : ℚ) • (R : ℚ)⁻¹ • zm m) := by
      rw [smul_smul, mul_inv_cancel₀ hR0, one_smul]; exact (intM_iff _).2 ⟨m, rfl⟩
    rw [ft_eq hR h hm, ← hV, ← mul_assoc, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hT, Finset.prod_mul_distrib, pr, ech_sum, mul_assoc]
    rfl
  simp only [hl]
  rw [Summable.tsum_finsetSum fun n _ =>
    ((tsum_pi_prod κ _ (T n) (hTs n)).1.of_norm.mul_left _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [tsum_mul_left, (tsum_pi_prod κ _ (T n) (hTs n)).2]
  have hr := (tsum_pi_prod κ _ (fun k (m : ι → ℤ) => gs τ (ζ k) (rep R n k + (R : ℚ) • zv m))
    (fun k => (hrow _ _).1)).2
  have hr' : ∑' m : κ → ι → ℤ, ∏ k, gs τ (ζ k) ((rep R n + (R : ℚ) • zm m) k) =
      ∏ k, ∑' m : ι → ℤ, gs τ (ζ k) (rep R n k + (R : ℚ) • zv m) := hr
  have hp2 : Fintype.card κ / 2 = p := by omega
  have hprod : cexp (π * I * ∑ k, ζ k ⬝ᵥ τ⁻¹ *ᵥ ζ k) *
      ∏ k, ∑' m : ι → ℤ, gs τ (ζ k) (rep R n k + (R : ℚ) • zv m) =
      c ^ (p + p) * ∏ k, ∑' m, T n k m := by
    rw [Finset.mul_sum, Complex.exp_sum, ← Finset.prod_mul_distrib, ← hp, ← Finset.card_univ,
      ← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => (hrow _ _).2.2
  rw [hr', hp2, ← hconst]
  linear_combination (-(τ.det ^ p * φ (rep R n))) * hprod

theorem exists_trans_J : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι],
    Even (Fintype.card κ) → ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, IsSB φ →
      IsSB (ω φ) ∧ TransS (Matrix.J ι ℚ) φ (ω φ) ∧
        ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ' := by
  intro κ ι _ _ _ ⟨p, hp⟩
  refine ⟨fun φ y => I ^ (Fintype.card ι * p) * ft φ y, fun φ ⟨R, hR, h⟩ =>
    ⟨⟨R, hR, ft_level hR h _⟩, trans_J hp hR h, fun φ' ⟨S, hS, h'⟩ => ?_⟩⟩
  refine plancherel (Nat.mul_pos hR hS) (level_mul h S) (by rw [mul_comm]; exact level_mul h' R) _ ?_
  rw [map_pow, ← mul_pow]; simp


/-- The previously constructed, exactly normalized Fourier operator
satisfies the genuine theta law for the standard symplectic generator. -/
theorem fourierJ_transS [DecidableEq ι] (hκ : Even (Fintype.card κ))
    {φ : Matrix κ ι ℚ → ℂ} (hφ : IsSB φ) :
    TransS (Matrix.J ι ℚ) φ (fourierJ φ) := by
  obtain ⟨p, hp⟩ := hκ
  obtain ⟨R, hR, hφ⟩ := hφ
  have hp2 : Fintype.card κ / 2 = p := by omega
  simpa only [fourierJ, hp2] using trans_J hp hR hφ


end RHLean.Geometry.NativeTheta.Cusp.FourierJ

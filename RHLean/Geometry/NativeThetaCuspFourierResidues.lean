import RHLean.Geometry.NativeThetaCuspHaarAlgebra

/-!
# Exact finite quotient representatives for the native Haar integral

The rational Schwartz–Bruhat level is evaluated on the actual quotient
representatives in (R⁻¹ℤ/Rℤ)^(κ×ι). Both the finite Haar sum and the
absolutely convergent sum over its lattice cosets are proved with their
original normalizations. These are the finite Fourier generator's inputs.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EchEqOneIff.lean,
src/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatIntegralEqSumResidueRepresentative.lean,
src/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TsumSchwartzBruhatLevelEqSumResidueCosets.lean.
Duplicate representative proofs are shared. The source mirror states no
license; attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Matrix Complex
open scoped ComplexConjugate Real BigOperators Classical

namespace RHLean.Geometry.NativeTheta.Cusp.FourierJ

variable {κ ι : Type}

def rep (R : ℕ) (n : κ → ι → Fin (R * R)) : Matrix κ ι ℚ :=
  Matrix.of fun k i => ((n k i : ℕ) : ℚ) / R

def zm (m : κ → ι → ℤ) : Matrix κ ι ℚ := Matrix.of fun k i => (m k i : ℚ)

def zv (m : ι → ℤ) : ι → ℚ := fun i => (m i : ℚ)

def ech (t : ℚ) : ℂ := cexp (2 * π * I * (t : ℂ))

def gs [Fintype ι] (τ : Matrix ι ι ℂ) (ζ : ι → ℂ) (v : ι → ℚ) : ℂ :=
  cexp (π * I * (qv v ⬝ᵥ τ *ᵥ qv v + 2 * (qv v ⬝ᵥ ζ)))

theorem ech_add (s t : ℚ) : ech (s + t) = ech s * ech t := by
  unfold ech
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ech_zero : ech 0 = 1 := by
  simp [ech]

theorem ech_int (m : ℤ) : ech (m : ℚ) = 1 := by
  unfold ech
  rw [show (2 : ℂ) * π * I * ((m : ℚ) : ℂ) = (m : ℂ) * (2 * π * I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I m

theorem ech_eq_one_iff (t : ℚ) : ech t = 1 ↔ ∃ m : ℤ, t = m := by
  unfold ech
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h : (t : ℂ) = ((n : ℚ) : ℂ) := by
      apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
      rw [hn]
      push_cast
      ring
    exact_mod_cast h
  · rintro ⟨m, rfl⟩
    exact ⟨m, by push_cast; ring⟩

theorem norm_ech (t : ℚ) : ‖ech t‖ = 1 := by
  unfold ech
  rw [show (2 : ℂ) * π * I * (t : ℂ) = ((2 * π * t : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem conj_ech (t : ℚ) : conj (ech t) = ech (-t) := by
  unfold ech
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_ratCast]
  push_cast
  ring

theorem ech_sum {α : Type} (s : Finset α) (f : α → ℚ) : ech (∑ a ∈ s, f a) = ∏ a ∈ s, ech (f a) := by
  unfold ech
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum]

theorem intM_iff (x : Matrix κ ι ℚ) : IntM x ↔ ∃ m : κ → ι → ℤ, x = zm m := by
  constructor
  · intro h
    choose m hm using fun k i => (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp (h k i)
    refine ⟨m, Matrix.ext fun k i => ?_⟩
    rw [← hm k i]
    simp [zm]
  · rintro ⟨m, rfl⟩ k i
    simpa [zm] using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ ℚ (m k i)))


open Matrix Complex in
open scoped ComplexConjugate Real in
theorem exists_rep_add_smul_zm_of_intM_smul {κ ι : Type} [Fintype κ] [Fintype ι] {R : ℕ}
    (hR : 0 < R) (x : Matrix κ ι ℚ) (hx : RHLean.Geometry.NativeTheta.Cusp.IntM (R • x)) :
    ∃ (n : κ → ι → Fin (R * R)) (m : κ → ι → ℤ),
      x = RHLean.Geometry.NativeTheta.Cusp.FourierJ.rep R n + R • RHLean.Geometry.NativeTheta.Cusp.FourierJ.zm m := by
  obtain ⟨M, hM⟩ := (RHLean.Geometry.NativeTheta.Cusp.FourierJ.intM_iff _).mp hx
  have hRR : (0 : ℤ) < (R : ℤ) * R := by positivity
  have hRq : (R : ℚ) ≠ 0 := by positivity
  refine ⟨fun k i => ⟨(M k i % ((R : ℤ) * R)).toNat, ?_⟩, fun k i => M k i / ((R : ℤ) * R), ?_⟩
  · have h1 := Int.emod_nonneg (M k i) hRR.ne'
    have h2 := Int.emod_lt_of_pos (M k i) hRR
    have h3 : ((M k i % ((R : ℤ) * R)).toNat : ℤ) < (R : ℤ) * R := by
      rw [Int.toNat_of_nonneg h1]; exact h2
    exact_mod_cast h3
  · ext k i
    have hk := congrFun (congrFun hM k) i
    simp only [Matrix.smul_apply, RHLean.Geometry.NativeTheta.Cusp.FourierJ.zm, Matrix.of_apply, nsmul_eq_mul] at hk
    simp only [RHLean.Geometry.NativeTheta.Cusp.FourierJ.rep, Matrix.add_apply, Matrix.smul_apply,
      Matrix.of_apply, RHLean.Geometry.NativeTheta.Cusp.FourierJ.zm, nsmul_eq_mul]
    have h1 := Int.emod_nonneg (M k i) hRR.ne'
    have hn : (((M k i % ((R : ℤ) * R)).toNat : ℕ) : ℚ) = ((M k i % ((R : ℤ) * R) : ℤ) : ℚ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h1]
    have hq : ((M k i % ((R : ℤ) * R) : ℤ) : ℚ) + (R : ℚ) * R * ((M k i / ((R : ℤ) * R) : ℤ) : ℚ)
        = (M k i : ℚ) := by
      have := Int.mul_ediv_add_emod (M k i) ((R : ℤ) * R)
      have h' : (R : ℚ) * R * ((M k i / ((R : ℤ) * R) : ℤ) : ℚ) +
          ((M k i % ((R : ℤ) * R) : ℤ) : ℚ) = (M k i : ℚ) := by
        exact_mod_cast this
      linear_combination h'
    have hx' : x k i = (M k i : ℚ) / R := by
      rw [eq_div_iff hRq]
      linear_combination hk
    rw [hx', hn, ← hq, add_div]
    congr 1
    rw [mul_assoc, mul_div_cancel_left₀ _ hRq]

open Matrix Complex in
open scoped ComplexConjugate Real in
private theorem mem_perSub_iff_exists_eq_smul_zm {κ ι : Type} [Fintype κ] [Fintype ι] (R : ℕ)
    (y : Matrix κ ι ℚ) : y ∈ RHLean.Geometry.NativeTheta.Cusp.perSub ℚ κ ι R ↔
      ∃ m : κ → ι → ℤ, y = R • RHLean.Geometry.NativeTheta.Cusp.FourierJ.zm m := by
  rw [RHLean.Geometry.NativeTheta.Cusp.HaarLevel.mem_perSub]
  constructor
  · rintro ⟨y', rfl⟩
    obtain ⟨m, hm⟩ := (RHLean.Geometry.NativeTheta.Cusp.FourierJ.intM_iff _).mp
      ((RHLean.Geometry.NativeTheta.Cusp.HaarLevel.intM_iff _).mpr ⟨y', rfl⟩)
    exact ⟨m, by rw [hm]⟩
  · rintro ⟨m, rfl⟩
    obtain ⟨y', hy'⟩ := (RHLean.Geometry.NativeTheta.Cusp.HaarLevel.intM_iff _).mp
      ((RHLean.Geometry.NativeTheta.Cusp.FourierJ.intM_iff _).mpr ⟨m, rfl⟩)
    exact ⟨y', by rw [hy']⟩

open Matrix Complex in
open scoped ComplexConjugate Real in
theorem rep_injective_of_neg_add_eq_smul_zm {κ ι : Type} {R : ℕ} (hR : 0 < R)
    {n n' : κ → ι → Fin (R * R)} (m : κ → ι → ℤ)
    (hm : -RHLean.Geometry.NativeTheta.Cusp.FourierJ.rep R n + RHLean.Geometry.NativeTheta.Cusp.FourierJ.rep R n' =
      R • RHLean.Geometry.NativeTheta.Cusp.FourierJ.zm m) : n = n' := by
    funext k i
    have hk := congrFun (congrFun hm k) i
    simp only [RHLean.Geometry.NativeTheta.Cusp.FourierJ.rep, Matrix.add_apply, Matrix.neg_apply,
      Matrix.of_apply, Matrix.smul_apply, RHLean.Geometry.NativeTheta.Cusp.FourierJ.zm, nsmul_eq_mul] at hk
    have hRq : (R : ℚ) ≠ 0 := by positivity
    rw [neg_add_eq_sub, ← sub_div, div_eq_iff hRq] at hk
    have hzq : ((n' k i : ℕ) : ℚ) - (n k i : ℕ) = (R : ℚ) * R * m k i := by
      linear_combination hk
    have hz : ((n' k i : ℕ) : ℤ) - (n k i : ℕ) = (R : ℤ) * R * m k i := by
      exact_mod_cast hzq
    have hb : ((n' k i : ℕ) : ℤ) < (R : ℤ) * R := by exact_mod_cast (n' k i).isLt
    have ha : ((n k i : ℕ) : ℤ) < (R : ℤ) * R := by exact_mod_cast (n k i).isLt
    have h0 : ((n' k i : ℕ) : ℤ) - (n k i : ℕ) = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd ⟨m k i, hz⟩
      rw [abs_lt]
      constructor <;>
        linarith [Int.natCast_nonneg (n k i : ℕ), Int.natCast_nonneg (n' k i : ℕ)]
    exact Fin.ext (by omega)

open Matrix Complex in
open scoped ComplexConjugate Real in

theorem haar_eq_sum_rep : ∀ (κ ι : Type) [Fintype κ]
    [Fintype ι] [DecidableEq κ] [DecidableEq ι] (R : ℕ) (φ : Matrix κ ι ℚ → ℂ), 0 < R →
    RHLean.Geometry.NativeTheta.Cusp.HasLevel R φ → RHLean.Geometry.NativeTheta.Cusp.haar φ =
      ((R : ℂ) ^ (Fintype.card κ * Fintype.card ι))⁻¹ *
        ∑ n : κ → ι → Fin (R * R), φ (RHLean.Geometry.NativeTheta.Cusp.FourierJ.rep R n) := by
  intro κ ι _ _ _ _ R φ hR hφ
  classical
  obtain ⟨h1, -⟩ := RHLean.Geometry.NativeTheta.Cusp.haar_eq_haarAt ℚ κ ι R φ hR hφ
  rw [h1]
  unfold RHLean.Geometry.NativeTheta.Cusp.haarAt
  rw [Module.finrank_self, one_mul]
  congr 1
  have hper : ∀ x : Matrix κ ι ℚ, φ (Quotient.out
      (QuotientAddGroup.mk x : Matrix κ ι ℚ ⧸ RHLean.Geometry.NativeTheta.Cusp.perSub ℚ κ ι R)) = φ x := by
    intro x
    have hmem : -x + Quotient.out
        (QuotientAddGroup.mk x : Matrix κ ι ℚ ⧸ RHLean.Geometry.NativeTheta.Cusp.perSub ℚ κ ι R) ∈
        RHLean.Geometry.NativeTheta.Cusp.perSub ℚ κ ι R :=
      QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' _).symm
    have h := RHLean.Geometry.NativeTheta.Cusp.HaarLevel.periodic hφ x _ hmem
    rwa [add_neg_cancel_left] at h
  have hsupp : (Function.support fun q : Matrix κ ι ℚ ⧸ RHLean.Geometry.NativeTheta.Cusp.perSub ℚ κ ι R =>
      φ (Quotient.out q)) ⊆ ↑(Finset.univ.image fun n : κ → ι → Fin (R * R) =>
        (QuotientAddGroup.mk (RHLean.Geometry.NativeTheta.Cusp.FourierJ.rep R n) :
          Matrix κ ι ℚ ⧸ RHLean.Geometry.NativeTheta.Cusp.perSub ℚ κ ι R)) := by
    intro q hq
    obtain ⟨n, m, hnm⟩ := exists_rep_add_smul_zm_of_intM_smul hR _ (hφ.1 _ (Function.mem_support.mp hq))
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    refine ⟨n, ?_⟩
    rw [← QuotientAddGroup.out_eq' q, hnm, QuotientAddGroup.eq, neg_add_cancel_left]
    exact (mem_perSub_iff_exists_eq_smul_zm R _).mpr ⟨m, rfl⟩
  have hinj : Function.Injective fun n : κ → ι → Fin (R * R) =>
      (QuotientAddGroup.mk (RHLean.Geometry.NativeTheta.Cusp.FourierJ.rep R n) :
        Matrix κ ι ℚ ⧸ RHLean.Geometry.NativeTheta.Cusp.perSub ℚ κ ι R) := by
    intro n n' h
    obtain ⟨m, hm⟩ := (mem_perSub_iff_exists_eq_smul_zm R _).mp (QuotientAddGroup.eq.mp h)
    exact rep_injective_of_neg_add_eq_smul_zm hR m hm
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image (fun n _ n' _ h => hinj h)]
  exact Finset.sum_congr rfl fun n _ => hper _


theorem tsum_level_eq_sum_cosets : ∀ (κ ι : Type) [Fintype κ] [Fintype ι]
    [DecidableEq κ]
    [DecidableEq ι] (R : ℕ) (φ F : Matrix κ ι ℚ → ℂ), 0 < R → RHLean.Geometry.NativeTheta.Cusp.HasLevel R φ →
    Summable (fun x => φ x * F x) → ∑' x, φ x * F x =
      ∑ n : κ → ι → Fin (R * R), φ (RHLean.Geometry.NativeTheta.Cusp.FourierJ.rep R n) *
        ∑' m : κ → ι → ℤ, F (RHLean.Geometry.NativeTheta.Cusp.FourierJ.rep R n +
          (R : ℚ) • RHLean.Geometry.NativeTheta.Cusp.FourierJ.zm m) := by
  intro κ ι _ _ _ _ R φ F hR hφ hsum
  have hRq : (R : ℚ) ≠ 0 := by positivity
  have hsmul : ∀ m : κ → ι → ℤ, (R : ℚ) • RHLean.Geometry.NativeTheta.Cusp.FourierJ.zm m = R • RHLean.Geometry.NativeTheta.Cusp.FourierJ.zm m :=
    fun m => Nat.cast_smul_eq_nsmul ℚ R _
  let e : (κ → ι → Fin (R * R)) × (κ → ι → ℤ) → Matrix κ ι ℚ := fun p =>
    RHLean.Geometry.NativeTheta.Cusp.FourierJ.rep R p.1 + (R : ℚ) • RHLean.Geometry.NativeTheta.Cusp.FourierJ.zm p.2
  have he : Function.Injective e := by
    rintro ⟨n, m⟩ ⟨n', m'⟩ h
    simp only [e] at h
    have hn : n = n' := by
      apply rep_injective_of_neg_add_eq_smul_zm hR (m - m')
      ext k i
      have hk := congrFun (congrFun h k) i
      simp only [RHLean.Geometry.NativeTheta.Cusp.FourierJ.rep, Matrix.add_apply, Matrix.neg_apply,
        Matrix.of_apply, Matrix.smul_apply, RHLean.Geometry.NativeTheta.Cusp.FourierJ.zm, nsmul_eq_mul, smul_eq_mul,
        Pi.sub_apply] at hk ⊢
      push_cast
      linear_combination -hk
    subst hn
    have hm : m = m' := by
      funext k i
      have hk := congrFun (congrFun h k) i
      simp only [Matrix.add_apply, Matrix.smul_apply, RHLean.Geometry.NativeTheta.Cusp.FourierJ.zm, Matrix.of_apply,
        smul_eq_mul, add_right_inj] at hk
      exact_mod_cast mul_left_cancel₀ hRq hk
    rw [hm]
  have hsupp : Function.support (fun x => φ x * F x) ⊆ Set.range e := by
    intro x hx
    have hφx : φ x ≠ 0 := left_ne_zero_of_mul (Function.mem_support.mp hx)
    obtain ⟨n, m, hnm⟩ := exists_rep_add_smul_zm_of_intM_smul hR x (hφ.1 x hφx)
    exact ⟨(n, m), by simp only [e, hsmul]; exact hnm.symm⟩
  rw [← he.tsum_eq hsupp]
  have hs2 : Summable fun p => φ (e p) * F (e p) := hsum.comp_injective he
  rw [hs2.tsum_prod' (fun n => hs2.comp_injective (by intro m m' h; simpa using h)),
    tsum_fintype]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  simp only [e]
  rw [hφ.2 _ _ ((RHLean.Geometry.NativeTheta.Cusp.FourierJ.intM_iff _).mpr ⟨m, rfl⟩)]


end RHLean.Geometry.NativeTheta.Cusp.FourierJ

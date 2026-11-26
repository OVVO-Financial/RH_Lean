import RHLean.Geometry.NativeThetaCuspSeries

/-!
# The convergent Riemann theta kernel used by the Fourier generator

Only the positive matrix, Gaussian domination, summability, and exact
translation identities needed for Poisson transformation are reconstructed.
The theta kernel is its literal exponential series. Positivity uses the
same Siegel condition as the native rational test-function theta sum.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean
(declaration cut at Gaussian summability and translations). The native
SiegelSum coercivity theorem is reused. The source mirror states no
license; attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Complex Matrix
open scoped Real BigOperators

namespace RHLean.Geometry.NativeTheta.Cusp.Riemann

variable {ι : Type} [Fintype ι]

abbrev IsSiegel (Ω : Matrix ι ι ℂ) : Prop := Ω ∈ Siegel ι

theorem IsSiegel.mk {Ω : Matrix ι ι ℂ} (isSymm : Ω.IsSymm) (posDef : (Ω.map Complex.im).PosDef) :
    IsSiegel Ω := ⟨isSymm, posDef⟩

theorem IsSiegel.isSymm {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω) : Ω.IsSymm := h.1

theorem IsSiegel.posDef {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω) : (Ω.map Complex.im).PosDef := h.2

omit [Fintype ι] in
theorem isHermitian_map_im_of_isSymm {Ω : Matrix ι ι ℂ} (h : Ω.IsSymm) :
    (Ω.map Complex.im).IsHermitian := by
  ext i j
  simp [conjTranspose_apply, h.apply]

theorem IsSiegel.of_dotProduct_pos {Ω : Matrix ι ι ℂ} (h : Ω.IsSymm)
    (hpos : ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (Ω.map Complex.im *ᵥ x)) : IsSiegel Ω :=
  ⟨h, PosDef.of_dotProduct_mulVec_pos (isHermitian_map_im_of_isSymm h)
    fun x hx => by simpa using hpos x hx⟩

theorem IsSiegel.dotProduct_pos {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω) {x : ι → ℝ}
    (hx : x ≠ 0) : 0 < x ⬝ᵥ (Ω.map Complex.im *ᵥ x) := by
  simpa using h.posDef.dotProduct_mulVec_pos hx

theorem isSiegel_diagonal_iff [DecidableEq ι] {τ : ι → ℂ} :
    IsSiegel (diagonal τ) ↔ ∀ i, 0 < (τ i).im := by
  have : (diagonal τ).map Complex.im = diagonal fun i => (τ i).im := diagonal_map (by simp)
  refine ⟨fun h => ?_, fun h => ⟨isSymm_diagonal _, ?_⟩⟩
  · simpa [this] using h.posDef
  · simpa [this] using h

theorem IsSiegel.smul {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω) {q : ℝ} (hq : 0 < q) :
    IsSiegel ((q : ℂ) • Ω) := by
  refine ⟨h.isSymm.smul _, ?_⟩
  convert h.posDef.smul hq using 1
  ext i j
  simp

theorem IsSiegel.natCast_smul {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω) {q : ℕ} (hq : 0 < q) :
    IsSiegel ((q : ℂ) • Ω) := by
  simpa using h.smul (q := q) (by exact_mod_cast hq)

def riemannThetaTerm (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) (n : ι → ℤ) : ℂ :=
  cexp (2 * π * I * (((fun i => (n i : ℂ) + a i) ⬝ᵥ
    (Ω *ᵥ fun i => (n i : ℂ) + a i)) / 2 +
      (fun i => (n i : ℂ) + a i) ⬝ᵥ fun i => v i + b i))

theorem riemannThetaTerm_def (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) (n : ι → ℤ) :
    riemannThetaTerm a b Ω v n =
      cexp (2 * π * I * (((fun i => (n i : ℂ) + a i) ⬝ᵥ (Ω *ᵥ fun i => (n i : ℂ) + a i)) / 2 +
        (fun i => (n i : ℂ) + a i) ⬝ᵥ fun i => v i + b i)) := rfl

def riemannTheta (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) : ℂ :=
  ∑' n : ι → ℤ, riemannThetaTerm a b Ω v n

theorem riemannTheta_def (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) :
    riemannTheta a b Ω v = ∑' n : ι → ℤ, riemannThetaTerm a b Ω v n := rfl

theorem riemannThetaTerm_zero_zero (Ω : Matrix ι ι ℂ) (v : ι → ℂ) (n : ι → ℤ) :
    riemannThetaTerm 0 0 Ω v n =
      cexp (2 * π * I * (((fun i => (n i : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => (n i : ℂ))) / 2 +
        (fun i => (n i : ℂ)) ⬝ᵥ v)) := by
  simp [riemannThetaTerm_def]

theorem norm_riemannThetaTerm (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) (n : ι → ℤ) :
    ‖riemannThetaTerm a b Ω v n‖ =
      Real.exp (-π * ((fun i => (n i : ℝ) + a i) ⬝ᵥ (Ω.map Complex.im *ᵥ fun i => (n i : ℝ) + a i))
        - 2 * π * ((fun i => (n i : ℝ) + a i) ⬝ᵥ fun i => (v i).im)) := by
  rw [riemannThetaTerm_def, Complex.norm_exp]
  congr 1
  simp [dotProduct, mulVec, Finset.mul_sum _ _ ((n _ : ℂ) + a _),
    Finset.mul_sum _ _ ((n _ : ℝ) + a _)]
  ring

def riemannThetaBound (a : ι → ℝ) (c S : ℝ) (n : ι → ℤ) : ℝ :=
  Real.exp (-π * (c * ((fun i => (n i : ℝ) + a i) ⬝ᵥ fun i => (n i : ℝ) + a i) -
    2 * S * ∑ i, |(n i : ℝ) + a i|))

theorem riemannThetaBound_pos (a : ι → ℝ) (c S : ℝ) (n : ι → ℤ) :
    0 < riemannThetaBound a c S n := Real.exp_pos _

theorem norm_riemannThetaTerm_le (a b : ι → ℝ) {Ω : Matrix ι ι ℂ} {v : ι → ℂ} {c S : ℝ}
    (hΩ : ∀ x : ι → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Ω.map Complex.im *ᵥ x)) (hv : ∀ i, |(v i).im| ≤ S)
    (n : ι → ℤ) : ‖riemannThetaTerm a b Ω v n‖ ≤ riemannThetaBound a c S n := by
  rw [norm_riemannThetaTerm, riemannThetaBound, Real.exp_le_exp]
  have h1 := hΩ fun i => (n i : ℝ) + a i
  have h2 : -((fun i => (n i : ℝ) + a i) ⬝ᵥ fun i => (v i).im) ≤ S * ∑ i, |(n i : ℝ) + a i| := by
    rw [dotProduct, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => (neg_le_abs _).trans ?_
    rw [abs_mul, mul_comm]
    gcongr
    exact hv i
  nlinarith [mul_le_mul_of_nonneg_left h1 Real.pi_pos.le,
    mul_le_mul_of_nonneg_left h2 Real.pi_pos.le]

theorem summable_pi_prod_of_nonneg {α : ι → Type*} {f : ∀ i, α i → ℝ} (h0 : ∀ i x, 0 ≤ f i x)
    (hf : ∀ i, Summable (f i)) : Summable fun n : ∀ i, α i => ∏ i, f i (n i) := by
  classical
  refine summable_of_sum_le (c := ∏ i, ∑' x, f i x)
    (fun n => Finset.prod_nonneg fun i _ => h0 i _) fun s => ?_
  calc ∑ n ∈ s, ∏ i, f i (n i)
      ≤ ∑ n ∈ Fintype.piFinset fun i => s.image (· i), ∏ i, f i (n i) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun n hn => Fintype.mem_piFinset.mpr fun i => Finset.mem_image_of_mem _ hn)
          fun n _ _ => Finset.prod_nonneg fun i _ => h0 i _
    _ = ∏ i, ∑ x ∈ s.image (· i), f i x := (Finset.prod_univ_sum _ _).symm
    _ ≤ _ := Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun x _ => h0 i x)
        fun i _ => (hf i).sum_le_tsum _ fun x _ => h0 i x

theorem summable_exp_neg_shifted_sq (a S : ℝ) {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => Real.exp (-π * (c * ((n + a) * (n + a)) - 2 * S * |n + a|)) := by
  have := (summable_pow_mul_jacobiTheta₂_term_bound (|S| + c * |a|) hc 0).mul_left
    (Real.exp (2 * π * |S| * |a|))
  refine this.of_nonneg_of_le (fun n => (Real.exp_pos _).le) fun n => ?_
  rw [pow_zero, one_mul, ← Real.exp_add, Real.exp_le_exp, Int.cast_abs]
  have h1 : S * |n + a| ≤ |S| * (|(n : ℝ)| + |a|) :=
    mul_le_mul (le_abs_self S) (abs_add_le _ _) (abs_nonneg _) (abs_nonneg _)
  have h2 : -((n : ℝ) * a) ≤ |(n : ℝ)| * |a| := by
    rw [← abs_mul]
    exact neg_le_abs _
  have h3 : c * (n ^ 2 - 2 * (|(n : ℝ)| * |a|)) ≤ c * ((n + a) * (n + a)) := by
    gcongr
    nlinarith [sq_nonneg a]
  nlinarith [mul_le_mul_of_nonneg_left h1 Real.pi_pos.le,
    mul_le_mul_of_nonneg_left h3 Real.pi_pos.le]

theorem summable_riemannThetaBound (a : ι → ℝ) {c : ℝ} (hc : 0 < c) (S : ℝ) :
    Summable (riemannThetaBound a c S) := by
  refine (summable_pi_prod_of_nonneg (fun i x => (Real.exp_pos _).le)
    fun i => summable_exp_neg_shifted_sq (a i) S hc).congr fun n => ?_
  rw [riemannThetaBound, ← Real.exp_sum]
  simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]

theorem abs_im_apply_le_norm (v : ι → ℂ) (i : ι) : |(v i).im| ≤ ‖v‖ :=
  (Complex.abs_im_le_norm _).trans (norm_le_pi_norm v i)

theorem IsSiegel.summable_norm_riemannThetaTerm {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) (v : ι → ℂ) : Summable fun n => ‖riemannThetaTerm a b Ω v n‖ := by
  obtain ⟨c, hc, hY⟩ := SiegelSum.exists_mul_dotProduct_le h.posDef
  exact (summable_riemannThetaBound a hc ‖v‖).of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_riemannThetaTerm_le a b hY (abs_im_apply_le_norm v))

theorem IsSiegel.summable_riemannThetaTerm {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) (v : ι → ℂ) : Summable (riemannThetaTerm a b Ω v) :=
  (h.summable_norm_riemannThetaTerm a b v).of_norm

theorem dotProduct_mulVec_comm_of_isSymm {Ω : Matrix ι ι ℂ} (h : Ω.IsSymm) (u w : ι → ℂ) :
    u ⬝ᵥ (Ω *ᵥ w) = w ⬝ᵥ (Ω *ᵥ u) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, h.eq, dotProduct_comm]

theorem riemannThetaTerm_add_ofReal (a b x : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) (n : ι → ℤ) :
    riemannThetaTerm a b Ω (v + fun i => (x i : ℂ)) n = riemannThetaTerm a (b + x) Ω v n := by
  simp only [riemannThetaTerm_def, Pi.add_apply, ofReal_add, add_assoc, add_comm (x _ : ℂ)]

theorem riemannTheta_add_ofReal (a b x : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) :
    riemannTheta a b Ω (v + fun i => (x i : ℂ)) = riemannTheta a (b + x) Ω v := by
  simp only [riemannTheta_def, riemannThetaTerm_add_ofReal]

theorem riemannThetaTerm_add (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v w : ι → ℂ) (n : ι → ℤ) :
    riemannThetaTerm a b Ω (v + w) n =
      riemannThetaTerm a b Ω v n * cexp (2 * π * I * ((fun i => (n i : ℂ) + a i) ⬝ᵥ w)) := by
  rw [riemannThetaTerm_def, riemannThetaTerm_def, ← Complex.exp_add]
  congr 1
  have : (fun i => (v + w) i + (b i : ℂ)) = (fun i => v i + b i) + w := by
    funext i
    simp only [Pi.add_apply]
    ring
  rw [this, dotProduct_add]
  ring

theorem riemannThetaTerm_add_mulVec_ofReal {Ω : Matrix ι ι ℂ} (h : Ω.IsSymm) (a b y : ι → ℝ)
    (v : ι → ℂ) (n : ι → ℤ) :
    riemannThetaTerm a b Ω (v + Ω *ᵥ fun i => (y i : ℂ)) n =
      cexp (-(2 * π * I) * (((fun i => (y i : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => (y i : ℂ))) / 2 +
        (fun i => (y i : ℂ)) ⬝ᵥ fun i => v i + b i)) * riemannThetaTerm (a + y) b Ω v n := by
  have : (fun i => (n i : ℂ) + ((a + y) i : ℝ)) =
      (fun i => (n i : ℂ) + a i) + fun i => (y i : ℂ) := by
    funext i
    simp [add_assoc]
  rw [riemannThetaTerm_add, riemannThetaTerm_def, riemannThetaTerm_def, this, ← Complex.exp_add,
    ← Complex.exp_add, mulVec_add, add_dotProduct, add_dotProduct, dotProduct_add, dotProduct_add,
    dotProduct_mulVec_comm_of_isSymm h (fun i => (y i : ℂ)) fun i => (n i : ℂ) + a i]
  congr 1
  ring

theorem riemannTheta_add_mulVec_ofReal {Ω : Matrix ι ι ℂ} (h : Ω.IsSymm) (a b y : ι → ℝ)
    (v : ι → ℂ) :
    riemannTheta a b Ω (v + Ω *ᵥ fun i => (y i : ℂ)) =
      cexp (-(2 * π * I) * (((fun i => (y i : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => (y i : ℂ))) / 2 +
        (fun i => (y i : ℂ)) ⬝ᵥ fun i => v i + b i)) * riemannTheta (a + y) b Ω v := by
  simp only [riemannTheta_def, riemannThetaTerm_add_mulVec_ofReal h, tsum_mul_left]

end RHLean.Geometry.NativeTheta.Cusp.Riemann

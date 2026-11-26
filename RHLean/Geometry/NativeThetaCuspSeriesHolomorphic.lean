import RHLean.Geometry.NativeThetaCuspSeriesInjective
import RHLean.Geometry.NativeThetaCuspFiniteOverlap

/-!
# Holomorphic, nonzero theta series from the constructed vacua

The rational theta sum is locally normally convergent in its actual complex
variable. A finite set of imaginary corners supplies the summable bound;
the existing native theorem for locally normal sums then proves holomorphy.
Fourier injectivity makes every normalized finite-adelic vacuum a nonzero
holomorphic theta function. These are analytic functions attached to the
actual Haar-normalized test functions. Global automorphic descent and
cuspidality are separate suppliers.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThetaSeriesTestFunctionHolomorphicWeight.lean
(`exists_corner`, `differentiable_thS`), with the established native normal
convergence theorem replacing the source's derivative-bound detour. The
source mirror states no license; attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Matrix Complex
open scoped Real BigOperators Topology Classical

namespace RHLean.Geometry.NativeTheta.Cusp.ThetaHol

variable {κ ι : Type} [Fintype κ] [Fintype ι]

/-- A finite set of imaginary corners dominates the theta exponential on
an actual norm ball. -/
theorem exists_corner (τ : Matrix ι ι ℂ) (S : ℝ) (x : Matrix κ ι ℚ) :
    ∃ s : κ → ι → Bool, ∀ ζ : κ → ι → ℂ, ‖ζ‖ ≤ S →
      ‖cexp (π * I * ∑ k, (qv (x k) ⬝ᵥ τ *ᵥ qv (x k) +
        2 * (qv (x k) ⬝ᵥ ζ k)))‖ ≤
      ‖cexp (π * I * ∑ k, (qv (x k) ⬝ᵥ τ *ᵥ qv (x k) +
        2 * (qv (x k) ⬝ᵥ fun i => (if s k i then -S else S : ℝ) * I)))‖ := by
  refine ⟨fun k i => decide (0 ≤ x k i), fun ζ hζ => ?_⟩
  rw [Complex.norm_exp, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [mul_assoc, Complex.re_ofReal_mul, Complex.I_mul_re, Complex.im_sum,
    Complex.add_im, Complex.mul_im, dotProduct, qv, Complex.ratCast_re,
    Complex.ratCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, zero_mul, mul_zero, add_zero, mul_one, Complex.re_ofNat,
    Complex.im_ofNat, decide_eq_true_eq]
  refine mul_le_mul_of_nonneg_left (neg_le_neg (Finset.sum_le_sum fun k _ => ?_))
    Real.pi_pos.le
  refine add_le_add le_rfl ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) zero_le_two
  have h1 : |(ζ k i).im| ≤ S := (Complex.abs_im_le_norm _).trans
    ((norm_le_pi_norm (ζ k) i).trans ((norm_le_pi_norm ζ k).trans hζ))
  have h2 := abs_le.mp h1
  split_ifs with h
  · have : (0 : ℝ) ≤ (x k i : ℝ) := by exact_mod_cast h
    nlinarith
  · have : (x k i : ℝ) < 0 := by exact_mod_cast lt_of_not_ge h
    nlinarith

variable [DecidableEq ι]

/-- Holomorphy of the absolutely convergent rational theta sum follows
from its proved summable local bound. -/
theorem differentiable_thS {φ : Matrix κ ι ℚ → ℂ} (hφ : IsSB φ)
    {τ : Matrix ι ι ℂ} (hτ : τ ∈ Siegel ι) : Differentiable ℂ (thS φ τ) := by
  let F : Matrix κ ι ℚ → (κ → ι → ℂ) → ℂ := fun x ζ => φ x *
    cexp (π * I * ∑ k, (qv (x k) ⬝ᵥ τ *ᵥ qv (x k) +
      2 * (qv (x k) ⬝ᵥ ζ k)))
  have hFd : ∀ x, Differentiable ℂ (F x) := by
    intro x
    simp only [F, dotProduct]
    fun_prop
  change Differentiable ℂ (fun ζ => ∑' x, F x ζ)
  rw [← differentiableOn_univ]
  apply GaussianSeries.differentiableOn_tsum_of_locally_normal isOpen_univ
    (fun x => (hFd x).differentiableOn)
  intro ζ₀ _
  let S : ℝ := ‖ζ₀‖ + 2
  let cor : (κ → ι → Bool) → κ → ι → ℂ :=
    fun s k i => ((if s k i then -S else S : ℝ) : ℂ) * I
  choose s hs using fun x : Matrix κ ι ℚ => exists_corner τ S x
  have hsum : Summable fun x => ‖F x (cor (s x))‖ := by
    have hfin : Summable fun x => ∑ t : κ → ι → Bool, ‖F x (cor t)‖ :=
      summable_sum fun t _ => SiegelSum.summable_norm_thetaTerm κ ι φ hφ τ hτ (cor t)
    refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) hfin
    exact Finset.single_le_sum (f := fun t => ‖F x (cor t)‖)
      (fun t _ => norm_nonneg _) (Finset.mem_univ (s x))
  refine ⟨Metric.ball ζ₀ 1, Metric.ball_mem_nhds ζ₀ one_pos,
    (fun x => ‖F x (cor (s x))‖), hsum, fun x ζ hζ => ?_⟩
  have hζS : ‖ζ‖ ≤ S := by
    rw [Metric.mem_ball, dist_eq_norm] at hζ
    have := norm_sub_norm_le ζ ζ₀
    dsimp only [S]
    linarith
  simp only [F, norm_mul]
  exact mul_le_mul_of_nonneg_left (hs x ζ hζS) (norm_nonneg _)

/-- Vanishing of the entire theta function is exactly vanishing of its
original Schwartz–Bruhat coefficients. -/
theorem thS_eq_zero_iff {φ : Matrix κ ι ℚ → ℂ} (hφ : IsSB φ)
    {τ : Matrix ι ι ℂ} (hτ : τ ∈ Siegel ι) : thS φ τ = 0 ↔ φ = 0 := by
  constructor
  · intro h
    apply eq_of_thS_eq κ ι φ 0 hφ isSB_zero τ hτ
    intro ζ
    rw [show thS φ τ ζ = 0 from congrFun h ζ]
    simp [thS]
  · rintro rfl
    funext ζ
    simp [thS]

/-- Every nonzero test function yields a nonzero actual theta function. -/
theorem exists_thS_ne_zero {φ : Matrix κ ι ℚ → ℂ} (hφ : IsSB φ) (hφ0 : φ ≠ 0)
    {τ : Matrix ι ι ℂ} (hτ : τ ∈ Siegel ι) : ∃ ζ, thS φ τ ζ ≠ 0 :=
  Function.ne_iff.mp ((thS_eq_zero_iff hφ hτ).not.mpr hφ0)

/-- The actual unit Haar norm of a constructed vacuum gives a holomorphic
nonzero theta function at every Siegel matrix. -/
theorem holomorphic_nonzero_of_vacuum
    {ε : FiniteOverlap.Position (κ := κ) (ι := ι) → ℂ}
    {A : AddSubgroup (FiniteOverlap.Position (κ := κ) (ι := ι))}
    {v : Matrix κ ι ℚ → ℂ} (hv : FiniteOverlap.IsVac ε A v)
    {τ : Matrix ι ι ℂ} (hτ : τ ∈ Siegel ι) :
    Differentiable ℂ (thS v τ) ∧ ∃ ζ, thS v τ ζ ≠ 0 := by
  refine ⟨differentiable_thS hv.1 hτ, exists_thS_ne_zero hv.1 ?_ hτ⟩
  intro h0
  have hip : ip v v = 0 := by
    rw [h0]
    simpa using (FiniteOverlap.ip_smul_left (κ := κ) (ι := ι)
      (φ := 0) (ψ := 0) (0 : ℂ) isSB_zero isSB_zero)
  exact one_ne_zero (hv.2.1.symm.trans hip)

end RHLean.Geometry.NativeTheta.Cusp.ThetaHol

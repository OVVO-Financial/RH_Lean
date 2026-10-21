import Mathlib

/-!
# Path 2: actual parent-child reindexing and a fixed logarithmic dipole

Source identities only, NOT a seven-eighths estimate. No OpenAI final
nonvanishing theorem, Mertens converse, or moment bound is an input.

The marked theorem changes the summation index b -> p*b and the scale
Y -> Y/N(p), using the genuine UFD Moebius function on distinct labels.
For W(u)=F(u)-F(c*u), the positive-channel candidate densities are exact
dilations of the SAME function u*F'(u), not nonsmooth positive parts.
-/

noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory
namespace RHLean.Analysis.VF919Path2

def logDipole (W : ℝ → ℝ) (u : ℝ) : ℝ := -u * deriv W u
def logDensity (F : ℝ → ℝ) (u : ℝ) : ℝ := u * deriv F u

theorem logDipole_antiderivative_window
    (F : ℝ → ℝ) (hF : Differentiable ℝ F) (c u : ℝ) :
    logDipole (fun v => F v - F (c * v)) u =
      logDensity F (c * u) - logDensity F u := by
  have hd := (hF u).hasDerivAt.sub
    ((hF (c * u)).hasDerivAt.comp u ((hasDerivAt_id u).const_mul c))
  have hfun : (F - F ∘ HMul.hMul c) = (fun v => F v - F (c * v)) := by
    funext v
    rfl
  have hd0 := hd.deriv
  rw [hfun] at hd0
  unfold logDipole logDensity
  rw [hd0]
  ring

theorem density_channels_bounds (eta : ℝ → ℝ) (C c : ℝ)
    (hC : 0 < C) (hEta : ∀ v, 0 ≤ eta v ∧ eta v ≤ C) (u : ℝ) :
    (0 ≤ eta (c * u) / C ∧ eta (c * u) / C ≤ 1) ∧
    (0 ≤ eta u / C ∧ eta u / C ≤ 1) := by
  constructor <;> constructor
  · exact div_nonneg (hEta _).1 hC.le
  · exact (div_le_one hC).mpr (hEta _).2
  · exact div_nonneg (hEta _).1 hC.le
  · exact (div_le_one hC).mpr (hEta _).2

theorem density_channels_reconstruct (eta : ℝ → ℝ) (C c u : ℝ)
    (hC : C ≠ 0) :
    C * (eta (c * u) / C - eta u / C) = eta (c * u) - eta u := by
  field_simp

theorem density_channels_smooth (eta : ℝ → ℝ)
    (hEta : ContDiff ℝ ∞ eta) (C c : ℝ) :
    ContDiff ℝ ∞ (fun u => eta (c * u) / C) ∧
    ContDiff ℝ ∞ (fun u => eta u / C) := by
  exact ⟨(hEta.comp (contDiff_const.mul contDiff_id)).div_const C,
    hEta.div_const C⟩

theorem density_channels_support (eta : ℝ → ℝ)
    (hEta : Function.support eta ⊆ Set.Ioo ((5 : ℝ) / 4) ((8 : ℝ) / 5))
    (C : ℝ) :
    Function.support (fun u => eta (((4 : ℝ) / 5) * u) / C) ⊆ Set.Ioo (1 : ℝ) 2 ∧
    Function.support (fun u => eta u / C) ⊆ Set.Ioo (1 : ℝ) 2 := by
  constructor
  · intro u hu
    have he : eta (((4 : ℝ) / 5) * u) ≠ 0 := by
      intro hz
      exact hu (by simp [hz])
    have hh := hEta he
    constructor <;> linarith [hh.1, hh.2]
  · intro u hu
    have he : eta u ≠ 0 := by
      intro hz
      exact hu (by simp [hz])
    have hh := hEta he
    constructor <;> linarith [hh.1, hh.2]

/-- Exact FTC; all q,t dependence is in the scale, never in derivatives
of a family of sharper and sharper profiles. Includes the q=1 dipole. -/
theorem fixed_profile_dipole (W : ℝ → ℝ) (hW : Differentiable ℝ W)
    (hWd : Continuous (deriv W)) (q z : ℝ) (hq : 0 < q) :
    W (q * z) - W ((q + 1) * z) =
      ∫ t : ℝ in 0..1, (q + t)⁻¹ * logDipole W ((q + t) * z) := by
  have hftc := intervalIntegral.integral_unitInterval_deriv_eq_sub
    (f := W) (f' := deriv W) (z₀ := q * z) (z₁ := z)
    (hWd.comp (by fun_prop)).continuousOn
    (fun t _ => (hW _).hasDerivAt)
  simp only [smul_eq_mul] at hftc
  have hpoint (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
      (q + t)⁻¹ * logDipole W ((q + t) * z) =
        -z * deriv W (q * z + t * z) := by
    have ht0 : 0 ≤ t := (Set.uIcc_of_le (α := ℝ) zero_le_one ▸ ht).1
    have hqt : q + t ≠ 0 := ne_of_gt (by linarith)
    have he : (q + t) * z = q * z + t * z := by ring
    unfold logDipole
    rw [he]
    field_simp [hqt]
  have heq : (∫ t : ℝ in 0..1, (q + t)⁻¹ * logDipole W ((q + t) * z)) =
      -z * (∫ t : ℝ in 0..1, deriv W (q * z + t * z)) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr hpoint
  rw [heq]
  have he : q * z + z = (q + 1) * z := by ring
  rw [he] at hftc
  linarith

theorem fixed_profile_cofactor_dipole
    (W : ℝ → ℝ) (hW : Differentiable ℝ W) (hWd : Continuous (deriv W))
    (P m : ℝ) (q : ℝ) (hq : 0 < q) :
    W (q * (m / P)) - W ((q + 1) * (m / P)) =
      ∫ t : ℝ in 0..1, (q + t)⁻¹ *
        logDipole W (m / (P / (q + t))) := by
  rw [fixed_profile_dipole W hW hWd q (m / P) hq]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  have he : (q + t) * (m / P) = m / (P / (q + t)) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  rw [he]

/-- Every cofactor pair and EVERY original label remains present. This
is finite, so no unproved exchange of infinite sums is being invoked. -/
theorem finite_labelled_cofactor_transport {A : Type*}
    (s : Finset A) (coeff : A → ℝ) (N : A → ℝ) (K : ℕ)
    (W : ℝ → ℝ) (hW : Differentiable ℝ W) (hWd : Continuous (deriv W)) (P : ℝ) :
    (∑ a ∈ s, coeff a * ∑ k ∈ Finset.range K,
      (W ((3 * (k : ℝ) + 1) * (N a / P)) -
        W ((3 * (k : ℝ) + 2) * (N a / P)))) =
    ∑ a ∈ s, coeff a * ∑ k ∈ Finset.range K,
      ∫ t : ℝ in 0..1, (3 * (k : ℝ) + 1 + t)⁻¹ *
        logDipole W (N a / (P / (3 * (k : ℝ) + 1 + t))) := by
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have hq : 0 < 3 * (k : ℝ) + 1 := by positivity
  have h := fixed_profile_cofactor_dipole W hW hWd P (N a)
    (3 * (k : ℝ) + 1) hq
  have he : (3 * (k : ℝ) + 1) + 1 = 3 * (k : ℝ) + 2 := by ring
  simpa only [he] using h

section ActualMoebius
variable {A : Type*} [CommMonoidWithZero A] [UniqueFactorizationMonoid A]

def normSource (N : A →* ℕ) (s : Finset A) (W : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ a ∈ s, (UniqueFactorizationMonoid.moebius a : ℂ) * W ((N a : ℝ) / Y)

/-- Complete finite parent-to-child reindexing. Equal norms NEVER merge
labels. This uses actual UFD Moebius signs, not a postulated sign rule. -/
theorem marked_norm_source (N : A →* ℕ) (s : Finset A) (p : A)
    (hp : Prime p) (hinj : Function.Injective (fun b : A => p * b))
    (hcop : ∀ b ∈ s, IsRelPrime p b) (W : ℝ → ℂ) (Y : ℝ) :
    normSource N (s.image (fun b => p * b)) W Y =
      -normSource N s W (Y / (N p : ℝ)) := by
  unfold normSource
  rw [Finset.sum_image (fun a _ b _ h => hinj h), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [(hcop b hb).moebius_mul, hp.irreducible.moebius_eq, Int.cast_mul]
  simp only [Int.cast_neg, Int.cast_one, neg_one_mul, map_mul, Nat.cast_mul]
  have he : (N p : ℝ) * (N b : ℝ) / Y = (N b : ℝ) / (Y / (N p : ℝ)) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  rw [he]
  ring

/-- A dilation of a fixed density is the SAME source at a new scale,
not the difference of two independently normalized nonlinear probes. -/
theorem density_dilation_same_source (N : A →* ℕ) (s : Finset A)
    (eta : ℝ → ℂ) (c Y : ℝ) :
    normSource N s (fun u => eta (c * u)) Y = normSource N s eta (Y / c) := by
  unfold normSource
  apply Finset.sum_congr rfl
  intro a _
  dsimp only
  have he : c * ((N a : ℝ) / Y) = (N a : ℝ) / (Y / c) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  rw [he]

end ActualMoebius

#print axioms logDipole_antiderivative_window
#print axioms density_channels_bounds
#print axioms density_channels_reconstruct
#print axioms density_channels_smooth
#print axioms density_channels_support
#print axioms fixed_profile_dipole
#print axioms fixed_profile_cofactor_dipole
#print axioms finite_labelled_cofactor_transport
#print axioms marked_norm_source
#print axioms density_dilation_same_source
end RHLean.Analysis.VF919Path2

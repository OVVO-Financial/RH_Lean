import Mathlib

/-!
# Path 2: actual parent-child reindexing and a fixed logarithmic dipole

These are source identities, NOT a seven-eighths estimate. There is no
import of an OpenAI nonvanishing theorem, no Mertens converse, and no
assumed moment or power-bound hypothesis.

Unlike multiplying an unchanged sharp site by a local Euler identity,
`marked_norm_source` changes the summation index from parents b to children
p*b and changes the scale to Y/N(p). It uses the genuine UFD Moebius
function, so it specializes to actual Eisenstein ideals, without assigning
new signs or identifying different ideals having the same norm.

The logarithmic antiderivative construction needs no arbitrary positive
majorant: for W(u)=F(u)-F(c*u), its dipole is exactly
  -(u * W'(u)) = (c*u)*F'(c*u) - u*F'(u).
Both components are dilations of the SAME density. The cofactor FTC
identity below similarly puts all k,t dependence into the scale.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace RHLean.Analysis.VF919Path2

/-- One fixed signed profile; the arithmetic scale is a separate argument. -/
def logDipole (W : ℝ → ℝ) (u : ℝ) : ℝ := -u * deriv W u

def logDensity (F : ℝ → ℝ) (u : ℝ) : ℝ := u * deriv F u

/-- For the #990 logarithmic window the two channels are dilations of one
nonnegative density, not nonsmooth positive and negative parts. -/
theorem logDipole_antiderivative_window
    (F : ℝ → ℝ) (hF : Differentiable ℝ F) (c u : ℝ) :
    logDipole (fun v => F v - F (c * v)) u =
      logDensity F (c * u) - logDensity F u := by
  have hd := (hF u).hasDerivAt.sub
    ((hF (c * u)).hasDerivAt.comp u ((hasDerivAt_id u).const_mul c))
  unfold logDipole logDensity
  rw [hd.deriv]
  ring

/-- The two density channels are individually in [0,1] with one fixed
normalizing constant. No cancellation estimate is a premise. -/
theorem density_channels_bounds (eta : ℝ → ℝ) (C c : ℝ)
    (hC : 0 < C) (hEta : ∀ v, 0 ≤ eta v ∧ eta v ≤ C) (u : ℝ) :
    (0 ≤ eta (c * u) / C ∧ eta (c * u) / C ≤ 1) ∧
    (0 ≤ eta u / C ∧ eta u / C ≤ 1) := by
  constructor <;> constructor
  · exact div_nonneg (hEta _).1 hC.le
  · exact (div_le_one hC).mpr (hEta _).2
  · exact div_nonneg (hEta _).1 hC.le
  · exact (div_le_one hC).mpr (hEta _).2

/-- Recover the signed density without changing its absolute scale. -/
theorem density_channels_reconstruct (eta : ℝ → ℝ) (C c u : ℝ)
    (hC : C ≠ 0) :
    C * (eta (c * u) / C - eta u / C) = eta (c * u) - eta u := by
  field_simp

/-- The positive profiles are smooth without taking max(.,0). -/
theorem density_channels_smooth (eta : ℝ → ℝ)
    (hEta : ContDiff ℝ ∞ eta) (C c : ℝ) :
    ContDiff ℝ ∞ (fun u => eta (c * u) / C) ∧
    ContDiff ℝ ∞ (fun u => eta u / C) := by
  exact ⟨(hEta.comp (contDiff_const.mul contDiff_id)).div_const C,
    hEta.div_const C⟩

/-- The #990 density support (5/4,8/5) makes BOTH profiles admissible in
(1,2), using c=4/5. All constants and support margins are fixed. -/
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

/-- Actual FTC dipole, including k=0. The SAME profile logDipole W
is used for all q>0; the variable t enters the scale, not its derivatives. -/
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
    have ht0 : 0 ≤ t := (Set.uIcc_of_le zero_le_one ▸ ht).1
    have hqt : q + t ≠ 0 := ne_of_gt (by linarith)
    have he : (q + t) * z = q * z + t * z := by ring
    unfold logDipole
    rw [he]
    field_simp
    <;> ring
  have heq : (∫ t : ℝ in 0..1, (q + t)⁻¹ * logDipole W ((q + t) * z)) =
      -z * (∫ t : ℝ in 0..1, deriv W (q * z + t * z)) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr hpoint
  rw [heq]
  have he : q * z + z = (q + 1) * z := by ring
  rw [he] at hftc
  linarith

/-- The cofactor substitution at physical norm m and external scale P.
No small-scale or k=0 term is discarded. -/
theorem fixed_profile_cofactor_dipole
    (W : ℝ → ℝ) (hW : Differentiable ℝ W) (hWd : Continuous (deriv W))
    (P m : ℝ) (q : ℝ) (hq : 0 < q) :
    W (q * (m / P)) - W ((q + 1) * (m / P)) =
      ∫ t : ℝ in 0..1, (q + t)⁻¹ *
        logDipole W (m / (P / (q + t))) := by
  rw [fixed_profile_dipole W hW hWd q (m / P) hq]
  apply intervalIntegral.integral_congr
  intro t _
  congr 2
  simp only [div_div, div_eq_mul_inv]
  ring

section ActualMoebius
variable {A : Type*} [CommMonoidWithZero A] [UniqueFactorizationMonoid A]

/-- Genuine Moebius coefficients on labelled objects, never norm-collapsed. -/
def normSource (N : A →* ℕ) (s : Finset A) (W : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ a ∈ s, (UniqueFactorizationMonoid.moebius a : ℂ) * W ((N a : ℝ) / Y)

/-- Reindex a complete finite set of parent labels to p*b. The injection
is explicit so no two labelled children are merged by a norm projection. -/
theorem marked_norm_source (N : A →* ℕ) (s : Finset A) (p : A)
    (hp : Prime p) (hinj : Function.Injective (fun b : A => p * b))
    (hcop : ∀ b ∈ s, IsRelPrime p b) (hNp : (N p : ℝ) ≠ 0)
    (W : ℝ → ℂ) (Y : ℝ) :
    normSource N (s.image (fun b => p * b)) W Y =
      -normSource N s W (Y / (N p : ℝ)) := by
  classical
  unfold normSource
  rw [Finset.sum_image (fun a _ b _ h => hinj h), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [(hcop b hb).moebius_mul, hp.irreducible.moebius_eq, Int.cast_mul]
  simp only [Int.cast_neg, Int.cast_one, neg_one_mul, map_mul, Nat.cast_mul]
  have he : (N p : ℝ) * (N b : ℝ) / Y = (N b : ℝ) / (Y / (N p : ℝ)) := by
    rw [div_div, div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [he]
  ring

end ActualMoebius

#print axioms logDipole_antiderivative_window
#print axioms density_channels_bounds
#print axioms density_channels_reconstruct
#print axioms density_channels_smooth
#print axioms density_channels_support
#print axioms fixed_profile_dipole
#print axioms fixed_profile_cofactor_dipole
#print axioms marked_norm_source

end RHLean.Analysis.VF919Path2

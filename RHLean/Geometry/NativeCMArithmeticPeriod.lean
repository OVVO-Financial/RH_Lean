import RHLean.Geometry.NativeCMChowlaSelberg
import RHLean.Geometry.NativeCMOrderIdentification
import RHLean.Geometry.NativeCMWeierstrassSeedComparison

/-!+# The exact class-group period on the actual native quadratic field

The literal field Q(G.rt), its ring of integers, its quadratic character and
its ideal-class period lattices are constructed together. The principal
class is represented by the very same elliptic seed period lattice used in
the Weierstrass equation comparison. The class-group mean is proved from
the native Kronecker limit calculation and Dedekind-zeta factorization.

This does not identify an average over conjugates of an integral tangent
generator with the class-group average: that arithmetic CM comparison is
a separate required theorem. No metric, degree or height is assigned the
desired logarithmic L-derivative value.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/
DedekindZetaEqSumRealEisenstein.lean, `chowla_selberg_lattice`.
The supplying analytic proofs are reconstructed in the five native period
arithmetic modules. Source attribution is retained; no license is assigned.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField Module
open scoped nonZeroDivisors

namespace RHLean.Geometry.NativeCM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : NativeGeometricHost E) (τ : E →+* ℂ)

theorem quadraticField_discr : discr (quadraticField G) = -(G.d : ℤ) :=
  PeriodArithmetic.discr_eq_neg_of_sq_eq (quadraticField_finrank G)
    G.d_prime.squarefree (by have := G.d_mod; omega) (quadraticFieldRoot_sq G)

/-- The genuine quadratic Dirichlet character of the same prime discriminant. -/
def periodCharacter : DirichletCharacter ℂ G.d :=
  have : Fact G.d.Prime := ⟨G.d_prime⟩
  (quadraticChar (ZMod G.d)).ringHomComp (Int.castRingHom ℂ)

theorem periodCharacter_isKronecker : PeriodArithmetic.IsKroneckerChar (periodCharacter G) := by
  have : Fact G.d.Prime := ⟨G.d_prime⟩
  exact PeriodArithmetic.isKroneckerChar_quadraticChar (by have := G.d_mod; omega)

/-- Restriction of the original complex embedding, with no new field choice. -/
def quadraticEmbedding : quadraticField G →+* ℂ :=
  τ.comp (algebraMap (quadraticField G) E)

/-- The original seed is the period lattice of the principal ideal class
of the very same quadratic subfield. -/
theorem seedPeriod_eq_image_one :
    ((EllipticSeed.periodPair G τ).lattice : Set ℂ) =
      quadraticEmbedding G τ ''
        (1 : FractionalIdeal (𝓞 (quadraticField G))⁰ (quadraticField G)) := by
  rw [EllipticSeed.periodPair_lattice]
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨(orderIntegerRingEquiv G a : quadraticField G), ?_, ?_⟩
    · exact FractionalIdeal.mem_one_iff.mpr ⟨orderIntegerRingEquiv G a, rfl⟩
    · change τ (((algebraMap (𝓞 (quadraticField G)) (𝓞 E)
        (orderIntegerRingEquiv G a)) : 𝓞 E) : E) = τ ((a : 𝓞 E) : E)
      rw [orderIntegerRingEquiv_inclusion]
  · rintro ⟨a, ha, hz⟩
    obtain ⟨b, rfl⟩ := FractionalIdeal.mem_one_iff.mp ha
    exact ⟨quadraticIntegersToOrder G b, hz⟩

/-- The nontrivial Weierstrass scale is retained in the original polarized
metric. Its logarithm is exactly the analytic lattice-period expression. -/
theorem exact_metric_scale_log
    (C : WeierstrassCurve.VariableChange ℂ)
    (hscale : (C.u : ℂ) ^ 12 *
      (Weierstrass.latticeCurve (EllipticSeed.periodPair G τ)).Δ = 1) :
    -Real.log (Real.pi * (EllipticSeed.hermitian G τ (C.u : ℂ) (C.u : ℂ)).re) =
      PeriodArithmetic.latticeLogPeriod (EllipticSeed.periodPair G τ) := by
  have ha : |(EllipticSeed.omega G τ).im| ≠ 0 :=
    abs_ne_zero.mpr (EllipticSeed.omega_im_ne_zero G τ)
  have hu : ‖(C.u : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr C.u.ne_zero
  have hΔ : ‖(Weierstrass.latticeCurve (EllipticSeed.periodPair G τ)).Δ‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Weierstrass.latticeCurve_Δ_ne_zero _)
  have hcovol : ZLattice.covolume (EllipticSeed.periodPair G τ).lattice =
      |(EllipticSeed.omega G τ).im| := by
    have h := PeriodArithmetic.covolume_lattice_eq
      (L := EllipticSeed.periodPair G τ) one_ne_zero
      (Weierstrass.mem_lattice_periodPairOfTau (EllipticSeed.upperPeriod G τ))
    simpa only [norm_one, one_pow, one_mul, EllipticSeed.upperPeriod_im] using h
  have hlog := congrArg (fun z : ℂ => Real.log ‖z‖) hscale
  simp only [norm_mul, norm_pow, norm_one, Real.log_one,
    Real.log_mul (pow_ne_zero 12 hu) hΔ, Real.log_pow] at hlog
  rw [EllipticSeed.hermitian_self, PeriodArithmetic.latticeLogPeriod, hcovol,
    ← Weierstrass.latticeCurve_Δ,
    Real.log_mul Real.pi_ne_zero (mul_ne_zero (inv_ne_zero ha) (pow_ne_zero 2 hu)),
    Real.log_mul (inv_ne_zero ha) (pow_ne_zero 2 hu), Real.log_inv, Real.log_pow,
    Real.log_div ha Real.pi_ne_zero]
  norm_num at hlog ⊢
  linarith

/-- The analytic class-group mean, including the actual seed in its
principal class, is the exact signed logarithmic L-derivative expression. -/
theorem exists_idealClassPeriods_with_seed :
    ∃ (A : ClassGroup (𝓞 (quadraticField G)) →
        (FractionalIdeal (𝓞 (quadraticField G))⁰ (quadraticField G))ˣ)
      (L : ClassGroup (𝓞 (quadraticField G)) → PeriodPair),
      (∀ c, ClassGroup.mk (quadraticField G) (A c) = c) ∧
      (∀ c, ((L c).lattice : Set ℂ) = quadraticEmbedding G τ '' (A c).1) ∧
      L 1 = EllipticSeed.periodPair G τ ∧
      (periodCharacter G).LFunction 1 =
        (Real.pi * classNumber (quadraticField G) / Real.sqrt G.d : ℝ) ∧
      (((∑ c, PeriodArithmetic.latticeLogPeriod (L c)) /
          classNumber (quadraticField G) : ℝ) : ℂ) =
        (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / Real.sqrt G.d) : ℝ) -
          deriv (periodCharacter G).LFunction 1 / (periodCharacter G).LFunction 1 := by
  classical
  have : NeZero G.d := ⟨G.d_prime.ne_zero⟩
  have hd : 4 < G.d := by have := G.d_mod; omega
  have hrep : ∀ c : ClassGroup (𝓞 (quadraticField G)),
      ∃ (A : (FractionalIdeal (𝓞 (quadraticField G))⁰ (quadraticField G))ˣ)
        (L : PeriodPair), ClassGroup.mk (quadraticField G) A = c ∧
          (L.lattice : Set ℂ) = quadraticEmbedding G τ '' A.1 ∧
          (c = 1 → L = EllipticSeed.periodPair G τ) := by
    intro c
    by_cases hc : c = 1
    · subst c
      exact ⟨1, EllipticSeed.periodPair G τ, by simp,
        seedPeriod_eq_image_one G τ, fun _ => rfl⟩
    · obtain ⟨A, L, hA, hL⟩ := PeriodArithmetic.exists_classRep_periodPair
        (quadraticField_finrank G) (quadraticField_discr G) (quadraticEmbedding G τ) c
      exact ⟨A, L, hA, hL, fun h => (hc h).elim⟩
  choose A L hA hL hOne using hrep
  refine ⟨A, L, hA, hL, hOne 1 rfl, ?_, ?_⟩
  · exact PeriodArithmetic.LFunction_one_eq_classNumber
      (quadraticField_finrank G) (quadraticField_discr G) hd
      (periodCharacter_isKronecker G) (quadraticEmbedding G τ)
  · exact PeriodArithmetic.chowla_selberg_lattice
      (quadraticField_finrank G) (quadraticField_discr G) hd
      (periodCharacter_isKronecker G) (quadraticEmbedding G τ) hA hL

end RHLean.Geometry.NativeCM

end

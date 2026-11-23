import RHLean.Geometry.NativePrescribedGeometricPeriod

/-!
# Construct the canonical theta automorphy factor on the native periods

The phase is the literal source expression
`(-1)^(EF a (w0 • a))` on the original integral lattice. Its semicharacter
law is proved from the actual alternating form, its adjointness, and the
CM half-root identity `w0 + bar w0 = 1`; no phase law is assumed.

Together with the already constructed positive Hermitian period form this
gives an explicit nonvanishing Appell--Humbert factor, its cocycle law, and
the invariant Gaussian Hermitian fiber metric. The final native theorem
uses the same prescribed inverse-half-different lattice and period map.

These are analytic automorphy and metric data. Existence of a nonzero
holomorphic theta section, algebraization to the moduli scheme, integral
extension, cusp spanning and the global Petersson normalization are separate
obligations; none is asserted by the cocycle construction.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`Development/AbelianVarietyTheory/Definitions/TorusSections/IsTorusOf.lean`,
`Proofs/TorusSplitting/TorusAtExistsOfParts.lean`,
`Proofs/CuspFormEvaluations/ExistsTorusWithSignUniformisationFrame.lean`,
and `AppellHumbertFrameSemicharacter.lean`.
The source mirror states no license; attribution is preserved without
assigning one. No upstream compiled object or terminal RH theorem is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField
open scoped BigOperators Pointwise ComplexConjugate

namespace RHLean.Geometry.NativeTheta.AppellHumbert

open NativeGeometricPeriods

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/-- The half-root identity is forced by the actual CM involution. -/
theorem weight_add_bar (H : NativeGeometricHost E) :
    H.w0 + H.bar H.w0 = 1 := by
  have hsq : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by
    rw [← map_pow, H.rt_sq]
    simp
  have hne : H.bar H.rt ≠ H.rt := by
    intro h
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h1 : IsCMField.complexConj E (H.rt : E) = H.rt := by
      rw [← H.bar_eq, h]
    have h2 := IsCMField.complexEmbedding_complexConj E τ (H.rt : E)
    rw [h1] at h2
    have h3 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
      have h4 := congrArg (fun x : 𝓞 E => τ (x : E)) H.rt_sq
      simpa using h4
    have him : (τ (H.rt : E)).im = 0 := Complex.conj_eq_iff_im.1 h2.symm
    have h4 := congrArg Complex.re h3
    simp [sq, him] at h4
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [mul_self_nonneg (τ (H.rt : E)).re]
  have hb : H.bar H.rt = -H.rt := (sq_eq_sq_iff_eq_or_eq_neg.1 hsq).resolve_left hne
  have h2 : 2 * H.bar H.w0 = 1 - H.rt := by
    have h := congrArg H.bar H.two_weight_eq_one_add_root
    rw [map_mul, map_add, map_one, hb, map_ofNat] at h
    rw [h]
    ring
  have h : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by
    rw [mul_add, H.two_weight_eq_one_add_root, h2]
    ring
  exact mul_left_cancel₀ two_ne_zero h

section Phase

variable {H : NativeGeometricHost E} (D : NativeGeometricDatum H)

theorem form_skew (x y : D.La) : D.EF y x = -D.EF x y := by
  have h := D.alt (x + y)
  rw [map_add, LinearMap.add_apply, map_add, map_add, D.alt, D.alt] at h
  omega

/-- The integer quadratic refinement is constructed on the original lattice. -/
def quadraticRefinement (x : D.La) : ℤ := D.EF x (H.w0 • x)

theorem quadraticRefinement_add (x y : D.La) :
    quadraticRefinement D (x + y) =
      quadraticRefinement D x + quadraticRefinement D y + D.EF x y +
        2 * (-D.EF x (H.bar H.w0 • y)) := by
  have h1 : D.EF y (H.w0 • x) = -D.EF x (H.bar H.w0 • y) := by
    rw [form_skew, D.adj]
  have h2 : D.EF x (H.w0 • y) + D.EF x (H.bar H.w0 • y) = D.EF x y := by
    rw [← map_add, ← add_smul, weight_add_bar, one_smul]
  simp only [quadraticRefinement, smul_add, map_add, LinearMap.add_apply]
  omega

/-- Canonical source phase; no semicharacter is chosen or supplied. -/
def phase (x : D.La) : ℂ := ((Int.negOnePow (quadraticRefinement D x) : ℤˣ) : ℤ)

theorem phase_eq_one_or_neg_one (x : D.La) : phase D x = 1 ∨ phase D x = -1 := by
  rcases Int.units_eq_one_or (Int.negOnePow (quadraticRefinement D x)) with h | h
  · exact Or.inl (by simp [phase, h])
  · exact Or.inr (by simp [phase, h])

@[simp] theorem norm_phase (x : D.La) : ‖phase D x‖ = 1 := by
  rcases phase_eq_one_or_neg_one D x with h | h <;> simp [h]

theorem phase_ne_zero (x : D.La) : phase D x ≠ 0 := by
  intro h
  have hnorm := norm_phase D x
  rw [h, norm_zero] at hnorm
  exact zero_ne_one hnorm

@[simp] theorem phase_zero : phase D 0 = 1 := by
  simp [phase, quadraticRefinement]

@[simp] theorem phase_sq (x : D.La) : phase D x ^ 2 = 1 := by
  rcases phase_eq_one_or_neg_one D x with h | h <;> simp [h]

theorem intSign_eq_exp (a : ℤ) :
    (((Int.negOnePow a : ℤˣ) : ℤ) : ℂ) =
      Complex.exp ((a : ℂ) * (Real.pi * Complex.I)) := by
  rw [Complex.exp_int_mul, Complex.exp_pi_mul_I, Int.cast_negOnePow]

theorem phase_add (x y : D.La) :
    phase D (x + y) = phase D x * phase D y *
      Complex.exp (Real.pi * Complex.I * (D.EF x y : ℂ)) := by
  have h : phase D (x + y) = phase D x * phase D y *
      (((Int.negOnePow (D.EF x y) : ℤˣ) : ℤ) : ℂ) := by
    simp only [phase, quadraticRefinement_add, Int.negOnePow_add, Int.negOnePow_two_mul]
    push_cast
    ring
  rw [h, intSign_eq_exp]
  congr 2
  ring

theorem phase_two_smul (x : D.La) : phase D ((2 : ℤ) • x) = 1 := by
  rw [two_smul, phase_add, D.alt]
  simpa [sq] using phase_sq D x

end Phase

section Hermitian

variable {g : ℕ}

theorem hermForm_add_left (Hm : Matrix (Fin g) (Fin g) ℂ) (x y z : Fin g → ℂ) :
    hermForm Hm (x + y) z = hermForm Hm x z + hermForm Hm y z := by
  simp [hermForm, add_dotProduct]

theorem hermForm_add_right (Hm : Matrix (Fin g) (Fin g) ℂ) (x y z : Fin g → ℂ) :
    hermForm Hm x (y + z) = hermForm Hm x y + hermForm Hm x z := by
  simp [hermForm, Matrix.mulVec_add, dotProduct_add]

theorem hermForm_swap (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian)
    (z w : Fin g → ℂ) : hermForm Hm w z = star (hermForm Hm z w) := by
  simp only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul',
    Finset.mul_sum, Pi.star_apply, star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hH.apply]
  ring

end Hermitian

section Automorphy

variable {H : NativeGeometricHost E} (D : NativeGeometricDatum H) {g : ℕ}
  (P : D.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ)

/-- Literal Appell--Humbert factor for the constructed canonical phase. -/
def factor (x : D.La) (z : Fin g → ℂ) : ℂ :=
  phase D x * Complex.exp
    (Real.pi * hermForm Hm z (P x) + Real.pi / 2 * hermForm Hm (P x) (P x))

@[simp] theorem factor_zero (z : Fin g → ℂ) : factor D P Hm 0 z = 1 := by
  simp [factor, hermForm]

theorem factor_ne_zero (x : D.La) (z : Fin g → ℂ) : factor D P Hm x z ≠ 0 :=
  mul_ne_zero (phase_ne_zero D x) (Complex.exp_ne_zero _)

/-- The cocycle is proved from the integer polarization and its exact
Hermitian-period identity, with the source's linear-first convention. -/
theorem factor_add (hH : Hm.IsHermitian)
    (hEF : ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y)
    (x y : D.La) (z : Fin g → ℂ) :
    factor D P Hm (x + y) z = factor D P Hm y (z + P x) * factor D P Hm x z := by
  have hcross : hermForm Hm (P x) (P y) - hermForm Hm (P y) (P x) =
      2 * (D.EF x y : ℂ) * Complex.I := by
    rw [hermForm_swap Hm hH (P x) (P y)]
    change hermForm Hm (P x) (P y) - conj (hermForm Hm (P x) (P y)) = _
    rw [Complex.sub_conj, hEF]
    push_cast
    ring
  unfold factor
  rw [phase_add, map_add, hermForm_add_right,
    hermForm_add_left, hermForm_add_right, hermForm_add_right, hermForm_add_left]
  calc
    _ = (phase D y * phase D x) * Complex.exp
        (Real.pi * Complex.I * (D.EF x y : ℂ) +
          (Real.pi * (hermForm Hm z (P x) + hermForm Hm z (P y)) +
            Real.pi / 2 * ((hermForm Hm (P x) (P x) + hermForm Hm (P x) (P y)) +
              (hermForm Hm (P y) (P x) + hermForm Hm (P y) (P y))))) := by
      rw [Complex.exp_add]
      ring
    _ = (phase D y * phase D x) * Complex.exp
        ((Real.pi * (hermForm Hm z (P y) + hermForm Hm (P x) (P y)) +
          Real.pi / 2 * hermForm Hm (P y) (P y)) +
          (Real.pi * hermForm Hm z (P x) + Real.pi / 2 * hermForm Hm (P x) (P x))) := by
      congr 2
      linear_combination -(Real.pi / 2 : ℂ) * hcross
    _ = _ := by
      rw [Complex.exp_add]
      ring

/-- The squared fiber norm retains the exact pi normalization. -/
def fiberNormSq (z : Fin g → ℂ) (u : ℂ) : ℝ :=
  ‖u‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)

theorem norm_factor (x : D.La) (z : Fin g → ℂ) :
    ‖factor D P Hm x z‖ = Real.exp
      (Real.pi * (hermForm Hm z (P x)).re + Real.pi / 2 * (hermForm Hm (P x) (P x)).re) := by
  have hcast : ((Real.pi / 2 : ℝ) : ℂ) = (Real.pi : ℂ) / 2 := by
    push_cast <;> rfl
  rw [factor, norm_mul, norm_phase, one_mul, Complex.norm_exp, ← hcast,
    Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]

/-- Translating by an actual period and its constructed factor preserves
the Gaussian Hermitian metric exactly, without a scalar-normalization law. -/
theorem fiberNormSq_translate (hH : Hm.IsHermitian)
    (x : D.La) (z : Fin g → ℂ) (u : ℂ) :
    fiberNormSq Hm (z + P x) (factor D P Hm x z * u) = fiberNormSq Hm z u := by
  have hcross : (hermForm Hm (P x) z).re = (hermForm Hm z (P x)).re := by
    simpa only [Complex.star_def, Complex.conj_re] using
      congrArg Complex.re (hermForm_swap Hm hH z (P x))
  have hexp :
      (Real.pi * (hermForm Hm z (P x)).re + Real.pi / 2 * (hermForm Hm (P x) (P x)).re) +
      (Real.pi * (hermForm Hm z (P x)).re + Real.pi / 2 * (hermForm Hm (P x) (P x)).re) +
      (-Real.pi * (hermForm Hm (z + P x) (z + P x)).re) =
      -Real.pi * (hermForm Hm z z).re := by
    rw [hermForm_add_left, hermForm_add_right, hermForm_add_right]
    simp only [Complex.add_re, hcross]
    ring
  simp only [fiberNormSq, norm_mul, norm_factor]
  calc
    _ = ‖u‖ ^ 2 *
        (Real.exp ((Real.pi * (hermForm Hm z (P x)).re + Real.pi / 2 * (hermForm Hm (P x) (P x)).re) +
          (Real.pi * (hermForm Hm z (P x)).re + Real.pi / 2 * (hermForm Hm (P x) (P x)).re)) *
          Real.exp (-Real.pi * (hermForm Hm (z + P x) (z + P x)).re)) := by
      rw [Real.exp_add]
      ring
    _ = _ := by rw [← Real.exp_add, hexp]

end Automorphy

end RHLean.Geometry.NativeTheta.AppellHumbert

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeGeometricPeriods
open RHLean.Geometry.NativeTheta.AppellHumbert
open NativeRawHostPolarization

/-- Construct the analytic theta cocycle and its metric on the same
prescribed native periods, using the already proved positive Hermitian form.
No phase, cocycle, metric or period compatibility hypothesis is added. -/
theorem nativeDyadicPrescribedPeriod_exists_thetaFactor
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    (B : Ideal (𝓞 (nativeDyadicHostRaw e q d he hH).E))
    (hB : let H := nativeDyadicHostRaw e q d he hH
      differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    let D := nativeDyadicPrescribedGeometricDatum e q d he hH B hB k m j hk hj
    let P := prescribedPeriodMap H.toHostRaw B hB k m j
    ∃ Hm : Matrix (Fin ((cmTypeFinset H.toHostRaw).card * (k + m - 1)))
        (Fin ((cmTypeFinset H.toHostRaw).card * (k + m - 1))) ℂ,
      Hm.IsHermitian ∧
      (∀ z, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
      (∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y) ∧
      (∀ x z, factor D P Hm x z ≠ 0) ∧
      (∀ x y z, factor D P Hm (x + y) z = factor D P Hm y (z + P x) * factor D P Hm x z) ∧
      (∀ x z u, fiberNormSq Hm (z + P x) (factor D P Hm x z * u) = fiberNormSq Hm z u) := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  let D := nativeDyadicPrescribedGeometricDatum e q d he hH B hB k m j hk hj
  let P := prescribedPeriodMap H.toHostRaw B hB k m j
  have hP := (nativeDyadicPrescribedGeometricDatum_isPeriod e q d he hH B hB k m j hk hj).2
  obtain ⟨Hm, hHerm, hpos, hEF⟩ := hP.2.2.2.2
  exact ⟨Hm, hHerm, hpos, hEF, factor_ne_zero D P Hm,
    factor_add D P Hm hHerm hEF, fiberNormSq_translate D P Hm hHerm⟩

end RHLean.Analysis.AlpogeThin

end

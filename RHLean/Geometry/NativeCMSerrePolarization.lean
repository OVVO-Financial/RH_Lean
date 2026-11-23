import RHLean.Geometry.NativeCMSerrePeriods
import RHLean.Geometry.NativeCMPureBlockPositivity

/-!
# Exact seed metric and trace-Hermitian tensor polarization

The Hermitian form on the actual projective coefficient module is paired
with the actual normalized elliptic metric. With the source orientation
epsilon * Im(omega) > 0, its imaginary part is exactly the original EF.
Its diagonal is the positive source integer divided by |Im(omega)|.
The native coefficient specialization discharges diagonal positivity from
the actual trace-as-sum-of-squares identity. No integral tangent generator
is identified with the normalized analytic coordinate.

Source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/`
`ExistsHermFormCurve.lean`, the `hform` calculation in
`exists_isExp_of_isTen`, and `ExistsUniqueCmHermitianLatticeForm.lean`.
The source archive states no license; attribution is retained without
assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField
open scoped Classical TensorProduct Pointwise

namespace RHLean.Geometry.NativeCM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    {G : NativeGeometricHost E} (D : TraceLattice G) (ε : ℤˣ) (τ : E →+* ℂ)

theorem kLin_embed_im (x y : D.La) :
    (embed G τ (kLin D ε x y)).im =
      ((ε : ℤ) : ℝ) * (D.EF x y : ℝ) * (EllipticSeed.omega G τ).im := by
  simp [kLin_apply, kFun, EllipticSeed.omega, Complex.mul_im]

/-- The sign is fixed by the actual chosen seed embedding. -/
theorem seed_orientation_abs
    (hε : 0 < ((ε : ℤ) : ℝ) * (EllipticSeed.omega G τ).im) :
    ((ε : ℤ) : ℝ) * (EllipticSeed.omega G τ).im =
      |(EllipticSeed.omega G τ).im| := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simp at hε ⊢
    exact (abs_of_pos hε).symm
  · simp at hε ⊢
    exact (abs_of_neg (by linarith : (EllipticSeed.omega G τ).im < 0)).symm

/-- The actual tensor polarization restricts to the very same integral
alternating trace form, with no sign or scalar discarded. -/
theorem seed_metric_kLin_im
    (hε : 0 < ((ε : ℤ) : ℝ) * (EllipticSeed.omega G τ).im) (x y : D.La) :
    (EllipticSeed.hermitian G τ (embed G τ (kLin D ε x y)) 1).im =
      (D.EF x y : ℝ) := by
  simp only [EllipticSeed.hermitian, map_one, mul_one, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [kLin_embed_im]
  have hb : |(EllipticSeed.omega G τ).im| ≠ 0 :=
    ne_of_gt (abs_pos.2 (EllipticSeed.omega_im_ne_zero G τ))
  calc
    _ = (|(EllipticSeed.omega G τ).im|⁻¹ *
        (((ε : ℤ) : ℝ) * (EllipticSeed.omega G τ).im)) * (D.EF x y : ℝ) := by ring
    _ = (D.EF x y : ℝ) := by
      rw [seed_orientation_abs ε τ hε, inv_mul_cancel₀ hb, one_mul]

theorem seed_metric_kLin_diagonal (x : D.La) :
    (EllipticSeed.hermitian G τ (embed G τ (kLin D ε x x)) 1).re =
      |(EllipticSeed.omega G τ).im|⁻¹ *
        (((ε : ℤ) * D.EF (G.w0 • x) x : ℤ) : ℝ) := by
  have hd : kLin D ε x x =
      (((ε : ℤ) * D.EF (G.w0 • x) x : ℤ) : OK G) :=
    Subtype.ext (kLin_diagonal D ε x)
  rw [hd]
  simp [EllipticSeed.hermitian]

theorem seed_metric_kLin_diagonal_pos (x : D.La)
    (hx : 0 < (ε : ℤ) * D.EF (G.w0 • x) x) :
    0 < (EllipticSeed.hermitian G τ (embed G τ (kLin D ε x x)) 1).re := by
  rw [seed_metric_kLin_diagonal]
  exact mul_pos (inv_pos.2 (abs_pos.2 (EllipticSeed.omega_im_ne_zero G τ)))
    (by exact_mod_cast hx)

/-- The scalar multiplying the actual embedded Hermitian form is exactly
the source discriminant normalization. -/
theorem seed_metric_kLin_pi (x : D.La) :
    Real.pi * (EllipticSeed.hermitian G τ
        (embed G τ (kLin D ε x x)) 1).re =
      (2 * Real.pi / Real.sqrt G.d) *
        (((ε : ℤ) * D.EF (G.w0 • x) x : ℤ) : ℝ) := by
  rw [seed_metric_kLin_diagonal, EllipticSeed.abs_omega_im, inv_div]
  ring

end RHLean.Geometry.NativeCM

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeCM
open NativeRawHostPolarization

/-- The original native CM type fixes the positive elliptic orientation. -/
theorem nativeDyadic_seedOrientation
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    let G := nativeDyadicGeometricHostOfDerived e q d he hH
    ∀ τ : cmTypeFinset H.toHostRaw, 0 < (EllipticSeed.omega G (τ : H.E →+* ℂ)).im := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  let G := nativeDyadicGeometricHostOfDerived e q d he hH
  intro τ
  have ht := (mem_cmTypeFinset H.toHostRaw τ).1 τ.2
  change (τ : H.E →+* ℂ) H.sqd = Complex.I * (Real.sqrt d : ℂ) at ht
  have hw := EllipticSeed.two_mul_omega G (τ : H.E →+* ℂ)
  change 2 * EllipticSeed.omega G (τ : H.E →+* ℂ) =
    1 + (τ : H.E →+* ℂ) H.sqd at hw
  rw [ht] at hw
  have hi := congrArg Complex.im hw
  simp at hi
  have hd : 0 < Real.sqrt (d : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast (Fact.out : d.Prime).pos)
  linarith

/-- On the actual native positive CM type, the seed and trace-Hermitian
module give exactly the original integral alternating polarization. -/
theorem nativeDyadic_coefficientSerreMetric_im
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    (B : Ideal (𝓞 (nativeDyadicHostRaw e q d he hH).E))
    (hB : let H := nativeDyadicHostRaw e q d he hH
      differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    let G := nativeDyadicGeometricHostOfDerived e q d he hH
    let D := coefficientTraceLattice H.toHostRaw G
      (nativeDyadicGeometricHost_bar_eq e q d he hH) B hB
    ∀ (τ : cmTypeFinset H.toHostRaw)
      (x y : (coefficientIdeal H.toHostRaw B : Submodule (𝓞 H.E) H.E)),
      (EllipticSeed.hermitian G (τ : H.E →+* ℂ)
        (embed G (τ : H.E →+* ℂ) (kLin D 1 x y)) 1).im =
          (integralTraceForm H.toHostRaw B hB x y : ℝ) := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  let G := nativeDyadicGeometricHostOfDerived e q d he hH
  let D := coefficientTraceLattice H.toHostRaw G
    (nativeDyadicGeometricHost_bar_eq e q d he hH) B hB
  intro τ x y
  apply seed_metric_kLin_im D 1 (τ : H.E →+* ℂ)
  simpa using nativeDyadic_seedOrientation e q d he hH τ

/-- The actual coefficient tensor metric is positive. Its exact pi-scaled
diagonal retains the original integral trace value and discriminant. -/
theorem nativeDyadic_coefficientSerreMetric
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    (B : Ideal (𝓞 (nativeDyadicHostRaw e q d he hH).E))
    (hB : let H := nativeDyadicHostRaw e q d he hH
      differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    let G := nativeDyadicGeometricHostOfDerived e q d he hH
    let D := coefficientTraceLattice H.toHostRaw G
      (nativeDyadicGeometricHost_bar_eq e q d he hH) B hB
    ∀ (τ : H.E →+* ℂ)
      (x : (coefficientIdeal H.toHostRaw B : Submodule (𝓞 H.E) H.E)),
      (x ≠ 0 → 0 < (EllipticSeed.hermitian G τ
        (embed G τ (kLin D 1 x x)) 1).re) ∧
      Real.pi * (EllipticSeed.hermitian G τ
        (embed G τ (kLin D 1 x x)) 1).re =
        (2 * Real.pi / Real.sqrt G.d) *
          (integralTraceForm H.toHostRaw B hB (G.w0 • x) x : ℝ) := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  let G := nativeDyadicGeometricHostOfDerived e q d he hH
  let D := coefficientTraceLattice H.toHostRaw G
    (nativeDyadicGeometricHost_bar_eq e q d he hH) B hB
  intro τ x
  constructor
  · intro hx
    apply seed_metric_kLin_diagonal_pos D 1 τ x
    simpa using (nativeDyadicHalfRoot_pureBlockPositivity e q d he hH B hB).1 x hx
  · simpa using seed_metric_kLin_pi D 1 τ x

end RHLean.Analysis.AlpogeThin

end

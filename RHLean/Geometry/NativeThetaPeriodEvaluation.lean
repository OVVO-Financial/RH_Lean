import RHLean.Geometry.NativeThetaAppellHumbert

/-! Evaluation on a single coset of the actual period lattice. -/

noncomputable section
open NumberField

namespace RHLean.Geometry.NativeTheta.AppellHumbert

open NativeGeometricPeriods

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
  {H : NativeGeometricHost E} (D : NativeGeometricDatum H) {g : ℕ}
  (P : D.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ)

/-- In the actual line trivialization, the evaluation along every period
translate reads the original value. The input is exactly the automorphy
field supplied by the square-host theta constructor. -/
theorem normalized_period_value (θ : (Fin g → ℂ) → ℂ)
    (hθ : ∀ v z, θ (z + P v) = factor D P Hm v z * θ z)
    (v : D.La) (z : Fin g → ℂ) :
    θ (z + P v) / factor D P Hm v z = θ z := by
  rw [hθ, div_eq_iff (factor_ne_zero D P Hm v z)]
  exact mul_comm _ _

/-- Two sections of the same automorphy factor on any two period translates
have zero evaluation determinant. This calculation uses the physical factor. -/
theorem period_value_two_minor (θ η : (Fin g → ℂ) → ℂ)
    (hθ : ∀ v z, θ (z + P v) = factor D P Hm v z * θ z)
    (hη : ∀ v z, η (z + P v) = factor D P Hm v z * η z)
    (v w : D.La) (z : Fin g → ℂ) :
    θ (z + P v) * η (z + P w) - θ (z + P w) * η (z + P v) = 0 := by
  simp only [hθ, hη]
  ring

end RHLean.Geometry.NativeTheta.AppellHumbert

end

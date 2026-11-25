import RHLean.Geometry.NativeThetaHasseDigits
import RHLean.Geometry.NativeThetaIntegralJets

/-!
# Integral recovery of the coarse Hasse coefficients

The transpose of the native Taylor matrix at one is the binomial evaluation
matrix on the same finite set of coarse labels. Its adjugate recovers the
coefficient vector modulo the original p^c.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace RHLean.Geometry.NativeTheta.HasseDigits

/-- Recover every coarse digit coefficient from the bounded grid of genuine
    binomial values. The result uses the same precision in the measurements
    and in the recovered coefficients. -/
theorem recover_bounded_hasse_digits {ι : Type} [Fintype ι] {p : ℕ} (hp : p.Prime)
    (g c : ℕ) (ρ M : ι → ℕ) :
    let B := (∑ i, M i / p ^ g) + c
    let S := (Finset.univ : Finset (ι → Fin B)).filter (fun k => (∑ i, (k i).val) < B)
    let a (k : S) : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => (k.val i).val)
    let D := (IntegralJets.jetMatrix (fun _ : ι => (1 : ZMod (p ^ c))) a).transpose
    D.adjugate.mulVec (fun k : S => ∏ i, ((ρ i + p ^ g * (k.val i).val).choose (M i) : ZMod (p ^ c))) =
      fun k : S => ∏ i, (digitCoeff (p ^ g) (ρ i) (M i) (k.val i).val : ZMod (p ^ c)) := by
  let B := (∑ i, M i / p ^ g) + c
  let S := (Finset.univ : Finset (ι → Fin B)).filter (fun k => (∑ i, (k i).val) < B)
  let a (k : S) : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => (k.val i).val)
  let D := (IntegralJets.jetMatrix (fun _ : ι => (1 : ZMod (p ^ c))) a).transpose
  let v (k : S) : ZMod (p ^ c) := ∏ i, (digitCoeff (p ^ g) (ρ i) (M i) (k.val i).val : ZMod (p ^ c))
  let y (k : S) : ZMod (p ^ c) := ∏ i, ((ρ i + p ^ g * (k.val i).val).choose (M i) : ZMod (p ^ c))
  change D.adjugate.mulVec y = v
  have ha : Function.Injective a := by
    intro k l h
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact congrArg (fun m : ι →₀ ℕ => m i) h
  have hdet : D.det = 1 :=
    (Matrix.det_transpose _).trans (IntegralJets.jetMatrix_det (fun _ : ι => (1 : ZMod (p ^ c))) a ha)
  have hD (j k : S) : D j k = ∏ i, ((j.val i).val.choose (k.val i).val : ZMod (p ^ c)) := by
    change IntegralJets.mixedTaylorWeight (fun _ : ι => (1 : ZMod (p ^ c))) (a k) (a j) = _
    simp only [IntegralJets.mixedTaylorWeight_eq_binomial, one_pow, mul_one]
    rfl
  have he : D.mulVec v = y := by
    funext j
    change ∑ k : S, D j k * v k = y j
    have hy : y j = ∑ k ∈ S, ∏ i, (digitCoeff (p ^ g) (ρ i) (M i) (k i).val : ZMod (p ^ c)) *
        ((j.val i).val.choose (k i).val : ZMod (p ^ c)) :=
      choose_prod_eq_bounded_hasse_sum hp g c ρ M (fun i => (j.val i).val)
    rw [hy, ← Finset.sum_coe_sort S]
    apply Finset.sum_congr rfl
    intro k _
    rw [hD, Finset.prod_mul_distrib]
    exact mul_comm _ _
  rw [← he, Matrix.mulVec_mulVec, Matrix.adjugate_mul, hdet, one_smul, Matrix.one_mulVec]

end RHLean.Geometry.NativeTheta.HasseDigits

end

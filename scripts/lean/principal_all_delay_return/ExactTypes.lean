import «research.oai_434.VF919PrincipalAllDelayReturn»

open scoped BigOperators
open OAI.SevenEighths
open HeckeFamily HeckeSignal Continuation PrincipalSignalComparison
open PrincipalSlotEstimate PrincipalAllDelayReturn

#check slotResidueC_eq_reciprocal
#check slotResidueC_shift_right
#check gaussian_atom_dilation
#check finite_response_contour
#check slotResidueC_all_delay_error
#check normalized_source_eq_slotResidueC
#check normalized_source_all_delay_error
#check source_correction_all_delay_error

example (G : ℂ → ℂ) (c Z d : ℝ) (hZ : 0 < Z) (B s : ℂ) :
    gaussianContourIntegrand G c Z s * (B * Complex.exp (-(d : ℂ) * s)) =
      (B * (Real.exp (d * c) : ℂ)) *
        gaussianContourIntegrand G c (Z / Real.exp d) s :=
  gaussian_atom_dilation G c hZ (d, B) s

example {κ ι : Type*} (chi : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7 / 8 < s.re})
    (hb : ∀ s : ℂ, 7 / 8 < s.re → ‖H s - 1‖ ≤ 1 / 2)
    (c : ℝ) {a Z m : ℝ} (ha : 7 / 8 < a) (ha2 : a ≤ 2)
    (hbeta : HeckeZeroSupremum.beta < a) (hZ : 1 ≤ Z)
    (K : ℕ) (horder : 2 ≤ (7 / 8 : ℝ) * m * (K + 1))
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A eta : κ → ι → ℂ) (h : SlotBounds S T w Q A eta (Z ^ m)) :
    ‖slotResidueC chi H c a Z S T w Q A eta -
        (signal chi H c Z + PrincipalAllDelayReturn.FiniteResponse.applyTerms
          (signal chi H c) c Z (principalProductResponseTerms K S T w Q A eta))‖ ≤
      (S.card * (5 : ℝ) ^ S.card * 4 * 2 ^ (K + 1)) * endpointConstant 2 * Z ^ c :=
  slotResidueC_all_delay_error chi H hH hb c ha ha2 hbeta hZ K horder S T w Q A eta h

example (Z d : ℝ) (hZ : 0 < Z) (hd : Real.log Z < d) :
    0 < Z / Real.exp d ∧ Z / Real.exp d < 1 := by
  refine ⟨div_pos hZ (Real.exp_pos d), ?_⟩
  rw [div_lt_one (Real.exp_pos d)]
  simpa only [Real.exp_log hZ] using Real.exp_lt_exp.mpr hd

#print axioms slotResidueC_shift_right
#print axioms gaussian_atom_dilation
#print axioms finite_response_contour
#print axioms slotResidueC_all_delay_error
#print axioms normalized_source_all_delay_error
#print axioms source_correction_all_delay_error

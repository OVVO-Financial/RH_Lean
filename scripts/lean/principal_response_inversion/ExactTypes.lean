import «research.oai_434.VF919PrincipalResponseInversion»

open scoped Topology
open Set Filter OAI.SevenEighths
open HeckeFamily HeckeSignal PrincipalSlotEstimate PrincipalMellinResidues PrincipalResponseInversion
open PrincipalSlotEstimate.FiniteResponse PrincipalAllDelayReturn.FiniteResponse

#check weighted_dilation
#check applyTerms_norm_le
#check weighted_prefix_bddAbove
#check power_bound_of_response
#check signal_small_argument_bound
#check signal_power_bound_of_eventual_response
#check principal_response_eventually_contracts
#check signal_power_bound_of_principal_response

example (f : ℝ → ℂ) (c theta q Z0 A : ℝ)
    (hf : ContinuousOn f (Ioi 0))
    (hzero : ∃ C ≥ 0, ∀ x, 0 < x → x ≤ 1 → ‖f x‖ ≤ C * x ^ (theta + c))
    (hq : 0 ≤ q) (hq1 : q < 1) (hZ0 : 1 ≤ Z0) (hA : 0 ≤ A)
    (p : ℝ → Terms)
    (hd : ∀ Z, Z0 ≤ Z → nonnegativeDelays (p Z))
    (hm : ∀ Z, Z0 ≤ Z → mass theta (p Z) ≤ q)
    (hr : ∀ Z, Z0 ≤ Z → ‖f Z + applyTerms f c Z (p Z)‖ ≤ A * Z ^ (theta + c)) :
    ∃ C ≥ 0, ∀ Z, 0 < Z → ‖f Z‖ ≤ C * Z ^ (theta + c) :=
  power_bound_of_response f c theta q Z0 A hf hzero hq hq1 hZ0 hA p hd hm hr

example (f : ℝ → ℂ) (c theta K X : ℝ)
    (hf : ∀ x, 0 < x → x ≤ X → ‖f x‖ ≤ K * x ^ (theta + c))
    (Z : ℝ) (hZ : 0 < Z) (hZX : Z ≤ X) (B : ℂ) :
    ‖applyTerms f c Z [(0, B)]‖ ≤
      K * Z ^ (theta + c) * mass theta [(0, B)] :=
  applyTerms_norm_le f c theta K X hf hZ hZX _ (by
    intro a ha
    have heq : a = (0, B) := List.mem_singleton.mp ha
    subst a
    exact le_rfl)

example (chi : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7 / 8 < s.re})
    (hb : ∀ s : ℂ, 7 / 8 < s.re → ‖H s - 1‖ ≤ 1 / 2)
    (c theta q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (p : ℝ → Terms)
    (hp : ∀ᶠ Z : ℝ in atTop, nonnegativeDelays (p Z) ∧ mass theta (p Z) ≤ q)
    (hr : ∃ A ≥ 0, ∀ᶠ Z : ℝ in atTop,
      ‖signal chi H c Z + applyTerms (signal chi H c) c Z (p Z)‖ ≤ A * Z ^ (theta + c)) :
    ∃ C ≥ 0, ∀ Z, 0 < Z → ‖signal chi H c Z‖ ≤ C * Z ^ (theta + c) :=
  signal_power_bound_of_eventual_response chi H hH hb c theta q hq hq1 p hp hr

example {κ ι : Type*} (chi : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7 / 8 < s.re})
    (hb : ∀ s : ℂ, 7 / 8 < s.re → ‖H s - 1‖ ≤ 1 / 2)
    (c : ℝ) (K : ℕ) (S : Finset κ) (T : ℝ → κ → Finset ι)
    (w Q : ℝ → κ → ι → ℝ) (A eta : ℝ → κ → ι → ℂ)
    (m theta : ℝ) (hm : 0 < m) (htheta : 3 / 5 < theta)
    (hslot : ∀ᶠ Z : ℝ in atTop, SlotBounds S (T Z) (w Z) (Q Z) (A Z) (eta Z) (Z ^ m))
    (hr : ∃ C ≥ 0, ∀ᶠ Z : ℝ in atTop,
      ‖signal chi H c Z + applyTerms (signal chi H c) c Z
        (principalProductResponseTerms K S (T Z) (w Z) (Q Z) (A Z) (eta Z))‖ ≤
          C * Z ^ (theta + c)) :
    ∃ C ≥ 0, ∀ Z, 0 < Z → ‖signal chi H c Z‖ ≤ C * Z ^ (theta + c) :=
  signal_power_bound_of_principal_response chi H hH hb c K S T w Q A eta m theta hm htheta hslot hr

example (Z d : ℝ) (hZ : 0 < Z) (hd : Real.log Z < d) :
    0 < Z / Real.exp d ∧ Z / Real.exp d < 1 := by
  refine ⟨div_pos hZ (Real.exp_pos d), ?_⟩
  rw [div_lt_one (Real.exp_pos d)]
  simpa only [Real.exp_log hZ] using Real.exp_lt_exp.mpr hd

#print axioms power_bound_of_response
#print axioms signal_power_bound_of_eventual_response
#print axioms principal_response_eventually_contracts
#print axioms signal_power_bound_of_principal_response

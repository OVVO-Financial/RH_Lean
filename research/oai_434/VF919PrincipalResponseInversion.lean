import «research.oai_434.VF919PrincipalAllDelayReturn»
import Mathlib.Topology.Order.Compact

/-!
# Finite-prefix inversion of the complete original principal response

Claim 20261110-coordinator-2309-EST/FFR3, independently accepted by
20261111-referee-1. Only finite-prefix suprema are taken. All delays and
repeated labels remain, including arguments below one. The full physical
response estimate (FFR4) is a separate obligation, not proved here.
-/

namespace OAI
noncomputable section
open scoped Classical Topology
open Set Filter
namespace SevenEighths.PrincipalResponseInversion
open HeckeFamily HeckeSignal PrincipalSlotEstimate PrincipalSignalComparison
open PrincipalSlotEstimate.FiniteResponse
open PrincipalAllDelayReturn.FiniteResponse

/-- Exact weight conversion, with no restriction on the real exponents. -/
theorem weighted_dilation (c theta d : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    Real.exp (d * c) * (Z / Real.exp d) ^ (theta + c) =
      Z ^ (theta + c) * Real.exp (-d * theta) := by
  rw [Real.div_rpow hZ.le (Real.exp_pos d).le, ← Real.exp_mul]
  calc
    _ = Z ^ (theta + c) * (Real.exp (d * c) / Real.exp (d * (theta + c))) := by ring
    _ = _ := by
      rw [← Real.exp_sub]
      congr 2
      ring

/-- A finite-prefix bound controls the whole labelled response. Zero delays
are allowed; strict contraction, not a minimum positive delay, is decisive. -/
theorem applyTerms_norm_le (f : ℝ → ℂ) (c theta K X : ℝ)
    (hprefix : ∀ x, 0 < x → x ≤ X → ‖f x‖ ≤ K * x ^ (theta + c))
    {Z : ℝ} (hZ : 0 < Z) (hZX : Z ≤ X) (p : Terms)
    (hd : nonnegativeDelays p) :
    ‖applyTerms f c Z p‖ ≤ K * Z ^ (theta + c) * mass theta p := by
  induction p with
  | nil => simp [applyTerms, mass]
  | cons a p ih =>
    have ha : 0 ≤ a.1 := hd a (by simp)
    have hp : nonnegativeDelays p := fun b hb => hd b (by simp [hb])
    have hx : 0 < Z / Real.exp a.1 := div_pos hZ (Real.exp_pos _)
    have hxZ : Z / Real.exp a.1 ≤ Z := by
      apply (div_le_iff₀ (Real.exp_pos _)).2
      nlinarith [Real.one_le_exp_iff.mpr ha]
    have hatom : ‖a.2 * (Real.exp (a.1 * c) : ℂ) * f (Z / Real.exp a.1)‖ ≤
        K * Z ^ (theta + c) * massAtom theta a := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      calc
        _ ≤ (‖a.2‖ * Real.exp (a.1 * c)) *
            (K * (Z / Real.exp a.1) ^ (theta + c)) :=
          mul_le_mul_of_nonneg_left (hprefix _ hx (hxZ.trans hZX)) (by positivity)
        _ = K * ‖a.2‖ *
            (Real.exp (a.1 * c) * (Z / Real.exp a.1) ^ (theta + c)) := by ring
        _ = _ := by rw [weighted_dilation c theta a.1 hZ]; unfold massAtom; ring
    calc
      _ ≤ ‖a.2 * (Real.exp (a.1 * c) : ℂ) * f (Z / Real.exp a.1)‖ +
          ‖applyTerms f c Z p‖ := norm_add_le _ _
      _ ≤ K * Z ^ (theta + c) * massAtom theta a +
          K * Z ^ (theta + c) * mass theta p := add_le_add hatom (ih hp)
      _ = _ := by rw [mass]; ring

/-- Local continuity plus an actual small-argument bound makes each finite
positive prefix bounded. This is not a global growth assumption. -/
theorem weighted_prefix_bddAbove (f : ℝ → ℂ) (gamma : ℝ)
    (hf : ContinuousOn f (Ioi 0))
    (hzero : ∃ C ≥ 0, ∀ x, 0 < x → x ≤ 1 → ‖f x‖ ≤ C * x ^ gamma)
    (X : ℝ) :
    BddAbove ((fun x => ‖f x‖ / x ^ gamma) '' Ioc 0 X) := by
  obtain ⟨C, _hC, hsmall⟩ := hzero
  have hsub : Icc (1 : ℝ) (max 1 X) ⊆ Ioi 0 := by
    intro x hx
    exact zero_lt_one.trans_le hx.1
  have hp : ContinuousOn (fun x : ℝ => x ^ gamma) (Icc 1 (max 1 X)) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (hsub hx)))
  have hc : ContinuousOn (fun x => ‖f x‖ / x ^ gamma) (Icc 1 (max 1 X)) :=
    (hf.mono hsub).norm.div hp (fun x hx => (Real.rpow_pos_of_pos (hsub hx) _).ne')
  obtain ⟨D, hD⟩ := isCompact_Icc.bddAbove_image hc
  refine ⟨max C D, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  by_cases hx1 : x ≤ 1
  · exact ((div_le_iff₀ (Real.rpow_pos_of_pos hx.1 gamma)).2
      (hsmall x hx.1 hx1)).trans (le_max_left _ _)
  · exact (hD (mem_image_of_mem _ ⟨(lt_of_not_ge hx1).le,
      hx.2.trans (le_max_right _ _)⟩)).trans (le_max_right _ _)

/-- Invert an outer-scale dependent response using finite suprema only.
The returned-response bound is explicit and remains a separate premise. -/
theorem power_bound_of_response (f : ℝ → ℂ) (c theta q Z0 A : ℝ)
    (hf : ContinuousOn f (Ioi 0))
    (hzero : ∃ C ≥ 0, ∀ x, 0 < x → x ≤ 1 → ‖f x‖ ≤ C * x ^ (theta + c))
    (hq : 0 ≤ q) (hq1 : q < 1) (hZ0 : 1 ≤ Z0) (hA : 0 ≤ A)
    (p : ℝ → Terms)
    (hd : ∀ Z, Z0 ≤ Z → nonnegativeDelays (p Z))
    (hm : ∀ Z, Z0 ≤ Z → mass theta (p Z) ≤ q)
    (hr : ∀ Z, Z0 ≤ Z → ‖f Z + applyTerms f c Z (p Z)‖ ≤ A * Z ^ (theta + c)) :
    ∃ C ≥ 0, ∀ Z, 0 < Z → ‖f Z‖ ≤ C * Z ^ (theta + c) := by
  obtain ⟨C0, hC0⟩ := weighted_prefix_bddAbove f (theta + c) hf hzero Z0
  let C := (max 0 C0 + A) / (1 - q)
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  refine ⟨C, div_nonneg (add_nonneg (le_max_left _ _) hA) hden.le, ?_⟩
  intro Z hZ
  let X := max Z0 Z
  let V := (fun x => ‖f x‖ / x ^ (theta + c)) '' Ioc 0 X
  have hX : 1 ≤ X := hZ0.trans (le_max_left _ _)
  have hbdd : BddAbove V := weighted_prefix_bddAbove f (theta + c) hf hzero X
  have hne : V.Nonempty := ⟨‖f 1‖ / (1 : ℝ) ^ (theta + c),
    mem_image_of_mem _ ⟨zero_lt_one, hX⟩⟩
  let U := sSup V
  have hpoint (x : ℝ) (hx : 0 < x) (hxX : x ≤ X) :
      ‖f x‖ / x ^ (theta + c) ≤ U := le_csSup hbdd (mem_image_of_mem _ ⟨hx, hxX⟩)
  have hU : 0 ≤ U := (div_nonneg (norm_nonneg _) (Real.rpow_nonneg zero_le_one _)).trans
    (hpoint 1 zero_lt_one hX)
  have hprefix (x : ℝ) (hx : 0 < x) (hxX : x ≤ X) :
      ‖f x‖ ≤ U * x ^ (theta + c) :=
    (div_le_iff₀ (Real.rpow_pos_of_pos hx _)).1 (hpoint x hx hxX)
  have hsup : U ≤ max 0 C0 + A + q * U := by
    apply csSup_le hne
    rintro y ⟨x, hx, rfl⟩
    by_cases hx0 : x ≤ Z0
    · have hinit := hC0 (mem_image_of_mem (fun x => ‖f x‖ / x ^ (theta + c)) ⟨hx.1, hx0⟩)
      have := le_max_right (0 : ℝ) C0
      have := mul_nonneg hq hU
      linarith
    · have hx0' : Z0 ≤ x := (lt_of_not_ge hx0).le
      have hresp := applyTerms_norm_le f c theta U X hprefix hx.1 hx.2 (p x) (hd x hx0')
      have hn : ‖f x‖ ≤ (A + q * U) * x ^ (theta + c) := by
        calc
          _ = ‖(f x + applyTerms f c x (p x)) - applyTerms f c x (p x)‖ := by simp
          _ ≤ ‖f x + applyTerms f c x (p x)‖ + ‖applyTerms f c x (p x)‖ := norm_sub_le _ _
          _ ≤ A * x ^ (theta + c) + U * x ^ (theta + c) * mass theta (p x) :=
            add_le_add (hr x hx0') hresp
          _ ≤ A * x ^ (theta + c) + U * x ^ (theta + c) * q :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left (hm x hx0')
              (mul_nonneg hU (Real.rpow_nonneg hx.1.le _)))
          _ = _ := by ring
      have hnorm := (div_le_iff₀ (Real.rpow_pos_of_pos hx.1 (theta + c))).2 hn
      have := le_max_left (0 : ℝ) C0
      linarith
  have hUC : U ≤ C := (le_div_iff₀ hden).2 (by nlinarith [hsup])
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).1
    ((hpoint Z hZ (le_max_right _ _)).trans hUC)

/-- The original signal supplies its small-argument estimate with one fixed
B=max(2,theta), even when theta+c is negative. -/
theorem signal_small_argument_bound (chi : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7 / 8 < s.re})
    (hb : ∀ s : ℂ, 7 / 8 < s.re → ‖H s - 1‖ ≤ 1 / 2)
    (c theta : ℝ) :
    ∃ C ≥ 0, ∀ x, 0 < x → x ≤ 1 → ‖signal chi H c x‖ ≤ C * x ^ (theta + c) := by
  refine ⟨endpointConstant (max 2 theta), endpointConstant_nonneg _, ?_⟩
  intro x hx hx1
  exact (signal_bound_at_zero chi H hH hb c (max 2 theta) (le_max_left _ _) hx hx1).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith [le_max_right (2 : ℝ) theta]))
      (endpointConstant_nonneg _))

/-- FFR3 for the same original Hecke signal, with an eventual response bound.
There is no assumed global supremum and no restriction on theta here. -/
theorem signal_power_bound_of_eventual_response (chi : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7 / 8 < s.re})
    (hb : ∀ s : ℂ, 7 / 8 < s.re → ‖H s - 1‖ ≤ 1 / 2)
    (c theta q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (p : ℝ → Terms)
    (hp : ∀ᶠ Z : ℝ in atTop, nonnegativeDelays (p Z) ∧ mass theta (p Z) ≤ q)
    (hr : ∃ A ≥ 0, ∀ᶠ Z : ℝ in atTop,
      ‖signal chi H c Z + applyTerms (signal chi H c) c Z (p Z)‖ ≤ A * Z ^ (theta + c)) :
    ∃ C ≥ 0, ∀ Z, 0 < Z → ‖signal chi H c Z‖ ≤ C * Z ^ (theta + c) := by
  obtain ⟨A, hA, hr⟩ := hr
  obtain ⟨Z0, hZ0⟩ := eventually_atTop.1 (hp.and hr)
  apply power_bound_of_response (signal chi H c) c theta q (max 1 Z0) A
    (signal_continuousOn chi H hH hb c) (signal_small_argument_bound chi H hH hb c theta)
    hq hq1 (le_max_left _ _) hA p
  · intro Z hZ
    exact (hZ0 Z ((le_max_right _ _).trans hZ)).1.1
  · intro Z hZ
    exact (hZ0 Z ((le_max_right _ _).trans hZ)).1.2
  · intro Z hZ
    exact (hZ0 Z ((le_max_right _ _).trans hZ)).2

/-- The already-proved complete original coefficient bound supplies eventual
contraction. Pool data may vary with the OUTER scale; no label is removed. -/
theorem principal_response_eventually_contracts {κ ι : Type*}
    (K : ℕ) (S : Finset κ) (T : ℝ → κ → Finset ι)
    (w Q : ℝ → κ → ι → ℝ) (A eta : ℝ → κ → ι → ℂ)
    (m theta : ℝ) (hm : 0 < m) (htheta : 3 / 5 < theta)
    (hslot : ∀ᶠ Z : ℝ in atTop, SlotBounds S (T Z) (w Z) (Q Z) (A Z) (eta Z) (Z ^ m)) :
    ∀ᶠ Z : ℝ in atTop,
      nonnegativeDelays (principalProductResponseTerms K S (T Z) (w Z) (Q Z) (A Z) (eta Z)) ∧
      mass theta (principalProductResponseTerms K S (T Z) (w Z) (Q Z) (A Z) (eta Z)) ≤ 1 / 2 := by
  have hpower := tendsto_rpow_atTop hm
  have hgate := hpower.eventually (principal_response_mass_gate_eventually theta htheta)
  have htend := (principal_response_mass_majorant_tendsto S.card theta htheta).comp hpower
  have hmass := htend.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hslot, hgate, hmass] with Z hs hg hM
  refine ⟨principal_product_response_delays K S (T Z) (w Z) (Q Z) (A Z) (eta Z)
    (fun j hj i hi => hg.1.trans (hs.norm_lower j hj i hi)), ?_⟩
  exact (principal_product_response_terms_mass K S (T Z) (w Z) (Q Z) (A Z) (eta Z)
    (Z ^ m) theta hg.1 htheta.le hg.2 hs.weight_nonneg hs.norm_lower hs.phase_bound
    (fun j hj i hi => (hs.target_unit j hj i hi).le) hs.mass_pos).trans hM

/-- Original complete-product FFR3 consumer. The full physical bound on the
returned signal is still displayed, and must be independently supplied by FFR4. -/
theorem signal_power_bound_of_principal_response {κ ι : Type*}
    (chi : Character) (H : ℂ → ℂ)
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
    ∃ C ≥ 0, ∀ Z, 0 < Z → ‖signal chi H c Z‖ ≤ C * Z ^ (theta + c) := by
  exact signal_power_bound_of_eventual_response chi H hH hb c theta (1 / 2)
    (by norm_num) (by norm_num) _
    (principal_response_eventually_contracts K S T w Q A eta m theta hm htheta hslot) hr

end SevenEighths.PrincipalResponseInversion
end
end OAI

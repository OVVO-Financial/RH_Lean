import OAI.NumberTheory.DirichletL.Reflection.LowExponent
import OAI.NumberTheory.DirichletL.Reflection.TupleDyads
import OAI.NumberTheory.DirichletL.Detector.LowNominalGeometry
import OAI.NumberTheory.DirichletL.ParametersHighDataFine
import OAI.NumberTheory.DirichletL.Detector.GlobalRegion
import OAI.NumberTheory.DirichletL.Hecke.SignalIdentity
import OAI.NumberTheory.DirichletL.PrincipalSignalComparison
import OAI.NumberTheory.DirichletL.Detector.PrincipalRemainderBounds
import OAI.NumberTheory.DirichletL.Detector.PrincipalPhysical
import OAI.NumberTheory.DirichletL.Reflection.LowSector

/-!
# A finite-slot gap in the actual reflected low exponent

The continuous scalar relaxation permits arbitrarily small positive selected
length. A fixed finite source with positive slot lengths does not. The theorem
below retains the original reflected exponent and proves a sufficient gate
that uses this distinction, uniformly over the surviving reflected dyads.

The source-facing theorem keeps the original ideals, optional pools, frozen
branches, masks and retained-width hypotheses. Its physical exponent is
generalized from 5/6 to S and its total slot length from 1/6 to L. The actual
correction function, principal normalization and conditional continuation
theorem are also generalized. No endpoint below seven eighths is asserted:
the complete perturbed low/high probe estimates remain to be reconstructed.
-/

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.RHLeanFiniteSlotGap

open InverseTerminalWidths SevenEighths.ProbeLowReflected


/-- Small epsilon and e already follow from every HighData record; no extra
constructor hypothesis is needed. -/
theorem high_data_small_errors {Delta : ℝ} (D : Parameters.HighData Delta) :
    D.ε ≤ D.t / 2000 ∧ D.e ≤ D.t / 2000 ∧
      D.e ≤ ((7 / 8 : ℝ) * D.rmin) / 4 := by
  have hslot := D.slots_bounds ⟨0, D.slots_pos⟩
  have hrsmall : D.rmin ≤ (1 / 2000 : ℝ) := by
    linarith only [hslot.2.1, hslot.2.2, D.t_small]
  have hp := mul_le_mul_of_nonneg_right hrsmall D.t_pos.le
  have hepsilon : D.ε ≤ D.t / 2000 := by
    nlinarith only [D.epsilon_gap, hp]
  have heepsilon : D.e ≤ D.ε := by
    linarith only [D.detector_budget, D.e_pos, D.kappa_pos, D.cost_pos]
  have htell : D.t ≤ (7 / 32 : ℝ) := by linarith only [D.t_small]
  have hrt := mul_le_mul_of_nonneg_left htell D.rmin_pos.le
  exact ⟨hepsilon, heepsilon.trans hepsilon, by
    nlinarith only [heepsilon, D.epsilon_gap, hrt]⟩

/-- Decrease only the two allowances needed for an explicit central reserve.
The slot list, its positive minimum and its fineness remain unchanged. -/
def cappedHighData {Delta : ℝ} (D : Parameters.HighData Delta) :
    Parameters.HighData Delta := by
  let eps := min D.eps (D.t / ((D.N : ℝ) + 8))
  let sigma := min D.sigma (((7 / 8 : ℝ) * D.rmin) / 4)
  have hepspos : 0 < eps :=
    lt_min D.eps_pos (div_pos D.t_pos (by positivity))
  have hepsle : eps ≤ D.eps := min_le_left _ _
  have hspos : 0 < sigma :=
    lt_min D.sigma_pos (div_pos (mul_pos (by norm_num) D.rmin_pos) (by norm_num))
  have hsle : sigma ≤ D.sigma := min_le_left _ _
  have hepsN := mul_le_mul_of_nonneg_left hepsle
    (show 0 ≤ (D.N : ℝ) + 8 by positivity)
  exact {
    D with
    eps := eps
    sigma := sigma
    eps_pos := hepspos
    eps_small := hepsle.trans D.eps_small
    sigma_pos := hspos
    central_budget := by linarith only [D.central_budget, hepsN]
    geometric_budget := by linarith only [D.geometric_budget, hsle]
    principal_budget := by linarith only [D.principal_budget, hsle]
    window_budget := by linarith only [D.window_budget, hsle]
    floor_budget := by linarith only [D.floor_budget, hepsN, hsle]
    high_saving := by linarith only [D.high_saving, hsle]
    height_choice := by
      intro J hJ
      obtain ⟨tau, htau, hd, hc, ht, hJcost, hepscost⟩ := D.height_choice J hJ
      refine ⟨tau, htau, hd, hc, ht, hJcost, ?_⟩
      exact (mul_le_mul_of_nonneg_left
        (show 2 + 4 * eps ≤ 2 + 4 * D.eps by linarith only [hepsle])
        htau.le).trans_lt hepscost
  }

theorem capped_high_data_geometry {Delta : ℝ} (D : Parameters.HighData Delta) :
    (cappedHighData D).t = D.t ∧
      (cappedHighData D).N = D.N ∧
      (cappedHighData D).ell = D.ell ∧
      (cappedHighData D).rmin = D.rmin := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- All the additional reserve bounds hold for the capped record. -/
theorem capped_high_data_bounds {Delta : ℝ} (D : Parameters.HighData Delta) :
    let E := cappedHighData D
    E.ε ≤ E.t / 2000 ∧ E.e ≤ E.t / 2000 ∧
      ((E.N : ℝ) + 8) * E.eps ≤ E.t ∧
      E.sigma ≤ ((7 / 8 : ℝ) * E.rmin) / 4 ∧
      E.e ≤ ((7 / 8 : ℝ) * E.rmin) / 4 := by
  have hs := high_data_small_errors D
  have hep : min D.eps (D.t / ((D.N : ℝ) + 8)) *
      ((D.N : ℝ) + 8) ≤ D.t :=
    (le_div_iff₀ (show 0 < (D.N : ℝ) + 8 by positivity)).mp (min_le_right _ _)
  change D.ε ≤ D.t / 2000 ∧ D.e ≤ D.t / 2000 ∧
    ((D.N : ℝ) + 8) * min D.eps (D.t / ((D.N : ℝ) + 8)) ≤ D.t ∧
    min D.sigma (((7 / 8 : ℝ) * D.rmin) / 4) ≤ ((7 / 8 : ℝ) * D.rmin) / 4 ∧
    D.e ≤ ((7 / 8 : ℝ) * D.rmin) / 4
  exact ⟨hs.1, hs.2.1, by simpa only [mul_comm] using hep,
    min_le_right _ _, hs.2.2⟩

/-- The central reserve depends only on these explicit small-error bounds,
so it can be consumed from an existential chosen-data witness directly. -/
theorem high_data_central_cost_of_bounds {Delta : ℝ} (D : Parameters.HighData Delta)
    (hepsilon : D.ε ≤ D.t / 2000) (he : D.e ≤ D.t / 2000)
    (heps : ((D.N : ℝ) + 8) * D.eps ≤ D.t) :
    (13 / 16) * (159 * D.ε + D.t + D.t + 7 * D.t) +
      2 * D.t + (3 / 2) * (2 * D.t) +
      (26 * D.e + ((D.N : ℝ) + 8) * D.eps + D.t + D.t / 6) +
      (D.t + D.t + D.t) ≤ 18 * D.t := by
  linarith only [hepsilon, he, heps, D.t_pos]

/-- Explicit reserve for the original high central consumer before its saving
parameter. No unused slack is inferred from the stored central_budget. -/
theorem capped_high_data_central_cost {Delta : ℝ} (D : Parameters.HighData Delta) :
    let E := cappedHighData D
    (13 / 16) * (159 * E.ε + E.t + E.t + 7 * E.t) +
      2 * E.t + (3 / 2) * (2 * E.t) +
      (26 * E.e + ((E.N : ℝ) + 8) * E.eps + E.t + E.t / 6) +
      (E.t + E.t + E.t) ≤ 18 * E.t := by
  have hs := capped_high_data_bounds D
  dsimp only at hs ⊢
  exact high_data_central_cost_of_bounds (cappedHighData D) hs.1 hs.2.1 hs.2.2.1

theorem capped_high_data_central_reserve {Delta : ℝ} (D : Parameters.HighData Delta) :
    let E := cappedHighData D
    (13 / 16) * (159 * E.ε + E.t + E.t + 7 * E.t) +
      2 * E.t + (3 / 2) * (2 * E.t) +
      (26 * E.e + ((E.N : ℝ) + 8) * E.eps + E.t + E.t / 6) +
      (E.t + E.t + E.t) + 49 / 881280 ≤ 49 / 440640 := by
  have hc := capped_high_data_central_cost D
  dsimp only at hc ⊢
  linarith only [hc, (cappedHighData D).t_small]

/-- The fixed positive auxiliary Delta can be paid together with the outer
central costs using the existing high_saving and t_small fields. -/
theorem fixed_delta_target_payment {Delta : ℝ} (D : Parameters.HighData Delta) :
    (1 / 1000000 : ℝ) + D.sigma + D.t / 8 + D.t / 8 ≤ 49 / 881280 := by
  linarith only [D.high_saving, D.t_small]

/-- The same fixed data pays for the wider 21/25 principal window. -/
theorem capped_high_data_window {Delta : ℝ} (D : Parameters.HighData Delta) :
    let E := cappedHighData D
    E.sigma + E.e < (21 / 25) * ((7 / 8 : ℝ) * E.rmin) := by
  have hs := capped_high_data_bounds D
  dsimp only at hs ⊢
  linarith only [hs.2.2.2.1, hs.2.2.2.2, (cappedHighData D).rmin_pos]


/-- Existence with any prescribed positive fine mesh and the explicit
reserve bounds; the old constructor is reused without changing the slots. -/
theorem exists_fine_high_data_with_reserve (Delta : ℝ) (hDelta : 0 < Delta)
    (mesh : ℝ → ℝ) (hmesh : ∀ t : ℝ, 0 < t → 0 < mesh t) :
    ∃ D : Parameters.HighData Delta,
      (∀ j, D.ell j ≤ mesh D.t / 200) ∧
      D.ε ≤ D.t / 2000 ∧ D.e ≤ D.t / 2000 ∧
      ((D.N : ℝ) + 8) * D.eps ≤ D.t ∧
      D.sigma ≤ ((7 / 8 : ℝ) * D.rmin) / 4 ∧
      D.e ≤ ((7 / 8 : ℝ) * D.rmin) / 4 := by
  obtain ⟨D, hfine⟩ := Parameters.exists_high_data_fine Delta hDelta mesh hmesh
  exact ⟨cappedHighData D, hfine, capped_high_data_bounds D⟩

/-- A positive physical perturbation chosen before the character. Its
smallness preserves the original principal contour domains in the candidate
contradiction range as well as the finite-slot, Gram and large-tail gates. -/
theorem source_gain_budgets {Delta : ℝ} (D : Parameters.HighData Delta) :
    let delta := D.e / 48
    0 < delta ∧
      24 * delta < (7 / 8 : ℝ) * D.rmin ∧
      delta < 1 / 960 ∧
      24 * delta < D.t ∧
      ∀ beta : ℝ, 7 / 8 - delta ≤ beta → 7 / 8 < beta + D.e := by
  have hs := high_data_small_errors D
  dsimp only
  refine ⟨div_pos D.e_pos (by norm_num), ?_, ?_, ?_, ?_⟩
  · linarith only [hs.2.2, D.rmin_pos]
  · linarith only [D.e_small]
  · linarith only [hs.2.1, D.t_pos]
  · intro beta hbeta
    linarith only [hbeta, D.e_pos]

/-- Zero actual slot width is a full-hybrid branch, even if the nominal
selected length contains a small positive padding. -/
lemma hybridSaving_zero {v : ℝ} (hv : 0 ≤ v) :
    hybridSaving v 0 = 0 := by
  unfold hybridSaving
  rw [add_zero, min_eq_left (div_nonneg hv (by norm_num)), min_eq_right hv]

/-- Every nonempty selection of fixed positive slots retains at least one
whole slot. This is the restriction lost by continuous scalar relaxation. -/
lemma finite_selected_mass_gap {ι : Type*} [DecidableEq ι]
    (ell : ι → ℝ) (ellMin : ℝ) (hmin : 0 < ellMin)
    (hell : ∀ i, ellMin ≤ ell i) (J : Finset ι) :
    J = ∅ ∨ ellMin ≤ ∑ i ∈ J, ell i := by
  by_cases hJ : J = ∅
  · exact Or.inl hJ
  · right
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hJ
    exact (hell i).trans
      (Finset.single_le_sum (fun j _ => hmin.le.trans (hell j)) hi)

/-- The original HighData source has the positive minimum required by the
finite-slot argument. This is a source restriction, not an added target bound. -/
lemma source_selected_mass_gap {Δ : ℝ} (D : Parameters.HighData Δ)
    (J : Finset (Fin D.N)) :
    Finset.univ \ J = ∅ ∨
      (7 / 8 : ℝ) * D.rmin ≤ ProbePhysical.lowSelectedLength D.ell J := by
  have h := finite_selected_mass_gap D.ell ((7 / 8 : ℝ) * D.rmin)
    (mul_pos (by norm_num) D.rmin_pos)
    (fun i => (D.slots_bounds i).2.1) (Finset.univ \ J)
  simpa only [ProbePhysical.lowSelectedLength, Finset.sum_coe_sort] using h

/-- The exact gate supplied by a positive finite slot family. The zero-width
hypothesis records the empty-product dyad identity; no arithmetic row or slot
coefficient is replaced. -/
lemma finite_slot_gate {ι : Type*} [DecidableEq ι]
    (ell : ι → ℝ) (J : Finset ι) (ellMin ell0 a v z : ℝ)
    (hmin : 0 < ellMin) (hell : ∀ i, ellMin ≤ ell i)
    (hselected : (∑ i ∈ J, ell i) ≤ ell0)
    (hgain : a ≤ ellMin) (hv : 0 ≤ v) (hempty : J = ∅ → z = 0) :
    hybridSaving v z = z ∨ a ≤ ell0 := by
  rcases finite_selected_mass_gap ell ellMin hmin hell J with hJ | hJ
  · left
    rw [hempty hJ]
    exact hybridSaving_zero hv
  · exact Or.inr (hgain.trans (hJ.trans hselected))

/-- Generalized reflected exponent, using the exact nonnegative surviving
widths. The loss is 38 eta / 3, versus the old caller's 200 eta.

The extra gate is satisfied either by zero actual selected width, or by a
positive selected mass at least 1 + 4 L - 2 S. Thus S may be slightly smaller
than 5/6 with L = 1/6, provided the fixed finite slot gap is retained. -/
theorem reflected_exponent_finite_slot_gap
    (S L d ell0 O H A N S0 B z v ell el theta eta : ℝ)
    (hSL : S + L ≤ 1) (_hL : L ≤ 1 / 3) (hd : 0 ≤ d) (heta : 0 ≤ eta)
    (hO : 0 ≤ O) (hH : H ≤ (S - 2 * d) - O + eta)
    (hA : 2 * A ≤ O + 3 * eta) (hN : 0 ≤ N) (hNA : N ≤ A)
    (hS0 : 0 ≤ S0) (hB : 0 ≤ B)
    (hell0 : ell0 ≤ L - d + eta) (hz : z ≤ ell0 + eta)
    (hv : 0 ≤ v) (hell : 0 ≤ ell) (hel : -eta ≤ el)
    (htheta : |theta| ≤ eta)
    (hgap : hybridSaving v z = z ∨ 1 + 4 * L - 2 * S ≤ ell0)
    (hret : v + 3 * ell + el ≤
      2 * H + 2 * A + 2 * z - 1 - ell0 - theta - N - 3 * B + 2 * eta) :
    reflectedExponent O H S0 B z v ell el
      (2 * H + 2 * A + 2 * z - 1 - ell0 - theta - N - 3 * B) ≤
        S - 2 * d + (38 / 3) * eta := by
  let Td := 2 * H + 2 * A + 2 * z - 1 - ell0 - theta - N - 3 * B
  have hthetaLo := (abs_le.mp htheta).1
  have hthetaHi := (abs_le.mp htheta).2
  have hTd : Td ≤ H - 3 * d + 8 * eta := by
    dsimp [Td]
    linarith
  have hcol : v + ell ≤ H + 11 * eta := by
    dsimp [Td] at hTd
    linarith
  have hmax : max H (v + ell) ≤ H + 11 * eta :=
    max_le (by linarith) hcol
  have hk := le_max_left 0 (Td - v - 3 * ell - el)
  change reflectedExponent O H S0 B z v ell el Td ≤ _
  by_cases hu : hybridSaving v z = z
  · unfold reflectedExponent
    rw [hu]
    linarith
  · have hlength := hgap.resolve_left hu
    have hhalf : v / 2 ≤ hybridSaving v z := by
      simpa using hybrid_half_with_error (show -(0 : ℝ) ≤ v by simpa using hv)
        (le_refl (0 : ℝ)) hu
    by_cases hrow : v + ell ≤ H
    · have hquarter := retained_kernel_quarter Td (v + 3 * ell + el)
      have heq : Td - (v + 3 * ell + el) = Td - v - 3 * ell - el := by ring
      rw [heq] at hquarter
      have hcharge : Td / 4 - 5 * eta / 12 ≤
          hybridSaving v z + ell + 2 * el / 3 +
            max 0 (Td - v - 3 * ell - el) / 2 := by
        linarith
      have hbound : reflectedExponent O H S0 B z v ell el Td ≤
          O / 2 + H - S0 - B + z - Td / 4 + 5 * eta / 12 := by
        unfold reflectedExponent
        rw [max_eq_left hrow]
        linarith
      have hpartial : reflectedExponent O H S0 B z v ell el Td ≤
          S - 2 * d + (1 + 4 * L - 2 * S - ell0) / 4 + 8 * eta / 3 := by
        apply hbound.trans
        dsimp [Td]
        linarith
      linarith
    · have hrow' : H ≤ v + ell := le_of_lt (lt_of_not_ge hrow)
      have hpartial : reflectedExponent O H S0 B z v ell el Td ≤
          S - 2 * d - 1 / 2 + 3 * L / 2 - 3 * d / 2 + 26 * eta / 3 := by
        unfold reflectedExponent
        rw [max_eq_right hrow']
        dsimp [Td] at hk ⊢
        linarith
      linarith

/-- Exact exponent accounting for equal perturbations of the two physical
lengths. This identity alone is not a complete detector estimate. -/
theorem equal_scale_perturbation (delta : ℝ) :
    let x := (17 / 48 : ℝ) - 6 * delta
    let y := (23 / 48 : ℝ) - 6 * delta
    let L := (1 / 6 : ℝ)
    (5 * x + y) / 12 - (-5 / 6 + x / 3 + L / 6) = 7 / 8 - delta ∧
      1 + 4 * L - 2 * (x + y) = 24 * delta := by
  dsimp
  constructor <;> ring

/-- A tilted perturbation has the same finite-slot charge and crossing as the
equal perturbation, while improving the high physical prefactor. -/
theorem tilted_scale_perturbation (delta : ℝ) :
    let x := (17 / 48 : ℝ) - 24 * delta
    let y := (23 / 48 : ℝ) + 12 * delta
    let L := (1 / 6 : ℝ)
    (5 * x + y) / 12 = 3 / 16 - 9 * delta ∧
      -5 / 6 + x / 3 + L / 6 = -11 / 16 - 8 * delta ∧
      (5 * x + y) / 12 - (-5 / 6 + x / 3 + L / 6) = 7 / 8 - delta ∧
      1 + 4 * L - 2 * (x + y) = 24 * delta ∧
      2 * x - y - L = 1 / 16 - 60 * delta ∧
      1 - x + L = 13 / 16 + 24 * delta := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

/-- The exact change of the high physical exponent. After paying the nine
delta movement of the lowest target signal, at least 24 delta / 25 remains.
This is a prefactor estimate, not a bound for the complete high probe. -/
theorem tilted_central_prefactor_margin (delta a e : ℝ)
    (hdelta : 0 ≤ delta) (ha : 51 / 100 ≤ a) (he : 0 ≤ e) :
    (((17 / 48 : ℝ) - 24 * delta) * (4 / 25) +
        a + 16 * e - 33 / 50 +
        ((23 / 48 : ℝ) + 12 * delta) * (-a - 6 * e)) -
      ((17 / 48 : ℝ) * (4 / 25) + a + 16 * e - 33 / 50 +
        (23 / 48 : ℝ) * (-a - 6 * e)) + 9 * delta ≤
      -(24 / 25) * delta := by
  have hcoef : 249 / 25 ≤ 96 / 25 + 12 * a + 72 * e := by linarith
  have hmul := mul_le_mul_of_nonneg_right hcoef hdelta
  nlinarith only [hmul]

end SevenEighths.RHLeanFiniteSlotGap

namespace SevenEighths.InverseReflectedPhase
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic
  CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
local notation "Eis" => ActualEisensteinCubic.O
variable {a c₀ : Eis} {mode : Bool}

/-- A nonempty dyad on an empty active slot type has scale exactly one.
Consequently the actual logarithmic slot width used by LowFixedMember is zero. -/
theorem empty_active_tuple_dyad_width {σ : Type*} [Fintype σ] [DecidableEq σ]
    [IsEmpty σ] (tuples : Finset (σ → Ideal Eis)) (H Z : ℝ)
    (hn : ∀ p ∈ tuples, 1 ≤ (Ideal.absNorm (slotTupleProduct p) : ℝ) ∧
      (Ideal.absNorm (slotTupleProduct p) : ℝ) ≤ H)
    (i : Fin (columnDyadicLength H + 1))
    (hi : (activeTupleDyad tuples H i).Nonempty) :
    Real.logb Z ((2 * divisorDyadicScale i.val) / 2) = 0 := by
  obtain ⟨p, hp⟩ := hi
  have hs := (activeTupleDyad_bounds tuples H hn i p hp).1
  have hprod : slotTupleProduct p = 1 := by simp [slotTupleProduct]
  rw [hprod, map_one, Nat.cast_one] at hs
  have he : divisorDyadicScale i.val = 1 :=
    le_antisymm hs (divisorDyadicScale_ge_one i.val)
  rw [he]
  norm_num

theorem surviving_low_exponent_finite_slot_gap
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (kK kP η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hη : 0<η) :
    ∃ Z₀ : ℝ,1<Z₀ ∧
    ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀)) (e : A→Fin 3) (column : Ideal Eis→Ideal Eis→ℂ)
      (Z S L O₀ H za Nstar d ell0 shift δ π Ck CO CH X QK QP ε Lscale Lrow Lslot : ℝ) (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^(S-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      S+L≤1 → L≤1/3 → 0≤d → ell0≤L-d+η → 0≤O₀ → za≤ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z (kK*QK) → za=Real.logb Z (kP*QP) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → 0≤ε → (kK*QK)≤Z^Lrow → (kP*QP)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ) →
      e∈survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1) →
      let v := Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))
      let ell := Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))
      (hybridSaving v za=za ∨ 1+4*L-2*S≤ell0) →
      InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
        (normWidth Z (frozenExtracted G j e 2)) za v ell (ramifiedWidth Z i.1)
        (terminalDualWidth Z H za Nstar G.ideal j e)+ε*(H+v+ell+za)+η/2+O₀/2≤
      (S-2*d)+(38/3)*η+π := by
  obtain ⟨Z₀,hZ₀,hgates⟩ := actual_surviving_retained_gates s hc₀ kK kP η hkK hkP hη
  refine ⟨Z₀,hZ₀,?_⟩
  intro J I F Q Q₀ hJ hI hQ hpower hmask A e column
    Z S L O₀ H za Nstar d ell0 shift δ π Ck CO CH X QK QP ε Lscale Lrow Lslot i
    hZ hCk hCO hCH hX hK hP hIn hPow hRow hlog hPowUpper hQwidth hSL hL hd hell0 hO hza hshift
    hNs heH heza heN hδ hδη hε hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscale hret hsurv hgap
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hpair := (poolPrimeFamily J Q Q₀).restrict_pairwise (poolPrimeFamily_pairwise J Q Q₀) A
  obtain ⟨hv,hell,hel,hwidth⟩ := hgates G hpair j column e Z X QK QP δ i hZ hX hK hP hret hsurv
  rw [←heH,←heza,←heN] at hwidth
  have hH := physical_residual_width I Q hI Z (S-2*d) O₀ H Ck CO CH hz hCk hCO hCH hIn hPow hRow
  have hA := original_optional_powerful_width J I Q Q₀ hJ hI hQ hpower hmask A Z hz
  have hN0 := normWidth_nonneg Z hz _ (frozenExtracted_ne_zero G j e 1)
  have hS0 := normWidth_nonneg Z hz _ (frozenExtracted_ne_zero G j e 0)
  have hB0 := normWidth_nonneg Z hz _ (frozenExtracted_ne_zero G j e 2)
  have hNA := frozenExtracted_width_le G j e 1 Z hz
  have ht := RHLeanFiniteSlotGap.reflected_exponent_finite_slot_gap S L d ell0 O₀ H
    (normWidth Z (∏ b,G.ideal b)) (normWidth Z (frozenExtracted G j e 1))
    (normWidth Z (frozenExtracted G j e 0)) (normWidth Z (frozenExtracted G j e 2)) za
    (Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1)))
    (Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2)))
    (ramifiedWidth Z i.1) shift η
    hSL hL hd hη.le hO (by linarith) (by linarith)
    hN0 hNA hS0 hB0 hell0 hza hv hell hel hshift hgap ?_
  · have hb := retained_extracted_log_budget (familyRawScale G s X QK QP) Z δ Lscale Lrow Lslot η
      (kK*QK) (kP*QP) (familyRawScale_pos G s hc₀ X QK QP hX hK hP) hz
      (mul_pos hkK hK) (mul_pos hkP hP) hscale hconst hrowcap hslotcap i hret
      (frozenExtracted G j e 1) (frozenExtracted G j e 2)
      (frozenExtracted_ne_zero G j e 1) (frozenExtracted_ne_zero G j e 2)
    rw [←heH,←heza] at hb
    have hb' := mul_le_mul_of_nonneg_left hb hε
    have hTd : terminalDualWidth Z H za Nstar G.ideal j e=
        2*H+2*normWidth Z (∏ b,G.ideal b)+2*za-1-ell0-shift-
          normWidth Z (frozenExtracted G j e 1)-3*normWidth Z (frozenExtracted G j e 2) := by
      unfold terminalDualWidth
      rw [hNs,←frozenExtracted_eq_ideal,←frozenExtracted_eq_ideal]
      ring
    change InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
      (normWidth Z (frozenExtracted G j e 2)) za _ _ _ _+_+_+_≤_
    rw [hTd]
    unfold InverseTerminalWidths.reflectedExponent at ht ⊢
    linarith
  · dsimp only [terminalDualWidth] at hwidth
    rw [hNs,←frozenExtracted_eq_ideal,←frozenExtracted_eq_ideal] at hwidth
    linarith
end SevenEighths.InverseReflectedPhase

namespace SevenEighths.InverseReflectedPhase
open scoped ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic
  CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

/-- Sum the actual surviving branch powers with the finite-slot source gate.
The retained-dyad padding remains separate from the physical exponent. -/
theorem surviving_low_energy_sum_finite_slot_gap
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (ρ : ℝ) (hρ : 0<ρ) (kK kP η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hηpos : 0<η) :
    ∃ Z₀ C : ℝ, 1<Z₀ ∧ 0<C ∧
    ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (column : Ideal Eis→Ideal Eis→ℂ)
      (Z Sphys Ltot O₀ H za Nstar d ell0 shift retainedDelta π Ck CO CH X QK QP ε Lscale Lrow Lslot : ℝ) (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^(Sphys-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      Sphys+Ltot≤1 → Ltot≤1/3 → 0≤d → ell0≤Ltot-d+η → 0≤O₀ → za≤ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z (kK*QK) → za=Real.logb Z (kP*QP) → Nstar=Real.logb Z X →
      0≤retainedDelta → retainedDelta≤η → 0≤ε → (kK*QK)≤Z^Lrow → (kP*QP)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(retainedDelta+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^retainedDelta) →
      (za=0 ∨ 1+4*Ltot-2*Sphys≤ell0) →
      let branches := survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
      ((branches.card:ℝ)*∑ e∈branches,
        Z^(InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
          (normWidth Z (frozenExtracted G j e 2)) za
          (Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1)))
          (Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2)))
          (ramifiedWidth Z i.1) (terminalDualWidth Z H za Nstar G.ideal j e)+
          ε*(H+Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))+
            Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))+za)+η/2))≤
        C*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^((Sphys-2*d)+(38/3)*η+π-O₀/2) := by
  obtain ⟨Z₀,hZ₀,hsave⟩ := surviving_low_exponent_finite_slot_gap s hc₀ kK kP η hkK hkP hηpos
  obtain ⟨C,hC,hcount⟩ := surviving_branch_count_small_power ρ hρ
  refine ⟨Z₀,C,hZ₀,hC,?_⟩
  intro J I F Q Q₀ hJ hI hQ hpower hmask A column
    Z Sphys Ltot O₀ H za Nstar d ell0 shift retainedDelta π Ck CO CH X QK QP ε Lscale Lrow Lslot i
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hSL hLtot hd hell0 hO hzcap hshift
    hNs heH heza heN hretainedDelta hretainedDeltaη hε hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hret hgate
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  let branches := survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
  have hcbr := hcount G ((poolPrimeFamily J Q Q₀).restrict_pairwise
    (poolPrimeFamily_pairwise J Q Q₀) A) j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
  have hz' : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hpair := (poolPrimeFamily J Q Q₀).restrict_pairwise
    (poolPrimeFamily_pairwise J Q Q₀) A
  have hhybrid (e : A→Fin 3) (he : e∈branches) :
      hybridSaving (Real.logb Z (((2:ℝ)^i.2.2)/
        Ideal.absNorm (frozenExtracted G j e 1))) za = za ∨
        1+4*Ltot-2*Sphys≤ell0 := by
    rcases hgate with hz0 | hmass
    · have hnorm := surviving_forced_norms G hpair j column
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
        ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)
        (fun n hn => ⟨(reflectedNDyad_bounds _ n hn).1.2,
          (reflectedNDyad_bounds _ n hn).2.2⟩)
        (fun b hb => ⟨(reflectedBDyad_bounds _ b hb).1,
          (reflectedBDyad_bounds _ b hb).2.2⟩) e he
      have hp : (0:ℝ)<Ideal.absNorm (frozenExtracted G j e 1) := by
        exact_mod_cast Nat.pos_of_ne_zero
          (Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero G j e 1))
      have hv : 0 ≤ Real.logb Z (((2:ℝ)^i.2.2)/
          Ideal.absNorm (frozenExtracted G j e 1)) :=
        Real.logb_nonneg hz' ((one_le_div hp).mpr hnorm.1)
      left
      rw [hz0]
      exact RHLeanFiniteSlotGap.hybridSaving_zero hv
    · exact Or.inr hmass
  have hb (e : A→Fin 3) (he : e∈branches) := hsave J I F Q Q₀ hJ hI hQ hpower hmask A e column
    Z Sphys Ltot O₀ H za Nstar d ell0 shift retainedDelta π Ck CO CH X QK QP ε Lscale Lrow Lslot i
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hSL hLtot hd hell0 hO hzcap hshift
    hNs heH heza heN hretainedDelta hretainedDeltaη hε hrowcap hslotcap hconst hbudget hscap hret he (hhybrid e he)
  calc
    _ ≤ (branches.card:ℝ)*∑ _e∈branches,Z^((Sphys-2*d)+(38/3)*η+π-O₀/2) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro e he
      apply Real.rpow_le_rpow_of_exponent_le hz'.le
      have hh := hb e he
      linarith
    _ = ((branches.card:ℝ)^2)*Z^((Sphys-2*d)+(38/3)*η+π-O₀/2) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcbr (Real.rpow_nonneg (lt_trans zero_lt_one hz').le _)

/-- Transport the sharper branch estimate to the original literal signed
reflected dyadic row. Constants precede the physical exponents, masks,
prime pools, retained branches, source weights and Mellin height. -/
theorem low_sector_literal_energy_finite_slot_gap
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z Sphys Ltot O₀ H za Nstar d ell0 shift retainedDelta π Ck CO CH X QK QP Lscale Lrow Lslot : ℝ)
      (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^(Sphys-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      Sphys+Ltot≤1 → Ltot≤1/3 → 0≤d → ell0≤Ltot-d+η → 0≤O₀ → za≤ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤retainedDelta → retainedDelta≤η → QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(retainedDelta+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^retainedDelta) →
      (za=0 ∨ 1+4*Ltot-2*Sphys≤ell0) →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (u : Eisˣ) (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalDyadicRow G K.val (hrows K.val K.property) S j Pset
        (E.completion K) s hc₀ u i W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^((Sphys-2*d)+(38/3)*η+π-O₀/2) := by
  obtain ⟨degree,C₀,Cs,Zs,hC₀,hCs,hZs,henergy⟩ := sector_normalized_literal_energy
    (N:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ η hηpos
  obtain ⟨Zb,Cb,hZb,hCb,hbranch⟩ := surviving_low_energy_sum_finite_slot_gap s hc₀ ρ hρ 1 (1/2) η
    (by norm_num) (by norm_num) hηpos
  let Kc := (Real.exp (Real.log 2/2+Real.log 2))^2*(6*Cs)
  have hKc : 0<Kc := by dsimp [Kc];positivity
  refine ⟨degree*2,Kc*Cb*C₀^2+1,max Zs Zb,by positivity,lt_of_lt_of_le hZs (le_max_left _ _),?_⟩
  intro σ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z Sphys Ltot O₀ H za Nstar d ell0 shift retainedDelta π Ck CO CH X QK QP Lscale Lrow Lslot i
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hSL hLtot hd hell0 hO hzcap hshift
    hNs heH heza heN hretainedDelta hretainedDeltaη hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hret hgate rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar u θ r aw hqk hqp hKr hPr hr haw
  have hzpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZs ((le_max_left _ _).trans hZ))
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hpair := (poolPrimeFamily J Q Q₀).restrict_pairwise (poolPrimeFamily_pairwise J Q Q₀) A
  have hj : ∀ b : A,j b<6 := by intro b;exact Nat.mod_lt _ (by norm_num)
  have hs := henergy Z ((le_max_left _ _).trans hZ) G j hNlevel hbase hac hpair hGN hGchar hj
    rows Pset S hrows E hrowcop hprod hScop hSN hSchar u i X θ QK QP r aw hX hqk hqp hKr hPr hr haw
  have hb := hbranch J I F Q Q₀ hJ hI hQ hpower hmask A (actualCuspColumn E.referenceArithmetic s hc₀ u i.1)
    Z Sphys Ltot O₀ H za Nstar d ell0 shift retainedDelta π Ck CO CH X QK QP ε Lscale Lrow Lslot i
    ((le_max_right _ _).trans hZ) hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hSL hLtot hd hell0 hO hzcap hshift hNs
    (by simpa only [one_mul] using heH) (by simpa only [one_div,mul_comm,mul_inv_rev,div_eq_mul_inv,one_mul] using heza)
    heN hretainedDelta hretainedDeltaη hε.le
    (by simpa only [one_mul] using hrowcap) (by simpa only [one_div,mul_comm,mul_inv_rev,div_eq_mul_inv,one_mul] using hslotcap)
    hconst hbudget hscap hret hgate
  dsimp only at hs hb
  rw [←heH,←heza,←heN] at hs
  simp_rw [←Finset.mul_sum] at hs
  apply hs.trans
  calc
    _ = Kc*((survivingFrozenBranches G j (actualCuspColumn E.referenceArithmetic s hc₀ u i.1)
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)).card*
      ∑ e∈survivingFrozenBranches G j (actualCuspColumn E.referenceArithmetic s hc₀ u i.1)
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1),
        Z^(InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
          (normWidth Z (frozenExtracted G j e 2)) za
          (Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1)))
          (Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2)))
          (ramifiedWidth Z i.1) (terminalDualWidth Z H za Nstar G.ideal j e)+
          ε*(H+Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))+
            Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))+za)+η/2))*(C₀*(1+‖θ‖)^degree)^2 := by dsimp [Kc,G,j];ring
    _ ≤ Kc*(Cb*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^((Sphys-2*d)+(38/3)*η+π-O₀/2))*(C₀*(1+‖θ‖)^degree)^2 := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hKc.le) (sq_nonneg _)
    _ = (Kc*Cb*C₀^2)*(1+‖θ‖)^(degree*2)*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^((Sphys-2*d)+(38/3)*η+π-O₀/2) := by rw [mul_pow,←pow_mul];ring
    _ ≤ _ := by gcongr;linarith

end SevenEighths.InverseReflectedPhase


namespace SevenEighths.ProbeEuler

/-- The same local Euler correction bound holds down to real part 21/25.
The summable majorant and its constant are unchanged. Full contour and
principal-source wrappers are not generalized by this local theorem. -/
theorem unramifiedClosed_open_region_bound_twenty_one_twenty_fifths (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : (21/25:ℝ) ≤ x.re) (hw : (9/10:ℝ) ≤ w.re) (hz : (4/25:ℝ) ≤ z.re) :
    ‖unramifiedClosed Q A eta v x w z - 1‖ ≤ 240 * Q ^ (-(17/10:ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  have hV : ‖V‖ ≤ Q ^ (-(24/25:ℝ)) := by
    rw [show V = coordV Q z from rfl, coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : ‖R‖ ≤ Q ^ (-(2:ℝ)) :=
    (coordR_norm_le Q hQ0 A x z hA).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hW : ‖W‖ ≤ Q ^ (-(9/10:ℝ)) :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hD : ‖D‖ ≤ Q ^ (-(21/25:ℝ)) :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hK : ‖K‖ ≤ Q ^ (-(37/50:ℝ)) :=
    (coordK_norm_le Q hQ1 eta x w heta).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hVh : ‖V‖ ≤ 1/2 := hV.trans (rpow_le_half Q _ hQ (by norm_num))
  have hRh : ‖R‖ ≤ 1/2 := hR.trans (rpow_le_half Q _ hQ (by norm_num))
  have hDh : ‖D‖ ≤ 1/2 := hD.trans (rpow_le_half Q _ hQ (by norm_num))
  have hWh : ‖W‖ ≤ 1 := by
    exact hW.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num : -(9/10:ℝ) ≤ 0)).trans_eq (Real.rpow_zero Q))
  have hqi : ‖(Q:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0, ← one_div]
    exact (div_le_one hQ0).mpr hQ1
  let T := Q ^ (-(17/10:ℝ))
  have hT : 0 ≤ T := Real.rpow_nonneg hQ0.le _
  have hRT : ‖R‖ ≤ T := hR.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num))
  have hprod (a b a' b' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (haa : a ≤ Q^a') (hbb : b ≤ Q^b') (he : a'+b' ≤ -(17/10:ℝ)) : a*b ≤ T := by
    calc
      a*b ≤ Q^a' * Q^b' := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _ = Q^(a'+b') := (Real.rpow_add hQ0 _ _).symm
      _ ≤ T := Real.rpow_le_rpow_of_exponent_le hQ1 he
  have hKV : ‖K‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV (by norm_num)
  have hDV : ‖D‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hV (by norm_num)
  have hDW : ‖D‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hW (by norm_num)
  have hVW : ‖V‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hV hW (by norm_num)
  have hDVW : ‖D‖*‖V‖*‖W‖ ≤ T :=
    (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hWh).trans hDV
  let P := markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1
  have hE : ‖P+D‖ ≤ 28*T := by
    have h := ProbeLocal.unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    have hrw : ‖R‖*(1+‖W‖) ≤ 2*T := by
      calc
        _ ≤ ‖R‖*2 := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
        _ ≤ _ := by nlinarith
    dsimp only [P]
    nlinarith
  have h := ProbeLocal.continuedCorrection_defect_bound V W D P hVh hDh
  change ‖ProbeLocal.continuedCorrection V W D P-1‖ ≤ 240*T
  have hWE : (1+‖W‖)*‖P+D‖ ≤ 56*T := by
    calc
      _ ≤ 2*(28*T) := mul_le_mul (by linarith) hE (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  nlinarith


end SevenEighths.ProbeEuler


namespace SevenEighths.ProbeEuler

lemma open_region_denominators_wide (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : 21/25≤x.re) (hz : 4/25≤z.re) :
    1-coordR Q A x z≠0 ∧ 1-coordV Q z≠0 ∧ 1-coordD Q eta v x≠0 := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  have hR : ‖coordR Q A x z‖≤1/2 := by
    apply (coordR_norm_le Q hQ0 A x z hA).trans
    apply rpow_le_half Q _ hQ
    linarith
  have hV : ‖coordV Q z‖≤1/2 := by
    rw [coordV_norm Q hQ0]
    apply rpow_le_half Q _ hQ
    linarith
  have hD : ‖coordD Q eta v x‖≤1/2 := by
    apply (coordD_norm_le Q hQ0 eta v x he hv).trans
    apply rpow_le_half Q _ hQ
    linarith
  exact ⟨ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hR,
    ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hV,ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hD⟩

theorem unramifiedClosed_analytic_x_wide (Q : ℝ) (A eta v w z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hz : 4/25≤z.re) :
    AnalyticOnNhd ℂ (fun x=>unramifiedClosed Q A eta v x w z) {x : ℂ|21/25<x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := open_region_denominators_wide Q A eta v x z hQ hA he hv hx.le hz
  exact (unramifiedClosed_differentiableAt Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt


end SevenEighths.ProbeEuler

namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ProbeEuler CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma idealClosedCorrection_bound_wide (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4≤Ideal.absNorm P.val) (x w z : ℂ)
    (hx : 21/25≤x.re) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    ‖idealClosedCorrection η P x w z-1‖≤globalPrimeDefectBound P := by
  apply unramifiedClosed_open_region_bound_twenty_one_twenty_fifths
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one η _
  · exact HeckeFamily.idealCoeff_norm_le_one η P.val
  · simp
  · exact hx
  · exact hw
  · exact hz

theorem globalClosedCorrection_bound_wide (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : 21/25≤x.re) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    ‖globalClosedCorrection η S x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P=>idealClosedCorrection_bound_wide η P.val (hS.norm_four P.val P.property) x w z hx hw hz)
    hS.half hS.small


theorem globalClosedCorrection_analytic_x_wide (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (w z : ℂ) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    AnalyticOnNhd ℂ (fun x=>globalClosedCorrection η S x w z) {x : ℂ|21/25<x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply unramifiedClosed_analytic_x_wide
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hz
  · intro P x hx
    exact idealClosedCorrection_bound_wide η P.val (hS.norm_four P.val P.property) x w z hx.le hw hz
  · exact hS.half


end SevenEighths.ProbePhysical

namespace SevenEighths.PrincipalSignalComparison
open HeckeFamily ProbePhysical

/-- The actual original correction has the wider analytic domain, with the
same exclusions and summable prime tail. -/
theorem sourceCorrection_analytic_wide (eta : Character)
    (E : Finset (Ideal HeckeFamily.O)) (hE : SourceExclusions E) :
    AnalyticOnNhd ℂ (sourceCorrection eta E) {s : ℂ | 21 / 25 < s.re} :=
  globalClosedCorrection_analytic_x_wide eta E hE.tail 1 (1 / 6)
    (by norm_num) (by norm_num)

theorem sourceCorrection_bound_wide (eta : Character)
    (E : Finset (Ideal HeckeFamily.O)) (hE : SourceExclusions E)
    (s : ℂ) (hs : 21 / 25 < s.re) :
    ‖sourceCorrection eta E s - 1‖ ≤ 1 / 2 :=
  globalClosedCorrection_bound_wide eta E hE.tail s 1 (1 / 6)
    hs.le (by norm_num) (by norm_num)


open PrincipalMellinResidues
variable {κ ι : Type*}

/-- Exact normalization for an arbitrary first physical exponent. The new
signal shift comes from this source identity, not from relabeling an exponent. -/
theorem source_power_identity_variable_x {Z : ℝ} (hZ : 0 < Z) (x : ℝ) (s : ℂ) :
    ((Z^x : ℝ) : ℂ)^(1/3 : ℂ) * (Z : ℂ)^(s-5/6) =
      (Z : ℂ)^(((-(1/6 : ℝ)/6 : ℝ) : ℂ)) * (Z : ℂ)^(s + ((x/3 - 5/6 + 1/36 : ℝ) : ℂ)) := by
  have hz : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  rw [← Complex.cpow_mul_ofReal_nonneg hZ.le x (1/3),
    ← Complex.cpow_add _ _ hz, ← Complex.cpow_add _ _ hz]
  congr 1
  push_cast
  ring_nf


theorem normalized_source_double_residue_variable_x (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (χ : Character)
    (x Y Z : ℝ) (hZ : 0 < Z) (s : ℂ) (H B : ℂ → ℂ → ℂ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hB : B 1 (1/6) = slotProduct S T w Q A η s) :
    (fixedPrincipalResidue M ^ 2 / 6 *
      sourceMultiplier W0 W1 (Z^x) Y Z χ s H B 1 (1/6)) /
        (sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z (1/6) (slotMass T w) : ℂ)) =
      (Z : ℂ)^(s + ((x/3 - 5/6 + 1/36 : ℝ) : ℂ)) * Complex.exp ((s-5/6)^2) * H 1 (1/6) / LFunction χ s *
        slotRatio S T w Q A η s := by
  rw [source_double_residue, source_normalizer_cast S T w hZ, hB]
  have hp := source_power_identity_variable_x hZ x s
  have hz : (Z : ℂ)^(((-(1/6 : ℝ)/6 : ℝ) : ℂ)) ≠ 0 :=
    (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [hZ.ne'])
  rw [hp]
  simp only [slotRatio, div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (sourceResidueConstant W0 W1 M * (sourceResidueConstant W0 W1 M)⁻¹) *
        ((Z : ℂ)^(((-(1/6 : ℝ)/6 : ℝ) : ℂ)) *
          ((Z : ℂ)^(((-(1/6 : ℝ)/6 : ℝ) : ℂ)))⁻¹) *
        ((Z : ℂ)^(s + ((x/3 - 5/6 + 1/36 : ℝ) : ℂ)) * Complex.exp ((s-5/6)^2) * H 1 (1/6) *
          (LFunction χ s)⁻¹ * (slotProduct S T w Q A η s *
            (PrincipalSlotEstimate.principalScalar S (slotMass T w))⁻¹)) := by ring_nf
    _ = _ := by rw [mul_inv_cancel₀ hc, mul_inv_cancel₀ hz]; ring_nf


end SevenEighths.PrincipalSignalComparison


namespace SevenEighths.ProbePrincipalRemainderBounds

open Complex Set MeasureTheory Filter
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal ActualEisensteinCubic.O

/-- Exact physical scaling for the original remainder integrals, with the
first and second physical exponents left free. -/
lemma source_scale_identity_variable_xy {ι : Type*} (J : Finset ι) (ell : ι → ℝ)
    (hell : ∑ j ∈ J, ell j = 1 / 6) (Z a ξ υ x y : ℝ) (hZ : 0 < Z) :
    scalePower (Z ^ x) (Z ^ y) Z a ξ υ *
      (∏ j ∈ J, (Z ^ (ell j)) ^ ξ) =
    Z ^ (a + (x / 3 - 5 / 6 + 1 / 36) +
      (7 / 6 - x) * (ξ - 1 / 6) + y * (υ - 1)) := by
  have hp : (∏ j ∈ J, (Z ^ (ell j)) ^ ξ) = Z ^ ((1 / 6) * ξ) := by
    simp only [← Real.rpow_mul hZ.le]
    rw [← Real.rpow_sum_of_pos hZ, ← Finset.sum_mul, hell]
  rw [hp, scalePower, ← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le]
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  ring

lemma source_w_scale_identity_tilted {ι : Type*} (J : Finset ι) (ell : ι → ℝ)
    (hell : ∑ j ∈ J, ell j = 1 / 6) (Z a e physicalDelta : ℝ) (hZ : 0 < Z) :
    scalePower (Z ^ (17 / 48 - 24 * physicalDelta))
      (Z ^ (23 / 48 + 12 * physicalDelta)) Z a (1 / 6 + e) (19 / 20) *
      (∏ j ∈ J, (Z ^ (ell j)) ^ (1 / 6 + e)) =
    Z ^ (a - 11 / 16 - 8 * physicalDelta + (13 / 16) * e - 23 / 960 +
      physicalDelta * (24 * e - 3 / 5)) := by
  rw [source_scale_identity_variable_xy J ell hell Z a (1 / 6 + e) (19 / 20)
    (17 / 48 - 24 * physicalDelta) (23 / 48 + 12 * physicalDelta) hZ]
  congr 1
  ring

lemma source_z_scale_identity_tilted {ι : Type*} (J : Finset ι) (ell : ι → ℝ)
    (hell : ∑ j ∈ J, ell j = 1 / 6) (Z a physicalDelta : ℝ) (hZ : 0 < Z) :
    scalePower (Z ^ (17 / 48 - 24 * physicalDelta))
      (Z ^ (23 / 48 + 12 * physicalDelta)) Z a (33 / 200) 1 *
      (∏ j ∈ J, (Z ^ (ell j)) ^ (33 / 200 : ℝ)) =
    Z ^ (a - 11 / 16 - 8 * physicalDelta - 13 / 9600 - physicalDelta / 25) := by
  rw [source_scale_identity_variable_xy J ell hell Z a (33 / 200) 1
    (17 / 48 - 24 * physicalDelta) (23 / 48 + 12 * physicalDelta) hZ]
  congr 1
  ring

/-- The two actual principal remainder integrals keep the original strict
saving under every nonnegative physical tilt, with one constant chosen
before the tilt, slot exponents, window weights and prime pools. The original
contours and source multiplier are retained. Division by the outer source
normalizer is a separate step with its own arbitrary positive allowance. -/
theorem source_remainders_strict_saving_tilted {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0 < c) (hd : c ≤ d) (hB : 0 ≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (e : ℝ) (he : 0 < e) (hehi : e ≤ 1 / 1000)
    (ha : HeckeZeroSupremum.beta + e ∈ Icc (7 / 8 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ physicalDelta : ℝ, 0 ≤ physicalDelta →
    ∀ ell : ι → ℝ, (∑ j ∈ J, ell j = 1 / 6) → ∀ W : ι → ℝ → ℝ,
    (∀ j ∈ J, ∀ x, 0 ≤ W j x ∧ W j x ≤ B) →
    (∀ j ∈ J, Function.support (W j) ⊆ Icc c d) → ∀ T : ι → Finset PrimeIdeal,
    (∀ j ∈ J, ∀ p ∈ T j, p.val ∉ S) → ∀ Z : ℝ, 1 ≤ Z →
    (∀ j ∈ J, 480 ≤ c * Z ^ (ell j)) →
    (∀ j ∈ J, (Ideal.absNorm η.modulus : ℝ) < c * Z ^ (ell j)) →
    let K0 := fun s => sourceMultiplier W0 W1
      (Z ^ (17 / 48 - 24 * physicalDelta)) (Z ^ (23 / 48 + 12 * physicalDelta)) Z
      (η.excludePrimes S hS.prime) s (globalClosedCorrection η S s)
      (windowMultiplier η J T (fun j x => (W j x : ℂ)) (fun j => Z ^ (ell j)) s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral (HeckeZeroSupremum.beta + e)
      (fun s => verticalIntegral (1 / 6 + e) (fun z => verticalIntegral (19 / 20)
        (fun w => K0 s w z * LFunction π (6 * z) * LFunction π w)))‖ ≤
      C / e * Z ^ (HeckeZeroSupremum.beta - 11 / 16 - 8 * physicalDelta - 17 / 48000)) ∧
    (‖HeckeReciprocal.regularizedL π 1 *
      verticalIntegral (HeckeZeroSupremum.beta + e)
        (fun s => verticalIntegral (33 / 200) (fun z => K0 s 1 z * LFunction π (6 * z)))‖ ≤
      C * Z ^ (HeckeZeroSupremum.beta - 11 / 16 - 8 * physicalDelta - 17 / 48000)) := by
  obtain ⟨C, hC, hbound⟩ := ordered_remainders_scale_bound η S hS J c d B hc hd hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 (HeckeZeroSupremum.beta + e) e ha
    (by linarith only [he]) he (by linarith only [hehi])
  refine ⟨C, hC, ?_⟩
  intro physicalDelta hDelta ell hell W hW hsupp T hT Z hZ hthreshold hmod
  dsimp only
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hh := hbound W hW hsupp (fun j => Z ^ (ell j))
    (fun _ _ => Real.rpow_pos_of_pos hZpos _) hthreshold hmod T hT
    (Z ^ (17 / 48 - 24 * physicalDelta)) (Z ^ (23 / 48 + 12 * physicalDelta)) Z
    (Real.rpow_pos_of_pos hZpos _) (Real.rpow_pos_of_pos hZpos _) hZpos
  dsimp only at hh
  rw [source_w_scale_identity_tilted J ell hell Z (HeckeZeroSupremum.beta + e) e
      physicalDelta hZpos,
    source_z_scale_identity_tilted J ell hell Z (HeckeZeroSupremum.beta + e)
      physicalDelta hZpos] at hh
  have hwgain : physicalDelta * (24 * e - 3 / 5) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hDelta (by linarith only [hehi])
  have hwbase := source_w_strict_exponent HeckeZeroSupremum.beta e hehi
  have hzbase := source_z_strict_exponent HeckeZeroSupremum.beta e hehi
  constructor
  · exact hh.1.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith only [hwgain, hwbase]))
      (div_nonneg hC.le he.le))
  · exact hh.2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith only [hzbase, hDelta])) hC.le)

end SevenEighths.ProbePrincipalRemainderBounds


namespace SevenEighths.ProbePrincipalPhysical

open Complex MeasureTheory
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal HeckeFamily.O

/-- The actual weighted principal-row sum minus its actual source residue
retains the strict remainder saving, with one constant uniform in every
nonnegative physical tilt and all admissible slot windows and prime pools. -/
theorem physical_principal_residue_remainder_tilted {K : ℕ}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (e : ℝ) (he : 0<e) (hehi : e≤1/1000)
    (ha : 7/8<HeckeZeroSupremum.beta+e) (ha2 : HeckeZeroSupremum.beta+e≤2) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀physicalDelta : ℝ,0≤physicalDelta → ∀ell : Fin K→ℝ,(∑j,ell j)=1/6 → ∀W : Fin K→ℝ→ℝ,
    (∀j x,0≤W j x ∧ W j x≤B) → (∀j,Function.support (W j)⊆Set.Icc c d) →
    ∀T : Fin K→Finset PrimeIdeal,(∀j p,p∈T j→p.val∉S) →
    (∀P:(∀j,T j),Function.Injective (fun j=>(P j).val)) →
    ∀Z : ℝ,1≤Z → (∀j,480≤c*Z^(ell j)) → (∀j,(Ideal.absNorm η.modulus:ℝ)<c*Z^(ell j)) →
    ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(ell j)):ℂ))*
        principalRowIntegral η S (fun j=>primaryGenerator (P j).val.val)
          W0 W1 (Z^(17/48-24*physicalDelta)) (Z^(23/48+12*physicalDelta)) Z)-
      sourceResidueIntegral W0 W1 (∏p∈S,p) (η.excludePrimes S hS.prime)
        (HeckeZeroSupremum.beta+e) (Z^(17/48-24*physicalDelta)) (Z^(23/48+12*physicalDelta)) Z
        (globalClosedCorrection η S)
        (windowMultiplier η Finset.univ T (fun j x=>(W j x:ℂ)) (fun j=>Z^(ell j)))‖≤
      C/e*Z^(HeckeZeroSupremum.beta-11/16-8*physicalDelta-17/48000) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ := ProbePrincipalRemainderBounds.source_remainders_strict_saving_tilted η S hS
    (Finset.univ : Finset (Fin K)) c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ⟨ha.le,ha2⟩
  refine ⟨2*C,by positivity,?_⟩
  intro physicalDelta hDelta ell hell W hW hsupp T hT hdis Z hZ hthreshold hmod
  have hZ0 : 0<Z := by linarith
  have hb := hbound physicalDelta hDelta ell hell W (fun j _=>hW j) (fun j _=>hsupp j) T (fun j _ p hp=>hT j p hp)
    Z hZ (fun j _=>hthreshold j) (fun j _=>hmod j)
  dsimp only at hb
  have heq := principal_physical_pool_ordered η S hS T hT hdis
    (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/Z^(ell j)):ℂ)) W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 (Z^(17/48-24*physicalDelta)) (Z^(23/48+12*physicalDelta)) Z (HeckeZeroSupremum.beta+e) e
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0 ha (by linarith) (by linarith) he (by linarith)
  dsimp only at heq
  have hres (F : ℂ→ℂ) :
      (HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1)^2/6*
        verticalIntegral (HeckeZeroSupremum.beta+e) F=
      verticalIntegral (HeckeZeroSupremum.beta+e) (fun s=>fixedPrincipalResidue (∏p∈S,p)^2/6*F s) := by
    rw [verticalIntegral,verticalIntegral,integral_const_mul]
    dsimp only [fixedPrincipalResidue,fixedPrincipal,fixedSourcePrincipal]
    ring
  rw [heq]
  unfold sourceResidueIntegral windowMultiplier
  rw [hres,add_sub_cancel_right]
  have hn := (norm_add_le _ _).trans (add_le_add hb.1 hb.2)
  change _≤(2*C)/e*Z^(HeckeZeroSupremum.beta-11/16-8*physicalDelta-17/48000)
  apply hn.trans
  have hCe : C≤C/e := (le_div_iff₀ he).mpr (by nlinarith)
  have hzpow : 0≤Z^(HeckeZeroSupremum.beta-11/16-8*physicalDelta-17/48000) := Real.rpow_nonneg hZ0.le _
  have htwo : (2*C)/e=2*(C/e) := by ring
  rw [htwo]
  nlinarith
end SevenEighths.ProbePrincipalPhysical


namespace SevenEighths.HeckeSignal

open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology
open HeckeFamily Continuation

/-- The original signal and regularized Mellin identity permit a variable
analytic boundary and low-growth crossing. This theorem keeps the wider
analytic hypothesis explicit; it does not supply the physical probe bounds. -/
theorem nonzero_of_probe_bounds_variable_boundary
    (chi : Character) (H : ℂ → ℂ) (J : ℝ → ℂ)
    (alpha theta beta omega sigma c : ℝ)
    (halpha78 : alpha ≤ 7 / 8) (halphaTheta : alpha ≤ theta)
    (htheta0 : 0 ≤ theta) (hbeta : beta ≤ 1)
    (homega0 : 0 < omega) (homega : omega < beta - theta)
    (hsigma : 0 < sigma)
    (hH : AnalyticOnNhd ℂ H {s : ℂ | alpha < s.re})
    (hb : ∀ s : ℂ, alpha < s.re → ‖H s - 1‖ ≤ 1 / 2)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (theta + c + omega)))
    (herror : (fun x => J x - signal chi H c x) =O[atTop]
      (fun x : ℝ => x ^ (beta + c - sigma)))
    {rho : ℂ} (hrho : max (theta + omega) (beta - sigma) < rho.re)
    (hpole : rho ≠ 1 ∨ chi.residue ≠ 1) : LFunction chi rho ≠ 0 := by
  let a : ℝ := max (theta + omega) (beta - sigma)
  have hlow : theta + omega < beta := by linarith only [homega]
  have habeta : a < beta := by
    dsimp [a]
    exact max_lt hlow (by linarith only [hsigma])
  have ha2 : a < 2 := by linarith only [habeta, hbeta]
  have hthetaa : theta < a := by
    have hm : theta + omega ≤ a := le_max_left _ _
    linarith only [hm, homega0]
  have ha0 : 0 < a := lt_of_le_of_lt htheta0 hthetaa
  have halphaa : alpha < a := lt_of_le_of_lt halphaTheta hthetaa
  change a < rho.re at hrho
  have hH78 : AnalyticOnNhd ℂ H {s : ℂ | 7 / 8 < s.re} :=
    hH.mono (fun _ hs => lt_of_le_of_lt halpha78 hs)
  have hb78 : ∀ s : ℂ, 7 / 8 < s.re → ‖H s - 1‖ ≤ 1 / 2 :=
    fun s hs => hb s (lt_of_le_of_lt halpha78 hs)
  have hHa : AnalyticOnNhd ℂ H {s : ℂ | a < s.re} :=
    hH.mono (fun _ hs => lt_trans halphaa hs)
  have hexp : max (theta + c + omega) (beta + c - sigma) = a + c := by
    dsimp [a]
    rcases le_total (theta + omega) (beta - sigma) with h | h
    · have h' : theta + c + omega ≤ beta + c - sigma := by linarith
      rw [max_eq_right h', max_eq_right h]
      ring
    · have h' : beta + c - sigma ≤ theta + c + omega := by linarith
      rw [max_eq_left h', max_eq_left h]
      ring
  have htop : signal chi H c =O[atTop] (fun x : ℝ => x ^ (a + c)) := by
    simpa only [hexp] using
      common_signal_bound J (signal chi H c)
        (theta + c + omega) (beta + c - sigma) hJ herror
  have hL : AnalyticOnNhd ℂ (regularL chi) {s : ℂ | a < s.re} :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (regularL_entire chi)).mono (Set.subset_univ _)
  have hR : AnalyticOnNhd ℂ (targetRegularizer chi) {s : ℂ | a < s.re} :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (targetRegularizer_entire chi)).mono (Set.subset_univ _)
  have hrho0 : rho ≠ 0 := by
    intro hz
    rw [hz] at hrho
    norm_num at hrho
    linarith
  refine nonzero_of_regularized_signal a 1 c
    (LFunction chi) (regularL chi) (targetRegularizer chi)
    (gaussianMultiplier H) (signal chi H c)
    hL hR (gaussianMultiplier_analytic hHa)
    (signal_locallyIntegrable chi H hH78.differentiableOn hb78 c)
    htop (signal_rapidDecayAtZero chi H hH78.differentiableOn hb78 c)
    ?_ hrho (regularL_eq chi hrho0 hpole)
    (targetRegularizer_ne_zero chi hpole)
    (gaussianMultiplier_ne_zero (hb rho (lt_trans halphaa hrho)))
  intro s hs
  have hs1 : 1 < s.re := (le_max_right a 1).trans_lt hs
  have h0 : s ≠ 0 := by intro hz; norm_num [hz] at hs1
  have h1 : s ≠ 1 := by intro hz; norm_num [hz] at hs1
  rw [regularL_eq chi h0 (Or.inl h1),
    signalMellin_eq_amplitude chi H hH78.differentiableOn hb78 c a ha2 htop hs]
  unfold amplitude quotient gaussianMultiplier
  rw [HeckeReciprocal.reciprocal_eq_inv chi h0 h1]
  have hn := LFunction_ne_zero_of_one_lt_re chi hs1
  field_simp

end SevenEighths.HeckeSignal

#print axioms SevenEighths.PrincipalSignalComparison.source_power_identity_variable_x
#print axioms SevenEighths.ProbePrincipalRemainderBounds.source_scale_identity_variable_xy
#print axioms SevenEighths.ProbePrincipalRemainderBounds.source_remainders_strict_saving_tilted
#print axioms SevenEighths.ProbePrincipalPhysical.physical_principal_residue_remainder_tilted
#print axioms SevenEighths.PrincipalSignalComparison.normalized_source_double_residue_variable_x
#print axioms SevenEighths.PrincipalSignalComparison.sourceCorrection_analytic_wide
#print axioms SevenEighths.PrincipalSignalComparison.sourceCorrection_bound_wide
#print axioms SevenEighths.HeckeSignal.nonzero_of_probe_bounds_variable_boundary
#print axioms SevenEighths.RHLeanFiniteSlotGap.exists_fine_high_data_with_reserve
#print axioms SevenEighths.RHLeanFiniteSlotGap.source_gain_budgets
#print axioms SevenEighths.RHLeanFiniteSlotGap.high_data_small_errors
#print axioms SevenEighths.RHLeanFiniteSlotGap.capped_high_data_geometry
#print axioms SevenEighths.RHLeanFiniteSlotGap.capped_high_data_bounds
#print axioms SevenEighths.RHLeanFiniteSlotGap.high_data_central_cost_of_bounds
#print axioms SevenEighths.RHLeanFiniteSlotGap.capped_high_data_central_cost
#print axioms SevenEighths.RHLeanFiniteSlotGap.capped_high_data_central_reserve
#print axioms SevenEighths.RHLeanFiniteSlotGap.fixed_delta_target_payment
#print axioms SevenEighths.RHLeanFiniteSlotGap.capped_high_data_window
#print axioms SevenEighths.RHLeanFiniteSlotGap.hybridSaving_zero
#print axioms SevenEighths.RHLeanFiniteSlotGap.finite_selected_mass_gap
#print axioms SevenEighths.RHLeanFiniteSlotGap.source_selected_mass_gap
#print axioms SevenEighths.RHLeanFiniteSlotGap.finite_slot_gate
#print axioms SevenEighths.RHLeanFiniteSlotGap.reflected_exponent_finite_slot_gap
#print axioms SevenEighths.RHLeanFiniteSlotGap.equal_scale_perturbation
#print axioms SevenEighths.RHLeanFiniteSlotGap.tilted_scale_perturbation
#print axioms SevenEighths.RHLeanFiniteSlotGap.tilted_central_prefactor_margin
#print axioms SevenEighths.InverseReflectedPhase.empty_active_tuple_dyad_width
#print axioms SevenEighths.InverseReflectedPhase.surviving_low_exponent_finite_slot_gap
#print axioms SevenEighths.InverseReflectedPhase.surviving_low_energy_sum_finite_slot_gap
#print axioms SevenEighths.InverseReflectedPhase.low_sector_literal_energy_finite_slot_gap
#print axioms SevenEighths.ProbeEuler.unramifiedClosed_open_region_bound_twenty_one_twenty_fifths

end
end OAI


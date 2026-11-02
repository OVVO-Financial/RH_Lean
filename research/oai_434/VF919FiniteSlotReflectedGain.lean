import OAI.NumberTheory.DirichletL.Reflection.LowExponent
import OAI.NumberTheory.DirichletL.Reflection.TupleDyads
import OAI.NumberTheory.DirichletL.Detector.LowNominalGeometry
import OAI.NumberTheory.DirichletL.ParametersHighData
import OAI.NumberTheory.DirichletL.Detector.GlobalRegion

/-!
# A finite-slot gap in the actual reflected low exponent

The continuous scalar relaxation permits arbitrarily small positive selected
length. A fixed finite source with positive slot lengths does not. The theorem
below retains the original reflected exponent and proves a sufficient gate
that uses this distinction, uniformly over the surviving reflected dyads.

The source-facing theorem keeps the original ideals, optional pools, frozen
branches, masks and retained-width hypotheses. Its physical exponent is
generalized from 5/6 to S and its total slot length from 1/6 to L. No endpoint
below seven eighths is asserted: the complete perturbed low/high consumer and
analytic continuation chain still have to be reconstructed.
-/

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.RHLeanFiniteSlotGap

open InverseTerminalWidths SevenEighths.ProbeLowReflected

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
    (hSL : S + L ≤ 1) (hL : L ≤ 1 / 3) (hd : 0 ≤ d) (heta : 0 ≤ eta)
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
#print axioms SevenEighths.ProbeEuler.unramifiedClosed_open_region_bound_twenty_one_twenty_fifths

end
end OAI

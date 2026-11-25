import RHLean.Analysis.AlpogeNativeSignedSlopeComparison

/-!
# The global gain bound needs only a one-sided period comparison

The original data, gain, metrics, slopes, widths and MAIN are unchanged.
A measured divisor comparison at a period P, together with P >= logOm-rho,
adds exactly m*sumA*rho to the finite global budget. It is not amplified
by the rank-gap denominator or the width-variation term. After division
by the original physical character divisor its cost is
2*rho*mean(a)/(b*Delta).

This is a quantitative weakening of the required period supplier, not a
construction of the local recovery modules or of the physical DIV/slope
witnesses. The actual degree comparison at P remains explicit.

The finite argument follows Ga_bound5 and weighted_mean_bound_statement in
AlpogeSignedSlope/Formalism/SizeWindowBrackets/ChainSlopeWindows/
LevelOfCongruence.lean, reconstructed from Levent Alpoge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4.
No original data field is assigned the desired arithmetic formula.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators Classical

namespace RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.WeightedSlopeBounds

open RHLean.Geometry.AlpogeSignedSlope.Formalism.RankGapBounds.WeightedMeanData

variable {U0 : Type} [Fintype U0] {W : U0 → Type}
  [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
  {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ)

omit [Fintype U0] [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)] in
/-- Monotonicity uses the actual nonnegative heights. A lower bound on the
period is sufficient; an exact period identity is unnecessary. -/
theorem nativeDivisorDebt_of_period_lower
    (P : (u0 : U0) → W u0 → ℝ) (rho : ℝ)
    (ha : ∀ t, 0 ≤ D.aT t)
    (hP : ∀ u0 u, D.logOm - rho ≤ P u0 u)
    (hDegree : ∀ u0 (u : W u0), D.muCC u0 + D.h u0 u - D.Fo u0 ≤
      (∑ t, ((m : ℝ) * (ph (D.aT t) - D.aT t * P u0 u) -
        D.aT t * Real.log (D.T u0 u))) + D.EDiv C) :
    ∀ u0 (u : W u0), D.muCC u0 + D.h u0 u - D.Fo u0 ≤
      D.SDiv - D.sumA * Real.log (D.T u0 u) + D.EDiv C +
        (m : ℝ) * D.sumA * rho := by
  intro u0 u
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset Top))
    (fun t _ => show
      (m : ℝ) * (ph (D.aT t) - D.aT t * P u0 u) -
          D.aT t * Real.log (D.T u0 u) ≤
        (m : ℝ) * (ph (D.aT t) - D.aT t * D.logOm) -
          D.aT t * Real.log (D.T u0 u) +
          (m : ℝ) * D.aT t * rho from by
        have hp := mul_le_mul_of_nonneg_left (hP u0 u)
          (mul_nonneg (Nat.cast_nonneg m) (ha t))
        nlinarith only [hp])
  have heq : (∑ t, ((m : ℝ) * (ph (D.aT t) - D.aT t * D.logOm) -
      D.aT t * Real.log (D.T u0 u) + (m : ℝ) * D.aT t * rho)) =
      D.SDiv - D.sumA * Real.log (D.T u0 u) + (m : ℝ) * D.sumA * rho := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, Data.SDiv, Data.sumA]
  have h := hDegree u0 u
  rw [heq] at hsum
  linarith

omit [Fintype U0] in
private theorem native_s_lower_of_divisorDebt (debt : ℝ)
    (hS : D.HidaSetting C)
    (hDIV : ∀ u0 (u : W u0), D.muCC u0 + D.h u0 u - D.Fo u0 ≤
      D.SDiv - D.sumA * Real.log (D.T u0 u) + D.EDiv C + debt)
    (hE : EComp5 D C) (hCount : Count5 D C) (hSl : D.Slopes C)
    (hSN : QuotientSlopeBoundsWith D C Xpp) (u0 : U0) :
    D.Ga u0 + D.muCC u0 - K5v5 D C u0 -
      wmean (D.d u0) (Lo5 D C Xpp u0) - debt ≤ D.s u0 := by
  have hA := D.sumA_nonneg C hS
  obtain ⟨-, -, -, -, -, -, -, -, -, hd, -⟩ := hS
  unfold Data.s
  have hbound : D.Ga u0 + D.muCC u0 - K5v5 D C u0 - debt -
      wmean (D.d u0) (Lo5 D C Xpp u0) ≤
        wmean (D.d u0) (fun u => D.muN u0 u - D.h u0 u) := by
    refine sub_wmean_le (hd u0) _ (fun u => ?_)
    have h1 := (hSN u0 u).2
    have h2 := hDIV u0 u
    have h3 : Lam5 D C u0 ≤ Real.log (D.T u0 u) := (hCount u0 u).1
    have h4 := mul_le_mul_of_nonneg_left h3 hA
    have h5 := exponent_le_upper D C hE u0 u
    have h6 := (hSl u0 u).1
    unfold K5v5
    linarith
  linarith

omit [Fintype U0] in
/-- The divisor debt enters the original global gain estimate once, without
multiplying its price by the rank-gap or entropy coefficient. -/
theorem nativeGa_bound_of_divisorDebt (debt : ℝ)
    (hS : D.HidaSetting C)
    (hDIV : ∀ u0 (u : W u0), D.muCC u0 + D.h u0 u - D.Fo u0 ≤
      D.SDiv - D.sumA * Real.log (D.T u0 u) + D.EDiv C + debt) (hE : EComp5 D C)
    (hH : D.HComp C) (hCount : Count5 D C) (hSl : D.Slopes C) (hSN : QuotientSlopeBoundsWith D C Xpp)
    (hSI : D.SlopeIneq) (hHH : D.HHBound C) (hFP : D.FParams) (u0 : U0) :
    D.Ga u0 ≤ D.Main u0 + Real.log (Fintype.card (W u0) : ℝ) + K0v5 D C
      + wmean (D.d u0) (Lo5 D C Xpp u0)
      + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH)
          * (D.K3 C + wmean (D.d u0) (Lo5 D C Xpp u0) + D.b)
        + (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b)) + debt := by
  have hsl := native_s_lower_of_divisorDebt D C Xpp debt hS hDIV hE hCount hSl hSN u0
  have huF0 := D.uF_nonneg C hS u0
  have huF := u_function_le_mean D C Xpp hS hE hH hCount hSl hSN u0
  obtain ⟨hx, hb, -, -, -, hv, hf, -, hw, -, -, -, -, hdelBar, hetaBar, heBar0, heBar⟩ := hS
  have hid := key_identity5 D C hv hf u0 (hw u0)
  obtain ⟨hdel0, hdelle, heta0, hetale, he0, hele⟩ := hFP u0
  obtain ⟨hHH1, hHH2, hHH3⟩ := hHH u0
  have hSI' := hSI u0 hdel0 (by linarith) heta0 he0 (by linarith) hHH1 hHH2
  have hX : 0 < D.x ^ C.cHH := Real.rpow_pos_of_pos hx _
  have hphi := phi_bound huF0 hHH2 hHH3 hb hX huF
  have hA0 : 0 ≤ 4 * D.uF u0 * Real.log (1 + D.HH u0 / D.uF u0) :=
    mul_nonneg (by linarith)
      (Real.log_nonneg (by have := div_nonneg hHH2.le huF0; linarith))
  have hsq : Real.sqrt (D.e u0) ≤ Real.sqrt D.eBar := Real.sqrt_le_sqrt hele
  have hc0 : 0 ≤ D.η u0 + 4 * Real.sqrt (D.e u0) :=
    add_nonneg heta0 (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  have hc1 : 0 ≤ D.etaBar + 4 * Real.sqrt D.eBar :=
    add_nonneg hetaBar (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  have hB : (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0
      ≤ (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b) :=
    calc (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0
        ≤ (D.etaBar + 4 * Real.sqrt D.eBar) * D.HH u0 :=
          mul_le_mul_of_nonneg_right (by linarith) hHH2.le
      _ ≤ (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b) :=
          mul_le_mul_of_nonneg_left hHH3 hc1
  have hB0 : 0 ≤ (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0 := mul_nonneg hc0 hHH2.le
  have hinv : (1 - D.del u0)⁻¹ ≤ (1 - D.delBar)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  have hinv0 : 0 ≤ (1 - D.delBar)⁻¹ := inv_nonneg.mpr (by linarith)
  have hPhi : (1 - D.del u0)⁻¹ * (4 * D.uF u0 * Real.log (1 + D.HH u0 / D.uF u0)
        + (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0)
      ≤ (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH)
          * (D.K3 C + wmean (D.d u0) (Lo5 D C Xpp u0) + D.b)
        + (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b)) :=
    calc _ ≤ (1 - D.delBar)⁻¹ * (4 * D.uF u0 * Real.log (1 + D.HH u0 / D.uF u0)
          + (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0) :=
          mul_le_mul_of_nonneg_right hinv (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hinv0
  unfold K0v5
  unfold K5v5 at hsl
  linarith

/-- The same finite mean-loss theorem retains the extra divisor debt.
Every loss, slope and size hypothesis concerns the original data. -/
theorem nativeMean_bound_of_divisorDebt (debt : ℝ)
    (hne : Nonempty U0) (hS : D.HidaSetting C)
    (hDIV : ∀ u0 (u : W u0), D.muCC u0 + D.h u0 u - D.Fo u0 ≤
      D.SDiv - D.sumA * Real.log (D.T u0 u) + D.EDiv C + debt)
    (hE : EComp5 D C) (hH : D.HComp C) (hCount : Count5 D C)
    (hSl : D.Slopes C) (hSN : QuotientSlopeBoundsWith D C Xpp)
    (hLoss : D.Losses C) (hSI : D.SlopeIneq) (hHH : D.HHBound C)
    (hFP : D.FParams) :
    umean D.ASK ≤ umean D.Main + errorTermWith D C Xpp + debt := by
  have := hne
  have hx : 0 < D.x := hS.1
  have hdelBar : D.delBar < 1 := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcSl1 : 0 ≤ C.cSl1 := hS.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hinv0 : 0 ≤ (1 - D.delBar)⁻¹ := inv_nonneg.mpr (by linarith)
  have hX : 0 < D.x ^ C.cHH := Real.rpow_pos_of_pos hx _
  have hLX : 0 ≤ Real.log (1 + D.x ^ C.cHH) := Real.log_nonneg (by linarith)
  have hc4 : 0 ≤ (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH)) :=
    mul_nonneg hinv0 (mul_nonneg (by norm_num) hLX)
  have hp : 0 ≤ (1 + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH))) * C.cSl1 :=
    mul_nonneg (by linarith) hcSl1
  have hGa : ∀ u0, D.Ga u0 ≤ D.Main u0 + Real.log (Fintype.card (W u0) : ℝ)
      + ((1 + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH))) * C.cSl1) * D.IO u0
      + 0 * D.IO u0
      + (K0v5 D C + (1 + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH))) * K7v5 D C Xpp
        + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH)) * (D.K3 C + D.b)
        + (1 - D.delBar)⁻¹ * ((D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b)) + debt) := by
    intro u0
    have h1 := nativeGa_bound_of_divisorDebt D C Xpp debt hS hDIV hE hH hCount hSl hSN hSI hHH hFP u0
    have h2 := weighted_mean_lower_bound_le D C Xpp hS hCount u0
    have h3 := mul_le_mul_of_nonneg_left h2 hc4
    linarith
  have h1 := umean_le_comb (X := D.Ga) (A := D.Main)
    (B := fun u0 => Real.log (Fintype.card (W u0) : ℝ)) (P := D.IO) (E := D.IO) _ _ _ hGa
  have h2 := umean_le_comb (X := D.ASK) (A := fun u0 => D.ASK u0 - D.Ga u0) (B := D.Ga)
    (P := D.Ga) (E := D.Ga) 0 0 0 (fun i => by
      show D.ASK i ≤ (D.ASK i - D.Ga i) + D.Ga i + 0 * D.Ga i + 0 * D.Ga i + 0
      linarith)
  have h3 := mul_le_mul_of_nonneg_left hLoss.2 hp
  have h4 := hLoss.1
  unfold K0v5 Data.K3 K7v5 Data.EDiv at h1
  unfold errorTermWith UBar5 MLo5
  linarith

/-- The global comparison consumes a one-sided period bound and retains
its exact additional cost. The measured degree input is not supplied here. -/
theorem nativeMean_bound_of_period_lower
    (P : (u0 : U0) → W u0 → ℝ) (rho : ℝ)
    (hne : Nonempty U0) (hS : D.HidaSetting C)
    (hP : ∀ u0 u, D.logOm - rho ≤ P u0 u)
    (hDegree : ∀ u0 (u : W u0), D.muCC u0 + D.h u0 u - D.Fo u0 ≤
      (∑ t, ((m : ℝ) * (ph (D.aT t) - D.aT t * P u0 u) -
        D.aT t * Real.log (D.T u0 u))) + D.EDiv C)
    (hE : EComp5 D C) (hH : D.HComp C) (hCount : Count5 D C)
    (hSl : D.Slopes C) (hSN : QuotientSlopeBoundsWith D C Xpp)
    (hLoss : D.Losses C) (hSI : D.SlopeIneq) (hHH : D.HHBound C)
    (hFP : D.FParams) :
    umean D.ASK ≤ umean D.Main + errorTermWith D C Xpp +
      (m : ℝ) * D.sumA * rho := by
  have ha : ∀ t, 0 ≤ D.aT t := hS.2.2.2.2.2.2.2.1
  exact nativeMean_bound_of_divisorDebt D C Xpp ((m : ℝ) * D.sumA * rho)
    hne hS (nativeDivisorDebt_of_period_lower D C P rho ha hP hDegree)
    hE hH hCount hSl hSN hLoss hSI hHH hFP


/-- The literal width sum, with the original finite CM averaging. -/
def nativeWidthLog (u0 : U0) : ℝ :=
  ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ)

/-- Both comparisons use the same independently supplied period at each
fiber. No equality with logOm, absolute period normalization, or choice
of new height, slope, or gain data is required. The measured divisor and
count inequalities themselves still need genuine suppliers. -/
def NativeCoupledDegree (P : (u0 : U0) → W u0 → ℝ) : Prop :=
  ∀ u0 (u : W u0), D.muCC u0 + D.h u0 u - D.Fo u0 ≤
    (∑ t, ((m : ℝ) * (ph (D.aT t) - D.aT t * P u0 u) -
      D.aT t * Real.log (D.T u0 u))) + D.EDiv C

def NativeCoupledCount (P : (u0 : U0) → W u0 → ℝ) : Prop :=
  ∀ u0 (u : W u0),
    nativeWidthLog D u0 + (m : ℝ) * (D.gam - D.LpL - P u0 u) +
      (m : ℝ) * D.lg - C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k) ≤
        Real.log (D.T u0 u)

/-- The original upper and oscillation count conditions, retaining the
measured T. The period-dependent lower condition is separate. -/
def NativeCountRest : Prop :=
  ∀ u0 (u : W u0), Real.log (D.T u0 u) ≤ C.cCount * (m : ℝ) * D.L ∧
    ∀ u' : W u0, |Real.log (D.T u0 u) - Real.log (D.T u0 u')| ≤
      C.cCount * Real.log D.k

omit [Fintype U0] [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)] in
private theorem main_eq_widthLog (u0 : U0) :
    D.Main u0 = (m : ℝ) * (∑ t, ph (D.aT t)) -
      D.sumA * (nativeWidthLog D u0 + (m : ℝ) * (D.gam - D.LpL)) := by
  have hcard : ∀ c : ℝ, ∑ _j : Fin m, c = (m : ℝ) * c := fun c => by simp
  have hj : ∀ j : Fin m,
      (∑ t, D.aT t * (Real.log (D.aT t) - 1 - D.gam + D.LpL -
        (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ))) =
      (∑ t, ph (D.aT t)) -
        D.sumA * (D.gam - D.LpL +
          (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ)) := by
    intro j
    calc
      _ = ∑ t, (ph (D.aT t) - D.aT t * (D.gam - D.LpL +
          (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ))) := by
        apply Finset.sum_congr rfl
        intro t _
        unfold ph
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, Data.sum_aT_mul]
  unfold Data.Main nativeWidthLog
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hj j),
    Finset.sum_sub_distrib, hcard, ← Finset.mul_sum, Finset.sum_add_distrib, hcard]
  ring

omit [Fintype U0] [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)] in
/-- Exact cancellation of an arbitrary common measured period. In contrast
to a one-sided period approximation, no additional period debt appears. -/
theorem nativeRelativeDegreeCount_le
    (P : (u0 : U0) → W u0 → ℝ) (hS : D.HidaSetting C)
    (hDegree : NativeCoupledDegree D C P) (hCount : NativeCoupledCount D C P)
    (u0 : U0) (u : W u0) :
    D.muCC u0 + D.h u0 u - D.Fo u0 ≤
      D.Main u0 - (m : ℝ) * D.sumA * D.lg +
        D.sumA * (C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k)) + D.EDiv C := by
  have hdeg := hDegree u0 u
  have hsplit : (∑ t, ((m : ℝ) * (ph (D.aT t) - D.aT t * P u0 u) -
      D.aT t * Real.log (D.T u0 u))) =
      (m : ℝ) * (∑ t, ph (D.aT t)) - (m : ℝ) * D.sumA * P u0 u -
        D.sumA * Real.log (D.T u0 u) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Data.sum_aT_mul, Data.sum_aT_mul]
    ring
  rw [hsplit] at hdeg
  have hc := mul_le_mul_of_nonneg_left (hCount u0 u) (D.sumA_nonneg C hS)
  have hmain := main_eq_widthLog D u0
  nlinarith only [hdeg, hc, hmain]

omit [Fintype U0] in
private theorem native_s_lower_of_coupled_period
    (P : (u0 : U0) → W u0 → ℝ) (hS : D.HidaSetting C)
    (hDegree : NativeCoupledDegree D C P) (hCount : NativeCoupledCount D C P)
    (hE : EComp5 D C) (hSl : D.Slopes C)
    (hSN : QuotientSlopeBoundsWith D C Xpp) (u0 : U0) :
    D.Ga u0 + D.muCC u0 - D.Main u0 - K0v5 D C -
      wmean (D.d u0) (Lo5 D C Xpp u0) ≤ D.s u0 := by
  have hd := hS.2.2.2.2.2.2.2.2.2.1
  unfold Data.s
  have hbound := sub_wmean_le (hd u0)
    (D.Ga u0 + D.muCC u0 - D.Main u0 - K0v5 D C)
    (Y := Lo5 D C Xpp u0) (X := fun u => D.muN u0 u - D.h u0 u) (fun u => by
      have h1 := (hSN u0 u).2
      have h2 := nativeRelativeDegreeCount_le D C P hS hDegree hCount u0 u
      have h5 := exponent_le_upper D C hE u0 u
      have h6 := (hSl u0 u).1
      unfold K0v5
      linarith)
  exact hbound

omit [Fintype U0] [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)] in
private theorem nativeVvar_bound_of_countRest
    (hS : D.HidaSetting C) (hE : EComp5 D C) (hH : D.HComp C)
    (hCount : NativeCountRest D C) (u0 : U0) (u u' : W u0) :
    (-D.Ee u0 u - D.h u0 u) - (-D.Ee u0 u' - D.h u0 u') ≤ D.Vvar C := by
  have hA := D.sumA_nonneg C hS
  have h1 := exponent_le_upper D C hE u0 u'
  have h2 := exponent_ge_lower D C hE u0 u
  have h3 := (abs_le.mp (hH u0 u' u)).2
  rw [Data.sum_aT_mul, Data.sum_aT_mul] at h3
  have h4 := (abs_le.mp ((hCount u0 u).2 u')).2
  have h5 := mul_le_mul_of_nonneg_left h4 hA
  unfold Data.Vvar
  linarith

omit [Fintype U0] in
private theorem native_uF_bound_of_countRest
    (hS : D.HidaSetting C) (hE : EComp5 D C) (hH : D.HComp C)
    (hCount : NativeCountRest D C) (hSl : D.Slopes C)
    (hSN : QuotientSlopeBoundsWith D C Xpp) (u0 : U0) :
    D.uF u0 ≤ D.K3 C + wmean (D.d u0) (Lo5 D C Xpp u0) := by
  have hd := hS.2.2.2.2.2.2.2.2.2.1
  have hs : ∀ u, (D.muMaxN u0 u - D.h u0 u - D.K3 C) -
      wmean (D.d u0) (Lo5 D C Xpp u0) ≤ D.s u0 := by
    intro u
    unfold Data.s
    refine sub_wmean_le (hd u0) _ (fun u' => ?_)
    have h1 := (hSN u0 u).1
    have h2 := (hSN u0 u').2
    have h3 := (hSl u0 u).2
    have h4 := (hSl u0 u').1
    have h5 := nativeVvar_bound_of_countRest D C hS hE hH hCount u0 u u'
    unfold Data.K3
    try dsimp only
    linarith
  unfold Data.uF
  have hsup := Finset.sup'_le (Finset.univ_nonempty (α := W u0))
    (fun u : W u0 => D.muMaxN u0 u - D.h u0 u)
    (a := D.s u0 + (D.K3 C + wmean (D.d u0) (Lo5 D C Xpp u0)))
    (fun u _ => by have := hs u; linarith)
  linarith

omit [Fintype U0] in
private theorem nativeLo5_le_of_countRest
    (hS : D.HidaSetting C) (hCount : NativeCountRest D C) (u0 : U0) :
    wmean (D.d u0) (Lo5 D C Xpp u0) ≤ C.cSl1 * D.IO u0 + K7v5 D C Xpp := by
  obtain ⟨-, -, ha, hb', hk, -, -, -, -, hd, -, -, hcSl1, -⟩ := hS
  refine wmean_le_const (hd u0) _ (fun u => ?_)
  have hc : 0 ≤ C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') :=
    mul_nonneg (mul_nonneg (mul_nonneg hcSl1 D.nT_nonneg) (Nat.cast_nonneg _))
      (add_nonneg (div_nonneg ha hk.le) hb')
  have h1 := mul_le_mul_of_nonneg_left (hCount u0 u).1 hc
  unfold Lo5 K7v5
  linarith

omit [Fintype U0] in
/-- The same finite global gain bound with no absolute period comparison.
Both degree and counting inequalities use the original measured data.
All rank, slope, variation and error conditions are retained. -/
theorem nativeGa_bound_of_coupled_period
    (P : (u0 : U0) → W u0 → ℝ) (hS : D.HidaSetting C)
    (hDegree : NativeCoupledDegree D C P) (hCount : NativeCoupledCount D C P)
    (hRest : NativeCountRest D C) (hE : EComp5 D C) (hH : D.HComp C)
    (hSl : D.Slopes C) (hSN : QuotientSlopeBoundsWith D C Xpp)
    (hSI : D.SlopeIneq) (hHH : D.HHBound C) (hFP : D.FParams) (u0 : U0) :
    D.Ga u0 ≤ D.Main u0 + Real.log (Fintype.card (W u0) : ℝ) + K0v5 D C
      + wmean (D.d u0) (Lo5 D C Xpp u0)
      + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH)
          * (D.K3 C + wmean (D.d u0) (Lo5 D C Xpp u0) + D.b)
        + (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b)) := by
  have hsl := native_s_lower_of_coupled_period D C Xpp P hS hDegree hCount hE hSl hSN u0
  have huF0 := D.uF_nonneg C hS u0
  have huF := native_uF_bound_of_countRest D C Xpp hS hE hH hRest hSl hSN u0
  obtain ⟨hx, hb, -, -, -, -, -, -, -, -, -, -, -, hdelBar, hetaBar, -, heBar⟩ := hS
  obtain ⟨hdel0, hdelle, heta0, hetale, he0, hele⟩ := hFP u0
  obtain ⟨hHH1, hHH2, hHH3⟩ := hHH u0
  have hSI' := hSI u0 hdel0 (by linarith) heta0 he0 (by linarith) hHH1 hHH2
  have hX : 0 < D.x ^ C.cHH := Real.rpow_pos_of_pos hx _
  have hphi := phi_bound huF0 hHH2 hHH3 hb hX huF
  have hA0 : 0 ≤ 4 * D.uF u0 * Real.log (1 + D.HH u0 / D.uF u0) :=
    mul_nonneg (by linarith)
      (Real.log_nonneg (by have := div_nonneg hHH2.le huF0; linarith))
  have hsq : Real.sqrt (D.e u0) ≤ Real.sqrt D.eBar := Real.sqrt_le_sqrt hele
  have hc0 : 0 ≤ D.η u0 + 4 * Real.sqrt (D.e u0) :=
    add_nonneg heta0 (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  have hc1 : 0 ≤ D.etaBar + 4 * Real.sqrt D.eBar :=
    add_nonneg hetaBar (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  have hB : (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0
      ≤ (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b) :=
    calc (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0
        ≤ (D.etaBar + 4 * Real.sqrt D.eBar) * D.HH u0 :=
          mul_le_mul_of_nonneg_right (by linarith) hHH2.le
      _ ≤ (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b) :=
          mul_le_mul_of_nonneg_left hHH3 hc1
  have hB0 : 0 ≤ (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0 := mul_nonneg hc0 hHH2.le
  have hinv : (1 - D.del u0)⁻¹ ≤ (1 - D.delBar)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  have hinv0 : 0 ≤ (1 - D.delBar)⁻¹ := inv_nonneg.mpr (by linarith)
  have hPhi : (1 - D.del u0)⁻¹ * (4 * D.uF u0 * Real.log (1 + D.HH u0 / D.uF u0)
        + (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0)
      ≤ (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH)
          * (D.K3 C + wmean (D.d u0) (Lo5 D C Xpp u0) + D.b)
        + (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b)) :=
    calc _ ≤ (1 - D.delBar)⁻¹ * (4 * D.uF u0 * Real.log (1 + D.HH u0 / D.uF u0)
          + (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0) :=
          mul_le_mul_of_nonneg_right hinv (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hinv0
  linarith

/-- The original complete mean-loss cost with the same errorTermWith,
now independent of the absolute period. The common period may vary
over the individual fibers. -/
theorem nativeMean_bound_of_coupled_period
    (P : (u0 : U0) → W u0 → ℝ)
    (hne : Nonempty U0) (hS : D.HidaSetting C)
    (hDegree : NativeCoupledDegree D C P) (hCount : NativeCoupledCount D C P)
    (hRest : NativeCountRest D C) (hE : EComp5 D C) (hH : D.HComp C)
    (hSl : D.Slopes C) (hSN : QuotientSlopeBoundsWith D C Xpp)
    (hLoss : D.Losses C) (hSI : D.SlopeIneq) (hHH : D.HHBound C)
    (hFP : D.FParams) :
    umean D.ASK ≤ umean D.Main + errorTermWith D C Xpp := by
  have := hne
  have hx : 0 < D.x := hS.1
  have hdelBar : D.delBar < 1 := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcSl1 : 0 ≤ C.cSl1 := hS.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hinv0 : 0 ≤ (1 - D.delBar)⁻¹ := inv_nonneg.mpr (by linarith)
  have hX : 0 < D.x ^ C.cHH := Real.rpow_pos_of_pos hx _
  have hLX : 0 ≤ Real.log (1 + D.x ^ C.cHH) := Real.log_nonneg (by linarith)
  have hc4 : 0 ≤ (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH)) :=
    mul_nonneg hinv0 (mul_nonneg (by norm_num) hLX)
  have hp : 0 ≤ (1 + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH))) * C.cSl1 :=
    mul_nonneg (by linarith) hcSl1
  have hGa : ∀ u0, D.Ga u0 ≤ D.Main u0 + Real.log (Fintype.card (W u0) : ℝ)
      + ((1 + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH))) * C.cSl1) * D.IO u0
      + 0 * D.IO u0
      + (K0v5 D C + (1 + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH))) * K7v5 D C Xpp
        + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH)) * (D.K3 C + D.b)
        + (1 - D.delBar)⁻¹ * ((D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b))) := by
    intro u0
    have h1 := nativeGa_bound_of_coupled_period D C Xpp P hS hDegree hCount hRest hE hH hSl hSN hSI hHH hFP u0
    have h2 := nativeLo5_le_of_countRest D C Xpp hS hRest u0
    have h3 := mul_le_mul_of_nonneg_left h2 hc4
    linarith
  have h1 := umean_le_comb (X := D.Ga) (A := D.Main)
    (B := fun u0 => Real.log (Fintype.card (W u0) : ℝ)) (P := D.IO) (E := D.IO) _ _ _ hGa
  have h2 := umean_le_comb (X := D.ASK) (A := fun u0 => D.ASK u0 - D.Ga u0) (B := D.Ga)
    (P := D.Ga) (E := D.Ga) 0 0 0 (fun i => by
      show D.ASK i ≤ (D.ASK i - D.Ga i) + D.Ga i + 0 * D.Ga i + 0 * D.Ga i + 0
      linarith)
  have h3 := mul_le_mul_of_nonneg_left hLoss.2 hp
  have h4 := hLoss.1
  unfold K0v5 Data.K3 K7v5 Data.EDiv at h1
  unfold errorTermWith UBar5 MLo5
  linarith

end RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.WeightedSlopeBounds

namespace RHLean.Analysis

/-- Exact price of the one-sided period error at the already earned
physical divisor. `sumA` is the sum of the original amplitudes, not the
geometric error parameter `aE`. -/
theorem alpogeNativePeriodDebt_div_projectionDivisor
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (TT T2 : Finset H) (m : ℕ) (b sumA rho : ℝ)
    (hTT : TT.Nonempty) (hT2 : T2.Nonempty) (hm : 0 < m)
    (hb : 0 < b) :
    ((m : ℝ) * sumA * rho) / alpogeNativeProjectionDivisor TT T2 m b =
      2 * rho * (sumA / (TT.card : ℝ)) /
        (b * alpogeNativeProjectionDensity T2) := by
  have hT : (TT.card : ℝ) ≠ 0 := by exact_mod_cast hTT.card_pos.ne'
  have hh : (T2.card : ℝ) ≠ 0 := by exact_mod_cast hT2.card_pos.ne'
  have hn : (Fintype.card H : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card H).ne'
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold alpogeNativeProjectionDivisor alpogeNativeProjectionDensity
  field_simp [hT, hh, hn, hm', hb.ne']

end RHLean.Analysis

namespace RHLean.Analysis.AlpogeNativeSignedSlope

open RHLean.Geometry.AlpogeSignedSlope.Formalism.RankGapBounds.WeightedMeanData
open RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.WeightedSlopeBounds

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
  (A0 : AddSubgroup H) {W : A0 → Type} {m f : ℕ} (TT : Finset H)
  (D0 : Data A0 W TT m f)
  (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
  (frob : ℕ → AlpogeNativeE0 × H)
  (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
  (N : ℕ) (a : H → ℝ) (w : H → Fin m → AlpogeNativeE0 × H → ℝ)
  (eP : Fin f ≃ (alpogeNativePhiSet H))
  [∀ u, Fintype (W u)] [∀ u, Nonempty (W u)]
  (C : Consts) (Xpp : ℝ)

local notation "DP" => physicalData A0 TT D0 inertia frob ell N a w eP

/-- The original physical top excess inherits the one-sided period supplier
with the exact normalized penalty. The gain and all geometric entries remain
those of D0; only the previously constructed physicalData identification is
used. This statement is conditional on the measured degree and slope inputs. -/
theorem physicalTopExcess_div_le_errorTerm_of_period_lower
    (P : (u : A0) → W u → ℝ) (rho : ℝ)
    (hS : (DP).HidaSetting C)
    (hP : ∀ u v, (DP).logOm - rho ≤ P u v)
    (hDegree : ∀ u (v : W u), (DP).muCC u + (DP).h u v - (DP).Fo u ≤
      (∑ t, ((m : ℝ) * (ph ((DP).aT t) - (DP).aT t * P u v) -
        (DP).aT t * Real.log ((DP).T u v))) + (DP).EDiv C)
    (hE : EComp5 DP C) (hH : (DP).HComp C) (hCount : Count5 DP C)
    (hSl : (DP).Slopes C) (hSN : QuotientSlopeBoundsWith DP C Xpp)
    (hLoss : (DP).Losses C) (hSI : (DP).SlopeIneq)
    (hHH : (DP).HHBound C) (hFP : (DP).FParams)
    (T2 : Finset H) (hTT : TT.Nonempty) (hT2 : T2.Nonempty) (hm : 0 < m) :
    alpogeNativePhysicalSubgroupTopExcess A0 inertia frob ell N TT a w /
        alpogeNativeProjectionDivisor TT T2 m D0.b ≤
      errorTermWith DP C Xpp / alpogeNativeProjectionDivisor TT T2 m D0.b +
        2 * rho * ((DP).sumA / (TT.card : ℝ)) /
          (D0.b * alpogeNativeProjectionDensity T2) := by
  have hmean := nativeMean_bound_of_period_lower DP C Xpp P rho
    (inferInstance : Nonempty A0) hS hP hDegree
    hE hH hCount hSl hSN hLoss hSI hHH hFP
  have hsource : alpogeNativePhysicalSubgroupTopExcess A0 inertia frob ell N TT a w ≤
      errorTermWith DP C Xpp + (m : ℝ) * (DP).sumA * rho := by
    rw [physicalTopExcess_eq_meanGap A0 TT D0 inertia frob ell N a w eP]
    linarith
  have hQ : 0 < alpogeNativeProjectionDivisor TT T2 m D0.b :=
    alpogeNativeProjectionDivisor_pos TT T2 hTT hT2 m hm D0.b hS.2.1
  calc
    _ ≤ (errorTermWith DP C Xpp + (m : ℝ) * (DP).sumA * rho) /
        alpogeNativeProjectionDivisor TT T2 m D0.b :=
      div_le_div_of_nonneg_right hsource hQ.le
    _ = _ := by
      rw [add_div, alpogeNativePeriodDebt_div_projectionDivisor TT T2 m D0.b
        (DP).sumA rho hTT hT2 hm hS.2.1]


/-- Exact physical attachment of the paired-period comparison.
No geometry is constructed here and no estimate for the target
source is assumed. The relative measured suppliers are explicit. -/
theorem physicalTopExcess_div_le_errorTerm_of_coupled_period
    (P : (u : A0) → W u → ℝ)
    (hS : (DP).HidaSetting C)
    (hDegree : NativeCoupledDegree DP C P)
    (hCount : NativeCoupledCount DP C P)
    (hRest : NativeCountRest DP C)
    (hE : EComp5 DP C) (hH : (DP).HComp C)
    (hSl : (DP).Slopes C) (hSN : QuotientSlopeBoundsWith DP C Xpp)
    (hLoss : (DP).Losses C) (hSI : (DP).SlopeIneq)
    (hHH : (DP).HHBound C) (hFP : (DP).FParams)
    (T2 : Finset H) (hTT : TT.Nonempty) (hT2 : T2.Nonempty) (hm : 0 < m) :
    alpogeNativePhysicalSubgroupTopExcess A0 inertia frob ell N TT a w /
        alpogeNativeProjectionDivisor TT T2 m D0.b ≤
      errorTermWith DP C Xpp / alpogeNativeProjectionDivisor TT T2 m D0.b := by
  have hmean := nativeMean_bound_of_coupled_period DP C Xpp P
    (inferInstance : Nonempty A0) hS hDegree hCount hRest
    hE hH hSl hSN hLoss hSI hHH hFP
  have hsource : alpogeNativePhysicalSubgroupTopExcess A0 inertia frob ell N TT a w ≤
      errorTermWith DP C Xpp := by
    rw [physicalTopExcess_eq_meanGap A0 TT D0 inertia frob ell N a w eP]
    linarith
  have hQ : 0 < alpogeNativeProjectionDivisor TT T2 m D0.b :=
    alpogeNativeProjectionDivisor_pos TT T2 hTT hT2 m hm D0.b hS.2.1
  exact div_le_div_of_nonneg_right hsource hQ.le

end RHLean.Analysis.AlpogeNativeSignedSlope

end

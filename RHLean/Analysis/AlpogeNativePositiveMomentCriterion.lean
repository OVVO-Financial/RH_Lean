import RHLean.Analysis.AlpogeNativeWindowLandau
import RHLean.Analysis.AlpogeExactNNSGzBridge

/-!
# A direct positive-moment criterion for the complete native Gz

The observable is the positive part of `alpogeNativeGzArithmetic (exp u)`,
integrated against the factorial-normalized Laplace kernel. Its cofinal moment bound
feeds the Landau pole argument directly; no pointwise window estimate is
assumed. For each exponent, the kernel parameter and bound constant are
fixed before the moment order is chosen.

At natural endpoints, taking the positive part preserves the entire signed
NNS history, including its lower mass and harmonic/Euler centering. It does
not identify this observable with the sum of the positive local sources.

The existing Mertens-first estimate supplies an unconditional linear upper
bound and hence moments of size `B / (σ - 1)^(k+1)`. The stronger cofinal
moment growth bound used for RH remains an explicit arithmetic premise.
-/

noncomputable section
open Complex MeasureTheory Set

namespace RHLean.Analysis

/-- The weighted upper first partial moment of the complete native source.
The index `k` is the kernel order, not the degree of the source moment.
For `2 < σ`, the native coarse growth bound guarantees integrability. -/
def alpogeNativeGzPositiveMoment (σ : ℝ) (k : ℕ) : ℝ :=
  WindowLandau.weightedPositiveMoment
    (fun u => alpogeNativeGzArithmetic (Real.exp u)) σ k

/-- An explicit constant supplied by native Mertens-first arithmetic. -/
def alpogeNativeGzLinearUpperConstant : ℝ :=
  Real.log 4 + 3 + |Real.eulerMascheroniConstant|

theorem alpogeNativeGzLinearUpperConstant_nonneg :
    0 ≤ alpogeNativeGzLinearUpperConstant := by
  unfold alpogeNativeGzLinearUpperConstant
  have hlog : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  linarith [abs_nonneg Real.eulerMascheroniConstant]

/-- A proved coarse upper bound for the positive part of the complete real
source. It uses the signed Mertens-first estimate before taking a maximum. -/
theorem alpogeNativeGzArithmetic_posPart_le_linear (x : ℝ) (hx : 1 ≤ x) :
    max (alpogeNativeGzArithmetic x) 0 ≤ alpogeNativeGzLinearUpperConstant * x := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hn : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr (by simpa using hx)
  have hn0 : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by exact_mod_cast hn
  have hlog : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
    Real.log_le_log hn0 (Nat.floor_le hx0)
  have hM := (nativeLambdaRecip_sub_log_bounds ⌊x⌋₊ hn).2
  have hrecip : nativeLambdaRecip ⌊x⌋₊ - Real.log x ≤ Real.log 4 + 2 := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hrecip hx0
  have hgamma := mul_le_mul_of_nonneg_right
    (le_abs_self Real.eulerMascheroniConstant) hx0
  have hpsi := nativePsi_nonneg ⌊x⌋₊
  have hsource : alpogeNativeGzArithmetic x ≤ alpogeNativeGzLinearUpperConstant * x := by
    unfold alpogeNativeGzArithmetic alpogeNativeGzLinearUpperConstant
    nlinarith only [hmul, hgamma, hpsi]
  exact max_le hsource (mul_nonneg alpogeNativeGzLinearUpperConstant_nonneg hx0)

/-- The existing arithmetic bounds supply all positive moments at exponent
one. This denominator is weaker than the `σ - θ` denominator needed when
`θ < 1`; no critical moment estimate is inferred from it. -/
theorem alpogeNativeGzPositiveMoment_le_linear {σ : ℝ} (hσ : 2 < σ) (k : ℕ) :
    alpogeNativeGzPositiveMoment σ k ≤
      alpogeNativeGzLinearUpperConstant / (σ - 1) ^ (k + 1) := by
  exact WindowLandau.weightedPositiveMoment_le_of_exp_upper
    alpogeNativeGzArithmetic_poleData (σ := σ) (α := 1)
    (B := alpogeNativeGzLinearUpperConstant) hσ (by linarith)
    alpogeNativeGzLinearUpperConstant_nonneg (by
      intro u hu
      simpa only [one_mul] using
        (le_max_left (alpogeNativeGzArithmetic (Real.exp u)) 0).trans
          (alpogeNativeGzArithmetic_posPart_le_linear (Real.exp u)
            (Real.one_le_exp hu))) k

/-- The positive part is taken after summation and exact centering.
Both historical signs remain inside the maximum. -/
theorem nativeAlpogeGz_posPart_eq_NNSHistory (N : ℕ) (hN : 1 ≤ N) :
    max (nativeAlpogeGz N) 0 = (N : ℝ) *
      max (alpogeGzNNSUpper N - alpogeGzNNSLower N +
        (harmonic N : ℝ) - Real.log (N : ℝ) +
        Real.eulerMascheroniConstant) 0 := by
  have heq : nativeAlpogeGz N = (N : ℝ) * alpogeGzNNSHistory N := by
    change alpogeErdosGz N = _
    exact alpogeGz_eq_exact_NNSHistory N hN
  change max (nativeAlpogeGz N) 0 = (N : ℝ) * max (alpogeGzNNSHistory N) 0
  rw [heq]
  by_cases h : 0 ≤ alpogeGzNNSHistory N
  · rw [max_eq_left (mul_nonneg (Nat.cast_nonneg N) h), max_eq_left h]
  · have hh : alpogeGzNNSHistory N ≤ 0 := (lt_of_not_ge h).le
    rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg N) hh),
      max_eq_right hh, mul_zero]

/-- Real positive values are controlled by the positive part of the entire
centered history at the floor, plus the already proved one-sided movement
cost. No local positive mass is substituted for the centered source. -/
theorem alpogeNativeGzArithmetic_posPart_le_floorHistory (x : ℝ) (hx : 1 ≤ x) :
    max (alpogeNativeGzArithmetic x) 0 ≤
      (⌊x⌋₊ : ℝ) * max (alpogeGzNNSHistory ⌊x⌋₊) 0 +
        nativeAlpogeSafeSlope * (x - (⌊x⌋₊ : ℝ)) := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hn : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr (by simpa using hx)
  have hgap : 0 ≤ nativeAlpogeSafeSlope * (x - (⌊x⌋₊ : ℝ)) :=
    mul_nonneg nativeAlpogeSafeSlope_nonneg (sub_nonneg.mpr (Nat.floor_le hx0))
  have hsource := alpogeNativeGzArithmetic_le_floor x hx
  have hmax : max (alpogeNativeGzArithmetic x) 0 ≤
      max (nativeAlpogeGz ⌊x⌋₊) 0 +
        nativeAlpogeSafeSlope * (x - (⌊x⌋₊ : ℝ)) :=
    max_le (hsource.trans (add_le_add (le_max_left _ _) le_rfl))
      (add_nonneg (le_max_right _ _) hgap)
  rw [nativeAlpogeGz_posPart_eq_NNSHistory ⌊x⌋₊ hn] at hmax
  exact hmax

/-- A cofinal bound on actual positive moments excludes zeta zeros to the
right of the exponent. The same `σ` and `C` work for arbitrarily high orders;
no bound on the negative part and no pointwise window premise is added. -/
theorem riemannZeta_ne_zero_of_nativeGz_positiveMoments {θ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1)
    (hM : ∃ σ : ℝ, 2 < σ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ k₀ : ℕ, ∃ k ≥ k₀,
        alpogeNativeGzPositiveMoment σ k ≤ C / (σ - θ) ^ k) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 := by
  intro s hs hz
  exact hs.not_ge (WindowLandau.landau_of_positiveMoments
    alpogeNativeGzArithmetic_poleData hθ hθ1 hM s ⟨hθ.trans hs, hz⟩)

/-- Conditional RH from positive moments of the complete native source.
Any fixed positive range of exponent losses suffices. The kernel parameter
and constant may depend on `η`, but not on the requested order `k₀`. -/
theorem riemannHypothesis_of_nativeGz_positiveMoments {η₀ : ℝ}
    (hη₀ : 0 < η₀)
    (hM : ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ σ : ℝ, 2 < σ ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∀ k₀ : ℕ, ∃ k ≥ k₀,
          alpogeNativeGzPositiveMoment σ k ≤
            C / (σ - (1 / 2 + η)) ^ k) :
    RiemannHypothesis := by
  have hright (s : ℂ) (hs : 1 / 2 < s.re) : riemannZeta s ≠ 0 := by
    by_cases h1 : 1 ≤ s.re
    · exact riemannZeta_ne_zero_of_one_le_re h1
    have hs1 : s.re < 1 := lt_of_not_ge h1
    let η := min (η₀ / 2) ((s.re - 1 / 2) / 2)
    have hη : 0 < η := by
      dsimp [η]
      exact lt_min (by linarith) (by linarith)
    have hη₀' : η < η₀ := by
      have hle : η ≤ η₀ / 2 := min_le_left _ _
      linarith
    have hηs : η ≤ (s.re - 1 / 2) / 2 := min_le_right _ _
    exact riemannZeta_ne_zero_of_nativeGz_positiveMoments
      (θ := 1 / 2 + η) (by linarith) (by linarith)
      (hM η hη hη₀') s (by linarith)
  intro s hz htriv hs1
  apply le_antisymm (le_of_not_gt fun hs => hright s hs hz)
  by_contra! hleft
  have hs0 : s ≠ 0 := by rintro rfl; norm_num [riemannZeta_zero] at hz
  have hΓ : Gammaℝ s ≠ 0 := by
    rintro hzero
    obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hzero
    cases n with
    | zero => exact hs0 (by simpa using! hn)
    | succ k => exact htriv ⟨k, by simpa [Nat.cast_succ] using! hn⟩
  have hcomp : completedRiemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs0] at hz
    exact (div_eq_zero_iff.mp hz).resolve_right hΓ
  apply hright (1 - s) (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  rw [riemannZeta_def_of_ne_zero (sub_ne_zero.mpr hs1.symm),
    completedRiemannZeta_one_sub, hcomp, zero_div]

end RHLean.Analysis

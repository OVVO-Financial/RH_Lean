import RHLean.Analysis.AlpogeThin.NativeConstructedDyadicSignedSlopePayment
import RHLean.Analysis.AlpogeNativeBoundHandoff
import RHLean.Analysis.AlpogeThin.Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions
import RHLean.Geometry.NativeSquareCapacityPeriod
import RHLean.Geometry.NativeServedPrimeApplication

/-!
# Apply the existing recovery comparison on the same selected family

This is the already present constructed dyadic payment, invoking its
proved mean-loss variant instead of demanding stronger pointwise losses.
The original consumer remains intact. The actual exponent, PairGood,
Frobenius and inertia, cutoff, height and width data, and all other
geometric fields are preserved. No new recovery inequality is proved
or postulated. The mean-loss hypotheses must be supplied by the original
local recovery and descent on that family.

The original height window also pays pointwise proximity at the original
rank parameter; no reduced rank or extra variance-recovery problem
is required. The period lemma simply applies the existing period-debt
comparison with zero debt to the original DIV premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace RHLean.Analysis.AlpogeThin

open RHLean.Geometry.AlpogeSignedSlope.Formalism.RankGapBounds.WeightedMeanData
open RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.WeightedSlopeBounds
open RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.LErr

/-- Specialize the actual terminal upstream cyclic-level source to the
primitive principal character. This is a finite arithmetic identity,
not a bound or a zero-free assertion. -/
theorem nativePrincipalCyclicGm_eq_statementOCGz (x : ℝ) :
    (Formalism.HC.Level.cyc Formalism.HC.PChar.one).Gm x =
      RHLean.Analysis.AlpogeNativeBoundHandoff.statementOCGz x := by
  classical
  let L := Formalism.HC.Level.cyc Formalism.HC.PChar.one
  have hkept : L.KEPT = {Formalism.HC.PChar.one} := by
    ext ψ
    rw [Finset.mem_singleton]
    constructor
    · intro hψ
      obtain ⟨χ, hχ, heq⟩ := (Formalism.HC.Level.mem_ofSub
        (Subgroup.zpowers Formalism.HC.PChar.one.χ) ψ).mp hψ
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hχ
      have hone : Formalism.HC.PChar.one.χ = 1 := rfl
      rw [hone, one_zpow] at hj
      rw [← hj, Formalism.HC.PChar.of_one] at heq
      exact heq.symm
    · intro hψ
      subst ψ
      exact Formalism.HC.Level.mem_cyc _
  change L.Gm x = _
  rw [Formalism.HC.Level.Gm, Formalism.HC.Level.Nt, hkept]
  simp only [Finset.erase_singleton, Finset.sum_empty, add_zero]
  rfl

/-- The complete principal cyclic source is RH_Lean's literal prime-power
source, including the Euler centering. -/
theorem nativePrincipalCyclicGm_eq (x : ℝ) :
    (Formalism.HC.Level.cyc Formalism.HC.PChar.one).Gm x =
      RHLean.Analysis.alpogeNativeGzArithmetic x :=
  (nativePrincipalCyclicGm_eq_statementOCGz x).trans
    (RHLean.Analysis.AlpogeNativeBoundHandoff.statementOCGz_eq_native x)

/-- The exact window normalization used by the published principal cyclic
application. The genuine tied-window family and its quantitative supplier
must still be supplied; this lemma only transports their existing conclusion.
It does not require an eventual bound on every real x or a new cancellation
estimate. Constants eD and eL are fixed before choosing epsilon. -/
theorem nativeSmallEpsilonWindowBound_of_principalCyclic
    (eD eL eps₁ : ℝ)
    (h : ∀ eps : ℝ, 0 < eps → eps < eps₁ →
      ∃ (S : Set ℝ) (x₁ : ℝ),
        (∀ y : ℝ, ∃ Y : ℝ, y ≤ Y ∧
          ∀ x : ℝ, Y ≤ x → x ≤ Y ^ ((3 : ℝ) / 2) → x ∈ S) ∧
        (∀ x ≥ x₁, x ∈ S →
          (Formalism.HC.Level.cyc Formalism.HC.PChar.one).Gm x ≤
            x ^ (1 / 2 + (eD + eL + 7) * eps))) :
    RHLean.Analysis.AlpogeNativeBoundHandoff.SmallEpsilonWindowBound
      (eD + eL + 7) eps₁ := by
  intro eps he he₁
  obtain ⟨S, x₁, hwin, hbound⟩ := h eps he he₁
  refine ⟨1, fun Y₀ => ?_⟩
  obtain ⟨Y, hY, hS⟩ := hwin (max Y₀ (max x₁ 1))
  refine ⟨Y, (le_max_left _ _).trans hY, fun y hy => ?_⟩
  rw [one_mul, ← nativePrincipalCyclicGm_eq_statementOCGz]
  exact hbound y
    ((le_max_left x₁ 1).trans ((le_max_right Y₀ (max x₁ 1)).trans (hY.trans hy.1)))
    (hS y hy.1 hy.2)

/-- Use the existing original signed-slope comparison with averaged
losses on precisely the original selected dyadic family. -/
theorem nativeConstructedDyadicSignedSlopePayment_of_meanLoss
    (eps A : ℝ) (he : 0 < eps) (he52 : eps < 1 / 52) (hA : 1 ≤ A) :
    ∃ (exponent : ℝ → ℕ) (Y₀ x₀ : ℝ),
      (∀ x : ℝ, x₀ ≤ x →
        UpperTheory.Top.PageN eps x (exponent x) ∧
        x ^ (2 + 8 * eps - eps / 100) ≤
            (Fintype.card (AlpogeNativeDyadicH (exponent x)) : ℝ) ∧
        (Fintype.card (AlpogeNativeDyadicH (exponent x)) : ℝ) ≤
            x ^ (2 + 8 * eps + eps / 100)) ∧
      ∀ Y : ℝ, Y₀ ≤ Y →
        ∃ (q d : ℕ) (hG : UpperTheory.Top.PairGood 1 eps Y (Y ^ A) q d),
          letI : Fact q.Prime := ⟨hG.pair.q_prime⟩
          letI : Fact d.Prime := ⟨hG.pair.d_prime⟩
          ∀ x : ℝ, x₀ ≤ x → Y ≤ x →
            let e := exponent x
            let r := alpogeNativeRecMap e q d
            let D := alpogeNativeHostData e q d
            let ell := alpogeNativeCanonicalHostEll r
            ∀ (m : ℕ) (TT T2 : Finset (AlpogeNativeDyadicH e)),
              TT.Nonempty → T2.Nonempty → 0 < m →
              ∀ (a : AlpogeNativeDyadicH e → ℝ) (b h Amax beta : ℝ)
                (w : AlpogeNativeDyadicH e → Fin m →
                  AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ),
                0 < beta → beta ≤ b → 0 ≤ h →
                Real.exp (x ^ eps) ≤ b → h ≤ Real.exp (x ^ (eps / 4)) + 1 →
                (∀ t ∈ TT, 0 < a t) → (∀ t ∈ TT, a t ≤ Amax) →
                Amax / b ≤ x + 1 →
                x ^ (-eps) ≤ alpogeNativeProjectionDensity T2 →
                (∀ u j ρ, alpogeNativeInPhi ρ → beta ≤ w u j ρ) →
                (∀ u j ρ, ρ ∈ alpogeNativeThickPositiveSites T2 u →
                  b ≤ w u j ρ ∧ w u j ρ ≤ b + h) →
                (∀ (u : (⊤ : AddSubgroup (AlpogeNativeDyadicH e))) t,
                  t ∈ TT → ∀ (j : Fin m) g,
                  g ∈ (Finset.univ.filter
                      (fun g : AlpogeNativeE0 × AlpogeNativeDyadicH e =>
                        ¬ alpogeNativeInPhi g)) \
                        alpogeNativeProjectionThickColours T2 u t →
                    Real.exp (x ^ (eps / 3)) / 3 ≤
                      a t / w u j (alpogeNativePartner t g)) →
                (∀ t ∈ TT, a t / b ∈ Set.Icc Y (Y ^ A)) →
                ∀ (f : ℕ) (W : (⊤ : AddSubgroup (AlpogeNativeDyadicH e)) → Type)
                  [∀ u, Fintype (W u)] [∀ u, Nonempty (W u)]
                  (D0 : Data (⊤ : AddSubgroup (AlpogeNativeDyadicH e)) W TT m f)
                  (eP : Fin f ≃ (alpogeNativePhiSet (AlpogeNativeDyadicH e)))
                  (C : Consts) (Xpp eK K : ℝ),
                  let Ds : Data (⊤ : AddSubgroup (AlpogeNativeDyadicH e)) W TT m f :=
                    { D0 with x := x, ε := eps, b := b }
                  let DP := AlpogeNativeSignedSlope.physicalData
                    (⊤ : AddSubgroup (AlpogeNativeDyadicH e)) TT Ds
                    D.inertia D.frob ell (Nat.ceil (Amax / beta)) a w eP
                  DP.HidaSetting C → DP.DIV C → EComp5 DP C → DP.HComp C →
                  Count5 DP C → DP.Slopes C → QuotientSlopeBoundsWith DP C Xpp →
                  DP.Losses C → DP.SlopeIneq → DP.HHBound C → DP.FParams →
                  ErrWindows DP C Xpp eK K → LargeX x eps K C.cHH eK →
                  D0.B0 ≤ 2 * (Fintype.card (AlpogeNativeDyadicH e) : ℝ) * m * b *
                    x ^ eps →
                  D0.Nc ≤ (T2.card : ℝ) * D0.k * b * x ^ eps /
                    ((Fintype.card (AlpogeNativeDyadicH e) : ℝ) *
                      ((Fintype.card (AlpogeNativeDyadicH e) : ℝ) / x ^ eps)) →
                  ((1 / (TT.card : ℝ)) * ∑ t ∈ TT,
                      alpogeNativeGzArithmetic (a t / b) ≤
                    x ^ (CErr C * eps) *
                      alpogeNativeNormalizedGeometricCosts TT.card
                        (alpogeNativeProjectionDensity T2)
                        (Fintype.card (AlpogeNativeDyadicH e)) m b D0.k D0.a
                        (x ^ eps) + x ^ ((1 : ℝ) / 2 + eps)) ∧
                  (NativeGeometricCostWindows.GeometricSizeWindows (CErr C) eps x
                      (Fintype.card (AlpogeNativeDyadicH e)) TT.card T2.card m
                      b D0.k D0.a →
                    (1 / (TT.card : ℝ)) * ∑ t ∈ TT,
                        alpogeNativeGzArithmetic (a t / b) ≤
                      x ^ ((1 : ℝ) / 2 + (CErr C + 3) * eps)) := by
  obtain ⟨exponent, Y₀, x₀, hsize, hsource⟩ :=
    nativeConstructedDyadicGzPayment eps A he he52 hA
  refine ⟨exponent, Y₀, x₀, hsize, ?_⟩
  intro Y hY
  obtain ⟨q, d, hG, hpaid⟩ := hsource Y hY
  refine ⟨q, d, hG, ?_⟩
  let : Fact q.Prime := ⟨hG.pair.q_prime⟩
  let : Fact d.Prime := ⟨hG.pair.d_prime⟩
  intro x hx hYx
  dsimp only
  intro m TT T2 hTT hT2 hm a b h Amax beta w
    hbeta hbetab hh hb hupper ha hAmax hmax hdensity hwbeta hwthick hwthin hwindow
    f W _ _ D0 eP C Xpp eK K
    hS hDIV hE hH hCount hSl hSN hLoss hSI hHH hFP hWin hLarge hB0 hNc
  let Ds : Data (⊤ : AddSubgroup (AlpogeNativeDyadicH (exponent x))) W TT m f :=
    { D0 with x := x, ε := eps, b := b }
  have hgeom := AlpogeNativeSignedSlope.physicalTopExcess_div_le_normalizedGeometricCosts_of_meanLoss
    (⊤ : AddSubgroup (AlpogeNativeDyadicH (exponent x))) TT Ds
    (alpogeNativeHostData (exponent x) q d).inertia
    (alpogeNativeHostData (exponent x) q d).frob
    (alpogeNativeCanonicalHostEll (alpogeNativeRecMap (exponent x) q d))
    (Nat.ceil (Amax / beta)) a w eP C Xpp
    hS hDIV hE hH hCount hSl hSN hLoss hSI hHH hFP eK K hWin hLarge
    T2 hTT hT2 hm hB0 hNc
  have hanalytic := hpaid x hx hYx m TT T2 hTT hT2 hm a b h Amax beta w
    hbeta hbetab hh hb hupper ha hAmax hmax hdensity hwbeta hwthick hwthin hwindow
  have hfull := hanalytic.trans (add_le_add hgeom le_rfl)
  refine ⟨hfull, ?_⟩
  intro hSize
  exact hfull.trans (NativeGeometricCostWindows.normalizedCosts_add_analytic_le
    (CErr C) eps x TT T2 m b D0.k D0.a hSize)

/-- InWin uses a height interval of length a/(k*sigma), with a=x*b and
sigma=x^(Scale.A/2). At the original admissible k>=x, sigma>=1, this
gives the actual pointwise height proximity used by the existing
analytic payment. No variance or smaller-rank recovery is required. -/
theorem nativeOriginalHeightWindow (x b k sigma h : ℝ)
    (hx : 0 < x) (hb : 0 < b) (hk : x ≤ k) (hsigma : 1 ≤ sigma)
    (hlo : x * b ≤ h) (hhi : h ≤ x * b + x * b / (k * sigma)) :
    x ≤ h / b ∧ h / b ≤ x + 1 ∧ |h / b - x| ≤ 1 := by
  have hk0 : 0 < k := hx.trans_le hk
  have hs0 : 0 < sigma := by linarith
  have hden : 0 < k * sigma := mul_pos hk0 hs0
  have hprod : x ≤ k * sigma :=
    hk.trans (by nlinarith only [mul_nonneg hk0.le (sub_nonneg.mpr hsigma)])
  have hsmall : x * b / (k * sigma) ≤ b := by
    apply (div_le_iff₀ hden).2
    nlinarith only [mul_le_mul_of_nonneg_right hprod hb.le]
  have hlo' := (le_div_iff₀ hb).2 hlo
  have hhi' : h / b ≤ x + 1 := by
    apply (div_le_iff₀ hb).2
    nlinarith only [hhi, hsmall]
  exact ⟨hlo', hhi', by rw [abs_of_nonneg (sub_nonneg.mpr hlo')]; linarith⟩

end RHLean.Analysis.AlpogeThin

namespace RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.WeightedSlopeBounds

open RHLean.Geometry.AlpogeSignedSlope.Formalism.RankGapBounds.WeightedMeanData

/-- The already-proved one-sided period-debt theorem, with debt zero,
directly supplies the DIV premise. No exact period equality is needed. -/
theorem nativeDIV_of_period_lower
    {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ}
    (D : Data U0 W Top m f) (C : Consts)
    (P : (u : U0) → W u → ℝ) (ha : ∀ t, 0 ≤ D.aT t)
    (hP : ∀ u v, D.logOm ≤ P u v)
    (hDegree : ∀ u (v : W u), D.muCC u + D.h u v - D.Fo u ≤
      (∑ t, ((m : ℝ) * (ph (D.aT t) - D.aT t * P u v) -
        D.aT t * Real.log (D.T u v))) + D.EDiv C) : D.DIV C := by
  intro u v
  have h := nativeDivisorDebt_of_period_lower D C P 0 ha
    (fun u v => by simpa only [sub_zero] using hP u v) hDegree u v
  simpa only [mul_zero, add_zero, Data.SDiv, Data.sumA, Data.EDiv,
    Finset.sum_sub_distrib, Finset.sum_mul, ← add_assoc] using h

end RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.WeightedSlopeBounds

end

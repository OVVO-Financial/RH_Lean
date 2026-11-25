import RHLean.Analysis.AlpogeThin.NativeConstructedDyadicSignedSlopePayment
import RHLean.Analysis.AlpogeNativeThickFreezing
import RHLean.Analysis.AlpogeThin.NativeScalarSupplierPayment
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
  simpa only [Finset.erase_singleton, Finset.sum_empty, add_zero] using
    (show Formalism.Gz x = RHLean.Analysis.AlpogeNativeBoundHandoff.statementOCGz x from rfl)

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

set_option maxHeartbeats 1800000 in
/-- The pointwise discrepancy ledger on the selected arithmetic host. All eligible
profiles use their original cutoff and divisor. The comparison widths are computed
from the supplied widths. Original-window heights pay a single movement constant. -/
theorem nativeConstructedDyadicDiscrepancyLedger
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
                1 ≤ x → (∀ t ∈ TT, x ≤ a t / b) →
                let η := b * alpogeNativeProjectionDensity T2 * Real.sqrt x / (2 * Amax)
                alpogeNativeGzArithmetic x ≤
                  alpogeNativePhysicalSubgroupTopExcess
                      (⊤ : AddSubgroup (AlpogeNativeDyadicH e))
                      D.inertia D.frob ell (Nat.ceil (Amax / beta)) TT a
                      (fun u j ρ => alpogeNativeLowerLogWidth η (w u j ρ)) /
                    alpogeNativeProjectionDivisor TT T2 m b +
                  (alpogeNativeMoveConstant + x ^ ((1 : ℝ) / 2 + eps) + Real.sqrt x) := by
  classical
  obtain ⟨exponent, Y₀, x₀, hHost, hPair⟩ := nativeConstructedDyadicGzPayment eps A he he52 hA
  refine ⟨exponent, Y₀, x₀, hHost, ?_⟩
  intro Y hY
  obtain ⟨q, d, hG, hPaid⟩ := hPair Y hY
  refine ⟨q, d, hG, ?_⟩
  letI : Fact q.Prime := ⟨hG.pair.q_prime⟩
  letI : Fact d.Prime := ⟨hG.pair.d_prime⟩
  intro x hx hYx
  dsimp only
  intro m TT T2 hTT hT2 hm a b h Amax beta w hbeta hbetab hh hbexp hupper ha
    haMax hmax hDensity hwBeta hwThick hwThin hWindow hx1 hLower
  have hAnalytic := hPaid x hx hYx m TT T2 hTT hT2 hm a b h Amax beta w
    hbeta hbetab hh hbexp hupper ha haMax hmax hDensity hwBeta hwThick hwThin hWindow
  have hb : 0 < b := hbeta.trans_le hbetab
  obtain ⟨t₀, ht₀⟩ := hTT
  have hAmax := (ha t₀ ht₀).trans_le (haMax t₀ ht₀)
  have hδ : 0 < alpogeNativeProjectionDensity T2 := by
    unfold alpogeNativeProjectionDensity
    exact div_pos (by exact_mod_cast hT2.card_pos) (by exact_mod_cast Fintype.card_pos)
  let η := b * alpogeNativeProjectionDensity T2 * Real.sqrt x / (2 * Amax)
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hη : 0 < η := div_pos (mul_pos (mul_pos hb hδ) (Real.sqrt_pos.2 hxpos)) (by positivity)
  have hGrid := alpogeNativePhysicalSubgroupTopExcess_logGrid_le
    (⊤ : AddSubgroup (AlpogeNativeDyadicH (exponent x)))
    (alpogeNativeHostData (exponent x) q d).inertia (alpogeNativeHostData (exponent x) q d).frob
    (alpogeNativeCanonicalHostEll (alpogeNativeRecMap (exponent x) q d))
    (Nat.ceil (Amax / beta)) m TT T2 a Amax b η w ⟨t₀, ht₀⟩ hT2 hm hb hη
    (fun t ht => ⟨(ha t ht).le, haMax t ht⟩)
    (fun u j ρ hρ => hbeta.trans_le (hwBeta u j ρ hρ))
  have hPrice : 2 * Amax * η / (b * alpogeNativeProjectionDensity T2) = Real.sqrt x := by
    dsimp [η]
    field_simp [hb.ne', hδ.ne', hAmax.ne'] <;> ring
  rw [hPrice] at hGrid
  have hPoint := alpogeNativeGzArithmetic_le_mean_add_move TT ⟨t₀, ht₀⟩ x
    (fun t => a t / b) hx1 (fun t ht => hx1.trans (hLower t ht))
  have hSum := Finset.sum_le_sum (s := TT) (g := fun _ => (1 : ℝ))
    (fun t ht => (show |x - a t / b| ≤ 1 by
      rw [abs_of_nonpos (sub_nonpos.mpr (hLower t ht))]
      have hu := (div_le_div_of_nonneg_right (haMax t ht) hb.le).trans hmax
      linarith))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hSum
  have hTT' : TT.Nonempty := ⟨t₀, ht₀⟩
  have hCard : (0 : ℝ) < TT.card := by exact_mod_cast hTT'.card_pos
  have hMeanMove : (1 / (TT.card : ℝ)) * ∑ t ∈ TT, |x - a t / b| ≤ 1 := by
    rw [one_div, ← div_eq_inv_mul]
    exact (div_le_iff₀ hCard).2 (by simpa using hSum)
  have hMove := mul_le_mul_of_nonneg_left hMeanMove alpogeNativeMoveConstant_nonneg
  dsimp only [η] at hGrid
  dsimp only at hAnalytic hPoint ⊢
  linarith only [hPoint, hAnalytic, hGrid, hMove]

/-- Uniform normalized price of the three discrepancy entries. -/
theorem nativeDiscrepancyPrice_le (x eps : ℝ) (hx : 1 ≤ x) (he : 0 ≤ eps) :
    alpogeNativeMoveConstant + x ^ ((1 : ℝ) / 2 + eps) + Real.sqrt x ≤
      (alpogeNativeMoveConstant + 2) * x ^ ((1 : ℝ) / 2 + eps) := by
  have h1 : 1 ≤ x ^ ((1 : ℝ) / 2 + eps) := Real.one_le_rpow hx (by linarith)
  have hs : Real.sqrt x ≤ x ^ ((1 : ℝ) / 2 + eps) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hc := mul_le_mul_of_nonneg_left h1 alpogeNativeMoveConstant_nonneg
  linarith only [hs, hc]

/-- At square-clock rank `k = x * R`, the original height window contains
at most one integer when `b < R * sigma`. In that range, varying the
integral top heights on this fixed window supplies no additional direction. -/
theorem nativeSquareClock_integerHeights_eq (x b R sigma : ℝ)
    (hx : 0 < x) (hR : 0 < R) (hsigma : 0 < sigma) (hb : b < R * sigma)
    (h₁ h₂ : ℤ)
    (hw₁ : (h₁ : ℝ) ∈ Set.Icc (x * b) (x * b + x * b / (x * R * sigma)))
    (hw₂ : (h₂ : ℝ) ∈ Set.Icc (x * b) (x * b + x * b / (x * R * sigma))) :
    h₁ = h₂ := by
  have hw : x * b / (x * R * sigma) < 1 := by
    apply (div_lt_one (mul_pos (mul_pos hx hR) hsigma)).2
    rw [mul_assoc]
    exact mul_lt_mul_of_pos_left hb hx
  have hlt₁ : (h₁ : ℝ) < (h₂ : ℝ) + 1 := by linarith only [hw₁.2, hw₂.1, hw]
  have hlt₂ : (h₂ : ℝ) < (h₁ : ℝ) + 1 := by linarith only [hw₂.2, hw₁.1, hw]
  have hi₁ : h₁ < h₂ + 1 := by exact_mod_cast hlt₁
  have hi₂ : h₂ < h₁ + 1 := by exact_mod_cast hlt₂
  omega

open Filter in
/-- With the original exponential width and `Scale.A = 26`, the ceiling
of the prescribed lower endpoint is an admissible integer height and
has the required pointwise proximity, uniformly for `1 ≤ R ≤ x`. -/
theorem nativeSquareClock_ceilHeight_eventually (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, ∀ R : ℝ, 1 ≤ R → R ≤ x →
      let b := Real.exp (x ^ eps)
      let a := x * b
      let h : ℝ := (⌈a⌉ : ℤ)
      h ∈ Set.Icc a (a + a / (x * R * x ^ (13 : ℕ))) ∧ |h / b - x| ≤ 1 := by
  filter_upwards [dyadic_rpow_le_exp_eventually ((14 : ℕ) : ℝ) eps heps,
    eventually_ge_atTop (1 : ℝ)] with x hb hx1
  rw [Real.rpow_natCast] at hb
  intro R hR hRx
  let b := Real.exp (x ^ eps)
  let a := x * b
  let h : ℝ := (⌈a⌉ : ℤ)
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hs : 1 ≤ x ^ (13 : ℕ) := one_le_pow₀ hx1
  have hden : 0 < x * R * x ^ (13 : ℕ) :=
    mul_pos (mul_pos hx (zero_lt_one.trans_le hR)) (zero_lt_one.trans_le hs)
  have hscale : R * x ^ (13 : ℕ) ≤ b := calc
    R * x ^ (13 : ℕ) ≤ x * x ^ (13 : ℕ) :=
      mul_le_mul_of_nonneg_right hRx (pow_nonneg hx.le _)
    _ = x ^ (14 : ℕ) := by ring
    _ ≤ b := hb
  have hwidth : 1 ≤ a / (x * R * x ^ (13 : ℕ)) := by
    apply (le_div_iff₀ hden).2
    rw [one_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hscale hx.le
  have hw : h ∈ Set.Icc a (a + a / (x * R * x ^ (13 : ℕ))) :=
    ⟨Int.le_ceil a, (Int.ceil_lt_add_one a).le.trans (add_le_add (le_refl a) hwidth)⟩
  exact ⟨hw, (nativeOriginalHeightWindow x b (x * R) (x ^ (13 : ℕ)) h hx
    (Real.exp_pos _) (le_mul_of_one_le_right hx.le hR) hs hw.1 hw.2).2.2⟩

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

import RHLean.Analysis.AlpogeThin.NativeConstructedDyadicSignedSlopePayment
import RHLean.Analysis.AlpogeThin.NativeDyadicRamifiedWindow
import RHLean.Analysis.AlpogeNativeThickFreezing
import RHLean.Analysis.AlpogeNativeProperPowerCentering
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

private theorem pointwise_le_signedComparison
    {point mean physical comparison move moveCost analytic width : ℝ}
    (hPoint : point ≤ mean + move) (hMean : mean ≤ physical + analytic)
    (hPhysical : physical ≤ comparison + width) (hMove : move ≤ moveCost) :
    point ≤ comparison + (moveCost + analytic + width) := by
  linarith

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
  let : Fact q.Prime := ⟨hG.pair.q_prime⟩
  let : Fact d.Prime := ⟨hG.pair.d_prime⟩
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
    field_simp [hb.ne', hδ.ne', hAmax.ne']
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
  exact pointwise_le_signedComparison hPoint hAnalytic hGrid
    (by simpa only [mul_one] using hMove)

/-- Compl3-style sparse comparison on the SAME selected pair, heights,
Frobenius/inertia, cutoff, and physical width profile. Freeze precisely
the thick sites; leave the signed thin return and all other data intact.
This is a transfer estimate, not a bound on the frozen signed source. -/
theorem nativeConstructedDyadicFrozenDiscrepancyLedger
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
                alpogeNativeGzArithmetic x ≤
                  alpogeNativePhysicalSubgroupTopExcess
                      (⊤ : AddSubgroup (AlpogeNativeDyadicH e))
                      D.inertia D.frob ell (Nat.ceil (Amax / beta)) TT a
                      (fun u j => alpogeNativeFreezeThick T2 u b (w u j)) /
                    alpogeNativeProjectionDivisor TT T2 m b +
                  (alpogeNativeMoveConstant + x ^ ((1 : ℝ) / 2 + eps) +
                   (Amax / b) * (h / b)) := by
  classical
  obtain ⟨exponent, Y₀, x₀, hHost, hPair⟩ := nativeConstructedDyadicGzPayment eps A he he52 hA
  refine ⟨exponent, Y₀, x₀, hHost, ?_⟩
  intro Y hY
  obtain ⟨q, d, hG, hPaid⟩ := hPair Y hY
  refine ⟨q, d, hG, ?_⟩
  let : Fact q.Prime := ⟨hG.pair.q_prime⟩
  let : Fact d.Prime := ⟨hG.pair.d_prime⟩
  intro x hx hYx
  dsimp only
  intro m TT T2 hTT hT2 hm a b h Amax beta w hbeta hbetab hh hbexp hupper ha
    haMax hmax hDensity hwBeta hwThick hwThin hWindow hx1 hLower
  have hAnalytic := hPaid x hx hYx m TT T2 hTT hT2 hm a b h Amax beta w
    hbeta hbetab hh hbexp hupper ha haMax hmax hDensity hwBeta hwThick hwThin hWindow
  have hb : 0 < b := hbeta.trans_le hbetab
  obtain ⟨t₀, ht₀⟩ := hTT
  have hFreeze := alpogeNativePhysicalSubgroupTopExcess_freezeThick_upper_le
    (⊤ : AddSubgroup (AlpogeNativeDyadicH (exponent x)))
    (alpogeNativeHostData (exponent x) q d).inertia
    (alpogeNativeHostData (exponent x) q d).frob
    (alpogeNativeCanonicalHostEll (alpogeNativeRecMap (exponent x) q d))
    (Nat.ceil (Amax / beta)) m TT T2 a Amax b h w
    ⟨t₀, ht₀⟩ hT2 hm hb hh (fun t ht => ⟨(ha t ht).le, haMax t ht⟩) hwThick
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
  exact pointwise_le_signedComparison hPoint hAnalytic hFreeze
    (by simpa only [mul_one] using hMove)

open Filter in
/-- The sparse thick-width comparison charge is at most 1/x eventually,
uniformly over all admissible widths and heights. Use the proved cost window
at e=0, K=0: this numerical specialization does not alter the selected
physical host in the comparison theorem. -/
theorem nativeFrozenWidthPrice_eventually (eps : ℝ) (he : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, ∀ A b h : ℝ,
      Real.exp (x ^ eps) ≤ b → 0 ≤ h →
      h ≤ Real.exp (x ^ (eps / 4)) + 1 → A / b ≤ x + 1 →
      (A / b) * (h / b) ≤ 1 / x := by
  have hW := nativeDyadicCostWindows_eventually eps 0 he
  filter_upwards [hW, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  intro A b h hb hh hupper hmax
  have hbpos := (Real.exp_pos (x ^ eps)).trans_le hb
  have hxpos : 0 < x := by linarith
  have hcost := (hx 0 (by simp) b h hb hh hupper).2
  norm_num at hcost
  have hnon : 0 ≤ (x + 1) * h := mul_nonneg (by linarith) hh
  have hsmall : (x + 1) * h ≤ b / x := by nlinarith only [hcost, hnon]
  calc
    _ ≤ (x + 1) * (h / b) := mul_le_mul_of_nonneg_right hmax (div_nonneg hh hbpos.le)
    _ = ((x + 1) * h) / b := by ring
    _ ≤ (b / x) / b := div_le_div_of_nonneg_right hsmall hbpos.le
    _ = 1 / x := by field_simp [hbpos.ne', hxpos.ne']

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

open Filter in
/-- Consecutive integers realize distinct heights on the whole dyadic host
at the original exponential width. Their logs price divisibility exceptions
on the same profile uniformly throughout the square-clock collar. -/
theorem nativeSquareClock_injectiveHeights_log_eventually (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, ∀ (e : ℕ) (R : ℝ), 1 ≤ R → R ≤ x →
      (Fintype.card (AlpogeNativeDyadicH e) : ℝ) ≤ x^3 →
      let b := Real.exp (x^eps)
      ∃ a : AlpogeNativeDyadicH e → ℕ, Function.Injective a ∧ ∀ t,
        0 < a t ∧ (a t : ℝ) ∈ Set.Ico (x*b) (x*b + x*b/(x*R*x^13)) ∧
        (a t : ℝ) ≤ (x+1)*b ∧ Real.log (a t : ℝ) ≤ x^eps + Real.log (x+1) := by
  filter_upwards [dyadic_rpow_le_exp_eventually ((17 : ℕ) : ℝ) eps heps,
    eventually_ge_atTop (1 : ℝ)] with x hscale hx
  rw [Real.rpow_natCast] at hscale
  intro e R hR hRx hcard
  let b := Real.exp (x^eps)
  have hb : 0 < b := Real.exp_pos _
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hden : 0 < x*R*x^13 := by positivity
  have hroom : (Fintype.card (AlpogeNativeDyadicH e) : ℝ) ≤ x*b/(x*R*x^13) := by
    apply hcard.trans ((le_div_iff₀ hden).2 ?_)
    calc
      _ = (x*x^16)*R := by ring
      _ ≤ (x*x^16)*x := mul_le_mul_of_nonneg_left hRx (by positivity)
      _ = x*x^17 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hscale hx0.le
  have hcap : x*b/(x*R*x^13) ≤ b := by
    apply (div_le_iff₀ hden).2
    have h1 : 1 ≤ R*x^13 := one_le_mul_of_one_le_of_one_le hR (one_le_pow₀ hx)
    calc
      _ ≤ (x*b)*(R*x^13) := le_mul_of_one_le_right (by positivity) h1
      _ = _ := by ring
  let ix := Fintype.equivFin (AlpogeNativeDyadicH e)
  let a := fun t => ⌈x*b⌉₊ + (ix t).val
  refine ⟨a, fun i j hij => ix.injective (Fin.ext (Nat.add_left_cancel hij)), fun t => ?_⟩
  have hcast : (a t : ℝ) = (⌈x*b⌉₊ : ℝ) + ((ix t).val : ℝ) := by simp [a]
  have hidx : ((ix t).val : ℝ)+1 ≤ Fintype.card (AlpogeNativeDyadicH e) := by
    exact_mod_cast Nat.succ_le_of_lt (ix t).isLt
  have hlow : x*b ≤ (a t : ℝ) := by
    rw [hcast]
    exact (Nat.le_ceil (x*b)).trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
  have hhigh : (a t : ℝ) < x*b + x*b/(x*R*x^13) := by
    linarith only [hcast, Nat.ceil_lt_add_one (mul_nonneg hx0.le hb.le), hidx, hroom]
  have ha : 0 < (a t : ℝ) := (mul_pos hx0 hb).trans_le hlow
  have hmax : (a t : ℝ) ≤ (x+1)*b := by linarith only [hhigh, hcap]
  refine ⟨by exact_mod_cast ha, ⟨hlow, hhigh⟩, hmax, (Real.log_le_log ha hmax).trans_eq ?_⟩
  rw [Real.log_mul (by positivity) hb.ne', show Real.log b = x^eps from Real.log_exp _]
  ring

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

namespace RHLean.Analysis

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

/-- In the physical ASK row keep the original cut on first primes above z.
Every other site keeps its actual Fourier-inverted mass and linear height
term, including at ramified primes and at the original upper cutoff. -/
noncomputable def alpogeNativeFirstPrimeWidthASK
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H)) (frob : ℕ → AlpogeNativeE0 × H)
    (N z : ℕ) (a : ℝ) (t : H) (w : AlpogeNativeE0 × H → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    ∑ g ∈ Finset.univ.filter (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g),
      alpogeNativeASKRealWeight inertia frob n g *
        (if n.Prime ∧ z < n then alpogeASKPos (a / (n : ℝ)) (w (alpogeNativePartner t g))
         else a / (n : ℝ))

/-- Exact large-prime saving on the same measured row. Together with the
normalized error estimate this identifies the remaining one-sided target. -/
theorem alpogeNativeFirstPrimeWidthASK_eq_linear_sub_saving
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H)) (frob : ℕ → AlpogeNativeE0 × H)
    (N z : ℕ) (a : ℝ) (t : H) (w : AlpogeNativeE0 × H → ℝ) :
    let G := Finset.univ.filter (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g)
    alpogeNativeFirstPrimeWidthASK inertia frob N z a t w =
      (∑ n ∈ Finset.Icc 1 N, ∑ g ∈ G, alpogeNativeASKRealWeight inertia frob n g * (a / n)) -
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => n.Prime ∧ z < n), ∑ g ∈ G,
        alpogeNativeASKRealWeight inertia frob n g * min (a / n) (w (alpogeNativePartner t g)) := by
  dsimp only
  rw [alpogeNativeFirstPrimeWidthASK, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n.Prime ∧ z < n
  · have hcut (u v : ℝ) : alpogeASKPos u v = u - min u v := by
      rcases le_total u v with h | h
      · rw [alpogeASKPos, max_eq_right (sub_nonpos.mpr h), min_eq_left h, sub_self]
      · rw [alpogeASKPos, max_eq_left (sub_nonneg.mpr h), min_eq_right h]
    simp only [ite_eq_left hn, ← Finset.sum_sub_distrib, ← mul_sub, hcut]
  · simp [hn]

/-- Uniform signed cost of removing the width dependence from all proper
powers and the first primes up to z, including every repeated partner. -/
theorem alpogeNativeFirstPrimeWidthASK_error :
    ∃ K : ℝ, 0 ≤ K ∧
    ∀ (H : Type*) [AddCommGroup H] [Fintype H] [DecidableEq H]
      (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H)) (frob : ℕ → AlpogeNativeE0 × H)
      (N M z : ℕ) (a B : ℝ) (t : H) (w : AlpogeNativeE0 × H → ℝ),
      1 ≤ M → 0 ≤ a → 0 ≤ B → a ≤ B * M →
      (∀ g, ¬ alpogeNativeInPhi g → w (alpogeNativePartner t g) ∈ Set.Icc 0 B) →
      alpogeNativeFirstPrimeWidthASK inertia frob N z a t w -
        (alpogeNativeFullKernelASK inertia frob N a t w).re ∈
          Set.Icc 0 (2 * B * (K * Real.sqrt M + (Real.log 4 + 2) * z)) := by
  obtain ⟨K, hK, hproper⟩ := nativeProperPower_clippedMass_le
  refine ⟨K, hK, ?_⟩
  intro H _ _ _ inertia frob N M z a B t w hM ha hB haM hw
  let price (n : ℕ) : ℝ :=
    if n.Prime then (if n ≤ z then 1 else 0) else min ((M : ℝ) / n) 1
  let cut (n : ℕ) (g : AlpogeNativeE0 × H) :=
    alpogeASKPos (a / (n : ℝ)) (w (alpogeNativePartner t g))
  let diff (n : ℕ) (g : AlpogeNativeE0 × H) :=
    (if n.Prime ∧ z < n then cut n g else a / (n : ℝ)) - cut n g
  let G := Finset.univ.filter (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g)
  let I := Finset.Icc 1 N
  have hprice (n : ℕ) : 0 ≤ price n := by
    dsimp [price]
    split_ifs <;> positivity
  have hd (n : ℕ) (g : AlpogeNativeE0 × H) (hg : g ∈ G) :
      diff n g ∈ Set.Icc 0 (B * price n) := by
    obtain ⟨hw0, hwB⟩ := hw g (Finset.mem_filter.mp hg).2
    have hz : 0 ≤ a / (n : ℝ) := div_nonneg ha (Nat.cast_nonneg _)
    have hlo : 0 ≤ a / (n : ℝ) - cut n g :=
      sub_nonneg.mpr (max_le (sub_le_self _ hw0) hz)
    have hup : a / (n : ℝ) - cut n g ≤ B := by
      have h := le_max_left (a / (n : ℝ) - w (alpogeNativePartner t g)) 0
      change a / (n : ℝ) - max _ 0 ≤ B
      linarith
    have hheight : a / (n : ℝ) - cut n g ≤ B * ((M : ℝ) / n) := by
      calc
        _ ≤ a / (n : ℝ) := sub_le_self _ (le_max_right _ _)
        _ ≤ (B * M) / n := div_le_div_of_nonneg_right haM (Nat.cast_nonneg n)
        _ = _ := by ring
    by_cases hp : n.Prime
    · by_cases hn : n ≤ z
      · simpa [Set.mem_Icc, diff, price, hp, hn, not_lt.mpr hn] using And.intro hlo hup
      · simp [diff, price, hp, hn, lt_of_not_ge hn]
    · simp only [diff, price, hp, false_and, ↓reduceIte, Set.mem_Icc]
      refine ⟨hlo, ?_⟩
      rcases le_total ((M : ℝ) / n) 1 with h | h
      · rwa [min_eq_left h]
      · simpa [min_eq_right h] using hup
  have heq : alpogeNativeFirstPrimeWidthASK inertia frob N z a t w -
      (alpogeNativeFullKernelASK inertia frob N a t w).re =
      ∑ n ∈ I, ∑ g ∈ G, alpogeNativeASKRealWeight inertia frob n g * diff n g := by
    rw [alpogeNativeFirstPrimeWidthASK, alpogeNativeFullKernelASK_re_eq_weighted,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    simp only [G, diff, cut, mul_sub, Finset.sum_sub_distrib]
  have hlow : (∑ n ∈ I, if n ≤ z then Λ n else 0) ≤ nativePsi z := by
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      obtain ⟨hnI, hnz⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hnI).1, hnz⟩
    · intro n _ _
      exact ArithmeticFunction.vonMangoldt_nonneg
  have hmass : ∑ n ∈ I, Λ n * price n ≤ K * Real.sqrt M + (Real.log 4 + 2) * z := by
    calc
      _ ≤ ∑ n ∈ I, (nativeProperPowerAtom n * min ((M : ℝ) / n) 1 +
          (if n ≤ z then Λ n else 0)) := by
        apply Finset.sum_le_sum
        intro n _
        by_cases hp : n.Prime <;> by_cases hn : n ≤ z <;>
          simp [price, nativeProperPowerAtom, hp, hn, ArithmeticFunction.vonMangoldt_nonneg]
      _ ≤ _ := by
        rw [Finset.sum_add_distrib]
        exact add_le_add (hproper M N hM) (hlow.trans (nativePsi_le_const_mul z))
  rw [heq]
  constructor
  · exact Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun g hg =>
      mul_nonneg (alpogeNativeASKRealWeight_nonneg inertia frob n g) (hd n g hg).1
  · calc
      _ ≤ ∑ n ∈ I, (2 * B) * (Λ n * price n) := by
        apply Finset.sum_le_sum
        intro n _
        calc
          _ ≤ ∑ g ∈ G, alpogeNativeASKRealWeight inertia frob n g * (B * price n) :=
            Finset.sum_le_sum fun g hg => mul_le_mul_of_nonneg_left (hd n g hg).2
              (alpogeNativeASKRealWeight_nonneg inertia frob n g)
          _ = (∑ g ∈ G, alpogeNativeASKRealWeight inertia frob n g) * (B * price n) :=
            (Finset.sum_mul _ _ _).symm
          _ ≤ (2 * Λ n) * (B * price n) := mul_le_mul_of_nonneg_right
            (alpogeNativeASKRealWeight_sum_le_two_lambda inertia frob n) (mul_nonneg hB (hprice n))
          _ = _ := by ring
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left hmass (by positivity)

/-- The price after the actual top, row and translate sums is independent of
their multiplicities. MAIN is evaluated on the original row throughout. -/
theorem alpogeNativeFirstPrimeWidth_normalized_error :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (H : Type*) [AddCommGroup H] [Fintype H] [DecidableEq H]
      (A0 : AddSubgroup H)
      (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H)) (frob : ℕ → AlpogeNativeE0 × H)
      (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ) (N M z m : ℕ)
      (TT T2 : Finset H) (a : H → ℝ) (b B : ℝ)
      (w : H → Fin m → AlpogeNativeE0 × H → ℝ),
      TT.Nonempty → T2.Nonempty → 0 < m → 0 < b → 0 ≤ B → 1 ≤ M →
      (∀ t ∈ TT, 0 ≤ a t ∧ a t ≤ B * M) →
      (∀ (u : A0) j t, t ∈ TT → ∀ g, ¬ alpogeNativeInPhi g →
        w u j (alpogeNativePartner t g) ∈ Set.Icc 0 B) →
      let centered := (1 / (Fintype.card A0 : ℝ)) * ∑ u : A0, ∑ t ∈ TT, ∑ j : Fin m,
        (alpogeNativeFirstPrimeWidthASK inertia frob N z (a t) t (w u j) -
         (alpogeNativeMAIN ell (a t) (w u j)).re)
      (centered - alpogeNativePhysicalSubgroupTopExcess A0 inertia frob ell N TT a w) /
        alpogeNativeProjectionDivisor TT T2 m b ∈
          Set.Icc 0 (4 * B / (b * alpogeNativeProjectionDensity T2) *
            (K * Real.sqrt M + (Real.log 4 + 2) * z)) := by
  obtain ⟨K, hK, hrow⟩ := alpogeNativeFirstPrimeWidthASK_error
  refine ⟨K, hK, ?_⟩
  intro H _ _ _ A0 inertia frob ell N M z m TT T2 a b B w hTT hT2 hm hb hB hM ha hw
  let D (u : A0) (t : H) (j : Fin m) :=
    alpogeNativeFirstPrimeWidthASK inertia frob N z (a t) t (w u j) -
      (alpogeNativeFullKernelASK inertia frob N (a t) t (w u j)).re
  let C := K * Real.sqrt M + (Real.log 4 + 2) * z
  have hd (u : A0) (t : H) (ht : t ∈ TT) (j : Fin m) : D u t j ∈ Set.Icc 0 (2 * B * C) :=
    hrow H inertia frob N M z (a t) B t (w u j) hM (ha t ht).1 hB (ha t ht).2 (hw u j t ht)
  have hu : (0 : ℝ) < Fintype.card A0 := by exact_mod_cast Fintype.card_pos
  have ht : (0 : ℝ) < TT.card := by exact_mod_cast hTT.card_pos
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hDelta : 0 < alpogeNativeProjectionDensity T2 :=
    div_pos (by exact_mod_cast hT2.card_pos) (by exact_mod_cast Fintype.card_pos)
  have hQ := alpogeNativeProjectionDivisor_pos TT T2 hTT hT2 m hm b hb
  have hlo : 0 ≤ ∑ u : A0, ∑ t ∈ TT, ∑ j : Fin m, D u t j :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun t ht' =>
      Finset.sum_nonneg fun j _ => (hd u t ht' j).1
  have hup : (∑ u : A0, ∑ t ∈ TT, ∑ j : Fin m, D u t j) ≤
      ∑ _u : A0, ∑ _t ∈ TT, ∑ _j : Fin m, (2 * B * C) :=
    Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun t ht' =>
      Finset.sum_le_sum fun j _ => (hd u t ht' j).2
  dsimp only
  unfold alpogeNativePhysicalSubgroupTopExcess
  simp only [Complex.sub_re, ← mul_sub, ← Finset.sum_sub_distrib, sub_sub_sub_cancel_right]
  change (1 / (Fintype.card A0 : ℝ) * (∑ u : A0, ∑ t ∈ TT, ∑ j : Fin m, D u t j)) /
    alpogeNativeProjectionDivisor TT T2 m b ∈ Set.Icc 0 _
  constructor
  · exact div_nonneg (mul_nonneg (one_div_nonneg.mpr hu.le) hlo) hQ.le
  · refine (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hup (one_div_nonneg.mpr hu.le)) hQ.le).trans_eq ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp only [alpogeNativeProjectionDivisor, C]
    field [hu.ne', ht.ne', hm'.ne', hb.ne', hDelta.ne']

/-- Below X'/(x+1)^2 the thin sites contribute negligible first-prime
savings, even when their widths depend on the lift and on the row. The
factor 2/(b*delta) is the original divisor for a single averaged row. -/
theorem alpogeNativeThinFirstPrime_saving_le
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H)) (frob : ℕ → AlpogeNativeE0 × H)
    (N T z : ℕ) (T2 : Finset H) (u t : H) (w : AlpogeNativeE0 × H → ℝ)
    (a b x X' η δ : ℝ) (hx : 1 ≤ x) (hb : 0 < b) (hX : 0 < X') (hη : 0 < η)
    (hδ : 0 < δ) (ha : a / b ≤ x + 1) (hT : (T : ℝ) * (x + 1)^2 ≤ X')
    (hthin : ∀ g ∈ (Finset.univ.filter (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g)) \
        alpogeNativeProjectionThickColours T2 u t,
      0 < w (alpogeNativePartner t g) ∧ X' / 3 ≤ a / w (alpogeNativePartner t g)) :
    let thin := (Finset.univ.filter (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g)) \
      alpogeNativeProjectionThickColours T2 u t
    2 / (b * δ) * (∑ p ∈ (Finset.Icc 1 (min N T)).filter (fun p => p.Prime ∧ z < p),
      ∑ g ∈ thin, alpogeNativeASKRealWeight inertia frob p g *
        min (a / (p : ℝ)) (alpogeNativeLowerLogWidth η (w (alpogeNativePartner t g)))) ≤
      12 * (Real.log 4 + 2) / ((x + 1) * δ) := by
  let G := Finset.univ.filter (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g)
  let thin := G \ alpogeNativeProjectionThickColours T2 u t
  let P := (Finset.Icc 1 (min N T)).filter (fun p => p.Prime ∧ z < p)
  let B := 3 * ((x + 1) * b) / X'
  let C := Real.log 4 + 2
  have hx' : 0 < x + 1 := by linarith
  have hB : 0 ≤ B := div_nonneg (by positivity) hX.le
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hwidth (g : AlpogeNativeE0 × H) (hg : g ∈ thin) :
      alpogeNativeLowerLogWidth η (w (alpogeNativePartner t g)) ≤ B := by
    let W := w (alpogeNativePartner t g)
    obtain ⟨hw, hprice⟩ := hthin g hg
    have hf : (⌊Real.log W / η⌋ : ℤ) * η ≤ Real.log W := (le_div_iff₀ hη).mp (Int.floor_le _)
    have hr : alpogeNativeLowerLogWidth η W ≤ W :=
      (Real.exp_le_exp.mpr hf).trans (Real.exp_log hw).le
    apply hr.trans ((le_div_iff₀ hX).mpr ?_)
    have h := (le_div_iff₀ hw).mp hprice
    have hab := (div_le_iff₀ hb).mp ha
    change (X' / 3) * W ≤ a at h
    linarith only [h, hab]
  have hsub : P ⊆ Finset.Icc 1 T := by
    intro p hp
    exact (Finset.Icc_subset_Icc le_rfl (min_le_right N T)) (Finset.mem_filter.mp hp).1
  have hcop (p : ℕ) :
      (∑ g ∈ thin, alpogeNativeASKRealWeight inertia frob p g *
        min (a / (p : ℝ)) (alpogeNativeLowerLogWidth η (w (alpogeNativePartner t g)))) ≤
        (2 * B) * Λ p := by
    calc
      _ ≤ ∑ g ∈ thin, alpogeNativeASKRealWeight inertia frob p g * B :=
        Finset.sum_le_sum fun g hg => mul_le_mul_of_nonneg_left
          ((min_le_right _ _).trans (hwidth g hg)) (alpogeNativeASKRealWeight_nonneg inertia frob p g)
      _ = (∑ g ∈ thin, alpogeNativeASKRealWeight inertia frob p g) * B := (Finset.sum_mul _ _ _).symm
      _ ≤ (2 * Λ p) * B := by
        apply mul_le_mul_of_nonneg_right _ hB
        exact (Finset.sum_le_sum_of_subset_of_nonneg (show thin ⊆ G from Finset.sdiff_subset)
          (fun g _ _ => alpogeNativeASKRealWeight_nonneg inertia frob p g)).trans
          (alpogeNativeASKRealWeight_sum_le_two_lambda inertia frob p)
      _ = _ := by ring
  have hsum : (∑ p ∈ P, Λ p) ≤ C * T :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)).trans
      (nativePsi_le_const_mul T)
  have hfactor : 0 ≤ 2 / (b * δ) := by positivity
  calc
    _ ≤ 2 / (b * δ) * (∑ p ∈ P, (2 * B) * Λ p) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ => hcop p) hfactor
    _ ≤ 2 / (b * δ) * ((2 * B) * (C * T)) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (by positivity)) hfactor
    _ = (12 * C / ((x + 1) * δ)) * (((T : ℝ) * (x + 1)^2) / X') := by
      dsimp only [B]
      field [hb.ne', hδ.ne', hX.ne', hx'.ne']
    _ ≤ _ := mul_le_of_le_one_right (by positivity) ((div_le_one hX).mpr hT)

/-- A forward difference of the centered triangular twist controls the sharp
prime-power sum. Its linear logarithmic derivative cancels exactly. The price
of the boundary interval is independent of the character and conductor. -/
theorem alpogeNativeTwistedSharp_le_forward {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (ell : ℂ) {x h : ℝ} (hx : 1 ≤ x) (hh : 0 < h) :
    ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Λ n : ℝ) : ℂ) * χ n‖ ≤
      (x/h) * (‖alpogeNativeGchiArithmetic χ ell (x+h)‖ +
        ‖alpogeNativeGchiArithmetic χ ell x‖) +
        ‖alpogeNativeGchiArithmetic χ ell x‖ + (h+1)*Real.log (x+h) := by
  classical
  let I := Finset.Icc 1 ⌊x⌋₊
  let J := Finset.Icc 1 ⌊x+h⌋₊
  let c := fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ n
  let w := fun (y : ℝ) (n : ℕ) => y / (n : ℝ) - 1
  let f := alpogeNativeGchiArithmetic χ ell
  let E := ∑ n ∈ J \ I, (((x/h)*w (x+h) n : ℝ) : ℂ) * c n
  have hx0 := zero_lt_one.trans_le hx
  have hk : ⌊x⌋₊ ≤ ⌊x+h⌋₊ := Nat.floor_mono (le_add_of_nonneg_right hh.le)
  have hIJ : I ⊆ J := Finset.Icc_subset_Icc le_rfl hk
  have hsum (y : ℝ) : f y =
      (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (w y n : ℂ) * c n) + (y : ℂ) * ell := by
    unfold f alpogeNativeGchiArithmetic alpogeNativeTwistedPrimeSum
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    dsimp only [w,c,alpogeNativePrimePowerWeight]
    rw [Complex.ofReal_mul]
    ring
  have hpoint (n : ℕ) (hn : n ∈ I) :
      (x/h) * (w (x+h) n - w x n) - w x n = 1 := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 from Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)
    dsimp only [w]
    field [hh.ne', hn0]
  have hid : ((x/h : ℝ) : ℂ) * (f (x+h) - f x) - f x = (∑ n ∈ I, c n) + E := by
    have hxsum := hsum x
    have hysum := hsum (x+h)
    change f (x+h) = (∑ n ∈ J, (w (x+h) n : ℂ) * c n) + _ at hysum
    rw [← Finset.sum_sdiff hIJ] at hysum
    change f x = (∑ n ∈ I, (w x n : ℂ) * c n) + _ at hxsum
    have hlinear : ((x/h : ℝ) : ℂ) * (((x+h : ℝ) : ℂ)*ell - (x : ℂ)*ell) -
        (x : ℂ)*ell = 0 := by
      push_cast
      field [Complex.ofReal_ne_zero.mpr hh.ne']
    have hlow : ((x/h : ℝ) : ℂ) *
          ((∑ n ∈ I, (w (x+h) n : ℂ)*c n) - (∑ n ∈ I, (w x n : ℂ)*c n)) -
          (∑ n ∈ I, (w x n : ℂ)*c n) = ∑ n ∈ I, c n := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      have hc : ((x/h : ℝ) : ℂ) * ((w (x+h) n : ℂ) - (w x n : ℂ)) - (w x n : ℂ) = 1 := by
        exact_mod_cast hpoint n hn
      linear_combination c n * hc
    have htail : ((x/h : ℝ) : ℂ) * (∑ n ∈ J \ I, (w (x+h) n : ℂ)*c n) = E := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [Complex.ofReal_mul, mul_assoc]
    rw [hysum, hxsum]
    linear_combination hlow + htail + hlinear
  have htail (n : ℕ) (hn : n ∈ J \ I) : x < (n : ℝ) ∧ (n : ℝ) ≤ x+h := by
    obtain ⟨hj, hi⟩ := Finset.mem_sdiff.mp hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hj
    have hf : ⌊x⌋₊ < n := lt_of_not_ge fun hn' => hi (Finset.mem_Icc.mpr ⟨hn1, hn'⟩)
    exact ⟨(Nat.lt_floor_add_one x).trans_le (by exact_mod_cast Nat.succ_le_of_lt hf),
      (by exact_mod_cast hn2 : (n : ℝ) ≤ (⌊x+h⌋₊ : ℕ)).trans (Nat.floor_le (by positivity))⟩
  have hlog : 0 ≤ Real.log (x+h) := Real.log_nonneg (by linarith)
  have hcard : ((J \ I).card : ℝ) ≤ h+1 := by
    have sub : J \ I ⊆ Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊ := by
      intro n hn
      have h := htail n hn
      exact Finset.mem_Ioc.mpr ⟨(Nat.floor_lt hx0.le).2 h.1, Nat.le_floor h.2⟩
    have h1 : ((J \ I).card : ℝ) ≤ ((Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊).card : ℝ) := by
      exact_mod_cast Finset.card_le_card sub
    rw [Nat.card_Ioc, Nat.cast_sub hk] at h1
    linarith only [h1, Nat.floor_le (show 0 ≤ x+h by positivity), Nat.lt_floor_add_one x]
  have hE : ‖E‖ ≤ (h+1)*Real.log (x+h) := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _n ∈ J \ I, Real.log (x+h) := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨hnl, hnu⟩ := htail n hn
        have hn0 := hx0.trans hnl
        have hw0 : 0 ≤ w (x+h) n := sub_nonneg.mpr ((one_le_div hn0).2 hnu)
        have hw1 : x/h * w (x+h) n ≤ 1 := by
          dsimp only [w]
          rw [div_mul_eq_mul_div, div_le_one hh]
          rw [mul_sub, ← mul_div_assoc, sub_le_iff_le_add]
          apply (div_le_iff₀ hn0).2
          nlinarith only [mul_le_mul_of_nonneg_right hnl.le (show 0 ≤ x+h by positivity)]
        have hc : ‖c n‖ ≤ Real.log (x+h) := by
          dsimp only [c]
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          exact (mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)).trans
            (ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hn0 hnu))
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (div_nonneg hx0.le hh.le) hw0)]
        exact (mul_le_mul_of_nonneg_right hw1 (norm_nonneg _)).trans (by simpa only [one_mul] using hc)
      _ ≤ _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right hcard hlog
  have hk0 : 0 ≤ x/h := div_nonneg hx0.le hh.le
  calc
    _ = ‖(((x/h : ℝ) : ℂ) * (f (x+h) - f x) - f x) - E‖ := by rw [hid, add_sub_cancel_right]
    _ ≤ ‖((x/h : ℝ) : ℂ) * (f (x+h) - f x) - f x‖ + ‖E‖ := norm_sub_le _ _
    _ ≤ _ := by
      apply add_le_add _ hE
      refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hk0]
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) hk0

end RHLean.Analysis

namespace RHLean.Analysis.AlpogeThin

open Filter
open scoped BigOperators Classical

/-- Complete the finite ASK only on the majorizing side. Rounding may put a
width below the original beta. The original cutoff still admits this upper
bound because every extra real cut has nonnegative Fourier-inverted weight. -/
theorem nativeLedger_anyCutoff_le_thick_add_thin
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H)) (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ) (N : ℕ) (T2 : Finset H)
    (u t : H) (a : ℝ) (w : AlpogeNativeE0 × H → ℝ)
    (ha : 0 < a) (hw : ∀ ρ, alpogeNativeInPhi ρ → 0 < w ρ) :
    let F := alpogeNativeFrobInertiaGPsi inertia frob ell
    (alpogeNativeFullKernelASK inertia frob N a t w - alpogeNativeMAIN ell a w).re ≤
      (alpogeNativeProjectionActualThick F T2 a u t w).re +
        ‖alpogeNativeProjectionThinReturn F T2 a u t w‖ := by
  classical
  let L := max N (Finset.univ.sup fun ρ : AlpogeNativeE0 × H => ⌈a / w ρ⌉₊)
  have hcover (ρ : AlpogeNativeE0 × H) (_hρ : alpogeNativeInPhi ρ) : a / w ρ ≤ (L : ℝ) := by
    apply (Nat.le_ceil _).trans
    exact_mod_cast (Finset.le_sup (f := fun σ : AlpogeNativeE0 × H => ⌈a / w σ⌉₊)
      (Finset.mem_univ ρ)).trans (le_max_right N _)
  have hmono : (alpogeNativeFullKernelASK inertia frob N a t w).re ≤
      (alpogeNativeFullKernelASK inertia frob L a t w).re := by
    rw [alpogeNativeFullKernelASK_re_eq_weighted, alpogeNativeFullKernelASK_re_eq_weighted]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl (le_max_left N _))
      fun n _ _ => Finset.sum_nonneg fun g _ => mul_nonneg
        (alpogeNativeASKRealWeight_nonneg inertia frob n g) (le_max_right _ _)
  dsimp only
  calc
    _ ≤ (alpogeNativeFullKernelASK inertia frob L a t w - alpogeNativeMAIN ell a w).re := by
      simp only [Complex.sub_re]
      exact sub_le_sub_right hmono _
    _ = _ := congrArg Complex.re (alpogeNativeFullASK_sub_MAIN_eq_De inertia frob ell L a t w ha hw hcover)
    _ ≤ _ := by
      rw [← alpogeNativeProjectionFullSource_eq_nativeDe,
        alpogeNativeProjectionFull_eq_thick_add_thin _ T2 a u t w, Complex.add_re]
      exact add_le_add le_rfl (Complex.re_le_norm _)

private theorem nonzero_twoBit (H : Type*) [AddCommGroup H] [Fintype H] [DecidableEq H]
    (i j : Fin 2) (hij : i ≠ 0 ∨ j ≠ 0) :
    (i : ℕ) • alpogeNativePsC H + (j : ℕ) • alpogeNativeChC H ≠ 0 := by
  intro hz
  let v := (((0, 1) : AlpogeNativeE0), (0 : H))
  have hB : alpogeNativePsC H v = -1 := by
    change (if (1 : ZMod 2) = 0 then (1 : ℂ) else -1) = -1
    exact ite_eq_right (by decide)
  have hA : alpogeNativeChC H v = 1 := rfl
  have h1 := DFunLike.congr_fun hz (alpogeNativeProjectionE1 (0 : H))
  have h2 := DFunLike.congr_fun hz v
  simp only [AddChar.add_apply, AddChar.nsmul_apply, alpogeNativeChC_projectionE1,
    alpogeNativePsC_projectionE1, AddChar.zero_apply, one_pow, one_mul] at h1
  simp only [AddChar.add_apply, AddChar.nsmul_apply, hA, hB, AddChar.zero_apply,
    one_pow, mul_one] at h2
  have zero_bit (k : Fin 2) (hk : (-1 : ℂ) ^ (k : ℕ) = 1) : k = 0 := by
    by_contra h
    have hne : (k : ℕ) ≠ 0 := fun he => h (Fin.ext he)
    have ho : (k : ℕ) = 1 := by omega
    rw [ho, pow_one] at hk
    norm_num at hk
  exact hij.elim (fun hi => hi (zero_bit i h2)) (fun hj => hj (zero_bit j h1))

private theorem pairGood_sharp_induced {q d N : ℕ} [NeZero N]
    {eps Y Z x h : ℝ} (hG : UpperTheory.Top.PairGood 1 eps Y Z q d)
    (i j : Fin 2) (hij : i ≠ 0 ∨ j ≠ 0) (χ : DirichletCharacter ℂ N) (hne : χ ≠ 1)
    (hI : Formalism.HC.An.Induces χ (UpperTheory.Top.tw
      (fun a => (1 : DirichletCharacter ℂ 1) (a : ZMod 1)) q d i j) (2 * 1 * q * d))
    (hx : 1 ≤ x) (hh : 0 < h) (hY : Y ≤ x) (hZ : x+h ≤ Z) :
    ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n‖ ≤
      (x/h) * ((x+h)^((1 : ℝ)/2+eps/2) + x^((1 : ℝ)/2+eps/2)) +
        x^((1 : ℝ)/2+eps/2) + (h+1)*Real.log (x+h) := by
  let ell := deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1
  have bound (t : ℝ) (h1 : Y ≤ t) (h2 : t ≤ Z) :
      ‖alpogeNativeGchiArithmetic χ ell t‖ ≤ t^((1 : ℝ)/2+eps/2) := by
    have ht := (hG.bounds (1 : DirichletCharacter ℂ 1) i j hij N χ hI t h1 h2).1
    rw [hostResponse_eq_nativeResponse, nativeResponse, ite_eq_right hne] at ht
    exact ht
  have hle : x ≤ x+h := le_add_of_nonneg_right hh.le
  have h0 := bound x hY (hle.trans hZ)
  have h1 := bound (x+h) (hY.trans hle) hZ
  exact (alpogeNativeTwistedSharp_le_forward χ ell hx hh).trans
    (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (add_le_add h1 h0)
      (div_nonneg (zero_le_one.trans hx) hh.le)) h0) le_rfl)

set_option diagnostics true in
private theorem sharp_on_native_character {H : Type*} [AddCommGroup H] [Fintype H]
    [DecidableEq H] {M q d : ℕ} [NeZero M] {eps Y Z x h : ℝ}
    (r : (ZMod M)ˣ →* Multiplicative (AlpogeNativeE0 × H)) (hr : Function.Surjective r)
    (ψ : AddChar (AlpogeNativeE0 × H) ℂ) (hψ : ψ ≠ 0)
    (hG : UpperTheory.Top.PairGood 1 eps Y Z q d) (i j : Fin 2) (hij : i ≠ 0 ∨ j ≠ 0)
    (hI : Formalism.HC.An.Induces (alpogeNativeDirChar (N := M) (H := H) r ψ).primitiveCharacter
      (UpperTheory.Top.tw (fun a => (1 : DirichletCharacter ℂ 1) (a : ZMod 1)) q d i j) (2*1*q*d))
    (hx : 1 ≤ x) (hh : 0 < h) (hY : Y ≤ x) (hZ : x+h ≤ Z) :
    let c := Formalism.HC.PChar.of (alpogeNativeDirChar (N := M) (H := H) r ψ)
    ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * c.val n‖ ≤
      (x/h) * ((x+h)^((1 : ℝ)/2+eps/2) + x^((1 : ℝ)/2+eps/2)) +
        x^((1 : ℝ)/2+eps/2) + (h+1)*Real.log (x+h) := by
  let χ : DirichletCharacter ℂ M := alpogeNativeDirChar (N := M) (H := H) r ψ
  let : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  have hn : χ.primitiveCharacter ≠ 1 := fun hn =>
    hψ ((nativePrimitive_eq_one_iff (N := M) (H := H) r hr ψ).mp hn)
  exact pairGood_sharp_induced (N := χ.conductor) hG i j hij χ.primitiveCharacter hn hI hx hh hY hZ

set_option diagnostics true in
/-- A sharp, conductor-uniform prime-power estimate on each of the three
actual nonprincipal twists of the existing selected pair. Both points
are in its original window. -/
theorem nativeLedger_pairGood_sharp_twist (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    {eps Y Z x h : ℝ} (hG : UpperTheory.Top.PairGood 1 eps Y Z q d)
    (i j : Fin 2) (hij : i ≠ 0 ∨ j ≠ 0) (hx : 1 ≤ x) (hh : 0 < h)
    (hY : Y ≤ x) (hZ : x+h ≤ Z) :
    let c := Formalism.HC.PChar.of (alpogeNativeDirChar (N := alpogeNativeHostN e q d)
      (H := AlpogeNativeDyadicH e) (alpogeNativeRecMap e q d) (nativeDyadicTwoBitCharacter e i j))
    ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * c.val n‖ ≤
      (x/h) * ((x+h)^((1 : ℝ)/2+eps/2) + x^((1 : ℝ)/2+eps/2)) +
        x^((1 : ℝ)/2+eps/2) + (h+1)*Real.log (x+h) := by
  have hq2 : q ≠ 2 := by have := hG.pair.q_mod; omega
  have hd2 : d ≠ 2 := by have := hG.pair.d_mod; omega
  have hqd : q ≠ d := by have := hG.pair.q_mod; have := hG.pair.d_mod; omega
  exact sharp_on_native_character (M := alpogeNativeHostN e q d) (H := AlpogeNativeDyadicH e)
    (alpogeNativeRecMap e q d) (alpogeNativeRecMap_surjective e q d hq2 hd2 hqd)
    (nativeDyadicTwoBitCharacter e i j) (nonzero_twoBit (AlpogeNativeDyadicH e) i j hij)
    hG i j hij (nativeDyadicTwoBitCharacter_induces e q d i j) hx hh hY hZ

/-- The entire centered thin channel, including arbitrarily large first
primes, is paid on every original good pair. The bound is uniform in the
original finite cutoff and the positive grid spacing. -/
theorem nativeLedger_pairGood_roundedASK_le_thick (eps : ℝ) (he : 0 < eps) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (Y Z : ℝ) (q d e N : ℕ)
      (hG : UpperTheory.Top.PairGood 1 eps Y Z q d),
      letI : Fact q.Prime := ⟨hG.pair.q_prime⟩
      letI : Fact d.Prime := ⟨hG.pair.d_prime⟩
      ∀ (T2 : Finset (AlpogeNativeDyadicH e)) (u t : AlpogeNativeDyadicH e)
        (a η : ℝ) (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ),
        0 < a → 0 < η →
        Real.log (alpogeNativeHostN e q d) ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2 →
        (∀ g ∈ (Finset.univ.filter (fun g : AlpogeNativeE0 × AlpogeNativeDyadicH e =>
          ¬ alpogeNativeInPhi g)) \ alpogeNativeProjectionThickColours T2 u t,
          0 < w (alpogeNativePartner t g) ∧
            Real.exp (x ^ (eps / 3)) / 3 ≤ a / w (alpogeNativePartner t g)) →
        let D := alpogeNativeHostData e q d
        let ell := alpogeNativeCanonicalHostEll (H := AlpogeNativeDyadicH e) (alpogeNativeRecMap e q d)
        let F := alpogeNativeFrobInertiaGPsi D.inertia D.frob ell
        let v := fun ρ => alpogeNativeLowerLogWidth η (w ρ)
        (alpogeNativeFullKernelASK D.inertia D.frob N a t v - alpogeNativeMAIN ell a v).re ≤
          (alpogeNativeProjectionActualThick F T2 a u t v).re +
            ((2 * (Fintype.card (AlpogeNativeDyadicH e) : ℝ) - T2.card) /
              (alpogeNativePhiSet (AlpogeNativeDyadicH e)).card) *
              (4 * (Fintype.card (AlpogeNativeDyadicH e) : ℝ) * a * Real.exp (-(x ^ (eps / 8)))) := by
  obtain ⟨c₀, hc₀, hnoExc⟩ := principalPair_uniform_noExc
  obtain ⟨x₀, hthin⟩ := QH.thin eps 2 1 c₀ he two_pos one_pos hc₀
  refine ⟨x₀, ?_⟩
  intro x hx Y Z q d e N hG
  let : Fact q.Prime := ⟨hG.pair.q_prime⟩
  let : Fact d.Prime := ⟨hG.pair.d_prime⟩
  dsimp only
  intro T2 u t a η w ha hη hlog hsites
  let D := alpogeNativeHostData e q d
  let r := alpogeNativeRecMap e q d
  let ell := alpogeNativeCanonicalHostEll (H := AlpogeNativeDyadicH e) r
  let F := alpogeNativeFrobInertiaGPsi D.inertia D.frob ell
  let v := fun ρ => alpogeNativeLowerLogWidth η (w ρ)
  have honto : Function.Surjective r := alpogeNativeRecMap_surjective e q d
    (by have := hG.pair.q_mod; omega) (by have := hG.pair.d_mod; omega)
    (by have := hG.pair.q_mod; have := hG.pair.d_mod; omega)
  have hF (ψ : AddChar (AlpogeNativeE0 × AlpogeNativeDyadicH e) ℂ) (y : ℝ)
      (hy : Real.exp (x ^ (eps / 3)) / 3 ≤ y) :
      ‖F ψ y‖ ≤ y * Real.exp (-(x ^ (eps / 8))) := by
    let χ := alpogeNativeDirChar (H := AlpogeNativeDyadicH e) r ψ
    let : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero _⟩
    have hc : χ.conductor ∣ alpogeNativeHostN e q d := DirichletCharacter.conductor_dvd_level χ
    have hcpos : (0 : ℝ) < χ.conductor := by exact_mod_cast Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero χ)
    have hcN : (χ.conductor : ℝ) ≤ alpogeNativeHostN e q d := by exact_mod_cast Nat.le_of_dvd (NeZero.pos _) hc
    have hp := DirichletCharacter.primitiveCharacter_isPrimitive χ
    have hbound := hthin x hx χ.conductor χ.primitiveCharacter hp
      ((Real.log_le_log hcpos hcN).trans hlog)
      (hnoExc eps Y Z q d hG (e+2) χ.conductor χ.primitiveCharacter hp hc) y hy
    rw [G0_eq_nativeResponse] at hbound
    change ‖alpogeNativeFrobInertiaGPsi (alpogeNativeCftData (H := AlpogeNativeDyadicH e) (alpogeNativeHostN e q d) q d r).inertia
      (alpogeNativeCftData (H := AlpogeNativeDyadicH e) (alpogeNativeHostN e q d) q d r).frob ell ψ y‖ ≤ _
    rw [nativeCftGPsi_eq_nativeResponse (H := AlpogeNativeDyadicH e) q d r honto ψ y]
    simpa only [one_mul] using hbound
  have hpay := nativeThinReturn_norm_le F T2 a (Real.exp (-(x ^ (eps / 8)))) u t v
    (fun _ _ => Real.exp_pos _) (fun g hg ψ => by
      obtain ⟨hw, hy⟩ := hsites g hg
      apply hF ψ _ (hy.trans ?_)
      have hfloor := (le_div_iff₀ hη).mp (Int.floor_le (Real.log (w (alpogeNativePartner t g)) / η))
      exact div_le_div_of_nonneg_left ha.le (Real.exp_pos _)
        ((Real.exp_le_exp.mpr hfloor).trans (Real.exp_log hw).le))
  rw [nativeThinColourCount] at hpay
  exact (nativeLedger_anyCutoff_le_thick_add_thin D.inertia D.frob ell N T2 u t a v ha
    (fun _ _ => Real.exp_pos _)).trans (add_le_add le_rfl hpay)

/-- Return the rounded thick coordinates to their actual measured widths,
leaving rounded thin coordinates fixed. The complete finite signed row costs
at most 8(log 4 + 2) a η, uniformly in its original cutoff. -/
theorem nativeLedger_restoreMeasuredThick_le
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H)) (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ) (N : ℕ) (T2 : Finset H)
    (u t : H) (a b η : ℝ) (w : AlpogeNativeE0 × H → ℝ)
    (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (hthick : ∀ ρ ∈ alpogeNativeThickPositiveSites T2 u, b ≤ w ρ ∧ w ρ ≤ 2 * b) :
    let v := fun ρ => alpogeNativeLowerLogWidth η (w ρ)
    let mixed := fun ρ => if ρ ∈ alpogeNativeThickPositiveSites T2 u then w ρ else v ρ
    alpogeNativeSignedWidthSource inertia frob ell N a t v ≤
      alpogeNativeSignedWidthSource inertia frob ell N a t mixed + 8 * (Real.log 4 + 2) * a * η := by
  classical
  let v := fun ρ => alpogeNativeLowerLogWidth η (w ρ)
  let mixed := fun ρ => if ρ ∈ alpogeNativeThickPositiveSites T2 u then w ρ else v ρ
  have hgrid (ρ) (hs : ρ ∈ alpogeNativeThickPositiveSites T2 u) :
      (w ρ) * (1 - η) ≤ v ρ ∧ v ρ ≤ w ρ := by
    have hp := hb.trans_le (hthick ρ hs).1
    have hlo := (le_div_iff₀ hη).mp (Int.floor_le (Real.log (w ρ) / η))
    have hhi := (div_lt_iff₀ hη).mp (Int.lt_floor_add_one (Real.log (w ρ) / η))
    refine ⟨?_, (Real.exp_le_exp.mpr hlo).trans (Real.exp_log hp).le⟩
    calc
      _ ≤ w ρ * Real.exp (-η) := mul_le_mul_of_nonneg_left (Real.one_sub_le_exp_neg η) hp.le
      _ = Real.exp (Real.log (w ρ) - η) := by rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hp]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hhi])
  have hm := alpogeNativeSignedWidthSource_lower_width_le inertia frob ell N a (b/2) (2*b*η) t
    v mixed ha (half_pos hb) (by positivity) (fun _ _ => Real.exp_pos _)
    (fun ρ _ => by
      dsimp only [mixed]
      split_ifs with hs
      · exact (hgrid ρ hs).2
      · exact le_rfl)
    (fun ρ _ => by
      dsimp only [mixed]
      split_ifs with hs
      · linarith only [(hgrid ρ hs).1, mul_le_mul_of_nonneg_right (hthick ρ hs).2 hη.le]
      · rw [sub_self]; positivity)
    (fun ρ _ => by
      by_cases hs : ρ ∈ alpogeNativeThickPositiveSites T2 u
      · right
        have h1 : (1:ℝ)/2 ≤ 1-η := by linarith
        exact (by linarith only [(mul_le_mul (hthick ρ hs).1 h1 (by norm_num)
          (hb.trans_le (hthick ρ hs).1).le).trans (hgrid ρ hs).1] : b/2 ≤ v ρ)
      · exact Or.inl (by simp only [mixed, ite_eq_right hs]))
  refine hm.trans (add_le_add le_rfl ?_)
  calc
    _ ≤ 2 * (2*b*η) * (Real.log 4 + 2) * (a/(b/2)) :=
      alpogeNativeFreezing_cost_le a (b/2) (2*b*η) ha.le (half_pos hb) (by positivity)
    _ = _ := by field [hb.ne']

/-- On every thick first-prime site below the anchor, its saving is the
base width up to the physical collar and one grid step. The exact count
over translates removes the thick density from the normalized error. -/
theorem nativeLedger_thickFirst_saving_census
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (T2 : Finset H) (t v : H) (z b h η : ℝ) (hb : 0 < b) (hη : 0 < η) (hz : b ≤ z)
    (w : H → AlpogeNativeE0 × H → ℝ)
    (hw : ∀ u, alpogeNativeProjectionE1 v ∈ alpogeNativeProjectionThickColours T2 u t →
      w u (alpogeNativePartner t (alpogeNativeProjectionE1 v)) ∈ Set.Icc b (b+h)) :
    let U := Finset.univ.filter (fun u : H =>
      alpogeNativeProjectionE1 v ∈ alpogeNativeProjectionThickColours T2 u t)
    (∑ u ∈ U, min z (alpogeNativeLowerLogWidth η (w u (alpogeNativePartner t (alpogeNativeProjectionE1 v))))) ∈
      Set.Icc ((T2.card : ℝ) * (b * Real.exp (-η))) ((T2.card : ℝ) * (b+h)) := by
  classical
  let U := Finset.univ.filter (fun u : H =>
    alpogeNativeProjectionE1 v ∈ alpogeNativeProjectionThickColours T2 u t)
  let W := fun u => w u (alpogeNativePartner t (alpogeNativeProjectionE1 v))
  have hbase : b * Real.exp (-η) ≤ z :=
    (mul_le_of_le_one_right hb.le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hη.le))).trans hz
  have hpoint (u : H) (hu : u ∈ U) :
      min z (alpogeNativeLowerLogWidth η (W u)) ∈ Set.Icc (b * Real.exp (-η)) (b+h) := by
    obtain ⟨hlo, hhi⟩ := hw u (Finset.mem_filter.mp hu).2
    have hpos : 0 < W u := hb.trans_le hlo
    have hc := alpogeNativeLowerLogWidth_cut_le η z b (W u) hη hpos hlo
    change max (z - alpogeNativeLowerLogWidth η (W u)) 0 ≤ max (z - b * Real.exp (-η)) 0 at hc
    rw [max_eq_left (sub_nonneg.mpr hbase)] at hc
    have hgrid := (le_div_iff₀ hη).mp (Int.floor_le (Real.log (W u)/η))
    exact ⟨le_min hbase (by linarith only [(le_max_left _ _).trans hc]),
      (min_le_right _ _).trans (((Real.exp_le_exp.mpr hgrid).trans (Real.exp_log hpos).le).trans hhi)⟩
  have hcard : U.card = T2.card := alpogeNativeThickColour_translate_count T2 t v
  constructor
  · calc
      _ = ∑ _u ∈ U, b * Real.exp (-η) := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
      _ ≤ _ := Finset.sum_le_sum fun u hu => (hpoint u hu).1
  · calc
      _ ≤ ∑ _u ∈ U, (b+h) := Finset.sum_le_sum fun u hu => (hpoint u hu).2
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hcard]

/-- At the original grid spacing, every thick read with index at least x
lies in a shell of length at most 1+2√x, with height at most 3b/(2√x).
This applies to the measured width and all prime powers at once. -/
theorem nativeLedger_thickTail_cut {x b δ A a w n : ℝ}
    (hx : 1 ≤ x) (hb : 0 < b) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hA : x * b ≤ A) (ha : a ≤ (x + 1) * b) (hw : b ≤ w) (hn : x ≤ n) :
    let η := b * δ * Real.sqrt x / (2 * A)
    alpogeASKPos (a / n) (alpogeNativeLowerLogWidth η w) ≤
      if n < x + 1 + 2 * Real.sqrt x then 3 * b / (2 * Real.sqrt x) else 0 := by
  let R := Real.sqrt x
  let η := b * δ * R / (2 * A)
  have hx0 := zero_lt_one.trans_le hx
  have hR : 0 < R := Real.sqrt_pos.2 hx0
  have hR1 : 1 ≤ R := (Real.le_sqrt zero_le_one hx0.le).2 (by simpa using hx)
  have hRsq : R ^ 2 = x := Real.sq_sqrt hx0.le
  have hRx : R ≤ x := by nlinarith only [hRsq, mul_nonneg (sub_nonneg.mpr hR1) hR.le]
  have hA0 := (mul_pos hx0 hb).trans_le hA
  have hη0 : 0 < η := by dsimp only [η]; positivity
  have hstep : η ≤ 1 / (2 * R) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * A) (by positivity : 0 < 2 * R)).2
    calc
      (b * δ * R) * (2 * R) = 2 * ((x * b) * δ) := by rw [← hRsq]; ring
      _ ≤ 1 * (2 * A) := by
        linarith only [(mul_le_of_le_one_right (mul_nonneg hx0.le hb.le) hδ1).trans hA]
  have hn0 := hx0.trans_le hn
  have hcap : a / n ≤ b * (1 + 1 / x) := by
    apply (div_le_iff₀ hn0).2
    calc
      a ≤ (x + 1) * b := ha
      _ = (b * (1 + 1 / x)) * x := by field [hx0.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hn (by positivity)
  change alpogeASKPos (a / n) (alpogeNativeLowerLogWidth η w) ≤
    if n < x + 1 + 2 * R then 3 * b / (2 * R) else 0
  refine (alpogeNativeLowerLogWidth_cut_le η (a/n) b w hη0 (hb.trans_le hw) hw).trans ?_
  unfold alpogeASKPos
  split_ifs with h
  · apply max_le _ (by positivity)
    calc
      a / n - b * Real.exp (-η) ≤ b * (1 / x + η) := by
        linarith only [hcap, mul_le_mul_of_nonneg_left (Real.one_sub_le_exp_neg η) hb.le]
      _ ≤ b * (1 / R + 1 / (2 * R)) := mul_le_mul_of_nonneg_left
        (add_le_add (one_div_le_one_div_of_le hR hRx) hstep) hb.le
      _ = _ := by field [hR.ne']
  · apply max_le _ le_rfl
    have hf0 : 0 ≤ 1 - 1 / (2 * R) :=
      sub_nonneg.mpr ((div_le_one (by positivity : 0 < 2 * R)).2 (by linarith))
    have hf := (sub_le_sub_left hstep 1).trans (Real.one_sub_le_exp_neg η)
    have hend : x + 1 ≤ (x + 1 + 2 * R) * (1 - 1 / (2 * R)) := by
      apply le_of_mul_le_mul_right (a := 2 * R) _ (by positivity)
      have hdiff : ((x + 1 + 2 * R) * (1 - 1 / (2 * R)) - (x + 1)) * (2 * R) =
          (3 * R + 1) * (R - 1) := by
        rw [← hRsq]
        field [hR.ne']
      linarith only [hdiff, mul_nonneg (show 0 ≤ 3 * R + 1 by positivity) (sub_nonneg.mpr hR1)]
    have hlarge := hend.trans (mul_le_mul (le_of_not_gt h) hf hf0 hn0.le)
    apply sub_nonpos.mpr ((div_le_iff₀ hn0).2 (ha.trans ?_))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_right hlarge hb.le

/-- On the outstanding thick first-prime range, the third-power read of
the same shifted-width pair is already clipped to zero on the rounded frame. -/
theorem nativeLedger_highPrime_thick_thirdCut_zero (e q d p : ℕ) [Fact q.Prime] [Fact d.Prime]
    (t : AlpogeNativeDyadicH e) (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    {x b δ A a : ℝ} (hx : 4 ≤ x) (hb : 0 < b) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hA : x*b ≤ A) (ha : a ≤ (x+1)*b) (hp : Real.sqrt x < p)
    (hw : b ≤ w (alpogeNativePartner t ((3 : ℕ) • (alpogeNativeHostData e q d).frob p))) :
    nativeDyadicLocalSourceAtom e q d p a t
      (fun i => alpogeNativeLowerLogWidth (b*δ*Real.sqrt x/(2*A)) (w i)) 3 = 0 := by
  have hx0 : 0 ≤ x := by linarith
  have hR : 2 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) hx0).2 (by linarith)
  have h2p : 2 < p := by exact_mod_cast hR.trans_lt hp
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast Nat.succ_le_of_lt h2p
  have hsq : x ≤ (p : ℝ)^2 := (Real.sq_sqrt hx0).symm.le.trans
    (pow_le_pow_left₀ (Real.sqrt_nonneg _) hp.le 2)
  have h3x : 3*x ≤ (p : ℝ)^3 := calc
    _ ≤ (p : ℝ) * (p : ℝ)^2 := mul_le_mul hp3 hsq hx0 (Nat.cast_nonneg p)
    _ = _ := by ring
  have hRx : 2 * Real.sqrt x ≤ x := by
    nlinarith only [Real.sq_sqrt hx0,
      mul_nonneg (Real.sqrt_nonneg x) (sub_nonneg.mpr hR)]
  have hcut : x+1+2*Real.sqrt x ≤ (p : ℝ)^3 := by linarith only [h3x, hx, hRx]
  have h := nativeLedger_thickTail_cut (n := (p : ℝ)^3) (by linarith only [hx])
    hb hδ hδ1 hA ha hw (by linarith only [h3x, hx])
  rw [ite_eq_right (not_lt.mpr hcut)] at h
  simpa only [nativeDyadicLocalSourceAtom, alpogeNativeSiteCut, Complex.ofReal_re,
    Nat.cast_pow, alpogeASKPos] using le_antisymm h (le_max_right _ _)

/-- Total retained thick ASK above the real anchor on one measured row.
The bound includes every prime power and is independent of the cutoff. -/
theorem nativeLedger_thickTail_mass {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H)) (frob : ℕ → AlpogeNativeE0 × H)
    (N : ℕ) (T2 : Finset H) (u t : H) (w : AlpogeNativeE0 × H → ℝ)
    {x b δ A a : ℝ} (hx : 1 ≤ x) (hb : 0 < b) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hA : x * b ≤ A) (ha : a ≤ (x + 1) * b)
    (hw : ∀ g ∈ alpogeNativeProjectionThickColours T2 u t, b ≤ w (alpogeNativePartner t g)) :
    let η := b * δ * Real.sqrt x / (2 * A)
    let thick := (Finset.univ.filter (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g)).filter
      (fun g => g ∈ alpogeNativeProjectionThickColours T2 u t)
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => x ≤ (n : ℝ)), ∑ g ∈ thick,
      alpogeNativeASKRealWeight inertia frob n g *
        alpogeASKPos (a / n) (alpogeNativeLowerLogWidth η (w (alpogeNativePartner t g)))) ≤
      12 * b * Real.log (4 * x) := by
  classical
  let R := Real.sqrt x
  let Z := x + 1 + 2 * R
  let η := b * δ * R / (2 * A)
  let G := Finset.univ.filter (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g)
  let thick := G.filter (fun g => g ∈ alpogeNativeProjectionThickColours T2 u t)
  let I := (Finset.Icc 1 N).filter (fun n : ℕ => x ≤ (n : ℝ))
  let E := I.filter (fun n : ℕ => (n : ℝ) < Z)
  let C := 3 * b / (2 * R)
  let B := 2 * Real.log (4 * x) * C
  have hx0 := zero_lt_one.trans_le hx
  have hR : 0 < R := Real.sqrt_pos.2 hx0
  have hR1 : 1 ≤ R := (Real.le_sqrt zero_le_one hx0.le).2 (by simpa using hx)
  have hRx : R ≤ x := by
    nlinarith only [show R ^ 2 = x from Real.sq_sqrt hx0.le, mul_nonneg (sub_nonneg.mpr hR1) hR.le]
  have hZ : Z ≤ 4 * x := by dsimp only [Z]; linarith
  have hZ0 : 0 ≤ Z := by dsimp only [Z]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hlog : 0 ≤ Real.log (4 * x) := Real.log_nonneg (by linarith)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hsub : E ⊆ Finset.Icc ⌈x⌉₊ ⌊Z⌋₊ := by
    intro n hn
    obtain ⟨hi, hz⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr (Finset.mem_filter.mp hi).2, Nat.le_floor hz.le⟩
  have hceil := Nat.ceil_lt_add_one hx0.le
  have hleft : ⌈x⌉₊ ≤ ⌊Z⌋₊ := Nat.le_floor (by dsimp only [Z]; linarith only [hceil, hR1])
  have hcard : (E.card : ℝ) ≤ 4 * R := by
    calc
      _ ≤ ((Finset.Icc ⌈x⌉₊ ⌊Z⌋₊).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ _ := by
        rw [Nat.card_Icc, Nat.cast_sub (by omega : ⌈x⌉₊ ≤ ⌊Z⌋₊ + 1), Nat.cast_add, Nat.cast_one]
        have hfloor := Nat.floor_le hZ0
        dsimp only [Z] at hfloor
        linarith only [hfloor, Nat.le_ceil x, hR1]
  have hpoint (n : ℕ) (hn : n ∈ I) :
      (∑ g ∈ thick, alpogeNativeASKRealWeight inertia frob n g *
        alpogeASKPos (a / n) (alpogeNativeLowerLogWidth η (w (alpogeNativePartner t g)))) ≤
        if (n : ℝ) < Z then B else 0 := by
    let c : ℝ := if (n : ℝ) < Z then C else 0
    have hc : 0 ≤ c := by dsimp only [c]; split_ifs <;> positivity
    have hn' := (Finset.mem_filter.mp hn).2
    have hm := (Finset.sum_le_sum_of_subset_of_nonneg (show thick ⊆ G from Finset.filter_subset ..)
      (fun g _ _ => alpogeNativeASKRealWeight_nonneg inertia frob n g)).trans
        (alpogeNativeASKRealWeight_sum_le_two_lambda inertia frob n)
    calc
      _ ≤ ∑ g ∈ thick, alpogeNativeASKRealWeight inertia frob n g * c :=
        Finset.sum_le_sum fun g hg => mul_le_mul_of_nonneg_left
          (nativeLedger_thickTail_cut hx hb hδ hδ1 hA ha (hw g (Finset.mem_filter.mp hg).2) hn')
          (alpogeNativeASKRealWeight_nonneg inertia frob n g)
      _ = (∑ g ∈ thick, alpogeNativeASKRealWeight inertia frob n g) * c := (Finset.sum_mul ..).symm
      _ ≤ _ * c := mul_le_mul_of_nonneg_right hm hc
      _ ≤ _ := by
        dsimp only [c]
        split_ifs with hz
        · apply mul_le_mul_of_nonneg_right _ hC
          exact mul_le_mul_of_nonneg_left
            (ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log (hx0.trans_le hn') (hz.le.trans hZ)))
            (by norm_num)
        · simp
  calc
    _ ≤ ∑ n ∈ I, if (n : ℝ) < Z then B else 0 := Finset.sum_le_sum hpoint
    _ = (E.card : ℝ) * B := by rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4 * R) * B := mul_le_mul_of_nonneg_right hcard hB
    _ = _ := by dsimp only [B, C]; field [hR.ne']

/-- The discriminant of the actual outer-window pair exceeds every fixed
polynomial scale. In particular a compact frame requiring 10^14*d ≤ log X
cannot use this discriminant at any polynomially related anchor X. -/
theorem nativeLedger_winPair_discriminant_growth {eps Y x A : ℝ} {q d : ℕ}
    (hpair : UpperTheory.Top.WinPair eps Y q d) (he : 0 < eps) (hA : 0 ≤ A)
    (hY : Real.exp (max 1 (4 * A)) ≤ Y) (hx : 0 < x) (hhi : x ≤ Y ^ (2 : ℕ)) :
    A * Real.log x < Real.log (d : ℝ) := by
  have hY0 := (Real.exp_pos _).trans_le hY
  have hlarge : max 1 (4 * A) ≤ Real.log Y := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hY
  have hlog : 0 ≤ Real.log Y := (by norm_num : (0 : ℝ) ≤ 1).trans ((le_max_left _ _).trans hlarge)
  have hY1 : 1 ≤ Y := (Real.one_le_exp (zero_le_one.trans (le_max_left _ _))).trans hY
  have hscale : Real.log x ≤ 2 * Real.log Y := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hx hhi
  have hpoly : 2 * A * Real.log Y ≤ Real.log Y ^ 2 / 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right ((le_max_right 1 (4 * A)).trans hlarge) hlog]
  have hq := mul_le_mul_of_nonneg_right
    (Real.one_le_rpow hY1 (by positivity : 0 ≤ eps / 5)) (sq_nonneg (Real.log Y))
  calc
    _ ≤ A * (2 * Real.log Y) := mul_le_mul_of_nonneg_left hscale hA
    _ ≤ Real.log Y ^ 2 / 2 := by linarith only [hpoly]
    _ < _ := by linarith only [hpair.d_lo, hq]

/-- The saving at the discriminant prime is bounded by its one-power
zero-width mass on the same selected pair. This pays the term even if
rounding changes which of its physical cuts is active. -/
theorem nativeLedger_ramifiedFirst_saving_le
    {ι : Type*} (e q d : ℕ) {ε Y x b : ℝ} (hε : 0 < ε)
    (hY : Real.exp 16 ≤ Y) (hx : 1 ≤ x) (hhi : x ≤ Y ^ (2 : ℕ))
    (hpair : UpperTheory.Top.WinPair ε Y q d)
    (J : Finset ι) (TT T2 : Finset (AlpogeNativeDyadicH e))
    (hJ : J.Nonempty) (hTT : TT.Nonempty) (hb : 0 < b)
    (hdensity : x ^ (-ε) ≤ alpogeNativeProjectionDensity T2)
    (a : AlpogeNativeDyadicH e → ℝ)
    (w : ι → AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (ha : ∀ t ∈ TT, 0 ≤ a t ∧ a t ≤ b * (x + 1)) :
    letI : Fact q.Prime := ⟨hpair.q_prime⟩
    letI : Fact d.Prime := ⟨hpair.d_prime⟩
    (∑ j ∈ J, ∑ t ∈ TT, Real.log d * min (a t / (d : ℝ))
      (w j (alpogeNativePartner t (nativeDyadicDInvolution e + (alpogeNativeHostData e q d).frob d)))) /
      alpogeNativeProjectionDivisor TT T2 J.card b ≤ 16 * x ^ (ε - 1) := by
  let : Fact q.Prime := ⟨hpair.q_prime⟩
  let : Fact d.Prime := ⟨hpair.d_prime⟩
  let row (t : AlpogeNativeDyadicH e) := nativeDyadicDPrimeASK e q d 1 (a t) t (fun _ => 0)
  have hrow (t : AlpogeNativeDyadicH e) (ht : t ∈ TT) :
      (row t).re = Real.log d * (a t / (d : ℝ)) := by
    simp only [row, nativeDyadicDPrimeASK, Finset.Icc_self, Finset.sum_singleton,
      alpogeNativeSiteCut, pow_one, sub_zero, max_eq_left (div_nonneg (ha t ht).1 (Nat.cast_nonneg d)),
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have hbound := (nativeDyadicDPrimeASK_normalized_le_of_winPair e q d 1 hε hY hx hhi
    hpair J TT T2 hJ hTT hb hdensity a (fun _ _ => 0) ha (fun _ _ _ _ => le_rfl)).2
  have hδ := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) (-ε)).trans_le hdensity
  have hQ : 0 ≤ alpogeNativeProjectionDivisor TT T2 J.card b := by
    unfold alpogeNativeProjectionDivisor
    positivity
  calc
    _ ≤ (∑ _j ∈ J, ∑ t ∈ TT, (row t).re) / alpogeNativeProjectionDivisor TT T2 J.card b := by
      apply div_le_div_of_nonneg_right _ hQ
      exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun t ht =>
        (mul_le_mul_of_nonneg_left (min_le_left _ _) (Real.log_natCast_nonneg d)).trans_eq (hrow t ht).symm
    _ = (∑ _j ∈ J, ∑ t ∈ TT, row t).re / alpogeNativeProjectionDivisor TT T2 J.card b := by
      simp only [Complex.re_sum]
    _ ≤ ‖∑ _j ∈ J, ∑ t ∈ TT, row t‖ / alpogeNativeProjectionDivisor TT T2 J.card b :=
      div_le_div_of_nonneg_right (Complex.re_le_norm _) hQ
    _ ≤ _ := hbound

/-- The rounded widths in the discrepancy ledger obey the uniform cap 2b.
This uses its own thick window and thin return inequality on each physical
partner. The bound is uniform in the pair, top, lift and original cutoff. -/
theorem nativeLedger_roundedWidth_cap_eventually (eps : ℝ) (he : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, ∀ a b h η w : ℝ,
      Real.exp (x ^ eps) ≤ b → 0 ≤ h → h ≤ Real.exp (x ^ (eps / 4)) + 1 →
      a / b ≤ x + 1 → 0 < w → 0 < η →
      (w ≤ b + h ∨ Real.exp (x ^ (eps / 3)) / 3 ≤ a / w) →
      alpogeNativeLowerLogWidth η w ∈ Set.Icc 0 (2 * b) := by
  filter_upwards [nativeFrozenWidthPrice_eventually eps he,
    dyadic_rpow_le_exp_eventually 2 (eps / 3) (by positivity),
    eventually_ge_atTop (5 : ℝ)] with x hfreeze hX hx
  intro a b h η w hb hh hh' ha hw hη hregime
  have hb0 := (Real.exp_pos (x ^ eps)).trans_le hb
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hsmall := hfreeze b b h hb hh hh' (by rw [div_self hb0.ne']; linarith)
  rw [div_self hb0.ne', one_mul] at hsmall
  have hhb : h ≤ b := (div_le_one hb0).1 (hsmall.trans ((div_le_one (by linarith : 0 < x)).2 hx1))
  have hwb : w ≤ 2 * b := by
    rcases hregime with hthick | hthin
    · linarith
    · rw [Real.rpow_two] at hX
      have hwide : 3 * (x + 1) ≤ Real.exp (x ^ (eps / 3)) := by
        calc
          _ ≤ x ^ 2 := by nlinarith [mul_nonneg (show 0 ≤ x - 5 by linarith) (show 0 ≤ x by linarith)]
          _ ≤ _ := hX
      have hactive : (x + 1) * w ≤ a :=
        (le_div_iff₀ hw).mp ((show x + 1 ≤ Real.exp (x ^ (eps / 3)) / 3 by linarith).trans hthin)
      have hwle : w ≤ b := le_of_mul_le_mul_left
        (hactive.trans ((div_le_iff₀ hb0).mp ha)) (by linarith : 0 < x + 1)
      linarith
  have hfloor : (⌊Real.log w / η⌋ : ℤ) * η ≤ Real.log w :=
    (le_div_iff₀ hη).mp (Int.floor_le _)
  exact ⟨(Real.exp_pos _).le, (Real.exp_le_exp.mpr hfloor).trans ((Real.exp_log hw).le.trans hwb)⟩

/-- The very same pair selected on [Y,Y²] covers every height in the unit
collar of every real anchor in the complete handoff window, including its
right endpoint. The choice of pair can precede the choice of anchor. -/
theorem nativeLedger_realHeight_mem_pairWindow {Y x v : ℝ} (hY : 4 ≤ Y)
    (hx : x ∈ Set.Icc Y (Y ^ ((3 : ℝ) / 2))) (hv : v ∈ Set.Icc x (x + 1)) :
    v ∈ Set.Icc Y (Y ^ (2 : ℝ)) := by
  have hY0 : 0 < Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hroot : 2 ≤ Real.sqrt Y := (Real.le_sqrt (by norm_num) hY0.le).2 (by linarith)
  have hpower : 1 ≤ Y ^ ((3 : ℝ) / 2) := Real.one_le_rpow hY1 (by norm_num)
  refine ⟨hx.1.trans hv.1, ?_⟩
  calc
    v ≤ Y ^ ((3 : ℝ) / 2) + 1 := hv.2.trans (add_le_add hx.2 le_rfl)
    _ ≤ Y ^ ((3 : ℝ) / 2) * 2 := by linarith
    _ ≤ Y ^ ((3 : ℝ) / 2) * Real.sqrt Y :=
      mul_le_mul_of_nonneg_left hroot (zero_le_one.trans hpower)
    _ = Y ^ (2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hY0]
      norm_num

/-- Specialize the normalized centering price to the original density and
the square-root first-prime cutoff on every real anchor. -/
theorem nativeLedger_firstPrimeWidth_price_le {x eps b δ K : ℝ}
    (hx : 1 ≤ x) (hb : 0 < b) (hδ : x ^ (-eps) ≤ δ) (hK : 0 ≤ K) :
    4 * (2 * b) / (b * δ) *
        (K * Real.sqrt (⌈x + 1⌉₊ : ℕ) + (Real.log 4 + 2) * (⌊Real.sqrt x⌋₊ : ℕ)) ≤
      8 * (2 * K + (Real.log 4 + 2)) * x ^ ((1 : ℝ) / 2 + eps) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hδ0 : 0 < δ := (Real.rpow_pos_of_pos hx0 _).trans_le hδ
  have hceil : (⌈x + 1⌉₊ : ℝ) < x + 1 + 1 := Nat.ceil_lt_add_one (by linarith)
  have hsqrt : Real.sqrt (⌈x + 1⌉₊ : ℕ) ≤ 2 * Real.sqrt x := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith only [hceil, hx, Real.sq_sqrt hx0.le]
  have hc : 0 ≤ Real.log 4 + 2 := by positivity
  have hbracket : K * Real.sqrt (⌈x + 1⌉₊ : ℕ) + (Real.log 4 + 2) * (⌊Real.sqrt x⌋₊ : ℕ) ≤
      (2 * K + (Real.log 4 + 2)) * Real.sqrt x := by
    calc
      _ ≤ K * (2 * Real.sqrt x) + (Real.log 4 + 2) * Real.sqrt x :=
        add_le_add (mul_le_mul_of_nonneg_left hsqrt hK)
          (mul_le_mul_of_nonneg_left (Nat.floor_le (Real.sqrt_nonneg _)) hc)
      _ = _ := by ring
  have hinv : 1 / δ ≤ x ^ eps := by
    rw [Real.rpow_neg hx0.le, ← one_div] at hδ
    apply (div_le_iff₀ hδ0).mpr
    simpa only [mul_comm] using (div_le_iff₀ (Real.rpow_pos_of_pos hx0 eps)).mp hδ
  have hfac : 4 * (2 * b) / (b * δ) = 8 * (1 / δ) := by field [hb.ne', hδ0.ne']
  rw [hfac]
  calc
    _ ≤ (8 * x ^ eps) * ((2 * K + (Real.log 4 + 2)) * Real.sqrt x) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hinv (by norm_num)) hbracket
      · positivity
      · positivity
    _ = _ := by rw [Real.rpow_add hx0, Real.sqrt_eq_rpow]; ring

/-- On the dyadic reciprocity host itself all replaced width cuts fit the
square-root budget. The constant precedes epsilon, the selected pair, the
outer window and every measured input. The physical cutoff N and the
canonical signed MAIN appear unchanged on both sides. -/
theorem nativeLedger_firstPrimeWidth_on_dyadicFrame :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ eps : ℝ, 0 < eps → ∀ᶠ x : ℝ in atTop,
      ∀ (e q d N m : ℕ) [Fact q.Prime] [Fact d.Prime]
        (TT T2 : Finset (AlpogeNativeDyadicH e)) (b h η : ℝ) (a : AlpogeNativeDyadicH e → ℝ)
        (w : AlpogeNativeDyadicH e → Fin m → AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ),
        TT.Nonempty → T2.Nonempty → 0 < m → Real.exp (x ^ eps) ≤ b →
        0 ≤ h → h ≤ Real.exp (x ^ (eps / 4)) + 1 → 0 < η →
        x ^ (-eps) ≤ alpogeNativeProjectionDensity T2 →
        (∀ t ∈ TT, 0 ≤ a t ∧ a t / b ≤ x + 1) →
        (∀ u j ρ, alpogeNativeInPhi ρ → 0 < w u j ρ) →
        (∀ u j ρ, ρ ∈ alpogeNativeThickPositiveSites T2 u → w u j ρ ≤ b + h) →
        (∀ (u : (⊤ : AddSubgroup (AlpogeNativeDyadicH e))) t, t ∈ TT → ∀ (j : Fin m) g,
          g ∈ (Finset.univ.filter (fun g : AlpogeNativeE0 × AlpogeNativeDyadicH e =>
            ¬ alpogeNativeInPhi g)) \ alpogeNativeProjectionThickColours T2 u t →
          Real.exp (x ^ (eps / 3)) / 3 ≤ a t / w u j (alpogeNativePartner t g)) →
        let D := alpogeNativeHostData e q d
        let ell := alpogeNativeCanonicalHostEll (H := AlpogeNativeDyadicH e) (alpogeNativeRecMap e q d)
        let A0 : AddSubgroup (AlpogeNativeDyadicH e) := ⊤
        let v := fun u j ρ => alpogeNativeLowerLogWidth η (w u j ρ)
        let centered := (1 / (Fintype.card A0 : ℝ)) * ∑ u : A0, ∑ t ∈ TT, ∑ j : Fin m,
          (alpogeNativeFirstPrimeWidthASK D.inertia D.frob N ⌊Real.sqrt x⌋₊ (a t) t (v u j) -
           (alpogeNativeMAIN ell (a t) (v u j)).re)
        (centered - alpogeNativePhysicalSubgroupTopExcess A0 D.inertia D.frob ell N TT a v) /
          alpogeNativeProjectionDivisor TT T2 m b ∈ Set.Icc 0 (C * x ^ ((1 : ℝ) / 2 + eps)) := by
  obtain ⟨K, hK, hnorm⟩ := alpogeNativeFirstPrimeWidth_normalized_error
  refine ⟨8 * (2 * K + (Real.log 4 + 2)), by positivity, ?_⟩
  intro eps he
  filter_upwards [nativeLedger_roundedWidth_cap_eventually eps he, eventually_ge_atTop (1 : ℝ)]
    with x hcap hx
  intro e q d N m _ _ TT T2 b h η a w hTT hT2 hm hb hh hh' hη hδ ha hw hthick hthin
  let A0 : AddSubgroup (AlpogeNativeDyadicH e) := ⊤
  let D := alpogeNativeHostData e q d
  let ell := alpogeNativeCanonicalHostEll (H := AlpogeNativeDyadicH e) (alpogeNativeRecMap e q d)
  let v := fun u j ρ => alpogeNativeLowerLogWidth η (w u j ρ)
  have hb0 := (Real.exp_pos _).trans_le hb
  have hceil := Nat.le_ceil (x + 1)
  have hM : 1 ≤ ⌈x + 1⌉₊ := by
    exact_mod_cast (show (1 : ℝ) ≤ (⌈x + 1⌉₊ : ℕ) by linarith only [hx, hceil])
  have hheight (t) (ht : t ∈ TT) : 0 ≤ a t ∧ a t ≤ (2 * b) * (⌈x + 1⌉₊ : ℕ) := by
    refine ⟨(ha t ht).1, ?_⟩
    calc
      a t ≤ (x + 1) * b := (div_le_iff₀ hb0).mp (ha t ht).2
      _ ≤ (⌈x + 1⌉₊ : ℝ) * b := mul_le_mul_of_nonneg_right hceil hb0.le
      _ ≤ _ := by nlinarith only [mul_nonneg (Nat.cast_nonneg (⌈x + 1⌉₊ : ℕ)) hb0.le]
  have hwidth (u : A0) j t (ht : t ∈ TT) g (hg : ¬ alpogeNativeInPhi g) :
      v u j (alpogeNativePartner t g) ∈ Set.Icc 0 (2 * b) := by
    apply hcap (a t) b h η _ hb hh hh' (ha t ht).2
      (hw u j _ (alpogeNativeFreezing_partner_inPhi t g hg)) hη
    by_cases hmem : g ∈ alpogeNativeProjectionThickColours T2 u t
    · exact Or.inl (hthick u j _ ((alpogeNativeFreezing_partner_mem_iff T2 u t g).2 hmem))
    · exact Or.inr (hthin u t ht j g
        (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩, hmem⟩))
  have hpaid := hnorm (AlpogeNativeDyadicH e) A0 D.inertia D.frob ell N ⌈x + 1⌉₊
    ⌊Real.sqrt x⌋₊ m TT T2 a b (2 * b) v hTT hT2 hm hb0 (by positivity) hM hheight hwidth
  exact ⟨hpaid.1, hpaid.2.trans (nativeLedger_firstPrimeWidth_price_le hx hb0 hδ hK)⟩

end RHLean.Analysis.AlpogeThin

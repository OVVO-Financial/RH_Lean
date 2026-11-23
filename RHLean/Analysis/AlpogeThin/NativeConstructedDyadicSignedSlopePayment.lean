import RHLean.Analysis.AlpogeThin.NativeConstructedDyadicGzPayment
import RHLean.Analysis.AlpogeNativeSignedSlopeComparison
import RHLean.Analysis.AlpogeThin.NativeGeometricCostWindows

/-!
# The constructed dyadic scalar source with the complete geometric costs

The exponent function and the selected prime pair are obtained once from
`nativeConstructedDyadicGzPayment`. The physical signed-slope comparison is
then applied to precisely that host, its actual inertia and Frobenius, its
canonical character constant, the same sharp cutoff, and the same heights
and widths. No second arithmetic witness is selected.

The scalar fields `x`, `epsilon` and `b` of the geometric data are set to
the actual source parameters. Its other geometric fields are preserved.
All eleven original finite slope hypotheses, the strong trace-error
window, and the two original auxiliary-budget bounds remain explicit on
that same data. The conclusion retains the full factor `x^(CErr*epsilon)`
and all three normalized geometric costs, plus the already-paid analytic
remainder. Under the original scalar size windows it also proves the exact
`CErr + 3` exponent bound. It does not assert that the remaining geometric
witnesses or these windows exist, or conclude the Riemann hypothesis.

Source correspondence: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean`
and `src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean`.
This composition invokes the native source proofs, without importing their
terminal RH consumers. The source mirror states no license; attribution is
retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators Classical

namespace RHLean.Analysis.AlpogeThin

open RHLean.Geometry.AlpogeSignedSlope.Formalism.RankGapBounds.WeightedMeanData
open RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.WeightedSlopeBounds
open RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.LErr

/-- The actual native scalar source is bounded by the complete signed
geometric cost and the already-paid analytic remainder. The constructed
host and selected prime pair are shared by every premise and conclusion.
The second conclusion pays the complete bracket under the source size windows,
without selecting another host or adding an assumed arithmetic bound. -/
theorem nativeConstructedDyadicSignedSlopePayment
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
                  LossBounds DP C → DP.SlopeIneq → DP.HHBound C → DP.FParams →
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
  have hgeom := AlpogeNativeSignedSlope.physicalTopExcess_div_le_normalizedGeometricCosts
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

end RHLean.Analysis.AlpogeThin

end

import RHLean.Analysis.AlpogeNativeCostNormalization
import RHLean.Geometry.AlpogeSignedSlope.Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence
import RHLean.Geometry.AlpogeSignedSlope.Formalism.SizeWindowBrackets.ChainSlopeWindows.StrongErrorBound

/-!
# The finite signed-slope comparison on the literal native physical source

The arithmetic entries of the source's weighted-slope data are constructed
from the same subgroup, heights, widths, inertia, Frobenius map and complete
prime-power ASK kernel used in `alpogeNativePhysicalSubgroupTopExcess`.
The real geometric entries of the input data, including `Ga`, the lattices'
slopes and their trace errors, are preserved by the record update.

The finite equivalence of the CM type proves the exact MAIN identity. The
original eleven slope hypotheses then yield the signed top-excess bound;
the original strong error windows give its explicit scalar form. Only the
subgroup means of `ASK - Ga` and `IO` are needed for the loss hypothesis;
the pointwise-loss API is retained as a specialization. No bound on top
excess, replacement finite-place gain or synthetic geometric family is
assumed. Constructing the genuine geometric suppliers for these eleven
hypotheses remains a separate task.

Source correspondence: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean`
(`ch_top_main_eq`, `ch_top`), together with the averaged finite comparison
in `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean`
and the strong error estimate in
`src/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean`.
The source mirror states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators Classical

namespace RHLean.Analysis.AlpogeNativeSignedSlope

open RHLean.Geometry.AlpogeSignedSlope.Formalism.RankGapBounds.WeightedMeanData
open RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.WeightedSlopeBounds
open RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.LErr

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
  (A0 : AddSubgroup H) {W : A0 → Type} {m f : ℕ} (TT : Finset H)
  (D0 : Data A0 W TT m f)
  (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
  (frob : ℕ → AlpogeNativeE0 × H)
  (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
  (N : ℕ) (a : H → ℝ) (w : H → Fin m → AlpogeNativeE0 × H → ℝ)
  (eP : Fin f ≃ (alpogeNativePhiSet H))

/-- The visible arithmetic entries are the literal native source. All other
entries, in particular the finite-place gain `Ga`, come unchanged from `D0`. -/
def physicalData : Data A0 W TT m f :=
  { D0 with
    gam := Real.eulerMascheroniConstant
    LpL := (ell (alpogeNativeChC H)).re
    aT := fun t => a t
    w := fun u j ρ => w u j (eP ρ)
    ASK := fun u => ∑ t ∈ TT, ∑ j : Fin m,
      (alpogeNativeFullKernelASK inertia frob N (a t) t (w u j)).re }

/-- The physical attachment never chooses a replacement gain to make the
loss inequality true. -/
theorem physicalData_Ga (u : A0) :
    (physicalData A0 TT D0 inertia frob ell N a w eP).Ga u = D0.Ga u := rfl

/-- The original closed logarithmic MAIN term, on precisely the same CM
type and original widths, equals the finite slope data's MAIN entry. -/
theorem physicalData_main (u : A0) :
    (physicalData A0 TT D0 inertia frob ell N a w eP).Main u =
      ∑ t ∈ TT, ∑ j : Fin m, (alpogeNativeMAIN ell (a t) (w u j)).re := by
  have hf : (f : ℝ) = ((alpogeNativePhiSet H).card : ℝ) := by
    have hc := Fintype.card_congr eP
    simp only [Fintype.card_fin, Fintype.card_coe] at hc
    exact_mod_cast hc
  have hsum : ∀ g : AlpogeNativeE0 × H → ℝ,
      ∑ ρ : Fin f, g (eP ρ) = ∑ ρ ∈ alpogeNativePhiSet H, g ρ := by
    intro g
    rw [← Finset.sum_coe_sort (alpogeNativePhiSet H)]
    exact Equiv.sum_comp eP (fun ρ => g ρ)
  change (∑ j : Fin m, ∑ t : TT,
    a t * (Real.log (a t) - 1 - Real.eulerMascheroniConstant +
      (ell (alpogeNativeChC H)).re -
      (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (w u j (eP ρ)))) = _
  rw [Finset.sum_comm, ← Finset.sum_coe_sort TT]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [hf, alpogeNativeMAIN, Complex.mul_re, Complex.add_re,
    Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hsum (fun ρ => Real.log (w u j ρ))]

/-- Exact same-subgroup arithmetic identity before any inequality is used. -/
theorem physicalTopExcess_eq_meanGap :
    alpogeNativePhysicalSubgroupTopExcess A0 inertia frob ell N TT a w =
      umean (physicalData A0 TT D0 inertia frob ell N a w eP).ASK -
        umean (physicalData A0 TT D0 inertia frob ell N a w eP).Main := by
  have hgap : ∀ u : A0,
      (∑ t ∈ TT, ∑ j : Fin m,
        (alpogeNativeFullKernelASK inertia frob N (a t) t (w u j) -
          alpogeNativeMAIN ell (a t) (w u j)).re) =
        (physicalData A0 TT D0 inertia frob ell N a w eP).ASK u -
          (physicalData A0 TT D0 inertia frob ell N a w eP).Main u := by
    intro u
    rw [physicalData_main A0 TT D0 inertia frob ell N a w eP u]
    change (∑ t ∈ TT, ∑ j : Fin m,
        (alpogeNativeFullKernelASK inertia frob N (a t) t (w u j) -
          alpogeNativeMAIN ell (a t) (w u j)).re) =
      (∑ t ∈ TT, ∑ j : Fin m,
        (alpogeNativeFullKernelASK inertia frob N (a t) t (w u j)).re) -
        (∑ t ∈ TT, ∑ j : Fin m, (alpogeNativeMAIN ell (a t) (w u j)).re)
    simp only [Complex.sub_re, Finset.sum_sub_distrib]
  unfold alpogeNativePhysicalSubgroupTopExcess
  simp_rw [hgap]
  unfold umean
  rw [Finset.sum_sub_distrib]
  ring

variable [∀ u, Fintype (W u)] [∀ u, Nonempty (W u)]
  (C : Consts) (Xpp : ℝ)

local notation "DP" => physicalData A0 TT D0 inertia frob ell N a w eP

/-- The averaged finite signed-slope theorem on the literal physical source.
Only the means of `ASK - Ga` and `IO` are required; every geometric source
hypothesis remains on the same constructed data. -/
theorem physicalTopExcess_le_errorTerm_of_meanLoss
    (hS : (DP).HidaSetting C) (hDIV : (DP).DIV C) (hE : EComp5 DP C)
    (hH : (DP).HComp C) (hCount : Count5 DP C) (hSl : (DP).Slopes C)
    (hSN : QuotientSlopeBoundsWith DP C Xpp) (hLoss : (DP).Losses C)
    (hSI : (DP).SlopeIneq) (hHH : (DP).HHBound C) (hFP : (DP).FParams) :
    alpogeNativePhysicalSubgroupTopExcess A0 inertia frob ell N TT a w ≤
      errorTermWith DP C Xpp := by
  rw [physicalTopExcess_eq_meanGap A0 TT D0 inertia frob ell N a w eP]
  have h := weighted_mean_bound_statement DP C Xpp (inferInstance : Nonempty A0)
    hS hDIV hE hH hCount hSl hSN hLoss hSI hHH hFP
  linarith

/-- Compatibility with the original pointwise-loss supplier. The source and
all other geometric hypotheses are unchanged. -/
theorem physicalTopExcess_le_errorTerm
    (hS : (DP).HidaSetting C) (hDIV : (DP).DIV C) (hE : EComp5 DP C)
    (hH : (DP).HComp C) (hCount : Count5 DP C) (hSl : (DP).Slopes C)
    (hSN : QuotientSlopeBoundsWith DP C Xpp) (hLoss : LossBounds DP C)
    (hSI : (DP).SlopeIneq) (hHH : (DP).HHBound C) (hFP : (DP).FParams) :
    alpogeNativePhysicalSubgroupTopExcess A0 inertia frob ell N TT a w ≤
      errorTermWith DP C Xpp := by
  exact physicalTopExcess_le_errorTerm_of_meanLoss A0 TT D0 inertia frob ell N a w eP
    C Xpp hS hDIV hE hH hCount hSl hSN (losses_of_losses5 DP C hLoss) hSI hHH hFP

/-- The source's strong error windows pay the entire signed finite error,
including the global trace-error term. The geometric hypotheses remain
explicit; this theorem supplies no witness for them. -/
theorem physicalTopExcess_le_strongWindowError
    (hS : (DP).HidaSetting C) (hDIV : (DP).DIV C) (hE : EComp5 DP C)
    (hH : (DP).HComp C) (hCount : Count5 DP C) (hSl : (DP).Slopes C)
    (hSN : QuotientSlopeBoundsWith DP C Xpp) (hLoss : LossBounds DP C)
    (hSI : (DP).SlopeIneq) (hHH : (DP).HHBound C) (hFP : (DP).FParams)
    (eK K : ℝ) (hWin : ErrWindows DP C Xpp eK K)
    (hLarge : LargeX D0.x D0.ε K C.cHH eK) :
    alpogeNativePhysicalSubgroupTopExcess A0 inertia frob ell N TT a w ≤
      D0.x ^ (CErr C * D0.ε) *
        ((TT.card : ℝ) * D0.a * (1 + (m : ℝ) ^ 2 / D0.k) +
          (m : ℝ) * (D0.B0 + D0.Nc)) := by
  calc
    _ ≤ errorTermWith DP C Xpp :=
      physicalTopExcess_le_errorTerm A0 TT D0 inertia frob ell N a w eP
        C Xpp hS hDIV hE hH hCount hSl hSN hLoss hSI hHH hFP
    _ ≤ _ := by
      simpa only [ErrText, Data.nT, Fintype.card_coe, physicalData] using
        (error_sizes DP C Xpp eK K hWin hLarge)

/-- The same signed geometric error after division by the actually earned
projection divisor. Its positivity follows from the original finite counts
and the positive source width in `HidaSetting`. -/
theorem physicalTopExcess_div_le_strongWindowError
    (hS : (DP).HidaSetting C) (hDIV : (DP).DIV C) (hE : EComp5 DP C)
    (hH : (DP).HComp C) (hCount : Count5 DP C) (hSl : (DP).Slopes C)
    (hSN : QuotientSlopeBoundsWith DP C Xpp) (hLoss : LossBounds DP C)
    (hSI : (DP).SlopeIneq) (hHH : (DP).HHBound C) (hFP : (DP).FParams)
    (eK K : ℝ) (hWin : ErrWindows DP C Xpp eK K)
    (hLarge : LargeX D0.x D0.ε K C.cHH eK)
    (T2 : Finset H) (hTT : TT.Nonempty) (hT2 : T2.Nonempty) (hm : 0 < m) :
    alpogeNativePhysicalSubgroupTopExcess A0 inertia frob ell N TT a w /
        alpogeNativeProjectionDivisor TT T2 m D0.b ≤
      (D0.x ^ (CErr C * D0.ε) *
        ((TT.card : ℝ) * D0.a * (1 + (m : ℝ) ^ 2 / D0.k) +
          (m : ℝ) * (D0.B0 + D0.Nc))) /
        alpogeNativeProjectionDivisor TT T2 m D0.b := by
  have hQ : 0 < alpogeNativeProjectionDivisor TT T2 m D0.b :=
    alpogeNativeProjectionDivisor_pos TT T2 hTT hT2 m hm D0.b hS.2.1
  exact div_le_div_of_nonneg_right
    (physicalTopExcess_le_strongWindowError A0 TT D0 inertia frob ell N a w eP
      C Xpp hS hDIV hE hH hCount hSl hSN hLoss hSI hHH hFP eK K hWin hLarge)
    hQ.le

/-- Mean loss bounds and the two auxiliary geometric budgets give the original
three costs after division by the actual thick-source divisor. This keeps
the complete signed source and requires no pointwise loss estimate. -/
theorem physicalTopExcess_div_le_normalizedGeometricCosts_of_meanLoss
    (hS : (DP).HidaSetting C) (hDIV : (DP).DIV C) (hE : EComp5 DP C)
    (hH : (DP).HComp C) (hCount : Count5 DP C) (hSl : (DP).Slopes C)
    (hSN : QuotientSlopeBoundsWith DP C Xpp) (hLoss : (DP).Losses C)
    (hSI : (DP).SlopeIneq) (hHH : (DP).HHBound C) (hFP : (DP).FParams)
    (eK K : ℝ) (hWin : ErrWindows DP C Xpp eK K)
    (hLarge : LargeX D0.x D0.ε K C.cHH eK)
    (T2 : Finset H) (hTT : TT.Nonempty) (hT2 : T2.Nonempty) (hm : 0 < m)
    (hB0 : D0.B0 ≤ 2 * (Fintype.card H : ℝ) * m * D0.b * D0.x ^ D0.ε)
    (hNc : D0.Nc ≤ (T2.card : ℝ) * D0.k * D0.b * D0.x ^ D0.ε /
      ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) / D0.x ^ D0.ε))) :
    alpogeNativePhysicalSubgroupTopExcess A0 inertia frob ell N TT a w /
        alpogeNativeProjectionDivisor TT T2 m D0.b ≤
      D0.x ^ (CErr C * D0.ε) *
        alpogeNativeNormalizedGeometricCosts TT.card
          (alpogeNativeProjectionDensity T2) (Fintype.card H) m D0.b D0.k D0.a
          (D0.x ^ D0.ε) := by
  have hBracket :
      (TT.card : ℝ) * D0.a * (1 + (m : ℝ) ^ 2 / D0.k) +
          (m : ℝ) * (D0.B0 + D0.Nc) ≤
        alpogeNativeGeometricErrorBracket TT.card T2.card (Fintype.card H) m
          D0.b D0.k D0.a (D0.x ^ D0.ε) := by
    unfold alpogeNativeGeometricErrorBracket
    exact add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (add_le_add hB0 hNc) (Nat.cast_nonneg m))
  have hError : errorTermWith DP C Xpp ≤
      D0.x ^ (CErr C * D0.ε) *
        ((TT.card : ℝ) * D0.a * (1 + (m : ℝ) ^ 2 / D0.k) +
          (m : ℝ) * (D0.B0 + D0.Nc)) := by
    simpa only [ErrText, Data.nT, Fintype.card_coe, physicalData] using
      (error_sizes DP C Xpp eK K hWin hLarge)
  have hScaled :=
    ((physicalTopExcess_le_errorTerm_of_meanLoss A0 TT D0 inertia frob ell N a w eP
      C Xpp hS hDIV hE hH hCount hSl hSN hLoss hSI hHH hFP).trans hError).trans
        (mul_le_mul_of_nonneg_left hBracket (Real.rpow_nonneg hS.1.le _))
  have hQ : 0 < alpogeNativeProjectionDivisor TT T2 m D0.b :=
    alpogeNativeProjectionDivisor_pos TT T2 hTT hT2 m hm D0.b hS.2.1
  calc
    _ ≤ (D0.x ^ (CErr C * D0.ε) *
        alpogeNativeGeometricErrorBracket TT.card T2.card (Fintype.card H) m
          D0.b D0.k D0.a (D0.x ^ D0.ε)) /
        alpogeNativeProjectionDivisor TT T2 m D0.b :=
      div_le_div_of_nonneg_right hScaled hQ.le
    _ = _ := by
      rw [mul_div_assoc]
      exact congrArg (fun z : ℝ => D0.x ^ (CErr C * D0.ε) * z)
        (alpogeNativeGeometricErrorBracket_div_projectionDivisor TT T2 m
          D0.b D0.k D0.a (D0.x ^ D0.ε) hTT hT2 hm hS.2.1)

/-- The original pointwise-loss normalized endpoint follows by averaging
its loss hypotheses on the same physical data. -/
theorem physicalTopExcess_div_le_normalizedGeometricCosts
    (hS : (DP).HidaSetting C) (hDIV : (DP).DIV C) (hE : EComp5 DP C)
    (hH : (DP).HComp C) (hCount : Count5 DP C) (hSl : (DP).Slopes C)
    (hSN : QuotientSlopeBoundsWith DP C Xpp) (hLoss : LossBounds DP C)
    (hSI : (DP).SlopeIneq) (hHH : (DP).HHBound C) (hFP : (DP).FParams)
    (eK K : ℝ) (hWin : ErrWindows DP C Xpp eK K)
    (hLarge : LargeX D0.x D0.ε K C.cHH eK)
    (T2 : Finset H) (hTT : TT.Nonempty) (hT2 : T2.Nonempty) (hm : 0 < m)
    (hB0 : D0.B0 ≤ 2 * (Fintype.card H : ℝ) * m * D0.b * D0.x ^ D0.ε)
    (hNc : D0.Nc ≤ (T2.card : ℝ) * D0.k * D0.b * D0.x ^ D0.ε /
      ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) / D0.x ^ D0.ε))) :
    alpogeNativePhysicalSubgroupTopExcess A0 inertia frob ell N TT a w /
        alpogeNativeProjectionDivisor TT T2 m D0.b ≤
      D0.x ^ (CErr C * D0.ε) *
        alpogeNativeNormalizedGeometricCosts TT.card
          (alpogeNativeProjectionDensity T2) (Fintype.card H) m D0.b D0.k D0.a
          (D0.x ^ D0.ε) := by
  exact physicalTopExcess_div_le_normalizedGeometricCosts_of_meanLoss
    A0 TT D0 inertia frob ell N a w eP C Xpp hS hDIV hE hH hCount hSl hSN
    (losses_of_losses5 DP C hLoss) hSI hHH hFP eK K hWin hLarge T2 hTT hT2 hm hB0 hNc

end RHLean.Analysis.AlpogeNativeSignedSlope

import RHLean.Geometry.AlpogeSignedSlope.Formalism.SizeWindowBrackets.QuotientSlopeBoundsWith


/-!
Native finite signed-slope assembly from Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.
Source: `src/Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean`.
The finite proofs and their hypotheses are retained. This module does not
construct the geometric family or assume an arithmetic cancellation bound.
The source mirror states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Real

namespace RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.LErr

open RHLean.Geometry.AlpogeSignedSlope.Formalism.RankGapBounds.WeightedMeanData RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.WeightedSlopeBounds

noncomputable section

section
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}

def ErrText (D : Data U0 W Top m f) : ℝ :=
  D.nT * D.a * (1 + (m : ℝ) ^ 2 / D.k) + (m : ℝ) * (D.B0 + D.Nc)

def CErr (C : Consts) : ℝ := C.eDiv + C.eLoss + 3

def KBig (K cHH eK : ℝ) : ℝ := 200 * (1 + K) ^ 2 * (1 + cHH) * (1 + eK)

def ConstsBound (C : Consts) (K : ℝ) : Prop :=
  0 ≤ C.cDiv ∧ C.cDiv ≤ K ∧ 0 ≤ C.cE ∧ C.cE ≤ K ∧ 0 ≤ C.cH ∧ C.cH ≤ K ∧
  0 ≤ C.cCount ∧ C.cCount ≤ K ∧ 0 ≤ C.cSlope ∧ C.cSlope ≤ K ∧ 0 ≤ C.cSl1 ∧ C.cSl1 ≤ K ∧
  0 ≤ C.cLoss ∧ C.cLoss ≤ K ∧ 0 ≤ C.eDiv ∧ 0 ≤ C.eLoss ∧ 0 ≤ C.cHH

def ErrWindows0 (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ) : Prop :=
  1 ≤ D.x ∧ 0 < D.ε ∧ D.ε ≤ 1 ∧
  1 ≤ D.b ∧ D.x * D.b ≤ D.a ∧
  1 ≤ D.nT ∧
  (m : ℝ) ≤ D.x ^ ((1 : ℝ) / 2 + D.ε / 2) ∧ D.x * m ≤ D.k ∧
  0 ≤ eK ∧ 1 ≤ D.k ∧ D.k ≤ D.x ^ eK ∧ D.k ≤ D.a ∧
  0 ≤ D.L ∧ D.L ≤ 2 * D.x ^ D.ε ∧ 0 ≤ D.La ∧ D.La ≤ 2 * D.x ^ D.ε ∧
  0 ≤ D.b' ∧ D.k * D.b' ≤ D.a ∧
  0 ≤ Xpp ∧ Xpp ≤ D.a ∧
  (∀ t, 0 ≤ D.aT t ∧ D.aT t ≤ 2 * D.a) ∧
  0 ≤ D.B0 ∧ 0 ≤ D.Nc ∧
  (∀ u0, Real.log (Fintype.card (W u0) : ℝ) ≤ (D.k - 3) * Real.log 2) ∧
  D.delBar ≤ 1 / 2 ∧ 0 ≤ D.etaBar ∧ 0 ≤ D.eBar ∧
  ConstsBound C K

def ErrWindows (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ) : Prop :=
  ErrWindows0 D C Xpp eK K ∧
  (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b) ≤ K * D.x ^ D.ε * (D.nT * D.a)

def ErrWindowsWeak (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ) : Prop :=
  ErrWindows0 D C Xpp eK K ∧ D.etaBar ≤ 1 ∧ D.eBar ≤ 1

end

def LargeX (x ε K cHH eK : ℝ) : Prop := Real.log x ≤ x ^ ε ∧ KBig K cHH eK ≤ x ^ ε

def ErrorFormsUnderWindows : Prop :=
  ∀ {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ),
    ErrWindows D C Xpp eK K → LargeX D.x D.ε K C.cHH eK →
    errorTermWith D C Xpp ≤ D.x ^ (CErr C * D.ε) * ErrText D

end

end RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.LErr

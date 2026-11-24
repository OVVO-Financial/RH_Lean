import RHLean.Analysis.AlpogeNativeBoundHandoff
import RHLean.Analysis.AlpogeNativeBoundConsequences

/-!
# Exact native bound handoff: source, quantifier, and terminal-axiom audit

The typed examples below pin the complete prime-power source, the order of
the uniform quantifiers, and the exact NNS and candidate-capacity corrections.
The nonempty-window check requests arbitrarily late windows starting beyond
`2`; an empty interval cannot satisfy this audited consequence.

Every critical quantitative bound remains an explicit hypothesis. Standard
terminal axioms certify the conditional proofs, not an upstream supplier or
an unconditional proof of the native source bound or RH.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis.AlpogeNativeBoundHandoffAudit

open AlpogeNativeBoundHandoff

/- The source is the entire von Mangoldt sum, not its prime-only part. -/
example (x : ℝ) :
    statementOCSz x =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / (n : ℝ) - 1) := rfl

example (x : ℝ) :
    statementOCGz x =
      statementOCSz x - x * Real.log x +
        (1 + Real.eulerMascheroniConstant) * x := rfl

example (x : ℝ) : statementOCGz x = alpogeNativeGzArithmetic x :=
  statementOCGz_eq_native x

example (N : ℕ) : statementOCGz (N : ℝ) = nativeAlpogeGz N :=
  statementOCGz_natCast N

/- These definitional checks expose every bound and scale quantifier. -/
example (δ : ℝ) :
    RealWindowBound δ ↔
      ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧
        ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)),
          alpogeNativeGzArithmetic y ≤ C * y ^ (1 / 2 + η) := Iff.rfl

example :
    SquareClockBound ↔
      ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∃ R₀ : ℕ,
        ∀ R : ℕ, 2 ≤ R → R₀ ≤ R →
          nativeAlpogeGz (R ^ 2 - 1) ≤ C * (R : ℝ) ^ (1 + η) := Iff.rfl

example :
    EventualRealBound ↔
      ∀ η : ℝ, 0 < η → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
        alpogeNativeGzArithmetic x ≤ C * x ^ (1 / 2 + η) := Iff.rfl

example (K ε₁ : ℝ) :
    SmallEpsilonWindowBound K ε₁ ↔
      ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∃ C : ℝ, ∀ Y₀ : ℝ, ∃ Y : ℝ,
        Y₀ ≤ Y ∧ ∀ y ∈ Set.Icc Y (Y ^ ((3 : ℝ) / 2)),
          statementOCGz y ≤ C * y ^ (1 / 2 + K * ε) := Iff.rfl

example {K ε₁ : ℝ} (hε₁ : 0 < ε₁) (h : SmallEpsilonWindowBound K ε₁) :
    RealWindowBound (1 / 2) :=
  realWindowBound_of_smallEpsilonWindowBound hε₁ h

/-- The conditional window handoff supplies genuinely nonempty windows,
with one constant selected before their arbitrarily late starting point. -/
theorem smallEpsilonWindow_has_nonempty_late_windows
    {K ε₁ : ℝ} (hε₁ : 0 < ε₁) (h : SmallEpsilonWindowBound K ε₁)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, ∀ Y₀ : ℝ, ∃ Y : ℝ, max Y₀ 2 ≤ Y ∧
      (Set.Icc Y (Y ^ ((3 : ℝ) / 2))).Nonempty ∧
      ∀ y ∈ Set.Icc Y (Y ^ ((3 : ℝ) / 2)),
        alpogeNativeGzArithmetic y ≤ C * y ^ (1 / 2 + η) := by
  obtain ⟨C, hC⟩ := realWindowBound_of_smallEpsilonWindowBound hε₁ h η hη
  refine ⟨C, fun Y₀ => ?_⟩
  obtain ⟨Y, hY, hwindow⟩ := hC (max Y₀ 2)
  have hY2 : (2 : ℝ) ≤ Y := (le_max_right Y₀ 2).trans hY
  have hupper : Y ≤ Y ^ ((3 : ℝ) / 2) :=
    Real.self_le_rpow_of_one_le (by linarith) (by norm_num)
  refine ⟨Y, hY, ⟨Y, le_rfl, hupper⟩, ?_⟩
  intro y hy
  apply hwindow y
  have hexp : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
  simpa only [hexp] using hy

example {δ : ℝ} (hδ : 0 < δ) (h : RealWindowBound δ) : RiemannHypothesis :=
  riemannHypothesis_of_realWindowBound hδ h

example (h : SquareClockBound) : RiemannHypothesis :=
  riemannHypothesis_of_squareClockBound h

example (h : EventualRealBound) : RiemannHypothesis :=
  riemannHypothesis_of_eventualRealBound h

example {K ε₁ : ℝ} (hε₁ : 0 < ε₁) (h : SmallEpsilonWindowBound K ε₁) :
    RiemannHypothesis :=
  riemannHypothesis_of_smallEpsilonWindowBound hε₁ h

example (h : EventualRealBound) :
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → 1 ≤ N →
        nativeAlpogeGz N ≤ C * (N : ℝ) ^ (1 / 2 + η) :=
  eventualNativeBound_of_eventualRealBound h

/- The signed history keeps all centering terms and both NNS channels. -/
example (N : ℕ) :
    alpogeGzNNSHistory N =
      alpogeGzNNSUpper N - alpogeGzNNSLower N +
        (harmonic N : ℝ) - Real.log (N : ℝ) +
          Real.eulerMascheroniConstant := rfl

/- Candidate capacity includes the complete proper-prime-power correction. -/
example (S : Finset ℕ) (N : ℕ) :
    nativeSquareCandidateCapacity S N =
      (∑ n ∈ S, nativeSquareCandidateWeight N n) +
        nativeSquareProperPowerCapacity N - (N : ℝ) * Real.log (N : ℝ) +
          (1 + Real.eulerMascheroniConstant) * (N : ℝ) := rfl

example (N : ℕ) :
    nativeSquareProperPowerCapacity N =
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ n.Prime),
        Λ n * nativeSquareCandidateKernel N n := rfl

example (N : ℕ) (hN : 1 ≤ N) :
    nativeAlpogeGz N = (N : ℝ) * alpogeGzNNSHistory N :=
  nativeAlpogeGz_eq_NNSHistory N hN

example (N : ℕ) (hN : 1 ≤ N) :
    alpogeGzNNSHistory N = nativeAlpogeGz N / (N : ℝ) :=
  alpogeGzNNSHistory_eq_normalized_nativeGz N hN

example (N : ℕ) (hN : 1 ≤ N) (C η : ℝ) :
    nativeAlpogeGz N ≤ C * (N : ℝ) ^ ((1 : ℝ) / 2 + η) ↔
      alpogeGzNNSHistory N ≤ C * (N : ℝ) ^ (-(1 : ℝ) / 2 + η) :=
  nativeAlpogeGz_rpow_le_iff_NNSHistory N hN C η

example (N : ℕ) (hN : 1 ≤ N) (C η : ℝ) :
    nativeAlpogeGz N ≤ C * (N : ℝ) ^ ((1 : ℝ) / 2 + η) ↔
      alpogeGzNNSUpper N ≤
        alpogeGzNNSLower N + Real.log (N : ℝ) - (harmonic N : ℝ) -
          Real.eulerMascheroniConstant +
          C * (N : ℝ) ^ (-(1 : ℝ) / 2 + η) :=
  nativeAlpogeGz_rpow_le_iff_NNSUpper N hN C η

example :
    (∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → 1 ≤ N →
        nativeAlpogeGz N ≤ C * (N : ℝ) ^ ((1 : ℝ) / 2 + η)) ↔
    (∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → 1 ≤ N →
        alpogeGzNNSHistory N ≤ C * (N : ℝ) ^ (-(1 : ℝ) / 2 + η)) :=
  nativeAlpogeGz_eventual_rpow_iff_NNSHistory

example (cutoff : ℕ → ℕ) (hcutoff : ∀ r, cutoff r ≤ r)
    (N : ℕ) (C η : ℝ) :
    nativeAlpogeGz N ≤ C * (N : ℝ) ^ ((1 : ℝ) / 2 + η) ↔
      nativeSquareCandidateCapacity (nativeSquarePrefixCandidates cutoff N) N -
          C * (N : ℝ) ^ ((1 : ℝ) / 2 + η) ≤
        nativeSquareCompositeRemoval (nativeSquarePrefixCandidates cutoff N) N :=
  nativeAlpogeGz_rpow_le_iff_squarePrefixRemoval cutoff hcutoff N C η

example
    (h : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∃ R₀ : ℕ,
      ∀ R : ℕ, 2 ≤ R → R₀ ≤ R →
        alpogeGzNNSHistory (R ^ 2 - 1) ≤
          C * ((R ^ 2 - 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2 + η)) :
    RiemannHypothesis :=
  riemannHypothesis_of_eventual_squareClock_NNSHistory h

example (cutoff : ℕ → ℕ) (hcutoff : ∀ r, cutoff r ≤ r)
    (h : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∃ R₀ : ℕ,
      ∀ R : ℕ, 2 ≤ R → R₀ ≤ R →
        nativeSquareCandidateCapacity
            (nativeSquarePrefixCandidates cutoff (R ^ 2 - 1)) (R ^ 2 - 1) -
            C * (R : ℝ) ^ (1 + η) ≤
          nativeSquareCompositeRemoval
            (nativeSquarePrefixCandidates cutoff (R ^ 2 - 1)) (R ^ 2 - 1)) :
    RiemannHypothesis :=
  riemannHypothesis_of_eventual_squareClock_squarePrefixRemoval cutoff hcutoff h

/- One shared constant and threshold precede every candidate set choice. -/
example (h : EventualRealBound) :
    RiemannHypothesis ∧
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → 1 ≤ N →
        (alpogeGzNNSHistory N ≤ C * (N : ℝ) ^ (-(1 : ℝ) / 2 + η)) ∧
        ∀ candidates : Finset ℕ,
          candidates ⊆ Finset.Icc 1 N →
          (∀ p ∈ Finset.Icc 1 N, p.Prime → p ∈ candidates) →
          nativeSquareCandidateCapacity candidates N -
              C * (N : ℝ) ^ ((1 : ℝ) / 2 + η) ≤
            nativeSquareCompositeRemoval candidates N :=
  nativeAlpogeConsequences_of_eventualRealBound h

end RHLean.Analysis.AlpogeNativeBoundHandoffAudit

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let roots : Array Name := #[
    ``RHLean.Analysis.AlpogeNativeBoundHandoff.statementOCSz_eq_nativePrincipalPrimeSum,
    ``RHLean.Analysis.AlpogeNativeBoundHandoff.statementOCGz_eq_native,
    ``RHLean.Analysis.AlpogeNativeBoundHandoff.statementOCGz_natCast,
    ``RHLean.Analysis.AlpogeNativeBoundHandoff.eventualNativeBound_of_eventualRealBound,
    ``RHLean.Analysis.AlpogeNativeBoundHandoff.realWindowBound_of_eventualRealBound,
    ``RHLean.Analysis.AlpogeNativeBoundHandoff.realWindowBound_of_smallEpsilonWindowBound,
    ``RHLean.Analysis.AlpogeNativeBoundHandoff.riemannHypothesis_of_realWindowBound,
    ``RHLean.Analysis.AlpogeNativeBoundHandoff.riemannHypothesis_of_squareClockBound,
    ``RHLean.Analysis.AlpogeNativeBoundHandoff.riemannHypothesis_of_eventualRealBound,
    ``RHLean.Analysis.AlpogeNativeBoundHandoff.riemannHypothesis_of_smallEpsilonWindowBound,
    ``RHLean.Analysis.AlpogeNativeBoundHandoffAudit.smallEpsilonWindow_has_nonempty_late_windows,
    ``RHLean.Analysis.nativeAlpogeGz_eq_erdosGz,
    ``RHLean.Analysis.alpogeGzNNSHistory_eq_nativeCenteredHistory,
    ``RHLean.Analysis.nativeAlpogeGz_eq_NNSHistory,
    ``RHLean.Analysis.alpogeGzNNSHistory_eq_normalized_nativeGz,
    ``RHLean.Analysis.nativeAlpogeGz_rpow_le_iff_NNSHistory,
    ``RHLean.Analysis.nativeAlpogeGz_rpow_le_iff_NNSUpper,
    ``RHLean.Analysis.nativeAlpogeGz_eventual_rpow_iff_NNSHistory,
    ``RHLean.Analysis.nativeAlpogeGz_eventual_rpow_iff_candidateRemoval,
    ``RHLean.Analysis.nativeAlpogeGz_rpow_le_iff_squarePrefixRemoval,
    ``RHLean.Analysis.nativeAlpogeGz_eventual_rpow_iff_squarePrefixRemoval,
    ``RHLean.Analysis.riemannHypothesis_of_eventual_squareClock_NNSHistory,
    ``RHLean.Analysis.riemannHypothesis_of_eventual_squareClock_squarePrefixRemoval,
    ``RHLean.Analysis.nativeAlpogeConsequences_of_eventualRealBound]
  let env ← getEnv
  for root in roots do
    unless env.contains root do
      throwError "Missing native bound handoff declaration: {root}"
    let axioms ← liftCoreM (Lean.collectAxioms root)
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unapproved terminal axiom for {root}: {ax}"
    logInfo m!"PASS native conditional bound handoff {root}: {axioms}"

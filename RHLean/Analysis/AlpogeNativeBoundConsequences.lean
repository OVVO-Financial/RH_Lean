import RHLean.Analysis.AlpogeExactNNSGzBridge
import RHLean.Analysis.AlpogeNativeBoundHandoff
import RHLean.Analysis.AlpogeNativeSquareClockCriterion
import RHLean.Analysis.AlpogeNativeSquareCandidateCapacity

/-!
# Exact native consequences of the complete Alpoge source bound

The native `Gz`, its complete centered Chebyshev history, its degree-one
NNS upper/lower masses, and the completed candidate-capacity accounting
describe the same signed arithmetic source. This file transfers the
one-sided bound between those coordinates with its exact constants and
thresholds. The harmonic/Euler correction and proper prime powers remain.

The conditional RH theorems consume an explicitly assumed history, removal,
or complete real source bound in the existing native RH criterion. The
combined return theorem uses the same constant and threshold for the history
and every admissible candidate set, directly from the supplied source bound.
These theorems do not prove that bound, construct its geometric supplier,
infer an absolute estimate, or assert an individual square-block prime count.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace RHLean.Analysis

/-- The older Erdos name and the current native name have the same literal
complete prime-power definition, at every natural endpoint. -/
theorem nativeAlpogeGz_eq_erdosGz (N : ℕ) :
    nativeAlpogeGz N = alpogeErdosGz N := rfl

/-- The NNS source is the actual centered native Chebyshev history. -/
theorem alpogeGzNNSHistory_eq_nativeCenteredHistory (N : ℕ) :
    alpogeGzNNSHistory N = nativeAlpogeCenteredHistory N := by
  exact alpogeGzNNSHistory_eq_centeredHistory N

/-- The complete native source equals `N` times its exact signed NNS
history. The endpoint is `N-1` inside the history, as in the original sum. -/
theorem nativeAlpogeGz_eq_NNSHistory (N : ℕ) (hN : 1 ≤ N) :
    nativeAlpogeGz N = (N : ℝ) * alpogeGzNNSHistory N := by
  rw [nativeAlpogeGz_eq_erdosGz]
  exact alpogeGz_eq_exact_NNSHistory N hN

/-- Normalization divides the complete signed source by the positive
integer endpoint; it does not divide the two NNS channels separately. -/
theorem alpogeGzNNSHistory_eq_normalized_nativeGz (N : ℕ) (hN : 1 ≤ N) :
    alpogeGzNNSHistory N = nativeAlpogeGz N / (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [nativeAlpogeGz_eq_NNSHistory N hN, mul_div_cancel_left₀ _ hNpos.ne']

private theorem nativeAlpogeCriticalPower_div
    (N : ℕ) (hN : 1 ≤ N) (C η : ℝ) :
    (C * (N : ℝ) ^ ((1 : ℝ) / 2 + η)) / (N : ℝ) =
      C * (N : ℝ) ^ (-(1 : ℝ) / 2 + η) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hpow : (N : ℝ) ^ ((1 : ℝ) / 2 + η) =
      (N : ℝ) * (N : ℝ) ^ (-(1 : ℝ) / 2 + η) := by
    calc
      (N : ℝ) ^ ((1 : ℝ) / 2 + η) =
          (N : ℝ) ^ ((1 : ℝ) + (-(1 : ℝ) / 2 + η)) := by
            congr 1
            ring
      _ = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(1 : ℝ) / 2 + η) :=
        Real.rpow_add hNpos (1 : ℝ) (-(1 : ℝ) / 2 + η)
      _ = (N : ℝ) * (N : ℝ) ^ (-(1 : ℝ) / 2 + η) := by
        rw [Real.rpow_one]
  rw [hpow, mul_div_assoc, mul_div_cancel_left₀ _ hNpos.ne']

/-- Exact one-sided critical-power translation. Neither the constant nor
the exponent is changed, except for the necessary division by `N`. -/
theorem nativeAlpogeGz_rpow_le_iff_NNSHistory
    (N : ℕ) (hN : 1 ≤ N) (C η : ℝ) :
    nativeAlpogeGz N ≤ C * (N : ℝ) ^ ((1 : ℝ) / 2 + η) ↔
      alpogeGzNNSHistory N ≤ C * (N : ℝ) ^ (-(1 : ℝ) / 2 + η) := by
  rw [nativeAlpogeGz_eq_erdosGz,
    alpogeGz_bound_iff_exact_NNS N hN,
    nativeAlpogeCriticalPower_div N hN C η]

/-- The same bound written as the actual upper NNS mass versus the lower
mass. The harmonic term, logarithm and positive Euler constant are retained
with their exact signs. No bound on either mass separately is asserted. -/
theorem nativeAlpogeGz_rpow_le_iff_NNSUpper
    (N : ℕ) (hN : 1 ≤ N) (C η : ℝ) :
    nativeAlpogeGz N ≤ C * (N : ℝ) ^ ((1 : ℝ) / 2 + η) ↔
      alpogeGzNNSUpper N ≤
        alpogeGzNNSLower N + Real.log (N : ℝ) - (harmonic N : ℝ) -
          Real.eulerMascheroniConstant +
          C * (N : ℝ) ^ (-(1 : ℝ) / 2 + η) := by
  rw [nativeAlpogeGz_rpow_le_iff_NNSHistory N hN C η]
  unfold alpogeGzNNSHistory
  constructor <;> intro h <;> linarith only [h]

/-- The full eventual natural-input statement is equivalent to the
normalized history statement. Each direction reuses the identical
`C_eta` and natural threshold chosen in the other statement. -/
theorem nativeAlpogeGz_eventual_rpow_iff_NNSHistory :
    (∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → 1 ≤ N →
        nativeAlpogeGz N ≤ C * (N : ℝ) ^ ((1 : ℝ) / 2 + η)) ↔
    (∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → 1 ≤ N →
        alpogeGzNNSHistory N ≤ C * (N : ℝ) ^ (-(1 : ℝ) / 2 + η)) := by
  constructor
  · intro h η hη
    obtain ⟨C, hC, N₀, hbound⟩ := h η hη
    refine ⟨C, hC, N₀, fun N hN₀ hN => ?_⟩
    exact (nativeAlpogeGz_rpow_le_iff_NNSHistory N hN C η).mp
      (hbound N hN₀ hN)
  · intro h η hη
    obtain ⟨C, hC, N₀, hbound⟩ := h η hη
    refine ⟨C, hC, N₀, fun N hN₀ hN => ?_⟩
    exact (nativeAlpogeGz_rpow_le_iff_NNSHistory N hN C η).mpr
      (hbound N hN₀ hN)

/-- For any actual prime-complete candidate family, the uniform source
bound is exactly the stated lower bound on cumulative composite removal.
The existing capacity keeps its independent proper-prime-power term.
Both directions preserve the same constants and thresholds. -/
theorem nativeAlpogeGz_eventual_rpow_iff_candidateRemoval
    (candidates : ℕ → Finset ℕ)
    (hsubset : ∀ N, candidates N ⊆ Finset.Icc 1 N)
    (hprime : ∀ N p, p ∈ Finset.Icc 1 N → p.Prime → p ∈ candidates N) :
    (∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → 1 ≤ N →
        nativeAlpogeGz N ≤ C * (N : ℝ) ^ ((1 : ℝ) / 2 + η)) ↔
    (∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → 1 ≤ N →
        nativeSquareCandidateCapacity (candidates N) N -
            C * (N : ℝ) ^ ((1 : ℝ) / 2 + η) ≤
          nativeSquareCompositeRemoval (candidates N) N) := by
  constructor
  · intro h η hη
    obtain ⟨C, hC, N₀, hbound⟩ := h η hη
    refine ⟨C, hC, N₀, fun N hN₀ hN => ?_⟩
    exact (nativeAlpogeGz_le_iff_candidateRemoval (candidates N) N
      (C * (N : ℝ) ^ ((1 : ℝ) / 2 + η)) (hsubset N) (hprime N)).mp
        (hbound N hN₀ hN)
  · intro h η hη
    obtain ⟨C, hC, N₀, hbound⟩ := h η hη
    refine ⟨C, hC, N₀, fun N hN₀ hN => ?_⟩
    exact (nativeAlpogeGz_le_iff_candidateRemoval (candidates N) N
      (C * (N : ℝ) ^ ((1 : ℝ) / 2 + η)) (hsubset N) (hprime N)).mpr
        (hbound N hN₀ hN)

/-- The actual square-dependent prefix wheel is prime-complete whenever
its cutoff at radius `r` is at most `r`. Its previously proved containment
and prime-coverage theorems discharge both candidate hypotheses. -/
theorem nativeAlpogeGz_rpow_le_iff_squarePrefixRemoval
    (cutoff : ℕ → ℕ) (hcutoff : ∀ r, cutoff r ≤ r)
    (N : ℕ) (C η : ℝ) :
    nativeAlpogeGz N ≤ C * (N : ℝ) ^ ((1 : ℝ) / 2 + η) ↔
      nativeSquareCandidateCapacity (nativeSquarePrefixCandidates cutoff N) N -
          C * (N : ℝ) ^ ((1 : ℝ) / 2 + η) ≤
        nativeSquareCompositeRemoval (nativeSquarePrefixCandidates cutoff N) N := by
  exact nativeAlpogeGz_le_iff_candidateRemoval _ N
    (C * (N : ℝ) ^ ((1 : ℝ) / 2 + η))
    (nativeSquarePrefixCandidates_subset cutoff N)
    (nativeSquarePrefixCandidates_contains_prime cutoff hcutoff N)

/-- Uniform completed removal on the native square-prefix candidates is
equivalent to the original eventual natural-input source bound. -/
theorem nativeAlpogeGz_eventual_rpow_iff_squarePrefixRemoval
    (cutoff : ℕ → ℕ) (hcutoff : ∀ r, cutoff r ≤ r) :
    (∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → 1 ≤ N →
        nativeAlpogeGz N ≤ C * (N : ℝ) ^ ((1 : ℝ) / 2 + η)) ↔
    (∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → 1 ≤ N →
        nativeSquareCandidateCapacity (nativeSquarePrefixCandidates cutoff N) N -
            C * (N : ℝ) ^ ((1 : ℝ) / 2 + η) ≤
          nativeSquareCompositeRemoval (nativeSquarePrefixCandidates cutoff N) N) := by
  exact nativeAlpogeGz_eventual_rpow_iff_candidateRemoval
    (nativeSquarePrefixCandidates cutoff)
    (nativeSquarePrefixCandidates_subset cutoff)
    (nativeSquarePrefixCandidates_contains_prime cutoff hcutoff)

/-- A one-sided bound on the normalized complete history at the original
square endpoints supplies the existing square-clock window criterion.
The hypothesis is the still-open arithmetic estimate, not a supplied bound. -/
theorem riemannHypothesis_of_eventual_squareClock_NNSHistory
    (h : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∃ R₀ : ℕ,
      ∀ R : ℕ, 2 ≤ R → R₀ ≤ R →
        alpogeGzNNSHistory (R ^ 2 - 1) ≤
          C * ((R ^ 2 - 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2 + η)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_squareClock_Gz_windows (δ := 1) (by norm_num)
  intro η hη
  obtain ⟨C, _hC, R₀, hbound⟩ := h η hη
  refine ⟨C, fun A₀ => ?_⟩
  let A := max A₀ (max 2 R₀)
  refine ⟨A, le_max_left _ _, fun R hAR _hwindow => ?_⟩
  have hR : 2 ≤ R :=
    (le_max_left 2 R₀).trans ((le_max_right A₀ (max 2 R₀)).trans hAR)
  have hR₀ : R₀ ≤ R :=
    (le_max_right 2 R₀).trans ((le_max_right A₀ (max 2 R₀)).trans hAR)
  have hN : 1 ≤ R ^ 2 - 1 := by
    have hsq : 4 ≤ R ^ 2 := by nlinarith
    omega
  exact (nativeAlpogeGz_rpow_le_iff_NNSHistory (R ^ 2 - 1) hN C η).mpr
    (hbound R hR hR₀)

/-- The complete removal estimate at the original square endpoints is a
conditional RH input. The cutoff supplies actual prime coverage; the
critical quantitative removal inequality remains the explicit hypothesis. -/
theorem riemannHypothesis_of_eventual_squareClock_squarePrefixRemoval
    (cutoff : ℕ → ℕ) (hcutoff : ∀ r, cutoff r ≤ r)
    (h : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∃ R₀ : ℕ,
      ∀ R : ℕ, 2 ≤ R → R₀ ≤ R →
        nativeSquareCandidateCapacity
            (nativeSquarePrefixCandidates cutoff (R ^ 2 - 1)) (R ^ 2 - 1) -
            C * (R : ℝ) ^ (1 + η) ≤
          nativeSquareCompositeRemoval
            (nativeSquarePrefixCandidates cutoff (R ^ 2 - 1)) (R ^ 2 - 1)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_eventual_squareClock_Gz_rpow
  intro η hη
  obtain ⟨C, hC, R₀, hbound⟩ := h η hη
  refine ⟨C, hC, R₀, fun R hR hR₀ => ?_⟩
  exact (nativeAlpogeGz_le_iff_candidateRemoval _ (R ^ 2 - 1)
    (C * (R : ℝ) ^ (1 + η))
    (nativeSquarePrefixCandidates_subset cutoff (R ^ 2 - 1))
    (nativeSquarePrefixCandidates_contains_prime cutoff hcutoff (R ^ 2 - 1))).mpr
      (hbound R hR hR₀)

/-- The complete all-real input returns RH and both native arithmetic
consequences. The single constant and threshold work simultaneously for the
centered history and every prime-complete candidate set at every large
endpoint. Both estimates follow directly from the source bound, without
using RH as an intermediate premise. The source bound itself is assumed. -/
theorem nativeAlpogeConsequences_of_eventualRealBound
    (h : AlpogeNativeBoundHandoff.EventualRealBound) :
    RiemannHypothesis ∧
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → 1 ≤ N →
        (alpogeGzNNSHistory N ≤ C * (N : ℝ) ^ (-(1 : ℝ) / 2 + η)) ∧
        ∀ candidates : Finset ℕ,
          candidates ⊆ Finset.Icc 1 N →
          (∀ p ∈ Finset.Icc 1 N, p.Prime → p ∈ candidates) →
          nativeSquareCandidateCapacity candidates N -
              C * (N : ℝ) ^ ((1 : ℝ) / 2 + η) ≤
            nativeSquareCompositeRemoval candidates N := by
  refine ⟨AlpogeNativeBoundHandoff.riemannHypothesis_of_eventualRealBound h, ?_⟩
  intro η hη
  obtain ⟨C, hC, N₀, hbound⟩ :=
    AlpogeNativeBoundHandoff.eventualNativeBound_of_eventualRealBound h η hη
  refine ⟨C, hC, N₀, fun N hN₀ hN => ?_⟩
  have hsource := hbound N hN₀ hN
  refine ⟨(nativeAlpogeGz_rpow_le_iff_NNSHistory N hN C η).mp hsource, ?_⟩
  intro candidates hsubset hprime
  exact (nativeAlpogeGz_le_iff_candidateRemoval candidates N
    (C * (N : ℝ) ^ ((1 : ℝ) / 2 + η)) hsubset hprime).mp hsource

end RHLean.Analysis

end

import «research.VF_919_EXACT_INTEGER_BY_INTEGER_317_1027_20261019»
import RHLean.Analysis.DeterministicTGreenKuboComparison

/-!
# Exact finite site ledger is the ORIGINAL native signed Mertens pair carrier

The tuple M,K,C from the integer-by-integer proof is IDENTICAL to the
repository's established realMertensLength, realMertensDiagonal and
realMertensPositiveLagPairSum, after accounting for the n=0 zero
site. This is a source identity for ALL n, not a second surrogate model.
All exact numerical 317/1027 values thus belong to the original signed
Green-Kubo covariance, not merely the temporary computational ledger.
-/

noncomputable section
namespace RHLean.Analysis

/-- The one-integer-at-a-time recursion agrees at every endpoint with
    the ORIGINAL native real Mertens mass, diagonal and signed off-diagonal. -/
theorem vf919ExactIntegerLedger_eq_nativeMertens (n : ℕ) :
    (((vf919ExactSiteLedger n).1 : ℤ) : ℝ) =
        realMertensLength (n + 1) ∧
    (((vf919ExactSiteLedger n).2.1 : ℤ) : ℝ) =
        realMertensDiagonal (n + 1) ∧
    (((vf919ExactSiteLedger n).2.2 : ℤ) : ℝ) =
        realMertensPositiveLagPairSum (n + 1) := by
  induction n with
  | zero =>
      simp [vf919ExactSiteLedger, realMertensLength,
        realMertensDiagonal, realMertensPositiveLagPairSum,
        realMoebiusStep, ArithmeticFunction.moebius]
  | succ n ih =>
      obtain ⟨hM, hK, hC⟩ := ih
      have hmu :
          ((vf919ExactSiteMu (n + 1) : ℤ) : ℝ) =
            realMoebiusStep (n + 1) := rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [realMertensLength_succ]
        change (((vf919ExactSiteLedger n).1 +
            vf919ExactSiteMu (n + 1) : ℤ) : ℝ) =
          realMertensLength (n + 1) + realMoebiusStep (n + 1)
        push_cast
        rw [hM, hmu]
      · rw [realMertensDiagonal_succ]
        change (((vf919ExactSiteLedger n).2.1 +
            vf919ExactSiteMu (n + 1) ^ 2 : ℤ) : ℝ) =
          realMertensDiagonal (n + 1) + realMoebiusStep (n + 1) ^ 2
        push_cast
        rw [hK, hmu]
      · rw [realMertensPositiveLagPairSum_succ]
        change (((vf919ExactSiteLedger n).2.2 +
            (vf919ExactSiteLedger n).1 *
              vf919ExactSiteMu (n + 1) : ℤ) : ℝ) =
          realMertensPositiveLagPairSum (n + 1) +
            realMoebiusStep (n + 1) * realMertensLength (n + 1)
        push_cast
        rw [hC, hM, hmu]
        ring

/-- Exact native 317: every physical site and every signed pair accounted. -/
theorem vf919ExactNativeMertens_317 :
    realMertensLength 318 = -4 ∧
      realMertensDiagonal 318 = 194 ∧
        realMertensPositiveLagPairSum 318 = -89 := by
  obtain ⟨hm, hk, hc⟩ := vf919ExactIntegerLedger_eq_nativeMertens 317
  refine ⟨?_, ?_, ?_⟩
  · have hh := hm.symm
    rw [vf919ExactSiteLedger_317] at hh
    simpa only [Prod.fst, Prod.snd, Int.cast_neg, Int.cast_ofNat] using hh
  · have hh := hk.symm
    rw [vf919ExactSiteLedger_317] at hh
    simpa only [Prod.fst, Prod.snd, Int.cast_neg, Int.cast_ofNat] using hh
  · have hh := hc.symm
    rw [vf919ExactSiteLedger_317] at hh
    simpa only [Prod.fst, Prod.snd, Int.cast_neg, Int.cast_ofNat] using hh

/-- Exact native 1027: all physical sign reversals, not an ideal subrow. -/
theorem vf919ExactNativeMertens_1027 :
    realMertensLength 1028 = -3 ∧
      realMertensDiagonal 1028 = 625 ∧
        realMertensPositiveLagPairSum 1028 = -308 := by
  obtain ⟨hm, hk, hc⟩ := vf919ExactIntegerLedger_eq_nativeMertens 1027
  refine ⟨?_, ?_, ?_⟩
  · have hh := hm.symm
    rw [vf919ExactSiteLedger_1027] at hh
    simpa only [Prod.fst, Prod.snd, Int.cast_neg, Int.cast_ofNat] using hh
  · have hh := hk.symm
    rw [vf919ExactSiteLedger_1027] at hh
    simpa only [Prod.fst, Prod.snd, Int.cast_neg, Int.cast_ofNat] using hh
  · have hh := hc.symm
    rw [vf919ExactSiteLedger_1027] at hh
    simpa only [Prod.fst, Prod.snd, Int.cast_neg, Int.cast_ofNat] using hh

/-- The same result in the repository's original COMPLEX Mertens function. -/
theorem vf919ExactNativeMertensSummatory_317 :
    mertensSummatory 317 = (-4 : ℂ) := by
  have h := realMertensLength_cast_eq_mertensSummatory 317
  rw [vf919ExactNativeMertens_317.1] at h
  simpa only [Complex.ofReal_neg, Complex.ofReal_ofNat] using h.symm

theorem vf919ExactNativeMertensSummatory_1027 :
    mertensSummatory 1027 = (-3 : ℂ) := by
  have h := realMertensLength_cast_eq_mertensSummatory 1027
  rw [vf919ExactNativeMertens_1027.1] at h
  simpa only [Complex.ofReal_neg, Complex.ofReal_ofNat] using h.symm

#print axioms vf919ExactIntegerLedger_eq_nativeMertens
#print axioms vf919ExactNativeMertens_317
#print axioms vf919ExactNativeMertens_1027
#print axioms vf919ExactNativeMertensSummatory_317
#print axioms vf919ExactNativeMertensSummatory_1027

end RHLean.Analysis

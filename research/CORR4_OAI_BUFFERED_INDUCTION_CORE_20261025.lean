import Mathlib
import «research.CORR4_OAI_POWER_GRAM_EQUIVALENCE_20261025»

/-!
# Buffered all-integer CORR-4 induction: original sharp daughter cutoff

This theorem compiles the shell/endpoint induction, CONDITIONAL on a
prefix-to-daughter energy estimate and a trivial finite base. The first
condition is deterministic but must be proved for actual q² daughters in
a subsequent module before claiming an unconditional biconditional.

No independence, covariance, RH, or analytic exponent gain is assumed
or concluded. The source-level Corr4PowerPhysicalRemainder hypothesis
remains visible in the theorem statement.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof
open RHLean.Analysis RHLean.Arithmetic
attribute [local instance] Classical.propDecidable

/-- Exact buffered all-integer induction, without nearest-square rounding.
    The assumptions hD and hbase are stated explicitly; they are not hidden
    analytic axioms. Proving hD from source-level finite q² division is the
    remaining deterministic bridge for the full Gram <-> Mertens exponent. -/
theorem corr4_buffered_all_integer_of_prefix_daughter_frame
    (A β H : ℝ)
    (hβ : (1 / 2 : ℝ) ≤ β)
    (hH : 1000 ≤ H)
    (hBuffer :
      ((101 / 100 : ℝ) * (886 / 225) * (211 / 900)) * H ^ 2 +
        (101 / 75 : ℝ) * A + 101 ≤ (49 / 50 : ℝ) ^ 2 * H ^ 2)
    (hB : Corr4PowerPhysicalRemainder A β)
    (hBase :
      ∀ n : ℕ, 1 ≤ n → n ≤ squareRootEndpoint 56 →
        ‖mertensSummatory n‖ ≤ H * Real.rpow (n : ℝ) β)
    (hDaughter :
      ∀ R : ℕ, 56 ≤ R →
        (∀ n : ℕ, 1 ≤ n → n ≤ squareRootEndpoint R →
          ‖mertensSummatory n‖ ≤ H * Real.rpow (n : ℝ) β) →
        canonicalRoughLowQ2DaughterEnergy R ≤
          (211 / 900 : ℝ) * H ^ 2 *
            Real.rpow (R : ℝ) (4 * β)) :
    ∀ n : ℕ, 1 ≤ n →
      ‖mertensSummatory n‖ ≤ H * Real.rpow (n : ℝ) β := by
  have hH0 : 0 ≤ H := by linarith
  have hβ0 : 0 ≤ β := by linarith
  have hPrefix : ∀ R : ℕ, 56 ≤ R →
      ∀ n : ℕ, 1 ≤ n → n ≤ squareRootEndpoint R →
        ‖mertensSummatory n‖ ≤ H * Real.rpow (n : ℝ) β := by
    intro R hR
    induction R, hR using Nat.le_induction with
    | base =>
      exact hBase
    | succ R hR ih =>
      intro n hn hnR
      by_cases hOld : n ≤ squareRootEndpoint R
      · exact ih n hn hOld
      · have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (show 1 ≤ R by omega)
        have hRpos : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg _
        have hRP : 0 ≤ Real.rpow (R : ℝ) (4 * β) :=
          Real.rpow_nonneg hRpos _
        have hR2 : (R : ℝ) ^ 2 ≤ Real.rpow (R : ℝ) (4 * β) := by
          calc
            (R : ℝ) ^ 2 = Real.rpow (R : ℝ) (2 : ℝ) :=
              (Real.rpow_natCast (R : ℝ) 2).symm
            _ ≤ Real.rpow (R : ℝ) (4 * β) :=
              Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
        have hEnergy := hDaughter R hR ih
        have hRec :=
          corr4_mertens_endpoint_unrounded_power_recurrence hB R hR
        have hRoot :
            ‖mertensSummatory (R - 1)‖ ≤ (R : ℝ) := by
          calc
            ‖mertensSummatory (R - 1)‖ ≤ ((R - 1 : ℕ) : ℝ) :=
              RHLean.Analysis.MertensExponent.mertens_norm_le (R - 1)
            _ ≤ (R : ℝ) := by
              exact_mod_cast (Nat.sub_le R 1)
        have hRootSq :
            ‖mertensSummatory (R - 1)‖ ^ 2 ≤ (R : ℝ) ^ 2 := by
          nlinarith [norm_nonneg (mertensSummatory (R - 1))]
        have hRPowSq :
            (Real.rpow (R : ℝ) (2 * β)) ^ 2 =
              Real.rpow (R : ℝ) (4 * β) := by
          calc
            (Real.rpow (R : ℝ) (2 * β)) ^ 2 =
                Real.rpow (Real.rpow (R : ℝ) (2 * β)) (2 : ℝ) :=
                  (Real.rpow_natCast _ 2).symm
            _ = Real.rpow (R : ℝ) ((2 * β) * 2) :=
              (Real.rpow_mul hRpos (2 * β) 2).symm
            _ = Real.rpow (R : ℝ) (4 * β) := by congr 1; ring
        have hEnergyScaled :=
          mul_le_mul_of_nonneg_left hEnergy
            (show (0 : ℝ) ≤ (101 / 100) * (886 / 225) by norm_num)
        have hRootScaled :
            101 * ‖mertensSummatory (R - 1)‖ ^ 2 ≤
              101 * Real.rpow (R : ℝ) (4 * β) := by
          nlinarith [hRootSq, hR2]
        have hEndpointSq :
            ‖mertensSummatory (squareRootEndpoint R)‖ ^ 2 ≤
              ((101 / 100 : ℝ) * (886 / 225) * (211 / 900) *
                H ^ 2 + (101 / 75) * A + 101) *
                  Real.rpow (R : ℝ) (4 * β) := by
          nlinarith [hRec, hEnergyScaled, hRootScaled]
        have hBufScale :=
          mul_le_mul_of_nonneg_right hBuffer hRP
        have hEndSq :
            ‖mertensSummatory (squareRootEndpoint R)‖ ^ 2 ≤
              (49 / 50 : ℝ) ^ 2 * H ^ 2 *
                Real.rpow (R : ℝ) (4 * β) :=
          hEndpointSq.trans (by nlinarith [hBufScale])
        have hEnd :
            ‖mertensSummatory (squareRootEndpoint R)‖ ≤
              (49 / 50 : ℝ) * H *
                Real.rpow (R : ℝ) (2 * β) := by
          have hPowNonneg :
              0 ≤ Real.rpow (R : ℝ) (2 * β) :=
            Real.rpow_nonneg hRpos _
          have hRightNonneg :
              0 ≤ (49 / 50 : ℝ) * H *
                Real.rpow (R : ℝ) (2 * β) := by positivity
          have hEq :
              ((49 / 50 : ℝ) * H *
                  Real.rpow (R : ℝ) (2 * β)) ^ 2 =
                (49 / 50 : ℝ) ^ 2 * H ^ 2 *
                  Real.rpow (R : ℝ) (4 * β) := by
            rw [mul_pow, mul_pow, hRPowSq]
          rw [← hEq] at hEndSq
          nlinarith [norm_nonneg (mertensSummatory (squareRootEndpoint R))]
        have hOldLt : squareRootEndpoint R < n := Nat.lt_of_not_ge hOld
        have hOldLE : squareRootEndpoint R ≤ n := Nat.le_of_lt hOldLt
        have hRootIdentity : squareRootEndpoint R + 1 = R ^ 2 := by
          unfold squareRootEndpoint
          have hpos : 0 < R ^ 2 := by positivity
          omega
        have hNextIdentity : squareRootEndpoint (R + 1) =
            R ^ 2 + 2 * R := by
          unfold squareRootEndpoint
          have he : (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by ring
          rw [he]
          omega
        have hGapNat :
            n - squareRootEndpoint R ≤ 2 * R + 1 := by
          rw [hNextIdentity] at hnR
          omega
        have hGap :
            ((n - squareRootEndpoint R : ℕ) : ℝ) ≤
              2 * (R : ℝ) + 1 := by
          exact_mod_cast hGapNat
        have hVar :=
          norm_mertensSummatory_sub_le (squareRootEndpoint R) n hOldLE
        have hRPower :
            (R : ℝ) ≤ Real.rpow (R : ℝ) (2 * β) := by
          have hh :=
            Real.rpow_le_rpow_of_exponent_le hR1
              (show (1 : ℝ) ≤ 2 * β by linarith)
          simpa using hh
        have hShellBudget :
            2 * (R : ℝ) + 1 ≤
              (H / 50) * Real.rpow (R : ℝ) (2 * β) := by
          have h3 :
              2 * (R : ℝ) + 1 ≤ 3 * (R : ℝ) := by linarith
          have hpow := mul_le_mul_of_nonneg_left hRPower
            (show (0 : ℝ) ≤ 3 by norm_num)
          have h3H : (3 : ℝ) ≤ H / 50 := by linarith
          have hcoeff := mul_le_mul_of_nonneg_right h3H
            (Real.rpow_nonneg hRpos (2 * β))
          calc
            2 * (R : ℝ) + 1 ≤ 3 * (R : ℝ) := h3
            _ ≤ 3 * Real.rpow (R : ℝ) (2 * β) := hpow
            _ ≤ (H / 50) * Real.rpow (R : ℝ) (2 * β) := hcoeff
        have hnSquare : R ^ 2 ≤ n := by omega
        have hnSquareCast :
            (R : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hnSquare
        have hRootPower :
            Real.rpow (R : ℝ) (2 * β) ≤
              Real.rpow (n : ℝ) β := by
          have he :
              Real.rpow ((R : ℝ) ^ 2) β =
                Real.rpow (R : ℝ) (2 * β) := by
            calc
              Real.rpow ((R : ℝ) ^ 2) β =
                  Real.rpow (Real.rpow (R : ℝ) (2 : ℝ)) β := by
                    exact congrArg (fun t : ℝ => Real.rpow t β)
                      ((Real.rpow_natCast (R : ℝ) 2).symm)
              _ = Real.rpow (R : ℝ) (2 * β) :=
                (Real.rpow_mul hRpos 2 β).symm
          rw [← he]
          exact Real.rpow_le_rpow (sq_nonneg _) hnSquareCast hβ0
        have hTriangle :
            ‖mertensSummatory n‖ ≤
              ‖mertensSummatory (squareRootEndpoint R)‖ +
                ((n - squareRootEndpoint R : ℕ) : ℝ) := by
          calc
            ‖mertensSummatory n‖ =
                ‖(mertensSummatory n -
                    mertensSummatory (squareRootEndpoint R)) +
                    mertensSummatory (squareRootEndpoint R)‖ := by
                  rw [sub_add_cancel]
            _ ≤ ‖mertensSummatory n -
                  mertensSummatory (squareRootEndpoint R)‖ +
                    ‖mertensSummatory (squareRootEndpoint R)‖ :=
              norm_add_le _ _
            _ ≤ ((n - squareRootEndpoint R : ℕ) : ℝ) +
                  ‖mertensSummatory (squareRootEndpoint R)‖ :=
              add_le_add hVar le_rfl
            _ = _ := by ring
        calc
          ‖mertensSummatory n‖ ≤
              ‖mertensSummatory (squareRootEndpoint R)‖ +
                ((n - squareRootEndpoint R : ℕ) : ℝ) := hTriangle
          _ ≤ (49 / 50 : ℝ) * H *
                Real.rpow (R : ℝ) (2 * β) +
                (2 * (R : ℝ) + 1) :=
            add_le_add hEnd hGap
          _ ≤ H * Real.rpow (R : ℝ) (2 * β) := by
            nlinarith [hShellBudget]
          _ ≤ H * Real.rpow (n : ℝ) β :=
            mul_le_mul_of_nonneg_left hRootPower hH0
  intro n hn
  have hRoot : 56 ≤ n + 56 := by omega
  have hSquare : n + 1 ≤ (n + 56) ^ 2 := by
    nlinarith
  have hTop : n ≤ squareRootEndpoint (n + 56) := by
    unfold squareRootEndpoint
    omega
  exact hPrefix (n + 56) hRoot n hn hTop

#print axioms corr4_buffered_all_integer_of_prefix_daughter_frame

end RHLean.Proof

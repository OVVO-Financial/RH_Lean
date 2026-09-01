import Mathlib
import RHLean.Proof.SquareRootCanonicalDowncrossFinalSeam
import RHLean.Proof.LowWheelCanonicalRepeatedMovableCancellation
import RHLean.Proof.LowWheelCanonicalSignedOwnershipInterval

/-!
# The oriented seam at RH scale

After `LateParentCancellation.lateParentLedger_eq_zero`, the canonical downcross
ledger *is* the oriented ledger:

`D_R = O_R`.

`SquareRootCanonicalOrientedLinearBound` asks for `‖O_R‖ ≤ C * R`.  That is
strictly stronger than the Riemann hypothesis needs, and the repository already
compiles the reason: `norm_squarePrefixMertens_le_of_canonicalDowncrossLinear`
turns it into `|M(R^2-1)| ≤ (C+1) * R`, and since consecutive square endpoints
differ by `2R` that extends to `M(x) = O(sqrt x)` for all `x` — the strong
Mertens bound, which is open and widely believed false.

The energy bridge only ever consumes `SquarePrefixEnergyBoundedStatement`,

`∀ ε > 0, ∃ C, ∀ n, ‖squarePrefixMertens n‖^2 ≤ C * (n+1)^(2+ε)`,

i.e. `M(x) ≪ x^(1/2+ε)`, which is equivalent to RH.  So the correct seam is the
`1 + ε` bound below, and the base `(n+1)` of the energy statement is exactly the
root `R`, so no off-square interpolation is duplicated here: that loss is paid
once, inside `mertensEnergyBounded_of_squarePrefixEnergyBounded`.

`SquareRootCanonicalOrientedLinearBound` remains a valid *sufficient* criterion —
`orientedEpsilonBound_of_orientedLinearBound` below records that it implies this
one — but it is not the canonical final target.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis

namespace OrientedEpsilonBound

/-- **The final quantitative seam, at RH scale.**  For every `ε > 0` the
canonical oriented first-crossing ledger is `O(R^(1+ε))`. -/
def SquareRootCanonicalOrientedEpsilonBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, 3 ≤ R →
        ‖LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossOrientedLedger R‖ ≤
          C * Real.rpow (R : ℝ) (1 + ε)

private theorem one_le_cast_succ (n : ℕ) : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
  have h : (1 : ℕ) ≤ n + 1 := by omega
  exact_mod_cast h

private theorem cast_succ_pos (n : ℕ) : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
  have h : (0 : ℕ) < n + 1 := by omega
  exact_mod_cast h

/-- `x ≤ x ^ (1 + δ)` for a base at least one. -/
private theorem cast_le_rpow_one_add
    {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) ≤ Real.rpow ((n + 1 : ℕ) : ℝ) (1 + δ) := by
  have h := Real.rpow_le_rpow_of_exponent_le (one_le_cast_succ n)
    (by linarith : (1 : ℝ) ≤ 1 + δ)
  simpa using h

/-- `1 ≤ x ^ (2 + ε)` for a base at least one. -/
private theorem one_le_rpow_two_add
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    (1 : ℝ) ≤ Real.rpow ((n + 1 : ℕ) : ℝ) (2 + ε) := by
  have h := Real.rpow_le_rpow_of_exponent_le (one_le_cast_succ n)
    (by linarith : (0 : ℝ) ≤ 2 + ε)
  simpa using h

/-- **The oriented `1 + ε` seam gives the square-prefix energy criterion.**

Instantiating the oriented hypothesis at `ε / 2` is what makes the exponents
line up: the square of an `R^(1+ε/2)` bound is exactly `R^(2+ε)`, and the base
of the energy statement is literally `R = n + 1`. -/
theorem squarePrefixEnergyBounded_of_canonicalOrientedEpsilon
    (horiented : SquareRootCanonicalOrientedEpsilonBound) :
    SquarePrefixEnergyBoundedStatement := by
  intro ε hε
  obtain ⟨C, hC, hO⟩ := horiented (ε / 2) (by linarith)
  refine ⟨(1 + C) ^ 2 + 9, by positivity, ?_⟩
  intro n
  have hbaseNonneg : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hrpowNonneg : (0 : ℝ) ≤ Real.rpow ((n + 1 : ℕ) : ℝ) (2 + ε) :=
    Real.rpow_nonneg hbaseNonneg _
  by_cases hn : 2 ≤ n
  · -- Genuine range: the oriented seam applies at `R = n + 1 ≥ 3`.
    have hR : 3 ≤ n + 1 := by omega
    have hsplit := squarePrefixMertens_eq_mertens_sub_canonicalDowncross (n + 1) hR
    have hn1 : n + 1 - 1 = n := by omega
    rw [hn1, LateParentCancellation.downcrossLedger_eq_orientedLedger] at hsplit
    have hM : ‖mertensSummatory (n + 1)‖ ≤ ((n + 1 : ℕ) : ℝ) := by
      simpa using norm_mertensSummatory_sub_le 0 (n + 1) (Nat.zero_le _)
    have hRle := cast_le_rpow_one_add (δ := ε / 2) (by linarith) n
    have hA :
        ‖squarePrefixMertens n‖ ≤
          (1 + C) * Real.rpow ((n + 1 : ℕ) : ℝ) (1 + ε / 2) := by
      rw [hsplit]
      calc
        ‖mertensSummatory (n + 1) -
            LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossOrientedLedger
              (n + 1)‖ ≤
            ‖mertensSummatory (n + 1)‖ +
              ‖LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossOrientedLedger
                (n + 1)‖ := norm_sub_le _ _
        _ ≤ Real.rpow ((n + 1 : ℕ) : ℝ) (1 + ε / 2) +
              C * Real.rpow ((n + 1 : ℕ) : ℝ) (1 + ε / 2) :=
            add_le_add (hM.trans hRle) (hO (n + 1) hR)
        _ = (1 + C) * Real.rpow ((n + 1 : ℕ) : ℝ) (1 + ε / 2) := by ring
    have hprod :
        Real.rpow ((n + 1 : ℕ) : ℝ) (2 + ε) =
          Real.rpow ((n + 1 : ℕ) : ℝ) (1 + ε / 2) *
            Real.rpow ((n + 1 : ℕ) : ℝ) (1 + ε / 2) := by
      -- Mathlib states the `rpow` laws with `^` notation, which is defeq to
      -- `Real.rpow` but not syntactically equal, so rewrite the exponent inside
      -- the instantiated lemma and close by defeq rather than rewriting the goal.
      have h := Real.rpow_add (cast_succ_pos n) (1 + ε / 2) (1 + ε / 2)
      have hexp : (1 + ε / 2) + (1 + ε / 2) = 2 + ε := by ring
      rw [hexp] at h
      exact h
    have hAnn : (0 : ℝ) ≤ ‖squarePrefixMertens n‖ := norm_nonneg _
    have hsq :
        ‖squarePrefixMertens n‖ ^ 2 ≤
          ((1 + C) * Real.rpow ((n + 1 : ℕ) : ℝ) (1 + ε / 2)) ^ 2 := by
      nlinarith [hAnn, hA]
    calc
      ‖squarePrefixMertens n‖ ^ 2 ≤
          ((1 + C) * Real.rpow ((n + 1 : ℕ) : ℝ) (1 + ε / 2)) ^ 2 := hsq
      _ = (1 + C) ^ 2 *
            (Real.rpow ((n + 1 : ℕ) : ℝ) (1 + ε / 2) *
              Real.rpow ((n + 1 : ℕ) : ℝ) (1 + ε / 2)) := by ring
      _ = (1 + C) ^ 2 * Real.rpow ((n + 1 : ℕ) : ℝ) (2 + ε) := by rw [hprod]
      _ ≤ ((1 + C) ^ 2 + 9) * Real.rpow ((n + 1 : ℕ) : ℝ) (2 + ε) := by
          nlinarith [hrpowNonneg]
  · -- `n ≤ 1`: the trivial interval bound suffices.
    have hnle : n ≤ 1 := by omega
    have hEnd : squarePrefixEndpoint n ≤ 3 := by
      interval_cases n <;> simp [squarePrefixEndpoint]
    have hb : ‖squarePrefixMertens n‖ ≤ ((squarePrefixEndpoint n : ℕ) : ℝ) := by
      simpa [squarePrefixMertens] using
        norm_mertensSummatory_sub_le 0 (squarePrefixEndpoint n) (Nat.zero_le _)
    have hb3 : ‖squarePrefixMertens n‖ ≤ 3 := by
      have hcast : ((squarePrefixEndpoint n : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hEnd
      exact hb.trans hcast
    have hAnn : (0 : ℝ) ≤ ‖squarePrefixMertens n‖ := norm_nonneg _
    have hsq : ‖squarePrefixMertens n‖ ^ 2 ≤ 9 := by nlinarith [hAnn, hb3]
    have hone := one_le_rpow_two_add hε n
    nlinarith [hsq, hone, sq_nonneg (1 + C)]

/-- **RH from the oriented `1 + ε` seam**, through the already-compiled bridge.
The off-square interpolation is paid exactly once, inside
`mertensEnergyBounded_of_squarePrefixEnergyBounded`. -/
theorem riemannHypothesis_of_canonicalOrientedEpsilon
    (horiented : SquareRootCanonicalOrientedEpsilonBound) :
    RiemannHypothesis :=
  riemannHypothesis_of_mertensEnergy
    (mertensEnergyBounded_of_squarePrefixEnergyBounded
      (squarePrefixEnergyBounded_of_canonicalOrientedEpsilon horiented))

/-- The old linear seam is a *stronger* sufficient criterion, not the canonical
target: it implies this one for every `ε`. -/
theorem orientedEpsilonBound_of_orientedLinearBound
    (hlinear : LateParentCancellation.SquareRootCanonicalOrientedLinearBound) :
    SquareRootCanonicalOrientedEpsilonBound := by
  obtain ⟨C, hC, hO⟩ := hlinear
  intro ε hε
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, R = n + 1 := ⟨R - 1, by omega⟩
  exact (hO (n + 1) hR).trans
    (mul_le_mul_of_nonneg_left (cast_le_rpow_one_add (δ := ε) (le_of_lt hε) n) hC)

end OrientedEpsilonBound

end RHLean.Proof
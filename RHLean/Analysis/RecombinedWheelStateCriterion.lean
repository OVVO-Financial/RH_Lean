import Mathlib
import RHLean.Analysis.OutsidePrimeSignLayerPrimeWheelBridge

/-!
# Terminal recombined wheel-state criterion

The outside-prime square-deletion and ordinary sign layers have already been
recombined into the existing square-root prime-wheel field.  This module freezes
that fully recombined signed field at the complete square endpoint and makes it
the terminal analytic object.

Nothing in this file decomposes that state.  The only quantitative premise is a
single energy bound on the whole recombined state.  The proof then passes through
the repository's existing square-prefix Mertens criterion and its established
Mertens-to-RH continuation route.
-/

noncomputable section

namespace RHLean.Analysis

/-- The final analytic object at square scale `R`: the complete recovered
prime-wheel field at the endpoint `R^2 - 1`, with every signed correction kept
inside the state. -/
def recombinedWheelState (R : ℕ) : ℂ :=
  ((sqrtWheelRecoveredPrefix (R ^ 2 - 1) : ℤ) : ℂ)

/-- The frozen recombined state is exactly the analytic Mertens summatory
function at the same complete-square endpoint.  This is an exact identification,
not an estimate and not a decomposition. -/
theorem recombinedWheelState_eq_mertensSummatory (R : ℕ) :
    recombinedWheelState R = mertensSummatory (R ^ 2 - 1) := by
  unfold recombinedWheelState
  exact sqrtWheelRecoveredPrefix_cast_eq_mertensSummatory (R ^ 2 - 1)

/-- At positive square scale, the frozen state is exactly the repository's
square-prefix Mertens value with index `R - 1`. -/
theorem recombinedWheelState_eq_squarePrefixMertens
    {R : ℕ} (hR : 1 ≤ R) :
    recombinedWheelState R = squarePrefixMertens (R - 1) := by
  rw [recombinedWheelState_eq_mertensSummatory]
  unfold squarePrefixMertens squarePrefixEndpoint
  have hpred : R - 1 + 1 = R := by omega
  rw [hpred]

/-- **Terminal analytic premise.**  All cancellation remains inside
`recombinedWheelState`; no channel, prime, deletion, endpoint, or smooth term is
bounded separately. -/
def RecombinedWheelStateEnergyBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ R : ℕ, 2 ≤ R →
        ‖recombinedWheelState R‖ ^ 2 ≤
          C * Real.rpow ((R : ℝ) ^ 2) (1 + ε)

private theorem rpow_square_one_add_half
    (x ε : ℝ) (hx : 0 ≤ x) :
    Real.rpow (x ^ 2) (1 + ε / 2) =
      Real.rpow x (2 + ε) := by
  have htwo : Real.rpow x (2 : ℝ) = x ^ (2 : ℕ) :=
    Real.rpow_natCast x 2
  calc
    Real.rpow (x ^ 2) (1 + ε / 2) =
        Real.rpow (Real.rpow x (2 : ℝ)) (1 + ε / 2) :=
      congrArg (fun t : ℝ => Real.rpow t (1 + ε / 2)) htwo.symm
    _ = Real.rpow x ((2 : ℝ) * (1 + ε / 2)) :=
      (Real.rpow_mul hx (2 : ℝ) (1 + ε / 2)).symm
    _ = Real.rpow x (2 + ε) := by ring_nf

/-- The single recombined-state energy bound gives the repository's RH-scale
square-prefix Mertens energy bound.  The only exponent adjustment is the
harmless reparameterization `ε ↦ ε / 2`:
`(R^2)^(1+ε/2) = R^(2+ε)`. -/
theorem squarePrefixEnergyBounded_of_recombinedWheelStateEnergy
    (h : RecombinedWheelStateEnergyBound) :
    SquarePrefixEnergyBoundedStatement := by
  intro ε hε
  rcases h (ε / 2) (by linarith) with ⟨C, hC, hbound⟩
  refine ⟨C, le_of_lt hC, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simpa [squarePrefixMertens, squarePrefixEndpoint] using (le_of_lt hC)
  · have hR : 2 ≤ n + 1 := by omega
    have hs := hbound (n + 1) hR
    have hstate :
        recombinedWheelState (n + 1) = squarePrefixMertens n := by
      simpa using
        (recombinedWheelState_eq_squarePrefixMertens
          (R := n + 1) (by omega : 1 ≤ n + 1))
    rw [hstate] at hs
    rw [rpow_square_one_add_half ((n + 1 : ℕ) : ℝ) ε (by positivity)] at hs
    exact hs

/-- The already-proved square-prefix sampling bridge and Mertens continuation
route send an RH-scale square-prefix energy bound to the Riemann hypothesis. -/
theorem riemannHypothesis_of_squarePrefixEnergyBound
    (h : SquarePrefixEnergyBoundedStatement) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_mertensEnergy
  exact mertensEnergyBounded_of_squarePrefixEnergyBounded h

/-- **Terminal chain.**  A bound on the one frozen recombined wheel state implies
the RH-scale square-prefix Mertens bound and therefore the Riemann hypothesis. -/
theorem riemannHypothesis_of_recombinedWheelStateEnergy
    (h : RecombinedWheelStateEnergyBound) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_squarePrefixEnergyBound
    (squarePrefixEnergyBounded_of_recombinedWheelStateEnergy h)

end RHLean.Analysis

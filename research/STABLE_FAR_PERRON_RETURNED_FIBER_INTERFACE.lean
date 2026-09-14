import Mathlib
import «research.STABLE_FAR_RETURNED_FIBER_PRODUCTION»
import «research.STABLE_FAR_LOG_FREQUENCY_DIAGONALIZATION»

/-!
# Perron/log-frequency interface for the centered stable-far returned fibre

This module is deliberately pre-energy.  It formalizes the exact interface
suggested by the finite factorization diagnostic:

* the centered physical returned-fibre multiplicity field admits finite Fubini
  against an arbitrary complex test weight;
* specializing that weight to the existing logarithmic phase retains every
  state-resolved Perron frequency before any norm is taken;
* on the critical log line, q^2 descent is a scalar multiplier: an exponential
  half-density factor times the already-compiled q^2 phase rotation.

No zero of zeta is mentioned, no simplicity or RH hypothesis is used, and no
LOW-4 estimate is asserted here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-! ## Arbitrary-weight finite Fubini on the returned fibre -/

/-- Signed descended baseline tested against an arbitrary complex observable on
its retained cofactor coordinate. -/
def stableFarReturnedWeightedDescendedMass
    (w : ℕ → ℂ) (R r p : ℕ) : ℂ :=
  ∑ e ∈ stableFarReturnedDescendedCofactors R r p,
    canonicalMoebiusWeight e * w e

/-- Signed crossing column with the same test observable.  The old owner `q`
remains an occurrence coordinate until the finite Fubini theorem below. -/
def stableFarReturnedWeightedCrossingColumn
    (w : ℕ → ℂ) (R r p : ℕ) : ℂ :=
  ∑ q ∈ stableFarReturnedOldOwners R r p,
    ∑ e ∈ stableFarReturnedCrossingCofactors R r p q,
      canonicalMoebiusWeight e * w e

/-- Center one genuine descended copy against every old-owner return, while
retaining the chosen complex observable. -/
def stableFarReturnedWeightedCenteredMass
    (w : ℕ → ℂ) (R r p : ℕ) : ℂ :=
  stableFarReturnedWeightedDescendedMass w R r p -
    stableFarReturnedWeightedCrossingColumn w R r p

/-- **Weighted returned-fibre Fubini.**  The physical old-owner occurrence
column can be pushed onto the common returned cofactor carrier for every complex
observable `w`.  No norm, absolute value, or unsigned occurrence bound enters. -/
theorem stableFarReturnedWeightedCrossingColumn_eq_multiplicity
    (w : ℕ → ℂ) {R r p : ℕ} (hr : r.Prime) (hp : p.Prime) :
    stableFarReturnedWeightedCrossingColumn w R r p =
      ∑ e ∈ stableFarReturnedDescendedCofactors R r p,
        (stableFarReturnedCrossingMultiplicity R r p e : ℂ) *
          canonicalMoebiusWeight e * w e := by
  unfold stableFarReturnedWeightedCrossingColumn
  calc
    (∑ q ∈ stableFarReturnedOldOwners R r p,
        ∑ e ∈ stableFarReturnedCrossingCofactors R r p q,
          canonicalMoebiusWeight e * w e) =
      ∑ q ∈ stableFarReturnedOldOwners R r p,
        ∑ e ∈ stableFarReturnedDescendedCofactors R r p,
          if e ∈ stableFarReturnedCrossingCofactors R r p q then
            canonicalMoebiusWeight e * w e else 0 := by
              apply Finset.sum_congr rfl
              intro q hq
              rw [← Finset.sum_filter]
              rw [← stableFarReturnedCrossingCofactors_eq_descended_filter
                hr hp hq]
    _ = ∑ e ∈ stableFarReturnedDescendedCofactors R r p,
        ∑ q ∈ stableFarReturnedOldOwners R r p,
          if e ∈ stableFarReturnedCrossingCofactors R r p q then
            canonicalMoebiusWeight e * w e else 0 := by
              exact Finset.sum_comm
    _ = ∑ e ∈ stableFarReturnedDescendedCofactors R r p,
        (stableFarReturnedCrossingMultiplicity R r p e : ℂ) *
          canonicalMoebiusWeight e * w e := by
              apply Finset.sum_congr rfl
              intro e _he
              rw [← Finset.sum_filter]
              simp [stableFarReturnedCrossingMultiplicity]
              ring

/-- **Weighted centered multiplicity normal form.**  The exact coefficient of a
returned cofactor is `1 - multiplicity`, now valid against every complex test
observable.  This is the state-resolved interface that endpoint Mertens values
cannot see. -/
theorem stableFarReturnedWeightedCenteredMass_eq_multiplicity
    (w : ℕ → ℂ) {R r p : ℕ} (hr : r.Prime) (hp : p.Prime) :
    stableFarReturnedWeightedCenteredMass w R r p =
      ∑ e ∈ stableFarReturnedDescendedCofactors R r p,
        (1 - (stableFarReturnedCrossingMultiplicity R r p e : ℂ)) *
          canonicalMoebiusWeight e * w e := by
  unfold stableFarReturnedWeightedCenteredMass
    stableFarReturnedWeightedDescendedMass
  rw [stableFarReturnedWeightedCrossingColumn_eq_multiplicity w hr hp]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _he
  ring

/-! ## Perron/log-frequency specialization -/

/-- State-resolved log-frequency projection of the centered returned fibre. -/
def stableFarReturnedLogFrequencyCenteredMass
    (tau : ℝ) (R r p : ℕ) : ℂ :=
  stableFarReturnedWeightedCenteredMass
    (stableFarPrimeLogPhase tau) R r p

/-- The Perron/log-frequency projection retains the exact physical centered
multiplicity coefficient on every returned cofactor. -/
theorem stableFarReturnedLogFrequencyCenteredMass_eq_multiplicity
    (tau : ℝ) {R r p : ℕ} (hr : r.Prime) (hp : p.Prime) :
    stableFarReturnedLogFrequencyCenteredMass tau R r p =
      ∑ e ∈ stableFarReturnedDescendedCofactors R r p,
        (1 - (stableFarReturnedCrossingMultiplicity R r p e : ℂ)) *
          canonicalMoebiusWeight e * stableFarPrimeLogPhase tau e := by
  unfold stableFarReturnedLogFrequencyCenteredMass
  exact stableFarReturnedWeightedCenteredMass_eq_multiplicity
    (stableFarPrimeLogPhase tau) hr hp

@[simp] theorem stableFarReturnedLogFrequencyCenteredMass_zero
    {R r p : ℕ} (hr : r.Prime) (hp : p.Prime) :
    stableFarReturnedLogFrequencyCenteredMass 0 R r p =
      ∑ e ∈ stableFarReturnedDescendedCofactors R r p,
        (1 - (stableFarReturnedCrossingMultiplicity R r p e : ℂ)) *
          canonicalMoebiusWeight e := by
  rw [stableFarReturnedLogFrequencyCenteredMass_eq_multiplicity 0 hr hp]
  simp

/-! ## Critical-line half-density and q^2 translation -/

/-- Critical-line mode on logarithmic scale: the half-density `exp(t/2)` times
one pure log frequency.  This is a harmonic coordinate; it does not assert that
`1/2 + i*tau` is a zero of zeta. -/
def stableFarCriticalLogMode (tau t : ℝ) : ℂ :=
  Complex.exp (((t / 2 : ℝ) : ℂ)) * stableFarLogFrequencyMode tau t

/-- Exact q^2 multiplier on the critical log coordinate.  The first factor is
the half-density contraction and the second is the already-compiled phase
rotation. -/
def stableFarCriticalQ2LogMultiplier (tau : ℝ) (q : ℕ) : ℂ :=
  Complex.exp (((-Real.log (q : ℝ) : ℝ) : ℂ)) *
    stableFarQ2LogFrequencyMultiplier tau q

/-- **Critical-line q^2 diagonalization.**  Translation by `2 log q` preserves
the frequency and multiplies the critical mode by one scalar.  This is the
finite, zero-free version of the Perron statement that a q^2 daughter carries a
`q^{-1}` half-density together with phase `exp(-2 i tau log q)`. -/
theorem stableFarCriticalLogMode_q2_shift
    (tau t : ℝ) (q : ℕ) :
    stableFarCriticalLogMode tau
        (t - 2 * Real.log (q : ℝ)) =
      stableFarCriticalQ2LogMultiplier tau q *
        stableFarCriticalLogMode tau t := by
  have hhalf :
      Complex.exp ((((t - 2 * Real.log (q : ℝ)) / 2 : ℝ) : ℂ)) =
        Complex.exp (((-Real.log (q : ℝ) : ℝ) : ℂ)) *
          Complex.exp (((t / 2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold stableFarCriticalLogMode stableFarCriticalQ2LogMultiplier
  rw [hhalf, stableFarLogFrequencyMode_q2_shift]
  ring

end RHLean.Proof

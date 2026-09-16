import Mathlib
import «research.LOW_OWNER_Q2_ENDPOINT_FREQUENCY_DISTANCE»

/-!
# Exact endpoint-arc Fubini for finite wheel frequencies

The physical information "distance from a known endpoint" has an exact Fourier
form.  For the finite Dirichlet response at one wheel frequency,

  D_{A+d}(r) - D_A(r) = chi(r)^A D_d(r).

Thus the difference of two pinned prefixes is not a new global object: it is a
finite sum of endpoint-phased short arcs.  For a nonzero frequency the short arc
then depends only on `d mod c_r`, where `c_r` is the reduced additive conductor.

This file is deliberately prior to any identification with a particular
Mertens shell.  It proves the exact finite harmonic dictionary, with no norm or
nonconcentration estimate.
-/

noncomputable section
open scoped BigOperators
open AddChar

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- Finite Dirichlet kernels split exactly at an intermediate distance. -/
theorem primeWheelDirichletKernel_add
    (W : PrimeWheelFiniteSystem) (A d : ℕ)
    (r : ZMod W.modulus) :
    primeWheelDirichletKernel W (A + d) r =
      primeWheelDirichletKernel W A r +
        ZMod.stdAddChar r ^ A * primeWheelDirichletKernel W d r := by
  by_cases hr : r = 0
  · subst r
    simp [primeWheelDirichletKernel_zero]
  · rw [primeWheelDirichletKernel_eq_geom_of_ne_zero W (A + d) r hr,
      primeWheelDirichletKernel_eq_geom_of_ne_zero W A r hr,
      primeWheelDirichletKernel_eq_geom_of_ne_zero W d r hr,
      pow_add]
    ring

/-- One frequency contribution to the forward arc of length `d` starting after
prefix length `A`. -/
def primeWheelForwardArcFrequencyAtom
    (W : PrimeWheelFiniteSystem) (A d : ℕ)
    (r : ZMod W.modulus) : ℂ :=
  primeWheelPinnedCoefficient W r *
    ZMod.stdAddChar r ^ A * primeWheelDirichletKernel W d r

/-- **Exact endpoint-arc Fubini.**  A difference of two finite pinned prefixes
is the sum of the endpoint-phased short frequency arcs. -/
theorem primeWheelDirichletPrefix_add_sub_eq_sum_forwardArc
    (W : PrimeWheelFiniteSystem) (A d : ℕ) :
    primeWheelDirichletPrefix W (A + d) -
        primeWheelDirichletPrefix W A =
      ∑ r : ZMod W.modulus,
        primeWheelForwardArcFrequencyAtom W A d r := by
  unfold primeWheelDirichletPrefix primeWheelForwardArcFrequencyAtom
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [primeWheelDirichletKernel_add W A d r]
  ring

/-- At a nonzero frequency, the short endpoint arc depends only on the physical
distance modulo the reduced additive conductor. -/
theorem primeWheelForwardArcFrequencyAtom_eq_reducedDistance
    (W : PrimeWheelFiniteSystem) (A d : ℕ)
    (r : ZMod W.modulus) (hr : r ≠ 0) :
    primeWheelForwardArcFrequencyAtom W A d r =
      primeWheelPinnedCoefficient W r *
        ZMod.stdAddChar r ^ A *
          primeWheelDirichletKernel W
            (d % reducedAdditiveConductor r) r := by
  unfold primeWheelForwardArcFrequencyAtom
  rw [primeWheelDirichletKernel_eq_mod_reducedAdditiveConductor W d r hr]

/-- The complete forward prefix difference can be partitioned into the zero
frequency plus nonzero residual-distance atoms without changing the sum. -/
theorem primeWheelDirichletPrefix_add_sub_eq_zero_add_reducedNonzero
    (W : PrimeWheelFiniteSystem) (A d : ℕ) :
    primeWheelDirichletPrefix W (A + d) -
        primeWheelDirichletPrefix W A =
      primeWheelForwardArcFrequencyAtom W A d 0 +
        ∑ r : ZMod W.modulus,
          if r = 0 then 0 else
            primeWheelPinnedCoefficient W r *
              ZMod.stdAddChar r ^ A *
                primeWheelDirichletKernel W
                  (d % reducedAdditiveConductor r) r := by
  rw [primeWheelDirichletPrefix_add_sub_eq_sum_forwardArc W A d]
  classical
  let f : ZMod W.modulus → ℂ :=
    fun r => primeWheelForwardArcFrequencyAtom W A d r
  have hsplitPointwise : ∀ r : ZMod W.modulus,
      f r =
        (if r = 0 then f 0 else 0) +
        (if r = 0 then 0 else f r) := by
    intro r
    by_cases hr : r = 0
    · subst r
      simp
    · simp [hr]
  calc
    (∑ r : ZMod W.modulus, primeWheelForwardArcFrequencyAtom W A d r) =
        ∑ r : ZMod W.modulus,
          ((if r = 0 then f 0 else 0) +
            (if r = 0 then 0 else f r)) := by
      apply Finset.sum_congr rfl
      intro r _hrmem
      simpa [f] using hsplitPointwise r
    _ = (∑ r : ZMod W.modulus, if r = 0 then f 0 else 0) +
        ∑ r : ZMod W.modulus, if r = 0 then 0 else f r := by
      rw [Finset.sum_add_distrib]
    _ = f 0 +
        ∑ r : ZMod W.modulus, if r = 0 then 0 else f r := by
      simp
    _ = primeWheelForwardArcFrequencyAtom W A d 0 +
        ∑ r : ZMod W.modulus,
          if r = 0 then 0 else
            primeWheelPinnedCoefficient W r *
              ZMod.stdAddChar r ^ A *
                primeWheelDirichletKernel W
                  (d % reducedAdditiveConductor r) r := by
      dsimp [f]
      congr 1
      apply Finset.sum_congr rfl
      intro r _hrmem
      by_cases hr : r = 0
      · simp [hr]
      · simp only [hr, if_false]
        exact primeWheelForwardArcFrequencyAtom_eq_reducedDistance W A d r hr

end RHLean.Analysis

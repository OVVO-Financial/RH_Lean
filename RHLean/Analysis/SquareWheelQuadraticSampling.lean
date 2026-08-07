import Mathlib
import RHLean.Analysis.PrimeWheelDirichletResponse
import RHLean.Analysis.PrimeWheelHarmonicCriterion
import RHLean.Analysis.SquareWheelNesting

/-!
# Quadratic sampling of the primorial-wheel spectrum at square endpoints

The square-block and wheel clocks interact nontrivially on the Fourier side.
For a pinned wheel prefix ending at

`X_n = (n+1)^2 - 1`,

the prefix length is `N = X_n - lower`.  The pinned start phase is the additive
character at `lower+1`; multiplying it by the `N`th power arising from the
Dirichlet kernel gives exactly the quadratic phase at `(n+1)^2`.

This module also records the exact conductor annihilation behind square-to-square
runs.  A nonzero frequency has additive order equal to its reduced additive
conductor.  Hence its finite Dirichlet kernel vanishes whenever that reduced
conductor divides the interval length.  Applied to a square run, the relevant
length is a difference of two squares.

These are exact finite identities.  No nonconcentration or power-saving estimate
is asserted here.
-/

noncomputable section

open scoped BigOperators
open AddChar

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

private theorem squareWheel_stdAddChar_nat_mul
    (W : PrimeWheelFiniteSystem) (r : ZMod W.modulus) (j : ℕ) :
    ZMod.stdAddChar (((j : ℕ) : ZMod W.modulus) * r) =
      ZMod.stdAddChar r ^ j := by
  simpa [nsmul_eq_mul] using
    (AddChar.map_nsmul_eq_pow
      (ZMod.stdAddChar : AddChar (ZMod W.modulus) ℂ) j r)

/-- For a finite wheel modulus, the reduced additive conductor is literally the
additive order of the frequency in `ZMod modulus`. -/
theorem reducedAdditiveConductor_eq_addOrderOf
    (W : PrimeWheelFiniteSystem) (r : ZMod W.modulus) :
    reducedAdditiveConductor r = addOrderOf r := by
  have hQ : W.modulus ≠ 0 := Nat.ne_of_gt W.modulus_pos
  calc
    reducedAdditiveConductor r =
        W.modulus / Nat.gcd r.val W.modulus := by
      simp [reducedAdditiveConductor]
    _ = W.modulus / Nat.gcd W.modulus r.val := by
      rw [Nat.gcd_comm]
    _ = addOrderOf ((r.val : ℕ) : ZMod W.modulus) := by
      symm
      exact ZMod.addOrderOf_coe r.val hQ
    _ = addOrderOf r := by
      rw [ZMod.natCast_zmod_val]

/-- Exact conductor annihilation of one finite Dirichlet response.  Every
nonzero frequency vanishes on an interval whose length is a multiple of its
reduced additive conductor. -/
theorem primeWheelDirichletKernel_eq_zero_of_reducedConductor_dvd
    (W : PrimeWheelFiniteSystem) (N : ℕ)
    (r : ZMod W.modulus) (hr : r ≠ 0)
    (hdiv : reducedAdditiveConductor r ∣ N) :
    primeWheelDirichletKernel W N r = 0 := by
  have hchar : ZMod.stdAddChar r ≠ 1 := by
    intro h
    have hzero : r = 0 :=
      ZMod.injective_stdAddChar (by simpa using h)
    exact hr hzero
  have horder : addOrderOf r ∣ N := by
    rw [← reducedAdditiveConductor_eq_addOrderOf W r]
    exact hdiv
  have hnsmul : N • r = 0 :=
    (addOrderOf_dvd_iff_nsmul_eq_zero).1 horder
  have hpow : ZMod.stdAddChar r ^ N = 1 := by
    calc
      ZMod.stdAddChar r ^ N =
          ZMod.stdAddChar (N • r) := by
        symm
        exact AddChar.map_nsmul_eq_pow
          (ZMod.stdAddChar : AddChar (ZMod W.modulus) ℂ) N r
      _ = ZMod.stdAddChar 0 := by rw [hnsmul]
      _ = 1 := AddChar.map_zero_eq_one _
  have hsum :
      primeWheelDirichletKernel W N r =
        ∑ j ∈ Finset.range N, ZMod.stdAddChar r ^ j := by
    unfold primeWheelDirichletKernel
    apply Finset.sum_congr rfl
    intro j hj
    exact squareWheel_stdAddChar_nat_mul W r j
  rw [hsum, geom_sum_eq hchar N, hpow]
  simp

/-- Prefix length from the wheel anchor to the `n`th complete-square endpoint. -/
def squareWheelSampleLength
    (W : PrimeWheelFiniteSystem) (n : ℕ) : ℕ :=
  RHLean.Analysis.squarePrefixEndpoint n - W.lower

/-- If a square endpoint lies after the wheel anchor, the pinned start phase
and the Dirichlet power combine to the pure quadratic phase at `(n+1)^2`.
This is the exact cancellation that makes square sampling special. -/
theorem primeWheelPinnedPhase_mul_samplePower_eq_quadraticPhase
    (W : PrimeWheelFiniteSystem) (n : ℕ)
    (r : ZMod W.modulus)
    (hlower : W.lower ≤ RHLean.Analysis.squarePrefixEndpoint n) :
    primeWheelPinnedPhase W r *
        ZMod.stdAddChar r ^ squareWheelSampleLength W n =
      ZMod.stdAddChar
        (((((n + 1) ^ 2 : ℕ) : ZMod W.modulus)) * r) := by
  let N := squareWheelSampleLength W n
  have hanchor : W.lower + N = RHLean.Analysis.squarePrefixEndpoint n := by
    dsimp [N, squareWheelSampleLength]
    exact Nat.add_sub_of_le hlower
  have hendpoint := RHLean.Analysis.squarePrefixEndpoint_add_one n
  have hclock : W.lower + 1 + N = (n + 1) ^ 2 := by
    omega
  have hpow :
      ZMod.stdAddChar r ^ N =
        ZMod.stdAddChar (((N : ℕ) : ZMod W.modulus) * r) := by
    symm
    exact squareWheel_stdAddChar_nat_mul W r N
  rw [show squareWheelSampleLength W n = N by rfl, hpow]
  unfold primeWheelPinnedPhase
  rw [← AddChar.map_add_eq_mul]
  congr 1
  have hcast :
      (((W.lower + 1 + N : ℕ) : ZMod W.modulus)) =
        ((((n + 1) ^ 2 : ℕ) : ZMod W.modulus)) := by
    exact congrArg (fun m : ℕ => (m : ZMod W.modulus)) hclock
  calc
    (((W.lower + 1 : ℕ) : ZMod W.modulus) * r) +
        (((N : ℕ) : ZMod W.modulus) * r) =
      (((W.lower + 1 + N : ℕ) : ZMod W.modulus) * r) := by
        push_cast
        ring
    _ = ((((n + 1) ^ 2 : ℕ) : ZMod W.modulus) * r) := by
      rw [hcast]

/-- Square-run specialization of conductor annihilation.  If a nonzero
frequency's reduced conductor divides the difference of the two square
endpoints, then its interval Dirichlet response is exactly zero. -/
theorem primeWheelDirichletKernel_squareRun_eq_zero
    (W : PrimeWheelFiniteSystem) (u v : ℕ)
    (r : ZMod W.modulus) (hr : r ≠ 0)
    (huv : u ≤ v)
    (hdiv : reducedAdditiveConductor r ∣ v ^ 2 - u ^ 2) :
    primeWheelDirichletKernel W (v ^ 2 - u ^ 2) r = 0 := by
  exact primeWheelDirichletKernel_eq_zero_of_reducedConductor_dvd
    W (v ^ 2 - u ^ 2) r hr hdiv

end RHLean.Analysis

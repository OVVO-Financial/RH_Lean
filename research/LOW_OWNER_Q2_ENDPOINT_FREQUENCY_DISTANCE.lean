import Mathlib
import RHLean.Analysis.SquareWheelQuadraticSampling
import «research.LOW_OWNER_Q2_NEAREST_SQUARE_ENDPOINT»

/-!
# Endpoint phase plus residual conductor distance

After the nearest-square reduction, every literal q² daughter lies within a
short oriented arc of a completed-square endpoint.  For one finite wheel
frequency `r`, the remaining arc is not an arbitrary prefix: its Dirichlet
response depends only on the arc length modulo the reduced additive conductor.

This file records that exact finite fact.  If

  c_r = reducedAdditiveConductor r,

then

  D_N(r) = D_{N mod c_r}(r).

We also package the endpoint-coordinate backward arc.  A completed-square
endpoint `S²-1` has known endpoint phase at `S²`; moving backward by `d` sites
multiplies by the inverse `d`th frequency phase and by the length-`d` Dirichlet
kernel.  Both factors are unchanged after replacing `d` by `d mod c_r`.

Thus the frequency state of a nearest-square shell is exactly

  (completed-square root S, frequency r, d mod c_r),

with the left/right midpoint choice already encoded by the selected endpoint.
No asymptotic estimate is used.
-/

noncomputable section
open scoped BigOperators
open AddChar

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- Powers of a finite wheel frequency depend only on the exponent modulo the
reduced additive conductor. -/
theorem stdAddChar_pow_eq_mod_reducedAdditiveConductor
    (W : PrimeWheelFiniteSystem) (N : ℕ)
    (r : ZMod W.modulus) :
    ZMod.stdAddChar r ^ N =
      ZMod.stdAddChar r ^ (N % reducedAdditiveConductor r) := by
  let c : ℕ := reducedAdditiveConductor r
  have hcOrder : c = addOrderOf r := by
    dsimp [c]
    exact reducedAdditiveConductor_eq_addOrderOf W r
  have hcDvd : addOrderOf r ∣ c := by
    rw [hcOrder]
  have hcsmul : c • r = 0 :=
    (addOrderOf_dvd_iff_nsmul_eq_zero).1 hcDvd
  have hpowc : ZMod.stdAddChar r ^ c = 1 := by
    calc
      ZMod.stdAddChar r ^ c = ZMod.stdAddChar (c • r) := by
        symm
        exact AddChar.map_nsmul_eq_pow
          (ZMod.stdAddChar : AddChar (ZMod W.modulus) ℂ) c r
      _ = ZMod.stdAddChar 0 := by rw [hcsmul]
      _ = 1 := AddChar.map_zero_eq_one _
  have hdecomp : N % c + c * (N / c) = N := Nat.mod_add_div N c
  calc
    ZMod.stdAddChar r ^ N =
        ZMod.stdAddChar r ^ (N % c + c * (N / c)) := by rw [hdecomp]
    _ = ZMod.stdAddChar r ^ (N % c) *
        ZMod.stdAddChar r ^ (c * (N / c)) := by rw [pow_add]
    _ = ZMod.stdAddChar r ^ (N % c) *
        (ZMod.stdAddChar r ^ c) ^ (N / c) := by rw [pow_mul]
    _ = ZMod.stdAddChar r ^ (N % c) := by rw [hpowc]; simp
    _ = ZMod.stdAddChar r ^ (N % reducedAdditiveConductor r) := by rfl

/-- **Exact residual-distance theorem.**  Every nonzero finite-wheel Dirichlet
response depends only on the distance modulo that frequency's reduced additive
conductor. -/
theorem primeWheelDirichletKernel_eq_mod_reducedAdditiveConductor
    (W : PrimeWheelFiniteSystem) (N : ℕ)
    (r : ZMod W.modulus) (hr : r ≠ 0) :
    primeWheelDirichletKernel W N r =
      primeWheelDirichletKernel W (N % reducedAdditiveConductor r) r := by
  rw [primeWheelDirichletKernel_eq_geom_of_ne_zero W N r hr,
    primeWheelDirichletKernel_eq_geom_of_ne_zero
      W (N % reducedAdditiveConductor r) r hr,
    stdAddChar_pow_eq_mod_reducedAdditiveConductor W N r]

/-- Root of the completed square selected by the nearest-endpoint midpoint
rule.  Its endpoint is `S²-1`. -/
def q2NearestSquareRoot (x : ℕ) : ℕ :=
  let s := Nat.sqrt x
  if x < s ^ 2 + s then s else s + 1

/-- Exact integer distance from `x` to its selected completed-square endpoint. -/
def q2NearestSquareDistance (x : ℕ) : ℕ :=
  let s := Nat.sqrt x
  if x < s ^ 2 + s then x - squareRootEndpoint s
  else squareRootEndpoint (s + 1) - x

/-- The root-coordinate and endpoint-coordinate definitions agree exactly. -/
theorem q2NearestSquareEndpoint_eq_rootEndpoint (x : ℕ) :
    q2NearestSquareEndpoint x =
      squareRootEndpoint (q2NearestSquareRoot x) := by
  simp [q2NearestSquareEndpoint, q2NearestSquareRoot]

/-- The explicit nearest-endpoint distance is at most the square-block
half-radius. -/
theorem q2NearestSquareDistance_le_sqrt (x : ℕ) :
    q2NearestSquareDistance x ≤ Nat.sqrt x := by
  let s := Nat.sqrt x
  have hs2 : s ^ 2 ≤ x := by
    simpa [s] using Nat.sqrt_le' x
  have hxlt : x < (s + 1) ^ 2 := by
    simpa [s] using Nat.lt_succ_sqrt' x
  by_cases hmid : x < s ^ 2 + s
  · have hdist :
        q2NearestSquareDistance x = x - squareRootEndpoint s := by
      simp [q2NearestSquareDistance, s, hmid]
    rw [hdist]
    have hgap : x - squareRootEndpoint s ≤ s := by
      unfold squareRootEndpoint
      omega
    simpa [s] using hgap
  · have hmid' : s ^ 2 + s ≤ x := Nat.le_of_not_gt hmid
    have hdist :
        q2NearestSquareDistance x = squareRootEndpoint (s + 1) - x := by
      simp [q2NearestSquareDistance, s, hmid]
    rw [hdist]
    have hsquare : (s + 1) ^ 2 = s ^ 2 + 2 * s + 1 := by ring
    have hgap : squareRootEndpoint (s + 1) - x ≤ s := by
      unfold squareRootEndpoint
      rw [hsquare]
      omega
    simpa [s] using hgap

/-- Backward frequency response from a completed-square endpoint `S²-1` by a
known distance `d`.  The first factor is the known endpoint phase at `S²`; the
second transports backward by `d`; the third is the finite arc response. -/
def completedSquareBackwardFrequencyKernel
    (W : PrimeWheelFiniteSystem) (S d : ℕ)
    (r : ZMod W.modulus) : ℂ :=
  ZMod.stdAddChar (((S ^ 2 : ℕ) : ZMod W.modulus) * r) *
    (ZMod.stdAddChar r ^ d)⁻¹ *
      primeWheelDirichletKernel W d r

/-- **Endpoint + residual distance normal form.**  At every nonzero frequency,
the completed-square backward arc is unchanged after replacing its physical
distance by the remainder modulo the reduced conductor. -/
theorem completedSquareBackwardFrequencyKernel_eq_reducedDistance
    (W : PrimeWheelFiniteSystem) (S d : ℕ)
    (r : ZMod W.modulus) (hr : r ≠ 0) :
    completedSquareBackwardFrequencyKernel W S d r =
      completedSquareBackwardFrequencyKernel W S
        (d % reducedAdditiveConductor r) r := by
  unfold completedSquareBackwardFrequencyKernel
  rw [stdAddChar_pow_eq_mod_reducedAdditiveConductor W d r,
    primeWheelDirichletKernel_eq_mod_reducedAdditiveConductor W d r hr]

end RHLean.Analysis

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- Finite endpoint/frequency state attached to one literal low-owner q²
daughter.  The completed-square root and the physical distance are completely
explicit from the daughter cutoff. -/
def lowOwnerQ2NearestSquareFrequencyKernel
    (W : PrimeWheelFiniteSystem) (R q : ℕ)
    (r : ZMod W.modulus) : ℂ :=
  completedSquareBackwardFrequencyKernel W
    (q2NearestSquareRoot (rawQ2ChildCutoff R q))
    (q2NearestSquareDistance (rawQ2ChildCutoff R q)) r

/-- Every nonzero frequency of every literal q² midpoint shell is exactly the
same finite kernel evaluated at its residual conductor distance. -/
theorem lowOwnerQ2NearestSquareFrequencyKernel_eq_reducedDistance
    (W : PrimeWheelFiniteSystem) (R q : ℕ)
    (r : ZMod W.modulus) (hr : r ≠ 0) :
    lowOwnerQ2NearestSquareFrequencyKernel W R q r =
      completedSquareBackwardFrequencyKernel W
        (q2NearestSquareRoot (rawQ2ChildCutoff R q))
        (q2NearestSquareDistance (rawQ2ChildCutoff R q) %
          reducedAdditiveConductor r) r := by
  unfold lowOwnerQ2NearestSquareFrequencyKernel
  exact completedSquareBackwardFrequencyKernel_eq_reducedDistance
    W (q2NearestSquareRoot (rawQ2ChildCutoff R q))
      (q2NearestSquareDistance (rawQ2ChildCutoff R q)) r hr

end RHLean.Proof

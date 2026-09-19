import Mathlib
import RHLean.Proof.PrimeCombVisualizationDynamics
import RHLean.Analysis.SquareRootMiddleSequentialCoherence
import RHLean.Proof.LowWheelCanonicalPrimeSplit

/-!
# Large-prime Euler response at a fixed endpoint

This file formalizes the elementary coordinate

  N_X(m) = #{ p prime : R < p and m*p <= X }

used to read the post-root sector one low Euler prime at a time.

The point is deliberately finite.

* one fresh low prime q leaves exactly the strip
    m*p <= X < q*m*p;
* two fresh primes give the four-corner difference as the difference of two
  such strips;
* the X = 30, R = 5 example is executable in the kernel;
* the arbitrary low-prime cube at one outer prime is exactly the already
  formalized frozen prime-universe mass at cutoff floor(X/(m*p)).

The last statement is the generalization: after all low coordinates are
processed, the residual at a fixed outer prime is an ordinary lower-scale
Mertens prefix whenever the frozen universe is saturated.  Thus endpoint
truncation is the only source of residual, but its signed boundary multiplicity
need not be one.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Indicator for one available large-prime extension. -/
def largePrimeEndpointIndicator
    (X R m p : ℕ) : ℤ :=
  if R < p ∧ p.Prime then
    if m * p ≤ X then 1 else 0
  else 0

/-- Finite large-prime response
    N_X(m) = #{p prime : R < p and m*p <= X}. -/
def largePrimeResponse
    (X R m : ℕ) : ℤ :=
  ∑ p ∈ Finset.range (X + 1), largePrimeEndpointIndicator X R m p

/-- The one-prime endpoint strip left after pairing m with q*m. -/
def largePrimeStripResponse
    (X R q m : ℕ) : ℤ :=
  ∑ p ∈ Finset.range (X + 1),
    if R < p ∧ p.Prime ∧ m * p ≤ X ∧ X < (q * m) * p then 1 else 0

/-- Pointwise fresh-prime cancellation.  The two Euler copies cancel unless
the endpoint lies strictly between m*p and q*m*p. -/
theorem largePrimeEndpointIndicator_sub_mul_eq_strip
    {X R m p q : ℕ} (hq : 1 ≤ q) :
    largePrimeEndpointIndicator X R m p -
        largePrimeEndpointIndicator X R (q * m) p =
      if R < p ∧ p.Prime ∧ m * p ≤ X ∧ X < (q * m) * p then 1 else 0 := by
  have hm : m ≤ q * m := by
    simpa using Nat.mul_le_mul_right m hq
  have hmono : m * p ≤ (q * m) * p :=
    Nat.mul_le_mul_right p hm
  by_cases hlarge : R < p ∧ p.Prime
  · by_cases hbase : m * p ≤ X
    · by_cases hchild : (q * m) * p ≤ X
      · have hnot : ¬ X < (q * m) * p := Nat.not_lt.mpr hchild
        simp [largePrimeEndpointIndicator, hlarge, hbase, hchild, hnot]
      · have hcross : X < (q * m) * p := Nat.lt_of_not_ge hchild
        simp [largePrimeEndpointIndicator, hlarge, hbase, hchild, hcross]
    · have hchild : ¬ (q * m) * p ≤ X := by
        intro h
        exact hbase (hmono.trans h)
      simp [largePrimeEndpointIndicator, hlarge, hbase, hchild]
  · simp [largePrimeEndpointIndicator, hlarge]

/-- Summed one-prime cancellation:
    N_X(m) - N_X(qm) is exactly the displaced prime strip. -/
theorem largePrimeResponse_sub_mul_eq_strip
    {X R m q : ℕ} (hq : 1 ≤ q) :
    largePrimeResponse X R m - largePrimeResponse X R (q * m) =
      largePrimeStripResponse X R q m := by
  unfold largePrimeResponse largePrimeStripResponse
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  exact largePrimeEndpointIndicator_sub_mul_eq_strip hq

/-- Exact two-prime four-corner response.  No estimate is used: the mixed
difference is the first q-strip minus the same q-strip after displacement by r. -/
theorem largePrimeResponse_twoPrimeMixed_eq_stripDifference
    {X R m q r : ℕ} (hq : 1 ≤ q) :
    largePrimeResponse X R m -
        largePrimeResponse X R (q * m) -
        largePrimeResponse X R (r * m) +
        largePrimeResponse X R (q * (r * m)) =
      largePrimeStripResponse X R q m -
        largePrimeStripResponse X R q (r * m) := by
  calc
    largePrimeResponse X R m -
        largePrimeResponse X R (q * m) -
        largePrimeResponse X R (r * m) +
        largePrimeResponse X R (q * (r * m)) =
      (largePrimeResponse X R m -
        largePrimeResponse X R (q * m)) -
      (largePrimeResponse X R (r * m) -
        largePrimeResponse X R (q * (r * m))) := by ring
    _ = largePrimeStripResponse X R q m -
        largePrimeStripResponse X R q (r * m) := by
      rw [largePrimeResponse_sub_mul_eq_strip hq,
        largePrimeResponse_sub_mul_eq_strip hq]

/-! ## The literal X = 30 picture

R = floor(sqrt 30) = 5.  The outer primes are
7, 11, 13, 17, 19, 23, 29.

Thus N(1)=7, N(2)=3, N(3)=1, N(6)=0, and the {2,3} Euler square has signed
boundary 7-3-1+0 = 3.  In strip language the q=2 strip has four primes,
while its r=3 displaced copy has one prime (p=7), hence 4-1=3.
-/

example : largePrimeResponse 30 5 1 = 7 := by native_decide
example : largePrimeResponse 30 5 2 = 3 := by native_decide
example : largePrimeResponse 30 5 3 = 1 := by native_decide
example : largePrimeResponse 30 5 6 = 0 := by native_decide

example :
    largePrimeResponse 30 5 1 -
        largePrimeResponse 30 5 2 -
        largePrimeResponse 30 5 3 +
        largePrimeResponse 30 5 6 = 3 := by
  native_decide

example : largePrimeStripResponse 30 5 2 1 = 4 := by native_decide
example : largePrimeStripResponse 30 5 2 3 = 1 := by native_decide

/-- Adding the third low prime 5 at X=30 leaves the same signed endpoint
boundary because every new vertex created beyond the root has zero response. -/
example :
    largePrimeResponse 30 5 1 -
        largePrimeResponse 30 5 2 -
        largePrimeResponse 30 5 3 -
        largePrimeResponse 30 5 5 +
        largePrimeResponse 30 5 6 +
        largePrimeResponse 30 5 10 +
        largePrimeResponse 30 5 15 -
        largePrimeResponse 30 5 30 = 3 := by
  native_decide

/-! ## Arbitrary finite Euler cube at one outer prime -/

/-- The full alternating low-prime cube seen from one outer prime p.
The moving endpoint is exactly floor(X/(m*p)). -/
def largePrimeEulerCubeAt
    (X m p : ℕ) (S : Finset ℕ) : ℤ :=
  frozenPrimeUniverseMass S (X / (m * p))

/-- Expanded form: the residual is literally the alternating sum of the cube
vertices surviving the moving cutoff. -/
theorem largePrimeEulerCubeAt_eq_cutoffSum
    (X m p : ℕ) (S : Finset ℕ) :
    largePrimeEulerCubeAt X m p S =
      ∑ t ∈ S.powerset,
        if primeFaceProduct t ≤ X / (m * p) then
          booleanCubeSign t else 0 := by
  exact frozenPrimeUniverseMass_eq_cutoffSum S (X / (m * p))

/-- A complete nonempty Euler cube cancels exactly.  Therefore only a cube cut
by the moving endpoint can leave mass. -/
theorem largePrimeEulerCubeAt_eq_zero_of_complete
    {X m p : ℕ} {S : Finset ℕ}
    (hS : S.Nonempty)
    (hprime : ∀ q ∈ S, q.Prime)
    (hfit : primeFaceProduct S ≤ X / (m * p)) :
    largePrimeEulerCubeAt X m p S = 0 := by
  exact frozenPrimeUniverseMass_eq_zero_of_complete_old_cube
    hS hprime hfit

/-- When the low-prime universe already contains every prime up to the moving
cutoff, the arbitrary Euler-cube boundary is exactly the ordinary lower-scale
Mertens prefix. -/
theorem largePrimeEulerCubeAt_cast_eq_mertens
    {X R m p : ℕ}
    (hcut : X / (m * p) ≤ R) :
    ((largePrimeEulerCubeAt X m p (primesUpTo R) : ℤ) : ℂ) =
      mertensSummatory (X / (m * p)) := by
  unfold largePrimeEulerCubeAt
  exact frozenPrimeUniverseMass_primesUpTo_cast_eq_mertens hcut

/-! A useful finite warning: endpoint ownership does not force one unit of
residual.  With cutoff 5 the saturated low-prime cube already has mass M(5)=-2.
For example X=100, R=10, p=19 gives floor(100/19)=5, so one outer-prime cube
carries two net boundary units after all exact interior cancellation. -/

example :
    frozenPrimeUniverseMass (primesUpTo 10) 5 = -2 := by
  native_decide

example :
    largePrimeEulerCubeAt 100 1 19 (primesUpTo 10) = -2 := by
  native_decide

/-! ## Coupled smooth/large-prime Euler recurrence

The correct object for the user's "every added prime offsets the previous
copies" picture is not the post-root sum in isolation. Keep the complete
low-prime cube and all post-root fibres in one signed state. A fresh low prime
then acts on the whole coupled state by the same multiplicative finite
difference.
-/

/-- Coupled low-cube minus large-prime-extension state. The outer cap U is
fixed; primes beyond the current inner endpoint are harmless because their
reciprocal cutoff is zero. Keeping U fixed makes the Euler recurrence literal,
with no changing-index-set bookkeeping. -/
def coupledLargePrimeEulerResidual
    (U R Y : ℕ) (S : Finset ℕ) : ℤ :=
  frozenPrimeUniverseMass S Y -
    ∑ p ∈ Finset.range (U + 1),
      if R < p ∧ p.Prime then
        frozenPrimeUniverseMass S (Y / p)
      else 0

/-- Reciprocal floor shifts by two coordinates commute. -/
theorem div_div_comm (Y p q : ℕ) :
    (Y / p) / q = (Y / q) / p := by
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm p q]

/-- Coupled fresh-prime Euler law. A fresh prime acts simultaneously on the
smooth cube and on every large-prime extension fibre:
G_(S union q)(Y) = G_S(Y) - G_S(floor(Y/q)).
No norm, prime-counting approximation, or endpoint estimate occurs. -/
theorem coupledLargePrimeEulerResidual_insert
    {U R Y q : ℕ} {S : Finset ℕ}
    (hq : q ∉ S) (hqPrime : q.Prime) :
    coupledLargePrimeEulerResidual U R Y (insert q S) =
      coupledLargePrimeEulerResidual U R Y S -
        coupledLargePrimeEulerResidual U R (Y / q) S := by
  unfold coupledLargePrimeEulerResidual
  rw [frozenPrimeUniverseMass_insert hq hqPrime]
  have hsum :
      (∑ p ∈ Finset.range (U + 1),
        if R < p ∧ p.Prime then
          frozenPrimeUniverseMass (insert q S) (Y / p)
        else 0) =
      (∑ p ∈ Finset.range (U + 1),
        if R < p ∧ p.Prime then
          frozenPrimeUniverseMass S (Y / p)
        else 0) -
      (∑ p ∈ Finset.range (U + 1),
        if R < p ∧ p.Prime then
          frozenPrimeUniverseMass S ((Y / q) / p)
        else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    by_cases hpLarge : R < p ∧ p.Prime
    · simp only [hpLarge, if_true]
      rw [frozenPrimeUniverseMass_insert hq hqPrime]
      rw [div_div_comm Y p q]
    · simp [hpLarge]
  rw [hsum]
  ring

/-- At X=30, processing 2 and then 3 in the coupled state is exactly the
iterated Euler finite difference, rather than a heuristic cancellation. -/
example :
    coupledLargePrimeEulerResidual 30 5 30 ({2, 3} : Finset ℕ) =
      coupledLargePrimeEulerResidual 30 5 30 ({2} : Finset ℕ) -
        coupledLargePrimeEulerResidual 30 5 10 ({2} : Finset ℕ) := by
  have h3 : 3 ∉ ({2} : Finset ℕ) := by norm_num
  simpa [Finset.insert_comm] using
    (coupledLargePrimeEulerResidual_insert
      (U := 30) (R := 5) (Y := 30) (q := 3)
      (S := ({2} : Finset ℕ)) h3 (by norm_num : Nat.Prime 3))

/-! ## Aggregate square-endpoint identification -/

/-- Sum of all post-root truncated Euler cubes at the square endpoint.  This is
the user's large-prime response after the entire low-prime Boolean cube has
been assembled before taking any norm. -/
def squareRootLargePrimeEulerCubeAggregate (R : ℕ) : ℂ :=
  ∑ p ∈ Finset.Ioc R (squareRootEndpoint R),
    if p.Prime then
      ((largePrimeEulerCubeAt
        (squareRootEndpoint R) 1 p (primesUpTo R) : ℤ) : ℂ)
    else 0

/-- Every post-root outer prime sees a completed low universe, so the aggregate
is exactly the familiar lower-scale Mertens transform. -/
theorem squareRootLargePrimeEulerCubeAggregate_eq_mertensTransform
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootLargePrimeEulerCubeAggregate R =
      ∑ p ∈ Finset.Ioc R (squareRootEndpoint R),
        if p.Prime then
          mertensSummatory (squareRootEndpoint R / p)
        else 0 := by
  unfold squareRootLargePrimeEulerCubeAggregate
  apply Finset.sum_congr rfl
  intro p hpI
  by_cases hp : p.Prime
  · simp only [hp, if_true]
    have hRp : R < p := (Finset.mem_Ioc.mp hpI).1
    have hcut :
        squareRootEndpoint R / p ≤ R := by
      exact Nat.le_of_lt
        (squareRootEndpoint_div_lt_root_of_postRoot (by omega) hRp)
    simpa using
      (largePrimeEulerCubeAt_cast_eq_mertens
        (X := squareRootEndpoint R) (R := R) (m := 1) (p := p) hcut)
  · simp [hp]

/-- The endpoint-truncated Euler-cube aggregate is not merely analogous to the
canonical post-root ledger: it is definitionally the same signed arithmetic
after the existing finite Fubini/reassembly. -/
theorem squareRootLargePrimeEulerCubeAggregate_eq_postRootDowncrossLedger
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootLargePrimeEulerCubeAggregate R =
      lowWheelCanonicalPostRootDowncrossLedger R := by
  rw [squareRootLargePrimeEulerCubeAggregate_eq_mertensTransform R hR,
    lowWheelCanonicalPostRootDowncrossLedger_eq_mertensTransform R hR]

/-- Hence the aggregate of endpoint-cut Euler cubes is exactly the repository's
original high-prime transport.  This closes the coordinate identification and
leaves only the quantitative signed-boundary estimate. -/
theorem squareRootLargePrimeEulerCubeAggregate_eq_transport
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootLargePrimeEulerCubeAggregate R =
      squareRootTransportCofactorFirst R := by
  rw [squareRootLargePrimeEulerCubeAggregate_eq_postRootDowncrossLedger R hR,
    lowWheelCanonicalPostRootDowncrossLedger_eq_transport R hR]

/-- **Exact smooth/large-prime cancellation in Euler-cube coordinates.**
At a completed square endpoint, the entire large-prime cube aggregate must be
subtracted from the complete low-prime smooth mass.  Their signed difference is
exactly the square-prefix Mertens value.  Thus neither side is required to be
root-scale separately; the RH-scale object is their assembled difference. -/
theorem squarePrefixMertens_eq_smooth_sub_largePrimeEulerCubeAggregate
    (R : ℕ) (hR : 2 ≤ R) :
    RHLean.Analysis.squarePrefixMertens (R - 1) =
      squareRootSmoothMass (R - 1) -
        squareRootLargePrimeEulerCubeAggregate R := by
  rw [squareRootLargePrimeEulerCubeAggregate_eq_transport R hR]
  rw [squarePrefixMertens_eq_squareRootSmooth_sub_transport]
  rw [squareRootTransportMass_pred_eq_cofactorFirst R (by omega)]

/-- The same identity directly at X_R = R^2-1. -/
theorem mertensSquareRootEndpoint_eq_smooth_sub_largePrimeEulerCubeAggregate
    (R : ℕ) (hR : 2 ≤ R) :
    mertensSummatory (squareRootEndpoint R) =
      squareRootSmoothMass (R - 1) -
        squareRootLargePrimeEulerCubeAggregate R := by
  have h :=
    squarePrefixMertens_eq_smooth_sub_largePrimeEulerCubeAggregate R hR
  unfold RHLean.Analysis.squarePrefixMertens
    RHLean.Analysis.squarePrefixEndpoint at h
  have hend :
      (R - 1 + 1) ^ 2 - 1 = squareRootEndpoint R := by
    unfold squareRootEndpoint
    rw [Nat.sub_add_cancel (by omega : 1 ≤ R)]
  rwa [hend] at h

end RHLean.Proof

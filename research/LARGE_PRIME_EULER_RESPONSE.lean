import Mathlib
import «research.BOUNDARY_SHADOW_MORSE»
import «research.REENTRY_TO_GO_SECOND_BOUNDARY»
import RHLean.Proof.PrimeCombVisualizationDynamics
import RHLean.Analysis.SquareRootMiddleSequentialCoherence
import RHLean.Proof.LowWheelCanonicalPrimeSplit
import RHLean.Arithmetic.PrimeCombFiniteDifferenceFreshPrime
import RHLean.Arithmetic.PrimeCombComplementSmoothInversion
import RHLean.Proof.PrimeWheelProperSubwheelDepthTwo

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

/-- Literal finite evolution at X=30.  The large-prime block starts at -6;
the fresh primes 2, 3, 5 add the exact displaced corrections +2, +1, 0, and
the fully processed coupled state is M(30) = -3. -/
example : coupledLargePrimeEulerResidual 30 5 30 (∅ : Finset ℕ) = -6 := by
  native_decide

example : coupledLargePrimeEulerResidual 30 5 30 ({2} : Finset ℕ) = -4 := by
  native_decide

example : coupledLargePrimeEulerResidual 30 5 30 ({2, 3} : Finset ℕ) = -3 := by
  native_decide

example :
    coupledLargePrimeEulerResidual 30 5 30 ({2, 3, 5} : Finset ℕ) = -3 := by
  native_decide

example : coupledLargePrimeEulerResidual 30 5 15 (∅ : Finset ℕ) = -2 := by
  native_decide

example : coupledLargePrimeEulerResidual 30 5 10 ({2} : Finset ℕ) = -1 := by
  native_decide

example :
    coupledLargePrimeEulerResidual 30 5 6 ({2, 3} : Finset ℕ) = 0 := by
  native_decide
/-! ## Exact energy polarization of one fresh-prime step -/

/-- Squaring one exact Euler update exposes the only genuinely quadratic term.
The parent energy and daughter energy are recursive; every departure from a
formal energy descent is the signed parent/daughter covariance. -/
theorem coupledLargePrimeEulerResidual_insert_sq
    (U R Y q : ℕ) (S : Finset ℕ)
    (hq : q ∉ S) (hprime : q.Prime) :
    (coupledLargePrimeEulerResidual U R Y (insert q S)) ^ 2 =
      (coupledLargePrimeEulerResidual U R Y S) ^ 2 +
        (coupledLargePrimeEulerResidual U R (Y / q) S) ^ 2 -
          2 * coupledLargePrimeEulerResidual U R Y S *
            coupledLargePrimeEulerResidual U R (Y / q) S := by
  rw [coupledLargePrimeEulerResidual_insert hq hprime]
  ring

/-- Equivalent decrement form: a fresh-prime step lowers energy exactly when
twice the signed parent/daughter covariance dominates the daughter energy.
This is the discrete boundary-shadow obstruction in one line. -/
theorem coupledLargePrimeEulerResidual_energy_sub_insert_eq_covariance
    (U R Y q : ℕ) (S : Finset ℕ)
    (hq : q ∉ S) (hprime : q.Prime) :
    (coupledLargePrimeEulerResidual U R Y S) ^ 2 -
        (coupledLargePrimeEulerResidual U R Y (insert q S)) ^ 2 =
      2 * coupledLargePrimeEulerResidual U R Y S *
          coupledLargePrimeEulerResidual U R (Y / q) S -
        (coupledLargePrimeEulerResidual U R (Y / q) S) ^ 2 := by
  rw [coupledLargePrimeEulerResidual_insert_sq U R Y q S hq hprime]
  ring

/-! ## Arbitrary finite-prime operator form -/

/-- The unprocessed coupled state.  It is the unit endpoint source minus the
large-prime extension count, including the cutoff-zero convention. -/
def coupledLargePrimeEulerSeed (U R : ℕ) : ℕ → ℤ :=
  fun Y => coupledLargePrimeEulerResidual U R Y ∅

/-- **All finite Euler bookkeeping in one identity.**
For any finite set of prime coordinates, the fully coupled smooth-minus-large
prime state is exactly the canonical Möbius finite-difference operator applied
to the unprocessed seed.  Thus the one-prime recurrence is not merely
iterable: its arbitrary finite iterate is already the repository's unordered
Euler operator. -/
theorem coupledLargePrimeEulerResidual_eq_finiteDifferenceOperator
    (U R : ℕ) (S : Finset ℕ)
    (hprime : ∀ q ∈ S, q.Prime) :
    (fun Y => coupledLargePrimeEulerResidual U R Y S) =
      RHLean.Arithmetic.finiteDifferenceOperator S
        (coupledLargePrimeEulerSeed U R) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      funext Y
      simp [coupledLargePrimeEulerSeed,
        RHLean.Arithmetic.finiteDifferenceOperator_empty]
  | @insert q S hq ih =>
      have hqPrime : q.Prime := hprime q (by simp)
      have hSPrime : ∀ r ∈ S, r.Prime := by
        intro r hr
        exact hprime r (Finset.mem_insert_of_mem hr)
      have ih' := ih hSPrime
      funext Y
      rw [coupledLargePrimeEulerResidual_insert hq hqPrime]
      rw [congrFun ih' Y, congrFun ih' (Y / q)]
      rw [RHLean.Arithmetic.finiteDifferenceOperator_insert
        S q hqPrime hq hSPrime (coupledLargePrimeEulerSeed U R)]
      simp only [Pi.sub_apply]
      rw [RHLean.Arithmetic.finiteDifferenceOperator_shift_comm]
      rfl

/-- Pointwise form of the arbitrary finite-prime operator identity. -/
theorem coupledLargePrimeEulerResidual_eq_finiteDifferenceOperator_apply
    (U R Y : ℕ) (S : Finset ℕ)
    (hprime : ∀ q ∈ S, q.Prime) :
    coupledLargePrimeEulerResidual U R Y S =
      RHLean.Arithmetic.finiteDifferenceOperator S
        (coupledLargePrimeEulerSeed U R) Y := by
  exact congrFun
    (coupledLargePrimeEulerResidual_eq_finiteDifferenceOperator U R S hprime) Y

/-- The X=30 calculation is therefore one evaluation of the unordered
three-prime Euler operator, not an order-specific coincidence. -/
example :
    RHLean.Arithmetic.finiteDifferenceOperator ({2, 3, 5} : Finset ℕ)
        (coupledLargePrimeEulerSeed 30 5) 30 = -3 := by
  rw [← coupledLargePrimeEulerResidual_eq_finiteDifferenceOperator_apply
    30 5 30 ({2, 3, 5} : Finset ℕ) (by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl <;> norm_num)]
  native_decide
/-- The coupled seed vanishes at cutoff zero, so the terminating
complement-smooth inversion applies without a boundary-at-zero correction. -/
theorem coupledLargePrimeEulerSeed_zero (U R : ℕ) :
    coupledLargePrimeEulerSeed U R 0 = 0 := by
  simp [coupledLargePrimeEulerSeed, coupledLargePrimeEulerResidual,
    frozenPrimeUniverseMass_eq_cutoffSum, primeFaceProduct]

/-- **Complement-smooth recovery for the coupled Euler state.**
After any already-processed prime set S, an arbitrary disjoint set T of
additional prime coordinates can be processed all at once. The old state is
then recovered exactly as the terminating sum of the fully processed
S union T state over T-smooth scale shifts. This is the arbitrary-prime
version of the offsetting mechanism: no chronology and no norm are used. -/
theorem coupledLargePrimeEulerResidual_eq_sum_complementSmooth
    (U R Y : ℕ) (S T : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime)
    (hT : ∀ q ∈ T, q.Prime)
    (hdisj : Disjoint S T) :
    coupledLargePrimeEulerResidual U R Y S =
      ∑ n ∈ RHLean.Arithmetic.primeSetSmoothIcc T Y,
        coupledLargePrimeEulerResidual U R (Y / n) (S ∪ T) := by
  rw [coupledLargePrimeEulerResidual_eq_finiteDifferenceOperator_apply
    U R Y S hS]
  rw [RHLean.Arithmetic.finiteDifferenceOperator_eq_sum_complementSmooth
    S T hS hT hdisj (coupledLargePrimeEulerSeed U R)
    (coupledLargePrimeEulerSeed_zero U R) Y]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [← coupledLargePrimeEulerResidual_eq_finiteDifferenceOperator_apply
    U R (Y / n) (S ∪ T)]
  intro q hq
  rcases Finset.mem_union.mp hq with hq | hq
  · exact hS q hq
  · exact hT q hq

/-- Starting from no processed coordinates, the seed is therefore recovered
from any finite prime wheel by summing the fully processed coupled state over
that wheel's smooth scale shifts. -/
theorem coupledLargePrimeEulerSeed_eq_sum_smooth
    (U R Y : ℕ) (T : Finset ℕ)
    (hT : ∀ q ∈ T, q.Prime) :
    coupledLargePrimeEulerSeed U R Y =
      ∑ n ∈ RHLean.Arithmetic.primeSetSmoothIcc T Y,
        coupledLargePrimeEulerResidual U R (Y / n) T := by
  simpa [coupledLargePrimeEulerSeed] using
    (coupledLargePrimeEulerResidual_eq_sum_complementSmooth
      U R Y ∅ T (by simp) hT (by simp : Disjoint (∅ : Finset ℕ) T))
/-! ## Exact recovery of ordinary Mertens below the square wall -/

/-- A frozen prime universe containing every prime through the numerical cutoff
is already the ordinary integer Mertens prefix. -/
theorem frozenPrimeUniverseMass_primesUpTo_eq_mertensSummatoryInt_of_le
    {X Y : ℕ} (hXY : X ≤ Y) :
    frozenPrimeUniverseMass (primesUpTo Y) X = mertensSummatoryInt X := by
  have hcast := frozenPrimeUniverseMass_primesUpTo_cast_eq_mertens hXY
  rw [← mertensSummatoryInt_cast X] at hcast
  exact_mod_cast hcast

/-- Below R^2, every prime p > R has reciprocal cutoff Y/p < R. Hence the
chronological moving p-column and the fixed-root p-column agree term by term.
This is the exact reason the coupled finite-difference state is ordinary
Mertens throughout the complete sub-square range, not just at X_R. -/
theorem coupledLargePrimeEulerResidual_primesUpTo_eq_mertensSummatoryInt
    {R Y : ℕ} (hR : 1 ≤ R) (hRY : R ≤ Y) (hYsq : Y < R ^ 2) :
    coupledLargePrimeEulerResidual Y R Y (primesUpTo R) =
      mertensSummatoryInt Y := by
  have hset :
      (Finset.range (Y + 1)).filter (fun p => R < p ∧ p.Prime) =
        frozenPrimeUniverseHighPrimeSet R Y := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range,
      mem_frozenPrimeUniverseHighPrimeSet]
    constructor
    · rintro ⟨hpY, hRp, hpPrime⟩
      exact ⟨hpPrime, hRp, by omega⟩
    · rintro ⟨hpPrime, hRp, hpY⟩
      exact ⟨by omega, hRp, hpPrime⟩
  have hsum :
      (∑ p ∈ Finset.range (Y + 1),
        if R < p ∧ p.Prime then
          frozenPrimeUniverseMass (primesUpTo R) (Y / p)
        else 0) =
      ∑ p ∈ frozenPrimeUniverseHighPrimeSet R Y,
        frozenPrimeUniverseMass (primesUpTo (p - 1)) (Y / p) := by
    rw [← Finset.sum_filter]
    rw [hset]
    apply Finset.sum_congr rfl
    intro p hp
    have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hp
    have hpPrime : p.Prime := hpData.1
    have hRp : R < p := hpData.2.1
    have hpPos : 0 < p := hpPrime.pos
    have hRpos : 0 < R := by omega
    have hRmul : R ^ 2 < R * p := by
      rw [pow_two]
      exact Nat.mul_lt_mul_of_pos_left hRp hRpos
    have hYpR : Y / p < R := by
      apply (Nat.div_lt_iff_lt_mul hpPos).2
      exact hYsq.trans hRmul
    have hroot :
        frozenPrimeUniverseMass (primesUpTo R) (Y / p) =
          mertensSummatoryInt (Y / p) :=
      frozenPrimeUniverseMass_primesUpTo_eq_mertensSummatoryInt_of_le
        (Nat.le_of_lt hYpR)
    have hpred :
        frozenPrimeUniverseMass (primesUpTo (p - 1)) (Y / p) =
          mertensSummatoryInt (Y / p) :=
      frozenPrimeUniverseMass_eq_mertensSummatoryInt_of_lt_owner
        hpPrime (hYpR.trans hRp)
    rw [hroot, hpred]
  have hchron :
      mertensSummatoryInt Y =
        frozenPrimeUniverseMass (primesUpTo R) Y -
          ∑ p ∈ frozenPrimeUniverseHighPrimeSet R Y,
            frozenPrimeUniverseMass (primesUpTo (p - 1)) (Y / p) :=
    mertensSummatoryInt_eq_properSubwheel_sub_highOwnerColumn Y R hRY
  unfold coupledLargePrimeEulerResidual
  rw [hsum]
  omega

/-- At the physical square endpoint this recovers M(X_R) directly from the
finite coupled Euler state, with no complex cast and no separate transport
notation. -/
theorem coupledLargePrimeEulerResidual_squareRootEndpoint_eq_mertensSummatoryInt
    {R : ℕ} (hR : 2 ≤ R) :
    coupledLargePrimeEulerResidual
        (squareRootEndpoint R) R (squareRootEndpoint R) (primesUpTo R) =
      mertensSummatoryInt (squareRootEndpoint R) := by
  apply coupledLargePrimeEulerResidual_primesUpTo_eq_mertensSummatoryInt
  · omega
  · unfold squareRootEndpoint
    have hRR : R + 1 ≤ R ^ 2 := by nlinarith
    omega
  · unfold squareRootEndpoint
    have hpos : 0 < R ^ 2 := by positivity
    omega

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

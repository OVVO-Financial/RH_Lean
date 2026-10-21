import «research.VF_919_EULER_PRIME_DENSITY_LEDGER_20261019»
import «research.SQUARE_BLOCK_EULER_ANCESTRY_COVARIANCE_20261017»

/-!
# Fixed VF square wheel: three arithmetic sources, six pair-covariance channels

For all integers x in [R^2,(R+1)^2), the actual low-prime wheel
{p prime | p <= R} is invariant. Each new integer is exactly ONE of:
  A: smooth with all prime factors <= R;
  H: composite with a unique highest prime > R;
  P: newly arriving prime > R, with genuine Mobius weight -1.

At every partial shell, not just at the right endpoint:
   S = A + H - Q,
   K = K_A + K_H + Q,
   C = C_AA + C_HH + C_PP + C_AH + C_AP + C_HP,
   S^2 = K + 2*C.

All definitions use true real Mobius coefficients. The six channels are
signed UNcentered pair sums; no statistical independence is postulated.
For each new event with weight a, delta C = a*S_before. Prime a=-1.

This module formalizes the exact ledger and the fixed-wheel status.
It does NOT prove a uniform exponent, signed response bound, or RH.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators
open RHLean.Arithmetic

namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- For two integer sites in one square block, the active wheel is equal. -/
theorem vf919EulerFixedWheel_constant_on_squareBlock
    {R x y : ℕ}
    (hx : x ∈ RHLean.Proof.canonicalSquareBlock R)
    (hy : y ∈ RHLean.Proof.canonicalSquareBlock R) :
    primesUpTo (Nat.sqrt x) = primesUpTo (Nat.sqrt y) := by
  rw [RHLean.Proof.squareBlock_fixed_sqrt hx,
    RHLean.Proof.squareBlock_fixed_sqrt hy]

/-- The fixed low wheel detects all composites in the original block. -/
theorem vf919EulerFixedWheel_prime_iff_survivor
    {R n : ℕ} (hR : 2 ≤ R)
    (hn : n ∈ RHLean.Proof.canonicalSquareBlock R) :
    n.Prime ↔ ∀ p ∈ primesUpTo R, ¬ p ∣ n :=
  RHLean.Proof.squareBlock_prime_iff_lowWheel hR hn

/-- Every prime dividing a smooth physical site is in the fixed wheel. -/
def vf919EulerFixedSmooth (R n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ≤ R

/-- A: signed composite sites generated entirely inside the fixed wheel. -/
def vf919EulerFixedSmoothWeight (R n : ℕ) : ℝ :=
  if n.Prime then 0
  else if vf919EulerFixedSmooth R n then realMoebiusStep n else 0

/-- H: signed high-prime COMPOSITE sites, not the arriving primes. -/
def vf919EulerFixedHighCompositeWeight (R n : ℕ) : ℝ :=
  if n.Prime then 0
  else if vf919EulerFixedSmooth R n then 0 else realMoebiusStep n

/-- Every source is counted exactly once, prime-only cofactor c=1 included. -/
theorem vf919EulerFixedWheel_site_partition (R n : ℕ) :
    realMoebiusStep n =
      vf919EulerFixedSmoothWeight R n +
        vf919EulerFixedHighCompositeWeight R n -
          vf919EulerPrimeIndicator n := by
  by_cases hp : n.Prime
  · simp [vf919EulerFixedSmoothWeight,
      vf919EulerFixedHighCompositeWeight, vf919EulerPrimeIndicator,
      hp, vf919EulerPrimeMobius n hp]
  · by_cases hs : vf919EulerFixedSmooth R n
    · simp [vf919EulerFixedSmoothWeight,
        vf919EulerFixedHighCompositeWeight, vf919EulerPrimeIndicator,
        hp, hs]
    · simp [vf919EulerFixedSmoothWeight,
        vf919EulerFixedHighCompositeWeight, vf919EulerPrimeIndicator,
        hp, hs]

/-- Squarefree diagonal does not mix the disjoint Euler source classes. -/
theorem vf919EulerFixedWheel_site_diagonal (R n : ℕ) :
    realMoebiusStep n ^ 2 =
      vf919EulerFixedSmoothWeight R n ^ 2 +
        vf919EulerFixedHighCompositeWeight R n ^ 2 +
          vf919EulerPrimeIndicator n := by
  by_cases hp : n.Prime
  · simp [vf919EulerFixedSmoothWeight,
      vf919EulerFixedHighCompositeWeight, vf919EulerPrimeIndicator,
      hp, vf919EulerPrimeMobius n hp]
  · by_cases hs : vf919EulerFixedSmooth R n
    · simp [vf919EulerFixedSmoothWeight,
        vf919EulerFixedHighCompositeWeight, vf919EulerPrimeIndicator,
        hp, hs]
    · simp [vf919EulerFixedSmoothWeight,
        vf919EulerFixedHighCompositeWeight, vf919EulerPrimeIndicator,
        hp, hs]

/-- Prefixes are half-open and can be stopped at ANY site in the block. -/
def vf919EulerFixedA (R X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (R ^ 2) X, vf919EulerFixedSmoothWeight R n

def vf919EulerFixedH (R X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (R ^ 2) X, vf919EulerFixedHighCompositeWeight R n

def vf919EulerFixedQ (R X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (R ^ 2) X, vf919EulerPrimeIndicator n

def vf919EulerFixedKA (R X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (R ^ 2) X, vf919EulerFixedSmoothWeight R n ^ 2

def vf919EulerFixedKH (R X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (R ^ 2) X, vf919EulerFixedHighCompositeWeight R n ^ 2

def vf919EulerFixedS (R X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (R ^ 2) X, realMoebiusStep n

def vf919EulerFixedK (R X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (R ^ 2) X, realMoebiusStep n ^ 2

theorem vf919EulerFixedWheel_prefix_signed (R X : ℕ) :
    vf919EulerFixedS R X =
      vf919EulerFixedA R X +
        vf919EulerFixedH R X - vf919EulerFixedQ R X := by
  unfold vf919EulerFixedS vf919EulerFixedA vf919EulerFixedH
    vf919EulerFixedQ
  calc
    (∑ n ∈ Finset.Ico (R ^ 2) X, realMoebiusStep n) =
        ∑ n ∈ Finset.Ico (R ^ 2) X,
          (vf919EulerFixedSmoothWeight R n +
            vf919EulerFixedHighCompositeWeight R n -
              vf919EulerPrimeIndicator n) := by
          apply Finset.sum_congr rfl
          intro n _
          exact vf919EulerFixedWheel_site_partition R n
    _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]

theorem vf919EulerFixedWheel_prefix_diagonal (R X : ℕ) :
    vf919EulerFixedK R X =
      vf919EulerFixedKA R X +
        vf919EulerFixedKH R X + vf919EulerFixedQ R X := by
  unfold vf919EulerFixedK vf919EulerFixedKA vf919EulerFixedKH
    vf919EulerFixedQ
  calc
    (∑ n ∈ Finset.Ico (R ^ 2) X, realMoebiusStep n ^ 2) =
        ∑ n ∈ Finset.Ico (R ^ 2) X,
          (vf919EulerFixedSmoothWeight R n ^ 2 +
            vf919EulerFixedHighCompositeWeight R n ^ 2 +
              vf919EulerPrimeIndicator n) := by
          apply Finset.sum_congr rfl
          intro n _
          exact vf919EulerFixedWheel_site_diagonal R n
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

/-- Six genuine signed source-pair channels: AA,HH,PP,AH,AP,HP. -/
def vf919EulerFixedSixCov (A H Q KA KH : ℝ) : ℝ :=
  (A ^ 2 - KA) / 2 + (H ^ 2 - KH) / 2 +
    (Q ^ 2 - Q) / 2 + A * H - A * Q - H * Q

/-- The complete signed Green--Kubo identity, without a closure hypothesis. -/
theorem vf919EulerFixedSixCov_identity
    (A H Q KA KH : ℝ) :
    (A + H - Q) ^ 2 =
      KA + KH + Q + 2 * vf919EulerFixedSixCov A H Q KA KH := by
  unfold vf919EulerFixedSixCov
  ring

/-- Every partial VF block retains its exact six-channel covariance. -/
theorem vf919EulerFixedWheel_prefix_covariance (R X : ℕ) :
    vf919EulerFixedS R X ^ 2 =
      vf919EulerFixedK R X +
        2 * vf919EulerFixedSixCov
          (vf919EulerFixedA R X) (vf919EulerFixedH R X)
          (vf919EulerFixedQ R X) (vf919EulerFixedKA R X)
          (vf919EulerFixedKH R X) := by
  rw [vf919EulerFixedWheel_prefix_signed,
      vf919EulerFixedWheel_prefix_diagonal]
  exact vf919EulerFixedSixCov_identity _ _ _ _ _

/-- Incoming prime of weight -1: positive prime-prime pair mass and
negative/positive cross response against the two existing populations. -/
theorem vf919EulerFixedSixCov_prime_arrival
    (A H Q KA KH : ℝ) :
    vf919EulerFixedSixCov A H (Q + 1) KA KH -
      vf919EulerFixedSixCov A H Q KA KH =
        -(A + H - Q) := by
  unfold vf919EulerFixedSixCov
  ring

/-- Incoming smooth site with genuine Möbius weight a (possibly zero). -/
theorem vf919EulerFixedSixCov_smooth_arrival
    (A H Q KA KH a : ℝ) :
    vf919EulerFixedSixCov (A + a) H Q (KA + a ^ 2) KH -
      vf919EulerFixedSixCov A H Q KA KH =
        a * (A + H - Q) := by
  unfold vf919EulerFixedSixCov
  ring

/-- Incoming high-prime composite with genuine Möbius weight a. -/
theorem vf919EulerFixedSixCov_highComposite_arrival
    (A H Q KA KH a : ℝ) :
    vf919EulerFixedSixCov A (H + a) Q KA (KH + a ^ 2) -
      vf919EulerFixedSixCov A H Q KA KH =
        a * (A + H - Q) := by
  unfold vf919EulerFixedSixCov
  ring

#print axioms vf919EulerFixedWheel_constant_on_squareBlock
#print axioms vf919EulerFixedWheel_prime_iff_survivor
#print axioms vf919EulerFixedWheel_site_partition
#print axioms vf919EulerFixedWheel_site_diagonal
#print axioms vf919EulerFixedWheel_prefix_signed
#print axioms vf919EulerFixedWheel_prefix_diagonal
#print axioms vf919EulerFixedSixCov_identity
#print axioms vf919EulerFixedWheel_prefix_covariance
#print axioms vf919EulerFixedSixCov_prime_arrival
#print axioms vf919EulerFixedSixCov_smooth_arrival
#print axioms vf919EulerFixedSixCov_highComposite_arrival

end RHLean.Analysis

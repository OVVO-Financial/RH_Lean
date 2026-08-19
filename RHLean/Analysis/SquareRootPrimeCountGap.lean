import Mathlib
import RHLean.Analysis.NativePNTSquarePrefixTransfer
import RHLean.Analysis.SquareRootTransportTopFibreNoGo

/-!
# Square-root middle versus inert prime-count gap

At the square endpoint `X_R = R^2 - 1`, the prime-first transport splits into

* middle primes `R < q <= X_R / 2`, whose reciprocal quotients lie in `[2,R)`;
* inert top primes `X_R / 2 < q <= X_R`, whose reciprocal quotient is exactly `1`.

The previous transport theorem shows that the top block is a same-sign block of
one unit per prime.  This file records the exact cardinality obstruction to a
one-for-one cancellation of that top block against the middle prime fibres.

Writing `pi(N) = Nat.primeCounting N`, the two fibre populations satisfy

`middle + pi(R) = pi(X_R / 2)`

and

`top + pi(X_R / 2) = pi(X_R)`.

Hence their signed count gap is exactly

`middle - top = 2*pi(X_R / 2) - pi(X_R) - pi(R)`.

This identity is unconditional.  The sign of the right-hand side is genuinely a
second-order prime-counting question: the repository's qualitative PNT
`pi(N) log N / N -> 1` does not determine it because the leading `X/log X`
terms cancel.  We therefore isolate the exact stronger input needed to force
non-offset rather than deriving it incorrectly from first-order PNT.
-/

noncomputable section

open Filter
open scoped Topology

namespace RHLean.Proof

open RHLean.Analysis

/-- Prime fibres strictly between the square-root cutoff and the inert top half. -/
def squareRootMiddleFibrePrimes (R : ℕ) : Finset ℕ :=
  (Finset.Ioc R (squareRootEndpoint R / 2)).filter Nat.Prime

/-- Prime cardinality of `(0,N]` is the ordinary prime-counting function. -/
private theorem primeCard_Ioc_zero_eq_primeCounting (N : ℕ) :
    ((Finset.Ioc 0 N).filter Nat.Prime).card = Nat.primeCounting N := by
  have hset :
      (Finset.Ioc 0 N).filter Nat.Prime = nativePrimeSet N := by
    unfold nativePrimeSet
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hp0, hpN⟩, hpPrime⟩
      exact ⟨⟨by omega, hpN⟩, hpPrime⟩
    · rintro ⟨⟨hp1, hpN⟩, hpPrime⟩
      exact ⟨⟨by omega, hpN⟩, hpPrime⟩
  rw [hset, nativePrimeSet_card_eq_primeCounting]

/-- Exact prime count in an interval `(a,b]`, written additively to avoid any
truncation issue from natural-number subtraction. -/
theorem primeCard_Ioc_add_primeCounting_eq
    {a b : ℕ} (hab : a ≤ b) :
    ((Finset.Ioc a b).filter Nat.Prime).card + Nat.primeCounting a =
      Nat.primeCounting b := by
  let lower : Finset ℕ := (Finset.Ioc 0 a).filter Nat.Prime
  let upper : Finset ℕ := (Finset.Ioc a b).filter Nat.Prime
  have hsplit :
      (Finset.Ioc 0 b).filter Nat.Prime = lower ∪ upper := by
    ext p
    simp only [lower, upper, Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hp0, hpb⟩, hpPrime⟩
      by_cases hpa : p ≤ a
      · exact Or.inl ⟨⟨hp0, hpa⟩, hpPrime⟩
      · exact Or.inr ⟨⟨lt_of_not_ge hpa, hpb⟩, hpPrime⟩
    · rintro (h | h)
      · exact ⟨⟨h.1.1, h.1.2.trans hab⟩, h.2⟩
      · exact ⟨⟨by omega, h.1.2⟩, h.2⟩
  have hdisj : Disjoint lower upper := by
    rw [Finset.disjoint_left]
    intro p hpLower hpUpper
    rcases Finset.mem_filter.mp hpLower with ⟨hpLowerIoc, _⟩
    rcases Finset.mem_filter.mp hpUpper with ⟨hpUpperIoc, _⟩
    rcases Finset.mem_Ioc.mp hpLowerIoc with ⟨_, hpa⟩
    rcases Finset.mem_Ioc.mp hpUpperIoc with ⟨hap, _⟩
    omega
  have hcard := congrArg Finset.card hsplit
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  have hlower : lower.card = Nat.primeCounting a := by
    dsimp [lower]
    exact primeCard_Ioc_zero_eq_primeCounting a
  have htotal : ((Finset.Ioc 0 b).filter Nat.Prime).card = Nat.primeCounting b :=
    primeCard_Ioc_zero_eq_primeCounting b
  dsimp [upper] at hcard ⊢
  rw [htotal, hlower] at hcard
  omega

/-- For `R >= 3`, the middle prime population plus the primes through `R`
is exactly `pi(X_R/2)`. -/
theorem squareRootMiddleFibrePrimes_card_add_primeCounting_root
    (R : ℕ) (hR : 3 ≤ R) :
    (squareRootMiddleFibrePrimes R).card + Nat.primeCounting R =
      Nat.primeCounting (squareRootEndpoint R / 2) := by
  have hpow : R ^ 2 = R * R := by ring
  have hge : 3 * R ≤ R * R := Nat.mul_le_mul hR (le_refl R)
  have hmul : R * 2 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    omega
  have hhalf : R ≤ squareRootEndpoint R / 2 :=
    (Nat.le_div_iff_mul_le (by norm_num)).2 hmul
  unfold squareRootMiddleFibrePrimes
  exact primeCard_Ioc_add_primeCounting_eq hhalf

/-- The inert top-prime population plus the primes through the half endpoint is
exactly `pi(X_R)`. -/
theorem squareRootTopFibrePrimes_card_add_primeCounting_half
    (R : ℕ) :
    (squareRootTopFibrePrimes R).card +
        Nat.primeCounting (squareRootEndpoint R / 2) =
      Nat.primeCounting (squareRootEndpoint R) := by
  have hhalfX : squareRootEndpoint R / 2 ≤ squareRootEndpoint R :=
    Nat.div_le_self _ _
  unfold squareRootTopFibrePrimes
  exact primeCard_Ioc_add_primeCounting_eq hhalfX

/-- Integer-valued middle-minus-top prime-count gap.  The integer presentation
keeps the signed difference exact. -/
def squareRootMiddleTopPrimeCountGap (R : ℕ) : ℤ :=
  2 * (Nat.primeCounting (squareRootEndpoint R / 2) : ℤ) -
    (Nat.primeCounting (squareRootEndpoint R) : ℤ) -
    (Nat.primeCounting R : ℤ)

/-- The PNT-coordinate expression is exactly the geometric fibre-cardinality
difference. -/
theorem squareRootMiddleTopPrimeCountGap_eq_card_sub
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootMiddleTopPrimeCountGap R =
      ((squareRootMiddleFibrePrimes R).card : ℤ) -
        ((squareRootTopFibrePrimes R).card : ℤ) := by
  have hmid := squareRootMiddleFibrePrimes_card_add_primeCounting_root R hR
  have htop := squareRootTopFibrePrimes_card_add_primeCounting_half R
  have hmidZ :
      ((squareRootMiddleFibrePrimes R).card : ℤ) +
          (Nat.primeCounting R : ℤ) =
        (Nat.primeCounting (squareRootEndpoint R / 2) : ℤ) := by
    exact_mod_cast hmid
  have htopZ :
      ((squareRootTopFibrePrimes R).card : ℤ) +
          (Nat.primeCounting (squareRootEndpoint R / 2) : ℤ) =
        (Nat.primeCounting (squareRootEndpoint R) : ℤ) := by
    exact_mod_cast htop
  unfold squareRootMiddleTopPrimeCountGap
  omega

/-- The two geometric prime layers fail to offset one-for-one exactly when the
second-order prime-counting gap is positive. -/
theorem squareRoot_top_card_lt_middle_iff_secondOrder_primeCounting_gap
    (R : ℕ) (hR : 3 ≤ R) :
    (squareRootTopFibrePrimes R).card <
        (squareRootMiddleFibrePrimes R).card ↔
      Nat.primeCounting (squareRootEndpoint R) + Nat.primeCounting R <
        2 * Nat.primeCounting (squareRootEndpoint R / 2) := by
  have hmid := squareRootMiddleFibrePrimes_card_add_primeCounting_root R hR
  have htop := squareRootTopFibrePrimes_card_add_primeCounting_half R
  omega

/-- The quantitative prime-counting input needed after first-order PNT.  It is
kept as a named proposition because `pi(N) log N / N -> 1` alone cannot decide
this second-order sign after the leading terms cancel. -/
def SquareRootSecondOrderPrimeCountGapStatement : Prop :=
  ∀ᶠ R : ℕ in atTop,
    Nat.primeCounting (squareRootEndpoint R) + Nat.primeCounting R <
      2 * Nat.primeCounting (squareRootEndpoint R / 2)

/-- Any proof of the second-order prime-counting gap immediately yields the
structural non-offset theorem for the square-root transport populations. -/
theorem squareRoot_middle_prime_population_eventually_exceeds_top
    (hgap : SquareRootSecondOrderPrimeCountGapStatement) :
    ∀ᶠ R : ℕ in atTop,
      (squareRootTopFibrePrimes R).card <
        (squareRootMiddleFibrePrimes R).card := by
  filter_upwards [hgap, eventually_ge_atTop 3] with R hpi hR
  exact
    (squareRoot_top_card_lt_middle_iff_secondOrder_primeCounting_gap R hR).2 hpi

/-! ## Weighted middle bias target -/

/-- The middle Mertens tail viewed in the sequential fresh-prime orientation.
Each fresh-prime extension reverses the parent sign, so the oriented throw mass
is the negative of the transport-convention middle tail. -/
def squareRootOrientedMiddleThrowMass (R : ℕ) : ℂ :=
  -squareRootMiddleMertensTail R

/-- The defect of the actual oriented middle throws from the unit model in
which every middle prime fibre contributes `+1`.

If `A_R` denotes the oriented throw mass and `N_mid` the number of middle prime
fibres, this is exactly `N_mid - A_R`. -/
def squareRootMiddleUnitModelDefect (R : ℕ) : ℂ :=
  ((squareRootMiddleFibrePrimes R).card : ℂ) -
    squareRootOrientedMiddleThrowMass R

/-- Complex-valued geometric presentation of the middle-minus-top population
gap.  This is the bias term that the weighted middle throws must absorb; it is
not itself a saving. -/
def squareRootMiddleTopPrimeCountGapMass (R : ℕ) : ℂ :=
  ((squareRootMiddleFibrePrimes R).card : ℂ) -
    ((squareRootTopFibrePrimes R).card : ℂ)

/-- The integer PNT-coordinate gap and the complex geometric gap are the same
quantity after casting. -/
theorem squareRootMiddleTopPrimeCountGap_cast_eq_mass
    (R : ℕ) (hR : 3 ≤ R) :
    ((squareRootMiddleTopPrimeCountGap R : ℤ) : ℂ) =
      squareRootMiddleTopPrimeCountGapMass R := by
  rw [squareRootMiddleTopPrimeCountGap_eq_card_sub R hR]
  unfold squareRootMiddleTopPrimeCountGapMass
  push_cast

/-- **Exact weighted middle-bias identity.**  The deficit of the oriented
middle throws from the unit model is the population gap plus the smooth edge,
up to exactly the square-endpoint Mertens residual:

`N_mid - A_R = G_R + S_R - M(X_R)`.

Thus the positive prime-count gap is a deterministic bias that must be absorbed
by the lower-scale Mertens weights; it is not a contraction term. -/
theorem squareRootMiddleUnitModelDefect_eq_gap_add_smooth_sub_mertens
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootMiddleUnitModelDefect R =
      squareRootMiddleTopPrimeCountGapMass R +
        squareRootSmoothMass (R - 1) - squarePrefixMertens (R - 1) := by
  rw [squarePrefixMertens_eq_smooth_sub_middle_sub_topCard R hR]
  unfold squareRootMiddleUnitModelDefect squareRootOrientedMiddleThrowMass
    squareRootMiddleTopPrimeCountGapMass
  ring

/-- The same identity with the population bias written directly in the exact
integer PNT coordinate from the preceding section. -/
theorem squareRootMiddleUnitModelDefect_eq_primeCountGap_add_smooth_sub_mertens
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootMiddleUnitModelDefect R =
      ((squareRootMiddleTopPrimeCountGap R : ℤ) : ℂ) +
        squareRootSmoothMass (R - 1) - squarePrefixMertens (R - 1) := by
  rw [squareRootMiddleTopPrimeCountGap_cast_eq_mass R hR]
  exact squareRootMiddleUnitModelDefect_eq_gap_add_smooth_sub_mertens R hR

/-- After removing the deterministic prime-population gap and smooth-edge
correction from the unit-model defect, the remaining weighted-middle bias is
the exact Mertens target.  No division by the middle population is needed. -/
def squareRootMiddleBiasResidual (R : ℕ) : ℂ :=
  squareRootMiddleUnitModelDefect R -
    (squareRootMiddleTopPrimeCountGapMass R + squareRootSmoothMass (R - 1))

/-- **Cross-multiplied average target.**  The centered weighted-middle bias is
exactly the negative square-prefix Mertens value. -/
theorem squareRootMiddleBiasResidual_eq_neg_mertens
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootMiddleBiasResidual R = -squarePrefixMertens (R - 1) := by
  unfold squareRootMiddleBiasResidual
  rw [squareRootMiddleUnitModelDefect_eq_gap_add_smooth_sub_mertens R hR]
  ring

/-- Norm form: controlling the weighted-middle bias after subtracting the PNT
population tilt and smooth correction is exactly equivalent, with no loss, to
controlling Mertens at the square endpoint. -/
theorem norm_squareRootMiddleBiasResidual_eq_mertens
    (R : ℕ) (hR : 3 ≤ R) :
    ‖squareRootMiddleBiasResidual R‖ = ‖squarePrefixMertens (R - 1)‖ := by
  rw [squareRootMiddleBiasResidual_eq_neg_mertens R hR]
  simp

end RHLean.Proof

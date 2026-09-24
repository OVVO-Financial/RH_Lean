import Mathlib
import RHLean.Analysis.NativePNTMertens
import RHLean.Analysis.NativePNTQuantitativeStatements
import RHLean.Analysis.SquareRootPositiveSmoothCollapse
import RHLean.Proof.MatchedFarSurvivorBridge
import RHLean.Proof.SquareRootAncestryRoot

/-!
# Möbius inversion is the global cross-prime cancellation

Finite experiments showed that the far-upper survivor column cancels against
born-smooth only after essentially the whole prime/scale range is summed; no
additive, multiplicative, shifted or reversed block of reciprocal cutoffs sees
it.  This module identifies the mechanism exactly.  It is the summatory form
of `mu * 1 = delta`:

  sum_{d <= X} M(floor(X/d)) = 1.

At `X = R^2 - 1` split `d` into `d = 1`, primes `p < R+8`, primes `p >= R+8`
and composites.  The far primes are exactly the negative far-upper survivor.
Composing with the compiled square-prefix decomposition gives

  bornSmooth + farSurvivor = M(R^2 - 1) + E_root,
  E_root = nearTransport - positiveSmooth
         = nearTransport + sum_{q <= R prime} M(q - 1),

and equivalently

  bornSmooth = 1 - compositeColumn - lowPrimeColumn + E_root.

Every argument of a Mertens value inside `E_root` is below `R`.  No estimate
is asserted.  The cancellation mechanism is exact, and its residual is the
top Mertens value `M(R^2 - 1)` itself.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis

/-- **Universal integer form.** `sum_{d <= X} sum_{m <= X/d} mu(m) = 1`. -/
theorem sum_moebius_prefix_floor_div_eq_one (X : ℕ) (hX : 1 ≤ X) :
    ∑ d ∈ Finset.Icc 1 X, ∑ m ∈ Finset.Icc 1 (X / d),
        (ArithmeticFunction.moebius m : ℤ) = 1 := by
  have hswap : ∀ d m : ℕ,
      d ∈ Finset.Icc 1 X ∧ m ∈ Finset.Icc 1 (X / d) ↔
        d ∈ Finset.Icc 1 (X / m) ∧ m ∈ Finset.Icc 1 X := by
    intro d m
    simp only [Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hd1, _hdX⟩, hm1, hmX⟩
      have hmd : m * d ≤ X := (Nat.le_div_iff_mul_le (by omega)).mp hmX
      refine ⟨⟨hd1, (Nat.le_div_iff_mul_le (by omega)).mpr ?_⟩, hm1,
        le_trans hmX (Nat.div_le_self _ _)⟩
      rw [Nat.mul_comm]
      exact hmd
    · rintro ⟨⟨hd1, hdX⟩, hm1, _hmX⟩
      have hdm : d * m ≤ X := (Nat.le_div_iff_mul_le (by omega)).mp hdX
      refine ⟨⟨hd1, le_trans hdX (Nat.div_le_self _ _)⟩, hm1,
        (Nat.le_div_iff_mul_le (by omega)).mpr ?_⟩
      rw [Nat.mul_comm]
      exact hdm
  rw [Finset.sum_comm' hswap]
  calc
    ∑ m ∈ Finset.Icc 1 X, ∑ _d ∈ Finset.Icc 1 (X / m),
        (ArithmeticFunction.moebius m : ℤ) =
      ∑ m ∈ Finset.Icc 1 X,
        (ArithmeticFunction.moebius m : ℤ) * ((X / m : ℕ) : ℤ) := by
      apply Finset.sum_congr rfl
      intro m _hm
      rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring
    _ = 1 := nativeSumMoebiusMulFloor X hX

/-- **Möbius inversion in the repository's Mertens coordinate.** -/
theorem sum_mertensSummatory_floor_div_eq_one (X : ℕ) (hX : 1 ≤ X) :
    ∑ d ∈ Finset.Icc 1 X, mertensSummatory (X / d) = 1 := by
  have h := sum_moebius_prefix_floor_div_eq_one X hX
  have hnat :
      ∑ d ∈ Finset.Icc 1 X, nativeMertensSummatory (X / d) = 1 := by
    unfold nativeMertensSummatory
    exact_mod_cast h
  simp_rw [mertensSummatory_eq_complex_nativeMertensSummatory]
  exact_mod_cast hnat

/-- Prime divisors below the far-upper cutoff, at the square endpoint. -/
def mobiusInversionLowPrimeColumn (R : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 (squareRootEndpoint R),
    if d.Prime ∧ d < R + 8 then
      mertensSummatory (squareRootEndpoint R / d) else 0

/-- Composite divisors, at the square endpoint. -/
def mobiusInversionCompositeColumn (R : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 (squareRootEndpoint R),
    if d ≠ 1 ∧ ¬ d.Prime then
      mertensSummatory (squareRootEndpoint R / d) else 0

/-- The explicit lower-scale strip left by the square-prefix decomposition.
Every Mertens argument in it is below `R`. -/
def mobiusInversionRootStrip (R : ℕ) : ℂ :=
  squareRootNearPrimeTransport R + squareRootPositiveSmoothPrimeMertensTransform R

private theorem fourWay_split (R d : ℕ) (f : ℂ) :
    f = (if d = 1 then f else 0) +
      (if d.Prime ∧ d < R + 8 then f else 0) +
      (if d.Prime ∧ R + 8 ≤ d then f else 0) +
      (if d ≠ 1 ∧ ¬ d.Prime then f else 0) := by
  by_cases h1 : d = 1
  · subst h1
    simp [Nat.not_prime_one]
  · by_cases hp : d.Prime
    · by_cases hlt : d < R + 8
      · have hnot : ¬ R + 8 ≤ d := by omega
        simp [h1, hp, hlt, hnot]
      · have hge : R + 8 ≤ d := by omega
        simp [h1, hp, hlt, hge]
    · simp [h1, hp]

private theorem farPrimeColumn_eq_farTransport (R : ℕ) (hR : 56 ≤ R) :
    (∑ d ∈ Finset.Icc 1 (squareRootEndpoint R),
        if d.Prime ∧ R + 8 ≤ d then
          mertensSummatory (squareRootEndpoint R / d) else 0) =
      squareRootFarPrimeTransport R := by
  unfold squareRootFarPrimeTransport
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_hd1, hdX⟩, hp, hR8⟩
    exact ⟨⟨hR8, hdX⟩, hp⟩
  · rintro ⟨⟨hR8, hdX⟩, hp⟩
    exact ⟨⟨by omega, hdX⟩, hp, hR8⟩

/-- **Square-endpoint Möbius inversion, four columns.** -/
theorem mertens_add_lowPrime_add_farTransport_add_composite_eq_one
    (R : ℕ) (hR : 56 ≤ R) :
    mertensSummatory (squareRootEndpoint R) +
        mobiusInversionLowPrimeColumn R +
        squareRootFarPrimeTransport R +
        mobiusInversionCompositeColumn R = 1 := by
  have hX : 1 ≤ squareRootEndpoint R := by
    have hsquare : 2 ^ 2 ≤ R ^ 2 :=
      Nat.pow_le_pow_left (by omega : 2 ≤ R) 2
    unfold squareRootEndpoint
    omega
  have htotal := sum_mertensSummatory_floor_div_eq_one
    (squareRootEndpoint R) hX
  rw [Finset.sum_congr rfl (fun d _ => fourWay_split R d
      (mertensSummatory (squareRootEndpoint R / d)))] at htotal
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib] at htotal
  have hone :
      (∑ d ∈ Finset.Icc 1 (squareRootEndpoint R),
          if d = 1 then mertensSummatory (squareRootEndpoint R / d) else 0) =
        mertensSummatory (squareRootEndpoint R) := by
    rw [Finset.sum_ite_eq']
    simp [Finset.mem_Icc, hX]
  rw [hone, farPrimeColumn_eq_farTransport R hR] at htotal
  unfold mobiusInversionLowPrimeColumn mobiusInversionCompositeColumn
  exact htotal

/-- **Born-smooth plus far survivor is the top Mertens value plus the explicit
lower-scale strip.** -/
theorem bornSmooth_add_farSurvivor_eq_mertens_add_rootStrip
    (R : ℕ) (hR : 56 ≤ R) :
    squareRootBornSmoothMass R + survivorSixteenFarUpperPrimeMass (R - 1) =
      mertensSummatory (squareRootEndpoint R) + mobiusInversionRootStrip R := by
  have h1 := squarePrefixMertens_eq_positiveSmooth_add_matched R (by omega)
  have h2 :=
    squareRootMatchedBornSmoothTransport_eq_bornSmooth_add_farSurvivor_sub_near
      R hR
  have hpos := squareRootPositiveSmoothMass_eq_neg_primeMertensTransform R
    (by omega)
  have hend :
      squarePrefixMertens (R - 1) = mertensSummatory (squareRootEndpoint R) := by
    unfold squarePrefixMertens
    rw [squarePrefixEndpoint_pred_eq_squareRootEndpoint R (by omega)]
  unfold mobiusInversionRootStrip
  linear_combination hend - h1 - h2 - hpos

/-- **Autopsy form.** Born-smooth is exactly one minus the composite and
low-prime Möbius-inversion columns, plus the lower-scale strip. -/
theorem bornSmooth_eq_one_sub_composite_sub_lowPrime_add_rootStrip
    (R : ℕ) (hR : 56 ≤ R) :
    squareRootBornSmoothMass R =
      1 - mobiusInversionCompositeColumn R - mobiusInversionLowPrimeColumn R +
        mobiusInversionRootStrip R := by
  have hmain := bornSmooth_add_farSurvivor_eq_mertens_add_rootStrip R hR
  have hfar := survivorSixteenFarUpperPrimeMass_pred_eq_neg_farTransport R hR
  have hinv := mertens_add_lowPrime_add_farTransport_add_composite_eq_one R hR
  linear_combination hmain - hfar + hinv

end RHLean.Proof

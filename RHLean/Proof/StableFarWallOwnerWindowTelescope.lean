import RHLean.Proof.StableFarWallCrossingOwnerWindow
import RHLean.Proof.PrimeWheelProperSubwheelDepthTwo

/-!
# Stable-far owner-window Euler telescope

The exact crossing-owner window already has the solved reciprocal-depth form

  max(r, sqrt T) < q <= min(R-1,T),

where `T = floor(X_R / (r*e*p))`.  On an actual stable-far descended child the
far prime satisfies `p > R`, hence `T < R`; the artificial root cap therefore
disappears.  The owner window is literally

  max(r, sqrt T) < q <= T.

At this cutoff the cubic proper-subwheel hypothesis is automatic.  Applying the
production moving-boundary theorem at `X=K=T` converts the entire first-power
Euler owner window, before any norm, into the ordinary lower Mertens endpoint
`M(T)` plus literal square daughters `M(T/q^2)`.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- On every descended stable-far child the reciprocal owner depth is strictly
below the physical root.  The far-prime coordinate alone supplies the strict
scale drop. -/
theorem lowWheelFarPrimeQ2CrossingOwnerDepth_lt_root
    {R : ℕ} {y : ℕ × (ℕ × ℕ)}
    (hy : y ∈ lowWheelFarPrimeQ2DescendedTriples R) :
    lowWheelFarPrimeQ2CrossingOwnerDepth R y < R := by
  have hyBase : y ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp hy).1
  rcases lowWheelFarPrimeLowCofactorTriple_data hyBase with
    ⟨hrPrime, hrR, he1, hpPrime, hpR, _heSq, _her, _hyCut⟩
  let A : ℕ := y.1 * y.2.1 * y.2.2
  have hApos : 0 < A := by
    dsimp [A]
    exact Nat.mul_pos (Nat.mul_pos hrPrime.pos (by omega)) hpPrime.pos
  unfold lowWheelFarPrimeQ2CrossingOwnerDepth
  apply (Nat.div_lt_iff_lt_mul hApos).2
  have hRpos : 0 < R := hrPrime.pos.trans hrR
  have hXlt : squareRootEndpoint R < R * R := by
    unfold squareRootEndpoint
    have hne : R ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.ne_of_gt hRpos)
    simpa [pow_two] using Nat.pred_lt hne
  have hre : 1 ≤ y.1 * y.2.1 := by
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero hrPrime.ne_zero (by omega))
  have hpLeA : y.2.2 ≤ A := by
    dsimp [A]
    have h := Nat.mul_le_mul_right y.2.2 hre
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  have hRA : R < A := by
    have hRp : R < y.2.2 := by omega
    exact hRp.trans_le hpLeA
  have hRRlt : R * R < R * A :=
    Nat.mul_lt_mul_of_pos_left hRA hRpos
  exact hXlt.trans hRRlt

/-- Consequently the nominal `R-1` cap in the solved owner window is inactive. -/
theorem lowWheelFarPrimeQ2CrossingOwnerUpper_eq_depth
    {R : ℕ} {y : ℕ × (ℕ × ℕ)}
    (hy : y ∈ lowWheelFarPrimeQ2DescendedTriples R) :
    lowWheelFarPrimeQ2CrossingOwnerUpper R y =
      lowWheelFarPrimeQ2CrossingOwnerDepth R y := by
  unfold lowWheelFarPrimeQ2CrossingOwnerUpper
  have hlt := lowWheelFarPrimeQ2CrossingOwnerDepth_lt_root hy
  have hle : lowWheelFarPrimeQ2CrossingOwnerDepth R y ≤ R - 1 :=
    Nat.le_pred_of_lt hlt
  exact min_eq_right hle

/-- The child's own returned owner and the square-root threshold both lie below
its reciprocal depth. -/
theorem lowWheelFarPrimeQ2CrossingOwnerLower_le_depth
    {R : ℕ} {y : ℕ × (ℕ × ℕ)}
    (hy : y ∈ lowWheelFarPrimeQ2DescendedTriples R) :
    lowWheelFarPrimeQ2CrossingOwnerLower R y ≤
      lowWheelFarPrimeQ2CrossingOwnerDepth R y := by
  have hyBase : y ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp hy).1
  rcases lowWheelFarPrimeLowCofactorTriple_data hyBase with
    ⟨hrPrime, _hrR, he1, hpPrime, _hpR, _heSq, _her, _hyCut⟩
  have hdesc := (Finset.mem_filter.mp hy).2
  let A : ℕ := y.1 * y.2.1 * y.2.2
  have hApos : 0 < A := by
    dsimp [A]
    exact Nat.mul_pos (Nat.mul_pos hrPrime.pos (by omega)) hpPrime.pos
  have hrDepth : y.1 ≤ lowWheelFarPrimeQ2CrossingOwnerDepth R y := by
    unfold lowWheelFarPrimeQ2CrossingOwnerDepth
    apply (Nat.le_div_iff_mul_le hApos).2
    simpa [A, Nat.mul_assoc] using hdesc
  have hsqrtDepth :
      Nat.sqrt (lowWheelFarPrimeQ2CrossingOwnerDepth R y) ≤
        lowWheelFarPrimeQ2CrossingOwnerDepth R y :=
    Nat.sqrt_le_self _
  unfold lowWheelFarPrimeQ2CrossingOwnerLower
  exact max_le hrDepth hsqrtDepth

/-- **Canonical stable-far owner interval.**  The actual old owners returning to
one descended child are exactly the primes in `(max(r,sqrt T), T]`; no root cap
remains. -/
theorem lowWheelFarPrimeQ2CrossingOuterOwnerSet_eq_depthPrimeInterval
    {R : ℕ} {y : ℕ × (ℕ × ℕ)}
    (hy : y ∈ lowWheelFarPrimeQ2DescendedTriples R) :
    lowWheelFarPrimeQ2CrossingOuterOwnerSet R y =
      (Finset.Ioc (lowWheelFarPrimeQ2CrossingOwnerLower R y)
        (lowWheelFarPrimeQ2CrossingOwnerDepth R y)).filter Nat.Prime := by
  rw [lowWheelFarPrimeQ2CrossingOuterOwnerSet_eq_primeInterval hy,
    lowWheelFarPrimeQ2CrossingOwnerUpper_eq_depth hy]

/-- The renewal multiplicity is the prime count on that uncapped reciprocal
owner interval. -/
theorem lowWheelFarPrimeQ2CrossingNextMultiplicity_eq_depthPrimeInterval_card
    {R : ℕ} {y : ℕ × (ℕ × ℕ)}
    (hy : y ∈ lowWheelFarPrimeQ2DescendedTriples R) :
    lowWheelFarPrimeQ2CrossingNextMultiplicity R y =
      ((Finset.Ioc (lowWheelFarPrimeQ2CrossingOwnerLower R y)
        (lowWheelFarPrimeQ2CrossingOwnerDepth R y)).filter Nat.Prime).card := by
  rw [lowWheelFarPrimeQ2CrossingNextMultiplicity_eq_ownerSet_card hy,
    lowWheelFarPrimeQ2CrossingOuterOwnerSet_eq_depthPrimeInterval hy]

/-- The square-root lower endpoint forces the cubic proper-subwheel condition at
one reciprocal depth. -/
private theorem crossingOwnerDepth_lt_lowerSuccCube
    (R : ℕ) (y : ℕ × (ℕ × ℕ)) :
    lowWheelFarPrimeQ2CrossingOwnerDepth R y <
      (lowWheelFarPrimeQ2CrossingOwnerLower R y + 1) ^ 3 := by
  let T := lowWheelFarPrimeQ2CrossingOwnerDepth R y
  let Y := lowWheelFarPrimeQ2CrossingOwnerLower R y
  have hroot : Nat.sqrt T ≤ Y := by
    dsimp [Y, T, lowWheelFarPrimeQ2CrossingOwnerLower]
    exact le_max_right _ _
  have hsucc : Nat.sqrt T + 1 ≤ Y + 1 := Nat.add_le_add_right hroot 1
  have hT : T < (Nat.sqrt T + 1) ^ 2 := Nat.lt_succ_sqrt' T
  have hsq : (Nat.sqrt T + 1) ^ 2 ≤ (Y + 1) ^ 2 :=
    Nat.pow_le_pow_left hsucc 2
  have hone : 1 ≤ Y + 1 := Nat.succ_le_succ (Nat.zero_le Y)
  have hcube : (Y + 1) ^ 2 ≤ (Y + 1) ^ 3 := by
    calc
      (Y + 1) ^ 2 = 1 * (Y + 1) ^ 2 := by simp
      _ ≤ (Y + 1) * (Y + 1) ^ 2 :=
        Nat.mul_le_mul_right ((Y + 1) ^ 2) hone
      _ = (Y + 1) ^ 3 := by ring
  dsimp [T, Y] at hT hsq hcube ⊢
  exact hT.trans_le (hsq.trans hcube)

/-- **Stable-far Euler updates telescope before squaring.**  For every actual
descended child, advance the frozen base through its entire solved old-owner
window and subtract the matching moving boundary at the same time.  The whole
first-power owner chronology disappears exactly.  What remains is the ordinary
lower Mertens endpoint at reciprocal depth `T` plus the literal square-daughter
column `M(T/q^2)` on the same owner interval.

No norm, triangle inequality, PNT estimate, or RH-scale hypothesis is used. -/
theorem lowWheelFarPrimeQ2CrossingOwnerWindow_telescope
    {R : ℕ} {y : ℕ × (ℕ × ℕ)}
    (hy : y ∈ lowWheelFarPrimeQ2DescendedTriples R) :
    frozenPrimeUniverseMass
          (primesUpTo (lowWheelFarPrimeQ2CrossingOwnerLower R y))
          (lowWheelFarPrimeQ2CrossingOwnerDepth R y) -
        (∑ q ∈ frozenPrimeUniverseHighPrimeSet
            (lowWheelFarPrimeQ2CrossingOwnerLower R y)
            (lowWheelFarPrimeQ2CrossingOwnerDepth R y),
          frozenPrimeUniverseMass (primesUpTo q)
            (lowWheelFarPrimeQ2CrossingOwnerDepth R y / q)) =
      mertensSummatoryInt (lowWheelFarPrimeQ2CrossingOwnerDepth R y) +
        ∑ q ∈ frozenPrimeUniverseHighPrimeSet
            (lowWheelFarPrimeQ2CrossingOwnerLower R y)
            (lowWheelFarPrimeQ2CrossingOwnerDepth R y),
          mertensSummatoryInt
            (lowWheelFarPrimeQ2CrossingOwnerDepth R y / (q * q)) := by
  let T := lowWheelFarPrimeQ2CrossingOwnerDepth R y
  let Y := lowWheelFarPrimeQ2CrossingOwnerLower R y
  have hYT : Y ≤ T := by
    dsimp [Y, T]
    exact lowWheelFarPrimeQ2CrossingOwnerLower_le_depth hy
  have hcubic : T < (Y + 1) ^ 3 := by
    dsimp [Y, T]
    exact crossingOwnerDepth_lt_lowerSuccCube R y
  have htel :=
    properSubwheel_base_sub_boundaryPrefix_eq_advancedBase_add_squares
      T Y T hYT le_rfl hcubic
  rw [frozenPrimeUniverseMass_primesUpTo_self_eq_mertensSummatoryInt] at htel
  simpa [T, Y] using htel

end RHLean.Proof

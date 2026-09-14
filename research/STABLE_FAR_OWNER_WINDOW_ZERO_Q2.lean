import Mathlib
import RHLean.Proof.StableFarWallCrossingOwnerWindow

/-!
# Stable-far returned-owner window has zero local q^2 column

The exact owner-window telescope in `StableFarWallCrossingOwnerWindow` leaves a
lower Mertens state at reciprocal depth `T` plus a formal column

  sum_{q in (max(r,sqrt T), T]} M(floor(T/q^2)).

But every returned owner in that interval satisfies `q > sqrt T`, hence
`q^2 > T`.  Every displayed q^2 daughter is therefore exactly `M(0)=0`.
This removes the local q^2 column before any norm is taken: the whole returned
owner chronology is exactly the single lower Mertens state `M(T)`, and the
existing module already proves `T < R`.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Every owner returned by the stable-far window lies beyond the square root
of its reciprocal depth, so its q^2 daughter cutoff is zero. -/
theorem lowWheelFarPrimeQ2CrossingOwner_div_square_eq_zero
    {R : ℕ} {y : ℕ × (ℕ × ℕ)}
    (hy : y ∈ lowWheelFarPrimeQ2DescendedTriples R)
    {q : ℕ}
    (hq : q ∈ frozenPrimeUniverseHighPrimeSet
      (lowWheelFarPrimeQ2CrossingOwnerLower R y)
      (lowWheelFarPrimeQ2CrossingOwnerDepth R y)) :
    lowWheelFarPrimeQ2CrossingOwnerDepth R y / (q * q) = 0 := by
  let T := lowWheelFarPrimeQ2CrossingOwnerDepth R y
  let Y := lowWheelFarPrimeQ2CrossingOwnerLower R y
  have hqData := mem_frozenPrimeUniverseHighPrimeSet.mp hq
  have hYq : Y < q := by
    simpa [Y] using hqData.2.1
  have hsqrtY : Nat.sqrt T ≤ Y := by
    dsimp [T, Y, lowWheelFarPrimeQ2CrossingOwnerLower]
    exact le_max_right _ _
  have hsqrtq : Nat.sqrt T < q := hsqrtY.trans_lt hYq
  have hsucc : Nat.sqrt T + 1 ≤ q := Nat.succ_le_iff.mpr hsqrtq
  have hTlt : T < (Nat.sqrt T + 1) ^ 2 := Nat.lt_succ_sqrt' T
  have hsqle : (Nat.sqrt T + 1) ^ 2 ≤ q ^ 2 :=
    Nat.pow_le_pow_left hsucc 2
  have hTq : T < q * q := by
    rw [← pow_two]
    exact hTlt.trans_le hsqle
  dsimp [T]
  exact Nat.div_eq_of_lt hTq

/-- The entire local q^2 daughter column in the returned-owner telescope
vanishes identically. -/
theorem lowWheelFarPrimeQ2CrossingOwnerWindow_q2Column_eq_zero
    {R : ℕ} {y : ℕ × (ℕ × ℕ)}
    (hy : y ∈ lowWheelFarPrimeQ2DescendedTriples R) :
    (∑ q ∈ frozenPrimeUniverseHighPrimeSet
        (lowWheelFarPrimeQ2CrossingOwnerLower R y)
        (lowWheelFarPrimeQ2CrossingOwnerDepth R y),
      mertensSummatoryInt
        (lowWheelFarPrimeQ2CrossingOwnerDepth R y / (q * q))) = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  rw [lowWheelFarPrimeQ2CrossingOwner_div_square_eq_zero hy hq]
  simp [mertensSummatoryInt]

/-- **Collapsed returned-owner telescope.**  The complete first-power chronology
on one stable-far descended child is exactly the lower Mertens state at depth
`T`; the apparent q^2 column is identically zero. -/
theorem lowWheelFarPrimeQ2CrossingOwnerWindow_telescope_eq_mertens
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
      mertensSummatoryInt (lowWheelFarPrimeQ2CrossingOwnerDepth R y) := by
  have h := lowWheelFarPrimeQ2CrossingOwnerWindow_telescope hy
  have hz := lowWheelFarPrimeQ2CrossingOwnerWindow_q2Column_eq_zero hy
  rw [hz, add_zero] at h
  exact h

end RHLean.Proof

import RHLean.Proof.PrimeWheelProperSubwheelDepthTwo

/-!
# Cubic proper-subwheel outer parity reassembly

This is the sign-visible companion to the chronological depth-two normal form.
Instead of opening a high owner at its own prime first, telescope the predecessor
state back to the common proper subwheel `Y`.

For `X < (Y+1)^3`, two primes above `Y` already force the reciprocal cutoff
back below `Y`.  Consequently

`F_{p^-}(X/p)
   = F_Y(X/p) - sum_{Y < q < p} M(X/(p*q))`,

and the whole Mertens value becomes

`M(X)
 = F_Y(X)
   - sum_{Y < p <= X} F_Y(X/p)
   + sum_{Y < q < p <= X} M(X/(p*q))`.

This is the literal prime/semiprime Möbius sign pattern on one common kernel:
base `+`, prime layer `-`, semiprime layer `+`.  The semiprime response is
already ordinary lower Mertens.  No norm or estimate is introduced.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- Two owners above the cubic cutoff push the reciprocal state below the
proper-subwheel threshold. -/
theorem properSubwheel_twoHighOwners_reciprocal_lt_succ
    {X Y p q : ℕ}
    (hp : Y < p) (hq : Y < q)
    (hpp : p.Prime) (hqp : q.Prime)
    (hcubic : X < (Y + 1) ^ 3) :
    X / (p * q) < Y + 1 := by
  have hpLower : Y + 1 ≤ p := by omega
  have hqLower : Y + 1 ≤ q := by omega
  have hprod : (Y + 1) * (Y + 1) ≤ p * q :=
    Nat.mul_le_mul hpLower hqLower
  have hscale : (Y + 1) ^ 3 ≤ (Y + 1) * (p * q) := by
    calc
      (Y + 1) ^ 3 = (Y + 1) * ((Y + 1) * (Y + 1)) := by ring
      _ ≤ (Y + 1) * (p * q) := Nat.mul_le_mul_left (Y + 1) hprod
  apply (Nat.div_lt_iff_lt_mul (Nat.mul_pos hpp.pos hqp.pos)).2
  exact hcubic.trans_le hscale

/-- **One predecessor boundary on the common proper subwheel.**  Its unfinished
part consists exactly of earlier high owners, and each such two-prime child is
already a completed lower Mertens state. -/
theorem properSubwheel_predecessorBoundary_eq_base_sub_semiprimeLayer
    {X Y p : ℕ}
    (hp : p ∈ frozenPrimeUniverseHighPrimeSet Y X)
    (hcubic : X < (Y + 1) ^ 3) :
    frozenPrimeUniverseMass (primesUpTo (p - 1)) (X / p) =
      frozenPrimeUniverseMass (primesUpTo Y) (X / p) -
        ∑ q ∈ frozenPrimeUniverseHighPrimeSet Y (p - 1),
          mertensSummatoryInt (X / (p * q)) := by
  have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hp
  have hYpred : Y ≤ p - 1 := by omega
  have htel :=
    frozenPrimeUniverse_highUpperColumn_telescope (X / p) Y (p - 1) hYpred
  have hterms :
      (∑ q ∈ frozenPrimeUniverseHighPrimeSet Y (p - 1),
          frozenPrimeUniverseMass (primesUpTo (q - 1)) ((X / p) / q)) =
        ∑ q ∈ frozenPrimeUniverseHighPrimeSet Y (p - 1),
          mertensSummatoryInt (X / (p * q)) := by
    apply Finset.sum_congr rfl
    intro q hq
    have hqData := mem_frozenPrimeUniverseHighPrimeSet.mp hq
    have hsmall :=
      properSubwheel_twoHighOwners_reciprocal_lt_succ
        hpData.2.1 hqData.2.1 hpData.1 hqData.1 hcubic
    have hcutq : X / (p * q) < q := by omega
    have hcomplete :=
      frozenPrimeUniverseMass_eq_mertensSummatoryInt_of_lt_owner
        hqData.1 hcutq
    rw [Nat.div_div_eq_div_mul, hcomplete]
  rw [hterms] at htel
  omega

/-- The full chronological high-owner column is the common-kernel prime layer
minus its ordered semiprime correction. -/
theorem properSubwheel_highOwnerColumn_eq_commonPrime_sub_semiprime
    (X Y : ℕ) (hcubic : X < (Y + 1) ^ 3) :
    (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
        frozenPrimeUniverseMass (primesUpTo (p - 1)) (X / p)) =
      (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
        frozenPrimeUniverseMass (primesUpTo Y) (X / p)) -
        ∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
          ∑ q ∈ frozenPrimeUniverseHighPrimeSet Y (p - 1),
            mertensSummatoryInt (X / (p * q)) := by
  calc
    (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
        frozenPrimeUniverseMass (primesUpTo (p - 1)) (X / p)) =
      ∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
        (frozenPrimeUniverseMass (primesUpTo Y) (X / p) -
          ∑ q ∈ frozenPrimeUniverseHighPrimeSet Y (p - 1),
            mertensSummatoryInt (X / (p * q))) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact properSubwheel_predecessorBoundary_eq_base_sub_semiprimeLayer
        hp hcubic
    _ = _ := by rw [Finset.sum_sub_distrib]

/-- **Cubic outer-parity normal form.**  Every term after the base has the
literal Möbius parity of its unresolved high-prime depth: prime responses are
negative and semiprime responses positive. -/
theorem mertensSummatoryInt_eq_properSubwheel_outerParityDepthTwo
    (X Y : ℕ) (hYX : Y ≤ X) (hcubic : X < (Y + 1) ^ 3) :
    mertensSummatoryInt X =
      frozenPrimeUniverseMass (primesUpTo Y) X -
        (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
          frozenPrimeUniverseMass (primesUpTo Y) (X / p)) +
        ∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
          ∑ q ∈ frozenPrimeUniverseHighPrimeSet Y (p - 1),
            mertensSummatoryInt (X / (p * q)) := by
  rw [mertensSummatoryInt_eq_properSubwheel_sub_highOwnerColumn X Y hYX,
    properSubwheel_highOwnerColumn_eq_commonPrime_sub_semiprime X Y hcubic]
  ring

/-- Same sign-visible identity on the literal frozen rough-seat correlation. -/
theorem primeWheelFrozenFullRoughSeatCorrelation_eq_outerParityDepthTwo
    (X Y : ℕ) (hYX : Y ≤ X) (hcubic : X < (Y + 1) ^ 3) :
    primeWheelFrozenFullRoughSeatCorrelation (primesUpTo Y) X =
      frozenPrimeUniverseMass (primesUpTo Y) X -
        (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
          frozenPrimeUniverseMass (primesUpTo Y) (X / p)) +
        ∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
          ∑ q ∈ frozenPrimeUniverseHighPrimeSet Y (p - 1),
            mertensSummatoryInt (X / (p * q)) := by
  rw [← mertensSummatoryInt_eq_properSubwheel_outerParityDepthTwo X Y hYX hcubic]
  rw [← roughMertens_one_eq_primeWheel_frozenFullRoughSeatCorrelation
    (primesUpTo Y) (fun p hp => prime_of_mem_primesUpTo hp) X]
  unfold roughMertens mertensSummatoryInt
  simp [roughMoebius]

/-- Square-endpoint form: the proper subwheel keeps the outer `- / +` prime
parity explicit all the way to the RH-critical physical endpoint. -/
theorem squareRootProperSubwheelFrozenCorrelation_eq_outerParityDepthTwo
    (R Y : ℕ)
    (hYX : Y ≤ squareRootEndpoint R)
    (hcubic : squareRootEndpoint R < (Y + 1) ^ 3) :
    squareRootProperSubwheelFrozenCorrelation R Y =
      frozenPrimeUniverseMass (primesUpTo Y) (squareRootEndpoint R) -
        (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y (squareRootEndpoint R),
          frozenPrimeUniverseMass (primesUpTo Y) (squareRootEndpoint R / p)) +
        ∑ p ∈ frozenPrimeUniverseHighPrimeSet Y (squareRootEndpoint R),
          ∑ q ∈ frozenPrimeUniverseHighPrimeSet Y (p - 1),
            mertensSummatoryInt (squareRootEndpoint R / (p * q)) := by
  unfold squareRootProperSubwheelFrozenCorrelation
  exact primeWheelFrozenFullRoughSeatCorrelation_eq_outerParityDepthTwo
    (squareRootEndpoint R) Y hYX hcubic

end RHLean.Proof

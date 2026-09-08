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

/-! ## Half-root specialization: the semiprime response has only four states -/

/-- At the square endpoint, stopping the wheel at `R/2` is already safely past
the cubic depth-two threshold once `R >= 6`. -/
theorem squareRootEndpoint_lt_halfRootSucc_cube
    (R : ℕ) (hR : 6 ≤ R) :
    squareRootEndpoint R < (R / 2 + 1) ^ 3 := by
  have hRlt : R < 2 * (R / 2 + 1) := by omega
  have hsq : R ^ 2 < (2 * (R / 2 + 1)) ^ 2 :=
    Nat.pow_lt_pow_left hRlt (by omega)
  have hfour : 4 ≤ R / 2 + 1 := by omega
  have hfourSq :
      4 * (R / 2 + 1) ^ 2 ≤ (R / 2 + 1) ^ 3 := by
    calc
      4 * (R / 2 + 1) ^ 2 ≤
          (R / 2 + 1) * (R / 2 + 1) ^ 2 :=
        Nat.mul_le_mul_right ((R / 2 + 1) ^ 2) hfour
      _ = (R / 2 + 1) ^ 3 := by ring
  have hsq' : R ^ 2 < 4 * (R / 2 + 1) ^ 2 := by
    calc
      R ^ 2 < (2 * (R / 2 + 1)) ^ 2 := hsq
      _ = 4 * (R / 2 + 1) ^ 2 := by ring
  have hX : squareRootEndpoint R < R ^ 2 := by
    unfold squareRootEndpoint
    have hpos : 0 < R ^ 2 := by positivity
    omega
  exact hX.trans (hsq'.trans_le hfourSq)

/-- Two primes above the half-root force the square-endpoint reciprocal quotient
into the fixed set `{0,1,2,3}`.  This is much sharper than the generic cubic
bound `X/(pq) < Y+1`. -/
theorem squareRootEndpoint_div_two_halfRootHighPrimes_lt_four
    {R p q : ℕ} (hR : 6 ≤ R)
    (hp : p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R))
    (hq : q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1)) :
    squareRootEndpoint R / (p * q) < 4 := by
  have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hp
  have hqData := mem_frozenPrimeUniverseHighPrimeSet.mp hq
  have hpLower : R / 2 + 1 ≤ p := by omega
  have hqLower : R / 2 + 1 ≤ q := by omega
  have hRlt : R < 2 * (R / 2 + 1) := by omega
  have hRsq : R ^ 2 < (2 * (R / 2 + 1)) ^ 2 :=
    Nat.pow_lt_pow_left hRlt (by omega)
  have hpqLower : (R / 2 + 1) * (R / 2 + 1) ≤ p * q :=
    Nat.mul_le_mul hpLower hqLower
  have hfour : (2 * (R / 2 + 1)) ^ 2 ≤ 4 * (p * q) := by
    calc
      (2 * (R / 2 + 1)) ^ 2 =
          4 * ((R / 2 + 1) * (R / 2 + 1)) := by ring
      _ ≤ 4 * (p * q) := Nat.mul_le_mul_left 4 hpqLower
  have hX : squareRootEndpoint R < R ^ 2 := by
    unfold squareRootEndpoint
    have hpos : 0 < R ^ 2 := by positivity
    omega
  have hX4 : squareRootEndpoint R < 4 * (p * q) :=
    hX.trans (hRsq.trans_le hfour)
  apply (Nat.div_lt_iff_lt_mul (Nat.mul_pos hpData.1.pos hqData.1.pos)).2
  simpa [Nat.mul_assoc] using hX4

/-- The four-state response carried by a pair of primes above the half-root.
The values are exactly the ordinary Mertens prefixes at reciprocal depths
`0,1,2,3`; only depths `1` and `3` survive. -/
def halfRootPrimePairWeight (R p q : ℕ) : ℤ :=
  if squareRootEndpoint R / (p * q) = 1 then 1
  else if squareRootEndpoint R / (p * q) = 3 then -1
  else 0

private theorem mertensSummatoryInt_zero : mertensSummatoryInt 0 = 0 := by
  simp [mertensSummatoryInt]

private theorem mertensSummatoryInt_one : mertensSummatoryInt 1 = 1 := by
  norm_num [mertensSummatoryInt]

private theorem mertensSummatoryInt_two : mertensSummatoryInt 2 = 0 := by
  norm_num [mertensSummatoryInt, ArithmeticFunction.moebius_apply_prime]

private theorem mertensSummatoryInt_three : mertensSummatoryInt 3 = -1 := by
  norm_num [mertensSummatoryInt, ArithmeticFunction.moebius_apply_prime]

/-- The semiprime Mertens response at the half-root is literally the finite
prime-pair weight `0,+1,0,-1`; no unknown lower Mertens value remains. -/
theorem mertensSummatoryInt_squareRootEndpoint_div_pair_eq_halfRootPrimePairWeight
    {R p q : ℕ} (hR : 6 ≤ R)
    (hp : p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R))
    (hq : q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1)) :
    mertensSummatoryInt (squareRootEndpoint R / (p * q)) =
      halfRootPrimePairWeight R p q := by
  have hlt := squareRootEndpoint_div_two_halfRootHighPrimes_lt_four hR hp hq
  have hcases : squareRootEndpoint R / (p * q) = 0 ∨
      squareRootEndpoint R / (p * q) = 1 ∨
      squareRootEndpoint R / (p * q) = 2 ∨
      squareRootEndpoint R / (p * q) = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · rw [h0, mertensSummatoryInt_zero]
    simp [halfRootPrimePairWeight, h0]
  · rw [h1, mertensSummatoryInt_one]
    simp [halfRootPrimePairWeight, h1]
  · rw [h2, mertensSummatoryInt_two]
    simp [halfRootPrimePairWeight, h2]
  · rw [h3, mertensSummatoryInt_three]
    simp [halfRootPrimePairWeight, h3]

/-- **Half-root prime-pair normal form.**  At the canonical square endpoint,
all two-high-prime Mertens responses collapse to the four-state arithmetic
weight above.  The only nontrivial unresolved signed objects are now the common
half-root frozen base and its one-prime response column; the semiprime layer is
pure finite prime-pair geometry. -/
theorem squareRootProperSubwheelFrozenCorrelation_eq_halfRootPrimePairWeight
    (R : ℕ) (hR : 6 ≤ R) :
    squareRootProperSubwheelFrozenCorrelation R (R / 2) =
      frozenPrimeUniverseMass (primesUpTo (R / 2)) (squareRootEndpoint R) -
        (∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R),
          frozenPrimeUniverseMass (primesUpTo (R / 2))
            (squareRootEndpoint R / p)) +
        ∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R),
          ∑ q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1),
            halfRootPrimePairWeight R p q := by
  have hRX : R ≤ squareRootEndpoint R := by
    have hquad : R + 1 ≤ R ^ 2 := by nlinarith
    unfold squareRootEndpoint
    omega
  have hYX : R / 2 ≤ squareRootEndpoint R := (Nat.div_le_self R 2).trans hRX
  have hcubic := squareRootEndpoint_lt_halfRootSucc_cube R hR
  have hmain :=
    squareRootProperSubwheelFrozenCorrelation_eq_outerParityDepthTwo
      R (R / 2) hYX hcubic
  have hsemi :
      (∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R),
          ∑ q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1),
            mertensSummatoryInt (squareRootEndpoint R / (p * q))) =
        ∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R),
          ∑ q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1),
            halfRootPrimePairWeight R p q := by
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    exact
      mertensSummatoryInt_squareRootEndpoint_div_pair_eq_halfRootPrimePairWeight
        hR hp hq
  rw [hsemi] at hmain
  exact hmain

end RHLean.Proof

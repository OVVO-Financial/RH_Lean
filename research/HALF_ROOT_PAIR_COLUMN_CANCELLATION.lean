import «research.HALF_ROOT_PRIME_PAIR_WEIGHT»

/-!
# Half-root pair/column cancellation

The half-root outer-parity form from #607 has a large common one-prime column
and a large signed prime-pair shell.  They must not be estimated separately.

This file combines them owner-by-owner before any norm.  For each high owner
`p > R/2`, the exact predecessor identity gives

`F_{R/2}(X_R/p) - sum_{R/2<q<p} M(X_R/(p*q)) = F_p(X_R/p) + M(X_R/p^2)`.

At the half-root cutoff both lower responses are already finite: the pair term
is the four-state weight from #607, and the square response `M(X_R/p^2)` also
has reciprocal depth `< 4`.  Thus the two-dimensional pair shell is consumed
inside the one-prime column and leaves only

* the genuine moving predecessor boundary `F_p(X_R/p)`, and
* a one-dimensional four-state prime-square correction.

The latter is the exponent-changing part of this cancellation: no two-prime
population remains in it.  No norm, PNT input, prime-gap assumption, Mertens
hypothesis, or asymptotic estimate is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

private theorem halfRoot_mertensSummatoryInt_zero : mertensSummatoryInt 0 = 0 := by
  simp [mertensSummatoryInt]

private theorem halfRoot_mertensSummatoryInt_one : mertensSummatoryInt 1 = 1 := by
  unfold mertensSummatoryInt
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  norm_num

private theorem halfRoot_mertensSummatoryInt_two : mertensSummatoryInt 2 = 0 := by
  have hmu2 : μ 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_two
  unfold mertensSummatoryInt
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  norm_num [hmu2]

private theorem halfRoot_mertensSummatoryInt_three : mertensSummatoryInt 3 = -1 := by
  have hmu2 : μ 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have hmu3 : μ 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  unfold mertensSummatoryInt
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ]
  norm_num [hmu2, hmu3]

/-- Four-state square residual left after the pair shell is consumed inside one
high-owner column. -/
def halfRootPrimeSquareWeight (R p : ℕ) : ℤ :=
  if squareRootEndpoint R / (p * p) = 1 then 1
  else if squareRootEndpoint R / (p * p) = 3 then -1
  else 0

/-- A high owner above `R/2` has square reciprocal depth strictly below four. -/
theorem squareRootEndpoint_div_square_halfRootHighPrime_lt_four
    {R p : ℕ} (hR : 6 ≤ R)
    (hp : p ∈ frozenPrimeUniverseHighPrimeSet
      (R / 2) (squareRootEndpoint R)) :
    squareRootEndpoint R / (p * p) < 4 := by
  have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hp
  have hpLower : R / 2 + 1 ≤ p := by omega
  have hRlt : R < 2 * (R / 2 + 1) := by omega
  have hscale : 2 * (R / 2 + 1) ≤ 2 * p :=
    Nat.mul_le_mul_left 2 hpLower
  have hRp : R < 2 * p := hRlt.trans_le hscale
  have hRsq : R ^ 2 < (2 * p) ^ 2 :=
    Nat.pow_lt_pow_left hRp (by omega)
  have hX : squareRootEndpoint R < R ^ 2 := by
    unfold squareRootEndpoint
    have hpos : 0 < R ^ 2 := by positivity
    omega
  have hX4 : squareRootEndpoint R < 4 * (p * p) := by
    calc
      squareRootEndpoint R < R ^ 2 := hX
      _ < (2 * p) ^ 2 := hRsq
      _ = 4 * (p * p) := by ring
  apply (Nat.div_lt_iff_lt_mul
    (Nat.mul_pos hpData.1.pos hpData.1.pos)).2
  simpa [Nat.mul_assoc] using hX4

/-- The completed square residual is exactly the four-state square weight. -/
theorem mertensSummatoryInt_squareRootEndpoint_div_square_eq_halfRootPrimeSquareWeight
    {R p : ℕ} (hR : 6 ≤ R)
    (hp : p ∈ frozenPrimeUniverseHighPrimeSet
      (R / 2) (squareRootEndpoint R)) :
    mertensSummatoryInt (squareRootEndpoint R / (p * p)) =
      halfRootPrimeSquareWeight R p := by
  have hlt := squareRootEndpoint_div_square_halfRootHighPrime_lt_four hR hp
  let z := squareRootEndpoint R / (p * p)
  have hzlt : z < 4 := by simpa [z] using hlt
  by_cases hz0 : z = 0
  · simp [halfRootPrimeSquareWeight, z, hz0,
      halfRoot_mertensSummatoryInt_zero]
  by_cases hz1 : z = 1
  · simp [halfRootPrimeSquareWeight, z, hz1,
      halfRoot_mertensSummatoryInt_one]
  by_cases hz2 : z = 2
  · simp [halfRootPrimeSquareWeight, z, hz2,
      halfRoot_mertensSummatoryInt_two]
  have hz3 : z = 3 := by
    clear_value z
    omega
  simp [halfRootPrimeSquareWeight, z, hz3,
    halfRoot_mertensSummatoryInt_three]

/-- Pointwise version of #607's pair evaluation at one fixed outer owner. -/
theorem halfRoot_semiprimeInnerLayer_eq_primePairWeight
    {R p : ℕ} (hR : 6 ≤ R)
    (hp : p ∈ frozenPrimeUniverseHighPrimeSet
      (R / 2) (squareRootEndpoint R)) :
    (∑ q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1),
        mertensSummatoryInt (squareRootEndpoint R / (p * q))) =
      ∑ q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1),
        halfRootPrimePairWeight R p q := by
  apply Finset.sum_congr rfl
  intro q hq
  exact mertensSummatoryInt_squareRootEndpoint_div_pair_eq_halfRootPrimePairWeight
    hR hp hq

/-- **Ownerwise exponent-changing cancellation.**

The common half-root prime column and its complete pair shell cancel before any
absolute value.  What survives at one owner is the genuine moving boundary plus
one square-dilated four-state residue. -/
theorem halfRoot_commonPrimeColumn_sub_pairShell_eq_boundary_add_squareWeight
    {R p : ℕ} (hR : 6 ≤ R)
    (hp : p ∈ frozenPrimeUniverseHighPrimeSet
      (R / 2) (squareRootEndpoint R)) :
    frozenPrimeUniverseMass (primesUpTo (R / 2))
          (squareRootEndpoint R / p) -
        (∑ q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1),
          halfRootPrimePairWeight R p q) =
      frozenPrimeUniverseMass (primesUpTo p)
          (squareRootEndpoint R / p) +
        halfRootPrimeSquareWeight R p := by
  have hcubic := squareRootEndpoint_lt_halfRootSucc_cube R hR
  have hpairs := halfRoot_semiprimeInnerLayer_eq_primePairWeight hR hp
  have hpred := properSubwheel_predecessorBoundary_eq_base_sub_semiprimeLayer
    hp hcubic
  have hmove := properSubwheel_highOwnerMovingTerm_eq_boundary_add_mertensSquare
    hp hcubic
  have hsq :=
    mertensSummatoryInt_squareRootEndpoint_div_square_eq_halfRootPrimeSquareWeight
      hR hp
  calc
    frozenPrimeUniverseMass (primesUpTo (R / 2))
          (squareRootEndpoint R / p) -
        (∑ q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1),
          halfRootPrimePairWeight R p q) =
      frozenPrimeUniverseMass (primesUpTo (R / 2))
          (squareRootEndpoint R / p) -
        (∑ q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1),
          mertensSummatoryInt (squareRootEndpoint R / (p * q))) := by
            rw [hpairs]
    _ = frozenPrimeUniverseMass (primesUpTo (p - 1))
          (squareRootEndpoint R / p) := hpred.symm
    _ = frozenPrimeUniverseMass (primesUpTo p)
          (squareRootEndpoint R / p) +
        mertensSummatoryInt (squareRootEndpoint R / (p * p)) := hmove
    _ = frozenPrimeUniverseMass (primesUpTo p)
          (squareRootEndpoint R / p) +
        halfRootPrimeSquareWeight R p := by rw [hsq]

/-- The full common one-prime column. -/
def halfRootCommonPrimeColumn (R : ℕ) : ℤ :=
  ∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R),
    frozenPrimeUniverseMass (primesUpTo (R / 2))
      (squareRootEndpoint R / p)

/-- The full signed pair shell from #607. -/
def halfRootPrimePairShell (R : ℕ) : ℤ :=
  ∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R),
    ∑ q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1),
      halfRootPrimePairWeight R p q

/-- The chronological moving boundary after the pair shell has been consumed. -/
def halfRootMovingBoundaryColumn (R : ℕ) : ℤ :=
  ∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R),
    frozenPrimeUniverseMass (primesUpTo p) (squareRootEndpoint R / p)

/-- One-dimensional square correction left by the ownerwise cancellation. -/
def halfRootPrimeSquareCorrection (R : ℕ) : ℤ :=
  ∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R),
    halfRootPrimeSquareWeight R p

/-- **Global pair/column cancellation.**  The complete two-prime shell is not a
separate error term: it cancels inside the common prime column and leaves one
moving boundary column plus the one-dimensional square correction. -/
theorem halfRoot_commonPrimeColumn_sub_pairShell_eq_boundary_add_squareCorrection
    (R : ℕ) (hR : 6 ≤ R) :
    halfRootCommonPrimeColumn R - halfRootPrimePairShell R =
      halfRootMovingBoundaryColumn R + halfRootPrimeSquareCorrection R := by
  unfold halfRootCommonPrimeColumn halfRootPrimePairShell
    halfRootMovingBoundaryColumn halfRootPrimeSquareCorrection
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  exact halfRoot_commonPrimeColumn_sub_pairShell_eq_boundary_add_squareWeight
    hR hp

/-- **#607 after the cancellation is actually taken.**  The explicit prime-pair
population has disappeared from the endpoint identity.  Its only residual is a
one-dimensional square weight; the remaining nontrivial object is the moving
boundary coupled to the common frozen base. -/
theorem squareRootProperSubwheelFrozenCorrelation_eq_halfRootBoundary_sub_squareCorrection
    (R : ℕ) (hR : 6 ≤ R) :
    squareRootProperSubwheelFrozenCorrelation R (R / 2) =
      frozenPrimeUniverseMass (primesUpTo (R / 2)) (squareRootEndpoint R) -
        halfRootMovingBoundaryColumn R - halfRootPrimeSquareCorrection R := by
  have h607 :=
    squareRootProperSubwheelFrozenCorrelation_eq_halfRootPrimePairShell R hR
  have hcancel :=
    halfRoot_commonPrimeColumn_sub_pairShell_eq_boundary_add_squareCorrection
      R hR
  calc
    squareRootProperSubwheelFrozenCorrelation R (R / 2) =
      frozenPrimeUniverseMass (primesUpTo (R / 2)) (squareRootEndpoint R) -
        halfRootCommonPrimeColumn R + halfRootPrimePairShell R := by
          simpa [halfRootCommonPrimeColumn, halfRootPrimePairShell] using h607
    _ = frozenPrimeUniverseMass (primesUpTo (R / 2)) (squareRootEndpoint R) -
        (halfRootCommonPrimeColumn R - halfRootPrimePairShell R) := by ring
    _ = frozenPrimeUniverseMass (primesUpTo (R / 2)) (squareRootEndpoint R) -
        (halfRootMovingBoundaryColumn R + halfRootPrimeSquareCorrection R) := by
          rw [hcancel]
    _ = frozenPrimeUniverseMass (primesUpTo (R / 2)) (squareRootEndpoint R) -
        halfRootMovingBoundaryColumn R - halfRootPrimeSquareCorrection R := by ring

/-- Every square correction atom has unit size. -/
theorem abs_halfRootPrimeSquareWeight_le_one (R p : ℕ) :
    |halfRootPrimeSquareWeight R p| ≤ 1 := by
  unfold halfRootPrimeSquareWeight
  split_ifs <;> norm_num

/-- Owners beyond the physical root have zero square correction. -/
theorem halfRootPrimeSquareWeight_eq_zero_of_root_lt
    {R p : ℕ} (hR : 1 ≤ R) (hRp : R < p) :
    halfRootPrimeSquareWeight R p = 0 := by
  have hX : squareRootEndpoint R < R ^ 2 := by
    unfold squareRootEndpoint
    have hpos : 0 < R ^ 2 := by positivity
    omega
  have hpow : R ^ 2 < p ^ 2 :=
    Nat.pow_lt_pow_left hRp (by omega)
  have hlt : squareRootEndpoint R < p * p := by
    simpa [pow_two] using hX.trans hpow
  have hzero : squareRootEndpoint R / (p * p) = 0 := Nat.div_eq_of_lt hlt
  simp [halfRootPrimeSquareWeight, hzero]

end RHLean.Proof

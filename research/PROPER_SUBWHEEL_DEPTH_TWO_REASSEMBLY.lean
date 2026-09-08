import RHLean.Proof.PrimeWheelProperSubwheelDepthTwo

/-!
# Proper-subwheel depth-two reassembly

The cubic proper-subwheel normal form in `PrimeWheelProperSubwheelDepthTwo`
leaves a moving frozen boundary `F_p(X/p)` for owners `Y < p <= R`.  This
scratch closes that algebraic layer exactly.

If `k < p^2`, the frozen universe through `p` can contain at most one later
prime coordinate beyond `p` at cutoff `k`.  The existing high-prime telescope
therefore gives

`F_p(k) = M(k) + sum_{p < q <= k} M(k/q)`.

At `k = X/p` under `X < p^3`, this is exactly the diagonal/off-diagonal
prime-semiprime layer.  No absolute value, counting estimate, or analytic input
is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- **Depth-two completion of a frozen boundary.**  Below `p^2`, every later
owner `q > p` has reciprocal cutoff below itself, hence its predecessor state
is already ordinary Mertens. -/
theorem frozenPrimeUniverseMass_primesUpTo_eq_mertens_add_highOwnerMertens
    {p k : ℕ} (hp : p.Prime) (hk : k < p ^ 2) :
    frozenPrimeUniverseMass (primesUpTo p) k =
      mertensSummatoryInt k +
        ∑ q ∈ frozenPrimeUniverseHighPrimeSet p k,
          mertensSummatoryInt (k / q) := by
  by_cases hpk : p ≤ k
  · have htel := frozenPrimeUniverse_highUpperColumn_telescope k p k hpk
    rw [frozenPrimeUniverseMass_primesUpTo_self_eq_mertensSummatoryInt] at htel
    have hterms :
        (∑ q ∈ frozenPrimeUniverseHighPrimeSet p k,
            frozenPrimeUniverseMass (primesUpTo (q - 1)) (k / q)) =
          ∑ q ∈ frozenPrimeUniverseHighPrimeSet p k,
            mertensSummatoryInt (k / q) := by
      apply Finset.sum_congr rfl
      intro q hq
      have hqData := mem_frozenPrimeUniverseHighPrimeSet.mp hq
      have hpq : p < q := hqData.2.1
      have hp2q2 : p ^ 2 < q ^ 2 := Nat.pow_lt_pow_left hpq (by omega)
      have hkq2 : k < q ^ 2 := hk.trans hp2q2
      have hdiv : k / q < q := by
        apply (Nat.div_lt_iff_lt_mul hqData.1.pos).2
        simpa [pow_two] using hkq2
      exact frozenPrimeUniverseMass_eq_mertensSummatoryInt_of_lt_owner
        hqData.1 hdiv
    rw [hterms] at htel
    omega
  · have hkp : k < p := Nat.lt_of_not_ge hpk
    have hbase :=
      frozenPrimeUniverseMass_primesUpTo_eq_mertensSummatoryInt_of_lt hp hkp
    have hempty : frozenPrimeUniverseHighPrimeSet p k = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      have hqData := mem_frozenPrimeUniverseHighPrimeSet.mp hq
      omega
    rw [hbase, hempty]
    simp

/-- Cubic specialization: the moving boundary at owner `p` is exactly one
lower Mertens state plus the off-diagonal semiprime states with second owner
`q > p`. -/
theorem properSubwheel_boundaryState_eq_mertens_add_semiprimeLayer
    {X Y p : ℕ}
    (hp : p ∈ frozenPrimeUniverseHighPrimeSet Y X)
    (hcubic : X < (Y + 1) ^ 3) :
    frozenPrimeUniverseMass (primesUpTo p) (X / p) =
      mertensSummatoryInt (X / p) +
        ∑ q ∈ frozenPrimeUniverseHighPrimeSet p (X / p),
          mertensSummatoryInt (X / (p * q)) := by
  have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hp
  have hcube : X < p ^ 3 :=
    properSubwheelHighPrime_owner_cube_gt hp hcubic
  have hkSq : X / p < p ^ 2 := by
    apply (Nat.div_lt_iff_lt_mul hpData.1.pos).2
    simpa [pow_succ, Nat.mul_assoc] using hcube
  have h :=
    frozenPrimeUniverseMass_primesUpTo_eq_mertens_add_highOwnerMertens
      hpData.1 hkSq
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro q _hq
  rw [Nat.div_div_eq_div_mul]

/-- The whole unfinished middle boundary is therefore a one-prime lower
Mertens band plus its off-diagonal semiprime layer. -/
theorem squareRootProperSubwheel_middleBoundary_eq_mertensBand_add_semiprimeLayer
    (R Y : ℕ) (hR : 2 ≤ R) (hYR : Y ≤ R)
    (hcubic : squareRootEndpoint R < (Y + 1) ^ 3) :
    (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y R,
        frozenPrimeUniverseMass (primesUpTo p) (squareRootEndpoint R / p)) =
      (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y R,
        mertensSummatoryInt (squareRootEndpoint R / p)) +
      ∑ p ∈ frozenPrimeUniverseHighPrimeSet Y R,
        ∑ q ∈ frozenPrimeUniverseHighPrimeSet p (squareRootEndpoint R / p),
          mertensSummatoryInt (squareRootEndpoint R / (p * q)) := by
  have hRX : R ≤ squareRootEndpoint R := by
    have hquad : R + 1 ≤ R ^ 2 := by nlinarith
    unfold squareRootEndpoint
    omega
  calc
    (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y R,
        frozenPrimeUniverseMass (primesUpTo p) (squareRootEndpoint R / p)) =
      ∑ p ∈ frozenPrimeUniverseHighPrimeSet Y R,
        (mertensSummatoryInt (squareRootEndpoint R / p) +
          ∑ q ∈ frozenPrimeUniverseHighPrimeSet p (squareRootEndpoint R / p),
            mertensSummatoryInt (squareRootEndpoint R / (p * q))) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hp
      have hpFull :
          p ∈ frozenPrimeUniverseHighPrimeSet Y (squareRootEndpoint R) :=
        mem_frozenPrimeUniverseHighPrimeSet.mpr
          ⟨hpData.1, hpData.2.1, hpData.2.2.trans hRX⟩
      exact properSubwheel_boundaryState_eq_mertens_add_semiprimeLayer
        hpFull hcubic
    _ = _ := by rw [Finset.sum_add_distrib]

/-- **All-Mertens cubic depth-two normal form.**  Every unfinished frozen
boundary has disappeared.  Beyond the single base state `F_Y(X_R)`, the exact
square-endpoint value is a one-prime lower-Mertens column and a two-prime
(diagonal plus off-diagonal) lower-Mertens column. -/
theorem squareRootProperSubwheelFrozenCorrelation_eq_base_sub_onePrime_sub_twoPrime
    (R Y : ℕ) (hR : 2 ≤ R) (hYR : Y ≤ R)
    (hcubic : squareRootEndpoint R < (Y + 1) ^ 3) :
    squareRootProperSubwheelFrozenCorrelation R Y =
      frozenPrimeUniverseMass (primesUpTo Y) (squareRootEndpoint R) -
        (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y (squareRootEndpoint R),
          mertensSummatoryInt (squareRootEndpoint R / p)) -
        (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y R,
          (mertensSummatoryInt (squareRootEndpoint R / (p * p)) +
            ∑ q ∈ frozenPrimeUniverseHighPrimeSet p (squareRootEndpoint R / p),
              mertensSummatoryInt (squareRootEndpoint R / (p * q)))) := by
  have hRX : R ≤ squareRootEndpoint R := by
    have hquad : R + 1 ≤ R ^ 2 := by nlinarith
    unfold squareRootEndpoint
    omega
  have hmain :=
    squareRootProperSubwheelFrozenCorrelation_eq_middleBoundary_sub_topBand_sub_middleSquares
      R Y hR hYR hcubic
  have hmiddle :=
    squareRootProperSubwheel_middleBoundary_eq_mertensBand_add_semiprimeLayer
      R Y hR hYR hcubic
  have hone :=
    sum_frozenPrimeUniverseHighPrimeSet_split
      Y R (squareRootEndpoint R) hYR hRX
      (fun p => mertensSummatoryInt (squareRootEndpoint R / p))
  rw [hmiddle] at hmain
  calc
    squareRootProperSubwheelFrozenCorrelation R Y =
      frozenPrimeUniverseMass (primesUpTo Y) (squareRootEndpoint R) -
        ((∑ p ∈ frozenPrimeUniverseHighPrimeSet Y R,
            mertensSummatoryInt (squareRootEndpoint R / p)) +
          ∑ p ∈ frozenPrimeUniverseHighPrimeSet R (squareRootEndpoint R),
            mertensSummatoryInt (squareRootEndpoint R / p)) -
        ((∑ p ∈ frozenPrimeUniverseHighPrimeSet Y R,
            mertensSummatoryInt (squareRootEndpoint R / (p * p))) +
          ∑ p ∈ frozenPrimeUniverseHighPrimeSet Y R,
            ∑ q ∈ frozenPrimeUniverseHighPrimeSet p (squareRootEndpoint R / p),
              mertensSummatoryInt (squareRootEndpoint R / (p * q))) := by
        rw [hmain]
        ring
    _ = _ := by
      rw [← hone]
      rw [← Finset.sum_add_distrib]

end RHLean.Proof

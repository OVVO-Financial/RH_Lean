import Mathlib
import RHLean.Proof.LowWheelFrozenSecondContactWindowReassembly

/-!
# Global telescope for the saturated frozen second-contact ledger

The saturated #629/#630 object must not be estimated owner-by-owner.  This
module takes the opposite order of operations: first sum the complete signed
owner windows, then telescope their moving upper endpoints globally.

For

`D_q = F_{q^-}(X_R/q) - F_{q^-}(max R (X_R/q^2))`,

the entire `X_R/q` column is exactly the upper-column telescope already proved
for the frozen Euler universe.  Hence

`sum_q D_q = 1 - F_{R-1}(X_R)
               - sum_q F_{q^-}(max R (X_R/q^2))`.

No norm, owner count, PNT input, Mertens hypothesis, or asymptotic estimate is
introduced.  This is the global signed Stokes form of the #630 ledger.

The final lemmas also record a structural limitation of the current ordinary
prime-toggle matching on the arithmetic child carrier: multiplying by a factor
strictly above the canonical largest-prime owner immediately crosses the
physical endpoint, while deleting the canonical owner destroys the
second-contact inequality.  Thus any surviving local toggle edge is necessarily
below the old owner; cancellation which changes the old owner must come from a
different global reassembly, not from another pass of the same local matching.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- **Global saturated upper-column telescope.**  Summing the #629 owner windows
before descending them consumes the entire moving upper column in one shot.
Only one root-floored lower column remains. -/
theorem lowWheelFrozenSecondContactHighOwnerWindowMass_sum_eq_rootFlooredLowerColumn
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ q ∈ primesUpTo (R - 1),
      lowWheelFrozenSecondContactHighOwnerWindowMass R q) =
      (1 - frozenPrimeUniverseMass (primesUpTo (R - 1))
        (squareRootEndpoint R)) -
        ∑ q ∈ primesUpTo (R - 1),
          frozenPrimeUniverseMass (primesUpTo (q - 1))
            (max R (squareRootEndpoint R / (q * q))) := by
  have hX : 1 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hsq : 2 ≤ R ^ 2 := by nlinarith
    omega
  calc
    (∑ q ∈ primesUpTo (R - 1),
        lowWheelFrozenSecondContactHighOwnerWindowMass R q) =
      ∑ q ∈ primesUpTo (R - 1),
        (frozenPrimeUniverseMass (primesUpTo (q - 1))
            (squareRootEndpoint R / q) -
          frozenPrimeUniverseMass (primesUpTo (q - 1))
            (max R (squareRootEndpoint R / (q * q)))) := by
      apply Finset.sum_congr rfl
      intro q hq
      have hqData := mem_primesUpTo.mp hq
      have hqR : q < R := by omega
      have he := lowWheelFrozenSecondContactHighOwnerWindow_endpoints
        hqData.1 hqR
      unfold lowWheelFrozenSecondContactHighOwnerWindowMass
      exact frozenPrimeUniverseWindowMass_eq_sub he.2
    _ = (∑ q ∈ primesUpTo (R - 1),
          frozenPrimeUniverseMass (primesUpTo (q - 1))
            (squareRootEndpoint R / q)) -
        ∑ q ∈ primesUpTo (R - 1),
          frozenPrimeUniverseMass (primesUpTo (q - 1))
            (max R (squareRootEndpoint R / (q * q))) := by
      rw [Finset.sum_sub_distrib]
    _ = (1 - frozenPrimeUniverseMass (primesUpTo (R - 1))
          (squareRootEndpoint R)) -
        ∑ q ∈ primesUpTo (R - 1),
          frozenPrimeUniverseMass (primesUpTo (q - 1))
            (max R (squareRootEndpoint R / (q * q))) := by
      rw [frozenPrimeUniverse_upperColumn_telescope
        (squareRootEndpoint R) (R - 1) hX]

/-- Multiplying a #630 child by anything strictly larger than its canonical
largest-prime owner necessarily crosses the square endpoint, so it cannot stay
in the arithmetic child carrier. -/
theorem lowWheelFrozenSecondContactArithmeticChild_mul_gt_owner_not_mem
    {R n p : ℕ}
    (hn : n ∈ lowWheelFrozenSecondContactArithmeticChildCarrier R)
    (hp : canonicalLargestPrimeFactor n < p) :
    p * n ∉ lowWheelFrozenSecondContactArithmeticChildCarrier R := by
  intro hpn
  rcases Finset.mem_filter.mp hn with
    ⟨hnIcc, _hsq, _hqR, hsecond, _hroot⟩
  have hnPos : 0 < n := by
    have hnLower := (Finset.mem_Icc.mp hnIcc).1
    omega
  have hgrow :
      n * canonicalLargestPrimeFactor n < n * p :=
    Nat.mul_lt_mul_of_pos_left hp hnPos
  have hcross : squareRootEndpoint R < p * n := by
    calc
      squareRootEndpoint R < n * canonicalLargestPrimeFactor n := hsecond
      _ < n * p := hgrow
      _ = p * n := by ac_rfl
  have hpnUpper :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hpn).1).2
  omega

/-- Deleting the canonical largest-prime owner from a #630 child destroys the
second-contact wall: the new owner is strictly smaller, while the old child was
already at or below the physical endpoint. -/
theorem lowWheelFrozenSecondContactArithmeticChild_canonicalCofactor_not_mem
    {R n : ℕ}
    (hn : n ∈ lowWheelFrozenSecondContactArithmeticChildCarrier R) :
    canonicalCofactor n ∉ lowWheelFrozenSecondContactArithmeticChildCarrier R := by
  intro hcMem
  let q := canonicalLargestPrimeFactor n
  let c := canonicalCofactor n
  have hborn : q ∈ squareRootBornPartnerSet R c ∧
      R < c ∧ squareRootEndpoint R < q * q * c ∧ c * q = n := by
    simpa [q, c] using
      lowWheelFrozenSecondContactArithmeticChild_bornTail_data hn
  rcases Finset.mem_filter.mp hborn.1 with
    ⟨_hqRange, _hqPrime, hrough, _hqLeC, _hupper⟩
  have hcPos : 0 < c := by omega
  have hnewGrow :
      c * canonicalLargestPrimeFactor c < c * q :=
    Nat.mul_lt_mul_of_pos_left hrough hcPos
  rcases Finset.mem_filter.mp hn with ⟨hnIcc, _⟩
  have hnUpper := (Finset.mem_Icc.mp hnIcc).2
  rcases Finset.mem_filter.mp hcMem with
    ⟨_hcIcc, _hcsq, _hrR, hcSecond, _hcRoot⟩
  have htooHigh : squareRootEndpoint R < n := by
    calc
      squareRootEndpoint R <
          c * canonicalLargestPrimeFactor c := by
            simpa [c] using hcSecond
      _ < c * q := hnewGrow
      _ = n := hborn.2.2.2
  omega

/-- Consequently, a fresh multiplicative edge which remains inside the #630
carrier can only use a coordinate strictly below the old canonical owner. -/
theorem lowWheelFrozenSecondContactArithmeticChild_fresh_mul_mem_forces_lt_owner
    {R n p : ℕ}
    (hn : n ∈ lowWheelFrozenSecondContactArithmeticChildCarrier R)
    (hfresh : ¬ p ∣ n)
    (hpn : p * n ∈ lowWheelFrozenSecondContactArithmeticChildCarrier R) :
    p < canonicalLargestPrimeFactor n := by
  have hle : p ≤ canonicalLargestPrimeFactor n := by
    by_contra hnot
    have hgt : canonicalLargestPrimeFactor n < p := Nat.lt_of_not_ge hnot
    exact (lowWheelFrozenSecondContactArithmeticChild_mul_gt_owner_not_mem hn hgt) hpn
  by_contra hnot
  have hownerLe : canonicalLargestPrimeFactor n ≤ p := Nat.le_of_not_gt hnot
  have heq : p = canonicalLargestPrimeFactor n := Nat.le_antisymm hle hownerLe
  have hnLower :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
  have hn1 : 1 < n := by omega
  have hdiv : canonicalLargestPrimeFactor n ∣ n :=
    canonicalLargestPrimeFactor_dvd hn1
  apply hfresh
  simpa [heq] using hdiv

end RHLean.Proof

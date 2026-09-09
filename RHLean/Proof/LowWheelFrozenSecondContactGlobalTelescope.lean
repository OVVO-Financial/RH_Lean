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

The last section adds the reciprocal-depth coordinate exposed by the two #630
walls.  For a child `n` with owner `q = P+(n)`, put `k = floor(X_R/n)`.
Then `k < q` and, much more importantly, `q*k < R`; hence `k^2 < R`.
Thus every saturated second-contact child starts in a genuinely sub-square-root
reciprocal layer.  Removing a divisor from the child can only increase this
reciprocal depth multiplicatively.  This is the monotone coordinate needed by
the descending-owner Euler descent: owner depth decreases while reciprocal
depth climbs toward the root.
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

/-! ## Reciprocal-depth descent coordinate -/

/-- The reciprocal depth `floor(X_R/n)` is strictly below the canonical owner.
This is the quotient form of the #630 second-contact wall `X_R < n*P+(n)`. -/
theorem lowWheelFrozenSecondContactArithmeticChild_reciprocalDepth_lt_owner
    {R n : ℕ}
    (hn : n ∈ lowWheelFrozenSecondContactArithmeticChildCarrier R) :
    squareRootEndpoint R / n < canonicalLargestPrimeFactor n := by
  rcases Finset.mem_filter.mp hn with
    ⟨hnIcc, _hsq, _hqR, hsecond, _hroot⟩
  have hnPos : 0 < n := by
    have hnLower := (Finset.mem_Icc.mp hnIcc).1
    omega
  apply (Nat.div_lt_iff_lt_mul hnPos).2
  simpa [Nat.mul_comm] using hsecond

/-- The stronger hyperbolic localization: owner times reciprocal depth is still
strictly below the root.  This combines the post-root cofactor wall
`R*P+(n) < n` with `n*floor(X_R/n) <= X_R < R^2`. -/
theorem lowWheelFrozenSecondContactArithmeticChild_owner_mul_reciprocalDepth_lt_root
    {R n : ℕ}
    (hn : n ∈ lowWheelFrozenSecondContactArithmeticChildCarrier R) :
    canonicalLargestPrimeFactor n * (squareRootEndpoint R / n) < R := by
  rcases Finset.mem_filter.mp hn with
    ⟨hnIcc, _hsq, hqR, _hsecond, hroot⟩
  have hnPos : 0 < n := by
    have hnLower := (Finset.mem_Icc.mp hnIcc).1
    omega
  have hn1 : 1 < n := by
    have hnLower := (Finset.mem_Icc.mp hnIcc).1
    omega
  have hqPrime := canonicalLargestPrimeFactor_prime hn1
  have hRPos : 0 < R := hqPrime.pos.trans hqR
  let k := squareRootEndpoint R / n
  by_cases hk : k = 0
  · simp [k, hk, hRPos]
  · have hkPos : 0 < k := Nat.pos_of_ne_zero hk
    have hleft :
        (R * canonicalLargestPrimeFactor n) * k < n * k :=
      Nat.mul_lt_mul_of_pos_right hroot hkPos
    have hnk : n * k ≤ squareRootEndpoint R := by
      simpa [k, Nat.mul_comm] using Nat.div_mul_le_self (squareRootEndpoint R) n
    have hXlt : squareRootEndpoint R < R * R := by
      unfold squareRootEndpoint
      have hsqPos : 0 < R ^ 2 := by positivity
      omega
    have hmul :
        R * (canonicalLargestPrimeFactor n * k) < R * R := by
      calc
        R * (canonicalLargestPrimeFactor n * k) =
            (R * canonicalLargestPrimeFactor n) * k := by ring
        _ < n * k := hleft
        _ ≤ squareRootEndpoint R := hnk
        _ < R * R := hXlt
    have hkRoot : canonicalLargestPrimeFactor n * k < R :=
      Nat.lt_of_mul_lt_mul_left hmul
    simpa [k] using hkRoot

/-- The child itself lies beyond the geometric mean of the root and square
endpoint: `R*X_R < n^2`.  This is the product form of the two #630 walls. -/
theorem lowWheelFrozenSecondContactArithmeticChild_root_mul_endpoint_lt_sq
    {R n : ℕ}
    (hn : n ∈ lowWheelFrozenSecondContactArithmeticChildCarrier R) :
    R * squareRootEndpoint R < n * n := by
  rcases Finset.mem_filter.mp hn with
    ⟨hnIcc, _hsq, hqR, hsecond, hroot⟩
  have hnPos : 0 < n := by
    have hnLower := (Finset.mem_Icc.mp hnIcc).1
    omega
  have hn1 : 1 < n := by
    have hnLower := (Finset.mem_Icc.mp hnIcc).1
    omega
  have hqPrime := canonicalLargestPrimeFactor_prime hn1
  have hRPos : 0 < R := hqPrime.pos.trans hqR
  calc
    R * squareRootEndpoint R <
        R * (n * canonicalLargestPrimeFactor n) :=
      Nat.mul_lt_mul_of_pos_left hsecond hRPos
    _ = n * (R * canonicalLargestPrimeFactor n) := by ring
    _ < n * n := Nat.mul_lt_mul_of_pos_left hroot hnPos

/-- **Sub-square-root reciprocal depth.**  Every #630 child belongs to a
reciprocal layer `k` with `k^2 < R`.  This is the exponent-changing support
localization: the saturated second-contact population begins in only the first
square-root many reciprocal depths. -/
theorem lowWheelFrozenSecondContactArithmeticChild_reciprocalDepth_sq_lt_root
    {R n : ℕ}
    (hn : n ∈ lowWheelFrozenSecondContactArithmeticChildCarrier R) :
    (squareRootEndpoint R / n) * (squareRootEndpoint R / n) < R := by
  let k := squareRootEndpoint R / n
  have hkq : k < canonicalLargestPrimeFactor n := by
    simpa [k] using
      lowWheelFrozenSecondContactArithmeticChild_reciprocalDepth_lt_owner hn
  have hqk : canonicalLargestPrimeFactor n * k < R := by
    simpa [k] using
      lowWheelFrozenSecondContactArithmeticChild_owner_mul_reciprocalDepth_lt_root hn
  by_cases hk : k = 0
  · subst k
    have hn1 : 1 < n := by
      have hnLower :=
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
      omega
    have hqR := (Finset.mem_filter.mp hn).2.2.1
    have hqPrime := canonicalLargestPrimeFactor_prime hn1
    have hRPos : 0 < R := hqPrime.pos.trans hqR
    simpa using hRPos
  · have hkPos : 0 < k := Nat.pos_of_ne_zero hk
    have hkk : k * k < canonicalLargestPrimeFactor n * k :=
      Nat.mul_lt_mul_of_pos_right hkq hkPos
    exact hkk.trans hqk

/-- Removing a positive divisor from an integer can only increase reciprocal
depth by at least that divisor.  This generic floor inequality is the monotone
engine for descending-owner induction. -/
theorem reciprocalDepth_mul_divisor_le_strippedDepth
    {X n r : ℕ} (hn : 0 < n) (hr : 0 < r) (hrDvd : r ∣ n) :
    r * (X / n) ≤ X / (n / r) := by
  have hrLe : r ≤ n := Nat.le_of_dvd hn hrDvd
  have hquotPos : 0 < n / r := Nat.div_pos hrLe hr
  apply (Nat.le_div_iff_mul_le hquotPos).2
  calc
    r * (X / n) * (n / r) =
        (X / n) * ((n / r) * r) := by ring
    _ = (X / n) * n := by rw [Nat.div_mul_cancel hrDvd]
    _ ≤ X := Nat.div_mul_le_self X n

/-! ## Intrinsic lower-scale exit carried by every source -/

/-- **Strict source-scale descent.**  A frozen second-contact source already
contains its own smaller cutoff.  If

`A = p * P(t)`

is its root-crossing/death coordinate and

`B = floor(X_R / A)`,

then the frozen cofactor `c` lies in the exact largest-prime exit shell

`c <= B < P+(c) * c`,

and the new cutoff is strictly below the old root, `B < R`.

Thus the second-contact obstruction at the square endpoint `R^2-1` is
pointwise a multiplicative endpoint crossing at a genuinely smaller numerical
scale.  No sum, norm, density input, or analytic estimate is used. -/
theorem lowWheelFrozenSecondContact_source_lowerScaleExit
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    let A := lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1
    let B := squareRootEndpoint R / A
    let q := lowWheelFrozenCofactorTopPrime y
    y.2.1 ≤ B ∧ B < q * y.2.1 ∧ B < R := by
  rcases Finset.mem_filter.mp hy with ⟨hyFrozen, hsecond⟩
  let A := lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1
  let B := squareRootEndpoint R / A
  let q := lowWheelFrozenCofactorTopPrime y
  have hAroot : R < A := by
    simpa [A] using
      lowWheelCanonicalRepeatedFrozenCofactor_facePivot_crosses_root hyFrozen
  have hApos : 0 < A := by omega
  rcases lowWheelCanonicalRepeatedFrozenCofactor_source_data hyFrozen with
    ⟨_hk, _hpPrime, _hpNotC, _hsq, hcgt, hcR⟩
  have hRpos : 0 < R := by omega
  have htop :
      primeFaceProduct (lowWheelCanonicalRepeatedFrozenProductOneFace y) ≤
        squareRootEndpoint R :=
    lowWheelFrozenProductOneFace_le_endpoint hyFrozen
  have hprod := lowWheelCanonicalRepeatedFrozenProductOneFace_product hyFrozen
  have hcA : y.2.1 * A ≤ squareRootEndpoint R := by
    calc
      y.2.1 * A =
          y.2.1 * lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1 := by
        simp [A]
        ring
      _ = primeFaceProduct
          (lowWheelCanonicalRepeatedFrozenProductOneFace y) := hprod.symm
      _ ≤ squareRootEndpoint R := htop
  have hcB : y.2.1 ≤ B := by
    unfold B
    exact (Nat.le_div_iff_mul_le hApos).2 hcA
  have hqca :
      squareRootEndpoint R < (q * y.2.1) * A := by
    calc
      squareRootEndpoint R <
          q * primeFaceProduct
            (lowWheelCanonicalRepeatedFrozenProductOneFace y) := by
        simpa [q] using hsecond
      _ = (q * y.2.1) * A := by
        rw [hprod]
        simp [A]
        ring
  have hBq : B < q * y.2.1 := by
    unfold B
    exact (Nat.div_lt_iff_lt_mul hApos).2 hqca
  have hXltRR : squareRootEndpoint R < R * R := by
    unfold squareRootEndpoint
    have hsqPos : 0 < R ^ 2 := by positivity
    simpa [pow_two] using Nat.pred_lt hsqPos
  have hRRltRA : R * R < R * A :=
    Nat.mul_lt_mul_of_pos_left hAroot hRpos
  have hXltRA : squareRootEndpoint R < R * A :=
    hXltRR.trans hRRltRA
  have hBR : B < R := by
    unfold B
    exact (Nat.div_lt_iff_lt_mul hApos).2 hXltRA
  exact ⟨hcB, hBq, hBR⟩

end RHLean.Proof

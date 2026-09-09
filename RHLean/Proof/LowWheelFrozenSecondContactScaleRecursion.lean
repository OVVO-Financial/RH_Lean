import Mathlib
import RHLean.Proof.LowWheelFrozenSecondContactGlobalTelescope
import RHLean.Proof.LowWheelFrozenSecondContactWindowDescent
import RHLean.Proof.SquareRootLowPrimeGoHyperbolicStripRecursion

/-!
# Strict lower-scale recursion for frozen second contacts

The factorization compiled in `LowWheelFrozenSecondContactGlobalTelescope`
places every frozen second-contact source at a strictly smaller cutoff

`B = floor(X_R / A) < R`

with

`c = q*d`, `q*d <= B < q^2*d`, `P+(d) < q`.

This file turns that pointwise factorization into the exact recursive window
needed for induction.  The stripped tail `d` is a literal face of

`W_q(B) = W(primes < q; B/q^2, B/q)`.

There are then only two cases.

* If `q^2 <= B`, the entire signed window descends, before any norm, to windows
  with strictly smaller owner `r < q`.
* If `B < q^2`, the lower endpoint is zero and the upper endpoint is already
  below `q`; hence the whole window is the completed ordinary Mertens prefix
  `M(floor(B/q))`.

Thus the recursion has no unclassified defect: every nonterminal node has a
strict owner descent and every terminal node is a completed Mertens leaf.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- The stripped cofactor furnished by the strict source-scale factorization is
literally a face in the lower-scale second-contact window. -/
theorem lowWheelFrozenSecondContact_source_strippedFace_mem_lowerScaleWindow
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    let A := lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1
    let B := squareRootEndpoint R / A
    let c := y.2.1
    let q := lowWheelFrozenCofactorTopPrime y
    let d := canonicalCofactor c
    squarefreePrimeFace d ∈
      frozenPrimeUniverseWindowFaces (primesUpTo (q - 1))
        (B / (q * q)) (B / q) := by
  let A := lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1
  let B := squareRootEndpoint R / A
  let c := y.2.1
  let q := lowWheelFrozenCofactorTopPrime y
  let d := canonicalCofactor c
  have hdata :
      q.Prime ∧ Squarefree d ∧ canonicalLargestPrimeFactor d < q ∧
        q * d = c ∧ q * d ≤ B ∧ B < q * q * d ∧ B < R := by
    simpa [A, B, c, q, d] using
      (lowWheelFrozenSecondContact_source_lowerScaleSecondContact hy)
  rcases hdata with
    ⟨hqPrime, hdSq, hrough, _hfactor, hqdB, hBqqd, _hBR⟩
  have hyFrozen := (Finset.mem_filter.mp hy).1
  rcases lowWheelCanonicalRepeatedFrozenCofactor_source_data hyFrozen with
    ⟨_hk, _hpPrime, _hpNotC, _hcsq, hcgtRaw, _hcR⟩
  have hcgt : 1 < c := by simpa [c] using hcgtRaw
  have hdPos : 0 < d := by
    have hdOne : 1 ≤ canonicalCofactor c :=
      CanonicalGapAncestryBridge.canonicalCofactor_pos hcgt
    simpa [d] using hdOne
  let t := squarefreePrimeFace d
  have htProd : primeFaceProduct t = d := by
    simpa [t] using primeFaceProduct_squarefreePrimeFace hdSq
  have htSub : t ⊆ primesUpTo (q - 1) := by
    intro r hr
    have hrFactors : r ∈ d.primeFactors := by
      simpa [t, squarefreePrimeFace] using hr
    have hrData := Nat.mem_primeFactors.mp hrFactors
    have hrPrime : r.Prime := hrData.1
    have hrDvd : r ∣ d := hrData.2.1
    have hrLeD : r ≤ d := Nat.le_of_dvd hdPos hrDvd
    have hdGt : 1 < d := hrPrime.one_lt.trans_le hrLeD
    have hrLeTop : r ≤ canonicalLargestPrimeFactor d := by
      unfold canonicalLargestPrimeFactor
      rw [dif_pos hdGt]
      exact Finset.le_max' d.primeFactors r hrFactors
    exact mem_primesUpTo.mpr ⟨hrPrime, by omega⟩
  have hqSqPos : 0 < q * q := Nat.mul_pos hqPrime.pos hqPrime.pos
  have hlo : B / (q * q) < d := by
    apply (Nat.div_lt_iff_lt_mul hqSqPos).2
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hBqqd
  have hup : d ≤ B / q := by
    apply (Nat.le_div_iff_mul_le hqPrime.pos).2
    simpa [Nat.mul_comm] using hqdB
  apply mem_frozenPrimeUniverseWindowFaces.mpr
  exact ⟨Finset.mem_powerset.mpr htSub, by simpa [htProd], by simpa [htProd]⟩

/-- Interior recursion.  Once the lower square endpoint is positive, the whole
lower-scale second-contact window descends signed to strictly smaller owners.
No absolute value is introduced. -/
theorem lowWheelFrozenSecondContact_lowerScaleWindowMass_eq_neg_smallerOwners
    {q B : ℕ} (hq : q.Prime) (hsquare : q * q ≤ B) :
    frozenPrimeUniverseWindowMass (primesUpTo (q - 1))
        (B / (q * q)) (B / q) =
      -∑ r ∈ primesUpTo (q - 1),
        frozenPrimeUniverseWindowMass (primesUpTo (r - 1))
          ((B / (q * q)) / r) ((B / q) / r) := by
  have hqSqPos : 0 < q * q := Nat.mul_pos hq.pos hq.pos
  have hlowPos : 1 ≤ B / (q * q) := by
    apply (Nat.le_div_iff_mul_le hqSqPos).2
    simpa using hsquare
  have hqLeSq : q ≤ q * q := by
    have hqOne : 1 ≤ q := hq.one_le
    simpa using Nat.mul_le_mul_left q hqOne
  have hmono : B / (q * q) ≤ B / q :=
    Nat.div_le_div_left hqLeSq hq.pos
  exact frozenPrimeUniverseWindowMass_eq_neg_smallerOwnerWindows
    (q - 1) hlowPos hmono

/-- Terminal recursion.  Across `B < q^2` the lower endpoint is zero and the
upper endpoint lies strictly below the owner, so the entire frozen window has
already completed to an ordinary Mertens prefix. -/
theorem lowWheelFrozenSecondContact_lowerScaleWindowMass_eq_mertens_of_crossing
    {q B : ℕ} (hq : q.Prime) (hcross : B < q * q) :
    frozenPrimeUniverseWindowMass (primesUpTo (q - 1))
        (B / (q * q)) (B / q) =
      mertensSummatoryInt (B / q) := by
  have hlowZero : B / (q * q) = 0 := Nat.div_eq_of_lt hcross
  have hupper : B / q < q := by
    apply (Nat.div_lt_iff_lt_mul hq.pos).2
    simpa [Nat.mul_comm] using hcross
  have hmono : B / (q * q) ≤ B / q := by
    rw [hlowZero]
    omega
  calc
    frozenPrimeUniverseWindowMass (primesUpTo (q - 1))
        (B / (q * q)) (B / q) =
      frozenPrimeUniverseMass (primesUpTo (q - 1)) (B / q) -
        frozenPrimeUniverseMass (primesUpTo (q - 1)) (B / (q * q)) :=
      frozenPrimeUniverseWindowMass_eq_sub hmono
    _ = mertensSummatoryInt (B / q) - mertensSummatoryInt 0 := by
      rw [hlowZero,
        frozenPrimeUniverseMass_eq_mertensSummatoryInt_of_lt_owner hq hupper,
        frozenPrimeUniverseMass_eq_mertensSummatoryInt_of_lt_owner hq hq.pos]
    _ = mertensSummatoryInt (B / q) := by
      simp [mertensSummatoryInt]

/-- Every strict-source factorization therefore lands in exactly one of the two
recursive regimes at a strictly smaller numerical cutoff.  This packages the
induction interface without choosing either branch prematurely. -/
theorem lowWheelFrozenSecondContact_source_lowerScale_recursion_dichotomy
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    let A := lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1
    let B := squareRootEndpoint R / A
    let q := lowWheelFrozenCofactorTopPrime y
    B < R ∧
      ((q * q ≤ B ∧
          frozenPrimeUniverseWindowMass (primesUpTo (q - 1))
              (B / (q * q)) (B / q) =
            -∑ r ∈ primesUpTo (q - 1),
              frozenPrimeUniverseWindowMass (primesUpTo (r - 1))
                ((B / (q * q)) / r) ((B / q) / r)) ∨
       (B < q * q ∧
          frozenPrimeUniverseWindowMass (primesUpTo (q - 1))
              (B / (q * q)) (B / q) =
            mertensSummatoryInt (B / q))) := by
  let A := lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1
  let B := squareRootEndpoint R / A
  let q := lowWheelFrozenCofactorTopPrime y
  let c := y.2.1
  let d := canonicalCofactor c
  have hdata :
      q.Prime ∧ Squarefree d ∧ canonicalLargestPrimeFactor d < q ∧
        q * d = c ∧ q * d ≤ B ∧ B < q * q * d ∧ B < R := by
    simpa [A, B, c, q, d] using
      (lowWheelFrozenSecondContact_source_lowerScaleSecondContact hy)
  rcases hdata with ⟨hq, _hdSq, _hrough, _hfactor, _hqdB, _hBqqd, hBR⟩
  refine ⟨hBR, ?_⟩
  by_cases hsquare : q * q ≤ B
  · exact Or.inl ⟨hsquare,
      lowWheelFrozenSecondContact_lowerScaleWindowMass_eq_neg_smallerOwners
        hq hsquare⟩
  · have hcross : B < q * q := Nat.lt_of_not_ge hsquare
    exact Or.inr ⟨hcross,
      lowWheelFrozenSecondContact_lowerScaleWindowMass_eq_mertens_of_crossing
        hq hcross⟩

end RHLean.Proof

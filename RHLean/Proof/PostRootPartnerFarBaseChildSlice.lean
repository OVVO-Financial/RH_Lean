import Mathlib
import RHLean.Proof.PostRootPartnerLogAlignment

/-!
# Exact common-base / child-far identification

The post-#685 diagnostic showed that the full q² high-transport column and the
stable-far chronology are different source populations.  After telescoping each
far predecessor cube from `p^-` back to the common `q^-` universe, however, the
remaining far-base carrier has exactly the same support as the already-compiled
q² child-far slice:

* the cofactor is squarefree and `q`-smooth;
* the far prime satisfies `p >= R+8`;
* the product satisfies `d*p <= X_R/q²`.

This file proves that local carrier/mass identification exactly.  No norm,
estimate, prime asymptotic, or cancellation hypothesis enters the argument.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Rectangular common-base carrier before the final product cutoff is imposed. -/
private def q2FarBasePairCarrier (R q : ℕ) : Finset (ℕ × ℕ) :=
  let Y := squareRootEndpoint R / (q * q)
  ((squareRootLowPrimeGoSmoothCofactors q Y).product
      (frozenPrimeUniverseHighPrimeSet (R + 7) Y)).filter fun dp =>
    dp.1 * dp.2 ≤ Y

/-- Restricting the q-smooth cofactor cutoff from `Y` to `Y/p` is exactly the
same as retaining the full q-smooth population and imposing `d*p <= Y`. -/
private theorem q2SmoothCofactors_div_eq_filter
    {q Y p : ℕ} (hp : 0 < p) :
    squareRootLowPrimeGoSmoothCofactors q (Y / p) =
      (squareRootLowPrimeGoSmoothCofactors q Y).filter fun d => d * p ≤ Y := by
  ext d
  simp only [Finset.mem_filter, mem_squareRootLowPrimeGoSmoothCofactors]
  constructor
  · rintro ⟨hd1, hdCut, hsq, hrough⟩
    have hmul : d * p ≤ Y := (Nat.le_div_iff_mul_le hp).1 hdCut
    have hdY : d ≤ Y := hdCut.trans (Nat.div_le_self Y p)
    exact ⟨⟨hd1, hdY, hsq, hrough⟩, hmul⟩
  · rintro ⟨⟨hd1, _hdY, hsq, hrough⟩, hmul⟩
    have hdCut : d ≤ Y / p := (Nat.le_div_iff_mul_le hp).2 hmul
    exact ⟨hd1, hdCut, hsq, hrough⟩

/-- **Exact carrier equality.**  The common-q far-base rectangle with the
product cutoff is literally the q² child-far slice. -/
private theorem q2FarBasePairCarrier_eq_childFarSlice
    (R q : ℕ) :
    q2FarBasePairCarrier R q = lowWheelFarPrimeQ2ChildFarSlice R q := by
  ext dp
  rcases dp with ⟨d, p⟩
  simp only [q2FarBasePairCarrier, Finset.mem_filter, Finset.mem_product,
    mem_lowWheelFarPrimeQ2ChildFarSlice]
  constructor
  · rintro ⟨hd, hpHigh, hdp⟩
    rcases mem_frozenPrimeUniverseHighPrimeSet.mp hpHigh with
      ⟨hpPrime, hpLower, hpUpper⟩
    have hpRange : p ∈ Finset.Icc (R + 8) (squareRootEndpoint R) := by
      apply Finset.mem_Icc.mpr
      refine ⟨?_, ?_⟩
      · omega
      · exact hpUpper.trans
          (Nat.div_le_self (squareRootEndpoint R) (q * q))
    exact ⟨hd, hpRange, hpPrime, hdp⟩
  · rintro ⟨hd, hpRange, hpPrime, hdp⟩
    have hd1 : 1 ≤ d :=
      (mem_squareRootLowPrimeGoSmoothCofactors.mp hd).1
    have hpLeDp : p ≤ d * p := by
      simpa using Nat.mul_le_mul_right p hd1
    have hpUpper : p ≤ squareRootEndpoint R / (q * q) :=
      hpLeDp.trans hdp
    have hpLower : R + 8 ≤ p := (Finset.mem_Icc.mp hpRange).1
    have hpHigh :
        p ∈ frozenPrimeUniverseHighPrimeSet
          (R + 7) (squareRootEndpoint R / (q * q)) :=
      mem_frozenPrimeUniverseHighPrimeSet.mpr
        ⟨hpPrime, by omega, hpUpper⟩
    exact ⟨hd, hpHigh, hdp⟩

/-- The common-q far-base column is the integer Möbius mass of the exact pair
carrier.  This is finite Fubini only. -/
private theorem q2DaughterFarBaseColumn_eq_pairCarrierMass
    {R q : ℕ} (hq : q.Prime) :
    q2DaughterFarBaseColumn R q =
      ∑ dp ∈ q2FarBasePairCarrier R q, μ dp.1 := by
  let Y := squareRootEndpoint R / (q * q)
  unfold q2DaughterFarBaseColumn q2FarBasePairCarrier
  change
    (∑ p ∈ frozenPrimeUniverseHighPrimeSet (R + 7) Y,
      frozenPrimeUniverseMass (primesUpTo (q - 1)) (Y / p)) =
      ∑ dp ∈
        ((squareRootLowPrimeGoSmoothCofactors q Y).product
          (frozenPrimeUniverseHighPrimeSet (R + 7) Y)).filter
            (fun dp => dp.1 * dp.2 ≤ Y),
        μ dp.1
  calc
    (∑ p ∈ frozenPrimeUniverseHighPrimeSet (R + 7) Y,
        frozenPrimeUniverseMass (primesUpTo (q - 1)) (Y / p)) =
      ∑ p ∈ frozenPrimeUniverseHighPrimeSet (R + 7) Y,
        ∑ d ∈ squareRootLowPrimeGoSmoothCofactors q (Y / p), μ d := by
          apply Finset.sum_congr rfl
          intro p _hp
          exact frozenPrimeUniverseMass_eq_goSmoothCofactorSum hq
    _ = ∑ p ∈ frozenPrimeUniverseHighPrimeSet (R + 7) Y,
        ∑ d ∈ squareRootLowPrimeGoSmoothCofactors q Y,
          if d * p ≤ Y then μ d else 0 := by
          apply Finset.sum_congr rfl
          intro p hp
          have hpPrime := (mem_frozenPrimeUniverseHighPrimeSet.mp hp).1
          rw [q2SmoothCofactors_div_eq_filter hpPrime.pos, Finset.sum_filter]
    _ = ∑ d ∈ squareRootLowPrimeGoSmoothCofactors q Y,
        ∑ p ∈ frozenPrimeUniverseHighPrimeSet (R + 7) Y,
          if d * p ≤ Y then μ d else 0 := by
          exact Finset.sum_comm
    _ = ∑ dp ∈
        (squareRootLowPrimeGoSmoothCofactors q Y).product
          (frozenPrimeUniverseHighPrimeSet (R + 7) Y),
        if dp.1 * dp.2 ≤ Y then μ dp.1 else 0 := by
          symm
          simpa only using
            (Finset.sum_product
              (s := squareRootLowPrimeGoSmoothCofactors q Y)
              (t := frozenPrimeUniverseHighPrimeSet (R + 7) Y)
              (f := fun dp : ℕ × ℕ =>
                if dp.1 * dp.2 ≤ Y then μ dp.1 else 0))
    _ = ∑ dp ∈
        ((squareRootLowPrimeGoSmoothCofactors q Y).product
          (frozenPrimeUniverseHighPrimeSet (R + 7) Y)).filter
            (fun dp => dp.1 * dp.2 ≤ Y),
        μ dp.1 := by
          rw [Finset.sum_filter]

/-- Ownerwise common-base mass equals the already-compiled child-far mass in
complex Möbius currency. -/
theorem q2DaughterFarBaseColumn_cast_eq_childFarSliceMass
    {R q : ℕ} (hq : q.Prime) :
    ((q2DaughterFarBaseColumn R q : ℤ) : ℂ) =
      ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
        canonicalMoebiusWeight dp.1 := by
  have h := q2DaughterFarBaseColumn_eq_pairCarrierMass (R := R) (q := q) hq
  rw [q2FarBasePairCarrier_eq_childFarSlice R q] at h
  have hcast := congrArg (fun z : ℤ => (z : ℂ)) h
  push_cast at hcast
  simpa [canonicalMoebiusWeight] using hcast

/-- **The local bridge left after the failed full-support splice is true.**
Summing the ownerwise carrier identity proves the named common-base/child-far
match without any root-scale estimate. -/
theorem farBaseChildSliceMatch : FarBaseChildSliceMatch := by
  intro R _hR
  unfold squareEndpointQ2FarBaseColumn squareEndpointQ2ChildFarSliceColumn
  push_cast
  apply Finset.sum_congr rfl
  intro q hq
  exact q2DaughterFarBaseColumn_cast_eq_childFarSliceMass
    (mem_primesUpTo.mp hq).1

/-- The corrected transport/far mismatch seam is therefore unconditional: the
only surviving terms are near high transport, the q²-or-deeper intermediate
prime tower, stable renewal, and the terminal population. -/
theorem q2TransportFarMismatch_eq_compiled_near_sub_tower_sub_renewal_sub_terminal
    (R : ℕ) (hR : 56 ≤ R) :
    q2TransportFarMismatch R =
      (((squareEndpointQ2NearHighTransportColumn R : ℤ) : ℂ)) -
        (((squareEndpointQ2IntermediatePrimeTower R : ℤ) : ℂ)) -
        stableFarRenewalColumn R - stableFarTerminalProductColumn R :=
  q2TransportFarMismatch_eq_near_sub_tower_sub_renewal_sub_terminal
    farBaseChildSliceMatch R hR

end RHLean.Proof

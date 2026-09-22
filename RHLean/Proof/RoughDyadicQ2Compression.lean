import RHLean.Analysis.DyadicTransportCompression
import RHLean.Analysis.SquareRootBornSmoothReciprocalForm
import RHLean.Proof.LowWheelFrozenSecondContactScaleFlux
import RHLean.Proof.PostRootPartnerLogAlignment
import RHLean.Proof.SquareRootLowPrimeGoAncestryClock
import RHLean.Proof.SquareWheelSurvivorProcessedResponseBridge
import RHLean.Proof.SurvivorDyadicActivityMismatch

/-!
# Rough dyadic compression of q^2 daughters

The ordinary dyadic Mobius compression pairs an odd cofactor `d` with `2*d`.
For a q^2 daughter the cofactor is not an unrestricted Mertens prefix: it is
restricted to the predecessor wheel `P+(d) < q`.

For every odd prime owner `q > 2`, adjoining the prime coordinate 2 preserves
that predecessor-wheel condition on every nonzero Mobius atom.  Hence the same
exact cancellation works *inside the q-rough carrier* before any norm is taken.

The owner `q = 2` is intentionally excluded.  It is the distinguished
prime-two coordinate itself and remains the explicit owner-two term already
kept signed by the FAR synthesis.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- The q-rough part of the ordinary odd dyadic boundary. -/
def roughDyadicCofactorBoundary (q B : ℕ) : Finset ℕ :=
  (dyadicCofactorBoundary B).filter fun d =>
    canonicalLargestPrimeFactor d < q

/-- Signed Mobius mass of the q-rough odd dyadic boundary. -/
def roughDyadicCofactorBoundaryMass (q B : ℕ) : ℂ :=
  ∑ d ∈ roughDyadicCofactorBoundary q B, canonicalMoebiusWeight d

@[simp] theorem mem_roughDyadicCofactorBoundary {q B d : ℕ} :
    d ∈ roughDyadicCofactorBoundary q B ↔
      d ∈ dyadicCofactorBoundary B ∧ canonicalLargestPrimeFactor d < q := by
  simp [roughDyadicCofactorBoundary]

private def roughDyadicWeight (q d : ℕ) : ℂ :=
  if canonicalLargestPrimeFactor d < q then canonicalMoebiusWeight d else 0

/-- On a squarefree odd parent, the predecessor-wheel condition is invariant
under adjoining the coordinate 2. -/
private theorem rough_two_mul_iff_of_odd_squarefree
    {q d : ℕ} (hq : q.Prime) (hqgt : 2 < q)
    (hd : Odd d) (hd1 : 1 ≤ d) (hsq : Squarefree d) :
    canonicalLargestPrimeFactor (2 * d) < q ↔
      canonicalLargestPrimeFactor d < q := by
  have h2copd : Nat.Coprime 2 d := hd.coprime_two_left
  have hsq2 : Squarefree (2 * d) :=
    (Nat.squarefree_mul h2copd).2 ⟨Nat.squarefree_two, hsq⟩
  constructor
  · intro hrough2
    have hdata2 : CanonicalSourceData q (2 * d) :=
      squareRootLowPrimeGo_canonicalSourceData_of_rough
        hq (by omega) hsq2 hrough2
    have hdata : CanonicalSourceData q d :=
      (canonicalSourceData_two_mul_iff_of_odd hd hqgt).mp hdata2
    exact canonicalLargestPrimeFactor_lt_of_sourceData hdata
  · intro hrough
    have hdata : CanonicalSourceData q d :=
      squareRootLowPrimeGo_canonicalSourceData_of_rough
        hq hd1 hsq hrough
    have hdata2 : CanonicalSourceData q (2 * d) :=
      (canonicalSourceData_two_mul_iff_of_odd hd hqgt).mpr hdata
    exact canonicalLargestPrimeFactor_lt_of_sourceData hdata2

/-- Exact masked doubling law.  The q-rough mask commutes with the prime-two
Mobius cancellation for every odd owner q.  Nonsquarefree parents vanish on
both sides, so no hidden support assumption is introduced. -/
private theorem roughDyadicWeight_two_mul
    (q d : ℕ) (hq : q.Prime) (hqgt : 2 < q) :
    roughDyadicWeight q (2 * d) =
      if Odd d then -roughDyadicWeight q d else 0 := by
  by_cases hd : Odd d
  · rw [if_pos hd]
    by_cases hsq : Squarefree d
    · have hd1 : 1 ≤ d := by
        rcases hd with ⟨k, hk⟩
        omega
      have hroughIff :=
        rough_two_mul_iff_of_odd_squarefree hq hqgt hd hd1 hsq
      by_cases hrough : canonicalLargestPrimeFactor d < q
      · have hrough2 : canonicalLargestPrimeFactor (2 * d) < q :=
          hroughIff.mpr hrough
        unfold roughDyadicWeight
        rw [if_pos hrough, if_pos hrough2,
          canonicalMoebiusWeight_two_mul, if_pos hd]
      · have hrough2 : ¬ canonicalLargestPrimeFactor (2 * d) < q := by
          intro h
          exact hrough (hroughIff.mp h)
        unfold roughDyadicWeight
        rw [if_neg hrough, if_neg hrough2]
        ring
    · have hmuZ : μ d = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
      have hmu : canonicalMoebiusWeight d = 0 := by
        simp [canonicalMoebiusWeight, hmuZ]
      have hmu2 : canonicalMoebiusWeight (2 * d) = 0 := by
        rw [canonicalMoebiusWeight_two_mul, if_pos hd, hmu, neg_zero]
      unfold roughDyadicWeight
      split_ifs <;> simp [hmu, hmu2]
  · rw [if_neg hd]
    have hmu2 : canonicalMoebiusWeight (2 * d) = 0 := by
      rw [canonicalMoebiusWeight_two_mul, if_neg hd]
    unfold roughDyadicWeight
    split_ifs <;> simp [hmu2]

private theorem rough_sum_Icc_eq_odd_add_even
    (q B : ℕ) :
    (∑ d ∈ Finset.Icc 1 B, roughDyadicWeight q d) =
      (∑ d ∈ oddCofactorPrefix B, roughDyadicWeight q d) +
        ∑ d ∈ evenCofactorPrefix B, roughDyadicWeight q d := by
  calc
    (∑ d ∈ Finset.Icc 1 B, roughDyadicWeight q d) =
        ∑ d ∈ Finset.Icc 1 B,
          ((if Odd d then roughDyadicWeight q d else 0) +
            (if Even d then roughDyadicWeight q d else 0)) := by
      apply Finset.sum_congr rfl
      intro d _hd
      by_cases hodd : Odd d
      · have hnotEven : ¬ Even d := Nat.not_even_iff_odd.mpr hodd
        simp [hodd, hnotEven]
      · have heven : Even d := Nat.not_odd_iff_even.mp hodd
        simp [hodd, heven]
    _ =
        (∑ d ∈ oddCofactorPrefix B, roughDyadicWeight q d) +
          ∑ d ∈ evenCofactorPrefix B, roughDyadicWeight q d := by
      rw [Finset.sum_add_distrib]
      unfold oddCofactorPrefix evenCofactorPrefix
      rw [Finset.sum_filter, Finset.sum_filter]

private theorem rough_sum_even_eq_sum_double
    (q B : ℕ) :
    (∑ d ∈ evenCofactorPrefix B, roughDyadicWeight q d) =
      ∑ e ∈ Finset.Icc 1 (B / 2), roughDyadicWeight q (2 * e) := by
  classical
  symm
  refine Finset.sum_bij (fun e _ => 2 * e) ?_ ?_ ?_ ?_
  · intro e he
    rcases Finset.mem_Icc.mp he with ⟨he1, heB⟩
    have h2eB : 2 * e ≤ B := by
      have hmul := (Nat.le_div_iff_mul_le (by omega : 0 < 2)).1 heB
      simpa [Nat.mul_comm] using hmul
    exact mem_evenCofactorPrefix.mpr
      ⟨by omega, h2eB, even_two_mul e⟩
  · intro e1 _he1 e2 _he2 h
    change 2 * e1 = 2 * e2 at h
    omega
  · intro d hd
    rcases mem_evenCofactorPrefix.mp hd with ⟨hd1, hdB, hdeven⟩
    have hdouble : 2 * (d / 2) = d := Nat.two_mul_div_two_of_even hdeven
    refine ⟨d / 2, ?_, hdouble⟩
    apply Finset.mem_Icc.mpr
    constructor
    · have hdne : d ≠ 0 := by omega
      have hdgt : 1 < d := Nat.one_lt_of_ne_zero_of_even hdne hdeven
      omega
    · apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
      have hmul : d / 2 * 2 = d := by
        simpa [Nat.mul_comm] using hdouble
      rw [hmul]
      exact hdB
  · intro e _he
    rfl

/-- The masked even sector is exactly the negative masked odd half-prefix. -/
private theorem rough_sum_even_eq_neg_odd_half
    (q B : ℕ) (hq : q.Prime) (hqgt : 2 < q) :
    (∑ d ∈ evenCofactorPrefix B, roughDyadicWeight q d) =
      -∑ d ∈ oddCofactorPrefix (B / 2), roughDyadicWeight q d := by
  rw [rough_sum_even_eq_sum_double]
  calc
    (∑ d ∈ Finset.Icc 1 (B / 2), roughDyadicWeight q (2 * d)) =
        ∑ d ∈ Finset.Icc 1 (B / 2),
          if Odd d then -roughDyadicWeight q d else 0 := by
      apply Finset.sum_congr rfl
      intro d _hd
      exact roughDyadicWeight_two_mul q d hq hqgt
    _ = ∑ d ∈ oddCofactorPrefix (B / 2), -roughDyadicWeight q d := by
      unfold oddCofactorPrefix
      rw [Finset.sum_filter]
    _ = -∑ d ∈ oddCofactorPrefix (B / 2), roughDyadicWeight q d := by
      simp

/-- **Wheel-truncated dyadic survivor invariant.**  For every odd prime owner,
the q-rough predecessor prefix compresses exactly to its q-rough odd dyadic
boundary.  This is an equality of signed amplitudes before any norm. -/
theorem roughCofactorMobiusPrefixMass_eq_roughDyadicBoundaryMass
    {q B : ℕ} (hq : q.Prime) (hqgt : 2 < q) :
    roughCofactorMobiusPrefixMass q B =
      roughDyadicCofactorBoundaryMass q B := by
  unfold roughCofactorMobiusPrefixMass roughDyadicCofactorBoundaryMass
  change
    (∑ d ∈ Finset.Icc 1 B, roughDyadicWeight q d) =
      ∑ d ∈ roughDyadicCofactorBoundary q B, canonicalMoebiusWeight d
  rw [rough_sum_Icc_eq_odd_add_even q B,
    rough_sum_even_eq_neg_odd_half q B hq hqgt]
  have hsubset := oddCofactorPrefix_half_subset B
  have hpartition :
      (∑ d ∈ oddCofactorPrefix B \ oddCofactorPrefix (B / 2),
          roughDyadicWeight q d) +
        ∑ d ∈ oddCofactorPrefix (B / 2), roughDyadicWeight q d =
          ∑ d ∈ oddCofactorPrefix B, roughDyadicWeight q d := by
    exact Finset.sum_sdiff hsubset
  calc
    (∑ d ∈ oddCofactorPrefix B, roughDyadicWeight q d) +
          -∑ d ∈ oddCofactorPrefix (B / 2), roughDyadicWeight q d =
        (∑ d ∈ oddCofactorPrefix B, roughDyadicWeight q d) -
          ∑ d ∈ oddCofactorPrefix (B / 2), roughDyadicWeight q d := by ring
    _ = ∑ d ∈ oddCofactorPrefix B \ oddCofactorPrefix (B / 2),
          roughDyadicWeight q d := by
      exact (eq_sub_of_add_eq hpartition).symm
    _ = ∑ d ∈ dyadicCofactorBoundary B, roughDyadicWeight q d := by
      rfl
    _ = ∑ d ∈ roughDyadicCofactorBoundary q B,
          canonicalMoebiusWeight d := by
      unfold roughDyadicCofactorBoundary roughDyadicWeight
      rw [Finset.sum_filter]

/-- The frozen q-predecessor cube is exactly the q-rough Mobius prefix in
complex currency.  This generic form lets the dyadic compression be applied at
every reciprocal cutoff `Y/p` in ChildFar, not only at the whole q^2 daughter
cutoff. -/
theorem frozenPrimeUniverseMass_cast_eq_roughCofactorMobiusPrefixMass
    {q B : ℕ} (hq : q.Prime) :
    ((frozenPrimeUniverseMass (primesUpTo (q - 1)) B : ℤ) : ℂ) =
      roughCofactorMobiusPrefixMass q B := by
  rw [frozenPrimeUniverseMass_eq_goSmoothCofactorSum hq]
  push_cast
  unfold squareRootLowPrimeGoSmoothCofactors
    roughCofactorMobiusPrefixMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hrough : canonicalLargestPrimeFactor d < q
  · rw [if_pos hrough]
    by_cases hsq : Squarefree d
    · simp [hsq, hrough, canonicalMoebiusWeight]
    · have hmu : μ d = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
      simp [hsq, hrough, canonicalMoebiusWeight, hmu]
  · simp [hrough]

/-- The literal Go q^2 daughter therefore lives on the q-rough dyadic boundary
for every odd owner q. -/
theorem squareRootLowPrimeGoWallSquareResidual_cast_eq_roughDyadicBoundaryMass
    {q X : ℕ} (hq : q.Prime) (hqgt : 2 < q) :
    (((squareRootLowPrimeGoWallSquareResidual q X : ℤ) : ℂ)) =
      roughDyadicCofactorBoundaryMass q (X / (q * q)) := by
  rw [squareRootLowPrimeGoWallSquareResidual_cast_eq_roughCofactorMobiusPrefixMass hq,
    roughCofactorMobiusPrefixMass_eq_roughDyadicBoundaryMass hq hqgt]

/-- Far-prime ChildFar column after exact q-rough dyadic compression in each
reciprocal p-fibre. -/
def q2DaughterFarRoughDyadicColumn (R q : ℕ) : ℂ :=
  let Y := squareRootEndpoint R / (q * q)
  ∑ p ∈ frozenPrimeUniverseHighPrimeSet (R + 7) Y,
    roughDyadicCofactorBoundaryMass q (Y / p)

/-- The common q-predecessor far column compresses fibrewise to the q-rough
dyadic wall for every odd owner. -/
theorem q2DaughterFarBaseColumn_cast_eq_roughDyadicColumn
    {R q : ℕ} (hq : q.Prime) (hqgt : 2 < q) :
    ((q2DaughterFarBaseColumn R q : ℤ) : ℂ) =
      q2DaughterFarRoughDyadicColumn R q := by
  let Y := squareRootEndpoint R / (q * q)
  unfold q2DaughterFarBaseColumn q2DaughterFarRoughDyadicColumn
  push_cast
  apply Finset.sum_congr rfl
  intro p _hp
  rw [frozenPrimeUniverseMass_cast_eq_roughCofactorMobiusPrefixMass hq,
    roughCofactorMobiusPrefixMass_eq_roughDyadicBoundaryMass hq hqgt]

/-- **ChildFar compression.**  For every odd q^2 owner, the literal physical
ChildFar mass is exactly a sum of q-rough odd dyadic walls, one at each
reciprocal cutoff `Y_q/p`.  This is still a signed identity before norms. -/
theorem lowWheelFarPrimeQ2ChildFarSlice_mass_eq_roughDyadicColumn
    {R q : ℕ} (hq : q.Prime) (hqgt : 2 < q) :
    (∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
        canonicalMoebiusWeight dp.1) =
      q2DaughterFarRoughDyadicColumn R q := by
  calc
    (∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
        canonicalMoebiusWeight dp.1) =
      ((q2DaughterFarBaseColumn R q : ℤ) : ℂ) :=
        (q2DaughterFarBaseColumn_cast_eq_childFarSliceMass hq).symm
    _ = q2DaughterFarRoughDyadicColumn R q :=
      q2DaughterFarBaseColumn_cast_eq_roughDyadicColumn hq hqgt

/-- Aggregate odd-owner ChildFar mass after the same exact compression. -/
def squareEndpointQ2OddChildFarRoughDyadicColumn (R : ℕ) : ℂ :=
  ∑ q ∈ (primesUpTo (R - 1)).erase 2,
    q2DaughterFarRoughDyadicColumn R q

/-- The whole odd-owner ChildFar column is carried by the wheel-truncated
dyadic walls.  Owner two is deliberately absent from both sides. -/
theorem squareEndpointQ2OddChildFarSlice_eq_roughDyadicColumn
    (R : ℕ) :
    (∑ q ∈ (primesUpTo (R - 1)).erase 2,
      ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
        canonicalMoebiusWeight dp.1) =
      squareEndpointQ2OddChildFarRoughDyadicColumn R := by
  unfold squareEndpointQ2OddChildFarRoughDyadicColumn
  apply Finset.sum_congr rfl
  intro q hq
  rcases Finset.mem_erase.mp hq with ⟨hqne, hqmem⟩
  have hqPrime : q.Prime := (mem_primesUpTo.mp hqmem).1
  have hqgt : 2 < q := by
    have hq2 := hqPrime.two_le
    omega
  exact lowWheelFarPrimeQ2ChildFarSlice_mass_eq_roughDyadicColumn hqPrime hqgt

end RHLean.Proof

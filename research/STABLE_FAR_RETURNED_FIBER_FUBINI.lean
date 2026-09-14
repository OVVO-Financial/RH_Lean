import «research.STABLE_FAR_RETURNED_FIBER_PRODUCTION»

/-!
# Physical identification for the stable-far returned-fibre Fubini

The signed returned-fibre Fubini is compiled in
`research.STABLE_FAR_RETURNED_FIBER_PRODUCTION`.  This file adds only the
physical identification: the arithmetic owner multiplicity on the common
returned cofactor carrier is exactly the repository's actual stable-far
crossing multiplicity.

No norm, absolute value, PNT estimate, or RH-scale hypothesis is introduced.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Every arithmetic descended cofactor produces an actual descended physical
returned child at `(r,(e,p))`. -/
theorem stableFarReturnedDescendedCofactor_mem_physical
    {R r p e : ℕ} (hr : r.Prime) (hrR : r < R)
    (hp : p.Prime) (hpR : R + 8 ≤ p)
    (he : e ∈ stableFarReturnedDescendedCofactors R r p) :
    (r, (e, p)) ∈ lowWheelFarPrimeQ2DescendedTriples R := by
  rcases mem_squareRootLowPrimeGoSmoothCofactors.mp he with
    ⟨he1, heCut, heSq, heRough⟩
  have hdenPos : 0 < r * r * p :=
    Nat.mul_pos (Nat.mul_pos hr.pos hr.pos) hp.pos
  have hq2raw : e * (r * r * p) ≤ squareRootEndpoint R :=
    (Nat.le_div_iff_mul_le hdenPos).1 heCut
  have hq2 : r * r * e * p ≤ squareRootEndpoint R := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hq2raw
  have hr1 : 1 ≤ r := hr.one_le
  have hbaseCut : r * e * p ≤ squareRootEndpoint R := by
    have hle : r * e * p ≤ r * r * e * p := by
      have h := Nat.mul_le_mul_right (r * e * p) hr1
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
    exact hle.trans hq2
  have hbase : (r, (e, p)) ∈ lowWheelFarPrimeLowCofactorTriples R :=
    lowWheelFarPrimeLowCofactorTriple_mem_of_data
      hr hrR he1 hp hpR heSq heRough hbaseCut
  exact Finset.mem_filter.mpr ⟨hbase, hq2⟩

/-- On a genuine returned cofactor, the explicit physical old-owner window is
exactly the arithmetic owner set filtered by the corresponding cofactor
window. -/
theorem lowWheelFarPrimeQ2CrossingOuterOwnerSet_eq_returnedFilter
    {R r p e : ℕ} (hr : r.Prime) (hrR : r < R)
    (hp : p.Prime) (hpR : R + 8 ≤ p)
    (he : e ∈ stableFarReturnedDescendedCofactors R r p) :
    lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (e, p)) =
      (stableFarReturnedOldOwners R r p).filter fun q =>
        e ∈ stableFarReturnedCrossingCofactors R r p q := by
  rcases mem_squareRootLowPrimeGoSmoothCofactors.mp he with
    ⟨he1, _heCut, heSq, heRough⟩
  have hRpos : 0 < R := hr.pos.trans hrR
  have hXlt : squareRootEndpoint R < R * R := by
    unfold squareRootEndpoint
    have hne : R ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.ne_of_gt hRpos)
    simpa [pow_two] using Nat.pred_lt hne
  ext q
  constructor
  · intro hqPhys
    rcases Finset.mem_filter.mp hqPhys with
      ⟨hqOldRoot, hrq, hcut, hcross⟩
    have hqData := mem_primesUpTo.mp hqOldRoot
    have hdenPos : 0 < q * r * p :=
      Nat.mul_pos (Nat.mul_pos hqData.1.pos hr.pos) hp.pos
    have heUpperCut : e ≤ squareRootEndpoint R / (q * r * p) := by
      apply (Nat.le_div_iff_mul_le hdenPos).2
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hcut
    have heUpper :
        e ∈ squareRootLowPrimeGoSmoothCofactors r
          (squareRootEndpoint R / (q * r * p)) :=
      mem_squareRootLowPrimeGoSmoothCofactors.mpr
        ⟨he1, heUpperCut, heSq, heRough⟩
    have heNotLower :
        e ∉ squareRootLowPrimeGoSmoothCofactors r
          (squareRootEndpoint R / (q * q * r * p)) := by
      intro heLower
      have heLowerCut :=
        (mem_squareRootLowPrimeGoSmoothCofactors.mp heLower).2.1
      have hden2Pos : 0 < q * q * r * p :=
        Nat.mul_pos
          (Nat.mul_pos (Nat.mul_pos hqData.1.pos hqData.1.pos) hr.pos) hp.pos
      have hleRaw : e * (q * q * r * p) ≤ squareRootEndpoint R :=
        (Nat.le_div_iff_mul_le hden2Pos).1 heLowerCut
      have hle : q * q * r * e * p ≤ squareRootEndpoint R := by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hleRaw
      exact (Nat.not_lt_of_ge hle) hcross
    have hcrossMem : e ∈ stableFarReturnedCrossingCofactors R r p q :=
      Finset.mem_sdiff.mpr ⟨heUpper, heNotLower⟩
    have hqrp : q * r * p ≤ squareRootEndpoint R := by
      have heOne : 1 ≤ e := he1
      have hle : q * r * p ≤ q * r * e * p := by
        have h := Nat.mul_le_mul_left (q * r) (Nat.mul_le_mul_right p heOne)
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
      exact hle.trans hcut
    have hqUpper : q ≤ squareRootEndpoint R / (r * p) := by
      have hrpPos : 0 < r * p := Nat.mul_pos hr.pos hp.pos
      apply (Nat.le_div_iff_mul_le hrpPos).2
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hqrp
    have hqReturned : q ∈ stableFarReturnedOldOwners R r p :=
      mem_frozenPrimeUniverseHighPrimeSet.mpr
        ⟨hqData.1, hrq, hqUpper⟩
    exact Finset.mem_filter.mpr ⟨hqReturned, hcrossMem⟩
  · intro hqArith
    rcases Finset.mem_filter.mp hqArith with ⟨hqReturned, heCross⟩
    rcases mem_frozenPrimeUniverseHighPrimeSet.mp hqReturned with
      ⟨hqPrime, hrq, hqUpper⟩
    rcases Finset.mem_sdiff.mp heCross with ⟨heUpper, heNotLower⟩
    have heUpperCut :=
      (mem_squareRootLowPrimeGoSmoothCofactors.mp heUpper).2.1
    have hdenPos : 0 < q * r * p :=
      Nat.mul_pos (Nat.mul_pos hqPrime.pos hr.pos) hp.pos
    have hcutRaw : e * (q * r * p) ≤ squareRootEndpoint R :=
      (Nat.le_div_iff_mul_le hdenPos).1 heUpperCut
    have hcut : q * r * e * p ≤ squareRootEndpoint R := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hcutRaw
    have hden2Pos : 0 < q * q * r * p :=
      Nat.mul_pos
        (Nat.mul_pos (Nat.mul_pos hqPrime.pos hqPrime.pos) hr.pos) hp.pos
    have hcross : squareRootEndpoint R < q * q * r * e * p := by
      by_contra hnot
      have hle : q * q * r * e * p ≤ squareRootEndpoint R :=
        Nat.le_of_not_gt hnot
      have hleRaw : e * (q * q * r * p) ≤ squareRootEndpoint R := by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hle
      have heLowerCut : e ≤ squareRootEndpoint R / (q * q * r * p) :=
        (Nat.le_div_iff_mul_le hden2Pos).2 hleRaw
      have heLower :
          e ∈ squareRootLowPrimeGoSmoothCofactors r
            (squareRootEndpoint R / (q * q * r * p)) :=
        mem_squareRootLowPrimeGoSmoothCofactors.mpr
          ⟨he1, heLowerCut, heSq, heRough⟩
      exact heNotLower heLower
    have hqrp : q * r * p ≤ squareRootEndpoint R := by
      have heOne : 1 ≤ e := he1
      have hle : q * r * p ≤ q * r * e * p := by
        have h := Nat.mul_le_mul_left (q * r) (Nat.mul_le_mul_right p heOne)
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
      exact hle.trans hcut
    have hqR : q < R := by
      by_contra hnot
      have hRq : R ≤ q := Nat.le_of_not_gt hnot
      have hRp : R ≤ p := by omega
      have hRR : R * R ≤ q * p := Nat.mul_le_mul hRq hRp
      have hrOne : 1 ≤ r := hr.one_le
      have hqp : q * p ≤ q * r * p := by
        have h := Nat.mul_le_mul_left q (Nat.mul_le_mul_right p hrOne)
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
      exact (Nat.not_lt_of_ge (hRR.trans (hqp.trans hqrp))) hXlt
    exact Finset.mem_filter.mpr
      ⟨mem_primesUpTo.mpr ⟨hqPrime, Nat.le_pred_of_lt hqR⟩,
        hrq, hcut, hcross⟩

/-- Therefore the arithmetic multiplicity is exactly the repository's physical
crossing multiplicity on every actual returned child. -/
theorem lowWheelFarPrimeQ2CrossingNextMultiplicity_eq_returnedMultiplicity
    {R r p e : ℕ} (hr : r.Prime) (hrR : r < R)
    (hp : p.Prime) (hpR : R + 8 ≤ p)
    (he : e ∈ stableFarReturnedDescendedCofactors R r p) :
    lowWheelFarPrimeQ2CrossingNextMultiplicity R (r, (e, p)) =
      stableFarReturnedCrossingMultiplicity R r p e := by
  have hy := stableFarReturnedDescendedCofactor_mem_physical hr hrR hp hpR he
  rw [lowWheelFarPrimeQ2CrossingNextMultiplicity_eq_ownerSet_card hy,
    lowWheelFarPrimeQ2CrossingOuterOwnerSet_eq_returnedFilter hr hrR hp hpR he]
  rfl

/-- Integer form of the actual physical centered returned fibre. -/
def stableFarReturnedPhysicalCenteredMassInt (R r p : ℕ) : ℤ :=
  ∑ e ∈ stableFarReturnedDescendedCofactors R r p,
    (1 - (lowWheelFarPrimeQ2CrossingNextMultiplicity R (r, (e, p)) : ℤ)) * μ e

/-- **Physical/arithmetic returned-fibre bridge.**  After signed Fubini, the
actual stable-far multiplicity field is exactly the frozen-prefix/window object
compiled in the returned-fibre core.  No coefficient norm or occurrence count
remains. -/
theorem stableFarReturnedPhysicalCenteredMassInt_eq_centeredMass
    {R r p : ℕ} (hr : r.Prime) (hrR : r < R)
    (hp : p.Prime) (hpR : R + 8 ≤ p) :
    stableFarReturnedPhysicalCenteredMassInt R r p =
      stableFarReturnedCenteredMass R r p := by
  rw [stableFarReturnedCenteredMass_eq_multiplicity hr hp]
  unfold stableFarReturnedPhysicalCenteredMassInt
  apply Finset.sum_congr rfl
  intro e he
  rw [lowWheelFarPrimeQ2CrossingNextMultiplicity_eq_returnedMultiplicity
    hr hrR hp hpR he]

end RHLean.Proof

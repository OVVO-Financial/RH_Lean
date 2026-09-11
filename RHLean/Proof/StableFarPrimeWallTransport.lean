import Mathlib
import RHLean.Proof.SquareRootLowPrimeCombinedResidualSourceNormalForm
import RHLean.Proof.LowWheelFrozenCofactorTopImageHighPrimeObstruction

/-!
# The stable far-prime wall, after the #646 witness

This continuation concerns only the literal wall carrier.  It retains the
existing #622 far-prime transport identity, records the sign of the single
insertion `c*q`, and proves that the putative `X_R/q^2` daughter scale is zero.
The top-half prime fibres have cofactor one and physical weight one.  None of
these exact statements bounds the complete signed wall mass.
-/

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

/-- The wall predicate itself is precisely one far-prime insertion into a
squarefree low cofactor.  The prime and the physical cutoff are unchanged. -/
theorem mem_stableFarWallCarrier_iff_primeInsertion
    {R : ℕ} (hR : 2 ≤ R) {z : LowWheelFullTaggedPhysicalState} :
    z ∈ stableFarWallCarrier R ↔
      z.1 = ∅ ∧ z.2.2.Prime ∧
      R + 8 ≤ z.2.2 ∧ z.2.2 ≤ squareRootEndpoint R ∧
      z.2.1 ∈ Finset.Ico 1 R ∧ Squarefree z.2.1 ∧
      z.2.1 * z.2.2 ≤ squareRootEndpoint R := by
  rw [stableFarWallCarrier_eq_stableCarrier]
  rcases z with ⟨t, c, q⟩
  constructor
  · exact lowWheelFarTaggedPhysicalStable_geometry hR
  · rintro ⟨rfl, hq, hfar, hqX, hc, hsq, hprod⟩
    exact lowWheelFarTaggedPhysicalStable_of_prime hR hc hsq hq hfar hqX hprod

/-- The wall's native signed mass is exactly the existing far-prime Mertens
transform.  This is the #622 identity on the entire surviving #646 wall. -/
theorem sum_stableFarWallCarrier_eq_farPrimeTransport
    {R : ℕ} (hR : 2 ≤ R) :
    (∑ z ∈ stableFarWallCarrier R, lowWheelFullTaggedPhysicalWeight z) =
      squareRootFarPrimeTransport R := by
  rw [stableFarWallCarrier_eq_stableCarrier,
    ← lowWheelFarTaggedPhysicalLedger_eq_stable]
  exact lowWheelFarTaggedPhysicalLedger_eq_farPrimeTransport R hR

/-- The native wall weight is `mu(c)`, hence the negative of the Möbius
weight of the represented single-insertion integer `c*q`. -/
theorem stableFarWall_singleInsertion_weight
    {R : ℕ} (hR : 2 ≤ R) {z : LowWheelFullTaggedPhysicalState}
    (hz : z ∈ stableFarWallCarrier R) :
    lowWheelFullTaggedPhysicalWeight z =
      -canonicalMoebiusWeight (z.2.1 * z.2.2) := by
  rcases (mem_stableFarWallCarrier_iff_primeInsertion hR).mp hz with
    ⟨hface, hq, hfar, _hqX, hc, _hsq, _hprod⟩
  have hcData := Finset.mem_Ico.mp hc
  have hflip := canonicalMoebiusWeight_mul_prime_eq_neg
    (by omega : 0 < z.2.1) (by omega : z.2.1 < z.2.2) hq
  simp [lowWheelFullTaggedPhysicalWeight, hface, booleanCubeSign, hflip]

/-- Every wall prime has exactly zero daughter scale in the `q^2` schedule
at this endpoint.  This does not make the single-insertion population empty. -/
theorem stableFarWall_primeSquare_daughterScale_eq_zero
    {R : ℕ} (hR : 2 ≤ R) {z : LowWheelFullTaggedPhysicalState}
    (hz : z ∈ stableFarWallCarrier R) :
    squareRootEndpoint R / (z.2.2 * z.2.2) = 0 := by
  have hfar := ((mem_stableFarWallCarrier_iff_primeInsertion hR).mp hz).2.2.1
  have hRq : R ≤ z.2.2 := by omega
  have hsq : R ^ 2 ≤ z.2.2 * z.2.2 := by
    simpa only [pow_two] using Nat.mul_le_mul hRq hRq
  have hpos : 0 < R ^ 2 := pow_pos (by omega : 0 < R) 2
  apply Nat.div_eq_of_lt
  exact (Nat.sub_lt hpos (by omega : 0 < 1)).trans_le hsq

/-- Above half the endpoint the literal wall fibre is forced to have cofactor
one and native signed weight one.  Cancellation of the complete wall, if
available, must retain its coupling to the other prime fibres. -/
theorem stableFarWall_topHalf_cofactor_eq_one_and_weight
    {R : ℕ} (hR : 2 ≤ R) {z : LowWheelFullTaggedPhysicalState}
    (hz : z ∈ stableFarWallCarrier R)
    (htop : squareRootEndpoint R < 2 * z.2.2) :
    z.2.1 = 1 ∧ lowWheelFullTaggedPhysicalWeight z = 1 := by
  rcases (mem_stableFarWallCarrier_iff_primeInsertion hR).mp hz with
    ⟨hface, _hq, _hfar, _hqX, hc, _hsq, hprod⟩
  have hcOne := (Finset.mem_Ico.mp hc).1
  have hcEq : z.2.1 = 1 := by
    by_contra hne
    have hcTwo : 2 ≤ z.2.1 := by omega
    have hmul := Nat.mul_le_mul_right z.2.2 hcTwo
    omega
  refine ⟨hcEq, ?_⟩
  simp [lowWheelFullTaggedPhysicalWeight, hface, hcEq, booleanCubeSign,
    canonicalMoebiusWeight]

end RHLean.Proof

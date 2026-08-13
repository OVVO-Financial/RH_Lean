import Mathlib
import RHLean.Analysis.PrimeSievePNTGoodMassAmplification

/-!
# First attack on the PNT good-mass packet charge

The #329 amplification theorem makes the scalar Selberg good mass
`nativeLambdaTwoGoodRecipMass N 1` an explicit positive coefficient in the
route to the critical packet estimate.  Before trying to exploit individual
good fibres, it is important to calibrate exactly how much strength is hidden
in the factorized scalar charge.

This file proves two deterministic facts.

* The good reciprocal `Lambda_2` mass is bounded above by the total reciprocal
  `Lambda_2` mass.
* Consequently the additive descendant-persistence statement from #329 already
  implies the factorized PNT good-mass charge.  Together with #329's converse,
  the two statements are equivalent at the level of block-uniform
  subpolynomial estimates.

Thus any genuinely new use of positive PNT good mass must eventually open the
sum over good fibres and couple those fibres locally to packet descendants;
leaving the good mass as one scalar factor does not weaken additive persistence.
-/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-- The good reciprocal `Lambda_2` mass is a positive submass of the total
reciprocal `Lambda_2` mass. -/
theorem nativeLambdaTwoGoodRecipMass_le_recipMass
    (N : ℕ) (beta : ℝ) :
    nativeLambdaTwoGoodRecipMass N beta ≤ nativeLambdaTwoRecipMass N := by
  unfold nativeLambdaTwoGoodRecipMass nativeLambdaTwoRecipMass
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (nativePNTGoodFiberSet_subset N beta) ?_
  intro n hn _hgood
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  exact div_nonneg (nativeLambdaTwo_nonneg n hn1) (by positivity)

/-- On every scale `N >= 3`, the good reciprocal mass is bounded by a fixed
multiple of `log(N)^2`.  The constant is deliberately left in terms of
`log 2`; only positivity matters for the amplification argument. -/
theorem nativeLambdaTwoGoodRecipMass_le_const_mul_log_sq
    (N : ℕ) (beta : ℝ) (hN : 3 ≤ N) :
    nativeLambdaTwoGoodRecipMass N beta ≤
      (1 + 1000 / Real.log 2 + 2000 / (Real.log 2) ^ 2) *
        (Real.log (N : ℝ)) ^ 2 := by
  let L : ℝ := Real.log (N : ℝ)
  let l2 : ℝ := Real.log 2
  have hNgt : 1 < N := by omega
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast hNgt)
  have hl2pos : 0 < l2 := by
    dsimp [l2]
    exact Real.log_pos (by norm_num)
  have htwoN : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 2 ≤ N by omega)
  have hlower : l2 ≤ L := by
    dsimp [l2, L]
    exact Real.log_le_log (by norm_num) htwoN
  have hquad : l2 * L ≤ L ^ 2 := by
    have := mul_le_mul_of_nonneg_right hlower hLpos.le
    nlinarith
  have hsq : l2 ^ 2 ≤ L ^ 2 := by
    nlinarith [sq_nonneg (L - l2)]
  have hlin : 1000 * L ≤ (1000 / l2) * L ^ 2 := by
    have hfac : 0 ≤ 1000 / l2 := div_nonneg (by norm_num) hl2pos.le
    have h := mul_le_mul_of_nonneg_left hquad hfac
    have hl2ne : l2 ≠ 0 := ne_of_gt hl2pos
    field_simp [hl2ne] at h ⊢
    nlinarith
  have hconst : (2000 : ℝ) ≤ (2000 / l2 ^ 2) * L ^ 2 := by
    have hl2sqpos : 0 < l2 ^ 2 := sq_pos_of_pos hl2pos
    have hfac : 0 ≤ 2000 / l2 ^ 2 := div_nonneg (by norm_num) hl2sqpos.le
    have h := mul_le_mul_of_nonneg_left hsq hfac
    have hl2sqne : l2 ^ 2 ≠ 0 := ne_of_gt hl2sqpos
    field_simp [hl2sqne] at h ⊢
    nlinarith
  have htotal := nativeLambdaTwoRecipMass_upper N hN
  have hgood := nativeLambdaTwoGoodRecipMass_le_recipMass N beta
  calc
    nativeLambdaTwoGoodRecipMass N beta ≤ nativeLambdaTwoRecipMass N := hgood
    _ ≤ L ^ 2 + 1000 * L + 2000 := by simpa [L] using htotal
    _ ≤ (1 + 1000 / l2 + 2000 / l2 ^ 2) * L ^ 2 := by
      nlinarith [hlin, hconst]
    _ = (1 + 1000 / Real.log 2 + 2000 / (Real.log 2) ^ 2) *
        (Real.log (N : ℝ)) ^ 2 := by rfl

/-- **Calibration of the factorized #329 charge.**  Additive descendant
persistence already implies the PNT good-mass charge.  The proof only uses the
upper bound for total reciprocal `Lambda_2` mass; it does not use the PNT lower
bound.

Combined with
`dyadicPacketAdditiveDescendantPersistence_of_pntGoodMassCharge`, this shows
that the scalar factorized charge and additive persistence are equivalent up to
an absolute change of constants. -/
theorem dyadicPacketPNTGoodMassCharge_of_additiveDescendantPersistence
    (cutoff : DyadicPacketCutoff)
    (hA : DyadicPacketAdditiveDescendantPersistenceStatement cutoff) :
    DyadicPacketPNTGoodMassChargeStatement cutoff := by
  intro ε hε B
  obtain ⟨CA, hCA, hAb⟩ := hA ε hε
  let K : ℝ := 1 + 1000 / Real.log 2 + 2000 / (Real.log 2) ^ 2
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨K * CA, mul_nonneg hK0 hCA, ?_⟩
  intro k x hk hlow hup
  let y := primorialPNTPrimeSieveCutoff k
  let J := cutoff k x
  let N : ℕ := x + B + 2
  let Q : ℝ := (Real.log (N : ℝ)) ^ 2
  let P : ℝ := Real.rpow ((x : ℝ) + 1) ε
  let A : ℝ := primeSieveDyadicPacketLevelEnergy y x J + ((x : ℝ) + 1)
  let D : ℝ := primeSieveDyadicPacketDeepEnergy y x (J + 1)
  have hxpos : 0 < x := by
    have hW := primorialEndpoint_pos k
    dsimp [primorialBlockLower] at hlow
    omega
  have hN3 : 3 ≤ N := by dsimp [N]; omega
  have hmass : nativeLambdaTwoGoodRecipMass N 1 ≤ K * Q := by
    simpa [K, Q] using
      nativeLambdaTwoGoodRecipMass_le_const_mul_log_sq N 1 hN3
  have hD0 : 0 ≤ D := by
    dsimp [D]
    exact primeSieveDyadicPacketDeepEnergy_nonneg y x (J + 1)
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hKQ0 : 0 ≤ K * Q := mul_nonneg hK0 hQ0
  have hpersist : D ≤ CA * P * A := by
    simpa [y, J, P, A, D] using hAb k x hk hlow hup
  calc
    nativeLambdaTwoGoodRecipMass N 1 * D ≤ (K * Q) * D :=
      mul_le_mul_of_nonneg_right hmass hD0
    _ ≤ (K * Q) * (CA * P * A) :=
      mul_le_mul_of_nonneg_left hpersist hKQ0
    _ = (K * CA) * Q * P * A := by ring

/-- The two #329 packet statements are therefore equivalent. -/
theorem dyadicPacketPNTGoodMassCharge_iff_additiveDescendantPersistence
    (cutoff : DyadicPacketCutoff) :
    DyadicPacketPNTGoodMassChargeStatement cutoff ↔
      DyadicPacketAdditiveDescendantPersistenceStatement cutoff := by
  constructor
  · exact dyadicPacketAdditiveDescendantPersistence_of_pntGoodMassCharge cutoff
  · exact dyadicPacketPNTGoodMassCharge_of_additiveDescendantPersistence cutoff

end RHLean.Analysis

import Mathlib
import «research.ZERO_TARGET_CRITICAL_CLIPPED_EDGE»

/-!
# Exact quadratic/boundary split of the critical clipped Mellin edge

For an actually admitted mixed owner child, `a ≤ b ≤ W` and `p*a ≤ W`.
The physical Mellin edge is supported on the same first LCM crossing
`W < p*lcm(a,b)`.  There are exactly two cases:

* if the companion mixed corner `p*b` is also inside the endpoint, the edge
  already carries a second factor `1-r`;
* if `p*b > W`, the companion is physically clipped and only the first-order
  edge survives.

Therefore

  (1-r) edge
    = (1-r)^2 * firstCrossing
      + r(1-r) * clippedCompanionBoundary.

At the critical physical ratio `r = 1/p`, the only genuinely one-dimensional
boundary has coefficient `(1/p)(1-1/p)`.  Thus it already carries the reciprocal
owner factor before squaring; its energy naturally carries `1/p^2`.

No estimate is introduced here.
-/

noncomputable section

namespace RHLean.Proof

private theorem criticalEdge_lcm_prime_mul_left
    {p a b : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    Nat.lcm (p * a) b = p * Nat.lcm a b := by
  apply Nat.dvd_antisymm
  · apply (Nat.lcm_dvd_iff).2
    constructor
    · exact Nat.mul_dvd_mul_left p (Nat.dvd_lcm_left a b)
    · rcases Nat.dvd_lcm_right a b with ⟨k, hk⟩
      refine ⟨p * k, ?_⟩
      rw [hk]
      ac_rfl
  · have hpTarget : p ∣ Nat.lcm (p * a) b :=
      (show p ∣ p * a from ⟨a, rfl⟩).trans (Nat.dvd_lcm_left (p * a) b)
    have haTarget : a ∣ Nat.lcm (p * a) b :=
      (show a ∣ p * a from ⟨p, by simp [Nat.mul_comm]⟩).trans
        (Nat.dvd_lcm_left (p * a) b)
    have hbTarget : b ∣ Nat.lcm (p * a) b := Nat.dvd_lcm_right (p * a) b
    have hlcmTarget : Nat.lcm a b ∣ Nat.lcm (p * a) b :=
      (Nat.lcm_dvd_iff).2 ⟨haTarget, hbTarget⟩
    have hlcmMul : Nat.lcm a b ∣ a * b := by
      apply (Nat.lcm_dvd_iff).2
      exact ⟨⟨b, rfl⟩, ⟨a, by simp [Nat.mul_comm]⟩⟩
    have hpNotLcm : ¬ p ∣ Nat.lcm a b := by
      intro hpLcm
      have hpMul : p ∣ a * b := hpLcm.trans hlcmMul
      rcases hp.dvd_mul.mp hpMul with hpA | hpB
      · exact hpa hpA
      · exact hpb hpB
    have hcop : Nat.Coprime p (Nat.lcm a b) :=
      hp.coprime_iff_not_dvd.mpr hpNotLcm
    exact hcop.mul_dvd_of_dvd_of_dvd hpTarget hlcmTarget

private theorem criticalEdge_lcm_prime_mul_right
    {p a b : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    Nat.lcm a (p * b) = p * Nat.lcm a b := by
  calc
    Nat.lcm a (p * b) = Nat.lcm (p * b) a := Nat.lcm_comm _ _
    _ = p * Nat.lcm b a := criticalEdge_lcm_prime_mul_left hp hpb hpa
    _ = p * Nat.lcm a b := by rw [Nat.lcm_comm b a]

/-- Exact value of the physical clipped edge on an admitted owner child. -/
theorem physicalSuperLcmMellinEdge_eq_firstCrossing_companion
    {W p a b : ℕ} (r : ℝ)
    (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b)
    (hab : a ≤ b) (hbW : b ≤ W) (hpaW : p * a ≤ W) :
    physicalSuperLcmMellinEdge W p r a b =
      if W < p * Nat.lcm a b then
        if p * b ≤ W then 1 - r else 1
      else 0 := by
  have haW : a ≤ W := hab.trans hbW
  have hleft := criticalEdge_lcm_prime_mul_left hp hpa hpb
  have hright := criticalEdge_lcm_prime_mul_right hp hpa hpb
  have hboth : Nat.lcm (p * a) (p * b) = p * Nat.lcm a b := by
    rw [Nat.lcm_mul_left]
  unfold physicalSuperLcmMellinEdge physicalSuperLcmIndicator superLcmIndicator
  rw [hleft, hright, hboth]
  by_cases hwall : W < p * Nat.lcm a b
  · by_cases hpbW : p * b ≤ W
    · simp [haW, hbW, hpaW, hpbW, hwall]
      ring
    · simp [haW, hbW, hpaW, hpbW, hwall]
  · simp [haW, hbW, hpaW, hwall]

/-- The first-order clipping correction splits exactly into a complete-square
quadratic term and one one-dimensional companion-boundary term. -/
theorem one_sub_mul_physicalSuperLcmMellinEdge_eq_quadratic_add_clippedBoundary
    {W p a b : ℕ} (r : ℝ)
    (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b)
    (hab : a ≤ b) (hbW : b ≤ W) (hpaW : p * a ≤ W) :
    (1 - r) * physicalSuperLcmMellinEdge W p r a b =
      (1 - r) ^ 2 * (if W < p * Nat.lcm a b then 1 else 0) +
        r * (1 - r) *
          (if W < p * Nat.lcm a b ∧ W < p * b then 1 else 0) := by
  rw [physicalSuperLcmMellinEdge_eq_firstCrossing_companion
    r hp hpa hpb hab hbW hpaW]
  by_cases hwall : W < p * Nat.lcm a b
  · by_cases hpbW : p * b ≤ W
    · have hnot : ¬ W < p * b := Nat.not_lt.mpr hpbW
      simp [hwall, hpbW, hnot]
      ring
    · have hpbgt : W < p * b := Nat.lt_of_not_ge hpbW
      simp [hwall, hpbW, hpbgt]
      ring
  · simp [hwall]

/-- Critical physical specialization.  The only one-dimensional clipped edge
already carries one reciprocal owner factor `1/p`; after squaring this is the
same `1/p²` owner energy used by the Perron/congestion contraction. -/
theorem critical_one_sub_mul_edge_eq_quadratic_add_reciprocalBoundary
    {W p a b : ℕ}
    (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b)
    (hab : a ≤ b) (hbW : b ≤ W) (hpaW : p * a ≤ W) :
    (1 - 1 / (p : ℝ)) *
        physicalSuperLcmMellinEdge W p (1 / (p : ℝ)) a b =
      (1 - 1 / (p : ℝ)) ^ 2 *
          (if W < p * Nat.lcm a b then 1 else 0) +
        (1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) *
          (if W < p * Nat.lcm a b ∧ W < p * b then 1 else 0) := by
  simpa using
    one_sub_mul_physicalSuperLcmMellinEdge_eq_quadratic_add_clippedBoundary
      (W := W) (p := p) (a := a) (b := b) (r := 1 / (p : ℝ))
      hp hpa hpb hab hbW hpaW

/-- The reciprocal factor on the genuinely clipped boundary has exactly the
critical Perron owner energy after squaring. -/
theorem critical_clippedBoundary_reciprocal_sq_eq_perronEnergy
    (tau : ℝ) {p : ℕ} (hp : p.Prime) :
    (1 / (p : ℝ)) ^ 2 =
      ‖stableFarCriticalQ2LogMultiplier tau p‖ ^ 2 :=
  zeroTarget_reciprocalSquare_eq_norm_sq_criticalQ2Multiplier tau hp.pos

end RHLean.Proof

import Mathlib
import «research.ZERO_TARGET_MELLIN_PHYSICAL_LCM_STENCIL»
import «research.ZERO_TARGET_PERRON_RECIPROCAL_IDENTIFICATION»

/-!
# Critical reciprocal specialization of the physically clipped Mellin square

The amplitude transport and the zero-target covariance square use the same
physical owner ratio.  At owner prime `p`, that ratio is `1/p` on amplitude,
not `1/sqrt(p)`.  Consequently the physically clipped four-corner square has

* first-order edge coefficient `1 - 1/p`, exactly the Euler-memory coefficient;
* double-corner energy coefficient `1/p^2`, exactly the norm-square of the
  critical Perron q² multiplier.

This file records that identification on the admitted physical LCM square so
later owner-descent proofs can use one owner coordinate for both amplitude and
energy.  No estimate is introduced.
-/

noncomputable section

namespace RHLean.Proof

/-- The coordinate-correct critical owner amplitude ratio. -/
def zeroTargetCriticalOwnerRatio (p : ℕ) : ℝ :=
  1 / (p : ℝ)

/-- **Critical clipped-edge normal form.**  On an admitted mixed owner child,
the physically clipped zero-target square has precisely the AMP
`(1 - 1/p)` memory coefficient. -/
theorem zeroTargetMellinPhysicalSuperLcmFourCorner_critical_eq_neg_firstCrossing_add_memoryEdge
    {W p a b : ℕ}
    (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b)
    (hab : a ≤ b) (hbW : b ≤ W) (hpaW : p * a ≤ W) :
    zeroTargetMellinPhysicalSuperLcmFourCorner W p
        (zeroTargetCriticalOwnerRatio p) a b =
      -postRootZeroTargetPairExcess (a, b) *
          (if Nat.lcm a b ≤ W ∧ W < p * Nat.lcm a b ∧ p * a ≤ W
            then 1 else 0) +
        (1 - (1 / (p : ℝ))) * postRootZeroTargetPairExcess (a, b) *
          physicalSuperLcmMellinEdge W p (1 / (p : ℝ)) a b := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hr : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  simpa [zeroTargetCriticalOwnerRatio] using
    zeroTargetMellinPhysicalSuperLcmFourCorner_eq_neg_firstCrossing_add_edge_of_mul_le
      (W := W) (p := p) (a := a) (b := b) (r := 1 / (p : ℝ))
      hr hp hpa hpb hab hbW hpaW

/-- The first-order coefficient in the preceding physical edge is literally
one minus the critical amplitude ratio. -/
theorem one_sub_zeroTargetCriticalOwnerRatio (p : ℕ) :
    1 - zeroTargetCriticalOwnerRatio p = 1 - 1 / (p : ℝ) := by
  rfl

/-- The quadratic double corner of the same critical owner ratio is exactly the
Perron q² energy coefficient. -/
theorem zeroTargetCriticalOwnerRatio_sq_eq_criticalPerronEnergy
    (tau : ℝ) {p : ℕ} (hp : p.Prime) :
    zeroTargetCriticalOwnerRatio p ^ 2 =
      ‖stableFarCriticalQ2LogMultiplier tau p‖ ^ 2 := by
  rw [show zeroTargetCriticalOwnerRatio p ^ 2 = 1 / (p : ℝ) ^ 2 by
    simp [zeroTargetCriticalOwnerRatio]]
  exact zeroTarget_reciprocalSquare_eq_norm_sq_criticalQ2Multiplier tau hp.pos

/-- Both pieces therefore use one and the same owner coordinate: amplitude
memory `1-r` and energy `r²` with `r = 1/p`. -/
theorem zeroTargetCriticalOwner_memory_and_energy_coordinates
    (tau : ℝ) {p : ℕ} (hp : p.Prime) :
    (1 - zeroTargetCriticalOwnerRatio p = 1 - 1 / (p : ℝ)) ∧
      (zeroTargetCriticalOwnerRatio p ^ 2 =
        ‖stableFarCriticalQ2LogMultiplier tau p‖ ^ 2) := by
  exact ⟨one_sub_zeroTargetCriticalOwnerRatio p,
    zeroTargetCriticalOwnerRatio_sq_eq_criticalPerronEnergy tau hp⟩

end RHLean.Proof

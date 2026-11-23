import RHLean.Analysis.AlpogeThin.NativeIdealClassBound
import RHLean.Analysis.AlpogeThin.NativeRayClassData
import RHLean.Analysis.AlpogeNativeQuadraticDifferent

/-!
# The original ray group's cardinality pays its actual discriminant

The existing class-group/residue-ring injection and the proved Minkowski
class-number bound give the cardinality of the SAME RayData group. The
actual degree-two root generates K; its native squarefree discriminant
calculation gives discr K = -d. No cardinality or discriminant estimate is
assumed. The stronger card <= d*M^2 is retained before the original
LFam allowance 4*d*M^2 is supplied.

Source guide: Levent Alpöge's archive, inspected pin
7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
`src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/`
`ClassNumberLeAbsDiscrOfFinrankEqTwo.lean` and `ExistsLFamRay.lean`.
The ray-group injection and discriminant construction are the existing
native RHLean proofs. The archive states no license; attribution assigns none.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField

namespace RHLean.Analysis.AlpogeThin.NativeRay

variable {K : Type} [Field K] [NumberField K]

/-- The original imaginary root generates the degree-two field, so the
native squarefree discriminant theorem applies without a new premise. -/
theorem discr_eq_neg_of_sq_eq_neg {d : ℕ} (hp : d.Prime) (hd : d % 4 = 3)
    {r : K} (hr : r ^ 2 = -(d : K)) (h2 : Module.finrank ℚ K = 2) :
    NumberField.discr K = -(d : ℤ) := by
  let : IsSimpleOrder (IntermediateField ℚ K) :=
    IntermediateField.isSimpleOrder_of_finrank_prime ℚ K (by
      rw [h2]
      exact Nat.prime_two)
  have hadj : IntermediateField.adjoin ℚ {r} = ⊤ := by
    rcases eq_bot_or_eq_top (IntermediateField.adjoin ℚ {r}) with hbot | htop
    · exfalso
      have hmem : r ∈ (⊥ : IntermediateField ℚ K) :=
        hbot ▸ IntermediateField.mem_adjoin_simple_self ℚ r
      obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hmem
      have hs : q ^ 2 = -(d : ℚ) := (algebraMap ℚ K).injective (by
        rw [map_pow, hq, hr, map_neg, map_natCast])
      have hdpos : (0 : ℚ) < d := by exact_mod_cast hp.pos
      nlinarith [sq_nonneg q]
    · exact htop
  have hsf : Squarefree (-(d : ℤ)) := by
    apply Int.squarefree_natAbs.mp
    simpa only [Int.natAbs_neg, Int.natAbs_natCast] using
      ((Nat.irreducible_iff_nat_prime d).mpr hp).squarefree
  exact NativeQuadraticDifferent.discr_eq K (-(d : ℤ)) r
    (by simpa using hr) hadj hsf (by omega) (by omega)

namespace RayData

/-- The original ray quotient is bounded by its actual absolute discriminant. -/
theorem card_le_abs_discr_mul_sq {M : ℕ} (D : RayData K M)
    (h2 : Module.finrank ℚ K = 2) (hM : M ≠ 0) :
    (Fintype.card D.G : ℝ) ≤ |(NumberField.discr K : ℝ)| * (M : ℝ) ^ 2 := by
  have hc : (Fintype.card D.G : ℝ) ≤ (classNumber K : ℝ) * (M : ℝ) ^ 2 := by
    exact_mod_cast D.card_le_classNumber_mul_sq h2 hM
  exact hc.trans (mul_le_mul_of_nonneg_right
    (NativeIdealClassBound.classNumber_le_abs_discr_of_finrank_eq_two K h2) (sq_nonneg _))

theorem card_le_four_mul_abs_discr_mul_sq {M : ℕ} (D : RayData K M)
    (h2 : Module.finrank ℚ K = 2) (hM : M ≠ 0) :
    (Fintype.card D.G : ℝ) ≤ 4 * |(NumberField.discr K : ℝ)| * (M : ℝ) ^ 2 := by
  apply (D.card_le_abs_discr_mul_sq h2 hM).trans
  nlinarith [mul_nonneg (abs_nonneg (NumberField.discr K : ℝ)) (sq_nonneg (M : ℝ))]

/-- The genuine root and native discriminant calculation pay the parameter d. -/
theorem card_le_d_mul_sq {d M : ℕ} (D : RayData K M) (hp : d.Prime)
    (hd : d % 4 = 3) {r : K} (hr : r ^ 2 = -(d : K))
    (h2 : Module.finrank ℚ K = 2) (hM : M ≠ 0) :
    Fintype.card D.G ≤ d * M ^ 2 := by
  have h := D.card_le_abs_discr_mul_sq h2 hM
  rw [discr_eq_neg_of_sq_eq_neg hp hd hr h2] at h
  have h' : (Fintype.card D.G : ℝ) ≤ (d : ℝ) * (M : ℝ) ^ 2 := by
    simpa only [Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d)] using h
  exact_mod_cast h'

end RayData

/-- The actual finite group satisfies the original LFam cardinality allowance. -/
theorem card_ray_le {d M : ℕ} (hp : d.Prime) (hd : d % 4 = 3)
    {r : K} (hr : r ^ 2 = -(d : K)) (h2 : Module.finrank ℚ K = 2)
    (hM : M ≠ 0) (D : RayData K M) :
    (Fintype.card D.G : ℝ) ≤ 4 * (d : ℝ) * (M : ℝ) ^ 2 := by
  have h : (Fintype.card D.G : ℝ) ≤ (d : ℝ) * (M : ℝ) ^ 2 := by
    exact_mod_cast D.card_le_d_mul_sq hp hd hr h2 hM
  nlinarith [mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) (sq_nonneg (M : ℝ))]

end RHLean.Analysis.AlpogeThin.NativeRay

end

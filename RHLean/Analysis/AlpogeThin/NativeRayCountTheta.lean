import RHLean.Analysis.AlpogeThin.NativeRayLatticeCount
import RHLean.Analysis.AlpogeThin.NativeRayTheta

/-!
# Universal count and Gaussian bounds for the actual native ray ideal norms

The same ideal-to-lattice equivalence supplies every coefficient. The finite
count bound retains M² in the actual reduced quadratic-form coefficients:
its discrepancy is at most 4*sqrt(y)/M + 1, uniformly over the ray class.
The Gaussian estimate retains the determinant normalizer and gives the
explicit coefficient (3*pi/8)*d*sqrt(d)*M^2 for every positive time,
instead of a broad degree-ten majorant. The modulus is normalized BEFORE
the Poisson comparison, and large times use the same Gaussian's monotonicity. Neither theorem is a critical Gz bound or a geometric section
realization; these are the count/theta suppliers for that construction.

Reconstructed from Levent Alpöge's proof archive, pinned source path
`src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayCountThetaFibreCount.lean`
and its named count/theta suppliers; inspected mirror pin
7cbf7a0c32fca1badf05931879a37c3f8a2b03b4. Attribution is retained without
assigning a license absent from that source. The sharper constants here
come from the native actual norm-coordinate estimates and full normalization.
-/

noncomputable section
open NumberField MeasureTheory
open scoped Classical

namespace RHLean.Analysis.AlpogeThin.NativeRay

theorem rayCountTheta_fibre_count {ι : Type} (Q : ι → ℝ) (q : ι → ℕ) (hq1 : ∀ v, 1 ≤ q v) (hq : ∀ v, Q v = q v)
    (y : ℝ) (hy : 1 ≤ y) (hfin : {v | Q v ≤ y}.Finite) :
    ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (({v | Q v = (n : ℕ)}.ncard : ℕ) : ℝ) = (({v | Q v ≤ y}.ncard : ℕ) : ℝ) := by
  have hmaps : ∀ v ∈ hfin.toFinset, q v ∈ Finset.Icc 1 ⌊y⌋₊ := by
    intro v hv
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, hq] at hv
    exact Finset.mem_Icc.mpr ⟨hq1 v, Nat.le_floor hv⟩
  have hfib : ∀ n ∈ Finset.Icc 1 ⌊y⌋₊,
      {v | Q v = (n : ℕ)}.ncard = (hfin.toFinset.filter fun v => q v = n).card := by
    intro n hn
    rw [← Set.ncard_coe_finset]
    congr 1
    ext v
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset, hq, Nat.cast_inj]
    constructor
    · rintro rfl
      exact ⟨le_trans (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2) (Nat.floor_le (by linarith)), rfl⟩
    · exact fun h => h.2
  rw [show (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (({v | Q v = (n : ℕ)}.ncard : ℕ) : ℝ)) =
      ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (((hfin.toFinset.filter fun v => q v = n).card : ℕ) : ℝ) from
    Finset.sum_congr rfl fun n hn => by rw [hfib n hn]]
  rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise hmaps, ← Set.ncard_coe_finset,
    Set.Finite.coe_toFinset]

theorem rayCountTheta_fibre_tsum {ι : Type} (Q : ι → ℝ) (q : ι → ℕ) (hq : ∀ v, Q v = q v) (t : ℝ)
    (hs : Summable fun v => Real.exp (-(t * Q v))) :
    ∑' n : ℕ, (({v | Q v = (n : ℕ)}.ncard : ℕ) : ℝ) * Real.exp (-(t * n)) = ∑' v, Real.exp (-(t * Q v)) := by
  have hf := hs.hasSum.tsum_fiberwise q
  rw [← hf.tsum_eq]
  congr 1
  funext n
  have hset : {v | Q v = (n : ℕ)} = q ⁻¹' {n} := by
    ext v
    simp [hq]
  calc (({v | Q v = (n : ℕ)}.ncard : ℕ) : ℝ) * Real.exp (-(t * n))
      = ∑' _ : q ⁻¹' {n}, Real.exp (-(t * n)) := by
        rw [tsum_const, hset, Nat.card_coe_set_eq, nsmul_eq_mul]
    _ = ∑' b : q ⁻¹' {n}, Real.exp (-(t * Q b)) := by
        congr 1
        funext b
        rw [hq b, show q b = n from b.2]


/-- The fibrewise theta series is summable because it is the actual norm
reindexing of a summable lattice Gaussian. -/
theorem rayCountTheta_fibre_summable {ι : Type} (Q : ι → ℝ) (q : ι → ℕ)
    (hq : ∀ v, Q v = q v) (t : ℝ)
    (hs : Summable fun v => Real.exp (-(t * Q v))) :
    Summable fun n : ℕ =>
      (({v | Q v = (n : ℕ)}.ncard : ℕ) : ℝ) * Real.exp (-(t * n)) := by
  have hf := hs.hasSum.tsum_fiberwise q
  apply hf.summable.congr
  intro n
  have hset : {v | Q v = (n : ℕ)} = q ⁻¹' {n} := by
    ext v
    simp [hq]
  symm
  calc (({v | Q v = (n : ℕ)}.ncard : ℕ) : ℝ) * Real.exp (-(t * n))
      = ∑' _ : q ⁻¹' {n}, Real.exp (-(t * n)) := by
        rw [tsum_const, hset, Nat.card_coe_set_eq, nsmul_eq_mul]
    _ = ∑' v : q ⁻¹' {n}, Real.exp (-(t * Q v)) := by
        congr 1
        funext v
        rw [hq v, show q v = n from v.2]

/-- Complete, uniformly quantified count/theta estimates on the ORIGINAL
ray-class ideal coefficients, with their genuine discriminant and modulus.
All field, ray-class and size hypotheses are explicit. -/
theorem rayCountTheta
    (K : Type) [Field K] [NumberField K] (d M : ℕ) (x : K)
    (hd : d.Prime) (hd4 : d % 4 = 3) (hd100 : 100 ≤ d)
    (hx : x ^ 2 = -(d : K)) (hK : Module.finrank ℚ K = 2) (hM : 3 ≤ M)
    (D : RayData K M) (g : D.G) :
    (∀ y : ℝ, 1 ≤ y →
      |∑ n ∈ Finset.Icc 1 ⌊y⌋₊, aRay D g n -
        2 * Real.pi / (Real.sqrt d * (M : ℝ) ^ 2) * y| ≤
          4 * Real.sqrt y / M + 1) ∧
    ∀ t : ℝ, 0 < t →
      Summable (fun n : ℕ => aRay D g n * Real.exp (-(t * n))) ∧
      |∑' n : ℕ, aRay D g n * Real.exp (-(t * n)) -
        2 * Real.pi / (Real.sqrt d * (M : ℝ) ^ 2) / t| ≤
          (3 * Real.pi / 8) * d * Real.sqrt d * (M : ℝ) ^ 2 * t := by
  obtain ⟨α, γ, l, θ₁, θ₂, Φ, hα, hγ, hαγ, hscale, hΦ0, key⟩ :=
    QuadraticForm.exists_quadratic_norm_coordinates_with_scale
      K d M x hd hd4 hd100 hx hK hM D g
  let q : ℤ × ℤ → ℕ := fun v => Ideal.absNorm (Φ v).1
  have hq1 : ∀ v, 1 ≤ q v := fun v =>
    Nat.one_le_iff_ne_zero.mpr fun hn => hΦ0 v (Ideal.absNorm_eq_zero_iff.mp hn)
  have hq : ∀ v, qForm α γ l θ₁ θ₂ v = q v := key
  have ha : ∀ n : ℕ,
      aRay D g n = (({v : ℤ × ℤ | qForm α γ l θ₁ θ₂ v = n}.ncard : ℕ) : ℝ) := by
    intro n
    have hset : idealsIn D g n = (Subtype.val ∘ Φ) ''
        {v : ℤ × ℤ | qForm α γ l θ₁ θ₂ v = n} := by
      ext I
      simp only [idealsIn, Set.mem_ofPred_eq, Set.mem_image, Function.comp_apply]
      constructor
      · rintro ⟨_, hIc, hIn, hIg⟩
        refine ⟨Φ.symm ⟨I, hIc, hIg⟩, ?_, by simp⟩
        rw [key, Equiv.apply_symm_apply]
        exact_mod_cast hIn
      · rintro ⟨v, hv, rfl⟩
        rw [key] at hv
        exact ⟨hΦ0 v, (Φ v).2.1, by exact_mod_cast hv, (Φ v).2.2⟩
    rw [aRay, hset, Set.ncard_image_of_injective _ (Subtype.val_injective.comp Φ.injective)]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.pos
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hα0 : 0 < α := by linarith
  have hγ0 : 0 < γ := by linarith
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd0
  have hsd4 : 4 ≤ Real.sqrt (d : ℝ) := by
    rw [show (4 : ℝ) = Real.sqrt 16 by norm_num]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 16 ≤ d))
  have hγM : (M : ℝ) ^ 2 ≤ γ := by
    have hm2 := sq_nonneg (M : ℝ)
    nlinarith [mul_le_mul_of_nonneg_left hsd4 hm2, hscale.2.1]
  have hs : Real.sqrt (α * γ) = Real.sqrt d * (M : ℝ) ^ 2 / 2 := by
    rw [hαγ, show (d : ℝ) * (M : ℝ) ^ 4 / 4 =
      (Real.sqrt d * (M : ℝ) ^ 2 / 2) ^ 2 by
        rw [div_pow, mul_pow, Real.sq_sqrt hd0.le]; ring]
    exact Real.sqrt_sq (by positivity)
  have hC : Real.pi / Real.sqrt (α * γ) =
      2 * Real.pi / (Real.sqrt d * (M : ℝ) ^ 2) := by
    rw [hs]
    field_simp
  refine ⟨fun y hy => ?_, fun t ht0 => ?_⟩
  · have hc := LatticeBounds.qForm_count α γ l θ₁ θ₂ y hα0 hγ0 (by linarith)
    have hsum : ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, aRay D g n =
        (({v : ℤ × ℤ | qForm α γ l θ₁ θ₂ v ≤ y}.ncard : ℕ) : ℝ) := by
      simp only [ha]
      exact rayCountTheta_fibre_count (qForm α γ l θ₁ θ₂) q hq1 hq y hy hc.1
    have hroot (z : ℝ) (hMz : (M : ℝ) ^ 2 ≤ z) :
        Real.sqrt (y / z) ≤ Real.sqrt y / M := by
      calc Real.sqrt (y / z) ≤ Real.sqrt (y / (M : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (by linarith : 0 ≤ y)
            (sq_pos_of_pos hM0) hMz)
        _ = Real.sqrt y / M := by
          rw [Real.sqrt_div (by linarith : 0 ≤ y), Real.sqrt_sq hM0.le]
    rw [hsum, ← hC]
    exact hc.2.trans (by linarith [hroot α hscale.1, hroot γ hγM])
  · have hM2 : 0 < (M : ℝ) ^ 2 := sq_pos_of_pos hM0
    have hαs : 1 ≤ α / (M : ℝ) ^ 2 := by
      rw [le_div_iff₀ hM2, one_mul]
      exact hscale.1
    have hγs : 1 ≤ γ / (M : ℝ) ^ 2 := by
      rw [le_div_iff₀ hM2, one_mul]
      exact hγM
    have hags : α / (M : ℝ) ^ 2 * (γ / (M : ℝ) ^ 2) = (d : ℝ) / 4 := by
      calc α / (M : ℝ) ^ 2 * (γ / (M : ℝ) ^ 2) =
          (α * γ) / (M : ℝ) ^ 4 := by field_simp; ring
        _ = ((d : ℝ) * (M : ℝ) ^ 4 / 4) / (M : ℝ) ^ 4 := by rw [hαγ]
        _ = (d : ℝ) / 4 := by field_simp
    have hPs : 2 ≤ α / (M : ℝ) ^ 2 * (γ / (M : ℝ) ^ 2) := by
      rw [hags]
      have hd100r : (100 : ℝ) ≤ d := by exact_mod_cast hd100
      linarith
    have hs0 : Real.sqrt (α / (M : ℝ) ^ 2 * (γ / (M : ℝ) ^ 2)) =
        Real.sqrt d / 2 := by
      rw [hags, Real.sqrt_div hd0.le]
      norm_num
    have hqscale (v : ℤ × ℤ) :
        ((M : ℝ) ^ 2 * t) * qForm (α / (M : ℝ) ^ 2) (γ / (M : ℝ) ^ 2) l θ₁ θ₂ v =
          t * qForm α γ l θ₁ θ₂ v := by
      unfold qForm
      field_simp
      ring
    have htheta := LatticeBounds.theta_qForm_all_time
      (α / (M : ℝ) ^ 2) (γ / (M : ℝ) ^ 2) l θ₁ θ₂
      ((M : ℝ) ^ 2 * t) hαs hγs hPs (mul_pos hM2 ht0)
    simp_rw [hqscale] at htheta
    have hnormal :
        Real.pi / Real.sqrt (α / (M : ℝ) ^ 2 * (γ / (M : ℝ) ^ 2)) /
            ((M : ℝ) ^ 2 * t) =
          2 * Real.pi / (Real.sqrt d * (M : ℝ) ^ 2) / t := by
      rw [hs0]
      field_simp
    have hcost :
        3 * (Real.pi / Real.sqrt (α / (M : ℝ) ^ 2 * (γ / (M : ℝ) ^ 2))) *
            (α / (M : ℝ) ^ 2 * (γ / (M : ℝ) ^ 2)) ^ 2 * ((M : ℝ) ^ 2 * t) =
          (3 * Real.pi / 8) * d * Real.sqrt d * (M : ℝ) ^ 2 * t := by
      rw [hs0, hags]
      field_simp [hM0.ne', hsd.ne']
      ring_nf
      rw [Real.sq_sqrt hd0.le]
    rw [hnormal, hcost] at htheta
    have htsum : ∑' n : ℕ, aRay D g n * Real.exp (-(t * n)) =
        ∑' v : ℤ × ℤ, Real.exp (-(t * qForm α γ l θ₁ θ₂ v)) := by
      simp only [ha]
      exact rayCountTheta_fibre_tsum (qForm α γ l θ₁ θ₂) q hq t htheta.1
    refine ⟨?_, ?_⟩
    · simp only [ha]
      exact rayCountTheta_fibre_summable (qForm α γ l θ₁ θ₂) q hq t htheta.1
    · rw [htsum]
      exact htheta.2

end RHLean.Analysis.AlpogeThin.NativeRay

end

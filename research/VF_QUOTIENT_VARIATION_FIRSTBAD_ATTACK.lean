import «research.VF_MID_919_QUOTIENT_SIGNED_RETURN»

/-!
# Arithmetic attack: exact square-hyperbola separation of sharp quotient mass

The square endpoint X = R^2 - 1 has a strict quotient gap: every norm m < R
has floor(X/m) >= R, while every m >= R has floor(X/m) < R.
The high-quotient part is therefore an EXACT short sum of genuine
excluded-six norm coefficients. The long-norm part stays as low quotient
buckets, where the hard cancellation remains.

This module proves only unconditional identities and a short-sum ceiling.
It does NOT assume a variation bound, an RH-strength Mertens estimate, or
a history-conditioned first-bad Sector Six payment.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- Exact square-hyperbola cutoff: at X=R^2-1 the diagonal cannot be hit.
The quotient >= R is equivalent to a STRICTLY smaller norm m < R. -/
theorem vfVarSquareHighQuotient_iff_smallNorm
    (R m : ℕ) (hR : 2 ≤ R) (hm : 0 < m) :
    R ≤ (R ^ 2 - 1) / m ↔ m < R := by
  have hsq : 1 ≤ R ^ 2 := by nlinarith
  constructor
  · intro hq
    have hmul : R * m ≤ R ^ 2 - 1 :=
      (Nat.le_div_iff_mul_le hm).mp hq
    have hlt : R ^ 2 - 1 < R ^ 2 :=
      Nat.sub_lt hsq (by decide)
    by_contra hn
    have hmR : R ≤ m := by omega
    nlinarith
  · intro hlt
    have hmR : m ≤ R - 1 := by omega
    have hmul : R * m ≤ R * (R - 1) :=
      Nat.mul_le_mul_left R hmR
    have hmax : R * (R - 1) ≤ R ^ 2 - 1 := by
      have hsub : R - 1 + 1 = R := by omega
      nlinarith
    exact (Nat.le_div_iff_mul_le hm).mpr (hmul.trans hmax)

/-- Arbitrary finite selection of quotient buckets. This is the
once-only, occurrence-preserving Fubini map for the genuine a^(6)(m). -/
theorem vfVarSelectedQuotientBuckets (X : ℕ) (S : Finset ℕ) :
    (∑ t ∈ S,
      (vf919SharpQuotientKernel36 t : ℂ) * vf919QuotientBucket X t) =
      ∑ m ∈ Finset.Icc 1 X,
        if X / m ∈ S then
          vf919ExcludedNormCoefficients m *
            (vf919SharpQuotientKernel36 (X / m) : ℂ)
        else 0 := by
  unfold vf919QuotientBucket
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _hm
  by_cases hmem : X / m ∈ S
  · rw [Finset.sum_eq_single (X / m)]
    · simp [hmem, mul_comm]
    · intro t _ht hne
      have hn : X / m ≠ t := Ne.symm hne
      simp [hn]
    · intro hnot
      exact (hnot hmem).elim
  · have hzero :
        (∑ t ∈ S,
          (vf919SharpQuotientKernel36 t : ℂ) *
            (if X / m = t then vf919ExcludedNormCoefficients m else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      have hn : X / m ≠ t := by
        intro heq
        exact hmem (heq ▸ ht)
      simp [hn]
    rw [hzero]
    simp [hmem]

/-- The hard long-norm component, kept as the original signed
low-quotient buckets rather than independently normed ideal rows. -/
def vfVarSquareLongNormLowQuotient (R : ℕ) : ℂ :=
  ∑ t ∈ Finset.Icc 1 (R - 1),
    (vf919SharpQuotientKernel36 t : ℂ) *
      vf919QuotientBucket (R ^ 2 - 1) t

/-- The complete high-quotient component is an EXACT short norm sum.
No smoothing and no future 36m return is spent at this endpoint. -/
def vfVarSquareShortNormHighQuotient (R : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (R - 1),
    vf919ExcludedNormCoefficients m *
      (vf919SharpQuotientKernel36 ((R ^ 2 - 1) / m) : ℂ)

/-- The entire high-quotient bucket sector has no large-norm terms.
This is a literal equality, not an upper-bound heuristic. -/
theorem vfVarSquareHighQuotient_eq_shortNorm
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ t ∈ Finset.Icc R (R ^ 2 - 1),
      (vf919SharpQuotientKernel36 t : ℂ) *
        vf919QuotientBucket (R ^ 2 - 1) t) =
      vfVarSquareShortNormHighQuotient R := by
  let X := R ^ 2 - 1
  have hX : R - 1 ≤ X := by
    dsimp [X]
    have hsq : 1 ≤ R ^ 2 := by nlinarith
    nlinarith
  rw [vfVarSelectedQuotientBuckets]
  unfold vfVarSquareShortNormHighQuotient
  change
    (∑ m ∈ Finset.Icc 1 X,
      if X / m ∈ Finset.Icc R X then
        vf919ExcludedNormCoefficients m *
          (vf919SharpQuotientKernel36 (X / m) : ℂ)
      else 0) =
    ∑ m ∈ Finset.Icc 1 (R - 1),
      vf919ExcludedNormCoefficients m *
        (vf919SharpQuotientKernel36 (X / m) : ℂ)
  have hsubset : Finset.Icc 1 (R - 1) ⊆ Finset.Icc 1 X := by
    intro m hm
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hm).1, (Finset.mem_Icc.mp hm).2.trans hX⟩
  calc
    (∑ m ∈ Finset.Icc 1 X,
      if X / m ∈ Finset.Icc R X then
        vf919ExcludedNormCoefficients m *
          (vf919SharpQuotientKernel36 (X / m) : ℂ)
      else 0) =
      ∑ m ∈ Finset.Icc 1 (R - 1),
        if X / m ∈ Finset.Icc R X then
          vf919ExcludedNormCoefficients m *
            (vf919SharpQuotientKernel36 (X / m) : ℂ)
        else 0 := by
          symm
          apply Finset.sum_subset hsubset
          intro m hm hmnot
          have hmpos : 0 < m := by
            have := (Finset.mem_Icc.mp hm).1
            omega
          have hquot : ¬ X / m ∈ Finset.Icc R X := by
            intro h
            have hsmall : m < R :=
              (vfVarSquareHighQuotient_iff_smallNorm R m hR hmpos).mp
                (Finset.mem_Icc.mp h).1
            exact hmnot (Finset.mem_Icc.mpr
              ⟨(Finset.mem_Icc.mp hm).1, by omega⟩)
          simp [hquot]
    _ = ∑ m ∈ Finset.Icc 1 (R - 1),
          vf919ExcludedNormCoefficients m *
            (vf919SharpQuotientKernel36 (X / m) : ℂ) := by
          apply Finset.sum_congr rfl
          intro m hm
          have hmpos : 0 < m := by
            have := (Finset.mem_Icc.mp hm).1
            omega
          have hquot : X / m ∈ Finset.Icc R X := by
            apply Finset.mem_Icc.mpr
            constructor
            · exact (vfVarSquareHighQuotient_iff_smallNorm R m hR hmpos).mpr
                (by have := (Finset.mem_Icc.mp hm).2; omega)
            · exact Nat.div_le_self X m
          simp [hquot]

/-- Genuine Mertens at the square cutoff splits exactly into one
short norm sector and one hard long-norm / low-quotient sector. -/
theorem vfVarMertens_squareHyperbola_exact_split
    (R : ℕ) (hR : 4 ≤ R) :
    (∑ n ∈ Finset.Icc 1 (R ^ 2 - 1),
      (ArithmeticFunction.moebius n : ℂ)) =
      vfVarSquareLongNormLowQuotient R +
        vfVarSquareShortNormHighQuotient R := by
  let X := R ^ 2 - 1
  have hX : 12 ≤ X := by dsimp [X]; nlinarith
  have hlow : (Finset.Icc 1 (R - 1)).Disjoint
      (Finset.Icc R X) := by
    apply Finset.disjoint_left.mpr
    intro t ht hu
    have ht' := (Finset.mem_Icc.mp ht).2
    have hu' := (Finset.mem_Icc.mp hu).1
    omega
  have hunion :
      Finset.Icc 1 X =
        Finset.Icc 1 (R - 1) ∪ Finset.Icc R X := by
    ext t
    simp only [Finset.mem_Icc, Finset.mem_union]
    have hX' : R ≤ X := by dsimp [X]; nlinarith
    omega
  calc
    (∑ n ∈ Finset.Icc 1 X,
      (ArithmeticFunction.moebius n : ℂ)) =
      ∑ t ∈ Finset.Icc 1 X,
        (vf919SharpQuotientKernel36 t : ℂ) *
          vf919QuotientBucket X t :=
      vf919Mertens_eq_exact_quotient_buckets X hX
    _ = (∑ t ∈ Finset.Icc 1 (R - 1),
          (vf919SharpQuotientKernel36 t : ℂ) *
            vf919QuotientBucket X t) +
        (∑ t ∈ Finset.Icc R X,
          (vf919SharpQuotientKernel36 t : ℂ) *
            vf919QuotientBucket X t) := by
          rw [hunion, Finset.sum_union hlow]
    _ = vfVarSquareLongNormLowQuotient R +
          vfVarSquareShortNormHighQuotient R := by
          rw [vfVarSquareHighQuotient_eq_shortNorm R (by omega)]
          rfl

/-- Universal norm bound on the 36-period sharp quotient coefficient.
This is a coefficient bound, NOT cancellation in a sum. -/
theorem vfVarSharpKernel_norm_le_two (t : ℕ) :
    ‖(vf919SharpQuotientKernel36 t : ℂ)‖ ≤ (2 : ℝ) := by
  rw [Complex.norm_intCast]
  have h := vf919SharpQuotientKernel36_bounds t
  have habs : |vf919SharpQuotientKernel36 t| ≤ (2 : ℤ) :=
    abs_le.mpr ⟨h.1, by omega⟩
  exact_mod_cast habs

/-- The high-quotient sector costs at most twice the absolute mass
of the SHORT norm coefficients m<R. The long-norm sector is not bounded. -/
theorem vfVarSquareShortNorm_norm_le_two_coeffMass (R : ℕ) :
    ‖vfVarSquareShortNormHighQuotient R‖ ≤
      2 * (∑ m ∈ Finset.Icc 1 (R - 1),
        ‖vf919ExcludedNormCoefficients m‖) := by
  unfold vfVarSquareShortNormHighQuotient
  calc
    ‖∑ m ∈ Finset.Icc 1 (R - 1),
        vf919ExcludedNormCoefficients m *
          (vf919SharpQuotientKernel36 ((R ^ 2 - 1) / m) : ℂ)‖ ≤
      ∑ m ∈ Finset.Icc 1 (R - 1),
        ‖vf919ExcludedNormCoefficients m *
          (vf919SharpQuotientKernel36 ((R ^ 2 - 1) / m) : ℂ)‖ :=
        norm_sum_le _ _
    _ = ∑ m ∈ Finset.Icc 1 (R - 1),
        ‖vf919ExcludedNormCoefficients m‖ *
          ‖(vf919SharpQuotientKernel36 ((R ^ 2 - 1) / m) : ℂ)‖ := by
          simp_rw [norm_mul]
    _ ≤ ∑ m ∈ Finset.Icc 1 (R - 1),
        ‖vf919ExcludedNormCoefficients m‖ * 2 := by
          apply Finset.sum_le_sum
          intro m _hm
          exact mul_le_mul_of_nonneg_left
            (vfVarSharpKernel_norm_le_two _) (norm_nonneg _)
    _ = 2 * (∑ m ∈ Finset.Icc 1 (R - 1),
          ‖vf919ExcludedNormCoefficients m‖) := by
          simp_rw [mul_comm (‖vf919ExcludedNormCoefficients _‖) (2 : ℝ)]
          rw [Finset.mul_sum]

/-- The precise new quantitative target: bound the hard low-quotient
sector; the high-quotient sector is already a short coefficient sum.
This is a proved reduction, not an assumed RH-scale estimate. -/
theorem vfVarSquareMertens_norm_le_longPlus_shortMass
    (R : ℕ) (hR : 4 ≤ R) :
    ‖(∑ n ∈ Finset.Icc 1 (R ^ 2 - 1),
      (ArithmeticFunction.moebius n : ℂ))‖ ≤
      ‖vfVarSquareLongNormLowQuotient R‖ +
        2 * (∑ m ∈ Finset.Icc 1 (R - 1),
          ‖vf919ExcludedNormCoefficients m‖) := by
  rw [vfVarMertens_squareHyperbola_exact_split R hR]
  exact (norm_add_le _ _).trans
    (add_le_add_left (vfVarSquareShortNorm_norm_le_two_coeffMass R) _)

end RHLean.Analysis

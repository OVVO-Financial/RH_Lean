import «research.VF_MID_919_OAI_PRINCIPAL_COEFFICIENT_MAP»

/-!
# Exact 36-period quotient-cutoff signed return

This is a full arithmetic identity for the *constructed* excluded-six norm
coefficients and the actual rational Mobius function. It is not a uniform
bound on their signed sums and does not identify an OAI analytic row.

The quotient buckets group all norm coefficients with the same literal
floor(X / m), without taking absolute values. The signed 36-periodic kernel
has a primitive whose exact range is [-4,4]. Abel transport therefore
places every surviving signed payment on differences of consecutive
physical quotient buckets. Those differences are the open quantitative
arithmetic object; a small observed variation is NOT assumed as a theorem.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- The signed norm coefficient in one exact quotient cutoff bucket. -/
def vf919QuotientBucket (X t : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 X,
    if X / m = t then vf919ExcludedNormCoefficients m else 0

/-- An exact quotient bucket cannot lie above the final cutoff. -/
theorem vf919QuotientBucket_above (X t : ℕ) (ht : X < t) :
    vf919QuotientBucket X t = 0 := by
  unfold vf919QuotientBucket
  apply Finset.sum_eq_zero
  intro m _hm
  have hdiv : X / m ≤ X := Nat.div_le_self X m
  have hne : X / m ≠ t := by omega
  simp [hne]

/-- Exact first-stage Fubini: each norm occurrence is charged once to the
bucket carrying its physical integer quotient. This is unconditional. -/
theorem vf919Mertens_eq_exact_quotient_buckets (X : ℕ) (hX : 12 ≤ X) :
    (∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.moebius n : ℂ)) =
      ∑ t ∈ Finset.Icc 1 X,
        (vf919SharpQuotientKernel36 t : ℂ) * vf919QuotientBucket X t := by
  rw [vf919Mertens_eq_excludedNorm_periodicKernel X hX]
  unfold vf919QuotientBucket
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  have hmpos : 0 < m := by
    have := (Finset.mem_Icc.mp hm).1
    omega
  have hmX : m ≤ X := (Finset.mem_Icc.mp hm).2
  have hquotient : X / m ∈ Finset.Icc 1 X := by
    apply Finset.mem_Icc.mpr
    constructor
    · exact (Nat.le_div_iff_mul_le hmpos).2 (by simpa using hmX)
    · exact Nat.div_le_self X m
  have hsingle :
      (∑ t ∈ Finset.Icc 1 X,
        (vf919SharpQuotientKernel36 t : ℂ) *
          (if X / m = t then vf919ExcludedNormCoefficients m else 0)) =
        (vf919SharpQuotientKernel36 (X / m) : ℂ) *
          vf919ExcludedNormCoefficients m := by
    rw [Finset.sum_eq_single (X / m)]
    · simp
    · intro t _ht hne
      have hn : X / m ≠ t := Ne.symm hne
      simp [hn]
    · intro hnot
      exact (hnot hquotient).elim
  rw [hsingle]
  ring

/-- The finite primitive of the *literal* period-36 integer kernel.
Its 36 entries are the exact partial sums starting at residue one. -/
def vf919QuotientKernelPrimitive36Table : Fin 36 → ℤ :=
  ![0, 1, 1, 0, -1, -3, -4, -4, -4, -4, -3, -3,
    -3, -2, -2, -1, 0, 0, 0, 1, 2, 2, 3, 3,
    3, 4, 4, 4, 4, 3, 1, 0, -1, -1, 0, 0]

def vf919QuotientKernelPrimitive36 (n : ℕ) : ℤ :=
  vf919QuotientKernelPrimitive36Table ⟨n % 36, by omega⟩

/-- Universal exact primitive bound: no hypothesis on rational or ideal
Mobius values enters this calculation. -/
theorem vf919QuotientKernelPrimitive36_bounds (n : ℕ) :
    -4 ≤ vf919QuotientKernelPrimitive36 n ∧
      vf919QuotientKernelPrimitive36 n ≤ 4 := by
  have hmod : n % 36 < 36 := Nat.mod_lt n (by decide)
  interval_cases h : n % 36 <;>
    norm_num [vf919QuotientKernelPrimitive36,
      vf919QuotientKernelPrimitive36Table, h]

/-- The exact derivative of the bounded primitive is the original signed
quotient kernel. This is what exposes the moving-cutoff return flux. -/
theorem vf919QuotientKernelPrimitive36_step (n : ℕ) (hn : 0 < n) :
    vf919QuotientKernelPrimitive36 n -
      vf919QuotientKernelPrimitive36 (n - 1) =
        vf919SharpQuotientKernel36 n := by
  have hprev : (n - 1) % 36 = (n % 36 + 35) % 36 := by omega
  have hmod : n % 36 < 36 := Nat.mod_lt n (by decide)
  have hindex :
      (⟨(n - 1) % 36, Nat.mod_lt (n - 1) (by decide)⟩ : Fin 36) =
        ⟨(n % 36 + 35) % 36, Nat.mod_lt _ (by decide)⟩ := by
    exact Fin.ext hprev
  rw [vf919SharpQuotientKernel36_mod]
  change vf919QuotientKernelPrimitive36Table ⟨n % 36, by omega⟩ -
      vf919QuotientKernelPrimitive36Table
        ⟨(n - 1) % 36, by omega⟩ =
        vf919SharpQuotientKernel36 (n % 36)
  rw [hindex]
  interval_cases h : n % 36 <;>
    norm_num [vf919QuotientKernelPrimitive36Table,
      vf919SharpQuotientKernel36,
      vf919IntegerCharacterPrefix_eq_residue, h]

/-- A universal finite signed Abel identity. This is a *signed equality*,
not the triangle inequality and not a moment estimate. -/
theorem vf919QuotientKernel36_signed_abel (N : ℕ) (b : ℕ → ℂ) :
    (∑ t ∈ Finset.Icc 1 N,
      (vf919SharpQuotientKernel36 t : ℂ) * b t) =
      (∑ t ∈ Finset.Icc 1 N,
        (vf919QuotientKernelPrimitive36 t : ℂ) * (b t - b (t + 1))) +
      (vf919QuotientKernelPrimitive36 N : ℂ) * b (N + 1) := by
  induction N with
  | zero =>
      simp [vf919QuotientKernelPrimitive36, vf919QuotientKernelPrimitive36Table]
  | succ N ih =>
      have hstep :
          (vf919SharpQuotientKernel36 (N + 1) : ℂ) =
            (vf919QuotientKernelPrimitive36 (N + 1) : ℂ) -
              (vf919QuotientKernelPrimitive36 N : ℂ) := by
        have h := vf919QuotientKernelPrimitive36_step (N + 1) (by omega)
        simpa using congrArg (fun z : ℤ => (z : ℂ)) h.symm
      change
        (∑ t ∈ Finset.Icc 1 (N + 1),
          (vf919SharpQuotientKernel36 t : ℂ) * b t) =
          (∑ t ∈ Finset.Icc 1 (N + 1),
            (vf919QuotientKernelPrimitive36 t : ℂ) * (b t - b (t + 1))) +
          (vf919QuotientKernelPrimitive36 (N + 1) : ℂ) * b (N + 1 + 1)
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
      rw [ih, hstep]
      ring

/-- Exact second-stage signed return for the *actual* sharp rational
Mertens prefix, with no free top boundary and no missing norm occurrence.
Every residual is a neighboring-quotient-bucket difference. -/
theorem vf919Mertens_eq_exact_signed_quotient_return
    (X : ℕ) (hX : 12 ≤ X) :
    (∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.moebius n : ℂ)) =
      ∑ t ∈ Finset.Icc 1 X,
        (vf919QuotientKernelPrimitive36 t : ℂ) *
          (vf919QuotientBucket X t - vf919QuotientBucket X (t + 1)) := by
  rw [vf919Mertens_eq_exact_quotient_buckets X hX,
    vf919QuotientKernel36_signed_abel]
  rw [vf919QuotientBucket_above X (X + 1) (by omega)]
  ring


/-! ## Exact 36m-cutoff return of an individual physical norm occurrence

The quotient kernel is periodic in its integer QUOTIENT. Therefore an
individual norm m reappears at each successive cutoff for m consecutive
integer endpoints. A complete period is 36*m endpoints. The total signed
coefficient across such an aligned period vanishes exactly, with no Mobius
estimate and no summation over different norms. This is a future return,
NOT a payment available before a hypothetical first bad endpoint. -/

private theorem vf919Kernel36_shift_range_sum (f : ℕ → ℤ) (n : ℕ) :
    (∑ j ∈ Finset.range n, f (j + 1)) =
      (∑ j ∈ Finset.range n, f j) - f 0 + f n := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [Finset.sum_range_succ]
      rw [ih]
      ring

/-- A complete quotient cycle has EXACT zero signed mass regardless of the
starting quotient. Not an estimate, and no principal-row hypothesis. -/
theorem vf919QuotientKernel36_all_start_zero (a : ℕ) :
    (∑ j ∈ Finset.range 36, vf919SharpQuotientKernel36 (a + j)) = 0 := by
  induction a with
  | zero =>
      simpa only [Nat.zero_add] using vf919SharpQuotientKernel36_mean_zero
  | succ a ih =>
      have hshift := vf919Kernel36_shift_range_sum
        (fun j => vf919SharpQuotientKernel36 (a + j)) 36
      have hper := vf919SharpQuotientKernel36_period a
      calc
        (∑ j ∈ Finset.range 36, vf919SharpQuotientKernel36 (a + 1 + j)) =
            ∑ j ∈ Finset.range 36,
              vf919SharpQuotientKernel36 (a + (j + 1)) := by
                apply Finset.sum_congr rfl
                intro j _hj
                congr 1
                omega
        _ = (∑ j ∈ Finset.range 36, vf919SharpQuotientKernel36 (a + j)) -
              vf919SharpQuotientKernel36 a +
              vf919SharpQuotientKernel36 (a + 36) := by
                simpa using hshift
        _ = (∑ j ∈ Finset.range 36, vf919SharpQuotientKernel36 (a + j)) := by
              rw [hper]
              ring
        _ = 0 := ih

/-- Every fixed actual norm coefficient has an exact signed return after
36*m consecutive endpoint cutoffs once it has entered the support.
The occurrence is kept, and the integer cutoff n/m is used literally.
The result holds for any positive m and starting quotient a. -/
theorem vf919EachNormFull36mCutoffReturn (m a : ℕ) (hm : 0 < m) :
    (∑ j ∈ Finset.range 36,
      ∑ r ∈ Finset.range m,
        vf919SharpQuotientKernel36 ((m * (a + j) + r) / m)) = 0 := by
  calc
    (∑ j ∈ Finset.range 36,
        ∑ r ∈ Finset.range m,
          vf919SharpQuotientKernel36 ((m * (a + j) + r) / m)) =
      ∑ j ∈ Finset.range 36,
        ∑ r ∈ Finset.range m,
          vf919SharpQuotientKernel36 (a + j) := by
            apply Finset.sum_congr rfl
            intro j _hj
            apply Finset.sum_congr rfl
            intro r hr
            have hquot : (m * (a + j) + r) / m = a + j := by
              rw [Nat.mul_add_div hm, Nat.div_eq_of_lt (Finset.mem_range.mp hr)]
              omega
            rw [hquot]
    _ = ∑ j ∈ Finset.range 36,
          (m : ℤ) * vf919SharpQuotientKernel36 (a + j) := by
        apply Finset.sum_congr rfl
        intro j _hj
        simp [Finset.sum_const]
    _ = (m : ℤ) * (∑ j ∈ Finset.range 36,
          vf919SharpQuotientKernel36 (a + j)) := by
        rw [Finset.mul_sum]
    _ = 0 := by rw [vf919QuotientKernel36_all_start_zero]; ring


/-! ## Unconditional but potentially weak signed-cutoff variation ceiling -/

/-- The finite quotient primitive is bounded by four even as a complex
coefficient. This uses ONLY the explicit 36-element table. -/
theorem vf919QuotientKernelPrimitive36_norm_le_four (t : ℕ) :
    ‖(vf919QuotientKernelPrimitive36 t : ℂ)‖ ≤ (4 : ℝ) := by
  rw [Complex.norm_intCast]
  have habs : |vf919QuotientKernelPrimitive36 t| ≤ (4 : ℤ) :=
    abs_le.mpr (vf919QuotientKernelPrimitive36_bounds t)
  exact_mod_cast habs

/-- A genuine all-cutoff coefficient inequality with NO numerical premise.
The open arithmetic task is to bound the signed bucket VARIATION; the
numerical observation V_X ~ sqrt(X) log X is not inserted here. -/
theorem vf919Mertens_norm_le_four_quotient_variation
    (X : ℕ) (hX : 12 ≤ X) :
    ‖(∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.moebius n : ℂ))‖ ≤
      4 * (∑ t ∈ Finset.Icc 1 X,
        ‖vf919QuotientBucket X t - vf919QuotientBucket X (t + 1)‖) := by
  rw [vf919Mertens_eq_exact_signed_quotient_return X hX]
  calc
    ‖∑ t ∈ Finset.Icc 1 X,
        (vf919QuotientKernelPrimitive36 t : ℂ) *
          (vf919QuotientBucket X t - vf919QuotientBucket X (t + 1))‖ ≤
      ∑ t ∈ Finset.Icc 1 X,
        ‖(vf919QuotientKernelPrimitive36 t : ℂ) *
          (vf919QuotientBucket X t - vf919QuotientBucket X (t + 1))‖ :=
        norm_sum_le _ _
    _ = ∑ t ∈ Finset.Icc 1 X,
        ‖(vf919QuotientKernelPrimitive36 t : ℂ)‖ *
          ‖vf919QuotientBucket X t - vf919QuotientBucket X (t + 1)‖ := by
        simp_rw [norm_mul]
    _ ≤ ∑ t ∈ Finset.Icc 1 X,
        (4 : ℝ) * ‖vf919QuotientBucket X t - vf919QuotientBucket X (t + 1)‖ := by
        apply Finset.sum_le_sum
        intro t _ht
        exact mul_le_mul_of_nonneg_right
          (vf919QuotientKernelPrimitive36_norm_le_four t) (norm_nonneg _)
    _ = 4 * (∑ t ∈ Finset.Icc 1 X,
          ‖vf919QuotientBucket X t - vf919QuotientBucket X (t + 1)‖) := by
        rw [Finset.mul_sum]

end RHLean.Analysis

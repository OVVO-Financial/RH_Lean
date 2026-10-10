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
      simp [vf919QuotientKernelPrimitive36]
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

end RHLean.Analysis

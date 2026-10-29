import Mathlib
import RHLean.Analysis.CanonicalLowOccupancy

/-!
# Off-critical LOW/HIGH: genuine integer coefficients and absolute LOW occupancy

The canonical signed height cut partitions each ACTUAL Mobius coefficient.
This module first proves a global, all-integer positive-mass census for LOW,
not just a signed square-prefix estimate. It is an unconditional arithmetic
input for the later LOW Dirichlet-series half-plane.

No zeta-zero assumption, conjectural cancellation, or project axiom occurs.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- The literal canonical LOW Mobius coefficient at every natural integer. -/
def offcriticalLowCoefficient (Lambda : ℝ) (m : ℕ) : ℂ :=
  if IsCanonicalLowHeight Lambda (Nat.sqrt m) m then
    canonicalMoebiusWeight m else 0

/-- The literal complementary canonical HIGH Mobius coefficient. -/
def offcriticalHighCoefficient (Lambda : ℝ) (m : ℕ) : ℂ :=
  if IsCanonicalHighHeight Lambda (Nat.sqrt m) m then
    canonicalMoebiusWeight m else 0

/-- Coefficient-level LOW plus HIGH equals the original Mobius atom. -/
theorem offcriticalLow_add_high_eq_moebius
    (Lambda : ℝ) (m : ℕ) :
    offcriticalLowCoefficient Lambda m +
      offcriticalHighCoefficient Lambda m =
        canonicalMoebiusWeight m := by
  by_cases h : IsCanonicalLowHeight Lambda (Nat.sqrt m) m
  · simp [offcriticalLowCoefficient, offcriticalHighCoefficient,
      IsCanonicalHighHeight, h]
  · simp [offcriticalLowCoefficient, offcriticalHighCoefficient,
      IsCanonicalHighHeight, h]

/-- The genuine nonzero LOW support up to EVERY integer N. -/
def offcriticalLowSupportUpTo (Lambda : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun m =>
    μ m ≠ 0 ∧ IsCanonicalLowHeight Lambda (Nat.sqrt m) m

/-- The support of a LOW atom lies in its UNIQUE integer square block. -/
theorem offcriticalLowSupport_mem_squareBlock
    {Lambda : ℝ} {N m : ℕ}
    (hm : m ∈ offcriticalLowSupportUpTo Lambda N) :
    m ∈ canonicalLowSupport Lambda (Nat.sqrt m) := by
  classical
  change m ∈ (Finset.range (N + 1)).filter
    (fun x => μ x ≠ 0 ∧ IsCanonicalLowHeight Lambda (Nat.sqrt x) x) at hm
  rcases Finset.mem_filter.mp hm with ⟨_hmN, hmMu, hmLow⟩
  have hmBlock :
      m ∈ canonicalSquareBlock (Nat.sqrt m) := by
    change m ∈ Finset.Ico ((Nat.sqrt m) ^ 2) ((Nat.sqrt m + 1) ^ 2)
    exact Finset.mem_Ico.mpr ⟨Nat.sqrt_le' m, Nat.lt_succ_sqrt' m⟩
  exact Finset.mem_filter.mpr ⟨hmBlock, hmMu, hmLow⟩

/-- At any natural cutoff N, the number of nonzero LOW coefficients grows
at most at square-root scale, with the EXACT fixed-height occupancy constant.
No Mobius cancellation is needed. -/
theorem offcriticalLowSupport_card_le
    (Lambda : ℝ) (N : ℕ) :
    (offcriticalLowSupportUpTo Lambda N).card ≤
      (Nat.sqrt N + 1) * (Nat.floor Lambda + 1) := by
  classical
  let cover : Finset ℕ :=
    (Finset.range (Nat.sqrt N + 1)).biUnion
      (canonicalLowSupport Lambda)
  have hsub : offcriticalLowSupportUpTo Lambda N ⊆ cover := by
    intro m hm
    have hmrange :
        m ∈ Finset.range (N + 1) :=
      (Finset.mem_filter.mp (show m ∈
          (Finset.range (N + 1)).filter
            (fun x => μ x ≠ 0 ∧ IsCanonicalLowHeight Lambda (Nat.sqrt x) x)
        from hm)).1
    have hmle : m ≤ N := by
      have hmlt := Finset.mem_range.mp hmrange
      omega
    have hroot : Nat.sqrt m ≤ Nat.sqrt N :=
      Nat.sqrt_le_sqrt hmle
    exact Finset.mem_biUnion.mpr
      ⟨Nat.sqrt m, Finset.mem_range.mpr (by omega),
       offcriticalLowSupport_mem_squareBlock hm⟩
  calc
    (offcriticalLowSupportUpTo Lambda N).card ≤ cover.card :=
      Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range (Nat.sqrt N + 1),
          (canonicalLowSupport Lambda j).card := by
            exact Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.range (Nat.sqrt N + 1),
          (Nat.floor Lambda + 1) := by
            apply Finset.sum_le_sum
            intro j _hj
            exact card_canonicalLowSupport_le_floor_add_one Lambda j
    _ = (Nat.sqrt N + 1) * (Nat.floor Lambda + 1) := by simp

/-- All-integer absolute LOW mass satisfies the same unconditional
square-root occupancy estimate. This is STRONGER than a signed prefix bound,
and is the correct input for absolute Dirichlet-series convergence. -/
theorem offcriticalLow_normSum_le
    (Lambda : ℝ) (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1),
      ‖offcriticalLowCoefficient Lambda m‖) ≤
        (((Nat.sqrt N + 1) * (Nat.floor Lambda + 1) : ℕ) : ℝ) := by
  classical
  calc
    (∑ m ∈ Finset.range (N + 1),
        ‖offcriticalLowCoefficient Lambda m‖) ≤
      ∑ m ∈ Finset.range (N + 1),
        if μ m ≠ 0 ∧ IsCanonicalLowHeight Lambda (Nat.sqrt m) m
        then (1 : ℝ) else 0 := by
          apply Finset.sum_le_sum
          intro m _hm
          by_cases hmMu : μ m = 0
          · simp [offcriticalLowCoefficient, canonicalMoebiusWeight, hmMu]
          · by_cases hmLow : IsCanonicalLowHeight Lambda (Nat.sqrt m) m
            · simpa [offcriticalLowCoefficient, hmMu, hmLow] using
                norm_canonicalMoebiusWeight_le_one m
            · simp [offcriticalLowCoefficient, hmLow]
    _ = ((offcriticalLowSupportUpTo Lambda N).card : ℝ) := by
          simp [offcriticalLowSupportUpTo]
    _ ≤ (((Nat.sqrt N + 1) * (Nat.floor Lambda + 1) : ℕ) : ℝ) := by
          exact_mod_cast offcriticalLowSupport_card_le Lambda N

/-! ## Absolute Dirichlet series beyond the critical line -/

open Filter Asymptotics

/-- The absolute mass of the actual canonical LOW coefficients is
O(N^(1/2)) at all natural cutoffs, not merely on square endpoints. -/
theorem offcriticalLow_absoluteMass_isBigO (Lambda : ℝ) :
    (fun N : ℕ => ∑ m ∈ Finset.Icc 1 N,
      ‖offcriticalLowCoefficient Lambda m‖) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 2)) := by
  let C : ℝ := (Nat.floor Lambda : ℝ) + 1
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine IsBigO.of_bound (2 * C) ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hsub : Finset.Icc 1 N ⊆ Finset.range (N + 1) := by
    intro m hm
    have hmle := (Finset.mem_Icc.mp hm).2
    exact Finset.mem_range.mpr (by omega)
  have hIcc :
      (∑ m ∈ Finset.Icc 1 N,
        ‖offcriticalLowCoefficient Lambda m‖) ≤
      ∑ m ∈ Finset.range (N + 1),
        ‖offcriticalLowCoefficient Lambda m‖ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro m _hm _hnot
    exact norm_nonneg _
  have hMass := offcriticalLow_normSum_le Lambda N
  have hSq : ((Nat.sqrt N : ℝ) ^ 2) ≤ (N : ℝ) := by
    exact_mod_cast Nat.sqrt_le' N
  have hSqrtSq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg N)
  have hSqrtPos : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hRootPos : 0 ≤ (Nat.sqrt N : ℝ) := Nat.cast_nonneg _
  have hRoot : (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) := by
    nlinarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN
  have hSqrtOne : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    nlinarith
  have hCmul :
      ((Nat.sqrt N : ℝ) + 1) * C ≤
        (2 * C) * Real.sqrt (N : ℝ) := by
    nlinarith
  have hNonneg :
      0 ≤ (∑ m ∈ Finset.Icc 1 N,
        ‖offcriticalLowCoefficient Lambda m‖) :=
    Finset.sum_nonneg (by intro m _hm; exact norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hNonneg]
  rw [Real.norm_eq_abs, abs_of_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg N) _)]
  calc
    (∑ m ∈ Finset.Icc 1 N,
        ‖offcriticalLowCoefficient Lambda m‖) ≤
      ∑ m ∈ Finset.range (N + 1),
        ‖offcriticalLowCoefficient Lambda m‖ := hIcc
    _ ≤ (((Nat.sqrt N + 1) * (Nat.floor Lambda + 1) : ℕ) : ℝ) :=
      hMass
    _ = ((Nat.sqrt N : ℝ) + 1) * C := by
      simp [C, Nat.cast_mul]
    _ ≤ (2 * C) * Real.sqrt (N : ℝ) := hCmul
    _ = (2 * C) * ((N : ℝ) ^ ((1 : ℝ) / 2)) := by
      rw [Real.sqrt_eq_rpow]

/-- Mathlib's Abel summation theorem turns the unconditional sparse absolute
LOW census into ABSOLUTE convergence of the genuine LOW Dirichlet series
throughout the open half-plane Re(s) > 1/2. -/
theorem offcriticalLow_LSeriesSummable
    (Lambda : ℝ) {s : ℂ} (hs : (1 : ℝ) / 2 < s.re) :
    LSeriesSummable (offcriticalLowCoefficient Lambda) s := by
  exact LSeriesSummable_of_sum_norm_bigO
    (offcriticalLow_absoluteMass_isBigO Lambda)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hs

/-- The LOW series is holomorphic at every point strictly to the right
of Re(s)=1/2. The theorem uses ACTUAL Mobius coefficient filtering only. -/
theorem offcriticalLow_LSeries_differentiableAt
    (Lambda : ℝ) {s : ℂ} (hs : (1 : ℝ) / 2 < s.re) :
    DifferentiableAt ℂ (LSeries (offcriticalLowCoefficient Lambda)) s := by
  have habsc :
      LSeries.abscissaOfAbsConv (offcriticalLowCoefficient Lambda) ≤
        ((1 : ℝ) / 2 : EReal) := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro y hy
    exact offcriticalLow_LSeriesSummable Lambda
      (s := (y : ℂ)) (by simpa using hy)
  have hpoint : ((1 : ℝ) / 2 : EReal) < (s.re : EReal) := by
    exact EReal.coe_lt_coe_iff.mpr hs
  exact (LSeries_hasDerivAt (habsc.trans_lt hpoint)).differentiableAt

/-- The genuine fixed-height LOW Dirichlet series is fully analytic,
not merely differentiable, throughout Re(s)>1/2. This is unconditional. -/
theorem offcriticalLow_LSeries_analyticAt
    (Lambda : ℝ) {s : ℂ} (hs : (1 : ℝ) / 2 < s.re) :
    AnalyticAt ℂ (LSeries (offcriticalLowCoefficient Lambda)) s := by
  have habsc :
      LSeries.abscissaOfAbsConv (offcriticalLowCoefficient Lambda) ≤
        ((1 : ℝ) / 2 : EReal) := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro y hy
    exact offcriticalLow_LSeriesSummable Lambda
      (s := (y : ℂ)) (by simpa using hy)
  have hlt :
      LSeries.abscissaOfAbsConv (offcriticalLowCoefficient Lambda) <
        (s.re : EReal) :=
    lt_of_le_of_lt habsc (EReal.coe_lt_coe_iff.mpr hs)
  exact (LSeries_analyticOnNhd (offcriticalLowCoefficient Lambda)) s hlt

end RHLean.Proof

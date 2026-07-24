import Mathlib
import RHLean.Analysis.GeometricRHReduction

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- The complex-valued Mertens summatory function, including the harmless `mu(0) = 0` term. -/
def mertensSummatory (x : ℕ) : ℂ :=
  ∑ m in Finset.range (x + 1), (((μ m : ℤ) : ℂ))

/-- The manuscript's exact complete-square endpoint `X_n = (n+1)^2 - 1`. -/
def squarePrefixEndpoint (n : ℕ) : ℕ :=
  (n + 1) ^ 2 - 1

/-- The manuscript's square-prefix value `S_n = M((n+1)^2 - 1)`. -/
def squarePrefixMertens (n : ℕ) : ℂ :=
  mertensSummatory (squarePrefixEndpoint n)

@[simp] theorem mertensSummatory_zero : mertensSummatory 0 = 0 := by
  simp [mertensSummatory]

@[simp] theorem mertensSummatory_succ (x : ℕ) :
    mertensSummatory (x + 1) =
      mertensSummatory x + (((μ (x + 1) : ℤ) : ℂ)) := by
  simp [mertensSummatory, Finset.sum_range_succ, add_assoc]

private theorem norm_moebius_cast_le_one (n : ℕ) :
    ‖(((μ n : ℤ) : ℂ))‖ ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h
  · simp [h]
  · simp [h]
  · simp [h]

/-- The Mertens function changes by at most the length of an integer interval. -/
theorem norm_mertensSummatory_sub_le (a b : ℕ) (hab : a ≤ b) :
    ‖mertensSummatory b - mertensSummatory a‖ ≤ ((b - a : ℕ) : ℝ) := by
  induction b with
  | zero =>
      have ha : a = 0 := Nat.eq_zero_of_le_zero hab
      subst a
      simp
  | succ b ih =>
      by_cases ha : a = b + 1
      · subst a
        simp
      · have hab' : a ≤ b := by omega
        calc
          ‖mertensSummatory (b + 1) - mertensSummatory a‖ =
              ‖(mertensSummatory b - mertensSummatory a) +
                (((μ (b + 1) : ℤ) : ℂ))‖ := by
            rw [mertensSummatory_succ]
            congr 1
            ring
          _ ≤ ‖mertensSummatory b - mertensSummatory a‖ +
                ‖(((μ (b + 1) : ℤ) : ℂ))‖ := norm_add_le _ _
          _ ≤ ((b - a : ℕ) : ℝ) + 1 :=
            add_le_add (ih hab') (norm_moebius_cast_le_one (b + 1))
          _ = (((b + 1) - a : ℕ) : ℝ) := by
            congr 1
            omega

/-- The endpoint immediately precedes the next square. -/
theorem squarePrefixEndpoint_add_one (n : ℕ) :
    squarePrefixEndpoint n + 1 = (n + 1) ^ 2 := by
  unfold squarePrefixEndpoint
  have h : 1 ≤ (n + 1) ^ 2 := by positivity
  exact Nat.sub_add_cancel h

private theorem rpow_sq_one_add_half (x ε : ℝ) (hx : 0 ≤ x) :
    Real.rpow (x ^ 2) (1 + ε / 2) = Real.rpow x (2 + ε) := by
  calc
    Real.rpow (x ^ 2) (1 + ε / 2) =
        Real.rpow (Real.rpow x (2 : ℝ)) (1 + ε / 2) := by
      rw [Real.rpow_natCast]
    _ = Real.rpow x ((2 : ℝ) * (1 + ε / 2)) := by
      rw [← Real.rpow_mul hx]
    _ = Real.rpow x (2 + ε) := by ring_nf

private theorem rpow_two_add_two_mul (x ε : ℝ) (hx : 0 ≤ x) :
    Real.rpow x (2 + 2 * ε) = Real.rpow (x ^ 2) (1 + ε) := by
  calc
    Real.rpow x (2 + 2 * ε) = Real.rpow x ((2 : ℝ) * (1 + ε)) := by ring_nf
    _ = Real.rpow (Real.rpow x (2 : ℝ)) (1 + ε) :=
      Real.rpow_mul hx (2 : ℝ) (1 + ε)
    _ = Real.rpow (x ^ 2) (1 + ε) := by rw [Real.rpow_natCast]

/-- The standard squared Mertens growth criterion, with critical exponent `1`. -/
def MertensEnergyBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℕ,
        ‖mertensSummatory x‖ ^ 2 ≤
          C * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε)

/-- The exact square-prefix squared growth criterion, with critical exponent `2`. -/
def SquarePrefixEnergyBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ,
        ‖squarePrefixMertens n‖ ^ 2 ≤
          C * Real.rpow ((n + 1 : ℕ) : ℝ) (2 + ε)

private theorem norm_sq_add_le_two (x y : ℂ) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have hnorm := norm_add_le x y
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hxy : 0 ≤ ‖x + y‖ := norm_nonneg (x + y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- The full Mertens criterion implies the exact square-prefix criterion without loss. -/
theorem squarePrefixEnergyBounded_of_mertensEnergyBounded
    (hM : MertensEnergyBoundedStatement) :
    SquarePrefixEnergyBoundedStatement := by
  intro ε hε
  rcases hM (ε / 2) (by linarith) with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro n
  have hendpoint :
      ((squarePrefixEndpoint n + 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast squarePrefixEndpoint_add_one n
  calc
    ‖squarePrefixMertens n‖ ^ 2 =
        ‖mertensSummatory (squarePrefixEndpoint n)‖ ^ 2 := rfl
    _ ≤ C * Real.rpow ((squarePrefixEndpoint n + 1 : ℕ) : ℝ)
          (1 + ε / 2) := hbound (squarePrefixEndpoint n)
    _ = C * Real.rpow (((n + 1 : ℕ) : ℝ) ^ 2) (1 + ε / 2) := by
      rw [hendpoint]
    _ = C * Real.rpow ((n + 1 : ℕ) : ℝ) (2 + ε) := by
      rw [rpow_sq_one_add_half]
      positivity

/-- Square-prefix control interpolates to the full Mertens criterion using `|mu| <= 1`. -/
theorem mertensEnergyBounded_of_squarePrefixEnergyBounded
    (hS : SquarePrefixEnergyBoundedStatement) :
    MertensEnergyBoundedStatement := by
  intro ε hε
  rcases hS (2 * ε) (by linarith) with ⟨C, hC, hbound⟩
  refine ⟨2 * C + 32, by positivity, ?_⟩
  intro x
  by_cases hx0 : x = 0
  · subst x
    simp [mertensSummatory]
  · let r := Nat.sqrt x
    have hr : 1 ≤ r := by
      dsimp [r]
      exact Nat.sqrt_pos.mpr (Nat.pos_of_ne_zero hx0)
    let n := r - 1
    have hn1 : n + 1 = r := by
      dsimp [n]
      omega
    have hendpoint : squarePrefixEndpoint n = r ^ 2 - 1 := by
      unfold squarePrefixEndpoint
      rw [hn1]
    have hr_sq_le : r ^ 2 ≤ x := by
      dsimp [r]
      exact Nat.sqrt_le' x
    have hendpoint_le : squarePrefixEndpoint n ≤ x := by
      rw [hendpoint]
      exact le_trans (Nat.sub_le _ _) hr_sq_le
    have hgapNat : x - squarePrefixEndpoint n ≤ 2 * (r + 1) := by
      have hx_lt : x < (r + 1) ^ 2 := by
        dsimp [r]
        exact Nat.lt_succ_sqrt' x
      rw [hendpoint]
      omega
    have hgap := norm_mertensSummatory_sub_le (squarePrefixEndpoint n) x hendpoint_le
    have hgapR :
        ‖mertensSummatory x - squarePrefixMertens n‖ ≤ 2 * (r + 1 : ℝ) := by
      rw [squarePrefixMertens]
      exact hgap.trans (by exact_mod_cast hgapNat)
    have hgapSq :
        ‖mertensSummatory x - squarePrefixMertens n‖ ^ 2 ≤
          4 * (r + 1 : ℝ) ^ 2 := by
      have hnonneg : 0 ≤ ‖mertensSummatory x - squarePrefixMertens n‖ := norm_nonneg _
      have hrnonneg : 0 ≤ (r + 1 : ℝ) := by positivity
      nlinarith
    have hsample := hbound n
    have hsampleR :
        ‖squarePrefixMertens n‖ ^ 2 ≤
          C * Real.rpow (r : ℝ) (2 + 2 * ε) := by
      simpa [hn1] using hsample
    have hexp : 0 ≤ 1 + ε := by linarith
    have hrpowSample :
        Real.rpow (r : ℝ) (2 + 2 * ε) ≤
          Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := by
      rw [rpow_two_add_two_mul]
      · apply Real.rpow_le_rpow
        · positivity
        · exact_mod_cast (hr_sq_le.trans (Nat.le_succ x))
        · exact hexp
      · positivity
    have hrplusSq : (r + 1 : ℝ) ^ 2 ≤ 4 * ((x + 1 : ℕ) : ℝ) := by
      have hr_le_x : r ≤ x := by
        dsimp [r]
        exact Nat.sqrt_le_self x
      have hrR : (r : ℝ) ≤ (x : ℝ) := by exact_mod_cast hr_le_x
      have hxR : 1 ≤ (x : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hx0)
      have hsqrt : (r : ℝ) ^ 2 ≤ (x : ℝ) := by exact_mod_cast hr_sq_le
      nlinarith
    have hbasePow :
        ((x + 1 : ℕ) : ℝ) ≤
          Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := by
      have hbase : (1 : ℝ) ≤ ((x + 1 : ℕ) : ℝ) := by positivity
      have hone : (1 : ℝ) ≤ 1 + ε := by linarith
      simpa [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hbase hone
    have hsampleFinal :
        ‖squarePrefixMertens n‖ ^ 2 ≤
          C * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) :=
      hsampleR.trans (mul_le_mul_of_nonneg_left hrpowSample hC)
    calc
      ‖mertensSummatory x‖ ^ 2 =
          ‖squarePrefixMertens n +
            (mertensSummatory x - squarePrefixMertens n)‖ ^ 2 := by
        congr 1
        ring
      _ ≤ 2 * ‖squarePrefixMertens n‖ ^ 2 +
            2 * ‖mertensSummatory x - squarePrefixMertens n‖ ^ 2 :=
        norm_sq_add_le_two _ _
      _ ≤ 2 * (C * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε)) +
            2 * (4 * (r + 1 : ℝ) ^ 2) := by
        nlinarith
      _ ≤ 2 * (C * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε)) +
            32 * ((x + 1 : ℕ) : ℝ) := by
        nlinarith
      _ ≤ (2 * C + 32) *
            Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := by
        nlinarith

/-- Square sampling loses no information at the critical Mertens growth scale. -/
theorem mertensEnergyBounded_iff_squarePrefixEnergyBounded :
    MertensEnergyBoundedStatement ↔ SquarePrefixEnergyBoundedStatement := by
  exact ⟨squarePrefixEnergyBounded_of_mertensEnergyBounded,
    mertensEnergyBounded_of_squarePrefixEnergyBounded⟩

/-- The current project pointwise criterion, specialized to the concrete square-prefix sequence. -/
def SquarePrefixCurrentPointwiseBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : ℕ, 1 ≤ N →
        ‖squarePrefixMertens N‖ ^ 2 ≤
          C * Real.rpow (N : ℝ) (2 + ε)

/-- The shifted exact square-prefix criterion and the current project criterion are equivalent. -/
theorem squarePrefixEnergyBounded_iff_currentPointwise :
    SquarePrefixEnergyBoundedStatement ↔
      SquarePrefixCurrentPointwiseBoundedStatement := by
  constructor
  · intro hshift ε hε
    rcases hshift ε hε with ⟨C, hC, hbound⟩
    let K := Real.rpow 2 (2 + ε)
    refine ⟨C * K, mul_nonneg hC (Real.rpow_nonneg (by norm_num) _), ?_⟩
    intro N hN
    have hNadd : ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
      exact_mod_cast (by omega : N + 1 ≤ 2 * N)
    have hexp : 0 ≤ 2 + ε := by linarith
    have hp := Real.rpow_le_rpow (by positivity) hNadd hexp
    calc
      ‖squarePrefixMertens N‖ ^ 2 ≤
          C * Real.rpow ((N + 1 : ℕ) : ℝ) (2 + ε) := hbound N
      _ ≤ C * Real.rpow (2 * (N : ℝ)) (2 + ε) :=
        mul_le_mul_of_nonneg_left hp hC
      _ = (C * K) * Real.rpow (N : ℝ) (2 + ε) := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]
        ring
  · intro hcurrent ε hε
    rcases hcurrent ε hε with ⟨C, hC, hbound⟩
    let Z := ‖squarePrefixMertens 0‖ ^ 2
    refine ⟨C + Z, add_nonneg hC (sq_nonneg _), ?_⟩
    intro n
    by_cases hn0 : n = 0
    · subst n
      simp [Z]
    · have hn : 1 ≤ n := Nat.pos_of_ne_zero hn0
      have h := hbound n hn
      have hbase : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
      have hexp : 0 ≤ 2 + ε := by linarith
      have hp := Real.rpow_le_rpow (by positivity) hbase hexp
      calc
        ‖squarePrefixMertens n‖ ^ 2 ≤
            C * Real.rpow (n : ℝ) (2 + ε) := h
        _ ≤ C * Real.rpow ((n + 1 : ℕ) : ℝ) (2 + ε) :=
          mul_le_mul_of_nonneg_left hp hC
        _ ≤ (C + Z) * Real.rpow ((n + 1 : ℕ) : ℝ) (2 + ε) := by
          gcongr
          exact sq_nonneg _

/-- Future mathlib integration needs to provide only this standard classical theorem. -/
structure ClassicalMertensRHCriterion where
  iff_riemannHypothesis :
    MertensEnergyBoundedStatement ↔ RiemannHypothesisStatement

/-- A concrete identification of an actual-start sequence with the manuscript's `S_n`. -/
structure ActualStartSquarePrefixRealization
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data) where
  actual_eq_squarePrefix : ∀ n, start.actual n = squarePrefixMertens n

/-- The current actual-start pointwise criterion is exactly the concrete square-prefix criterion. -/
theorem actualStart_pointwiseSquareBounded_iff_squarePrefixCurrent
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (realization : ActualStartSquarePrefixRealization start) :
    ActualStartPointwiseSquareBoundedStatement start ↔
      SquarePrefixCurrentPointwiseBoundedStatement := by
  constructor <;> intro h ε hε
  · rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro N hN
    simpa [realization.actual_eq_squarePrefix] using hbound N hN
  · rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro N hN
    simpa [realization.actual_eq_squarePrefix] using hbound N hN

/-- Pointwise actual-start control implies uniform local control by a direct window sum. -/
theorem actualStart_uniformLocalBounded_of_pointwiseSquareBounded
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (hpoint : ActualStartPointwiseSquareBoundedStatement start) :
    ActualStartUniformLocalBoundedStatement start := by
  intro ε hε
  rcases hpoint ε hε with ⟨C, hC, hbound⟩
  let K := Real.rpow 2 (2 + ε)
  refine ⟨C * K, mul_nonneg hC (Real.rpow_nonneg (by norm_num) _), ?_⟩
  intro N H hH hHN
  have hN : 1 ≤ N := hH.trans hHN
  unfold actualStartLocalFrameEnergy
  calc
    (∑ h ∈ Finset.range H, ‖start.actual (N + h)‖ ^ 2) ≤
        ∑ _h ∈ Finset.range H,
          (C * K) * Real.rpow (N : ℝ) (2 + ε) := by
      apply Finset.sum_le_sum
      intro h hh
      have hhlt : h < H := Finset.mem_range.mp hh
      have hindex : 1 ≤ N + h := le_add_right hN
      have hboundIndex := hbound (N + h) hindex
      have hindexNat : N + h ≤ 2 * N := by omega
      have hindexR : ((N + h : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hindexNat
      have hexp : 0 ≤ 2 + ε := by linarith
      have hp := Real.rpow_le_rpow (by positivity) hindexR hexp
      calc
        ‖start.actual (N + h)‖ ^ 2 ≤
            C * Real.rpow ((N + h : ℕ) : ℝ) (2 + ε) := hboundIndex
        _ ≤ C * Real.rpow (2 * (N : ℝ)) (2 + ε) :=
          mul_le_mul_of_nonneg_left hp hC
        _ = (C * K) * Real.rpow (N : ℝ) (2 + ε) := by
          rw [Real.mul_rpow (by norm_num) (by positivity)]
          ring
    _ = (H : ℝ) * ((C * K) * Real.rpow (N : ℝ) (2 + ε)) := by simp
    _ = (C * K) * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε) := by ring

/-- Uniform local and pointwise actual-start criteria are equivalent. -/
theorem actualStart_uniformLocalBounded_iff_pointwiseSquareBounded
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data) :
    ActualStartUniformLocalBoundedStatement start ↔
      ActualStartPointwiseSquareBoundedStatement start := by
  exact ⟨actualStart_pointwiseSquareBounded_of_uniformLocalBounded start,
    actualStart_uniformLocalBounded_of_pointwiseSquareBounded start⟩

/-- The concrete actual-start criterion is RH once the standard classical theorem is supplied. -/
theorem actualStart_uniformLocalBounded_iff_riemannHypothesis_of_mertens
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (realization : ActualStartSquarePrefixRealization start)
    (criterion : ClassicalMertensRHCriterion) :
    ActualStartUniformLocalBoundedStatement start ↔
      RiemannHypothesisStatement := by
  calc
    ActualStartUniformLocalBoundedStatement start ↔
        ActualStartPointwiseSquareBoundedStatement start :=
      actualStart_uniformLocalBounded_iff_pointwiseSquareBounded start
    _ ↔ SquarePrefixCurrentPointwiseBoundedStatement :=
      actualStart_pointwiseSquareBounded_iff_squarePrefixCurrent start realization
    _ ↔ SquarePrefixEnergyBoundedStatement :=
      squarePrefixEnergyBounded_iff_currentPointwise.symm
    _ ↔ MertensEnergyBoundedStatement :=
      mertensEnergyBounded_iff_squarePrefixEnergyBounded.symm
    _ ↔ RiemannHypothesisStatement := criterion.iff_riemannHypothesis

/-- The existing bridge structure is constructed mechanically from the canonical Mertens adapter. -/
def ActualStartRHBridge.ofMertens
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (localSignedFrame_to_uniformLocalBounded :
      ActualStartLocalSignedFrameStatement start →
        ActualStartUniformLocalBoundedStatement start)
    (realization : ActualStartSquarePrefixRealization start)
    (criterion : ClassicalMertensRHCriterion) :
    ActualStartRHBridge start where
  localSignedFrame_to_uniformLocalBounded :=
    localSignedFrame_to_uniformLocalBounded
  riemannHypothesis_to_uniformLocalBounded :=
    (actualStart_uniformLocalBounded_iff_riemannHypothesis_of_mertens
      start realization criterion).mpr
  pointwiseSquareBounded_to_riemannHypothesis := fun hpoint =>
    (actualStart_uniformLocalBounded_iff_riemannHypothesis_of_mertens
      start realization criterion).mp
      (actualStart_uniformLocalBounded_of_pointwiseSquareBounded start hpoint)

/-- No project-specific RH bridge remains in the final geometric equivalence theorem. -/
theorem actualStart_highUniformLocalBounded_iff_riemannHypothesis_of_mertens
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (partition : ActualStartGeometricPartition start)
    (realization : ActualStartSquarePrefixRealization start)
    (criterion : ClassicalMertensRHCriterion) :
    ActualStartHighUniformLocalBoundedStatement partition ↔
      RiemannHypothesisStatement := by
  calc
    ActualStartHighUniformLocalBoundedStatement partition ↔
        ActualStartUniformLocalBoundedStatement start :=
      (actualStart_uniformLocalBounded_iff_highUniformLocalBounded
        start partition).symm
    _ ↔ RiemannHypothesisStatement :=
      actualStart_uniformLocalBounded_iff_riemannHypothesis_of_mertens
        start realization criterion

end RHLean.Analysis

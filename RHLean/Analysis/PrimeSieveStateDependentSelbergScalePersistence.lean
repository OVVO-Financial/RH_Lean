import Mathlib
import RHLean.Analysis.NativePNTCubicContractionInequality
import RHLean.Analysis.PrimeSieveStateDependentSelbergPositiveGainClosure

/-!
# Effective persistence for state-dependent Selberg gain

A pointwise positive-gain theorem becomes quantitatively useful only when the
improved slope persists on an entire tail at a controlled physical scale.
This module isolates that deterministic step and its bound-changing scale
consequence.

Crucially, the physical cutoff is held fixed only through the finite cubic
chain needed to reach a requested target slope.  No claim of infinite
fixed-scale contraction is made.
-/

noncomputable section

namespace RHLean.Analysis

def PrimeSieveStateDependentSelbergTailAbove
    (M : Nat) (alpha : Real) : Prop :=
  2 <= M ∧ 0 < alpha ∧
    forall q : Nat, M <= q ->
      |nativePNTError q| <= alpha * (q : Real)

def PrimeSieveStateDependentSelbergCubicGainAbove
    (M : Nat) (alpha c : Real) : Prop :=
  forall N : Nat, M <= N ->
    ∃ beta : Real,
      0 <= beta ∧ beta < alpha ∧
        PrimeSieveStateDependentSelbergStateHasPowerGain
          c 3 N M alpha beta

theorem primeSieveStateDependentSelberg_cubicGainAbove_step
    (M : Nat) (alpha c : Real)
    (htail : PrimeSieveStateDependentSelbergTailAbove M alpha)
    (hgain : PrimeSieveStateDependentSelbergCubicGainAbove M alpha c)
    (hnext : 0 < alpha - c * alpha ^ 3) :
    PrimeSieveStateDependentSelbergTailAbove
      M (alpha - c * alpha ^ 3) := by
  rcases htail with ⟨hM2, halpha, htail⟩
  refine ⟨hM2, hnext, ?_⟩
  intro N hMN
  rcases hgain N hMN with ⟨beta, hbeta0, hbeta, hpower⟩
  have hN2 : 2 <= N := hM2.trans hMN
  have hM1 : 1 <= M := by omega
  have hadm :
      PrimeSieveStateDependentSelbergAdmissible N M alpha beta :=
    ⟨⟨hN2, hM1, hMN, halpha, htail⟩, hbeta0, hbeta⟩
  exact primeSieveStateDependentSelberg_error_le_power_contraction
    N M alpha beta c 3 hadm hpower

/-- Cubic surplus is required only for the first `n` contractions above one
physical cutoff. -/
def PrimeSieveStateDependentSelbergFiniteCubicGainChain
    (M : Nat) (c : Real) (a : Nat -> Real) : Nat -> Prop
  | 0 => True
  | n + 1 =>
      PrimeSieveStateDependentSelbergFiniteCubicGainChain M c a n ∧
        PrimeSieveStateDependentSelbergCubicGainAbove M (a n) c

/-- A finite chain of endpoint-wise cubic gains preserves the same physical
tail cutoff through exactly the requested contraction depth. -/
theorem primeSieveStateDependentSelberg_finite_cubic_chain_persists
    (M : Nat) (c : Real) (a : Nat -> Real)
    (hpos : forall n : Nat, 0 < a n)
    (hrec : forall n : Nat,
      a (n + 1) = a n - c * (a n) ^ 3)
    (htail0 : PrimeSieveStateDependentSelbergTailAbove M (a 0))
    (n : Nat)
    (hgain : PrimeSieveStateDependentSelbergFiniteCubicGainChain M c a n) :
    PrimeSieveStateDependentSelbergTailAbove M (a n) := by
  revert hgain
  induction n with
  | zero =>
      intro _hgain
      exact htail0
  | succ n ih =>
      intro hgain
      change
        PrimeSieveStateDependentSelbergFiniteCubicGainChain M c a n ∧
          PrimeSieveStateDependentSelbergCubicGainAbove M (a n) c at hgain
      rcases hgain with ⟨hprev, hstepGain⟩
      have htailn := ih hprev
      have hnext : 0 < a n - c * (a n) ^ 3 := by
        simpa [hrec n] using hpos (n + 1)
      have hstep := primeSieveStateDependentSelberg_cubicGainAbove_step
        M (a n) c htailn hstepGain hnext
      rw [hrec n]
      exact hstep

theorem primeSieveStateDependentSelberg_tail_le_eta_of_cubic_budget
    (M : Nat) (c eta : Real) (a : Nat -> Real)
    (hc : 0 <= c) (heta : 0 < eta)
    (hpos : forall n : Nat, 0 < a n)
    (hrec : forall n : Nat,
      a (n + 1) = a n - c * (a n) ^ 3)
    (htail0 : PrimeSieveStateDependentSelbergTailAbove M (a 0))
    (n : Nat)
    (hgain : PrimeSieveStateDependentSelbergFiniteCubicGainChain M c a n)
    (hbudget : 1 < 2 * c * (n : Real) * eta ^ 2) :
    forall N : Nat, M <= N ->
      |nativePNTError N| <= eta * (N : Real) := by
  have hrec_le : forall j : Nat,
      a (j + 1) <= a j - c * (a j) ^ 3 := by
    intro j
    rw [hrec j]
  have haeta : a n <= eta :=
    cubic_contraction_inequality_le_eta_of_budget
      a c eta hc heta hpos hrec_le n hbudget
  have htailn :=
    primeSieveStateDependentSelberg_finite_cubic_chain_persists
      M c a hpos hrec htail0 n hgain
  intro N hMN
  have hbound := htailn.2.2 N hMN
  have hN0 : 0 <= (N : Real) := by positivity
  exact hbound.trans (mul_le_mul_of_nonneg_right haeta hN0)

/-- A target slope is available on a tail whose physical cutoff grows at most
quadratically in the reciprocal target slope. -/
def NativePNTQuadraticTailScaleLaw (K : Real) : Prop :=
  0 < K ∧ forall eta : Real, 0 < eta ->
    ∃ M : Nat,
      (M : Real) * eta ^ 2 <= K ∧
      (forall N : Nat, M <= N ->
        |nativePNTError N| <= eta * (N : Real))

/-- The arithmetic package that exactly matches the existing cubic iteration
budget while keeping one physical cutoff fixed only through the finite chain
needed for the requested target slope. -/
def PrimeSieveStateDependentSelbergQuadraticScaleCubicLaw
    (K c : Real) : Prop :=
  0 < K ∧ 0 <= c ∧
    forall eta : Real, 0 < eta ->
      ∃ M : Nat, ∃ a : Nat -> Real, ∃ n : Nat,
        (M : Real) * eta ^ 2 <= K ∧
        (forall j : Nat, 0 < a j) ∧
        (forall j : Nat,
          a (j + 1) = a j - c * (a j) ^ 3) ∧
        PrimeSieveStateDependentSelbergTailAbove M (a 0) ∧
        PrimeSieveStateDependentSelbergFiniteCubicGainChain M c a n ∧
        1 < 2 * c * (n : Real) * eta ^ 2

theorem nativePNTQuadraticTailScaleLaw_of_stateDependentCubicGain
    (K c : Real)
    (hlaw : PrimeSieveStateDependentSelbergQuadraticScaleCubicLaw K c) :
    NativePNTQuadraticTailScaleLaw K := by
  rcases hlaw with ⟨hK, hc, hlaw⟩
  refine ⟨hK, ?_⟩
  intro eta heta
  rcases hlaw eta heta with
    ⟨M, a, n, hscale, hpos, hrec, htail0, hgain, hbudget⟩
  refine ⟨M, hscale, ?_⟩
  exact primeSieveStateDependentSelberg_tail_le_eta_of_cubic_budget
    M c eta a hc heta hpos hrec htail0 n hgain hbudget

/-- **Bound-changing theorem for the no-intercept route.**  Quadratic cutoff
growth in the target slope implies a square-root Chebyshev error. -/
theorem nativePNTError_abs_le_sqrt_of_quadraticTailScaleLaw
    (K : Real) (hlaw : NativePNTQuadraticTailScaleLaw K)
    (N : Nat) (hN : 1 <= N) :
    |nativePNTError N| <= Real.sqrt (K * (N : Real)) := by
  rcases hlaw with ⟨hK, hlaw⟩
  have hNR : 0 < (N : Real) := by
    exact_mod_cast (show 0 < N by omega)
  let eta : Real := Real.sqrt (K / (N : Real))
  have hratio : 0 < K / (N : Real) := div_pos hK hNR
  have heta : 0 < eta := by
    dsimp [eta]
    exact Real.sqrt_pos.2 hratio
  have heta_sq : eta ^ 2 = K / (N : Real) := by
    dsimp [eta]
    exact Real.sq_sqrt hratio.le
  rcases hlaw eta heta with ⟨M, hscale, htail⟩
  have hetaN : eta ^ 2 * (N : Real) = K := by
    rw [heta_sq]
    field_simp [ne_of_gt hNR]
  have hmul := mul_le_mul_of_nonneg_right hscale hNR.le
  have hKM : K * (M : Real) <= K * (N : Real) := by
    calc
      K * (M : Real) = ((M : Real) * eta ^ 2) * (N : Real) := by
        rw [mul_assoc, hetaN]
        ring
      _ <= K * (N : Real) := hmul
  have hMNreal : (M : Real) <= (N : Real) :=
    (mul_le_mul_iff_left₀ hK).mp hKM
  have hMN : M <= N := by exact_mod_cast hMNreal
  have hbound := htail N hMN
  have hscaled_nonneg : 0 <= eta * (N : Real) :=
    mul_nonneg heta.le hNR.le
  have hscaled_sq :
      (eta * (N : Real)) ^ 2 = K * (N : Real) := by
    calc
      (eta * (N : Real)) ^ 2 = eta ^ 2 * (N : Real) ^ 2 := by ring
      _ = (K / (N : Real)) * (N : Real) ^ 2 := by rw [heta_sq]
      _ = K * (N : Real) := by field_simp [ne_of_gt hNR]
  have hscaled_sqrt :
      eta * (N : Real) = Real.sqrt (K * (N : Real)) := by
    calc
      eta * (N : Real) = Real.sqrt ((eta * (N : Real)) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hscaled_nonneg]
      _ = Real.sqrt (K * (N : Real)) := by rw [hscaled_sq]
  rw [← hscaled_sqrt]
  exact hbound

theorem nativePNTError_abs_le_sqrt_of_stateDependentCubicGain
    (K c : Real)
    (hlaw : PrimeSieveStateDependentSelbergQuadraticScaleCubicLaw K c)
    (N : Nat) (hN : 1 <= N) :
    |nativePNTError N| <= Real.sqrt (K * (N : Real)) := by
  exact nativePNTError_abs_le_sqrt_of_quadraticTailScaleLaw K
    (nativePNTQuadraticTailScaleLaw_of_stateDependentCubicGain K c hlaw)
    N hN

end RHLean.Analysis

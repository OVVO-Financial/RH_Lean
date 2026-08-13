import Mathlib
import RHLean.Analysis.PrimeSieveStateDependentSelbergScalePersistence

noncomputable section

namespace RHLean.Analysis

/-- A target slope `eta` is available on a tail whose physical cutoff grows at
most quadratically in `eta^(-1)`. -/
def NativePNTQuadraticTailScaleLaw (K : Real) : Prop :=
  0 < K ∧ forall eta : Real, 0 < eta ->
    ∃ M : Nat,
      (M : Real) * eta ^ 2 <= K ∧
      (forall N : Nat, M <= N ->
        |nativePNTError N| <= eta * (N : Real))

/-- The arithmetic package needed to obtain the quadratic tail-scale law from
state-dependent cubic surplus while keeping one cutoff fixed through the
whole scalar contraction chain. -/
def PrimeSieveStateDependentSelbergQuadraticScaleCubicLaw
    (K c : Real) : Prop :=
  0 < K ∧ 0 <= c ∧
    forall eta : Real, 0 < eta ->
      ∃ M : Nat, ∃ a : Nat -> Real, ∃ n : Nat,
        (M : Real) * eta ^ 2 <= K ∧
        (forall j : Nat, 0 < a j) ∧
        (forall j : Nat,
          a (j + 1) = a j - c * (a j) ^ 3) ∧
        PrimeSieveStateDependentSelbergCubicGainChainAt M c a ∧
        PrimeSieveStateDependentSelbergTailAbove M (a 0) ∧
        1 < 2 * c * (n : Real) * eta ^ 2

/-- Fixed-cutoff cubic surplus plus the reciprocal-square iteration budget gives
an actual quadratic physical tail-scale law. -/
theorem nativePNTQuadraticTailScaleLaw_of_stateDependentCubicGain
    (K c : Real)
    (hlaw : PrimeSieveStateDependentSelbergQuadraticScaleCubicLaw K c) :
    NativePNTQuadraticTailScaleLaw K := by
  rcases hlaw with ⟨hK, hc, hlaw⟩
  refine ⟨hK, ?_⟩
  intro eta heta
  rcases hlaw eta heta with
    ⟨M, a, n, hscale, hpos, hrec, hgain, htail0, hbudget⟩
  refine ⟨M, hscale, ?_⟩
  exact primeSieveStateDependentSelberg_tail_le_eta_of_cubic_budget
    M c eta a hc heta hpos hrec hgain htail0 n hbudget

/-- **Bound-changing theorem for the no-intercept route.**  Quadratic cutoff
growth in the target slope already implies a square-root Chebyshev error. -/
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
  simpa [hscaled_sqrt] using hbound

/-- Therefore the state-dependent cubic package itself implies the same
square-root PNT bound once its physical cutoff is quadratic in the target
slope. -/
theorem nativePNTError_abs_le_sqrt_of_stateDependentCubicGain
    (K c : Real)
    (hlaw : PrimeSieveStateDependentSelbergQuadraticScaleCubicLaw K c)
    (N : Nat) (hN : 1 <= N) :
    |nativePNTError N| <= Real.sqrt (K * (N : Real)) := by
  exact nativePNTError_abs_le_sqrt_of_quadraticTailScaleLaw K
    (nativePNTQuadraticTailScaleLaw_of_stateDependentCubicGain K c hlaw)
    N hN

end RHLean.Analysis

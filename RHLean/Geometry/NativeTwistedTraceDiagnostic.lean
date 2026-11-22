import RHLean.Geometry.NativeFiniteIntegralDescent

/-!
# An integral two-point twisted-trace diagnostic

On the cyclic group `Fin 2`, translate the genuine integral function `(3,2)`.
Each map is its translated multiplication followed by the UNNORMALIZED
trivial-character trace. The source energy is normalized counting measure;
each invariant target is the constant scalar with its ordinary squared norm.
This is a finite function-algebra example, not a theta-section instance.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Geometry

def nativeTwoTraceSection (i : Fin 2) : ℤ := ![3, 2] i
def nativeTwoTraceMatrix : Matrix (Fin 2) (Fin 2) ℤ :=
  fun h i => nativeTwoTraceSection (i + h)
def nativeTwoTrace (f : Fin 2 → ℝ) (h : Fin 2) : ℝ :=
  ∑ i : Fin 2, (nativeTwoTraceMatrix h i : ℝ) * f i
def nativeTwoTraceSourceEnergy (f : Fin 2 → ℝ) : ℝ :=
  (∑ i : Fin 2, (f i) ^ 2) / 2
def nativeTwoTraceJointEnergy (f : Fin 2 → ℝ) : ℝ :=
  ∑ h : Fin 2, (nativeTwoTrace f h) ^ 2

theorem nativeTwoTrace_matrix : nativeTwoTraceMatrix = !![3, 2; 2, 3] := by
  ext h i
  fin_cases h <;> fin_cases i <;>
    norm_num [nativeTwoTraceMatrix, nativeTwoTraceSection]

theorem nativeTwoTrace_integerDet : nativeTwoTraceMatrix.det = 5 := by
  rw [nativeTwoTrace_matrix]
  norm_num [Matrix.det_fin_two]

theorem nativeTwoTrace_exact_rank :
    Module.finrank ℝ (Fin 2 → ℝ) = 2 ∧
    Module.finrank ℝ (Fin 2 → ℝ) =
      Fintype.card (Fin 2) * Module.finrank ℝ ℝ := by simp

theorem nativeTwoTrace_injective : Function.Injective nativeTwoTrace := by
  intro f g hfg
  have h0 := congrFun hfg (0 : Fin 2)
  have h1 := congrFun hfg (1 : Fin 2)
  simp [nativeTwoTrace, nativeTwoTrace_matrix, Fin.sum_univ_succ] at h0 h1
  funext i
  fin_cases i
  · change f 0 = g 0
    linarith
  · change f 1 = g 1
    linarith

/-- Squared multiplication norm at most `3^2`, in the stated source metric. -/
theorem nativeTwoTrace_multiplication_energy (h : Fin 2) (f : Fin 2 → ℝ) :
    nativeTwoTraceSourceEnergy
        (fun i => (nativeTwoTraceSection (i + h) : ℝ) * f i) ≤
      9 * nativeTwoTraceSourceEnergy f := by
  fin_cases h <;>
    simp [nativeTwoTraceSourceEnergy, nativeTwoTraceSection, Fin.sum_univ_succ] <;>
    nlinarith [sq_nonneg (f 0), sq_nonneg (f 1)]

theorem nativeTwoTrace_multiplication_norm (h : Fin 2) (f : Fin 2 → ℝ) :
    Real.sqrt (nativeTwoTraceSourceEnergy
      (fun i => (nativeTwoTraceSection (i + h) : ℝ) * f i)) ≤
        3 * Real.sqrt (nativeTwoTraceSourceEnergy f) := by
  calc
    _ ≤ Real.sqrt (9 * nativeTwoTraceSourceEnergy f) :=
      Real.sqrt_le_sqrt (nativeTwoTrace_multiplication_energy h f)
    _ = _ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9)]
      norm_num

theorem nativeTwoTrace_joint_identity (f : Fin 2 → ℝ) :
    nativeTwoTraceJointEnergy f =
      25 * ((f 0) ^ 2 + (f 1) ^ 2) - 12 * (f 0 - f 1) ^ 2 := by
  simp [nativeTwoTraceJointEnergy, nativeTwoTrace, nativeTwoTrace_matrix,
    Fin.sum_univ_succ]
  ring

theorem nativeTwoTrace_joint_energy_le (f : Fin 2 → ℝ) :
    nativeTwoTraceJointEnergy f ≤ 50 * nativeTwoTraceSourceEnergy f := by
  rw [nativeTwoTrace_joint_identity]
  simp [nativeTwoTraceSourceEnergy, Fin.sum_univ_succ]
  nlinarith [sq_nonneg (f 0 - f 1)]

/-- Integral injection and exact rank saturation do not give the `q^2 B^2`
joint bound: source energy is one, `q=2`, `B=3`, and joint energy is fifty. -/
theorem nativeTwoTrace_not_qSquared :
    nativeTwoTraceSourceEnergy (fun _ => 1) = 1 ∧
    nativeTwoTraceJointEnergy (fun _ => 1) = 50 ∧
    ¬ nativeTwoTraceJointEnergy (fun _ => 1) ≤
      (2 : ℝ) ^ 2 * 3 ^ 2 * nativeTwoTraceSourceEnergy (fun _ => 1) := by
  norm_num [nativeTwoTraceSourceEnergy, nativeTwoTraceJointEnergy, nativeTwoTrace,
    nativeTwoTrace_matrix, Fin.sum_univ_succ]

end RHLean.Geometry

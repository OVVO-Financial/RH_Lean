import «research.VF_MID_919_OAI_PRINCIPAL_COEFFICIENT_MAP»
import «research.VF_919_SEVEN_EIGHTHS_SQUARE_SHELL_BRIDGE_20261019»

/-!
# ORIGINAL square-block terms = full (chi_-3 * a_F) norm-fiber terms

Do NOT replace the physical sharp block or owner incidence with an OAI
theta probe. For R >= 4 write U=(R+1)^2-1, and let a_F be the original
#919 constructed inverse Dedekind-zeta coefficient:
  a_F = mu_Z * (chi_-3 * mu_Z).

The ACTUAL coefficient of every integer n in the block is
  mu_Z(n) = sum_{d*m=n} chi_-3(d) a_F(m).

The entire square block is then ONE double sum with the ORIGINAL
physical site indicator at the actual product d*m:
  S_R = sum_{1<=m<=U} a_F(m) *
          sum_{1<=d<=U} chi_-3(d) [R^2 <= d*m < (R+1)^2].

This is the precise sharp source into which OpenAI's *genuine* ideal
norm-fiber coefficient normFiberCoeff (baseChangeWeight (1)) must be
substituted. The upstream theorem in
  openai/math/lean/OAI/.../Hecke/LocalEulerIdentities.lean:
  ShortDraftHeckeBridge.normFiberCoeff_baseChange_eq_pairInverseCoeff
proves that true ideal-fiber coefficient on OAI's Lean 4.34.1 toolchain.

THIS MODULE uses the actual RH_Lean arithmetic coefficient and proves
all sharp physical weights, without assuming any ideal-phase source
identity or a character moment bound. A separate 4.34.1 crosswalk can
then specialize the already-proved OAI ideal coefficient theorem.

Only R>=4 is needed here to guarantee the positive finite sharp
cutoff; the first four shells remain literal in the global Gram.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- Exactly the original physical integer site mask on the HALF-OPEN
    square block. Used at d*m, never at a modified ideal norm alone. -/
def vf919OAITrueSquareBlockMask (R n : ℕ) : ℂ :=
  if R ^ 2 ≤ n ∧ n < (R + 1) ^ 2 then 1 else 0

/-- ONE actual quadratic Hecke norm fiber term, with all 1,2,3 and higher
    rational-prime contributions; no excluded-factor approximation. -/
def vf919OAITrueSquareIdealNormTerm (R U m : ℕ) : ℂ :=
  vf919EisensteinNormCoefficients m *
    ∑ d ∈ Finset.Icc 1 U,
      vf919ChiMinusThree d * vf919OAITrueSquareBlockMask R (m * d)

/-- All physical numbers in the exact square shell, reconstructed with
    the complete quadratic ideal-norm coefficients. -/
def vf919OAITrueSquareIdealNormSource (R : ℕ) : ℂ :=
  let U := (R + 1) ^ 2 - 1
  ∑ m ∈ Finset.Icc 1 U, vf919OAITrueSquareIdealNormTerm R U m

/-- Original square block mask vanishes strictly after U=(R+1)^2-1. -/
theorem vf919OAITrueSquareBlockMask_outside (R U n : ℕ)
    (hU : U + 1 = (R + 1) ^ 2)
    (hn : U < n) : vf919OAITrueSquareBlockMask R n = 0 := by
  unfold vf919OAITrueSquareBlockMask
  have h : ¬ n < (R + 1) ^ 2 := by omega
  simp [h]

/-- The true coefficient at EACH integer is the complete Hecke norm
    divisor convolution; all split/inert/ramified terms survive. -/
theorem vf919OAITrueSquareMu_at_integer (n : ℕ) :
    vf919RationalMobius n =
      ∑ t ∈ Nat.divisorsAntidiagonal n,
        vf919EisensteinNormCoefficients t.1 *
          vf919ChiMinusThree t.2 := by
  rw [← vf919QuadraticCharacter_mul_norm_eq_mobius]
  rw [mul_comm, ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro t _
  rw [vf919QuadraticCharacter_apply]

/-- The exact FULL square shell, before any analytic moment estimate,
    equals the one-source norm-fiber convolution, each n / m / d intact. -/
theorem vf919OAITrueSquareIdealNormSource_eq_originalShell
    (R : ℕ) (hR : 4 ≤ R) :
    vf919OAITrueSquareIdealNormSource R =
      (vf919SquareShellSum R : ℂ) := by
  let U : ℕ := (R + 1) ^ 2 - 1
  have hU : U + 1 = (R + 1) ^ 2 := by
    dsimp [U]
    have hb : 0 < (R + 1) ^ 2 := by nlinarith
    omega
  have hRone : 1 ≤ R ^ 2 := by nlinarith
  have hle : R ^ 2 ≤ (R + 1) ^ 2 := by nlinarith
  have hmem :
      (Finset.Icc 1 U).filter
        (fun n : ℕ => R ^ 2 ≤ n ∧ n < (R + 1) ^ 2) =
      Finset.Ico (R ^ 2) ((R + 1) ^ 2) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hphysical :
      (∑ n ∈ Finset.Icc 1 U,
        vf919RationalMobius n * vf919OAITrueSquareBlockMask R n) =
      ∑ n ∈ Finset.Ico (R ^ 2) ((R + 1) ^ 2),
        vf919RationalMobius n := by
    unfold vf919OAITrueSquareBlockMask
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    rw [hmem]
  have hsum :
      (∑ n ∈ Finset.Ico (R ^ 2) ((R + 1) ^ 2),
        realMoebiusStep n) = vf919SquareShellSum R := by
    calc
      (∑ n ∈ Finset.Ico (R ^ 2) ((R + 1) ^ 2),
        realMoebiusStep n) =
        (∑ n ∈ Finset.range ((R + 1) ^ 2), realMoebiusStep n) -
          (∑ n ∈ Finset.range (R ^ 2), realMoebiusStep n) :=
            Finset.sum_Ico_eq_sub _ hle
      _ = vf919SquareShellSum R := rfl
  have hsource :
      (∑ n ∈ Finset.Icc 1 U,
        vf919RationalMobius n * vf919OAITrueSquareBlockMask R n) =
      ∑ m ∈ Finset.Icc 1 U,
        vf919EisensteinNormCoefficients m *
          ∑ d ∈ Finset.Icc 1 U,
            vf919ChiMinusThree d *
              vf919OAITrueSquareBlockMask R (m * d) := by
    have hcoef :
        vf919EisensteinNormCoefficients * vf919QuadraticCharacter =
          vf919RationalMobius := by
      rw [mul_comm, vf919QuadraticCharacter_mul_norm_eq_mobius]
    rw [← hcoef]
    have hfubini := vf919DirichletWeightedPairing
      U vf919EisensteinNormCoefficients vf919QuadraticCharacter
      (vf919OAITrueSquareBlockMask R)
      (fun n hn => vf919OAITrueSquareBlockMask_outside R U n hU hn)
    rw [hfubini]
    apply Finset.sum_congr rfl
    intro m _
    congr 1
    apply Finset.sum_congr rfl
    intro d _
    rw [vf919QuadraticCharacter_apply]
  unfold vf919OAITrueSquareIdealNormSource
    vf919OAITrueSquareIdealNormTerm
  dsimp only
  rw [← hsource, hphysical]
  have hs := congrArg (fun x : ℝ => (x : ℂ)) hsum
  push_cast at hs
  calc
    (∑ n ∈ Finset.Ico (R ^ 2) ((R + 1) ^ 2),
        vf919RationalMobius n) =
      (∑ n ∈ Finset.Ico (R ^ 2) ((R + 1) ^ 2),
        (realMoebiusStep n : ℂ)) := by
          apply Finset.sum_congr rfl
          intro n _
          unfold vf919RationalMobius realMoebiusStep
          push_cast
          rfl
    _ = (vf919SquareShellSum R : ℂ) := hs

/-- In the original NNS Green--Kubo coordinates, the norm-fiber source
    cancels EXACTLY through the whole square-block signed covariance. -/
theorem vf919OAITrueSquareIdealNormSource_full_signed_covariance
    (R : ℕ) (hR : 4 ≤ R) :
    (vf919OAITrueSquareIdealNormSource R) ^ 2 =
      (vf919SquareShellDiagonal R : ℂ) +
        2 * (vf919SquareShellCovariance R : ℂ) := by
  rw [vf919OAITrueSquareIdealNormSource_eq_originalShell R hR]
  have h := vf919SquareShell_signedGreenKubo R
  exact (congrArg (fun x : ℝ => (x : ℂ)) h)

#print axioms vf919OAITrueSquareMu_at_integer
#print axioms vf919OAITrueSquareIdealNormSource_eq_originalShell
#print axioms vf919OAITrueSquareIdealNormSource_full_signed_covariance

end RHLean.Analysis

import «research.VF_919_OAI_TRUE_IDEAL_NORM_SHARP_SQUARE_BLOCK_20261019»

/-!
# The exact ORIGINAL physical square-block cutoff at EACH ideal norm

For R>=4 and 1<=m<=U=(R+1)^2-1 the actual cofactor sum is
    sum_d chi_-3(d) [R^2 <= d*m < (R+1)^2]
       = C_chi(floor(U/m)) - C_chi(floor(L/m)),
    L=R^2-1; C_chi(N)=sum_{d=1}^N chi_-3(d).

There is no 3/4/12 truncation at this stage: a_F(m) is the FULL
true ideal-norm coefficient, including inert norm p^2, ramified p=3,
and BOTH split prime-ideal factors when p=1 mod 3. Only after the
true ideal-fiber theorem may it be expanded as actual mu_F(ideal).

This is a term-by-term exact sharp carrier, with no smoothing,
heuristic density, or analytic power-saving assumption. It supplies
the arithmetic right-hand input to the original OAI theta/Mellin
source transport.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

def vf919OAITrueSquareU (R : ℕ) : ℕ := (R + 1)^2 - 1
def vf919OAITrueSquareL (R : ℕ) : ℕ := R^2 - 1

/-- Exact sharp half-open square indicator = upper sharp prefix
    indicator MINUS lower sharp prefix indicator. Each endpoint counts
    the original physical integer and not a shifted ideal norm. -/
theorem vf919OAITrueSquareBlockMask_eq_two_exact_prefixes
    (R : ℕ) (hR : 4 ≤ R) (n : ℕ) :
    vf919OAITrueSquareBlockMask R n =
      vf919SharpPhysicalWeight (vf919OAITrueSquareU R) n -
        vf919SharpPhysicalWeight (vf919OAITrueSquareL R) n := by
  have hU : vf919OAITrueSquareU R + 1 = (R+1)^2 := by
    unfold vf919OAITrueSquareU
    have h : 0 < (R+1)^2 := by nlinarith
    omega
  have hL : vf919OAITrueSquareL R + 1 = R^2 := by
    unfold vf919OAITrueSquareL
    have h : 0 < R^2 := by nlinarith
    omega
  by_cases hnlow : n < R^2
  · have hlow : ¬ R^2 ≤ n := by omega
    have hhi : n ≤ vf919OAITrueSquareU R := by omega
    have hlo : n ≤ vf919OAITrueSquareL R := by omega
    simp [vf919OAITrueSquareBlockMask, vf919SharpPhysicalWeight,
      hlow, hhi, hlo]
  · by_cases hnhi : n < (R+1)^2
    · have hlow : R^2 ≤ n := by omega
      have hhi : n ≤ vf919OAITrueSquareU R := by omega
      have hlo : ¬ n ≤ vf919OAITrueSquareL R := by omega
      simp [vf919OAITrueSquareBlockMask, vf919SharpPhysicalWeight,
        hlow, hnhi, hhi, hlo]
    · have hhi : ¬ n ≤ vf919OAITrueSquareU R := by omega
      have hlo : ¬ n ≤ vf919OAITrueSquareL R := by omega
      simp [vf919OAITrueSquareBlockMask, vf919SharpPhysicalWeight,
        hnhi, hhi, hlo]

/-- Original norm-cofactor character is exactly the period-three
    summatory character at floor(X/m), not a constant density. -/
private theorem vf919OAITrueCharacterSum_sharp_dilation
    (U X m : ℕ) (hX : X ≤ U) (hm : 0 < m) :
    (∑ d ∈ Finset.Icc 1 U,
        if m * d ≤ X then vf919ChiMinusThree d else 0) =
      (vf919IntegerCharacterPrefix (X / m) : ℂ) := by
  have hdiv : X / m ≤ U := (Nat.div_le_self X m).trans hX
  have hfilter :
      (Finset.Icc 1 U).filter (fun d => m * d ≤ X) =
        Finset.Icc 1 (X / m) := by
    ext d
    have hiff : m * d ≤ X ↔ d ≤ X / m := by
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm).symm
    simp only [Finset.mem_filter, Finset.mem_Icc, hiff]
    omega
  rw [← Finset.sum_filter, hfilter]
  simp only [vf919IntegerCharacterPrefix, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro d _
  unfold vf919IntegerCharacter vf919ChiMinusThree
  split_ifs <;> norm_num

private theorem vf919OAITrueCharacterSum_weightedSharp
    (U X m : ℕ) (hX : X ≤ U) (hm : 0 < m) :
    (∑ d ∈ Finset.Icc 1 U, vf919ChiMinusThree d *
      vf919SharpPhysicalWeight X (m * d)) =
      (vf919IntegerCharacterPrefix (X / m) : ℂ) := by
  unfold vf919SharpPhysicalWeight
  simp only [mul_ite, mul_one, mul_zero]
  exact vf919OAITrueCharacterSum_sharp_dilation U X m hX hm

/-- THE COFACTOR-BY-COFACTOR FLOOR IDENTITY at each original m.
    ALL integer admittances d*m are tested at their literal square
    boundary, and all character signs are preserved. -/
theorem vf919OAITrueSquareBlockCharacterWeight_eq_floorDifference
    (R m : ℕ) (hR : 4 ≤ R) (hm : 0 < m) :
    (∑ d ∈ Finset.Icc 1 (vf919OAITrueSquareU R),
        vf919ChiMinusThree d *
          vf919OAITrueSquareBlockMask R (m * d)) =
      ((vf919IntegerCharacterPrefix
          (vf919OAITrueSquareU R / m) : ℤ) : ℂ) -
      ((vf919IntegerCharacterPrefix
          (vf919OAITrueSquareL R / m) : ℤ) : ℂ) := by
  have hX : vf919OAITrueSquareL R ≤ vf919OAITrueSquareU R := by
    unfold vf919OAITrueSquareL vf919OAITrueSquareU
    have hsquare : R ^ 2 ≤ (R + 1) ^ 2 := by nlinarith
    omega
  simp_rw [vf919OAITrueSquareBlockMask_eq_two_exact_prefixes R hR]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  rw [vf919OAITrueCharacterSum_weightedSharp
    (vf919OAITrueSquareU R) (vf919OAITrueSquareU R) m le_rfl hm,
    vf919OAITrueCharacterSum_weightedSharp
      (vf919OAITrueSquareU R) (vf919OAITrueSquareL R) m hX hm]

/-- The ORIGINAL square-block contribution of EACH actual ideal norm,
    with no prior exclusion of inert, split, or ramified primes. -/
theorem vf919OAITrueSquareIdealNormTerm_eq_exact_floorDifference
    (R m : ℕ) (hR : 4 ≤ R) (hm : 0 < m) :
    vf919OAITrueSquareIdealNormTerm R
        (vf919OAITrueSquareU R) m =
      vf919EisensteinNormCoefficients m *
        ((vf919IntegerCharacterPrefix
          (vf919OAITrueSquareU R / m) : ℂ) -
        (vf919IntegerCharacterPrefix
          (vf919OAITrueSquareL R / m) : ℂ)) := by
  unfold vf919OAITrueSquareIdealNormTerm
  rw [vf919OAITrueSquareBlockCharacterWeight_eq_floorDifference
    R m hR hm]

/-- ALL sharp original square-block norm terms at once, without
    a hypothesis on the distribution of ideal phases or primes. -/
theorem vf919OAI_true_square_block_eq_sum_exact_ideal_norm_floors
    (R : ℕ) (hR : 4 ≤ R) :
    (vf919SquareShellSum R : ℂ) =
      ∑ m ∈ Finset.Icc 1 (vf919OAITrueSquareU R),
        vf919EisensteinNormCoefficients m *
          ((vf919IntegerCharacterPrefix
              (vf919OAITrueSquareU R / m) : ℂ) -
           (vf919IntegerCharacterPrefix
              (vf919OAITrueSquareL R / m) : ℂ)) := by
  rw [← vf919OAITrueSquareIdealNormSource_eq_originalShell R hR]
  unfold vf919OAITrueSquareIdealNormSource vf919OAITrueSquareU
  apply Finset.sum_congr rfl
  intro m hm
  exact vf919OAITrueSquareIdealNormTerm_eq_exact_floorDifference
    R m hR (by have := (Finset.mem_Icc.mp hm).1; omega)

#print axioms vf919OAITrueSquareBlockMask_eq_two_exact_prefixes
#print axioms vf919OAITrueSquareBlockCharacterWeight_eq_floorDifference
#print axioms vf919OAITrueSquareIdealNormTerm_eq_exact_floorDifference
#print axioms vf919OAI_true_square_block_eq_sum_exact_ideal_norm_floors

end RHLean.Analysis

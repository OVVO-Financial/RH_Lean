import RHLean.Analysis.SquareRootMatchedDegreeOneRecovery
import RHLean.Proof.SquareRootAmplificationClosure
import RHLean.Proof.SquareRootLowPrimeSharpFrameBudget

/-!
# Signed transport and square-endpoint amplification audit

The square-root amplification target is the fully recovered shifted state
`matched - H - 1`, not the matched channel alone.  The first theorem supplies
the exact normalization needed to use the existing amplification closure.

There is also a finite obstruction to requesting a subunit amplification
constant in the repository's all-`R >= 2` formulation: at `R = 2`, the lower
critical envelope `K = 1` is admissible and the endpoint numerator is four.
Consequently every uniform constant in that formulation is at least one.

After the signed post-#674 q^2 reassembly, the relevant terminal induction only
needs a square-endpoint recurrence.  For each odd prime owner `q`, recurse from
`X_R = R^2 - 1` to the lower square root of `floor(X_R / q^2)`.  The sharp odd
owner budget `17/72` then makes a factor-four recurrence subcritical with
coefficient `17/18`.  This is a conditional terminal theorem: it does not prove
the remaining signed survivor estimate.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The exact amplification numerator retains both the ancestral correction
`-H` and the exceptional unit-source shift `-1` before the norm is taken. -/
theorem recoveredMatchedShiftedEnergy_eq_amplificationNumerator
    (R : ℕ) (hR : 2 ≤ R) :
    ‖squareRootMatchedBornSmoothTransport R -
        squareRootPositiveSmoothPrimeMertensTransform R - 1‖ ^ 2 =
      (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ) ^ 2) := by
  rw [squareRootMatched_sub_positivePrimeTransform_eq_squarePrefixMertens
    R (by omega)]
  unfold squarePrefixMertens
  rw [squarePrefixEndpoint_pred_eq_squareRootEndpoint R (by omega)]
  exact shiftedMertensEnergy_eq_intSquare (squareRootEndpoint R)

/-- The lower-scale data at the first nontrivial root admit the unit envelope. -/
theorem lowerMertensCriticalEnvelope_two_one :
    LowerMertensCriticalEnvelope 2 1 := by
  refine ⟨by norm_num, ?_⟩
  intro y hy
  have hyCases : y = 0 ∨ y = 1 := by omega
  rcases hyCases with rfl | rfl
  · norm_num [mertensSummatoryInt]
  · have hM : mertensSummatoryInt 1 = 1 := by native_decide
    rw [hM]
    norm_num

/-- An amplification constant below one cannot satisfy the exact all-root
statement: its first square endpoint already forces `1 <= A`. -/
theorem squareRootEndpointAmplification_constant_ge_one
    {A : ℝ}
    (hbound : ∀ R : ℕ, ∀ K : ℝ,
      2 ≤ R → LowerMertensCriticalEnvelope R K →
        (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ) ^ 2) ≤
          A * (R : ℝ) ^ 2 * K) :
    1 ≤ A := by
  have h := hbound 2 1 (by norm_num) lowerMertensCriticalEnvelope_two_one
  have hM : mertensSummatoryInt (squareRootEndpoint 2) = -1 := by
    native_decide
  rw [hM] at h
  norm_num at h
  linarith

/-! ## Square-endpoint q² amplification closure -/

/-- Lower square root attached to the literal `q^2` daughter cutoff. -/
def roundedQ2ChildRoot (R q : ℕ) : ℕ :=
  Nat.sqrt (squareRootEndpoint R / (q * q))

/-- Unshifted Mertens energy at a physical square endpoint. -/
def squareEndpointMertensEnergyReal (R : ℕ) : ℝ :=
  ((mertensSummatoryInt (squareRootEndpoint R) : ℤ) : ℝ) ^ 2

/-- The square-endpoint factor-four recurrence in the form consumed by the
fixed-amplification induction.  The additive term scales with the same lower
critical envelope `K`, so this is the RH-scale formulation rather than a
uniform strong-Mertens statement. -/
def SquareEndpointRoundedOddQ2EnergyStep (C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    2 ≤ R →
    LowerMertensCriticalEnvelope R K →
    squareEndpointMertensEnergyReal R ≤
      C * (R : ℝ) ^ 2 * K +
        4 * ∑ q ∈ (primesUpTo (R - 1)).erase 2,
          squareEndpointMertensEnergyReal (roundedQ2ChildRoot R q)

private theorem squareEndpointMertensEnergyReal_eq_zero_of_lt_two
    {R : ℕ} (hR : R < 2) :
    squareEndpointMertensEnergyReal R = 0 := by
  interval_cases R <;>
    simp [squareEndpointMertensEnergyReal, squareRootEndpoint,
      mertensSummatoryInt]

private theorem roundedQ2ChildRoot_lt_parent
    {R q : ℕ} (hR : 1 ≤ R) :
    roundedQ2ChildRoot R q < R := by
  unfold roundedQ2ChildRoot
  apply (Nat.sqrt_lt').2
  have hle : squareRootEndpoint R / (q * q) ≤ squareRootEndpoint R :=
    Nat.div_le_self _ _
  have hend : squareRootEndpoint R < R ^ 2 := by
    unfold squareRootEndpoint
    omega
  exact hle.trans_lt hend

private theorem lowerEnvelope_mono_root
    {R S : ℕ} {K : ℝ}
    (hSR : S < R)
    (hK : LowerMertensCriticalEnvelope R K) :
    LowerMertensCriticalEnvelope S K := by
  refine ⟨hK.1, ?_⟩
  intro y hy
  exact hK.2 y (hy.trans hSR)

/-- The rounded child roots consume no more scale than the literal q² daughter
cutoffs, hence inherit the exact `17/72` odd-owner budget. -/
theorem sum_roundedQ2ChildRoot_sq_le_seventeen_over_seventy_two
    (R : ℕ) :
    (∑ q ∈ (primesUpTo (R - 1)).erase 2,
      ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2) ≤
        (17 : ℝ) / 72 * (R : ℝ) ^ 2 := by
  let S : Finset ℕ := (primesUpTo (R - 1)).erase 2
  have hterm :
      (∑ q ∈ S, ((roundedQ2ChildRoot R q : ℕ) : ℚ) ^ 2) ≤
        ∑ q ∈ S, (((squareRootEndpoint R) / (q * q) : ℕ) : ℚ) := by
    apply Finset.sum_le_sum
    intro q hq
    have hs : (roundedQ2ChildRoot R q) ^ 2 ≤
        squareRootEndpoint R / (q * q) := by
      exact Nat.sqrt_le' _
    exact_mod_cast hs
  have hscale :=
    sum_oddPrimeOwner_squareDilatedCutoffs_le_seventeen_over_seventy_two_parent
      (R - 1) (squareRootEndpoint R)
  change (∑ q ∈ S, (((squareRootEndpoint R) / (q * q) : ℕ) : ℚ)) ≤
      (17 / 72 : ℚ) * ((squareRootEndpoint R : ℕ) : ℚ) at hscale
  have hend : ((squareRootEndpoint R : ℕ) : ℚ) ≤ (R : ℚ) ^ 2 := by
    unfold squareRootEndpoint
    push_cast
    nlinarith
  have hQ :
      (∑ q ∈ S, ((roundedQ2ChildRoot R q : ℕ) : ℚ) ^ 2) ≤
        (17 / 72 : ℚ) * (R : ℚ) ^ 2 := by
    have hcoef : (0 : ℚ) ≤ 17 / 72 := by norm_num
    exact hterm.trans (hscale.trans
      (mul_le_mul_of_nonneg_left hend hcoef))
  exact_mod_cast hQ

/-- **Square-endpoint factor four closes at fixed amplification.**

Unlike the all-complete-cell recurrence, this conclusion retains the lower
critical envelope `K`.  The recursive coefficient is exactly `17/18`, so the
explicit fixed point `A = 18*C` suffices. -/
theorem squareEndpointRoundedOddQ2EnergyStep_implies_unshifted_amplification
    {C : ℝ} (hC : 0 ≤ C)
    (hstep : SquareEndpointRoundedOddQ2EnergyStep C) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ R : ℕ, ∀ K : ℝ,
        2 ≤ R →
        LowerMertensCriticalEnvelope R K →
        squareEndpointMertensEnergyReal R ≤ A * (R : ℝ) ^ 2 * K := by
  let A : ℝ := 18 * C
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  refine ⟨A, hA, ?_⟩
  intro R
  induction R using Nat.strong_induction_on with
  | h R ih =>
      intro K hR hK
      let S : Finset ℕ := (primesUpTo (R - 1)).erase 2
      have hK0 : 0 ≤ K := hK.1
      have hchild : ∀ q ∈ S,
          squareEndpointMertensEnergyReal (roundedQ2ChildRoot R q) ≤
            A * ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2 * K := by
        intro q hq
        have hsR : roundedQ2ChildRoot R q < R :=
          roundedQ2ChildRoot_lt_parent (by omega)
        by_cases hs2 : 2 ≤ roundedQ2ChildRoot R q
        · exact ih (roundedQ2ChildRoot R q) hsR K hs2
            (lowerEnvelope_mono_root hsR hK)
        · have hslt : roundedQ2ChildRoot R q < 2 := by omega
          rw [squareEndpointMertensEnergyReal_eq_zero_of_lt_two hslt]
          positivity
      have hchildren :
          (∑ q ∈ S,
            squareEndpointMertensEnergyReal (roundedQ2ChildRoot R q)) ≤
            A * K *
              ∑ q ∈ S, ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2 := by
        calc
          (∑ q ∈ S,
              squareEndpointMertensEnergyReal (roundedQ2ChildRoot R q)) ≤
            ∑ q ∈ S,
              A * ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2 * K := by
                apply Finset.sum_le_sum
                intro q hq
                exact hchild q hq
          _ = A * K *
              ∑ q ∈ S, ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2 := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro q hq
                ring
      have hscale := sum_roundedQ2ChildRoot_sq_le_seventeen_over_seventy_two R
      change (∑ q ∈ S, ((roundedQ2ChildRoot R q : ℕ) : ℝ) ^ 2) ≤
        (17 : ℝ) / 72 * (R : ℝ) ^ 2 at hscale
      have hAK : 0 ≤ A * K := mul_nonneg hA hK0
      have hchildren' :
          (∑ q ∈ S,
            squareEndpointMertensEnergyReal (roundedQ2ChildRoot R q)) ≤
            A * K * ((17 : ℝ) / 72 * (R : ℝ) ^ 2) :=
        hchildren.trans (mul_le_mul_of_nonneg_left hscale hAK)
      have hs := hstep R K hR hK
      change squareEndpointMertensEnergyReal R ≤
        C * (R : ℝ) ^ 2 * K +
          4 * ∑ q ∈ S,
            squareEndpointMertensEnergyReal (roundedQ2ChildRoot R q) at hs
      have hweighted := mul_le_mul_of_nonneg_left hchildren'
        (by norm_num : (0 : ℝ) ≤ 4)
      have hfixed : C + (17 : ℝ) / 18 * A = A := by
        dsimp [A]
        ring
      calc
        squareEndpointMertensEnergyReal R ≤
            C * (R : ℝ) ^ 2 * K +
              4 * ∑ q ∈ S,
                squareEndpointMertensEnergyReal (roundedQ2ChildRoot R q) := hs
        _ ≤ C * (R : ℝ) ^ 2 * K +
              4 * (A * K * ((17 : ℝ) / 72 * (R : ℝ) ^ 2)) :=
                add_le_add_left hweighted _
        _ = (C + (17 : ℝ) / 18 * A) * ((R : ℝ) ^ 2 * K) := by ring
        _ = A * (R : ℝ) ^ 2 * K := by rw [hfixed]; ring

/-- The square-endpoint q² recurrence supplies the fixed amplification statement
already consumed by `SquareRootAmplificationClosure`.  The exceptional shift by
`1` costs only another absolute factor because every admissible lower envelope
at `R >= 2` is at least one. -/
theorem squareEndpointRoundedOddQ2EnergyStep_implies_endpointAmplification
    {C : ℝ} (hC : 0 ≤ C)
    (hstep : SquareEndpointRoundedOddQ2EnergyStep C) :
    SquareRootMertensEndpointAmplificationStatement := by
  rcases squareEndpointRoundedOddQ2EnergyStep_implies_unshifted_amplification
      hC hstep with ⟨A, hA, hbound⟩
  refine ⟨2 * A + 1, by positivity, ?_⟩
  intro R K hR hK
  have hM := hbound R K hR hK
  have hK1 : 1 ≤ K := by
    have h0 := hK.2 0 (by omega)
    have hm0 : mertensSummatoryInt 0 = 0 := by
      simp [mertensSummatoryInt]
    rw [hm0] at h0
    norm_num at h0
    exact h0
  let m : ℝ := ((mertensSummatoryInt (squareRootEndpoint R) : ℤ) : ℝ)
  have hshift : (m - 1) ^ 2 ≤ 2 * m ^ 2 + 2 := by
    nlinarith [sq_nonneg (m + 1)]
  have hscale : 2 ≤ (R : ℝ) ^ 2 * K := by
    have hRreal : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    nlinarith [mul_le_mul_of_nonneg_left hK1 (sq_nonneg (R : ℝ))]
  change (m - 1) ^ 2 ≤ (2 * A + 1) * (R : ℝ) ^ 2 * K
  calc
    (m - 1) ^ 2 ≤ 2 * m ^ 2 + 2 := hshift
    _ ≤ 2 * (A * (R : ℝ) ^ 2 * K) + 2 := by nlinarith
    _ ≤ (2 * A + 1) * (R : ℝ) ^ 2 * K := by nlinarith

end RHLean.Proof

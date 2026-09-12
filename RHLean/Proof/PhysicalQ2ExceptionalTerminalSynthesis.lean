import RHLean.Proof.PhysicalQ2TerminalSynthesis

/-!
# Exceptional-owner terminal synthesis

The maximal blocker geometry leaves only the complete least-square owners
`3,5,7`.  If the fully compensated physical parent can be reconstructed from
those three whole signed q^2 daughters plus a linear energy error, no selected-11
spectral transfer is needed for closure.

The universal three-vector inequality costs a factor `3`.  Because #665/#666
identify the whole signed daughters with the raw Mertens cutoffs

`M(4*K/9), M(4*K/25), M(4*K/49)`,

the only extra bookkeeping is the at-most-three-site transfer from each raw
cutoff to its nearest complete four-cell endpoint.  Using

`E(Y) <= (5/4) E(4*floor(Y/4)) + 45`,

the effective recursive coefficient is

`3 * (5/4) * (1/9 + 1/25 + 1/49) = 1891/2940 < 1`.

Thus the factor-three exceptional recurrence alone implies RH.  This module is
conditional only on that parent recurrence; it does not assert that the physical
parent decomposition has already been proved.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- The exact complete-cell recurrence that a signed exceptional-parent
reconstruction would provide after the universal three-daughter Cauchy step. -/
def PhysicalCompleteCellExceptionalQ2EnergyStep (C : ℚ) : Prop :=
  ∀ K : ℕ,
    mertensEnergy (4 * K) ≤ C * (K : ℚ) +
      3 * (mertensEnergy ((4 * K) / 9) +
        mertensEnergy ((4 * K) / 25) +
        mertensEnergy ((4 * K) / 49))

private theorem natCast_div_le_rat
    (X d : ℕ) (hd : 0 < d) :
    ((X / d : ℕ) : ℚ) ≤ (X : ℚ) / (d : ℚ) := by
  apply (le_div_iff₀ (by exact_mod_cast hd : (0 : ℚ) < (d : ℚ))).2
  exact_mod_cast Nat.div_mul_le_self X d

/-- The complete-cell index beneath a raw `4*K/d` child is at most the exact
rational scale `K/d`. -/
private theorem rawDaughter_completeCellIndex_le_scale
    (K d : ℕ) (hd : 0 < d) :
    (((4 * K / d) / 4 : ℕ) : ℚ) ≤ (K : ℚ) / (d : ℚ) := by
  have h4 :
      (((4 * K / d) / 4 : ℕ) : ℚ) ≤
        (((4 * K / d : ℕ) : ℚ)) / 4 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℚ) < 4)).2
    exact_mod_cast Nat.div_mul_le_self (4 * K / d) 4
  have hdv := natCast_div_le_rat (4 * K) d hd
  calc
    (((4 * K / d) / 4 : ℕ) : ℚ) ≤
        (((4 * K / d : ℕ) : ℚ)) / 4 := h4
    _ ≤ (((4 * K : ℕ) : ℚ) / (d : ℚ)) / 4 := by
      nlinarith
    _ = (K : ℚ) / (d : ℚ) := by
      push_cast
      ring

/-- Exact reciprocal-square scale for the three exceptional complete-cell child
indices, with floors retained on the left. -/
private theorem exceptional_rawDaughter_completeCellIndices_scale (K : ℕ) :
    ((((4 * K / 9) / 4 : ℕ) : ℚ) +
      (((4 * K / 25) / 4 : ℕ) : ℚ) +
      (((4 * K / 49) / 4 : ℕ) : ℚ)) ≤
        (1891 : ℚ) / 11025 * (K : ℚ) := by
  have h9 := rawDaughter_completeCellIndex_le_scale K 9 (by norm_num)
  have h25 := rawDaughter_completeCellIndex_le_scale K 25 (by norm_num)
  have h49 := rawDaughter_completeCellIndex_le_scale K 49 (by norm_num)
  calc
    ((((4 * K / 9) / 4 : ℕ) : ℚ) +
      (((4 * K / 25) / 4 : ℕ) : ℚ) +
      (((4 * K / 49) / 4 : ℕ) : ℚ)) ≤
        (K : ℚ) / 9 + (K : ℚ) / 25 + (K : ℚ) / 49 := by
          linarith
    _ = (1891 : ℚ) / 11025 * (K : ℚ) := by ring

private theorem rawDaughter_completeCellIndex_lt
    {K d : ℕ} (hK : 0 < K) (hd : 0 < d) (hd4 : 4 < d) :
    (4 * K / d) / 4 < K := by
  have hY : 4 * K / d < K := by
    apply (Nat.div_lt_iff_lt_mul hd).2
    nlinarith
  exact (Nat.div_le_self (4 * K / d) 4).trans_lt hY

/-- **Factor-three exceptional induction.**  No prime-11 contraction appears:
the restricted `3,5,7` square scales already make the universal synthesis
subcritical after the exact endpoint transfer. -/
theorem physicalCompleteCell_exceptionalFactorThreeStep_implies_linear
    {C : ℚ} (hC : 0 ≤ C)
    (hstep : PhysicalCompleteCellExceptionalQ2EnergyStep C) :
    ∀ K : ℕ,
      mertensEnergy (4 * K) ≤ (3 * (C + 405)) * (K : ℚ) := by
  let A : ℚ := 3 * (C + 405)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hfixed :
      C + 405 + (1891 : ℚ) / 2940 * A ≤ A := by
    dsimp [A]
    nlinarith
  intro K
  induction K using Nat.strong_induction_on with
  | h K ih =>
      by_cases hK0 : K = 0
      · subst K
        simp [mertensEnergy, mertensSummatoryInt]
      · have hKpos : 0 < K := Nat.pos_of_ne_zero hK0
        have child_bound (d : ℕ) (hd : 0 < d) (hd4 : 4 < d) :
            mertensEnergy (4 * K / d) ≤
              (5 : ℚ) / 4 * A * ((((4 * K / d) / 4 : ℕ) : ℚ)) + 45 := by
          let Y : ℕ := 4 * K / d
          let J : ℕ := Y / 4
          have hJlt : J < K := by
            dsimp [J, Y]
            exact rawDaughter_completeCellIndex_lt hKpos hd hd4
          have hcomplete := ih J hJlt
          have hend := mertensEnergy_le_five_fourths_completeCell_add_fortyFive Y
          change mertensEnergy Y ≤
            (5 : ℚ) / 4 * A * (J : ℚ) + 45
          calc
            mertensEnergy Y ≤
                (5 : ℚ) / 4 * mertensEnergy (4 * J) + 45 := by
                  simpa [J] using hend
            _ ≤ (5 : ℚ) / 4 * (A * (J : ℚ)) + 45 := by
                  gcongr
            _ = (5 : ℚ) / 4 * A * (J : ℚ) + 45 := by ring
        have h9 := child_bound 9 (by norm_num) (by norm_num)
        have h25 := child_bound 25 (by norm_num) (by norm_num)
        have h49 := child_bound 49 (by norm_num) (by norm_num)
        have hscale := exceptional_rawDaughter_completeCellIndices_scale K
        have hKone : (1 : ℚ) ≤ (K : ℚ) := by exact_mod_cast hKpos
        have hchildren :
            mertensEnergy (4 * K / 9) +
              mertensEnergy (4 * K / 25) +
              mertensEnergy (4 * K / 49) ≤
                (((5 : ℚ) / 4 * (1891 : ℚ) / 11025 * A) + 135) *
                  (K : ℚ) := by
          have hcoef : 0 ≤ (5 : ℚ) / 4 * A := by positivity
          calc
            mertensEnergy (4 * K / 9) +
                mertensEnergy (4 * K / 25) +
                mertensEnergy (4 * K / 49) ≤
              (5 : ℚ) / 4 * A * ((((4 * K / 9) / 4 : ℕ) : ℚ)) + 45 +
                ((5 : ℚ) / 4 * A * ((((4 * K / 25) / 4 : ℕ) : ℚ)) + 45) +
                ((5 : ℚ) / 4 * A * ((((4 * K / 49) / 4 : ℕ) : ℚ)) + 45) := by
                  linarith
            _ = (5 : ℚ) / 4 * A *
                  (((((4 * K / 9) / 4 : ℕ) : ℚ)) +
                    ((((4 * K / 25) / 4 : ℕ) : ℚ)) +
                    ((((4 * K / 49) / 4 : ℕ) : ℚ))) + 135 := by ring
            _ ≤ (5 : ℚ) / 4 * A *
                  ((1891 : ℚ) / 11025 * (K : ℚ)) + 135 := by
                    exact add_le_add_right
                      (mul_le_mul_of_nonneg_left hscale hcoef) 135
            _ ≤ (5 : ℚ) / 4 * A *
                  ((1891 : ℚ) / 11025 * (K : ℚ)) +
                    135 * (K : ℚ) := by
                      linarith
            _ = (((5 : ℚ) / 4 * (1891 : ℚ) / 11025 * A) + 135) *
                  (K : ℚ) := by ring
        have hs := hstep K
        have hweighted := mul_le_mul_of_nonneg_left hchildren (by norm_num : (0 : ℚ) ≤ 3)
        calc
          mertensEnergy (4 * K) ≤
              C * (K : ℚ) +
                3 * (mertensEnergy (4 * K / 9) +
                  mertensEnergy (4 * K / 25) +
                  mertensEnergy (4 * K / 49)) := hs
          _ ≤ C * (K : ℚ) +
                3 * ((((5 : ℚ) / 4 * (1891 : ℚ) / 11025 * A) + 135) *
                  (K : ℚ)) := add_le_add_left hweighted _
          _ = (C + 405 + (1891 : ℚ) / 2940 * A) * (K : ℚ) := by ring
          _ ≤ A * (K : ℚ) :=
                mul_le_mul_of_nonneg_right hfixed (by positivity)

/-- **Exceptional-owner single-hypothesis RH theorem.**  If the compensated
physical parent supplies the universal factor-three recurrence on its exact
three whole signed daughters, all remaining arithmetic and analytic wiring is
already closed. -/
theorem riemannHypothesis_of_physicalCompleteCell_exceptionalFactorThreeStep
    {C : ℚ} (hC : 0 ≤ C)
    (hstep : PhysicalCompleteCellExceptionalQ2EnergyStep C) :
    RiemannHypothesis := by
  let A : ℚ := 3 * (C + 405)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hlinear : ∀ K : ℕ, mertensEnergy (4 * K) ≤ A * (K : ℚ) := by
    simpa [A] using
      physicalCompleteCell_exceptionalFactorThreeStep_implies_linear hC hstep
  exact riemannHypothesis_of_threeSlotDegreeOneEnergy
    (threeSlotDegreeOneEnergy_of_completeCellMertensLinear hA hlinear)

end RHLean.Proof

import Mathlib
import RHLean.Analysis.MobiusRenewalTelescope
import RHLean.Proof.SquareRootMertensEndpointAmplification
import RHLean.Arithmetic.TopPrimeReplacementIsolation

/-!
# Recursive prime replacement at a square endpoint

This module implements the first exact nonlocal replacement step forced by
`TopPrimeReplacementIsolation`.

For a square-root cutoff `R`, truncate the Möbius divisor convolution at
`d < R`:

`C_R(n) = sum_{d | n, d < R} mu(d)`.

Because the full divisor Möbius sum vanishes away from `n = 1`, `C_R(n)` is
zero for `1 < n < R`.  Applying the repository's exact Möbius renewal telescope
at `X_R = R^2 - 1` therefore gives

`M(X_R) = M(R-1) - sum_{R <= n <= X_R} C_R(n) M(floor(X_R/n))`.

Every reciprocal argument on the right is strictly below `R`.  Thus the
unmatched population is not an independent error: it is an exact signed family
of lower-scale Mertens states.

For a top prime `q > X_R/2`, the local insertion obstruction remains, but its
replacement coefficient is now part of the complete quotient fibre
`floor(X_R/n) = 1`, together with composite `n`.  This is the intended wholesale,
nonlocal arena for cancellation.

No absolute value is applied to an individual residual fibre in this module.
The quantitative frontier is the weighted row energy after equal reciprocal
arguments are recombined.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- Möbius seed retained strictly below the square-root cutoff. -/
def squareRootReplacementSeed (R d : ℕ) : ℂ :=
  if d < R then (((μ d : ℤ) : ℂ)) else 0

/-- Truncated divisor Möbius coefficient.  This is the complete signed
replacement coefficient at physical index `n`, before any norm is taken. -/
def squareRootReplacementKernel (R n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, squareRootReplacementSeed R d

/-- Below the root cutoff the truncated divisor sum is already the full Möbius
divisor sum, hence it vanishes except at `n = 1`. -/
theorem squareRootReplacementKernel_eq_ite_of_lt_root
    {R n : ℕ} (hn1 : 1 ≤ n) (hnR : n < R) :
    squareRootReplacementKernel R n = if n = 1 then 1 else 0 := by
  have hn0 : n ≠ 0 := by omega
  unfold squareRootReplacementKernel squareRootReplacementSeed
  calc
    (∑ d ∈ n.divisors,
        if d < R then (((μ d : ℤ) : ℂ)) else 0) =
      ∑ d ∈ n.divisors, (((μ d : ℤ) : ℂ)) := by
        apply Finset.sum_congr rfl
        intro d hd
        have hddata := Nat.mem_divisors.mp hd
        have hdn : d ≤ n := Nat.le_of_dvd (by omega) hddata.1
        have hdR : d < R := hdn.trans_lt hnR
        simp [hdR]
    _ = if n = 1 then 1 else 0 :=
      RHLean.Analysis.sum_divisors_moebius_eq_ite n

/-- Summing the truncated seed through any cutoff containing `R-1` gives the
ordinary Mertens prefix at `R-1`. -/
theorem sum_squareRootReplacementSeed_eq_mertens_pred
    {R X : ℕ} (hR : 2 ≤ R) (hRX : R - 1 ≤ X) :
    (∑ d ∈ Finset.Icc 1 X, squareRootReplacementSeed R d) =
      RHLean.Analysis.mertensSummatory (R - 1) := by
  have hfilter :
      (Finset.Icc 1 X).filter (fun d => d < R) = Finset.Icc 1 (R - 1) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  unfold squareRootReplacementSeed
  rw [← Finset.sum_filter, hfilter]
  exact (RHLean.Analysis.mertensSummatory_eq_sum_Icc (R - 1)).symm

/-- On the complete prefix below `R`, the replacement kernel contributes only
the `n = 1` term, which is exactly `M(X)`. -/
theorem sum_replacementKernel_below_root_eq_mertens
    {R X : ℕ} (hR : 2 ≤ R) :
    (∑ n ∈ Finset.Icc 1 (R - 1),
        squareRootReplacementKernel R n *
          RHLean.Analysis.mertensSummatory (X / n)) =
      RHLean.Analysis.mertensSummatory X := by
  have h1mem : (1 : ℕ) ∈ Finset.Icc 1 (R - 1) := by
    simp
    omega
  calc
    (∑ n ∈ Finset.Icc 1 (R - 1),
        squareRootReplacementKernel R n *
          RHLean.Analysis.mertensSummatory (X / n)) =
      ∑ n ∈ Finset.Icc 1 (R - 1),
        if n = 1 then RHLean.Analysis.mertensSummatory X else 0 := by
          apply Finset.sum_congr rfl
          intro n hn
          have hnIcc := Finset.mem_Icc.mp hn
          have hnR : n < R := by omega
          rw [squareRootReplacementKernel_eq_ite_of_lt_root hnIcc.1 hnR]
          by_cases hnone : n = 1
          · subst n
            simp
          · simp [hnone]
    _ = RHLean.Analysis.mertensSummatory X := by
      simp [h1mem]

/-- Every residual reciprocal cutoff in the square-endpoint tail is genuinely
lower scale. -/
theorem squareRootEndpoint_div_lt_root_of_root_le
    {R n : ℕ} (hR : 2 ≤ R) (hn : R ≤ n) :
    squareRootEndpoint R / n < R := by
  have hnpos : 0 < n := by omega
  apply (Nat.div_lt_iff_lt_mul hnpos).2
  have hXlt : squareRootEndpoint R < R * R := by
    unfold squareRootEndpoint
    have hsqpos : 0 < R ^ 2 := by positivity
    omega
  have hmul : R * R ≤ R * n := Nat.mul_le_mul_left R hn
  exact hXlt.trans_le hmul

/-- **Exact recursive replacement identity.**  At `X_R = R^2 - 1`, all
nontrivial truncated-divisor coefficients occur at indices `n >= R`, hence all
Mertens states produced by the replacement have argument strictly below `R`. -/
theorem mertensEndpoint_eq_pred_sub_recursiveReplacement
    (R : ℕ) (hR : 2 ≤ R) :
    RHLean.Analysis.mertensSummatory (squareRootEndpoint R) =
      RHLean.Analysis.mertensSummatory (R - 1) -
        ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
          squareRootReplacementKernel R n *
            RHLean.Analysis.mertensSummatory (squareRootEndpoint R / n) := by
  let X := squareRootEndpoint R
  have hRX : R ≤ X := by
    dsimp [X]
    unfold squareRootEndpoint
    have hsq : R + 1 ≤ R ^ 2 := by nlinarith
    omega
  have hpredX : R - 1 ≤ X := by omega
  have hset :
      Finset.Icc 1 X =
        Finset.Icc 1 (R - 1) ∪ Finset.Icc R X := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj :
      Disjoint (Finset.Icc 1 (R - 1)) (Finset.Icc R X) := by
    rw [Finset.disjoint_left]
    intro n hnlo hnhi
    simp only [Finset.mem_Icc] at hnlo hnhi
    omega
  have htel :=
    RHLean.Analysis.sum_convolveOne_mul_mertensSummatory_div
      (squareRootReplacementSeed R) X
  change
    (∑ n ∈ Finset.Icc 1 X,
        squareRootReplacementKernel R n *
          RHLean.Analysis.mertensSummatory (X / n)) =
      ∑ d ∈ Finset.Icc 1 X, squareRootReplacementSeed R d at htel
  rw [hset, Finset.sum_union hdisj,
    sum_replacementKernel_below_root_eq_mertens hR,
    sum_squareRootReplacementSeed_eq_mertens_pred hR hpredX] at htel
  dsimp [X] at htel ⊢
  rw [← htel]
  ring

/-- The exact residual tail, retained as a signed lower-scale Mertens family. -/
def squareRootRecursiveReplacementResidual (R : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
    squareRootReplacementKernel R n *
      RHLean.Analysis.mertensSummatory (squareRootEndpoint R / n)

/-- The endpoint is exactly the preceding lower-scale Mertens value minus the
recursive residual family. -/
theorem mertensEndpoint_eq_pred_sub_recursiveResidual
    (R : ℕ) (hR : 2 ≤ R) :
    RHLean.Analysis.mertensSummatory (squareRootEndpoint R) =
      RHLean.Analysis.mertensSummatory (R - 1) -
        squareRootRecursiveReplacementResidual R := by
  simpa [squareRootRecursiveReplacementResidual] using
    mertensEndpoint_eq_pred_sub_recursiveReplacement R hR

/-! ## Recombination by reciprocal quotient -/

/-- Complete signed coefficient carried by the physical tail indices whose
reciprocal cutoff is exactly `y`.  The complete fibre is summed before any norm. -/
def squareRootReplacementTailCoefficient (R y : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
    if squareRootEndpoint R / n = y then
      squareRootReplacementKernel R n
    else 0

/-- Final lower-scale coefficient row.  The preceding value `M(R-1)` is the
single Kronecker term; the entire physical replacement tail is subtracted only
after each reciprocal quotient fibre has been recombined. -/
def squareRootReplacementCoefficient (R y : ℕ) : ℂ :=
  (if y = R - 1 then 1 else 0) - squareRootReplacementTailCoefficient R y

/-- Recombining equal reciprocal cutoffs loses nothing: the physical residual
family is exactly the sum of the fully signed quotient-fibre coefficients times
the corresponding lower-scale Mertens values. -/
theorem sum_replacementTailCoefficient_mul_mertens_eq_residual
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ y ∈ Finset.range R,
        squareRootReplacementTailCoefficient R y *
          RHLean.Analysis.mertensSummatory y) =
      squareRootRecursiveReplacementResidual R := by
  classical
  unfold squareRootReplacementTailCoefficient
    squareRootRecursiveReplacementResidual
  calc
    (∑ y ∈ Finset.range R,
        (∑ n ∈ Finset.Icc R (squareRootEndpoint R),
          if squareRootEndpoint R / n = y then
            squareRootReplacementKernel R n
          else 0) * RHLean.Analysis.mertensSummatory y) =
      ∑ y ∈ Finset.range R,
        ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
          (if squareRootEndpoint R / n = y then
            squareRootReplacementKernel R n
          else 0) * RHLean.Analysis.mertensSummatory y := by
            apply Finset.sum_congr rfl
            intro y _hy
            rw [Finset.sum_mul]
    _ =
      ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
        ∑ y ∈ Finset.range R,
          (if squareRootEndpoint R / n = y then
            squareRootReplacementKernel R n
          else 0) * RHLean.Analysis.mertensSummatory y := by
            rw [Finset.sum_comm]
    _ =
      ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
        squareRootReplacementKernel R n *
          RHLean.Analysis.mertensSummatory (squareRootEndpoint R / n) := by
            apply Finset.sum_congr rfl
            intro n hn
            have hnR : R ≤ n := (Finset.mem_Icc.mp hn).1
            have hylt : squareRootEndpoint R / n < R :=
              squareRootEndpoint_div_lt_root_of_root_le hR hnR
            have hymem : squareRootEndpoint R / n ∈ Finset.range R :=
              Finset.mem_range.mpr hylt
            calc
              (∑ y ∈ Finset.range R,
                (if squareRootEndpoint R / n = y then
                  squareRootReplacementKernel R n
                else 0) * RHLean.Analysis.mertensSummatory y) =
                ∑ y ∈ Finset.range R,
                  if squareRootEndpoint R / n = y then
                    squareRootReplacementKernel R n *
                      RHLean.Analysis.mertensSummatory y
                  else 0 := by
                    apply Finset.sum_congr rfl
                    intro y _hy
                    by_cases heq : squareRootEndpoint R / n = y <;>
                      simp [heq]
              _ = squareRootReplacementKernel R n *
                    RHLean.Analysis.mertensSummatory
                      (squareRootEndpoint R / n) := by
                    simp [hymem]

/-- **Exact recombined lower-triangular row.**  The completed-square Mertens
value is a single signed linear combination of Mertens values at `y < R`.
There are no arbitrary-point or fibrewise error terms left. -/
theorem mertensEndpoint_eq_recombinedReplacementRow
    (R : ℕ) (hR : 2 ≤ R) :
    RHLean.Analysis.mertensSummatory (squareRootEndpoint R) =
      ∑ y ∈ Finset.range R,
        squareRootReplacementCoefficient R y *
          RHLean.Analysis.mertensSummatory y := by
  have htail := sum_replacementTailCoefficient_mul_mertens_eq_residual R hR
  have hpredlt : R - 1 < R := by omega
  have hpredmem : R - 1 ∈ Finset.range R := Finset.mem_range.mpr hpredlt
  have hpred :
      (∑ y ∈ Finset.range R,
        (if y = R - 1 then (1 : ℂ) else 0) *
          RHLean.Analysis.mertensSummatory y) =
        RHLean.Analysis.mertensSummatory (R - 1) := by
    simp [hpredmem]
  calc
    RHLean.Analysis.mertensSummatory (squareRootEndpoint R) =
        RHLean.Analysis.mertensSummatory (R - 1) -
          squareRootRecursiveReplacementResidual R :=
      mertensEndpoint_eq_pred_sub_recursiveResidual R hR
    _ =
        (∑ y ∈ Finset.range R,
          (if y = R - 1 then (1 : ℂ) else 0) *
            RHLean.Analysis.mertensSummatory y) -
        ∑ y ∈ Finset.range R,
          squareRootReplacementTailCoefficient R y *
            RHLean.Analysis.mertensSummatory y := by rw [hpred, htail]
    _ =
      ∑ y ∈ Finset.range R,
        squareRootReplacementCoefficient R y *
          RHLean.Analysis.mertensSummatory y := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y _hy
      unfold squareRootReplacementCoefficient
      ring

/-- Weighted coefficient row energy.  This is evaluated only after the entire
physical quotient fibre at each lower Mertens argument has been recombined. -/
def squareRootReplacementRowEnergy (R : ℕ) : ℝ :=
  ∑ y ∈ Finset.range R,
    (((y + 1 : ℕ) : ℝ)) * ‖squareRootReplacementCoefficient R y‖ ^ 2

/-- The genuinely new quantitative target for this recursive replacement.
An `O(R)` bound is exactly the row scale compatible with a lower critical
Mertens envelope after weighted Cauchy--Schwarz.  No such estimate is assumed by
any exact identity above. -/
def RecursivePrimeReplacementRowEnergyBoundedStatement : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧
    ∀ R : ℕ, 2 ≤ R →
      squareRootReplacementRowEnergy R ≤ A * (R : ℝ)

end RHLean.Proof

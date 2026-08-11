from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'nativeLambdaTwoErrorMass_compensation' not in s
marker = '\nend RHLean.Analysis\n'
assert marker in s
block = r'''

/-! ## Good-fibre compensation -/

/-- Fibres on which the normalized Chebyshev error is at most `beta`. -/
def nativePNTGoodFiberSet (N : ℕ) (beta : ℝ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n =>
    |nativePNTError (N / n)| ≤ beta * ((N : ℝ) / (n : ℝ)))

/-- Reciprocal second-kernel mass carried by the good fibres. -/
def nativeLambdaTwoGoodRecipMass (N : ℕ) (beta : ℝ) : ℝ :=
  ∑ n ∈ nativePNTGoodFiberSet N beta, nativeLambdaTwo n / (n : ℝ)

/-- The good reciprocal mass is nonnegative. -/
theorem nativeLambdaTwoGoodRecipMass_nonneg (N : ℕ) (beta : ℝ) :
    0 ≤ nativeLambdaTwoGoodRecipMass N beta := by
  unfold nativeLambdaTwoGoodRecipMass nativePNTGoodFiberSet
  apply Finset.sum_nonneg
  intro n hn
  have hnI := (Finset.mem_filter.mp hn).1
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
  exact div_nonneg (nativeLambdaTwo_nonneg n hn1) (by positivity)

/-- The good set is contained in the positive endpoint range. -/
theorem nativePNTGoodFiberSet_subset (N : ℕ) (beta : ℝ) :
    nativePNTGoodFiberSet N beta ⊆ Finset.Icc 1 N := by
  intro n hn
  exact (Finset.mem_filter.mp hn).1

private theorem nativeLambdaTwoRecipSplit
    (N : ℕ) (beta : ℝ) :
    nativeLambdaTwoGoodRecipMass N beta +
      (∑ n ∈ (Finset.Icc 1 N).filter
        (fun n => ¬ |nativePNTError (N / n)| ≤
          beta * ((N : ℝ) / (n : ℝ))),
        nativeLambdaTwo n / (n : ℝ)) =
      nativeLambdaTwoRecipMass N := by
  unfold nativeLambdaTwoGoodRecipMass nativePNTGoodFiberSet
    nativeLambdaTwoRecipMass
  exact Finset.sum_filter_add_sum_filter_not
    (s := Finset.Icc 1 N)
    (p := fun n => |nativePNTError (N / n)| ≤
      beta * ((N : ℝ) / (n : ℝ)))
    (f := fun n => nativeLambdaTwo n / (n : ℝ))

private theorem nativeLambdaTwoMassSplit
    (N : ℕ) (beta : ℝ) :
    (∑ n ∈ nativePNTGoodFiberSet N beta, nativeLambdaTwo n) +
      (∑ n ∈ (Finset.Icc 1 N).filter
        (fun n => ¬ |nativePNTError (N / n)| ≤
          beta * ((N : ℝ) / (n : ℝ))),
        nativeLambdaTwo n) = nativeLambdaTwoSummatory N := by
  unfold nativePNTGoodFiberSet nativeLambdaTwoSummatory
  exact Finset.sum_filter_add_sum_filter_not
    (s := Finset.Icc 1 N)
    (p := fun n => |nativePNTError (N / n)| ≤
      beta * ((N : ℝ) / (n : ℝ)))
    (f := fun n => nativeLambdaTwo n)

/-- **Good-fibre compensation identity.**  If every reciprocal fibre obeys an
`alpha` envelope up to an additive constant `D`, then fibres already inside a
smaller `beta` envelope subtract their reciprocal `LambdaTwo` mass from the
worst-case bound:

`errorMass <= alpha*N*S2 - (alpha-beta)*N*goodMass + D*rho`.

This is the exact algebraic deficit used by the Erdos cubic improvement. -/
theorem nativeLambdaTwoErrorMass_compensation
    (N : ℕ) (alpha beta D : ℝ)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hba : beta ≤ alpha)
    (hD : 0 ≤ D)
    (hall : ∀ n ∈ Finset.Icc 1 N,
      |nativePNTError (N / n)| ≤ alpha * ((N : ℝ) / (n : ℝ)) + D) :
    nativeLambdaTwoErrorMass N ≤
      alpha * (N : ℝ) * nativeLambdaTwoRecipMass N -
        (alpha - beta) * (N : ℝ) * nativeLambdaTwoGoodRecipMass N beta +
        D * nativeLambdaTwoSummatory N := by
  let p : ℕ → Prop := fun n =>
    |nativePNTError (N / n)| ≤ beta * ((N : ℝ) / (n : ℝ))
  let G := (Finset.Icc 1 N).filter p
  let B := (Finset.Icc 1 N).filter (fun n => ¬ p n)
  have hsplit :
      nativeLambdaTwoErrorMass N =
        (∑ n ∈ G, nativeLambdaTwo n * |nativePNTError (N / n)|) +
          ∑ n ∈ B, nativeLambdaTwo n * |nativePNTError (N / n)| := by
    unfold nativeLambdaTwoErrorMass
    dsimp [G, B]
    rw [Finset.sum_filter_add_sum_filter_not]
  have hgood :
      (∑ n ∈ G, nativeLambdaTwo n * |nativePNTError (N / n)|) ≤
        ∑ n ∈ G, nativeLambdaTwo n *
          (beta * ((N : ℝ) / (n : ℝ)) + D) := by
    apply Finset.sum_le_sum
    intro n hn
    have hnF := Finset.mem_filter.mp hn
    have hnI := hnF.1
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
    have hp : |nativePNTError (N / n)| ≤
        beta * ((N : ℝ) / (n : ℝ)) := hnF.2
    have hpD : |nativePNTError (N / n)| ≤
        beta * ((N : ℝ) / (n : ℝ)) + D :=
      hp.trans (le_add_of_nonneg_right hD)
    exact mul_le_mul_of_nonneg_left hpD (nativeLambdaTwo_nonneg n hn1)
  have hbad :
      (∑ n ∈ B, nativeLambdaTwo n * |nativePNTError (N / n)|) ≤
        ∑ n ∈ B, nativeLambdaTwo n *
          (alpha * ((N : ℝ) / (n : ℝ)) + D) := by
    apply Finset.sum_le_sum
    intro n hn
    have hnF := Finset.mem_filter.mp hn
    have hnI := hnF.1
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
    exact mul_le_mul_of_nonneg_left (hall n hnI)
      (nativeLambdaTwo_nonneg n hn1)
  have hbound :
      nativeLambdaTwoErrorMass N ≤
        (∑ n ∈ G, nativeLambdaTwo n *
          (beta * ((N : ℝ) / (n : ℝ)) + D)) +
        ∑ n ∈ B, nativeLambdaTwo n *
          (alpha * ((N : ℝ) / (n : ℝ)) + D) := by
    rw [hsplit]
    exact add_le_add hgood hbad
  have hGrec :
      (∑ n ∈ G, nativeLambdaTwo n * ((N : ℝ) / (n : ℝ))) =
        (N : ℝ) * nativeLambdaTwoGoodRecipMass N beta := by
    dsimp [G, p]
    unfold nativeLambdaTwoGoodRecipMass nativePNTGoodFiberSet
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _hn
    ring
  have hBrec :
      (∑ n ∈ B, nativeLambdaTwo n * ((N : ℝ) / (n : ℝ))) =
        (N : ℝ) *
          (∑ n ∈ (Finset.Icc 1 N).filter
            (fun n => ¬ |nativePNTError (N / n)| ≤
              beta * ((N : ℝ) / (n : ℝ))),
            nativeLambdaTwo n / (n : ℝ)) := by
    dsimp [B, p]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _hn
    ring
  have hGmass :
      (∑ n ∈ G, nativeLambdaTwo n) =
        ∑ n ∈ nativePNTGoodFiberSet N beta, nativeLambdaTwo n := by
    rfl
  have hBmass :
      (∑ n ∈ B, nativeLambdaTwo n) =
        ∑ n ∈ (Finset.Icc 1 N).filter
          (fun n => ¬ |nativePNTError (N / n)| ≤
            beta * ((N : ℝ) / (n : ℝ))), nativeLambdaTwo n := by
    rfl
  have hGexpand :
      (∑ n ∈ G, nativeLambdaTwo n *
        (beta * ((N : ℝ) / (n : ℝ)) + D)) =
        beta * ((N : ℝ) * nativeLambdaTwoGoodRecipMass N beta) +
          D * (∑ n ∈ nativePNTGoodFiberSet N beta, nativeLambdaTwo n) := by
    calc
      (∑ n ∈ G, nativeLambdaTwo n *
        (beta * ((N : ℝ) / (n : ℝ)) + D)) =
          beta * (∑ n ∈ G,
            nativeLambdaTwo n * ((N : ℝ) / (n : ℝ))) +
          D * (∑ n ∈ G, nativeLambdaTwo n) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro n _hn
        ring
      _ = _ := by rw [hGrec, hGmass]
  have hBexpand :
      (∑ n ∈ B, nativeLambdaTwo n *
        (alpha * ((N : ℝ) / (n : ℝ)) + D)) =
        alpha * ((N : ℝ) *
          (∑ n ∈ (Finset.Icc 1 N).filter
            (fun n => ¬ |nativePNTError (N / n)| ≤
              beta * ((N : ℝ) / (n : ℝ))),
            nativeLambdaTwo n / (n : ℝ))) +
          D * (∑ n ∈ (Finset.Icc 1 N).filter
            (fun n => ¬ |nativePNTError (N / n)| ≤
              beta * ((N : ℝ) / (n : ℝ))), nativeLambdaTwo n) := by
    calc
      (∑ n ∈ B, nativeLambdaTwo n *
        (alpha * ((N : ℝ) / (n : ℝ)) + D)) =
          alpha * (∑ n ∈ B,
            nativeLambdaTwo n * ((N : ℝ) / (n : ℝ))) +
          D * (∑ n ∈ B, nativeLambdaTwo n) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro n _hn
        ring
      _ = _ := by rw [hBrec, hBmass]
  rw [hGexpand, hBexpand] at hbound
  have hrecSplit := nativeLambdaTwoRecipSplit N beta
  have hmassSplit := nativeLambdaTwoMassSplit N beta
  nlinarith
'''
s = s.replace(marker, block + marker, 1)
p.write_text(s)

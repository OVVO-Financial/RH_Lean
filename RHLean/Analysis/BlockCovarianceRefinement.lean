import Mathlib
import RHLean.Analysis.BlockCovarianceDecomposition

open scoped ArithmeticFunction.Moebius BigOperators

/-!
# Refining blocks to the exact diagonal, and the fresh-prime family isomorphism

`BlockCovarianceDecomposition` proves `S^2 = E + 2X` for signed blocks and
instantiates it at the square blocks.  Two things follow, and both are exact.

## 1. The block energy is not a free linear fact

The square-block energy exceeds the exact squarefree diagonal by *precisely*
twice the aggregate within-block covariance:

```text
E - Q = 2 * sum_j C_j,        Q(N) = sum_{n<N} mu(n)^2 = N - Z(N).
```

So proving `E << N^(1+eps)` is proving that aggregate is of RH scale.  It is not
an independent input, and the linear behaviour measured numerically must not be
promoted to a theorem.

The way out is not to bound `E` but to *refine* it.  For any splitting of every
block into signed children,

```text
E_coarse = E_refined + 2 * sum_j (children cross covariance of block j),
```

so each refinement step moves energy into the children and leaves behind an
explicit signed cross term.  Iterated down to singletons the energy becomes the
exact squarefree diagonal `Q(N)`, which is linear with no conjecture at all, and
every unordered Möbius pair has been charged to the unique refinement node at
which its two entries first separate.  That is the Green--Kubo identity rewritten
as an Euler/Othello covariance tree, with every signed cross term preserved on
the way down.

## 2. Fresh post-root primes preserve pair covariance

For a prime `p` and cofactors below `p`, multiplication by `p` flips the Möbius
sign, so it *reverses* the family mass but **preserves** the family pair
covariance:

```text
mu(p c) = - mu(c),        mu(p c) mu(p d) = mu(c) mu(d).
```

Hence the covariance carried strictly inside the `p`-family is literally the
global Möbius covariance at the reduced scale:

```text
C_inside p-family (through W) = C(floor(W/p) + 1)        for p * p > W.
```

That is an exact covariance descent, not an analogy: a post-root prime family is
an isometric copy of a lower-scale prefix as far as pair covariance is
concerned.  Summing over post-root primes and grouping by the reciprocal
quotient turns a supercritical scale into a sum of strictly lower-scale
covariances, which is where the descent formulation of
`MertensCovarianceDescent` earns its power saving.

No estimate, asymptotic input or RH hypothesis appears in this file.
-/

noncomputable section

namespace RHLean.Analysis

/-! ## The site-level objects are the generic ones -/

theorem signedBlockPrefix_realMoebiusStep (K : ℕ) :
    signedBlockPrefix realMoebiusStep K = realMertensLength K := rfl

theorem signedBlockEnergy_realMoebiusStep (K : ℕ) :
    signedBlockEnergy realMoebiusStep K = realMertensDiagonal K := rfl

theorem signedBlockCrossCovariance_realMoebiusStep (K : ℕ) :
    signedBlockCrossCovariance realMoebiusStep K =
      realMertensPositiveLagPairSum K := rfl

/-! ## One refinement step -/

/-- **Refinement identity.**  Splitting every block into signed children moves
the energy into the children and leaves exactly twice their internal cross
covariance behind.  Nothing is estimated and no absolute value is taken. -/
theorem signedBlockEnergy_refine
    (b : ℕ → ℕ → ℝ) (m : ℕ → ℕ) (K : ℕ) :
    signedBlockEnergy (fun j => signedBlockPrefix (b j) (m j)) K =
      (∑ j ∈ Finset.range K, signedBlockEnergy (b j) (m j)) +
        2 * ∑ j ∈ Finset.range K, signedBlockCrossCovariance (b j) (m j) := by
  have hstep : ∀ j ∈ Finset.range K,
      signedBlockPrefix (b j) (m j) ^ 2 =
        signedBlockEnergy (b j) (m j) +
          2 * signedBlockCrossCovariance (b j) (m j) :=
    fun j _hj => signedBlockPrefix_sq_eq_energy_add_two_mul_cross (b j) (m j)
  calc signedBlockEnergy (fun j => signedBlockPrefix (b j) (m j)) K
      = ∑ j ∈ Finset.range K, signedBlockPrefix (b j) (m j) ^ 2 := rfl
    _ = ∑ j ∈ Finset.range K,
          (signedBlockEnergy (b j) (m j) +
            2 * signedBlockCrossCovariance (b j) (m j)) :=
        Finset.sum_congr rfl hstep
    _ = (∑ j ∈ Finset.range K, signedBlockEnergy (b j) (m j)) +
          ∑ j ∈ Finset.range K, 2 * signedBlockCrossCovariance (b j) (m j) :=
        Finset.sum_add_distrib
    _ = (∑ j ∈ Finset.range K, signedBlockEnergy (b j) (m j)) +
          2 * ∑ j ∈ Finset.range K, signedBlockCrossCovariance (b j) (m j) := by
        rw [Finset.mul_sum]

/-- The leaf of any refinement is the exact squarefree diagonal, which needs no
conjecture: it is bounded by the number of sites. -/
theorem signedBlockEnergy_leaf_le (K : ℕ) :
    signedBlockEnergy realMoebiusStep K ≤ (K : ℝ) := by
  rw [signedBlockEnergy_realMoebiusStep]
  exact realMertensDiagonal_le K

/-! ## Square blocks: energy versus the exact diagonal -/

/-- Squarefree diagonal carried by the square block `[j^2, (j+1)^2)`. -/
def realSquareBlockDiagonal (j : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (j ^ 2) ((j + 1) ^ 2), realMoebiusStep n ^ 2

private theorem square_le_succ_square (j : ℕ) : j ^ 2 ≤ (j + 1) ^ 2 :=
  Nat.pow_le_pow_left (by omega) 2

theorem realSquareBlockMass_eq_sub (j : ℕ) :
    realSquareBlockMass j =
      realMertensLength ((j + 1) ^ 2) - realMertensLength (j ^ 2) := by
  have hsplit :=
    Finset.sum_range_add_sum_Ico realMoebiusStep (square_le_succ_square j)
  unfold realSquareBlockMass realMertensLength
  linarith [hsplit]

theorem realSquareBlockDiagonal_eq_sub (j : ℕ) :
    realSquareBlockDiagonal j =
      realMertensDiagonal ((j + 1) ^ 2) - realMertensDiagonal (j ^ 2) := by
  have hsplit :=
    Finset.sum_range_add_sum_Ico (fun n => realMoebiusStep n ^ 2)
      (square_le_succ_square j)
  unfold realSquareBlockDiagonal realMertensDiagonal
  linarith [hsplit]

/-- **Green--Kubo inside one square block.** -/
theorem realSquareBlockMass_sq_eq_diagonal_add_two_mul_inner (j : ℕ) :
    realSquareBlockMass j ^ 2 =
      realSquareBlockDiagonal j + 2 * realSquareBlockInnerCovariance j := by
  have hb :=
    realMertensLength_sq_eq_diagonal_add_two_mul_positiveLagPairSum ((j + 1) ^ 2)
  have ha :=
    realMertensLength_sq_eq_diagonal_add_two_mul_positiveLagPairSum (j ^ 2)
  have hmass := realSquareBlockMass_eq_sub j
  have hinner : realSquareBlockInnerCovariance j =
      realMertensPositiveLagPairSum ((j + 1) ^ 2) -
        realMertensPositiveLagPairSum (j ^ 2) -
        realMertensLength (j ^ 2) *
          (realMertensLength ((j + 1) ^ 2) - realMertensLength (j ^ 2)) := by
    unfold realSquareBlockInnerCovariance
    rw [hmass]
  rw [hmass, realSquareBlockDiagonal_eq_sub j, hinner]
  linear_combination hb - ha

/-- The square-block diagonals telescope to the exact global diagonal. -/
theorem sum_realSquareBlockDiagonal (R : ℕ) :
    ∑ j ∈ Finset.range R, realSquareBlockDiagonal j =
      realMertensDiagonal (R ^ 2) := by
  induction R with
  | zero => norm_num [realMertensDiagonal]
  | succ R ih =>
      rw [Finset.sum_range_succ, ih, realSquareBlockDiagonal_eq_sub R]
      ring

/-- **The square-block energy is the exact diagonal plus twice the aggregate
within-block covariance.** -/
theorem signedBlockEnergy_realSquareBlockMass_eq (R : ℕ) :
    signedBlockEnergy realSquareBlockMass R =
      realMertensDiagonal (R ^ 2) +
        2 * ∑ j ∈ Finset.range R, realSquareBlockInnerCovariance j := by
  induction R with
  | zero => norm_num [realMertensDiagonal]
  | succ R ih =>
      rw [signedBlockEnergy_succ, Finset.sum_range_succ, ih,
        realSquareBlockMass_sq_eq_diagonal_add_two_mul_inner R,
        realSquareBlockDiagonal_eq_sub R]
      ring

/-- **The block energy is not an independent linear input.**  It exceeds the
exact squarefree diagonal by precisely twice the aggregate within-block
covariance, so an RH-scale bound on one is an RH-scale bound on the other. -/
theorem signedBlockEnergy_realSquareBlockMass_sub_diagonal (R : ℕ) :
    signedBlockEnergy realSquareBlockMass R - realMertensDiagonal (R ^ 2) =
      2 * ∑ j ∈ Finset.range R, realSquareBlockInnerCovariance j := by
  rw [signedBlockEnergy_realSquareBlockMass_eq]
  ring

/-! ## Fresh post-root prime families -/

/-- Multiplying a cofactor below `p` by the prime `p` reverses its Möbius
sign. -/
theorem realMoebiusStep_prime_mul_of_lt {p c : ℕ} (hp : p.Prime) (hc : c < p) :
    realMoebiusStep (p * c) = - realMoebiusStep c := by
  rcases Nat.eq_zero_or_pos c with rfl | hcpos
  · simp [realMoebiusStep]
  · have hnd : ¬ p ∣ c := by
      intro hd
      exact absurd (Nat.le_of_dvd hcpos hd) (not_le.mpr hc)
    exact realMoebiusStep_mul_prime_eq_neg hp hnd

/-- **A fresh prime preserves pair covariance while reversing mass.** -/
theorem realMoebiusStep_prime_mul_pair {p c d : ℕ} (hp : p.Prime)
    (hc : c < p) (hd : d < p) :
    realMoebiusStep (p * c) * realMoebiusStep (p * d) =
      realMoebiusStep c * realMoebiusStep d := by
  rw [realMoebiusStep_prime_mul_of_lt hp hc, realMoebiusStep_prime_mul_of_lt hp hd]
  ring

/-- Signed mass of the first `K` members of the `p`-family. -/
def largePrimeFamilyPrefix (p K : ℕ) : ℝ :=
  ∑ c ∈ Finset.range K, realMoebiusStep (p * c)

/-- Pair covariance carried strictly inside the `p`-family. -/
def largePrimeFamilyPairSum (p K : ℕ) : ℝ :=
  ∑ d ∈ Finset.range K, realMoebiusStep (p * d) * largePrimeFamilyPrefix p d

/-- The family mass is the reduced Mertens value with the sign reversed. -/
theorem largePrimeFamilyPrefix_eq_neg {p K : ℕ} (hp : p.Prime) (hK : K ≤ p) :
    largePrimeFamilyPrefix p K = - realMertensLength K := by
  have hstep : ∀ c ∈ Finset.range K,
      realMoebiusStep (p * c) = - realMoebiusStep c := by
    intro c hc
    exact realMoebiusStep_prime_mul_of_lt hp
      (lt_of_lt_of_le (Finset.mem_range.mp hc) hK)
  unfold largePrimeFamilyPrefix realMertensLength
  rw [Finset.sum_congr rfl hstep]
  simp

/-- **Covariance descent through a fresh prime family.**

The pair covariance inside the `p`-family is *exactly* the global Möbius
covariance at the reduced scale.  The two sign reversals cancel in every
product, so nothing is lost and nothing is estimated. -/
theorem largePrimeFamilyPairSum_eq {p K : ℕ} (hp : p.Prime) (hK : K ≤ p) :
    largePrimeFamilyPairSum p K = realMertensPositiveLagPairSum K := by
  unfold largePrimeFamilyPairSum realMertensPositiveLagPairSum
  refine Finset.sum_congr rfl ?_
  intro d hd
  have hdK := Finset.mem_range.mp hd
  have hdp : d < p := lt_of_lt_of_le hdK hK
  rw [realMoebiusStep_prime_mul_of_lt hp hdp,
    largePrimeFamilyPrefix_eq_neg hp (hdK.le.trans hK)]
  ring

/-- **Post-root form.**  For a prime beyond the square root of the cutoff the
whole family lies below `p`, so its internal covariance is the Möbius covariance
at scale `floor(W/p) + 1`. -/
theorem largePrimeFamilyPairSum_postRoot {p W : ℕ} (hp : p.Prime)
    (hW : W < p * p) :
    largePrimeFamilyPairSum p (W / p + 1) =
      realMertensPositiveLagPairSum (W / p + 1) := by
  refine largePrimeFamilyPairSum_eq hp ?_
  have hlt : W / p < p := (Nat.div_lt_iff_lt_mul hp.pos).mpr hW
  omega

end RHLean.Analysis

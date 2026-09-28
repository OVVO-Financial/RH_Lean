import Mathlib
import RHLean.Proof.SquareRootLowPrimeTSectorQ2Renormalization
import «research.GLOBAL_RETURNED_CORE_GENERIC_GREATEST_OWNER_CONTRACTION»

/-!
# Post-crossing normalization audit

This file isolates the normalization seam in the proposed use of the fixed
crossing depth.

There are two different statements.

1. If a coefficient has already legally entered reciprocal energy currency and
   is retained unchanged, then a greatest-owner child at prime `p` carries
   exactly `1/p^2` of the parent reciprocal energy.  With fixed-parent child
   multiplicity at most two, owners strictly above a cutoff `K` consume at
   most `2/K` of the parent energy.  This is an unconditional finite bound;
   no PNT is needed.

2. If instead one rescales the child coefficient by `p` in order to preserve
   the raw chronological amplitude, the `p^2` coefficient square cancels the
   reciprocal `1/p^2` child-energy factor exactly.  The child then carries the
   full parent energy.  Hence the cutoff alone cannot transfer the raw signed
   chronology into the reciprocal ledger.

The numerical prime `18353`, the first prime above the certified crossing
cutoff `18349`, is recorded only as a normalization sanity check:
`1/18353^2 = 1/336832609`, while multiplying the retained coefficient by
`18353` restores energy factor one.

No RH hypothesis, asymptotic estimate, or Mertens magnitude bound is used.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Prime owners strictly above a finite cutoff. -/
def postCrossingPrimeOwnerSet (K N : ℕ) : Finset ℕ :=
  (primesUpTo N).filter fun p => K < p

@[simp] theorem mem_postCrossingPrimeOwnerSet
    {K N p : ℕ} :
    p ∈ postCrossingPrimeOwnerSet K N ↔
      p.Prime ∧ p ≤ N ∧ K < p := by
  simp [postCrossingPrimeOwnerSet, and_assoc, and_left_comm, and_comm]

/-- Elementary finite reciprocal-square tail over all integers:
`sum_{K<n<=N} 1/n^2 <= 1/K - 1/N`. -/
theorem reciprocalSquareTail_Ioc_le_inv_sub_inv
    {K N : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) :
    (∑ n ∈ Finset.Ioc K N, (1 : ℚ) / (n : ℚ) ^ 2) ≤
      1 / (K : ℚ) - 1 / (N : ℚ) := by
  induction N, hKN using Nat.le_induction with
  | base =>
      simp
  | succ N hKN ih =>
      rw [Finset.sum_Ioc_succ_top hKN]
      have hterm := reciprocalSquareTerm_le_telescope
        (n := N + 1) (by omega)
      have hcast :
          (((N + 1 : ℕ) : ℚ) - 1) = (N : ℚ) := by
        push_cast
        ring
      rw [hcast] at hterm
      calc
        (∑ n ∈ Finset.Ioc K N, (1 : ℚ) / (n : ℚ) ^ 2) +
            (1 : ℚ) / ((N + 1 : ℕ) : ℚ) ^ 2 ≤
          (1 / (K : ℚ) - 1 / (N : ℚ)) +
            (1 / (N : ℚ) - 1 / ((N + 1 : ℕ) : ℚ)) :=
              add_le_add ih hterm
        _ = 1 / (K : ℚ) - 1 / ((N + 1 : ℕ) : ℚ) := by
          ring

/-- Dropping the nonnegative endpoint term gives the simple `1/K` tail. -/
theorem reciprocalSquareTail_Ioc_le_inv
    {K N : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) :
    (∑ n ∈ Finset.Ioc K N, (1 : ℚ) / (n : ℚ) ^ 2) ≤
      1 / (K : ℚ) := by
  have h :=
    reciprocalSquareTail_Ioc_le_inv_sub_inv hK hKN
  have hN : (0 : ℚ) ≤ 1 / (N : ℚ) := by positivity
  linarith

/-- Prime reciprocal-square mass above `K` is bounded by the integer tail. -/
theorem postCrossingPrimeOwnerReciprocalSquareBudget_le_inv
    {K N : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) :
    (∑ p ∈ postCrossingPrimeOwnerSet K N,
        (1 : ℚ) / (p : ℚ) ^ 2) ≤
      1 / (K : ℚ) := by
  have hsubset :
      postCrossingPrimeOwnerSet K N ⊆ Finset.Ioc K N := by
    intro p hp
    rcases mem_postCrossingPrimeOwnerSet.mp hp with ⟨_hpPrime, hpN, hKp⟩
    exact Finset.mem_Ioc.mpr ⟨hKp, hpN⟩
  have hsum :
      (∑ p ∈ postCrossingPrimeOwnerSet K N,
          (1 : ℚ) / (p : ℚ) ^ 2) ≤
        ∑ n ∈ Finset.Ioc K N, (1 : ℚ) / (n : ℚ) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro n _hnNew _hnOld
    positivity
  exact hsum.trans (reciprocalSquareTail_Ioc_le_inv hK hKN)

/-- Real form of the finite prime reciprocal-square tail. -/
theorem postCrossingPrimeOwnerReciprocalSquareBudgetReal_le_inv
    {K N : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) :
    (∑ p ∈ postCrossingPrimeOwnerSet K N,
        (1 : ℝ) / (p : ℝ) ^ 2) ≤
      1 / (K : ℝ) := by
  have hQ :=
    postCrossingPrimeOwnerReciprocalSquareBudget_le_inv hK hKN
  have hcast :
      (((∑ p ∈ postCrossingPrimeOwnerSet K N,
          (1 : ℚ) / (p : ℚ) ^ 2) : ℚ) : ℝ) ≤
        (((1 / (K : ℚ) : ℚ)) : ℝ) := by
    exact_mod_cast hQ
  push_cast at hcast
  simpa [Nat.cast_pow] using hcast

/-- Fixed-coefficient reciprocal energy carried by all greatest-owner children
whose owner lies strictly above `K`. -/
def lowOwnerRetainedCoefficientPostCrossingOutgoingEnergy
    (R K : ℕ) (parent : ℕ × ℕ) (coefficient : ℝ) : ℝ :=
  ∑ p ∈ postCrossingPrimeOwnerSet K (squareRootEndpoint R),
    ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent p,
      lowOwnerRetainedCoefficientChildEnergy coefficient child

/-- **Valid fixed-currency post-crossing bound.**

Once the coefficient is already in reciprocal currency and remains fixed, the
owner multiplicity bound `<= 2` and the reciprocal-square tail give the
unconditional coefficient `2/K`. -/
theorem lowOwnerRetainedCoefficientPostCrossingOutgoingEnergy_le_two_div
    {R K : ℕ} (hK : 1 ≤ K)
    (hKR : K ≤ squareRootEndpoint R)
    (parent : ℕ × ℕ) (coefficient : ℝ) :
    lowOwnerRetainedCoefficientPostCrossingOutgoingEnergy
        R K parent coefficient ≤
      (2 / (K : ℝ)) *
        lowOwnerRetainedCoefficientParentEnergy coefficient parent := by
  unfold lowOwnerRetainedCoefficientPostCrossingOutgoingEnergy
  calc
    (∑ p ∈ postCrossingPrimeOwnerSet K (squareRootEndpoint R),
      ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent p,
        lowOwnerRetainedCoefficientChildEnergy coefficient child) =
      ∑ p ∈ postCrossingPrimeOwnerSet K (squareRootEndpoint R),
        (lowOwnerGreatestOwnerFixedParentChildMultiplicity R parent p : ℝ) /
          (p : ℝ) ^ 2 *
            lowOwnerRetainedCoefficientParentEnergy coefficient parent := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpPrime := (mem_postCrossingPrimeOwnerSet.mp hp).1
      exact sum_lowOwnerRetainedCoefficientChildEnergy_eq
        hpPrime parent coefficient
    _ ≤
      ∑ p ∈ postCrossingPrimeOwnerSet K (squareRootEndpoint R),
        (2 : ℝ) / (p : ℝ) ^ 2 *
          lowOwnerRetainedCoefficientParentEnergy coefficient parent := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPrime := (mem_postCrossingPrimeOwnerSet.mp hp).1
      have hpPos : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast hpPrime.pos
      have hmultNat :=
        lowOwnerGreatestOwnerFixedParentChildMultiplicity_le_two R parent p
      have hmult :
          (lowOwnerGreatestOwnerFixedParentChildMultiplicity R parent p : ℝ) ≤ 2 := by
        exact_mod_cast hmultNat
      have hratio :
          (lowOwnerGreatestOwnerFixedParentChildMultiplicity R parent p : ℝ) /
              (p : ℝ) ^ 2 ≤
            (2 : ℝ) / (p : ℝ) ^ 2 := by
        exact div_le_div_of_nonneg_right hmult (by positivity)
      exact mul_le_mul_of_nonneg_right hratio
        (lowOwnerRetainedCoefficientParentEnergy_nonneg coefficient parent)
    _ =
      2 *
        (∑ p ∈ postCrossingPrimeOwnerSet K (squareRootEndpoint R),
          (1 : ℝ) / (p : ℝ) ^ 2) *
            lowOwnerRetainedCoefficientParentEnergy coefficient parent := by
      calc
        (∑ p ∈ postCrossingPrimeOwnerSet K (squareRootEndpoint R),
            (2 : ℝ) / (p : ℝ) ^ 2 *
              lowOwnerRetainedCoefficientParentEnergy coefficient parent) =
          ∑ p ∈ postCrossingPrimeOwnerSet K (squareRootEndpoint R),
            2 * ((1 : ℝ) / (p : ℝ) ^ 2 *
              lowOwnerRetainedCoefficientParentEnergy coefficient parent) := by
            apply Finset.sum_congr rfl
            intro p _hp
            ring
        _ = 2 *
            (∑ p ∈ postCrossingPrimeOwnerSet K (squareRootEndpoint R),
              (1 : ℝ) / (p : ℝ) ^ 2 *
                lowOwnerRetainedCoefficientParentEnergy coefficient parent) := by
              rw [Finset.mul_sum]
        _ = 2 *
            ((∑ p ∈ postCrossingPrimeOwnerSet K (squareRootEndpoint R),
              (1 : ℝ) / (p : ℝ) ^ 2) *
                lowOwnerRetainedCoefficientParentEnergy coefficient parent) := by
              rw [Finset.sum_mul]
        _ = 2 *
            (∑ p ∈ postCrossingPrimeOwnerSet K (squareRootEndpoint R),
              (1 : ℝ) / (p : ℝ) ^ 2) *
                lowOwnerRetainedCoefficientParentEnergy coefficient parent := by
              ring
    _ ≤
      (2 / (K : ℝ)) *
        lowOwnerRetainedCoefficientParentEnergy coefficient parent := by
      have htail :=
        postCrossingPrimeOwnerReciprocalSquareBudgetReal_le_inv hK hKR
      have hparent :=
        lowOwnerRetainedCoefficientParentEnergy_nonneg coefficient parent
      have hscaled :
          2 *
              (∑ p ∈ postCrossingPrimeOwnerSet K (squareRootEndpoint R),
                (1 : ℝ) / (p : ℝ) ^ 2) ≤
            2 * (1 / (K : ℝ)) :=
        mul_le_mul_of_nonneg_left htail (by norm_num)
      calc
        2 *
            (∑ p ∈ postCrossingPrimeOwnerSet K (squareRootEndpoint R),
              (1 : ℝ) / (p : ℝ) ^ 2) *
              lowOwnerRetainedCoefficientParentEnergy coefficient parent ≤
          (2 * (1 / (K : ℝ))) *
              lowOwnerRetainedCoefficientParentEnergy coefficient parent :=
            mul_le_mul_of_nonneg_right hscaled hparent
        _ = (2 / (K : ℝ)) *
              lowOwnerRetainedCoefficientParentEnergy coefficient parent := by
            ring

/-- Pointwise fixed-coefficient form: the literal `1/p^2` survives exactly
when the child retains the parent's coefficient. -/
theorem lowOwnerRetainedCoefficientChildEnergy_eq_invSq_mul_parent
    {R p : ℕ} {parent child : ℕ × ℕ}
    (hp : p.Prime)
    (hchild : child ∈
      lowOwnerGreatestOwnerFixedParentChildFiber R parent p)
    (coefficient : ℝ) :
    lowOwnerRetainedCoefficientChildEnergy coefficient child =
      (1 / (p : ℝ) ^ 2) *
        lowOwnerRetainedCoefficientParentEnergy coefficient parent := by
  unfold lowOwnerRetainedCoefficientChildEnergy
    lowOwnerRetainedCoefficientParentEnergy
  rw [lowOwnerGreatestOwnerFixedParentChild_energy_eq hp hchild]
  ring

/-- **Normalization obstruction.**

If raw-history preservation multiplies the child coefficient by its owner
`p`, that coefficient square cancels the reciprocal `1/p^2` child-energy
factor exactly.  The child then carries the full parent energy. -/
theorem lowOwnerOwnerRescaledChildEnergy_eq_parent
    {R p : ℕ} {parent child : ℕ × ℕ}
    (hp : p.Prime)
    (hchild : child ∈
      lowOwnerGreatestOwnerFixedParentChildFiber R parent p)
    (coefficient : ℝ) :
    lowOwnerRetainedCoefficientChildEnergy
        ((p : ℝ) * coefficient) child =
      lowOwnerRetainedCoefficientParentEnergy coefficient parent := by
  unfold lowOwnerRetainedCoefficientChildEnergy
    lowOwnerRetainedCoefficientParentEnergy
  rw [lowOwnerGreatestOwnerFixedParentChild_energy_eq hp hchild]
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  field_simp [hp0]

/-- Finite arithmetic sanity check at the first prime above the certified
crossing cutoff. -/
theorem reciprocalSquare_18353 :
    (1 : ℚ) / (18353 : ℚ) ^ 2 = 1 / 336832609 := by
  norm_num

/-- The corresponding raw-history coefficient rescaling removes that gain. -/
theorem reciprocalSquare_18353_rescaled :
    (18353 : ℚ) ^ 2 * ((1 : ℚ) / (18353 : ℚ) ^ 2) = 1 := by
  norm_num

/-- Concrete valid fixed-currency bound at the certified crossing cutoff. -/
theorem lowOwnerRetainedCoefficientPostCrossingOutgoingEnergy_le_18349
    {R : ℕ} (hR : 18349 ≤ squareRootEndpoint R)
    (parent : ℕ × ℕ) (coefficient : ℝ) :
    lowOwnerRetainedCoefficientPostCrossingOutgoingEnergy
        R 18349 parent coefficient ≤
      (2 / 18349 : ℝ) *
        lowOwnerRetainedCoefficientParentEnergy coefficient parent := by
  exact lowOwnerRetainedCoefficientPostCrossingOutgoingEnergy_le_two_div
    (K := 18349) (by norm_num) hR parent coefficient

end RHLean.Proof

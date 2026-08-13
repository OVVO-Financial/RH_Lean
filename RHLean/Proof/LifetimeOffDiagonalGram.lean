import Mathlib
import RHLean.Proof.LifetimeOverlapGramCriterion

/-!
# Only off-diagonal lifetime overlap remains analytic

The fixed-terminal overlap Gram from `LifetimeOverlapGramCriterion` is a finite
pair sum over canonical high atoms.  Its diagonal is elementary:

* a canonical Mobius weight has norm at most one;
* a self-overlap kernel counts at most `H` observation stages;
* the birth-high terminal universe through stage `T` contains at most
  `(T+1)^2` atoms, because the square blocks partition the first `(T+1)^2`
  source integers.

For a translated window with `T = N+H`, `1 <= H <= N`, this gives a diagonal
bound `O(H N^2)`, which is already at the critical scale.  Hence the complete
lifetime overlap-Gram criterion is equivalent to control of the off-diagonal
Mobius pair correlation alone.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators ComplexConjugate

namespace RHLean.Proof

/-- Diagonal part of a finite lifetime overlap Gram. -/
def lifetimeOverlapDiagonalGram
    (U : Finset CanonicalSourceAtom)
    (w : CanonicalSourceAtom → ℂ)
    (Λ : ℝ) (N H : ℕ) : ℂ :=
  ∑ p ∈ U,
    conj (w p) * w p * lifetimeOverlapKernel Λ N H p p

/-- Off-diagonal part, defined by exact subtraction from the full Gram. -/
def lifetimeOverlapOffDiagonalGram
    (U : Finset CanonicalSourceAtom)
    (w : CanonicalSourceAtom → ℂ)
    (Λ : ℝ) (N H : ℕ) : ℂ :=
  lifetimeOverlapGram U w Λ N H - lifetimeOverlapDiagonalGram U w Λ N H

/-- Exact diagonal/off-diagonal decomposition. -/
theorem lifetimeOverlapGram_eq_diagonal_add_offDiagonal
    (U : Finset CanonicalSourceAtom)
    (w : CanonicalSourceAtom → ℂ)
    (Λ : ℝ) (N H : ℕ) :
    lifetimeOverlapGram U w Λ N H =
      lifetimeOverlapDiagonalGram U w Λ N H +
        lifetimeOverlapOffDiagonalGram U w Λ N H := by
  unfold lifetimeOverlapOffDiagonalGram
  ring

/-- Canonical fixed-terminal diagonal Gram for one translated window. -/
def canonicalLifetimeOverlapDiagonalGram (Λ : ℝ) (N H : ℕ) : ℂ :=
  lifetimeOverlapDiagonalGram (canonicalLifetimeUniverse Λ (N + H))
    canonicalHighAtomWeight Λ N H

/-- Canonical fixed-terminal off-diagonal Gram for one translated window. -/
def canonicalLifetimeOverlapOffDiagonalGram (Λ : ℝ) (N H : ℕ) : ℂ :=
  lifetimeOverlapOffDiagonalGram (canonicalLifetimeUniverse Λ (N + H))
    canonicalHighAtomWeight Λ N H

private theorem card_canonicalSquareBlock (j : ℕ) :
    (canonicalSquareBlock j).card = 2 * j + 1 := by
  unfold canonicalSquareBlock
  rw [Nat.card_Ico]
  have hsq : (j + 1) ^ 2 = j ^ 2 + (2 * j + 1) := by ring
  rw [hsq]
  omega

private theorem sum_two_mul_add_one (n : ℕ) :
    (∑ j ∈ Finset.range n, (2 * j + 1)) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- The terminal birth-high universe is a filtered union of disjoint square
blocks, hence has at most `(T+1)^2` atoms. -/
theorem card_birthCanonicalHighAtomSet_le_square
    (Λ : ℝ) (T : ℕ) :
    (birthCanonicalHighAtomSet Λ T).card ≤ (T + 1) ^ 2 := by
  classical
  unfold birthCanonicalHighAtomSet
  rw [Finset.card_sigma]
  calc
    (∑ j ∈ Finset.range (T + 1),
        ((canonicalSquareBlock j).filter
          (fun m => IsCanonicalHighHeight Λ j m)).card) ≤
      ∑ j ∈ Finset.range (T + 1), (canonicalSquareBlock j).card := by
        apply Finset.sum_le_sum
        intro j _hj
        exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = ∑ j ∈ Finset.range (T + 1), (2 * j + 1) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [card_canonicalSquareBlock]
    _ = (T + 1) ^ 2 := sum_two_mul_add_one (T + 1)

private theorem norm_canonicalHighAtomWeight_le_one
    (p : CanonicalSourceAtom) :
    ‖canonicalHighAtomWeight p‖ ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or p.2 with h | h | h <;>
    simp [canonicalHighAtomWeight, canonicalMoebiusWeight, h]

private theorem norm_lifetimeOverlapKernel_self_le
    (Λ : ℝ) (N H : ℕ) (p : CanonicalSourceAtom) :
    ‖lifetimeOverlapKernel Λ N H p p‖ ≤ (H : ℝ) := by
  rw [lifetimeOverlapKernel_self]
  calc
    ‖∑ h ∈ Finset.range H,
        if IsLifetimeActive Λ p (N + h) then (1 : ℂ) else 0‖ ≤
      ∑ h ∈ Finset.range H,
        ‖if IsLifetimeActive Λ p (N + h) then (1 : ℂ) else 0‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ _h ∈ Finset.range H, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro h _hh
      by_cases hp : IsLifetimeActive Λ p (N + h) <;> simp [hp]
    _ = (H : ℝ) := by simp

private theorem norm_canonical_diagonal_term_le
    (Λ : ℝ) (N H : ℕ) (p : CanonicalSourceAtom) :
    ‖conj (canonicalHighAtomWeight p) * canonicalHighAtomWeight p *
        lifetimeOverlapKernel Λ N H p p‖ ≤ (H : ℝ) := by
  have hw := norm_canonicalHighAtomWeight_le_one p
  have hw0 : 0 ≤ ‖canonicalHighAtomWeight p‖ := norm_nonneg _
  have hw2 : ‖canonicalHighAtomWeight p‖ * ‖canonicalHighAtomWeight p‖ ≤ 1 := by
    nlinarith
  have hk := norm_lifetimeOverlapKernel_self_le Λ N H p
  calc
    ‖conj (canonicalHighAtomWeight p) * canonicalHighAtomWeight p *
        lifetimeOverlapKernel Λ N H p p‖ =
      (‖canonicalHighAtomWeight p‖ * ‖canonicalHighAtomWeight p‖) *
        ‖lifetimeOverlapKernel Λ N H p p‖ := by
          simp
    _ ≤ 1 * ‖lifetimeOverlapKernel Λ N H p p‖ :=
      mul_le_mul_of_nonneg_right hw2 (norm_nonneg _)
    _ ≤ (H : ℝ) := by simpa using hk

/-- Raw deterministic diagonal bound by terminal source population times window
length. -/
theorem norm_canonicalLifetimeOverlapDiagonalGram_le
    (Λ : ℝ) (N H : ℕ) :
    ‖canonicalLifetimeOverlapDiagonalGram Λ N H‖ ≤
      ((((N + H + 1) ^ 2 : ℕ) : ℝ)) * (H : ℝ) := by
  let U := canonicalLifetimeUniverse Λ (N + H)
  have hcardNat : U.card ≤ (N + H + 1) ^ 2 := by
    simpa [U, canonicalLifetimeUniverse] using
      card_birthCanonicalHighAtomSet_le_square Λ (N + H)
  have hcard : (U.card : ℝ) ≤ ((((N + H + 1) ^ 2 : ℕ) : ℝ)) := by
    exact_mod_cast hcardNat
  unfold canonicalLifetimeOverlapDiagonalGram lifetimeOverlapDiagonalGram
  change ‖∑ p ∈ U,
      conj (canonicalHighAtomWeight p) * canonicalHighAtomWeight p *
        lifetimeOverlapKernel Λ N H p p‖ ≤ _
  calc
    ‖∑ p ∈ U,
        conj (canonicalHighAtomWeight p) * canonicalHighAtomWeight p *
          lifetimeOverlapKernel Λ N H p p‖ ≤
      ∑ p ∈ U,
        ‖conj (canonicalHighAtomWeight p) * canonicalHighAtomWeight p *
          lifetimeOverlapKernel Λ N H p p‖ := by
            exact norm_sum_le _ _
    _ ≤ ∑ _p ∈ U, (H : ℝ) := by
      apply Finset.sum_le_sum
      intro p _hp
      exact norm_canonical_diagonal_term_le Λ N H p
    _ = (U.card : ℝ) * (H : ℝ) := by simp
    _ ≤ ((((N + H + 1) ^ 2 : ℕ) : ℝ)) * (H : ℝ) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)

/-- On translated windows `1 <= H <= N`, the diagonal is already at critical
scale, uniformly in the positive epsilon. -/
theorem canonicalLifetimeOverlapDiagonalGram_critical
    {Λ ε : ℝ} (hε : 0 < ε)
    {N H : ℕ} (hH : 1 ≤ H) (hHN : H ≤ N) :
    ‖canonicalLifetimeOverlapDiagonalGram Λ N H‖ ≤
      9 * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε) := by
  have hN : 1 ≤ N := hH.trans hHN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsumNat : N + H + 1 ≤ 3 * N := by omega
  have hsum : ((N + H + 1 : ℕ) : ℝ) ≤ 3 * (N : ℝ) := by
    exact_mod_cast hsumNat
  have hsq : (((N + H + 1 : ℕ) : ℝ)) ^ 2 ≤ 9 * (N : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (3 * (N : ℝ) - (N + H + 1 : ℕ))]
  have hpowEps : (1 : ℝ) ≤ Real.rpow (N : ℝ) ε :=
    Real.one_le_rpow hN1 hε.le
  have hrpow :
      Real.rpow (N : ℝ) (2 + ε) =
        (N : ℝ) ^ 2 * Real.rpow (N : ℝ) ε := by
    calc
      Real.rpow (N : ℝ) (2 + ε) =
          Real.rpow (N : ℝ) 2 * Real.rpow (N : ℝ) ε :=
        Real.rpow_add hNpos 2 ε
      _ = (N : ℝ) ^ 2 * Real.rpow (N : ℝ) ε := by norm_num
  have hN2 : (N : ℝ) ^ 2 ≤ Real.rpow (N : ℝ) (2 + ε) := by
    rw [hrpow]
    nlinarith [sq_nonneg (N : ℝ)]
  have hraw := norm_canonicalLifetimeOverlapDiagonalGram_le Λ N H
  have hcast : ((((N + H + 1) ^ 2 : ℕ) : ℝ)) =
      (((N + H + 1 : ℕ) : ℝ)) ^ 2 := by push_cast; ring
  rw [hcast] at hraw
  calc
    ‖canonicalLifetimeOverlapDiagonalGram Λ N H‖ ≤
        (((N + H + 1 : ℕ) : ℝ)) ^ 2 * (H : ℝ) := hraw
    _ ≤ (9 * (N : ℝ) ^ 2) * (H : ℝ) :=
      mul_le_mul_of_nonneg_right hsq (by positivity)
    _ ≤ (9 * Real.rpow (N : ℝ) (2 + ε)) * (H : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hN2 (by norm_num)) (by positivity)
    _ = 9 * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε) := by ring

/-- Critical translated-window bound for only the off-diagonal lifetime pair
correlation. -/
def LifetimeOffDiagonalGramUniformLocalBoundedStatement (Λ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N H : ℕ),
        1 ≤ H → H ≤ N →
        ‖canonicalLifetimeOverlapOffDiagonalGram Λ N H‖ ≤
          C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

/-- The full overlap-Gram criterion implies the off-diagonal criterion because
the diagonal is already critical. -/
theorem lifetimeOffDiagonalGramUniformLocalBounded_of_overlapGram
    {Λ : ℝ} (hG : LifetimeOverlapGramUniformLocalBoundedStatement Λ) :
    LifetimeOffDiagonalGramUniformLocalBoundedStatement Λ := by
  intro ε hε
  obtain ⟨C, hC, hGb⟩ := hG ε hε
  refine ⟨C + 9, by linarith, ?_⟩
  intro N H hH hHN
  have hfull := hGb N H hH hHN
  have hdiag := canonicalLifetimeOverlapDiagonalGram_critical
    (Λ := Λ) hε hH hHN
  unfold canonicalLifetimeOverlapOffDiagonalGram lifetimeOverlapOffDiagonalGram
  calc
    ‖lifetimeOverlapGram (canonicalLifetimeUniverse Λ (N + H))
          canonicalHighAtomWeight Λ N H -
        canonicalLifetimeOverlapDiagonalGram Λ N H‖ ≤
      ‖lifetimeOverlapGram (canonicalLifetimeUniverse Λ (N + H))
          canonicalHighAtomWeight Λ N H‖ +
        ‖canonicalLifetimeOverlapDiagonalGram Λ N H‖ := norm_sub_le _ _
    _ ≤ C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε) +
        9 * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε) :=
      add_le_add hfull hdiag
    _ = (C + 9) * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε) := by ring

/-- Conversely, controlling only off-diagonal pairs controls the full overlap
Gram, again because the diagonal is deterministic. -/
theorem lifetimeOverlapGramUniformLocalBounded_of_offDiagonal
    {Λ : ℝ} (hO : LifetimeOffDiagonalGramUniformLocalBoundedStatement Λ) :
    LifetimeOverlapGramUniformLocalBoundedStatement Λ := by
  intro ε hε
  obtain ⟨C, hC, hOb⟩ := hO ε hε
  refine ⟨C + 9, by linarith, ?_⟩
  intro N H hH hHN
  have hoff := hOb N H hH hHN
  have hdiag := canonicalLifetimeOverlapDiagonalGram_critical
    (Λ := Λ) hε hH hHN
  rw [lifetimeOverlapGram_eq_diagonal_add_offDiagonal]
  calc
    ‖lifetimeOverlapDiagonalGram (canonicalLifetimeUniverse Λ (N + H))
          canonicalHighAtomWeight Λ N H +
        lifetimeOverlapOffDiagonalGram (canonicalLifetimeUniverse Λ (N + H))
          canonicalHighAtomWeight Λ N H‖ ≤
      ‖canonicalLifetimeOverlapDiagonalGram Λ N H‖ +
        ‖canonicalLifetimeOverlapOffDiagonalGram Λ N H‖ := norm_add_le _ _
    _ ≤ 9 * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε) +
        C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε) :=
      add_le_add hdiag hoff
    _ = (C + 9) * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε) := by ring

/-- Exact analytic reduction: only off-diagonal lifetime correlations remain. -/
theorem lifetimeOffDiagonalGramUniformLocalBounded_iff_overlapGram
    (Λ : ℝ) :
    LifetimeOffDiagonalGramUniformLocalBoundedStatement Λ ↔
      LifetimeOverlapGramUniformLocalBoundedStatement Λ := by
  constructor
  · exact lifetimeOverlapGramUniformLocalBounded_of_offDiagonal
  · exact lifetimeOffDiagonalGramUniformLocalBounded_of_overlapGram

/-- Conditional RH terminal with the lifetime frontier reduced entirely to the
off-diagonal Mobius overlap Gram. -/
theorem lifetimeOffDiagonalGramUniformLocalBounded_implies_riemannHypothesis
    {Λ : ℝ} (hΛ : 0 < Λ)
    (criterion : RHLean.Analysis.ClassicalMertensRHCriterion)
    (hO : LifetimeOffDiagonalGramUniformLocalBoundedStatement Λ) :
    RHLean.Analysis.RiemannHypothesisStatement := by
  apply lifetimeOverlapGramUniformLocalBounded_implies_riemannHypothesis hΛ criterion
  exact (lifetimeOffDiagonalGramUniformLocalBounded_iff_overlapGram Λ).1 hO

end RHLean.Proof

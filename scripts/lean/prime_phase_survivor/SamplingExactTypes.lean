import «research.PRIME_PHASE_EXCEPTIONAL_SAMPLING_20261117»

set_option autoImplicit false
open RHLean.Analysis.PrimePhaseSampling

example {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (B : Finset ι) (E : Finset κ) (U : ι → Finset κ) (m : ℕ)
    (hcontained : ∀ r ∈ B, U r ⊆ E)
    (hdisjoint : ∀ r ∈ B, ∀ s ∈ B, r ≠ s → Disjoint (U r) (U s))
    (hsize : ∀ r ∈ B, m ≤ (U r).card) :
    m * B.card ≤ E.card :=
  exceptional_root_card_packing B E U m hcontained hdisjoint hsize

example {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (B : Finset ι) (E : Finset κ) (U : ι → Finset κ) (Y c C ε : ℝ)
    (hY : 0 < Y) (hc : 0 < c)
    (hcontained : ∀ r ∈ B, U r ⊆ E)
    (hdisjoint : ∀ r ∈ B, ∀ s ∈ B, r ≠ s → Disjoint (U r) (U s))
    (hsize : ∀ r ∈ B, c * Y ≤ ((U r).card : ℝ))
    (hbudget : (E.card : ℝ) ≤ C * Real.rpow Y ((3 : ℝ) / 2 + ε)) :
    (B.card : ℝ) ≤ (C / c) * Real.rpow Y ((1 : ℝ) / 2 + ε) :=
  exceptional_root_card_le_rpow_of_persistent_neighborhoods
    B E U Y c C ε hY hc hcontained hdisjoint hsize hbudget

example {R S w v : ℕ} (hRS : R < S) (hw : w ≤ 2 * R + 1) :
    Disjoint (squareSamplingNeighborhood R w) (squareSamplingNeighborhood S v) :=
  squareSamplingNeighborhood_disjoint_of_lt hRS hw

example (B E : Finset ℕ) (w : ℕ)
    (hw : ∀ R ∈ B, w ≤ 2 * R + 1)
    (hpersistence : ∀ R ∈ B, squareSamplingNeighborhood R w ⊆ E) :
    w * B.card ≤ E.card :=
  square_exceptional_root_card_packing B E w hw hpersistence

example (W : Finset ℕ) (hW : ∀ n ∈ W, 2 ≤ n) :
    ordinaryPrimeCount W + ordinaryCompositeCount W = W.card :=
  ordinary_prime_add_composite_count W hW

example (W : Finset ℕ) (hW : ∀ n ∈ W, 2 ≤ n) (P : ℝ) :
    |(ordinaryCompositeCount W : ℝ) - ((W.card : ℝ) - P)| =
      |(ordinaryPrimeCount W : ℝ) - P| :=
  ordinary_composite_abs_discrepancy_eq_prime W hW P

example (W I : Finset ℕ) (hW : ∀ n ∈ W, 2 ≤ n) (hI : I ⊆ W) (α : ℝ) :
    (ordinaryCompositeCount I : ℝ) - α * (ordinaryCompositeCount W : ℝ) =
      ((I.card : ℝ) - α * (W.card : ℝ)) -
        ((ordinaryPrimeCount I : ℝ) - α * (ordinaryPrimeCount W : ℝ)) :=
  ordinary_composite_phase_discrepancy W I hW hI α

#print exceptional_root_card_packing
#print exceptional_root_card_le_rpow_of_persistent_neighborhoods
#print square_exceptional_root_card_packing
#print ordinary_composite_phase_discrepancy

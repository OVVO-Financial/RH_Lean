import Mathlib

/-!
# Finite exceptional-set sampling and ordinary prime/composite accounting

The almost-every-square-block argument needs a sampling step: a bad sampled
root must own a sufficiently large neighborhood of bad starting points, and
the neighborhoods must not overlap.  The finite injection below proves that
step without asserting the analytic persistence or exceptional-set bounds.
It also records the exact square-spacing geometry and the resulting exponent
conversion when those quantitative inputs are supplied.

The ordinary composite-count identities are kept separate from the repository's
signed canonical death process.  They say exactly which integer-window error
must be retained when a prime discrepancy is replaced by a composite one.

No prime-distribution hypothesis is introduced as an axiom.  In particular,
this file does not prove Harman's theorem, a zero-density estimate, or a new
survivor/Mertens bound.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis.PrimePhaseSampling

/-- Disjoint neighborhoods contained in the bad sample set give a finite
injection from all root/neighborhood pairs into that sample set. -/
theorem sum_neighborhood_card_le_badSamples_card
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (badRoots : Finset ι) (badSamples : Finset κ)
    (neighborhood : ι → Finset κ)
    (hcontained : ∀ r ∈ badRoots, neighborhood r ⊆ badSamples)
    (hdisjoint : ∀ r ∈ badRoots, ∀ s ∈ badRoots, r ≠ s →
      Disjoint (neighborhood r) (neighborhood s)) :
    (∑ r ∈ badRoots, (neighborhood r).card) ≤ badSamples.card := by
  have hmaps : Set.MapsTo (fun a : Σ _ : ι, κ => a.2)
      (badRoots.sigma neighborhood) badSamples := by
    intro a ha
    obtain ⟨hr, hx⟩ := Finset.mem_sigma.mp ha
    exact hcontained a.1 hr hx
  have hinj : Set.InjOn (fun a : Σ _ : ι, κ => a.2)
      (badRoots.sigma neighborhood) := by
    rintro ⟨r, x⟩ ha ⟨s, y⟩ hb hxy
    obtain ⟨hr, hx⟩ := Finset.mem_sigma.mp ha
    obtain ⟨hs, hy⟩ := Finset.mem_sigma.mp hb
    change x = y at hxy
    have hrs : r = s := by
      by_contra hne
      exact (Finset.disjoint_left.mp (hdisjoint r hr s hs hne))
        hx (hxy.symm ▸ hy)
    subst s
    subst y
    rfl
  have hcard := Finset.card_le_card_of_injOn
    (s := badRoots.sigma neighborhood) (t := badSamples)
    (fun a : Σ _ : ι, κ => a.2) hmaps hinj
  simpa only [Finset.card_sigma] using hcard

/-- If each exceptional root owns at least `m` distinct bad sample points,
their disjointness charges `m` points to every root. -/
theorem exceptional_root_card_packing
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (badRoots : Finset ι) (badSamples : Finset κ)
    (neighborhood : ι → Finset κ) (m : ℕ)
    (hcontained : ∀ r ∈ badRoots, neighborhood r ⊆ badSamples)
    (hdisjoint : ∀ r ∈ badRoots, ∀ s ∈ badRoots, r ≠ s →
      Disjoint (neighborhood r) (neighborhood s))
    (hsize : ∀ r ∈ badRoots, m ≤ (neighborhood r).card) :
    m * badRoots.card ≤ badSamples.card := by
  calc
    m * badRoots.card = ∑ _r ∈ badRoots, m := by simp [Nat.mul_comm]
    _ ≤ ∑ r ∈ badRoots, (neighborhood r).card :=
      Finset.sum_le_sum hsize
    _ ≤ badSamples.card :=
      sum_neighborhood_card_le_badSamples_card
        badRoots badSamples neighborhood hcontained hdisjoint

/-- Real-valued neighborhood-size bounds avoid an artificial rounding loss
when the analytic persistence scale is a real multiple of the root scale. -/
theorem exceptional_root_real_card_packing
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (badRoots : Finset ι) (badSamples : Finset κ)
    (neighborhood : ι → Finset κ) (w : ℝ)
    (hcontained : ∀ r ∈ badRoots, neighborhood r ⊆ badSamples)
    (hdisjoint : ∀ r ∈ badRoots, ∀ s ∈ badRoots, r ≠ s →
      Disjoint (neighborhood r) (neighborhood s))
    (hsize : ∀ r ∈ badRoots, w ≤ ((neighborhood r).card : ℝ)) :
    w * (badRoots.card : ℝ) ≤ (badSamples.card : ℝ) := by
  have hcard := sum_neighborhood_card_le_badSamples_card
    badRoots badSamples neighborhood hcontained hdisjoint
  have hcardReal :
      (∑ r ∈ badRoots, ((neighborhood r).card : ℝ)) ≤
        (badSamples.card : ℝ) := by
    exact_mod_cast hcard
  calc
    w * (badRoots.card : ℝ) = ∑ _r ∈ badRoots, w := by
      simp [nsmul_eq_mul, mul_comm]
    _ ≤ ∑ r ∈ badRoots, ((neighborhood r).card : ℝ) :=
      Finset.sum_le_sum hsize
    _ ≤ (badSamples.card : ℝ) := hcardReal

/-- The discrete exceptional-set exponent conversion at square scale.
The neighborhood and bad-sample estimates are explicit inputs; this is not
a proof of those analytic estimates for primes. -/
theorem exceptional_root_card_le_rpow_of_persistent_neighborhoods
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (badRoots : Finset ι) (badSamples : Finset κ)
    (neighborhood : ι → Finset κ) (Y c C ε : ℝ)
    (hY : 0 < Y) (hc : 0 < c)
    (hcontained : ∀ r ∈ badRoots, neighborhood r ⊆ badSamples)
    (hdisjoint : ∀ r ∈ badRoots, ∀ s ∈ badRoots, r ≠ s →
      Disjoint (neighborhood r) (neighborhood s))
    (hsize : ∀ r ∈ badRoots,
      c * Y ≤ ((neighborhood r).card : ℝ))
    (hbudget : (badSamples.card : ℝ) ≤
      C * Real.rpow Y ((3 : ℝ) / 2 + ε)) :
    (badRoots.card : ℝ) ≤ (C / c) * Real.rpow Y ((1 : ℝ) / 2 + ε) := by
  have hpacking := exceptional_root_real_card_packing
    badRoots badSamples neighborhood (c * Y) hcontained hdisjoint hsize
  have hpower : Real.rpow Y ((3 : ℝ) / 2 + ε) =
      Y * Real.rpow Y ((1 : ℝ) / 2 + ε) := by
    have hYone : Real.rpow Y 1 = Y := Real.rpow_one Y
    calc
      Real.rpow Y ((3 : ℝ) / 2 + ε) =
          Real.rpow Y (1 + ((1 : ℝ) / 2 + ε)) := by
        congr 1
        ring
      _ = Real.rpow Y 1 * Real.rpow Y ((1 : ℝ) / 2 + ε) :=
        Real.rpow_add hY 1 ((1 : ℝ) / 2 + ε)
      _ = Y * Real.rpow Y ((1 : ℝ) / 2 + ε) := by rw [hYone]
  have hscaled :
      (c * Y) * (badRoots.card : ℝ) ≤
        (c * Y) * ((C / c) * Real.rpow Y ((1 : ℝ) / 2 + ε)) := by
    calc
      (c * Y) * (badRoots.card : ℝ) ≤
          C * Real.rpow Y ((3 : ℝ) / 2 + ε) := hpacking.trans hbudget
      _ = (c * Y) * ((C / c) * Real.rpow Y ((1 : ℝ) / 2 + ε)) := by
        rw [hpower]
        field_simp [ne_of_gt hc] <;> ring
  exact le_of_mul_le_mul_left hscaled (mul_pos hc hY)

/-- A one-sided integer neighborhood beginning at an actual square. -/
def squareSamplingNeighborhood (R width : ℕ) : Finset ℕ :=
  Finset.Ico (R ^ 2) (R ^ 2 + width)

/-- The neighborhood has its stated width exactly. -/
theorem squareSamplingNeighborhood_card (R width : ℕ) :
    (squareSamplingNeighborhood R width).card = width := by
  simp [squareSamplingNeighborhood]

/-- A neighborhood that fits before the next square cannot intersect a
neighborhood beginning at any later square. -/
theorem squareSamplingNeighborhood_disjoint_of_lt
    {R S widthR widthS : ℕ} (hRS : R < S)
    (hwidth : widthR ≤ 2 * R + 1) :
    Disjoint (squareSamplingNeighborhood R widthR)
      (squareSamplingNeighborhood S widthS) := by
  apply Finset.disjoint_left.mpr
  intro n hnR hnS
  obtain ⟨_hnRlo, hnRhi⟩ := Finset.mem_Ico.mp hnR
  obtain ⟨hnSlo, _hnShi⟩ := Finset.mem_Ico.mp hnS
  have hstep : R + 1 ≤ S := by omega
  have hsq : (R + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hstep 2
  have hfit : R ^ 2 + widthR ≤ (R + 1) ^ 2 := by nlinarith
  omega

/-- For actual square samples, the disjointness input is supplied by square
spacing; only the assertion that the neighborhoods are bad remains an input. -/
theorem square_exceptional_root_card_packing
    (badRoots badSamples : Finset ℕ) (width : ℕ)
    (hwidth : ∀ R ∈ badRoots, width ≤ 2 * R + 1)
    (hpersistence : ∀ R ∈ badRoots,
      squareSamplingNeighborhood R width ⊆ badSamples) :
    width * badRoots.card ≤ badSamples.card := by
  apply exceptional_root_card_packing badRoots badSamples
    (fun R => squareSamplingNeighborhood R width) width hpersistence
  · intro R hR S hS hne
    by_cases hRS : R < S
    · exact squareSamplingNeighborhood_disjoint_of_lt hRS (hwidth R hR)
    · have hSR : S < R := by omega
      exact (squareSamplingNeighborhood_disjoint_of_lt hSR (hwidth S hS)).symm
  · intro R _hR
    exact (squareSamplingNeighborhood_card R width).ge

/-- Ordinary prime count in a finite integer window. -/
def ordinaryPrimeCount (window : Finset ℕ) : ℕ :=
  (window.filter Nat.Prime).card

/-- Ordinary composite count; zero and one are explicitly excluded. -/
def ordinaryCompositeCount (window : Finset ℕ) : ℕ :=
  (window.filter fun n => 2 ≤ n ∧ ¬ Nat.Prime n).card

/-- On a window of integers at least two, prime and composite populations
partition the whole window exactly. -/
theorem ordinary_prime_add_composite_count
    (window : Finset ℕ) (hwindow : ∀ n ∈ window, 2 ≤ n) :
    ordinaryPrimeCount window + ordinaryCompositeCount window = window.card := by
  have hfilter :
      window.filter (fun n => 2 ≤ n ∧ ¬ Nat.Prime n) =
        window.filter (fun n => ¬ Nat.Prime n) := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hn, _hge, hnp⟩
      exact ⟨hn, hnp⟩
    · rintro ⟨hn, hnp⟩
      exact ⟨hn, hwindow n hn, hnp⟩
  unfold ordinaryPrimeCount ordinaryCompositeCount
  rw [hfilter]
  simpa using Finset.sum_filter_add_sum_filter_not
    window Nat.Prime (fun _ => (1 : ℕ))

/-- With complementary expected counts, the ordinary composite error is
exactly the negative prime error. -/
theorem ordinary_composite_discrepancy_eq_neg_prime
    (window : Finset ℕ) (hwindow : ∀ n ∈ window, 2 ≤ n)
    (expectedPrimes : ℝ) :
    (ordinaryCompositeCount window : ℝ) -
        ((window.card : ℝ) - expectedPrimes) =
      -((ordinaryPrimeCount window : ℝ) - expectedPrimes) := by
  have hcount :
      (ordinaryPrimeCount window : ℝ) + (ordinaryCompositeCount window : ℝ) =
        (window.card : ℝ) := by
    exact_mod_cast ordinary_prime_add_composite_count window hwindow
  linarith

/-- At matched precision the absolute errors coincide, so ordinary composite
counting gives no automatic improvement in the prime discrepancy. -/
theorem ordinary_composite_abs_discrepancy_eq_prime
    (window : Finset ℕ) (hwindow : ∀ n ∈ window, 2 ≤ n)
    (expectedPrimes : ℝ) :
    |(ordinaryCompositeCount window : ℝ) -
        ((window.card : ℝ) - expectedPrimes)| =
      |(ordinaryPrimeCount window : ℝ) - expectedPrimes| := by
  rw [ordinary_composite_discrepancy_eq_neg_prime window hwindow expectedPrimes,
    abs_neg]

/-- Phase discrepancies retain the integer-window discrepancy as well as the
oppositely signed prime discrepancy.  No rounding error is discarded. -/
theorem ordinary_composite_phase_discrepancy
    (window phaseWindow : Finset ℕ)
    (hwindow : ∀ n ∈ window, 2 ≤ n) (hsub : phaseWindow ⊆ window)
    (α : ℝ) :
    (ordinaryCompositeCount phaseWindow : ℝ) -
        α * (ordinaryCompositeCount window : ℝ) =
      ((phaseWindow.card : ℝ) - α * (window.card : ℝ)) -
        ((ordinaryPrimeCount phaseWindow : ℝ) -
          α * (ordinaryPrimeCount window : ℝ)) := by
  have hwhole :
      (ordinaryPrimeCount window : ℝ) + (ordinaryCompositeCount window : ℝ) =
        (window.card : ℝ) := by
    exact_mod_cast ordinary_prime_add_composite_count window hwindow
  have hphase :
      (ordinaryPrimeCount phaseWindow : ℝ) +
        (ordinaryCompositeCount phaseWindow : ℝ) = (phaseWindow.card : ℝ) := by
    exact_mod_cast ordinary_prime_add_composite_count phaseWindow
      (fun n hn => hwindow n (hsub hn))
  linear_combination hphase - α * hwhole

end RHLean.Analysis.PrimePhaseSampling

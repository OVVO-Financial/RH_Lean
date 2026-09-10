import Mathlib
import RHLean.Proof.SquareRootLowPrimeTSectorQ2Renormalization
import RHLean.Proof.SquareRootLowPrimeGoWallStripTelescope
import RHLean.Proof.LowWheelFrozenSecondContactScaleFlux

/-!
# The physical owner schedule is primorial-thresholded

The `4/3` frame target of #634 spends a *global* prime reciprocal-square budget:
`1` for every prime owner, or `1/2` after an odd telescope.  That budget is far
too pessimistic for the carrier the Go recursion actually uses.

A second-contact owner `q` is live at root `R` only if it carries a squarefree
core `c` with every prime factor below `q` and `c > R`.  Such a core divides the
predecessor primorial `∏_{p<q} p`, so

```text
live owner at R  ⟹  R < ∏_{p<q} p.
```

Small owners are therefore not merely rare, they are absent: `2`, `3` and `5`
are never live for `R ≥ 6`, `7` is never live for `R ≥ 30`, `11` is never live
for `R ≥ 210`, and the threshold marches to infinity with `R`.  The dual
statement holds on the daughter ledger: once the square-dilated cutoff reaches
the predecessor primorial the Boolean cube of `q`-smooth faces is complete, so
that daughter is *exactly* zero rather than merely small.

What is proved here, on the exact repository carriers:

* the daughter `squareRootLowPrimeGoWallSquareResidual q X` vanishes identically
  as soon as `∏_{p<q} p ≤ X / q^2`;
* every owner of a saturated #629 second-contact seed satisfies
  `R < ∏_{p<q} p`, hence `q ≥ 7` for `R ≥ 6`, `q ≥ 11` for `R ≥ 30`, and
  `q ≥ 13` for `R ≥ 210`;
* the owner reciprocal-square budget is therefore at most `1/12` uniformly and
  at most `1/20` beyond `R = 30`, against the `1/2` available to the complete
  prime schedule;
* consequently a frame loss of `12` uniformly, of `20` beyond `R = 30`, and in
  fact *any* prescribed frame loss beyond an explicit primorial root threshold,
  still closes the same linear energy induction, with envelope
  `E(X) ≤ (6348/143)*B*X`;
* and, with the owner weight `q` retained through the descent, the purely
  diagonal route — each owner column dominated by its own contracted daughter
  energy, no cross-owner cancellation of any kind — already closes whenever the
  owner harmonic sum `∑_{q} 1/q` stays at most one.

None of this proves a frame inequality on the reduced #643 physical packet,
identifies that packet with the recovered Mertens degree-one energy, or closes
RH.  What changes is the size of the target: the quantitative room available to
a Schur, Cotlar or Carleson argument on this carrier is an order of magnitude
larger than `4/3`, it grows with the root, and the elementary diagonal route is
separated from closure by the growth of a single harmonic sum.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic
open CanonicalGapAncestryBridge

/-! ## The predecessor primorial -/

/-- Product of every prime strictly below `q`. -/
def predecessorPrimorial (q : ℕ) : ℕ := primeFaceProduct (primesUpTo (q - 1))

theorem mem_primesUpTo_pred_iff {q p : ℕ} :
    p ∈ primesUpTo (q - 1) ↔ p.Prime ∧ p < q := by
  rw [mem_primesUpTo]
  constructor
  · rintro ⟨hp, hle⟩
    have h2 := hp.two_le
    exact ⟨hp, by omega⟩
  · rintro ⟨hp, hlt⟩
    exact ⟨hp, by omega⟩

theorem predecessorPrimorial_pos (q : ℕ) : 0 < predecessorPrimorial q := by
  unfold predecessorPrimorial primeFaceProduct
  apply Finset.prod_pos
  intro p hp
  exact (mem_primesUpTo_pred_iff.mp hp).1.pos

theorem predecessorPrimorial_mono {q Q : ℕ} (hq : q ≤ Q) :
    predecessorPrimorial q ≤ predecessorPrimorial Q := by
  unfold predecessorPrimorial primeFaceProduct
  apply Finset.prod_le_prod_of_subset_of_one_le'
  · intro p hp
    rcases mem_primesUpTo_pred_iff.mp hp with ⟨hpPrime, hplt⟩
    exact mem_primesUpTo_pred_iff.mpr ⟨hpPrime, by omega⟩
  · intro p hp _
    exact (mem_primesUpTo_pred_iff.mp hp).1.one_lt.le

/-- A squarefree number whose prime factors all lie below `q` divides the
predecessor primorial.  This is the whole arithmetic input of the module. -/
theorem squarefree_below_dvd_predecessorPrimorial
    {q c : ℕ} (hc : Squarefree c)
    (hbelow : ∀ p : ℕ, p.Prime → p ∣ c → p < q) :
    c ∣ predecessorPrimorial q := by
  have hsub : c.primeFactors ⊆ primesUpTo (q - 1) := by
    intro p hp
    rcases Nat.mem_primeFactors.mp hp with ⟨hpPrime, hpDvd, _⟩
    exact mem_primesUpTo_pred_iff.mpr ⟨hpPrime, hbelow p hpPrime hpDvd⟩
  have hprod : ∏ p ∈ c.primeFactors, p = c :=
    Nat.prod_primeFactors_of_squarefree hc
  calc
    c = ∏ p ∈ c.primeFactors, p := hprod.symm
    _ ∣ predecessorPrimorial q := by
        unfold predecessorPrimorial primeFaceProduct
        exact Finset.prod_dvd_prod_of_subset _ _ id hsub

theorem squarefree_below_le_predecessorPrimorial
    {q c : ℕ} (hc : Squarefree c)
    (hbelow : ∀ p : ℕ, p.Prime → p ∣ c → p < q) :
    c ≤ predecessorPrimorial q :=
  Nat.le_of_dvd (predecessorPrimorial_pos q)
    (squarefree_below_dvd_predecessorPrimorial hc hbelow)

/-! ### Explicit small primorials -/

theorem primesUpTo_four : primesUpTo 4 = ({2, 3} : Finset ℕ) := by
  ext q
  rw [mem_primesUpTo, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hqPrime, hqle⟩
    have h2 := hqPrime.two_le
    interval_cases q
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hqPrime (by norm_num)
  · rintro (rfl | rfl)
    · exact ⟨Nat.prime_two, by norm_num⟩
    · exact ⟨Nat.prime_three, by norm_num⟩

theorem primesUpTo_six : primesUpTo 6 = ({2, 3, 5} : Finset ℕ) := by
  ext q
  rw [mem_primesUpTo, Finset.mem_insert, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hqPrime, hqle⟩
    have h2 := hqPrime.two_le
    interval_cases q
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact absurd hqPrime (by norm_num)
    · exact Or.inr (Or.inr rfl)
    · exact absurd hqPrime (by norm_num)
  · rintro (rfl | rfl | rfl)
    · exact ⟨Nat.prime_two, by norm_num⟩
    · exact ⟨Nat.prime_three, by norm_num⟩
    · exact ⟨by norm_num, by norm_num⟩

theorem primesUpTo_ten : primesUpTo 10 = ({2, 3, 5, 7} : Finset ℕ) := by
  ext q
  rw [mem_primesUpTo, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hqPrime, hqle⟩
    have h2 := hqPrime.two_le
    interval_cases q
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact absurd hqPrime (by norm_num)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact absurd hqPrime (by norm_num)
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact absurd hqPrime (by norm_num)
    · exact absurd hqPrime (by norm_num)
    · exact absurd hqPrime (by norm_num)
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨Nat.prime_two, by norm_num⟩
    · exact ⟨Nat.prime_three, by norm_num⟩
    · exact ⟨by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num⟩

theorem predecessorPrimorial_five : predecessorPrimorial 5 = 6 := by
  have h : primesUpTo (5 - 1) = ({2, 3} : Finset ℕ) := by
    norm_num [primesUpTo_four]
  unfold predecessorPrimorial primeFaceProduct
  rw [h]
  decide

theorem predecessorPrimorial_seven : predecessorPrimorial 7 = 30 := by
  have h : primesUpTo (7 - 1) = ({2, 3, 5} : Finset ℕ) := by
    norm_num [primesUpTo_six]
  unfold predecessorPrimorial primeFaceProduct
  rw [h]
  decide

theorem predecessorPrimorial_eleven : predecessorPrimorial 11 = 210 := by
  have h : primesUpTo (11 - 1) = ({2, 3, 5, 7} : Finset ℕ) := by
    norm_num [primesUpTo_ten]
  unfold predecessorPrimorial primeFaceProduct
  rw [h]
  decide

/-! ## A saturated daughter is exactly zero, not merely small

Once the square-dilated cutoff `X / q^2` reaches the predecessor primorial every
`q`-smooth face is admitted, the Boolean cube is complete, and the signed
daughter cancels exactly.  No estimate is involved. -/

theorem frozenPrimeUniverseMass_predecessorPrimorial_saturated
    {q Y : ℕ} (hq : 3 ≤ q) (hY : predecessorPrimorial q ≤ Y) :
    frozenPrimeUniverseMass (primesUpTo (q - 1)) Y = 0 := by
  have h2 : (2 : ℕ) ∈ primesUpTo (q - 1) :=
    mem_primesUpTo_pred_iff.mpr ⟨Nat.prime_two, by omega⟩
  unfold frozenPrimeUniverseMass
  refine truncatedCubeAlternatingSum_eq_zero_of_no_firstFailure h2
    primeProductAdmissible_downward ?_
  intro t _ht hadm
  have hsub : insert 2 t ⊆ primesUpTo (q - 1) := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hpt
    · exact h2
    · exact hadm.1 hpt
  refine ⟨hsub, ?_⟩
  have hle : primeFaceProduct (insert 2 t) ≤ predecessorPrimorial q := by
    unfold predecessorPrimorial primeFaceProduct
    apply Finset.prod_le_prod_of_subset_of_one_le' hsub
    intro p hp _
    exact (mem_primesUpTo_pred_iff.mp hp).1.one_lt.le
  exact hle.trans hY

/-- **Exact vanishing of a saturated Go daughter.**  The signed `q`-square
daughter of the physical Go recursion is identically zero as soon as the
predecessor primorial fits below the square-dilated cutoff. -/
theorem squareRootLowPrimeGoWallSquareResidual_eq_zero_of_saturated
    {q X : ℕ} (hq : 3 ≤ q) (hX : predecessorPrimorial q ≤ X / (q * q)) :
    squareRootLowPrimeGoWallSquareResidual q X = 0 := by
  rw [squareRootLowPrimeGoWallSquareResidual_eq_squareCutoff]
  exact frozenPrimeUniverseMass_predecessorPrimorial_saturated hq hX

/-! ## The live owner schedule of the saturated second-contact seeds -/

/-- **Primorial threshold on live owners.**  A saturated #629 second-contact
seed carries a squarefree core above the root all of whose prime factors lie
below its owner.  Such a core divides the predecessor primorial. -/
theorem lowWheelFrozenSecondContactCanonicalSeeds_root_lt_predecessorPrimorial
    {R : ℕ} {s : SourceIndex (squareRootEndpoint R)}
    (hs : s ∈ lowWheelFrozenSecondContactCanonicalSeeds R) :
    R < predecessorPrimorial (sourcePrime s) := by
  rcases mem_lowWheelFrozenSecondContactCanonicalSeeds_iff.mp hs with
    ⟨hadm, _hqR, hcore, _hcut⟩
  obtain ⟨_hqPrime, _hc1, hcsq, _hcop, hbelow⟩ := hadm
  have hRlt : R < sourceCore s := lt_of_le_of_lt (le_max_left _ _) hcore
  have hle := squarefree_below_le_predecessorPrimorial hcsq hbelow
  omega

/-- Owners that a live saturated second-contact seed can carry. -/
def liveOwnerCandidates (R : ℕ) : Finset ℕ :=
  (primesUpTo R).filter fun q => R < predecessorPrimorial q

theorem mem_liveOwnerCandidates {R q : ℕ} :
    q ∈ liveOwnerCandidates R ↔
      q.Prime ∧ q ≤ R ∧ R < predecessorPrimorial q := by
  unfold liveOwnerCandidates
  rw [Finset.mem_filter, mem_primesUpTo]
  tauto

theorem liveOwnerCandidates_subset_primesUpTo (R : ℕ) :
    liveOwnerCandidates R ⊆ primesUpTo R :=
  Finset.filter_subset _ _

theorem sourcePrime_mem_liveOwnerCandidates
    {R : ℕ} {s : SourceIndex (squareRootEndpoint R)}
    (hs : s ∈ lowWheelFrozenSecondContactCanonicalSeeds R) :
    sourcePrime s ∈ liveOwnerCandidates R := by
  rcases mem_lowWheelFrozenSecondContactCanonicalSeeds_iff.mp hs with
    ⟨hadm, hqR, _hcore, _hcut⟩
  exact mem_liveOwnerCandidates.mpr ⟨hadm.1, le_of_lt hqR,
    lowWheelFrozenSecondContactCanonicalSeeds_root_lt_predecessorPrimorial hs⟩

/-- Every owner whose predecessor primorial already fits under the root is
dead. -/
theorem lt_of_mem_liveOwnerCandidates {R Q q : ℕ}
    (hQ : predecessorPrimorial Q ≤ R) (hq : q ∈ liveOwnerCandidates R) :
    Q < q := by
  by_contra hle
  push_neg at hle
  have hmono := predecessorPrimorial_mono hle
  have hlive := (mem_liveOwnerCandidates.mp hq).2.2
  omega

theorem seven_le_of_mem_liveOwnerCandidates {R q : ℕ} (hR : 6 ≤ R)
    (hq : q ∈ liveOwnerCandidates R) : 7 ≤ q := by
  have h5 : 5 < q :=
    lt_of_mem_liveOwnerCandidates
      (Q := 5) (by rw [predecessorPrimorial_five]; omega) hq
  have hprime := (mem_liveOwnerCandidates.mp hq).1
  rcases Nat.lt_or_ge q 7 with h | h
  · interval_cases q
    exact absurd hprime (by norm_num)
  · exact h

theorem eleven_le_of_mem_liveOwnerCandidates {R q : ℕ} (hR : 30 ≤ R)
    (hq : q ∈ liveOwnerCandidates R) : 11 ≤ q := by
  have h7 : 7 < q :=
    lt_of_mem_liveOwnerCandidates
      (Q := 7) (by rw [predecessorPrimorial_seven]; omega) hq
  have hprime := (mem_liveOwnerCandidates.mp hq).1
  rcases Nat.lt_or_ge q 11 with h | h
  · interval_cases q <;> exact absurd hprime (by norm_num)
  · exact h

theorem thirteen_le_of_mem_liveOwnerCandidates {R q : ℕ} (hR : 210 ≤ R)
    (hq : q ∈ liveOwnerCandidates R) : 13 ≤ q := by
  have h11 : 11 < q :=
    lt_of_mem_liveOwnerCandidates
      (Q := 11) (by rw [predecessorPrimorial_eleven]; omega) hq
  have hprime := (mem_liveOwnerCandidates.mp hq).1
  rcases Nat.lt_or_ge q 13 with h | h
  · interval_cases q
    exact absurd hprime (by norm_num)
  · exact h

/-! ## Sharper owner budgets from the primorial threshold -/

private theorem oddReciprocalSquareShiftedTerm_le_telescope
    {a : ℚ} (ha : 0 < a) :
    1 / (2 * a + 1) ^ 2 ≤ 1 / (4 * a) - 1 / (4 * (a + 1)) := by
  have ha1 : (0 : ℚ) < a + 1 := by linarith
  have hane : a ≠ 0 := ne_of_gt ha
  have ha1ne : a + 1 ≠ 0 := ne_of_gt ha1
  have hrw : (1 : ℚ) / (4 * a) - 1 / (4 * (a + 1)) = 1 / (4 * a * (a + 1)) := by
    field_simp [hane, ha1ne] <;> ring
  rw [hrw]
  apply one_div_le_one_div_of_le
  · exact mul_pos (by linarith) ha1
  · nlinarith

private theorem sum_shiftedOddReciprocalSquares_le_sub
    {a : ℚ} (ha : 0 < a) (N : ℕ) :
    (∑ j ∈ Finset.range N, 1 / (2 * (a + (j : ℚ)) + 1) ^ 2) ≤
      1 / (4 * a) - 1 / (4 * (a + (N : ℚ))) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hNnn : (0 : ℚ) ≤ (N : ℚ) := Nat.cast_nonneg N
      have hterm := oddReciprocalSquareShiftedTerm_le_telescope
        (a := a + (N : ℚ)) (by linarith)
      have hshift : a + ((N + 1 : ℕ) : ℚ) = a + (N : ℚ) + 1 := by
        push_cast
        ring
      rw [hshift]
      linarith

private theorem sum_shiftedOddReciprocalSquares_le
    {a : ℚ} (ha : 0 < a) (N : ℕ) :
    (∑ j ∈ Finset.range N, 1 / (2 * (a + (j : ℚ)) + 1) ^ 2) ≤ 1 / (4 * a) := by
  have h := sum_shiftedOddReciprocalSquares_le_sub ha N
  have hNnn : (0 : ℚ) ≤ (N : ℚ) := Nat.cast_nonneg N
  have hpos : (0 : ℚ) ≤ 1 / (4 * (a + (N : ℚ))) :=
    one_div_nonneg.mpr (by linarith)
  linarith

/-- **Sharpened owner budget.**  An owner schedule made of primes at least
`2*k₀+3` spends at most `1/(4*(k₀+1))` of the parent reciprocal-square budget.
The complete prime schedule only gives `1`; the primorial threshold above
supplies a large `k₀` on the physical schedule. -/
theorem oddOwnerReciprocalSquareBudget_le
    {S : Finset ℕ} {N k₀ : ℕ}
    (hSN : S ⊆ primesUpTo N)
    (hlow : ∀ q ∈ S, 2 * k₀ + 3 ≤ q) :
    (∑ q ∈ S, (1 : ℚ) / (q : ℚ) ^ 2) ≤ 1 / (4 * ((k₀ : ℚ) + 1)) := by
  have hsub : S ⊆ (Finset.range N).image (fun j => 2 * (k₀ + j) + 3) := by
    intro q hq
    have hmem := mem_primesUpTo.mp (hSN hq)
    have hqN : q ≤ N := hmem.2
    have hlowq := hlow q hq
    obtain ⟨m, hm⟩ := hmem.1.odd_of_ne_two (by omega)
    refine Finset.mem_image.mpr ⟨m - k₀ - 1, Finset.mem_range.mpr ?_, ?_⟩ <;>
      omega
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun q : ℕ => (1 : ℚ) / (q : ℚ) ^ 2)
    (by intro q _ _; positivity)
  rw [Finset.sum_image (by intro c _ d _ hcd; omega)] at hle
  have hcast : ∀ j ∈ Finset.range N,
      (1 : ℚ) / ((2 * (k₀ + j) + 3 : ℕ) : ℚ) ^ 2 =
        1 / (2 * (((k₀ : ℚ) + 1) + (j : ℚ)) + 1) ^ 2 := by
    intro j _
    push_cast
    ring
  calc
    (∑ q ∈ S, (1 : ℚ) / (q : ℚ) ^ 2) ≤
        ∑ j ∈ Finset.range N, (1 : ℚ) / ((2 * (k₀ + j) + 3 : ℕ) : ℚ) ^ 2 := hle
    _ = ∑ j ∈ Finset.range N,
          1 / (2 * (((k₀ : ℚ) + 1) + (j : ℚ)) + 1) ^ 2 :=
        Finset.sum_congr rfl hcast
    _ ≤ 1 / (4 * ((k₀ : ℚ) + 1)) :=
        sum_shiftedOddReciprocalSquares_le (a := (k₀ : ℚ) + 1) (by positivity) N

/-- Each square-dilated daughter cutoff is at most the parent scale times the
owner's reciprocal square. -/
theorem sum_squareDilatedCutoffs_le_scale_mul_reciprocalSquares
    (S : Finset ℕ) (X : ℕ) (hS : ∀ q ∈ S, q.Prime) :
    (∑ q ∈ S, ((X / (q * q) : ℕ) : ℚ)) ≤
      (X : ℚ) * ∑ q ∈ S, (1 : ℚ) / (q : ℚ) ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hp := hS q hq
  have hqqPos : (0 : ℚ) < ((q * q : ℕ) : ℚ) := by
    exact_mod_cast Nat.mul_pos hp.pos hp.pos
  have hmul : (((X / (q * q) : ℕ) : ℚ) * ((q * q : ℕ) : ℚ)) ≤ (X : ℚ) := by
    exact_mod_cast Nat.div_mul_le_self X (q * q)
  have hdiv := (le_div_iff₀ hqqPos).2 hmul
  have hrw : (X : ℚ) / ((q * q : ℕ) : ℚ) = (X : ℚ) * ((1 : ℚ) / (q : ℚ) ^ 2) := by
    push_cast
    ring
  rw [hrw] at hdiv
  exact hdiv

/-- The sharpened budget on the literal integer daughter cutoffs used by the Go
recursion. -/
theorem sum_oddOwner_squareDilatedCutoffs_le
    {S : Finset ℕ} {N k₀ : ℕ} (X : ℕ)
    (hSN : S ⊆ primesUpTo N)
    (hlow : ∀ q ∈ S, 2 * k₀ + 3 ≤ q) :
    (∑ q ∈ S, ((X / (q * q) : ℕ) : ℚ)) ≤
      (1 / (4 * ((k₀ : ℚ) + 1))) * (X : ℚ) := by
  have h := sum_squareDilatedCutoffs_le_scale_mul_reciprocalSquares S X
    (fun q hq => (mem_primesUpTo.mp (hSN hq)).1)
  have hb := oddOwnerReciprocalSquareBudget_le hSN hlow
  have hX : (0 : ℚ) ≤ (X : ℚ) := by positivity
  calc
    (∑ q ∈ S, ((X / (q * q) : ℕ) : ℚ)) ≤
        (X : ℚ) * ∑ q ∈ S, (1 : ℚ) / (q : ℚ) ^ 2 := h
    _ ≤ (X : ℚ) * (1 / (4 * ((k₀ : ℚ) + 1))) :=
      mul_le_mul_of_nonneg_left hb hX
    _ = (1 / (4 * ((k₀ : ℚ) + 1))) * (X : ℚ) := by ring

/-- Uniformly in the root, the live owner budget is at most `1/12`. -/
theorem liveOwnerCandidates_squareDilatedCutoffs_le_twelfth
    {R : ℕ} (hR : 6 ≤ R) (X : ℕ) :
    (∑ q ∈ liveOwnerCandidates R, ((X / (q * q) : ℕ) : ℚ)) ≤
      (1 / 12 : ℚ) * (X : ℚ) := by
  have h := sum_oddOwner_squareDilatedCutoffs_le (S := liveOwnerCandidates R)
    (N := R) (k₀ := 2) X (liveOwnerCandidates_subset_primesUpTo R)
    (fun q hq => by
      have := seven_le_of_mem_liveOwnerCandidates hR hq
      omega)
  refine h.trans (le_of_eq ?_)
  norm_num

/-- Beyond root `30` the live owner budget is at most `1/20`. -/
theorem liveOwnerCandidates_squareDilatedCutoffs_le_twentieth
    {R : ℕ} (hR : 30 ≤ R) (X : ℕ) :
    (∑ q ∈ liveOwnerCandidates R, ((X / (q * q) : ℕ) : ℚ)) ≤
      (1 / 20 : ℚ) * (X : ℚ) := by
  have h := sum_oddOwner_squareDilatedCutoffs_le (S := liveOwnerCandidates R)
    (N := R) (k₀ := 4) X (liveOwnerCandidates_subset_primesUpTo R)
    (fun q hq => by
      have := eleven_le_of_mem_liveOwnerCandidates hR hq
      omega)
  refine h.trans (le_of_eq ?_)
  norm_num

/-! ## The energy induction on a restricted owner schedule -/

/-- Owner-weighted form of the `q^2` energy induction.  The unweighted schedule
version is the special case `theta = 1`; retaining a weight is what makes the
purely diagonal route below possible. -/
theorem q2EnergyStep_implies_linear_of_weightedOwnerScheduleBudget
    {E : ℕ → ℚ} {owners : ℕ → Finset ℕ} {theta : ℕ → ℚ} {C lambda rho K : ℚ}
    (howners : ∀ X, owners X ⊆ primesUpTo X)
    (htheta : ∀ q, 0 ≤ theta q)
    (hK : 0 ≤ K) (hlambda : 0 ≤ lambda)
    (hscale : ∀ X, (∑ q ∈ owners X, theta q * ((X / (q * q) : ℕ) : ℚ)) ≤
      rho * (X : ℚ))
    (hfixed : C + lambda * rho * K ≤ K)
    (hstep : ∀ X, E X ≤ C * (X : ℚ) +
      lambda * ∑ q ∈ owners X, theta q * E (X / (q * q))) :
    ∀ X, E X ≤ K * (X : ℚ) := by
  intro X
  induction X using Nat.strong_induction_on with
  | h X ih =>
      by_cases hX : X = 0
      · subst X
        have hempty : owners 0 = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro q hq
          have hp := mem_primesUpTo.mp (howners 0 hq)
          have h2 := hp.1.two_le
          omega
        simpa [hempty] using hstep 0
      · have hchildren :
            (∑ q ∈ owners X, theta q * E (X / (q * q))) ≤
              K * (∑ q ∈ owners X, theta q * ((X / (q * q) : ℕ) : ℚ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro q hq
          have hp := (mem_primesUpTo.mp (howners X hq)).1
          have hchild := ih (X / (q * q))
            (Nat.div_lt_self (Nat.pos_of_ne_zero hX) (by nlinarith [hp.two_le]))
          calc
            theta q * E (X / (q * q)) ≤
                theta q * (K * ((X / (q * q) : ℕ) : ℚ)) :=
              mul_le_mul_of_nonneg_left hchild (htheta q)
            _ = K * (theta q * ((X / (q * q) : ℕ) : ℚ)) := by ring
        have hchildren' :
            (∑ q ∈ owners X, theta q * E (X / (q * q))) ≤ K * (rho * (X : ℚ)) :=
          hchildren.trans (mul_le_mul_of_nonneg_left (hscale X) hK)
        have hweighted :
            lambda * (∑ q ∈ owners X, theta q * E (X / (q * q))) ≤
              lambda * (K * (rho * (X : ℚ))) :=
          mul_le_mul_of_nonneg_left hchildren' hlambda
        calc
          E X ≤ C * (X : ℚ) +
              lambda * ∑ q ∈ owners X, theta q * E (X / (q * q)) := hstep X
          _ ≤ C * (X : ℚ) + lambda * (K * (rho * (X : ℚ))) := by linarith
          _ = (C + lambda * rho * K) * (X : ℚ) := by ring
          _ ≤ K * (X : ℚ) :=
            mul_le_mul_of_nonneg_right hfixed (by positivity)

/-- Unweighted owner-schedule induction: only the product of the owner scale
budget with the branching coefficient enters. -/
theorem q2EnergyStep_implies_linear_of_ownerScheduleBudget
    {E : ℕ → ℚ} {owners : ℕ → Finset ℕ} {C lambda rho K : ℚ}
    (howners : ∀ X, owners X ⊆ primesUpTo X)
    (hK : 0 ≤ K) (hlambda : 0 ≤ lambda)
    (hscale : ∀ X, (∑ q ∈ owners X, ((X / (q * q) : ℕ) : ℚ)) ≤ rho * (X : ℚ))
    (hfixed : C + lambda * rho * K ≤ K)
    (hstep : ∀ X, E X ≤ C * (X : ℚ) +
      lambda * ∑ q ∈ owners X, E (X / (q * q))) :
    ∀ X, E X ≤ K * (X : ℚ) := by
  refine q2EnergyStep_implies_linear_of_weightedOwnerScheduleBudget
    (theta := fun _ => 1) howners (fun _ => zero_le_one) hK hlambda ?_ hfixed ?_
  · intro X
    simpa using hscale X
  · intro X
    simpa using hstep X

/-! ## Admissible frame loss -/

/-- **Only the product of frame loss and owner budget matters.**  Whenever the
product `A * rho` is at most one, the compiled prime-`11` recurrence still closes
with the linear envelope `(6348/143)*B*X`.  The `4/3` frame target of #634 is the
case `A * rho = (4/3) * 1`, which is exactly what the crude unit budget forced. -/
theorem elevenQ2_frameLoss_budget_implies_linear
    {E I b : ℕ → ℚ} {owners : ℕ → Finset ℕ} {A rho B : ℚ}
    (hB : 0 ≤ B) (hA : 0 ≤ A) (hAr : A * rho ≤ 1)
    (howners : ∀ X, owners X ⊆ primesUpTo X)
    (hscale : ∀ X, (∑ q ∈ owners X, ((X / (q * q) : ℕ) : ℚ)) ≤ rho * (X : ℚ))
    (hdecomp : ∀ X, E X ≤ (I X + b X) ^ 2)
    (hinterior : ∀ X, (I X) ^ 2 ≤ A * elevenWeightOneEnergyFactor *
      ∑ q ∈ owners X, E (X / (q * q)))
    (hboundary : ∀ X, (b X) ^ 2 ≤ B * (X : ℚ)) :
    ∀ X, E X ≤ ((6348 : ℚ) / 143 * B) * (X : ℚ) := by
  have hfac : (0 : ℚ) ≤ elevenWeightOneEnergyFactor :=
    elevenWeightOneEnergyFactor_nonneg
  have hK : (0 : ℚ) ≤ (6348 : ℚ) / 143 * B := mul_nonneg (by norm_num) hB
  apply q2EnergyStep_implies_linear_of_ownerScheduleBudget
    (owners := owners) (C := 4 * B)
    (lambda := (4 : ℚ) / 3 * A * elevenWeightOneEnergyFactor) (rho := rho)
    howners hK (mul_nonneg (by linarith) hfac) hscale
  · have hchain :
        ((4 : ℚ) / 3 * A * elevenWeightOneEnergyFactor) * rho *
            ((6348 : ℚ) / 143 * B) ≤
          ((4 : ℚ) / 3 * elevenWeightOneEnergyFactor) *
            ((6348 : ℚ) / 143 * B) := by
      have hrewrite :
          ((4 : ℚ) / 3 * A * elevenWeightOneEnergyFactor) * rho *
              ((6348 : ℚ) / 143 * B) =
            ((4 : ℚ) / 3 * elevenWeightOneEnergyFactor) * (A * rho) *
              ((6348 : ℚ) / 143 * B) := by ring
      rw [hrewrite]
      have hinner : ((4 : ℚ) / 3 * elevenWeightOneEnergyFactor) * (A * rho) ≤
          ((4 : ℚ) / 3 * elevenWeightOneEnergyFactor) * 1 :=
        mul_le_mul_of_nonneg_left hAr (by linarith)
      have houter := mul_le_mul_of_nonneg_right hinner hK
      linarith
    have hval : ((4 : ℚ) / 3 * elevenWeightOneEnergyFactor) *
        ((6348 : ℚ) / 143 * B) = (5776 : ℚ) / 143 * B := by
      rw [elevenWeightOneEnergyFactor_eq]
      ring
    linarith
  · intro X
    have hi := hinterior X
    have hbX := hboundary X
    have he := hdecomp X
    have hy : (I X + b X) ^ 2 ≤ (4 : ℚ) / 3 * (I X) ^ 2 + 4 * (b X) ^ 2 := by
      nlinarith [sq_nonneg (I X - 3 * b X)]
    have h1 : (4 : ℚ) / 3 * (I X) ^ 2 ≤
        (4 : ℚ) / 3 * (A * elevenWeightOneEnergyFactor *
          ∑ q ∈ owners X, E (X / (q * q))) :=
      mul_le_mul_of_nonneg_left hi (by norm_num)
    have h2 : (4 : ℚ) * (b X) ^ 2 ≤ 4 * (B * (X : ℚ)) :=
      mul_le_mul_of_nonneg_left hbX (by norm_num)
    calc
      E X ≤ (I X + b X) ^ 2 := he
      _ ≤ (4 : ℚ) / 3 * (I X) ^ 2 + 4 * (b X) ^ 2 := hy
      _ ≤ (4 : ℚ) / 3 * (A * elevenWeightOneEnergyFactor *
            ∑ q ∈ owners X, E (X / (q * q))) + 4 * (B * (X : ℚ)) := by linarith
      _ = 4 * B * (X : ℚ) + ((4 : ℚ) / 3 * A * elevenWeightOneEnergyFactor) *
            ∑ q ∈ owners X, E (X / (q * q)) := by ring

/-- **Frame loss `4*(k₀+1)` on an owner schedule of primes at least `2*k₀+3`.**
The primorial threshold makes `k₀` grow with the root. -/
theorem oddOwnerFrame_implies_linear
    {E I b : ℕ → ℚ} {owners : ℕ → Finset ℕ} {A B : ℚ} {k₀ : ℕ}
    (hB : 0 ≤ B) (hA : 0 ≤ A) (hAk : A ≤ 4 * ((k₀ : ℚ) + 1))
    (howners : ∀ X, owners X ⊆ primesUpTo X)
    (hlow : ∀ X, ∀ q ∈ owners X, 2 * k₀ + 3 ≤ q)
    (hdecomp : ∀ X, E X ≤ (I X + b X) ^ 2)
    (hinterior : ∀ X, (I X) ^ 2 ≤ A * elevenWeightOneEnergyFactor *
      ∑ q ∈ owners X, E (X / (q * q)))
    (hboundary : ∀ X, (b X) ^ 2 ≤ B * (X : ℚ)) :
    ∀ X, E X ≤ ((6348 : ℚ) / 143 * B) * (X : ℚ) := by
  refine elevenQ2_frameLoss_budget_implies_linear
    (rho := 1 / (4 * ((k₀ : ℚ) + 1))) hB hA ?_ howners ?_ hdecomp hinterior
    hboundary
  · rw [mul_one_div, div_le_one (by positivity)]
    exact hAk
  · intro X
    exact sum_oddOwner_squareDilatedCutoffs_le X (howners X) (hlow X)

/-- **A factor-twelve frame is admissible on the live owner schedule.**  The
`4/3` target is far inside this budget. -/
theorem liveOwnerFrame_twelve_implies_linear
    {E I b : ℕ → ℚ} {owners : ℕ → Finset ℕ} {B : ℚ}
    (hB : 0 ≤ B)
    (howners : ∀ X, owners X ⊆ primesUpTo X)
    (hlow : ∀ X, ∀ q ∈ owners X, 7 ≤ q)
    (hdecomp : ∀ X, E X ≤ (I X + b X) ^ 2)
    (hinterior : ∀ X, (I X) ^ 2 ≤ 12 * elevenWeightOneEnergyFactor *
      ∑ q ∈ owners X, E (X / (q * q)))
    (hboundary : ∀ X, (b X) ^ 2 ≤ B * (X : ℚ)) :
    ∀ X, E X ≤ ((6348 : ℚ) / 143 * B) * (X : ℚ) :=
  oddOwnerFrame_implies_linear (k₀ := 2) (A := 12) hB (by norm_num)
    (by norm_num) howners
    (fun X q hq => by
      have := hlow X q hq
      omega)
    hdecomp hinterior hboundary

/-- **A factor-twenty frame is admissible beyond root `30`.** -/
theorem liveOwnerFrame_twenty_implies_linear
    {E I b : ℕ → ℚ} {owners : ℕ → Finset ℕ} {B : ℚ}
    (hB : 0 ≤ B)
    (howners : ∀ X, owners X ⊆ primesUpTo X)
    (hlow : ∀ X, ∀ q ∈ owners X, 11 ≤ q)
    (hdecomp : ∀ X, E X ≤ (I X + b X) ^ 2)
    (hinterior : ∀ X, (I X) ^ 2 ≤ 20 * elevenWeightOneEnergyFactor *
      ∑ q ∈ owners X, E (X / (q * q)))
    (hboundary : ∀ X, (b X) ^ 2 ≤ B * (X : ℚ)) :
    ∀ X, E X ≤ ((6348 : ℚ) / 143 * B) * (X : ℚ) :=
  oddOwnerFrame_implies_linear (k₀ := 4) (A := 20) hB (by norm_num)
    (by norm_num) howners
    (fun X q hq => by
      have := hlow X q hq
      omega)
    hdecomp hinterior hboundary

/-- **The admissible frame loss is unbounded in the root.**  For every
prescribed loss `A` there is an explicit primorial root threshold beyond which
the live owner schedule already pays for it.  This is the exact sense in which
a fixed `4/3` target was far too conservative. -/
theorem liveOwner_admissible_frameLoss_unbounded (A : ℚ) :
    ∃ k₀ R₀ : ℕ, A ≤ 4 * ((k₀ : ℚ) + 1) ∧
      ∀ R q : ℕ, R₀ ≤ R → q ∈ liveOwnerCandidates R → 2 * k₀ + 3 ≤ q := by
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt A
  refine ⟨k₀, predecessorPrimorial (2 * k₀ + 2), ?_, ?_⟩
  · have hnn : (0 : ℚ) ≤ (k₀ : ℚ) := Nat.cast_nonneg k₀
    linarith
  · intro R q hR hq
    have hlt := lt_of_mem_liveOwnerCandidates (Q := 2 * k₀ + 2) hR hq
    omega

/-! ## The purely diagonal route

Everything above still assumes a frame inequality.  The theorems below assume
none: only that the interior is the sum of its owner columns and that each
column separately is dominated by its own contracted daughter energy.  What
replaces the frame hypothesis is the owner weight `q`, retained through the
descent, and the criterion becomes a single harmonic sum. -/

private theorem sq_div_one_div (x t : ℚ) : x ^ 2 / (1 / t) = t * x ^ 2 := by
  rw [div_div_eq_mul_div, div_one, mul_comm]

/-- Weighted Cauchy–Schwarz on the owner columns.  No sign information and no
cross-owner cancellation is used. -/
theorem sq_sum_le_weightedOwnerEnergy
    (S : Finset ℕ) (m theta : ℕ → ℚ) (hpos : ∀ q ∈ S, 0 < theta q) :
    (∑ q ∈ S, m q) ^ 2 ≤
      (∑ q ∈ S, 1 / theta q) * ∑ q ∈ S, theta q * (m q) ^ 2 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  · have hginv : ∀ q ∈ S, (0 : ℚ) < 1 / theta q := by
      intro q hq
      exact one_div_pos.mpr (hpos q hq)
    have hsum : (0 : ℚ) < ∑ q ∈ S, 1 / theta q := Finset.sum_pos hginv hne
    have h := Finset.sq_sum_div_le_sum_sq_div S m hginv
    have hrw : (∑ q ∈ S, (m q) ^ 2 / (1 / theta q)) =
        ∑ q ∈ S, theta q * (m q) ^ 2 :=
      Finset.sum_congr rfl (fun q _ => sq_div_one_div (m q) (theta q))
    rw [hrw, div_le_iff₀ hsum] at h
    exact h.trans_eq (mul_comm _ _)

/-- Owner-weighted daughter budget: the weight `q` converts the reciprocal
square budget into the owner harmonic sum. -/
theorem sum_weighted_squareDilatedCutoffs_le_harmonic
    (S : Finset ℕ) (X : ℕ) (hS : ∀ q ∈ S, q.Prime) :
    (∑ q ∈ S, (q : ℚ) * ((X / (q * q) : ℕ) : ℚ)) ≤
      (X : ℚ) * ∑ q ∈ S, (1 : ℚ) / (q : ℚ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hp := hS q hq
  have hqPos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hp.pos
  have hmulCast : (((X / (q * q) : ℕ) : ℚ) * ((q * q : ℕ) : ℚ)) ≤ (X : ℚ) := by
    exact_mod_cast Nat.div_mul_le_self X (q * q)
  have hmul : (((X / (q * q) : ℕ) : ℚ) * ((q : ℚ) * (q : ℚ))) ≤ (X : ℚ) := by
    calc
      (((X / (q * q) : ℕ) : ℚ) * ((q : ℚ) * (q : ℚ))) =
          (((X / (q * q) : ℕ) : ℚ) * ((q * q : ℕ) : ℚ)) := by push_cast; ring
      _ ≤ (X : ℚ) := hmulCast
  rw [mul_one_div, le_div_iff₀ hqPos]
  calc
    (q : ℚ) * ((X / (q * q) : ℕ) : ℚ) * (q : ℚ) =
        ((X / (q * q) : ℕ) : ℚ) * ((q : ℚ) * (q : ℚ)) := by ring
    _ ≤ (X : ℚ) := hmul

/-- **Elementary diagonal criterion.**  Assume only that the interior is the sum
of its owner columns and that each column separately is dominated by its own
prime-`11` contracted daughter energy — no cross-owner cancellation, no frame
inequality of any kind.  Then the whole recurrence is controlled by one number:
the owner harmonic sum.  The weighted Cauchy–Schwarz step spends `c` and the
weighted daughter budget spends `c` again, so the branching coefficient is
`(4/3) * (19/23)^2 * c^2` and closure needs only `c < 23/(19*sqrt(4/3))`, i.e.
`c` up to about `1.048`. -/
theorem elevenQ2_harmonicOwnerColumns_implies_linear_of_bound
    {E I b : ℕ → ℚ} {column : ℕ → ℕ → ℚ} {owners : ℕ → Finset ℕ} {c B K : ℚ}
    (hB : 0 ≤ B) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hfixed : 4 * B +
      (4 : ℚ) / 3 * elevenWeightOneEnergyFactor * c ^ 2 * K ≤ K)
    (howners : ∀ X, owners X ⊆ primesUpTo X)
    (hharmonic : ∀ X, (∑ q ∈ owners X, (1 : ℚ) / (q : ℚ)) ≤ c)
    (hdecomp : ∀ X, E X ≤ (I X + b X) ^ 2)
    (hcolumns : ∀ X, I X = ∑ q ∈ owners X, column X q)
    (hdiagonal : ∀ X, ∀ q ∈ owners X, (column X q) ^ 2 ≤
      elevenWeightOneEnergyFactor * E (X / (q * q)))
    (hboundary : ∀ X, (b X) ^ 2 ≤ B * (X : ℚ)) :
    ∀ X, E X ≤ K * (X : ℚ) := by
  have hfac : (0 : ℚ) ≤ elevenWeightOneEnergyFactor :=
    elevenWeightOneEnergyFactor_nonneg
  apply q2EnergyStep_implies_linear_of_weightedOwnerScheduleBudget
    (owners := owners) (theta := fun q => (q : ℚ)) (C := 4 * B)
    (lambda := (4 : ℚ) / 3 * c * elevenWeightOneEnergyFactor) (rho := c)
    howners (fun q => Nat.cast_nonneg q) hK
    (mul_nonneg (mul_nonneg (by norm_num) hc) hfac)
  · intro X
    have h := sum_weighted_squareDilatedCutoffs_le_harmonic (owners X) X
      (fun q hq => (mem_primesUpTo.mp (howners X hq)).1)
    have hX : (0 : ℚ) ≤ (X : ℚ) := by positivity
    calc
      (∑ q ∈ owners X, (q : ℚ) * ((X / (q * q) : ℕ) : ℚ)) ≤
          (X : ℚ) * ∑ q ∈ owners X, (1 : ℚ) / (q : ℚ) := h
      _ ≤ (X : ℚ) * c := mul_le_mul_of_nonneg_left (hharmonic X) hX
      _ = c * (X : ℚ) := by ring
  · have hEq : ((4 : ℚ) / 3 * c * elevenWeightOneEnergyFactor) * c * K =
        (4 : ℚ) / 3 * elevenWeightOneEnergyFactor * c ^ 2 * K := by ring
    rw [hEq]
    exact hfixed
  · intro X
    have hpos : ∀ q ∈ owners X, (0 : ℚ) < (q : ℚ) := by
      intro q hq
      exact_mod_cast (mem_primesUpTo.mp (howners X hq)).1.pos
    have hcs := sq_sum_le_weightedOwnerEnergy (owners X) (column X)
      (fun q => (q : ℚ)) hpos
    have hVnonneg : (0 : ℚ) ≤ ∑ q ∈ owners X, (q : ℚ) * (column X q) ^ 2 := by
      apply Finset.sum_nonneg
      intro q _
      positivity
    have hdiag : (∑ q ∈ owners X, (q : ℚ) * (column X q) ^ 2) ≤
        ∑ q ∈ owners X, (q : ℚ) *
          (elevenWeightOneEnergyFactor * E (X / (q * q))) := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (hdiagonal X q hq) (by positivity)
    have hpull : (∑ q ∈ owners X, (q : ℚ) *
        (elevenWeightOneEnergyFactor * E (X / (q * q)))) =
          elevenWeightOneEnergyFactor *
            ∑ q ∈ owners X, (q : ℚ) * E (X / (q * q)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun q _ => by ring)
    have hIsq : (I X) ^ 2 ≤ c * (elevenWeightOneEnergyFactor *
        ∑ q ∈ owners X, (q : ℚ) * E (X / (q * q))) := by
      rw [hcolumns X]
      calc
        (∑ q ∈ owners X, column X q) ^ 2 ≤
            (∑ q ∈ owners X, 1 / (q : ℚ)) *
              ∑ q ∈ owners X, (q : ℚ) * (column X q) ^ 2 := hcs
        _ ≤ c * ∑ q ∈ owners X, (q : ℚ) * (column X q) ^ 2 :=
          mul_le_mul_of_nonneg_right (hharmonic X) hVnonneg
        _ ≤ c * ∑ q ∈ owners X, (q : ℚ) *
              (elevenWeightOneEnergyFactor * E (X / (q * q))) :=
          mul_le_mul_of_nonneg_left hdiag hc
        _ = c * (elevenWeightOneEnergyFactor *
              ∑ q ∈ owners X, (q : ℚ) * E (X / (q * q))) := by rw [hpull]
    have hbX := hboundary X
    have he := hdecomp X
    have hy : (I X + b X) ^ 2 ≤ (4 : ℚ) / 3 * (I X) ^ 2 + 4 * (b X) ^ 2 := by
      nlinarith [sq_nonneg (I X - 3 * b X)]
    have h1 : (4 : ℚ) / 3 * (I X) ^ 2 ≤
        (4 : ℚ) / 3 * (c * (elevenWeightOneEnergyFactor *
          ∑ q ∈ owners X, (q : ℚ) * E (X / (q * q)))) :=
      mul_le_mul_of_nonneg_left hIsq (by norm_num)
    have h2 : (4 : ℚ) * (b X) ^ 2 ≤ 4 * (B * (X : ℚ)) :=
      mul_le_mul_of_nonneg_left hbX (by norm_num)
    calc
      E X ≤ (I X + b X) ^ 2 := he
      _ ≤ (4 : ℚ) / 3 * (I X) ^ 2 + 4 * (b X) ^ 2 := hy
      _ ≤ (4 : ℚ) / 3 * (c * (elevenWeightOneEnergyFactor *
            ∑ q ∈ owners X, (q : ℚ) * E (X / (q * q)))) +
          4 * (B * (X : ℚ)) := by linarith
      _ = 4 * B * (X : ℚ) +
            ((4 : ℚ) / 3 * c * elevenWeightOneEnergyFactor) *
              ∑ q ∈ owners X, (q : ℚ) * E (X / (q * q)) := by ring

/-- The criterion at harmonic sum one, with the same envelope as every frame
statement above. -/
theorem elevenQ2_harmonicOwnerColumns_implies_linear
    {E I b : ℕ → ℚ} {column : ℕ → ℕ → ℚ} {owners : ℕ → Finset ℕ} {B : ℚ}
    (hB : 0 ≤ B)
    (howners : ∀ X, owners X ⊆ primesUpTo X)
    (hharmonic : ∀ X, (∑ q ∈ owners X, (1 : ℚ) / (q : ℚ)) ≤ 1)
    (hdecomp : ∀ X, E X ≤ (I X + b X) ^ 2)
    (hcolumns : ∀ X, I X = ∑ q ∈ owners X, column X q)
    (hdiagonal : ∀ X, ∀ q ∈ owners X, (column X q) ^ 2 ≤
      elevenWeightOneEnergyFactor * E (X / (q * q)))
    (hboundary : ∀ X, (b X) ^ 2 ≤ B * (X : ℚ)) :
    ∀ X, E X ≤ ((6348 : ℚ) / 143 * B) * (X : ℚ) := by
  refine elevenQ2_harmonicOwnerColumns_implies_linear_of_bound (c := 1)
    hB (by norm_num) (mul_nonneg (by norm_num) hB) ?_ howners hharmonic
    hdecomp hcolumns hdiagonal hboundary
  have hval : (4 : ℚ) / 3 * elevenWeightOneEnergyFactor * (1 : ℚ) ^ 2 *
      ((6348 : ℚ) / 143 * B) = (5776 : ℚ) / 143 * B := by
    rw [elevenWeightOneEnergyFactor_eq]
    ring
  linarith

/-- **The elementary criterion survives a harmonic sum above one.**  At
`c = 26/25 = 1.04` the branching coefficient is still `976144/991875 < 1`, so
the cancellation-free diagonal route closes with envelope
`(3967500/15731)*B*X`.  The exact elementary ceiling is `c^2 < 1587/1444`, that
is `c < 1.0483...`; the live owner harmonic sum first crosses it just past root
`10^4`. -/
theorem elevenQ2_harmonicOwnerColumns_implies_linear_at_twentySixFifths
    {E I b : ℕ → ℚ} {column : ℕ → ℕ → ℚ} {owners : ℕ → Finset ℕ} {B : ℚ}
    (hB : 0 ≤ B)
    (howners : ∀ X, owners X ⊆ primesUpTo X)
    (hharmonic : ∀ X, (∑ q ∈ owners X, (1 : ℚ) / (q : ℚ)) ≤ 26 / 25)
    (hdecomp : ∀ X, E X ≤ (I X + b X) ^ 2)
    (hcolumns : ∀ X, I X = ∑ q ∈ owners X, column X q)
    (hdiagonal : ∀ X, ∀ q ∈ owners X, (column X q) ^ 2 ≤
      elevenWeightOneEnergyFactor * E (X / (q * q)))
    (hboundary : ∀ X, (b X) ^ 2 ≤ B * (X : ℚ)) :
    ∀ X, E X ≤ ((3967500 : ℚ) / 15731 * B) * (X : ℚ) := by
  refine elevenQ2_harmonicOwnerColumns_implies_linear_of_bound (c := 26 / 25)
    hB (by norm_num) (mul_nonneg (by norm_num) hB) ?_ howners hharmonic
    hdecomp hcolumns hdiagonal hboundary
  have hval : (4 : ℚ) / 3 * elevenWeightOneEnergyFactor * ((26 : ℚ) / 25) ^ 2 *
      ((3967500 : ℚ) / 15731 * B) = (3904576 : ℚ) / 15731 * B := by
    rw [elevenWeightOneEnergyFactor_eq]
    ring
  linarith

/-- The exact elementary ceiling on the owner harmonic sum: the branching
coefficient stays below one precisely while `c^2 < 1587/1444`. -/
theorem elevenQ2_harmonicOwner_branchingCoefficient_lt_one :
    (4 : ℚ) / 3 * elevenWeightOneEnergyFactor * ((26 : ℚ) / 25) ^ 2 < 1 := by
  rw [elevenWeightOneEnergyFactor_eq]
  norm_num

end RHLean.Proof

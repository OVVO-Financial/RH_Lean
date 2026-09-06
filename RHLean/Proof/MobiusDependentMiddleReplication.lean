import Mathlib
import RHLean.Arithmetic.FourSlotCell
import RHLean.Arithmetic.PrimorialWheelPrefixIdentity
import RHLean.Analysis.DyadicTransportCompression
import RHLean.Proof.MiddlePrimeFibreCollapse

/-!
# Deterministic Möbius dependence in the post-root prime replication

This file packages the non-iid structure that is available before any
probabilistic model is introduced.

* Every aligned four-slot Möbius cell contains a forced zero.
* A same-sign run after deleting zero terms gives an exact Mertens excursion;
  no independence assumption is used.
* Every nontrivial post-root replication `c*q <= X_R` with `c >= 2` lies in the
  middle prime sector `R < q <= X_R/2`.
* Inside one middle prime fibre, adjoining `q` is a deterministic sign reversal
  of the already-fixed lower prefix.  Hence the complete three-state population
  is transported exactly: zeros stay zeros and `+1/-1` swap.
* The existing dyadic compression theorem is the first exact quantitative use
  of this dependence: doubled odd cofactors cancel their parents and multiples
  of four vanish, leaving only the odd dyadic boundary.

The point is structural.  The post-root prime clock does not resample Möbius
signs.  It repeatedly exposes nested prefixes of one fixed arithmetic sequence.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

/-! ## Forced dependence in the raw Möbius sequence -/

/-- Every aligned block `{4k+1,...,4k+4}` contains a forced Möbius zero. -/
theorem mobius_fourSlotCell_has_forced_zero (k : ℕ) :
    ∃ n ∈ Finset.Icc (4 * k + 1) (4 * k + 4), μ n = 0 := by
  refine ⟨4 * k + 4, Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, ?_⟩
  exact moebius_four_mul_add_four k

/-- Consequently an aligned four-slot cell can never consist entirely of
nonzero Möbius values.  This is a literal forbidden pattern, not an iid tail
estimate. -/
theorem mobius_fourSlotCell_not_all_nonzero (k : ℕ) :
    ¬(∀ n ∈ Finset.Icc (4 * k + 1) (4 * k + 4), μ n ≠ 0) := by
  intro h
  rcases mobius_fourSlotCell_has_forced_zero k with ⟨n, hn, hz⟩
  exact (h n hn) hz

/-- A same-sign Möbius run after deleting zero terms. -/
def IsSameSignNonzeroMobiusRun (a b : ℕ) (s : ℤ) : Prop :=
  (s = 1 ∨ s = -1) ∧
    ∀ n ∈ Finset.Ioc a b, μ n ≠ 0 → μ n = s

/-- Number of nonzero Möbius observations in an interval. -/
def sameSignNonzeroMobiusRunLength (a b : ℕ) : ℕ :=
  ((Finset.Ioc a b).filter fun n => μ n ≠ 0).card

/-- **Exact excursion law for a same-sign nonzero run.**
If all nonzero Möbius values in `(a,b]` have sign `s`, then the interval sum is
exactly `s` times the number of nonzero observations.  Zeros are ignored
without any independence assumption. -/
theorem sameSignNonzeroMobiusRun_sum
    {a b : ℕ} {s : ℤ}
    (hrun : IsSameSignNonzeroMobiusRun a b s) :
    (∑ n ∈ Finset.Ioc a b, μ n) =
      s * (sameSignNonzeroMobiusRunLength a b : ℤ) := by
  classical
  rcases hrun with ⟨_hs, hsign⟩
  let S : Finset ℕ := Finset.Ioc a b
  let T : Finset ℕ := S.filter fun n => μ n ≠ 0
  have hsub : T ⊆ S := Finset.filter_subset _ _
  have hvanish : ∀ n ∈ S, n ∉ T → μ n = 0 := by
    intro n hnS hnT
    by_contra hne
    exact hnT (Finset.mem_filter.mpr ⟨hnS, hne⟩)
  have hrestrict :
      (∑ n ∈ S, μ n) = ∑ n ∈ T, μ n :=
    (Finset.sum_subset hsub hvanish).symm
  calc
    (∑ n ∈ Finset.Ioc a b, μ n) = ∑ n ∈ T, μ n := by
      simpa [S] using hrestrict
    _ = ∑ _n ∈ T, s := by
      apply Finset.sum_congr rfl
      intro n hnT
      have hmem := Finset.mem_filter.mp hnT
      exact hsign n hmem.1 hmem.2
    _ = (T.card : ℤ) * s := by simp
    _ = s * (sameSignNonzeroMobiusRunLength a b : ℤ) := by
      simp [T, S, sameSignNonzeroMobiusRunLength, mul_comm]

/-- Complex Mertens form of the same exact excursion law. -/
theorem sameSignNonzeroMobiusRun_mertensExcursion
    {a b : ℕ} {s : ℤ} (hab : a ≤ b)
    (hrun : IsSameSignNonzeroMobiusRun a b s) :
    mertensSummatory b - mertensSummatory a =
      ((s * (sameSignNonzeroMobiusRunLength a b : ℤ) : ℤ) : ℂ) := by
  calc
    mertensSummatory b - mertensSummatory a =
        ∑ n ∈ Finset.Ioc a b, (((μ n : ℤ) : ℂ)) :=
      (RHLean.Arithmetic.moebius_Ioc_cast_eq_mertens_sub hab).symm
    _ = ((∑ n ∈ Finset.Ioc a b, μ n : ℤ) : ℂ) := by
      push_cast
    _ = ((s * (sameSignNonzeroMobiusRunLength a b : ℤ) : ℤ) : ℂ) := by
      rw [sameSignNonzeroMobiusRun_sum hrun]

/-! ## All nontrivial post-root replication is middle-sector replication -/

/-- If a post-root prime admits any cofactor `c >= 2`, then it necessarily lies
below the half endpoint.  Thus every nontrivial post-root replication is in the
middle sector, never the quotient-one top sector. -/
theorem nontrivialPostRootReplication_mem_middlePrimeSet
    {R q c : ℕ}
    (hqPrime : q.Prime) (hRq : R < q)
    (hc2 : 2 ≤ c) (hcq : c * q ≤ squareRootEndpoint R) :
    q ∈ middlePrimeSet R := by
  apply mem_middlePrimeSet.mpr
  refine ⟨hRq, ?_, hqPrime⟩
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < (2 : ℕ))).2
  calc
    q * 2 = 2 * q := by omega
    _ ≤ c * q := Nat.mul_le_mul_right q hc2
    _ ≤ squareRootEndpoint R := hcq

/-- A top-sector prime has no admissible positive cofactor except `1`. -/
theorem topPrime_admissibleCofactor_eq_one
    {R q c : ℕ}
    (hqmem : q ∈ squareRootTopFibrePrimes R)
    (hc1 : 1 ≤ c) (hcq : c * q ≤ squareRootEndpoint R) :
    c = 1 := by
  have hqPrime : q.Prime := (Finset.mem_filter.mp hqmem).2
  have hcdiv : c ≤ squareRootEndpoint R / q :=
    (Nat.le_div_iff_mul_le hqPrime.pos).2 hcq
  rw [middlePrimeTop_quotient_eq_one hqmem] at hcdiv
  omega

/-- Equivalently, a top-sector prime cannot carry a nontrivial `c >= 2`
replication at all. -/
theorem topPrime_no_nontrivialReplication
    {R q c : ℕ}
    (hqmem : q ∈ squareRootTopFibrePrimes R) (hc2 : 2 ≤ c) :
    ¬ c * q ≤ squareRootEndpoint R := by
  intro hcq
  have hc1 : 1 ≤ c := by omega
  have h := topPrime_admissibleCofactor_eq_one hqmem hc1 hcq
  omega

/-! ## Exact three-state transport in each middle prime fibre -/

/-- Pointwise deterministic sign inheritance in a middle prime fibre. -/
theorem middlePrimeFibre_moebius_eq_neg
    {R q c : ℕ} (hqmem : q ∈ middlePrimeSet R)
    (hc : c ∈ Finset.Icc 1 (squareRootEndpoint R / q)) :
    μ (c * q) = -μ c := by
  rcases mem_middlePrimeSet.mp hqmem with ⟨hRq, _hqle, hqPrime⟩
  have hquotR : squareRootEndpoint R / q < R :=
    (Finset.mem_Ico.mp (middlePrime_quotient_mem_Ico hqmem)).2
  have hcData := Finset.mem_Icc.mp hc
  have hcR : c < R := hcData.2.trans_lt hquotR
  let D : LargePrimeTransportData R c q :=
    { c_pos := hcData.1
      c_lt_cutoff := hcR
      q_prime := hqPrime
      cutoff_lt_q := hRq }
  have hflip := LargePrimeTransportData.moebius_mul_eq_neg D
  simpa [Nat.mul_comm] using hflip

/-- Lower-prefix coordinates carrying one prescribed Möbius state. -/
def prefixMobiusStateSet (N : ℕ) (z : ℤ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun c => μ c = z

/-- Coordinates in one middle prime fibre carrying one prescribed final Möbius
state. -/
def middlePrimeFibreStateSet (R q : ℕ) (z : ℤ) : Finset ℕ :=
  (Finset.Icc 1 (squareRootEndpoint R / q)).filter fun c => μ (c * q) = z

/-- **Exact three-state transport.**  A middle prime does not resample the
Möbius distribution.  Its `z`-states are literally the lower-prefix `-z`
states on the same cofactor coordinates. -/
theorem middlePrimeFibreStateSet_eq_prefix_neg
    {R q : ℕ} (hqmem : q ∈ middlePrimeSet R) (z : ℤ) :
    middlePrimeFibreStateSet R q z =
      prefixMobiusStateSet (squareRootEndpoint R / q) (-z) := by
  classical
  ext c
  simp only [middlePrimeFibreStateSet, prefixMobiusStateSet,
    Finset.mem_filter]
  constructor
  · rintro ⟨hc, hz⟩
    refine ⟨hc, ?_⟩
    have hflip := middlePrimeFibre_moebius_eq_neg hqmem hc
    rw [hflip] at hz
    omega
  · rintro ⟨hc, hz⟩
    refine ⟨hc, ?_⟩
    have hflip := middlePrimeFibre_moebius_eq_neg hqmem hc
    rw [hflip, hz]
    simp

/-- Cardinal form of exact three-state transport. -/
theorem middlePrimeFibreStateCount_eq_prefix_neg
    {R q : ℕ} (hqmem : q ∈ middlePrimeSet R) (z : ℤ) :
    (middlePrimeFibreStateSet R q z).card =
      (prefixMobiusStateSet (squareRootEndpoint R / q) (-z)).card := by
  rw [middlePrimeFibreStateSet_eq_prefix_neg hqmem z]

/-- In particular, zeros are preserved exactly and the two nonzero populations
are swapped. -/
theorem middlePrimeFibre_zero_pos_neg_counts
    {R q : ℕ} (hqmem : q ∈ middlePrimeSet R) :
    (middlePrimeFibreStateSet R q 0).card =
        (prefixMobiusStateSet (squareRootEndpoint R / q) 0).card ∧
    (middlePrimeFibreStateSet R q 1).card =
        (prefixMobiusStateSet (squareRootEndpoint R / q) (-1)).card ∧
    (middlePrimeFibreStateSet R q (-1)).card =
        (prefixMobiusStateSet (squareRootEndpoint R / q) 1).card := by
  constructor
  · simpa using middlePrimeFibreStateCount_eq_prefix_neg hqmem (0 : ℤ)
  constructor
  · simpa using middlePrimeFibreStateCount_eq_prefix_neg hqmem (1 : ℤ)
  · simpa using middlePrimeFibreStateCount_eq_prefix_neg hqmem (-1 : ℤ)

/-! ## Existing non-iid compression, specialized to the middle sector -/

/-- The already-compiled dyadic compression applies to every middle prime
fibre: the full inherited prefix is exactly its odd dyadic boundary. -/
theorem middlePrime_lowCofactorMass_eq_dyadicBoundary
    {R q : ℕ} (hqmem : q ∈ middlePrimeSet R) :
    primeDilatedLowCofactorMass R q =
      dyadicPrimeFiberBoundaryMass R q := by
  rcases mem_middlePrimeSet.mp hqmem with ⟨hRq, _hqle, hqPrime⟩
  have hR : 0 < R := by omega
  exact primeDilatedLowCofactorMass_eq_dyadicPrimeFiberBoundaryMass
    R q hR hRq hqPrime.pos

end RHLean.Proof

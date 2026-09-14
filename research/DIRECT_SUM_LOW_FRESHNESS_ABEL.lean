import Mathlib
import research.DIRECT_SUM_DYADIC_DISPERSION_BRIDGE

/-!
# Low-freshness dyadic Abel transform

This module adds only exact finite algebra to the direct-sum FAR-4 bridge.
It proves that the low freshness wavelet is boundary-free after dyadic
mean-centering, in the same sense as the already-compiled high reciprocal
channel.  No dispersion, large-sieve, PNT-error, or FAR-4 estimate is asserted.
-/

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Extend one low dyadic wavelet block by zero to the whole physical support. -/
def directSumLowBlockWaveletMask (R j n : ℕ) : ℂ :=
  if n ∈ directSumLowDyadicBlock R j then directSumLowWaveletAtom R n else 0

/-- Every occupied low dyadic block has exactly zero wavelet mass. -/
theorem sum_directSumLowWaveletAtom_block_eq_zero
    {R j : ℕ} (hj : j ∈ directSumLowDyadicBlockIndices R) :
    (∑ n ∈ directSumLowDyadicBlock R j, directSumLowWaveletAtom R n) = 0 := by
  classical
  rcases Finset.mem_image.mp hj with ⟨n, hn, hidx⟩
  have hnB : n ∈ directSumLowDyadicBlock R j := by
    simp [directSumLowDyadicBlock, hn, hidx]
  have hcardNat : 0 < (directSumLowDyadicBlock R j).card :=
    Finset.card_pos.mpr ⟨n, hnB⟩
  have hcard : (((directSumLowDyadicBlock R j).card : ℂ)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hcardNat)
  have hreindex :
      (∑ m ∈ directSumLowDyadicBlock R j, directSumLowWaveletAtom R m) =
        ∑ m ∈ directSumLowDyadicBlock R j,
          (directSumLowPrimeErrorAtom m - directSumLowDyadicBlockMean R j) := by
    apply Finset.sum_congr rfl
    intro m hm
    have hm0 := hm
    simp [directSumLowDyadicBlock] at hm0
    simp [directSumLowWaveletAtom, hm0.2]
  rw [hreindex, Finset.sum_sub_distrib]
  have hconst :
      (∑ _m ∈ directSumLowDyadicBlock R j, directSumLowDyadicBlockMean R j) =
        ((directSumLowDyadicBlock R j).card : ℂ) * directSumLowDyadicBlockMean R j := by
    simp [nsmul_eq_mul]
  rw [hconst]
  unfold directSumLowDyadicBlockMean
  field_simp [hcard]
  ring

/-- The low wavelet mask has zero mass on the complete physical support. -/
theorem sum_directSumLowBlockWaveletMask_eq_zero
    {R j : ℕ} (hj : j ∈ directSumLowDyadicBlockIndices R) :
    (∑ n ∈ Finset.Icc 2 R, directSumLowBlockWaveletMask R j n) = 0 := by
  classical
  have hblock := sum_directSumLowWaveletAtom_block_eq_zero (R := R) (j := j) hj
  have hfilter :
      (Finset.Icc 2 R).filter (fun n => n ∈ directSumLowDyadicBlock R j) =
        directSumLowDyadicBlock R j := by
    ext n
    simp [directSumLowDyadicBlock]
  unfold directSumLowBlockWaveletMask
  rw [← Finset.sum_filter, hfilter]
  exact hblock

/-- Negative prefix of one masked low dyadic block on the physical support. -/
def directSumLowMaskedAbelPotential (R j n : ℕ) : ℂ :=
  -∑ t ∈ Finset.Icc 2 (n - 1), directSumLowBlockWaveletMask R j t

/-- The masked potential agrees with the potential already used by the direct-sum energy. -/
theorem directSumLowMaskedAbelPotential_eq_energyPotential
    {R j n : ℕ} (hn : n ∈ Finset.Icc 2 R) :
    directSumLowMaskedAbelPotential R j n = directSumLowBlockAbelPotential R j n := by
  classical
  unfold directSumLowMaskedAbelPotential directSumLowBlockAbelPotential
    directSumLowBlockWaveletMask
  rw [← Finset.sum_filter]
  apply congrArg Neg.neg
  apply Finset.sum_congr
  · ext t
    simp [directSumLowDyadicBlock]
    omega
  · intro t ht
    simp only [Finset.mem_filter] at ht
    simp [ht.2]

/-- On the complete physical support, the low Abel potential has the masked
wavelet as its forward difference. -/
theorem directSumLowMaskedAbelPotential_forwardDifference
    {R j n : ℕ} (hn : n ∈ Finset.Icc 2 R) :
    directSumLowMaskedAbelPotential R j n -
        directSumLowMaskedAbelPotential R j (n + 1) =
      directSumLowBlockWaveletMask R j n := by
  have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
  have hpred : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
  have hsum :
      (∑ t ∈ Finset.Icc 2 n, directSumLowBlockWaveletMask R j t) =
        (∑ t ∈ Finset.Icc 2 (n - 1), directSumLowBlockWaveletMask R j t) +
          directSumLowBlockWaveletMask R j n := by
    rw [← hpred]
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ n - 1 + 1)]
    have hback : n - 1 + 1 - 1 = n - 1 := by omega
    rw [hback]
  unfold directSumLowMaskedAbelPotential
  rw [show n + 1 - 1 = n by omega, hsum]
  ring

/-- The terminal low Abel potential vanishes exactly on every occupied block. -/
theorem directSumLowMaskedAbelPotential_top_eq_zero
    {R j : ℕ} (hj : j ∈ directSumLowDyadicBlockIndices R) :
    directSumLowMaskedAbelPotential R j (R + 1) = 0 := by
  have hzero := sum_directSumLowBlockWaveletMask_eq_zero (R := R) (j := j) hj
  unfold directSumLowMaskedAbelPotential
  rw [show R + 1 - 1 = R by omega, hzero]
  simp

/-- Discrete Abel summation from the physical lower endpoint `2`. -/
private theorem sum_Icc_two_add_mul_forwardDifference
    (P G : ℕ → ℂ) : ∀ k : ℕ,
    (∑ n ∈ Finset.Icc 2 (k + 2), (P n - P (n + 1)) * G n) =
      P 2 * G 2 - P (k + 3) * G (k + 2) +
        ∑ n ∈ Finset.Icc 3 (k + 2), P n * (G n - G (n - 1)) := by
  intro k
  induction k with
  | zero =>
      simp
      ring
  | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ k + 3),
        Finset.sum_Icc_succ_top (by omega : 3 ≤ k + 3), ih]
      ring

/-- One occupied low dyadic block has a boundary-free Abel identity against the
freshness shell. -/
theorem directSumLowBlockWaveletContribution_eq_boundaryFreeAbel
    {R j : ℕ} (hR : 2 ≤ R) (hj : j ∈ directSumLowDyadicBlockIndices R) :
    (∑ n ∈ Finset.Icc 2 R,
      directSumLowBlockWaveletMask R j n * directSumLowFreshnessShell R n) =
      ∑ n ∈ Finset.Icc 3 R,
        directSumLowMaskedAbelPotential R j n *
          (directSumLowFreshnessShell R n - directSumLowFreshnessShell R (n - 1)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hR
  have htop := directSumLowMaskedAbelPotential_top_eq_zero (R := k + 2) (j := j) hj
  have hbot : directSumLowMaskedAbelPotential (k + 2) j 2 = 0 := by
    unfold directSumLowMaskedAbelPotential
    simp
  have habel := sum_Icc_two_add_mul_forwardDifference
    (fun n => directSumLowMaskedAbelPotential (k + 2) j n)
    (fun n => directSumLowFreshnessShell (k + 2) n) k
  have hfd : ∀ n ∈ Finset.Icc 2 (k + 2),
      directSumLowBlockWaveletMask (k + 2) j n =
        directSumLowMaskedAbelPotential (k + 2) j n -
          directSumLowMaskedAbelPotential (k + 2) j (n + 1) := by
    intro n hn
    exact (directSumLowMaskedAbelPotential_forwardDifference hn).symm
  calc
    (∑ n ∈ Finset.Icc 2 (k + 2),
        directSumLowBlockWaveletMask (k + 2) j n *
          directSumLowFreshnessShell (k + 2) n) =
      ∑ n ∈ Finset.Icc 2 (k + 2),
        (directSumLowMaskedAbelPotential (k + 2) j n -
          directSumLowMaskedAbelPotential (k + 2) j (n + 1)) *
            directSumLowFreshnessShell (k + 2) n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hfd n hn]
    _ = directSumLowMaskedAbelPotential (k + 2) j 2 *
          directSumLowFreshnessShell (k + 2) 2 -
        directSumLowMaskedAbelPotential (k + 2) j (k + 3) *
          directSumLowFreshnessShell (k + 2) (k + 2) +
        ∑ n ∈ Finset.Icc 3 (k + 2),
          directSumLowMaskedAbelPotential (k + 2) j n *
            (directSumLowFreshnessShell (k + 2) n -
              directSumLowFreshnessShell (k + 2) (n - 1)) := habel
    _ = ∑ n ∈ Finset.Icc 3 (k + 2),
          directSumLowMaskedAbelPotential (k + 2) j n *
            (directSumLowFreshnessShell (k + 2) n -
              directSumLowFreshnessShell (k + 2) (n - 1)) := by
      rw [hbot, htop]
      ring

/-- The complete low freshness wavelet is the sum of its occupied dyadic block
contributions. -/
theorem directSumLowWavelet_eq_sum_blockContributions (R : ℕ) :
    directSumLowWavelet R =
      ∑ j ∈ directSumLowDyadicBlockIndices R,
        ∑ n ∈ Finset.Icc 2 R,
          directSumLowBlockWaveletMask R j n * directSumLowFreshnessShell R n := by
  classical
  unfold directSumLowWavelet
  calc
    (∑ n ∈ Finset.Icc 2 R,
        directSumLowWaveletAtom R n * directSumLowFreshnessShell R n) =
      ∑ n ∈ Finset.Icc 2 R,
        (∑ j ∈ directSumLowDyadicBlockIndices R,
          directSumLowBlockWaveletMask R j n) * directSumLowFreshnessShell R n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hj : primeSieveDyadicIndex n ∈ directSumLowDyadicBlockIndices R :=
        Finset.mem_image.mpr ⟨n, hn, rfl⟩
      rw [Finset.sum_eq_single (primeSieveDyadicIndex n)]
      · simp [directSumLowBlockWaveletMask, directSumLowDyadicBlock, hn]
      · intro j _hj hne
        have hidxne : primeSieveDyadicIndex n ≠ j := Ne.symm hne
        simp [directSumLowBlockWaveletMask, directSumLowDyadicBlock, hn, hidxne]
      · intro hnot
        exact False.elim (hnot hj)
    _ = ∑ n ∈ Finset.Icc 2 R,
        ∑ j ∈ directSumLowDyadicBlockIndices R,
          directSumLowBlockWaveletMask R j n * directSumLowFreshnessShell R n := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [Finset.sum_mul]
    _ = ∑ j ∈ directSumLowDyadicBlockIndices R,
        ∑ n ∈ Finset.Icc 2 R,
          directSumLowBlockWaveletMask R j n * directSumLowFreshnessShell R n := by
      rw [Finset.sum_comm]

/-- **Boundary-free Abel representation of the complete low freshness wavelet.**
This is the exact low-channel analogue of
`primeSieveDyadicWaveletPNTError_eq_boundaryFreeAbel`. -/
theorem directSumLowWavelet_eq_boundaryFreeAbel
    (R : ℕ) (hR : 2 ≤ R) :
    directSumLowWavelet R =
      ∑ j ∈ directSumLowDyadicBlockIndices R,
        ∑ n ∈ Finset.Icc 3 R,
          directSumLowMaskedAbelPotential R j n *
            (directSumLowFreshnessShell R n - directSumLowFreshnessShell R (n - 1)) := by
  rw [directSumLowWavelet_eq_sum_blockContributions]
  apply Finset.sum_congr rfl
  intro j hj
  exact directSumLowBlockWaveletContribution_eq_boundaryFreeAbel hR hj

end RHLean.Proof

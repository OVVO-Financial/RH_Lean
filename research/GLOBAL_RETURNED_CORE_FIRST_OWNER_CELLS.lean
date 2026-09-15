import Mathlib
import «research.GLOBAL_RETURNED_CORE_FIRST_OWNER_GRAM»

/-!
# First-owner Gram cells on the actual AMP amplitude

The exact AMP square is already partitioned by the least prime at which two
squarefree sites differ.  This file exposes the corresponding lower-prime cell.
Inside one such cell, the owner `p` only separates the p-free branch from the
p-divisible branch.  The mixed covariance is therefore one product of branch
amplitudes, and after stripping `p` its complete part has the universal
amplitude-before-energy bound

  -L * P <= (L - P)^2 / 4.

No estimate on a Mobius partial sum is used here.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Prime coordinates strictly below `p` carried by one squarefree site. -/
def squarefreeLowerPrimeSignature (p n : ℕ) : Finset ℕ :=
  (squarefreePrimeFace n).filter fun q => q < p

private theorem prime_mem_squarefreePrimeFace_iff_dvd
    {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    p ∈ squarefreePrimeFace n ↔ p ∣ n := by
  constructor
  · intro hmem
    have hpf : p ∈ n.primeFactors := by
      simpa [squarefreePrimeFace] using hmem
    exact Nat.dvd_of_mem_primeFactors hpf
  · intro hdiv
    have hpf : p ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hdiv, hn.ne'⟩
    simpa [squarefreePrimeFace] using hpf

/-- An intrinsic first owner forces equality of every lower-prime signature. -/
theorem squarefreeLowerPrimeSignature_eq_of_firstOwner
    {p m n : ℕ} (hm : Squarefree m) (hn : Squarefree n) (hmn : m ≠ n)
    (howner : IsSquarefreePairFreshPrimeOwner p m n) :
    squarefreeLowerPrimeSignature p m = squarefreeLowerPrimeSignature p n := by
  have hcanon := squarefreePairFreshPrimeOwner_isOwner hm hn hmn
  have hp_le : p ≤ squarefreePairFreshPrimeOwner m n :=
    howner.2 _ hcanon.1
  have hcanon_le : squarefreePairFreshPrimeOwner m n ≤ p :=
    hcanon.2 _ howner.1
  have hpEq : p = squarefreePairFreshPrimeOwner m n := by omega
  ext q
  by_cases hqp : q < p
  · have hqcanon : q < squarefreePairFreshPrimeOwner m n := by
      simpa [← hpEq] using hqp
    have hchron := squarefreePairFreshPrimeOwner_chronology hm hn hmn hqcanon
    simp [squarefreeLowerPrimeSignature, hqp, hchron]
  · simp [squarefreeLowerPrimeSignature, hqp]

/-- Conversely, for squarefree sites, equality below `p` together with an xor
at `p` says exactly that `p` is the first separating owner. -/
theorem firstOwner_of_lowerSignature_eq_and_dvd_xor
    {p m n : ℕ} (hp : p.Prime) (hm : Squarefree m) (hn : Squarefree n)
    (hmpos : 0 < m) (hnpos : 0 < n)
    (hsig : squarefreeLowerPrimeSignature p m =
      squarefreeLowerPrimeSignature p n)
    (hxor : (p ∣ m ∧ ¬ p ∣ n) ∨ (p ∣ n ∧ ¬ p ∣ m)) :
    IsSquarefreePairFreshPrimeOwner p m n := by
  have hpm : p ∈ squarefreePrimeFace m ↔ p ∣ m :=
    prime_mem_squarefreePrimeFace_iff_dvd hp hmpos
  have hpn : p ∈ squarefreePrimeFace n ↔ p ∣ n :=
    prime_mem_squarefreePrimeFace_iff_dvd hp hnpos
  have hdiff : p ∈ squarefreePairFreshPrimeSet m n := by
    rcases hxor with h | h
    · have hpmem : p ∈ squarefreePrimeFace m := hpm.mpr h.1
      have hpnot : p ∉ squarefreePrimeFace n := by
        intro hmem
        exact h.2 (hpn.mp hmem)
      simp [squarefreePairFreshPrimeSet, hpmem, hpnot]
    · have hpnmem : p ∈ squarefreePrimeFace n := hpn.mpr h.1
      have hpnot : p ∉ squarefreePrimeFace m := by
        intro hmem
        exact h.2 (hpm.mp hmem)
      simp [squarefreePairFreshPrimeSet, hpnmem, hpnot]
  refine ⟨hdiff, ?_⟩
  intro q hq
  by_contra hqp
  have hqLt : q < p := by omega
  have hqm : q ∈ squarefreePrimeFace m ↔
      q ∈ squarefreeLowerPrimeSignature p m := by
    simp [squarefreeLowerPrimeSignature, hqLt]
  have hqn : q ∈ squarefreePrimeFace n ↔
      q ∈ squarefreeLowerPrimeSignature p n := by
    simp [squarefreeLowerPrimeSignature, hqLt]
  have hsame : q ∈ squarefreePrimeFace m ↔ q ∈ squarefreePrimeFace n := by
    rw [hqm, hqn, hsig]
  have hqdiff :
      (q ∈ squarefreePrimeFace m ∧ q ∉ squarefreePrimeFace n) ∨
        (q ∈ squarefreePrimeFace n ∧ q ∉ squarefreePrimeFace m) := by
    simpa [squarefreePairFreshPrimeSet] using hq
  rcases hqdiff with h | h
  · exact h.2 (hsame.mp h.1)
  · exact h.2 (hsame.mpr h.1)

/-- Nonzero Mobius sites on the common physical clock. -/
def lowOwnerNonzeroMobiusCarrier (R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (squareRootEndpoint R)).filter fun n =>
    realMoebiusStep n ≠ 0

/-- Lower-signature cells actually occupied at the endpoint. -/
def lowOwnerFirstOwnerSignatureSet (R p : ℕ) : Finset (Finset ℕ) :=
  (lowOwnerNonzeroMobiusCarrier R).image (squarefreeLowerPrimeSignature p)

/-- p-free side of one lower-signature cell. -/
def lowOwnerFirstOwnerBaseFiber
    (R p : ℕ) (sig : Finset ℕ) : Finset ℕ :=
  (lowOwnerNonzeroMobiusCarrier R).filter fun n =>
    squarefreeLowerPrimeSignature p n = sig ∧ ¬ p ∣ n

/-- p-divisible side of the same lower-signature cell. -/
def lowOwnerFirstOwnerChildFiber
    (R p : ℕ) (sig : Finset ℕ) : Finset ℕ :=
  (lowOwnerNonzeroMobiusCarrier R).filter fun n =>
    squarefreeLowerPrimeSignature p n = sig ∧ p ∣ n

/-- Actual AMP amplitude on the p-free side of one first-owner cell. -/
def lowOwnerFirstOwnerBaseAmplitude
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  ∑ n ∈ lowOwnerFirstOwnerBaseFiber R p sig,
    lowOwnerZeroFrequencyMobiusSite R n

/-- Actual AMP amplitude on the p-divisible side of one first-owner cell. -/
def lowOwnerFirstOwnerChildAmplitude
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  ∑ n ∈ lowOwnerFirstOwnerChildFiber R p sig,
    lowOwnerZeroFrequencyMobiusSite R n

/-- The mixed covariance of a first-owner cell is the product of its two branch
amplitudes. -/
def lowOwnerFirstOwnerCellGram
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  lowOwnerFirstOwnerBaseAmplitude R p sig *
    lowOwnerFirstOwnerChildAmplitude R p sig

/-- Pure algebra behind the complete-cell estimate.  If the p-divisible branch
is written as `-P`, then its mixed covariance with the p-free branch `L` is
`-L*P`, bounded by one quarter of the complete owner-difference amplitude. -/
theorem neg_mul_le_quarter_sub_sq (L P : ℝ) :
    -L * P ≤ (1 / 4 : ℝ) * (L - P) ^ 2 := by
  nlinarith [sq_nonneg (L + P)]

/-- Equivalent branch form: `A*B` is controlled by one quarter of the square of
the complete two-branch amplitude `A+B`. -/
theorem mul_le_quarter_add_sq_of_second_neg
    (A P : ℝ) :
    A * (-P) ≤ (1 / 4 : ℝ) * (A - P) ^ 2 := by
  simpa using neg_mul_le_quarter_sub_sq A P

end RHLean.Proof

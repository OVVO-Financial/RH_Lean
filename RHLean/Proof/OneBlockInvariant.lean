import Mathlib
import RHLean.Arithmetic.SquareBlockParityPopulation
import RHLean.Proof.CanonicalSignedParent

/-!
# One-block invariant architecture (issue #146)

This module makes the governing finite induction architecture explicit.

The completed prefix is represented by the exact recursive sum of square-block
increments. The next block is not treated as independent: its nonzero
squarefree states are inherited from canonical full-factorization parents in
the already-frozen carrier. The quantitative estimate is kept as an explicit
field of the invariant rather than silently assumed.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- Old frozen parent cutoff used by issue #146 for target square block `a`. -/
def oldParentCutoff (a : ℕ) : ℕ :=
  (a ^ 2 - 1) / 2

/-- Every prime factor is bounded by the canonical largest prime factor. -/
theorem primeFactor_le_canonicalLargestPrimeFactor
    {n p : ℕ} (hn : 1 < n) (hp : p ∈ n.primeFactors) :
    p ≤ canonicalLargestPrimeFactor n := by
  unfold canonicalLargestPrimeFactor
  rw [dif_pos hn]
  exact Finset.le_max' n.primeFactors p hp

/-- Above `2`, the canonical largest prime factor is at least `3`. -/
theorem three_le_canonicalLargestPrimeFactor
    {n : ℕ} (hsq : Squarefree n) (hn : 2 < n) :
    3 ≤ canonicalLargestPrimeFactor n := by
  have hn1 : 1 < n := by omega
  have hqPrime := canonicalLargestPrimeFactor_prime hn1
  have hqTwo : 2 ≤ canonicalLargestPrimeFactor n := hqPrime.two_le
  by_contra hcontra
  have hqEq : canonicalLargestPrimeFactor n = 2 := by omega
  have hfaces : n.primeFactors = {2} := by
    ext p
    constructor
    · intro hp
      have hpPrime : p.Prime := (Nat.mem_primeFactors.mp hp).1
      have hpLe : p ≤ canonicalLargestPrimeFactor n :=
        primeFactor_le_canonicalLargestPrimeFactor hn1 hp
      have hpEq : p = 2 := by omega
      simpa [hpEq]
    · intro hp
      have hpEq : p = 2 := by simpa using hp
      subst p
      simpa [hqEq] using canonicalLargestPrimeFactor_mem_primeFactors hn1
  have hprod := Nat.prod_primeFactors_of_squarefree hsq
  rw [hfaces] at hprod
  simp at hprod
  omega

/-- The two small post-seed blocks satisfy the old-carrier bound directly. -/
theorem canonicalCofactor_le_oldParentCutoff_three :
    ∀ n : ℕ, n ∈ squareBlockInterval 3 → Squarefree n → 1 < n →
      canonicalCofactor n ≤ oldParentCutoff 3 := by
  native_decide

/-- The second small post-seed block satisfies the old-carrier bound directly. -/
theorem canonicalCofactor_le_oldParentCutoff_four :
    ∀ n : ℕ, n ∈ squareBlockInterval 4 → Squarefree n → 1 < n →
      canonicalCofactor n ≤ oldParentCutoff 4 := by
  native_decide

/-- **Uniform prior-carrier theorem.** For every square block from `a = 3`
onward, the canonical cofactor of each squarefree state already lies in the
frozen old parent carrier.

The proof uses the canonical largest prime factor `q`. For `n > 2`, `q ≥ 3`, so
`3c ≤ n < (a+1)²`. From `a ≥ 5`, the elementary comparison
`2(a+1)² ≤ 3a²` gives `2c < a²`, hence `c ≤ (a²-1)/2`. Blocks `3` and `4` are
the finite post-seed base cases. -/
theorem canonicalCofactor_le_oldParentCutoff
    {a n : ℕ} (ha : 3 ≤ a)
    (hn : n ∈ squareBlockInterval a)
    (hsq : Squarefree n) (hn1 : 1 < n) :
    canonicalCofactor n ≤ oldParentCutoff a := by
  rcases lt_trichotomy a 5 with haLt | haEq | haGt
  · have haCases : a = 3 ∨ a = 4 := by omega
    rcases haCases with rfl | rfl
    · exact canonicalCofactor_le_oldParentCutoff_three n hn hsq hn1
    · exact canonicalCofactor_le_oldParentCutoff_four n hn hsq hn1
  · subst a
    have hnBounds : 5 ^ 2 ≤ n ∧ n < (5 + 1) ^ 2 := by
      simpa [squareBlockInterval, Finset.mem_Ico] using hn
    have hn2 : 2 < n := by omega
    have hq3 : 3 ≤ canonicalLargestPrimeFactor n :=
      three_le_canonicalLargestPrimeFactor hsq hn2
    have hprod := canonicalCofactor_mul_largestPrimeFactor hn1
    have hthree : 3 * canonicalCofactor n ≤ n := by
      calc
        3 * canonicalCofactor n = canonicalCofactor n * 3 := by omega
        _ ≤ canonicalCofactor n * canonicalLargestPrimeFactor n :=
          Nat.mul_le_mul_left _ hq3
        _ = n := hprod
    change canonicalCofactor n ≤ (5 ^ 2 - 1) / 2
    omega
  · have ha5 : 5 ≤ a := by omega
    have hnBounds : a ^ 2 ≤ n ∧ n < (a + 1) ^ 2 := by
      simpa [squareBlockInterval, Finset.mem_Ico] using hn
    have hn2 : 2 < n := by
      have : 9 ≤ a ^ 2 := by nlinarith
      omega
    have hq3 : 3 ≤ canonicalLargestPrimeFactor n :=
      three_le_canonicalLargestPrimeFactor hsq hn2
    have hprod := canonicalCofactor_mul_largestPrimeFactor hn1
    have hthree : 3 * canonicalCofactor n ≤ n := by
      calc
        3 * canonicalCofactor n = canonicalCofactor n * 3 := by omega
        _ ≤ canonicalCofactor n * canonicalLargestPrimeFactor n :=
          Nat.mul_le_mul_left _ hq3
        _ = n := hprod
    have h5a : 5 * a ≤ a * a := Nat.mul_le_mul_right a ha5
    have hquad : 4 * a + 2 ≤ a ^ 2 := by
      rw [pow_two]
      omega
    have hscale : 2 * (a + 1) ^ 2 ≤ 3 * a ^ 2 := by
      nlinarith
    have htwoLt : 2 * canonicalCofactor n < a ^ 2 := by
      nlinarith
    have htwoLe : canonicalCofactor n * 2 ≤ a ^ 2 - 1 := by
      omega
    exact (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2 htwoLe

/-- Full-factorization inheritance statement for one square block. -/
def PriorCarrierDeterminesBlock (a : ℕ) : Prop :=
  ∀ n : ℕ, n ∈ squareBlockInterval a → Squarefree n → 1 < n →
    canonicalCofactor n ≤ oldParentCutoff a ∧
    μ n = -μ (canonicalCofactor n) ∧
    (FullFactorizationState.canonical n).omega =
      (FullFactorizationState.canonical (canonicalCofactor n)).omega + 1

/-- Once the elementary parent-cutoff estimate is available, all sign and parity
parts of one-block inheritance follow from the merged full-factorization bridge. -/
theorem priorCarrierDeterminesBlock_of_parent_bound
    {a : ℕ}
    (hbound : ∀ n : ℕ, n ∈ squareBlockInterval a → Squarefree n → 1 < n →
      canonicalCofactor n ≤ oldParentCutoff a) :
    PriorCarrierDeterminesBlock a := by
  intro n hn hsq hn1
  exact ⟨hbound n hn hsq hn1,
    canonicalSignedParent_moebius hsq hn1,
    canonicalSignedParent_omega_succ hsq hn1⟩

/-- Every post-seed square block is completely determined by the frozen prior
carrier, with signs and parity read from complete factorization states. -/
theorem priorCarrierDeterminesBlock
    {a : ℕ} (ha : 3 ≤ a) : PriorCarrierDeterminesBlock a :=
  priorCarrierDeterminesBlock_of_parent_bound
    (fun n hn hsq hn1 => canonicalCofactor_le_oldParentCutoff ha hn hsq hn1)

/-- Exact cumulative discrepancy after the first `N` square blocks. -/
def completedBlockPrefixSum : ℕ → ℤ
  | 0 => 0
  | N + 1 => completedBlockPrefixSum N + squareBlockMoebius (N + 1)

@[simp] theorem completedBlockPrefixSum_zero : completedBlockPrefixSum 0 = 0 := rfl

@[simp] theorem completedBlockPrefixSum_succ (N : ℕ) :
    completedBlockPrefixSum (N + 1) =
      completedBlockPrefixSum N + squareBlockMoebius (N + 1) := rfl

/-- The finite state that issue #146 requires at stage `N`. -/
structure OneBlockInvariant (N : ℕ) where
  nextBlockInherited : PriorCarrierDeterminesBlock (N + 1)
  signedFrontier : ℤ
  signedFrontier_eq_prefix : signedFrontier = completedBlockPrefixSum N
  energyBudget : ℕ
  energy_control : signedFrontier ^ 2 ≤ (energyBudget : ℤ)

/-- Exact data needed to extend a valid stage by one finite block. -/
structure OneBlockExtensionData (N : ℕ) (hN : OneBlockInvariant N) where
  followingBlockInherited : PriorCarrierDeterminesBlock (N + 2)
  nextSignedFrontier : ℤ
  frontier_update :
    nextSignedFrontier = hN.signedFrontier + squareBlockMoebius (N + 1)
  nextEnergyBudget : ℕ
  next_energy_control : nextSignedFrontier ^ 2 ≤ (nextEnergyBudget : ℤ)

/-- The exact one-block extension constructor demanded by issue #146. -/
def oneBlockInvariant_succ
    {N : ℕ} (hN : OneBlockInvariant N)
    (hstep : OneBlockExtensionData N hN) :
    OneBlockInvariant (N + 1) where
  nextBlockInherited := hstep.followingBlockInherited
  signedFrontier := hstep.nextSignedFrontier
  signedFrontier_eq_prefix := by
    calc
      hstep.nextSignedFrontier =
          hN.signedFrontier + squareBlockMoebius (N + 1) := hstep.frontier_update
      _ = completedBlockPrefixSum N + squareBlockMoebius (N + 1) := by
          rw [hN.signedFrontier_eq_prefix]
      _ = completedBlockPrefixSum (N + 1) := by
          rw [completedBlockPrefixSum_succ]
  energyBudget := hstep.nextEnergyBudget
  energy_control := hstep.next_energy_control

/-- Uniform one-block law: every valid finite stage admits valid extension data. -/
def OneBlockExtensionLaw : Prop :=
  ∀ N : ℕ, ∀ hN : OneBlockInvariant N,
    Nonempty (OneBlockExtensionData N hN)

/-- A base invariant plus the uniform one-block law yields every finite stage by
ordinary induction. No completed infinity is used. -/
theorem oneBlockInvariant_all
    (h0 : OneBlockInvariant 0)
    (hlaw : OneBlockExtensionLaw) :
    ∀ N : ℕ, Nonempty (OneBlockInvariant N) := by
  intro N
  induction N with
  | zero => exact ⟨h0⟩
  | succ N ih =>
      obtain ⟨hN⟩ := ih
      obtain ⟨hstep⟩ := hlaw N hN
      exact ⟨oneBlockInvariant_succ hN hstep⟩

/-- The precise unresolved theorem package for issue #146. -/
def OneBlockInvariantClosureStatement : Prop :=
  Nonempty (OneBlockInvariant 0) ∧ OneBlockExtensionLaw

end RHLean.Proof

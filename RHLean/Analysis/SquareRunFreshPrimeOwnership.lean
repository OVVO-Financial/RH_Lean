import Mathlib
import RHLean.Analysis.SquareRunEscapeCovariance
import RHLean.Arithmetic.SquarefreePrimeFaceSurjectivity

open scoped ArithmeticFunction.Moebius BigOperators

/-!
# Canonical fresh-prime ownership of square-run covariance atoms

A nonzero Mobius covariance atom is a pair of distinct squarefree integers.
Represent each endpoint by its unique canonical prime face.  The first prime at
which those two faces differ is the unique chronological owner of the pair.

This is the literal Euler chronology needed by the fresh-prime pair-cube layer:
all smaller prime coordinates agree, the owner occurs in exactly one endpoint,
and hence it is fresh after erasing it from that endpoint.  No pair can be
owned by two primes.
-/

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- The exact positive-lag pair sum in a physical interval `[A,B)`. -/
def signedBlockIcoPairCovariance (w : ℕ → ℝ) (A B : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico A B,
    ∑ m ∈ Finset.Ico A n, w m * w n

@[simp] theorem signedBlockIcoPairCovariance_self
    (w : ℕ → ℝ) (A : ℕ) :
    signedBlockIcoPairCovariance w A A = 0 := by
  simp [signedBlockIcoPairCovariance]

private theorem signedBlockIcoPairCovariance_succ_top
    (w : ℕ → ℝ) {A B : ℕ} (hAB : A ≤ B) :
    signedBlockIcoPairCovariance w A (B + 1) =
      signedBlockIcoPairCovariance w A B +
        w B * (signedBlockPrefix w B - signedBlockPrefix w A) := by
  unfold signedBlockIcoPairCovariance
  rw [Finset.sum_Ico_succ_top hAB]
  have hsum := Finset.sum_Ico_eq_sub w hAB
  unfold signedBlockPrefix at hsum ⊢
  rw [Finset.sum_mul, hsum]
  ring

private theorem signedBlockInnerCovariance_succ_top
    (w : ℕ → ℝ) {A B : ℕ} (hAB : A ≤ B) :
    signedBlockInnerCovariance w A (B + 1) =
      signedBlockInnerCovariance w A B +
        w B * (signedBlockPrefix w B - signedBlockPrefix w A) := by
  unfold signedBlockInnerCovariance
  rw [signedBlockCrossCovariance_succ, signedBlockPrefix_succ]
  ring

/-- The prefix-difference definition of window covariance is literally the sum
of the physical unordered pairs inside that window. -/
theorem signedBlockInnerCovariance_eq_icoPairCovariance
    (w : ℕ → ℝ) {A B : ℕ} (hAB : A ≤ B) :
    signedBlockInnerCovariance w A B =
      signedBlockIcoPairCovariance w A B := by
  induction B, hAB using Nat.le_induction with
  | base =>
      simp [signedBlockInnerCovariance]
  | succ B hAB ih =>
      rw [signedBlockInnerCovariance_succ_top w hAB,
        signedBlockIcoPairCovariance_succ_top w hAB, ih]

/-- The square-run covariance therefore has its literal physical pair carrier. -/
theorem squareRunCovariance_eq_icoPairCovariance
    {a b : ℕ} (hab : a ≤ b) :
    squareRunCovariance a b =
      signedBlockIcoPairCovariance realMoebiusStep
        (a ^ 2) ((b + 1) ^ 2) := by
  unfold squareRunCovariance
  apply signedBlockInnerCovariance_eq_icoPairCovariance
  exact Nat.pow_le_pow_left (by omega) 2

/-- Prime coordinates on which the canonical squarefree faces of `m` and `n`
differ. -/
def squarefreePairFreshPrimeSet (m n : ℕ) : Finset ℕ :=
  (squarefreePrimeFace m \ squarefreePrimeFace n) ∪
    (squarefreePrimeFace n \ squarefreePrimeFace m)

/-- Distinct squarefree integers differ in at least one prime coordinate. -/
theorem squarefreePairFreshPrimeSet_nonempty
    {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n) (hmn : m ≠ n) :
    (squarefreePairFreshPrimeSet m n).Nonempty := by
  by_contra hnone
  have hempty : squarefreePairFreshPrimeSet m n = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hnone
  have hfaces : squarefreePrimeFace m = squarefreePrimeFace n := by
    ext p
    by_cases hpm : p ∈ squarefreePrimeFace m
    · have hpn : p ∈ squarefreePrimeFace n := by
        by_contra hpnot
        have hmem : p ∈ squarefreePairFreshPrimeSet m n := by
          simp [squarefreePairFreshPrimeSet, hpm, hpnot]
        rw [hempty] at hmem
        simp at hmem
      simp [hpm, hpn]
    · have hpn : p ∉ squarefreePrimeFace n := by
        intro hpn
        have hmem : p ∈ squarefreePairFreshPrimeSet m n := by
          simp [squarefreePairFreshPrimeSet, hpm, hpn]
        rw [hempty] at hmem
        simp at hmem
      simp [hpm, hpn]
  apply hmn
  have hprod := congrArg primeFaceProduct hfaces
  simpa [primeFaceProduct_squarefreePrimeFace hm,
    primeFaceProduct_squarefreePrimeFace hn] using hprod

/-- Canonical chronological owner: the least prime coordinate at which the two
squarefree faces differ.  The default `1` is used only off the contributing
carrier. -/
def squarefreePairFreshPrimeOwner (m n : ℕ) : ℕ :=
  if h : (squarefreePairFreshPrimeSet m n).Nonempty then
    (squarefreePairFreshPrimeSet m n).min' h
  else 1

/-- The canonical owner is one of the differing prime coordinates. -/
theorem squarefreePairFreshPrimeOwner_mem
    {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n) (hmn : m ≠ n) :
    squarefreePairFreshPrimeOwner m n ∈ squarefreePairFreshPrimeSet m n := by
  have hne := squarefreePairFreshPrimeSet_nonempty hm hn hmn
  unfold squarefreePairFreshPrimeOwner
  rw [dif_pos hne]
  exact Finset.min'_mem _ hne

/-- Membership in the owner set means exactly one endpoint carries that prime. -/
theorem squarefreePairFreshPrimeOwner_xor
    {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n) (hmn : m ≠ n) :
    (squarefreePairFreshPrimeOwner m n ∈ squarefreePrimeFace m ∧
      squarefreePairFreshPrimeOwner m n ∉ squarefreePrimeFace n) ∨
    (squarefreePairFreshPrimeOwner m n ∈ squarefreePrimeFace n ∧
      squarefreePairFreshPrimeOwner m n ∉ squarefreePrimeFace m) := by
  have hmem := squarefreePairFreshPrimeOwner_mem hm hn hmn
  simpa [squarefreePairFreshPrimeSet] using hmem

/-- The canonical owner is a genuine prime. -/
theorem squarefreePairFreshPrimeOwner_prime
    {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n) (hmn : m ≠ n) :
    (squarefreePairFreshPrimeOwner m n).Prime := by
  rcases squarefreePairFreshPrimeOwner_xor hm hn hmn with h | h
  · have hp := Nat.mem_primeFactors.mp (by
      simpa [squarefreePrimeFace] using h.1)
    exact hp.1
  · have hp := Nat.mem_primeFactors.mp (by
      simpa [squarefreePrimeFace] using h.1)
    exact hp.1

/-- Every earlier prime coordinate agrees in the two canonical faces. -/
theorem squarefreePairFreshPrimeOwner_chronology
    {m n q : ℕ} (hm : Squarefree m) (hn : Squarefree n) (hmn : m ≠ n)
    (hq : q < squarefreePairFreshPrimeOwner m n) :
    (q ∈ squarefreePrimeFace m ↔ q ∈ squarefreePrimeFace n) := by
  have hne := squarefreePairFreshPrimeSet_nonempty hm hn hmn
  unfold squarefreePairFreshPrimeOwner at hq
  rw [dif_pos hne] at hq
  by_contra hiff
  have hdiff : q ∈ squarefreePairFreshPrimeSet m n := by
    by_cases hqm : q ∈ squarefreePrimeFace m
    · have hqn : q ∉ squarefreePrimeFace n := by
        intro hqn
        exact hiff (by simp [hqm, hqn])
      simp [squarefreePairFreshPrimeSet, hqm, hqn]
    · have hqn : q ∈ squarefreePrimeFace n := by
        by_contra hqn
        exact hiff (by simp [hqm, hqn])
      simp [squarefreePairFreshPrimeSet, hqm, hqn]
  have hle : (squarefreePairFreshPrimeSet m n).min' hne ≤ q :=
    Finset.min'_le _ _ hdiff
  omega

/-- Intrinsic predicate saying that `p` is the first differing Euler coordinate. -/
def IsSquarefreePairFreshPrimeOwner (p m n : ℕ) : Prop :=
  p ∈ squarefreePairFreshPrimeSet m n ∧
    ∀ q ∈ squarefreePairFreshPrimeSet m n, p ≤ q

/-- The canonical owner satisfies the intrinsic first-separation predicate. -/
theorem squarefreePairFreshPrimeOwner_isOwner
    {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n) (hmn : m ≠ n) :
    IsSquarefreePairFreshPrimeOwner (squarefreePairFreshPrimeOwner m n) m n := by
  have hne := squarefreePairFreshPrimeSet_nonempty hm hn hmn
  constructor
  · exact squarefreePairFreshPrimeOwner_mem hm hn hmn
  · intro q hq
    unfold squarefreePairFreshPrimeOwner
    rw [dif_pos hne]
    exact Finset.min'_le _ _ hq

/-- **Unique global ownership.**  Every distinct squarefree pair has exactly one
first separating prime.  This is the no-overlap chronology theorem. -/
theorem existsUnique_squarefreePairFreshPrimeOwner
    {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n) (hmn : m ≠ n) :
    ∃! p : ℕ, IsSquarefreePairFreshPrimeOwner p m n := by
  refine ⟨squarefreePairFreshPrimeOwner m n,
    squarefreePairFreshPrimeOwner_isOwner hm hn hmn, ?_⟩
  intro p hp
  have hcanon := squarefreePairFreshPrimeOwner_isOwner hm hn hmn
  have hp_le := hp.2 (squarefreePairFreshPrimeOwner m n) hcanon.1
  have hc_le := hcanon.2 p hp.1
  omega

/-- A nonzero real Mobius coordinate is squarefree. -/
theorem squarefree_of_realMoebiusStep_ne_zero
    {n : ℕ} (hn : realMoebiusStep n ≠ 0) : Squarefree n := by
  apply ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp
  intro hmu
  apply hn
  simp [realMoebiusStep, hmu]

/-- **Square-run ownership theorem.**  Every nonzero physical covariance atom in
any consecutive square run has one and only one chronological fresh-prime
owner.  Zero Mobius atoms need no owner because their covariance weight is zero. -/
theorem squareRunCovarianceAtom_existsUnique_freshPrimeOwner
    {a b m n : ℕ} (hab : a ≤ b)
    (hm : m ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2))
    (hn : n ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2))
    (hmn : m < n)
    (hm0 : realMoebiusStep m ≠ 0)
    (hn0 : realMoebiusStep n ≠ 0) :
    ∃! p : ℕ, IsSquarefreePairFreshPrimeOwner p m n := by
  have hmsq := squarefree_of_realMoebiusStep_ne_zero hm0
  have hnsq := squarefree_of_realMoebiusStep_ne_zero hn0
  exact existsUnique_squarefreePairFreshPrimeOwner hmsq hnsq (by omega)

end RHLean.Analysis

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

/-! ## The natural negative prime leaf and the top-escape seam -/

/-- Same-`p` family covariance that stays wholly inside the physical square run.
Each such pair is `(m,p*m)` with `p` fresh to `m`, and its signed weight is
`-mu(m)^2`.  This is the natural nonpositive leaf left by a fixed-prime family
refinement. -/
def squareRunPrimeLeafCovariance (p a b : ℕ) : ℝ :=
  -∑ m ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2),
    if 0 < m ∧ ¬ p ∣ m ∧ p * m < (b + 1) ^ 2 then
      realMoebiusStep m ^ 2
    else 0

/-- The prime-family leaf never adds positive covariance. -/
theorem squareRunPrimeLeafCovariance_nonpos (p a b : ℕ) :
    squareRunPrimeLeafCovariance p a b ≤ 0 := by
  unfold squareRunPrimeLeafCovariance
  have hsum :
      0 ≤ ∑ m ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2),
        if 0 < m ∧ ¬ p ∣ m ∧ p * m < (b + 1) ^ 2 then
          realMoebiusStep m ^ 2
        else 0 := by
    apply Finset.sum_nonneg
    intro m hm
    split_ifs <;> positivity
  linarith

/-- The fixed-prime leaf is an admissible descended contribution in the run
escape architecture. -/
theorem squareRunPrimeLeafDescendedNonpositive (p : ℕ) :
    SquareRunDescendedNonpositive (squareRunPrimeLeafCovariance p) := by
  intro a b hab
  exact squareRunPrimeLeafCovariance_nonpos p a b

/-- The magnitude of the negative leaf is at most the exact physical window
length, because every parent contributes at most one Mobius square. -/
theorem neg_squareRunPrimeLeafCovariance_le_windowLength
    (p a b : ℕ) (hab : a ≤ b) :
    -squareRunPrimeLeafCovariance p a b ≤
      ((((b + 1) ^ 2 - a ^ 2 : ℕ) : ℝ)) := by
  have hsq : a ^ 2 ≤ (b + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  unfold squareRunPrimeLeafCovariance
  rw [neg_neg]
  calc
    (∑ m ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2),
        if 0 < m ∧ ¬ p ∣ m ∧ p * m < (b + 1) ^ 2 then
          realMoebiusStep m ^ 2
        else 0) ≤
        ∑ _m ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      by_cases h : 0 < m ∧ ¬ p ∣ m ∧ p * m < (b + 1) ^ 2
      · simp [h, realMoebiusStep_sq_le_one m]
      · simp [h]
    _ = ((Finset.Ico (a ^ 2) ((b + 1) ^ 2)).card : ℝ) := by simp
    _ = ((((b + 1) ^ 2 - a ^ 2 : ℕ) : ℝ)) := by
      rw [Nat.card_Ico]

/-- On a subdoubling physical window no prime family can have both `m` and
`p*m` inside the run.  Hence the nonpositive same-family leaf is exactly empty. -/
theorem squareRunPrimeLeafCovariance_eq_zero_of_subdoubling
    {p a b : ℕ} (hp : p.Prime)
    (hsub : (b + 1) ^ 2 ≤ 2 * a ^ 2) :
    squareRunPrimeLeafCovariance p a b = 0 := by
  unfold squareRunPrimeLeafCovariance
  have hzero :
      (∑ m ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2),
        if 0 < m ∧ ¬ p ∣ m ∧ p * m < (b + 1) ^ 2 then
          realMoebiusStep m ^ 2
        else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    by_cases h : 0 < m ∧ ¬ p ∣ m ∧ p * m < (b + 1) ^ 2
    · have hmA : a ^ 2 ≤ m := (Finset.mem_Ico.mp hm).1
      have hmul : 2 * a ^ 2 ≤ p * m := Nat.mul_le_mul hp.two_le hmA
      omega
    · simp [h]
  rw [hzero]
  norm_num

/-- Adjacent square blocks are subdoubling from radius `3` onward, so their
same-prime descended leaf is empty for every prime. -/
theorem squareRunPrimeLeafCovariance_adjacent_eq_zero
    {p r : ℕ} (hp : p.Prime) (hr : 3 ≤ r) :
    squareRunPrimeLeafCovariance p r r = 0 := by
  apply squareRunPrimeLeafCovariance_eq_zero_of_subdoubling hp
  nlinarith

/-- Therefore on a subdoubling run the natural top escape is not a smaller
residual: it is literally the entire square-run covariance. -/
theorem squareRunPrimeLeafEscape_eq_covariance_of_subdoubling
    {p a b : ℕ} (hp : p.Prime)
    (hsub : (b + 1) ^ 2 ≤ 2 * a ^ 2) :
    squareRunEscapeCovariance (squareRunPrimeLeafCovariance p) a b =
      squareRunCovariance a b := by
  rw [squareRunPrimeLeafCovariance_eq_zero_of_subdoubling hp hsub]
  simp [squareRunEscapeCovariance]

/-- The square-run diagonal is nonnegative on a genuine forward run. -/
theorem squareRunDiagonal_nonneg (a b : ℕ) (hab : a ≤ b) :
    0 ≤ squareRunDiagonal a b := by
  have hsq : a ^ 2 ≤ (b + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hsplit :=
    Finset.sum_range_add_sum_Ico (fun n => realMoebiusStep n ^ 2) hsq
  have hsum :
      0 ≤ ∑ n ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2), realMoebiusStep n ^ 2 := by
    exact Finset.sum_nonneg (fun n hn => sq_nonneg (realMoebiusStep n))
  unfold squareRunDiagonal realMertensDiagonal
  linarith

private theorem squareRun_root_rpow_eq_endpoint_rpow
    (r : ℕ) (ε : ℝ) :
    Real.rpow ((r + 1 : ℕ) : ℝ) (2 + 2 * ε) =
      Real.rpow ((((r + 1) ^ 2 : ℕ) : ℝ)) (1 + ε) := by
  have hx : (0 : ℝ) ≤ (((r + 1 : ℕ) : ℝ)) := by positivity
  have htwo :
      Real.rpow (((r + 1 : ℕ) : ℝ)) (2 : ℝ) =
        (((r + 1 : ℕ) : ℝ)) ^ (2 : ℕ) :=
    Real.rpow_natCast (((r + 1 : ℕ) : ℝ)) 2
  calc
    Real.rpow (((r + 1 : ℕ) : ℝ)) (2 + 2 * ε) =
        Real.rpow (((r + 1 : ℕ) : ℝ)) ((2 : ℝ) * (1 + ε)) := by
          congr 1
          ring
    _ = Real.rpow (Real.rpow (((r + 1 : ℕ) : ℝ)) (2 : ℝ)) (1 + ε) :=
      Real.rpow_mul hx (2 : ℝ) (1 + ε)
    _ = Real.rpow ((((r + 1) ^ 2 : ℕ) : ℝ)) (1 + ε) := by
      rw [htwo]
      norm_cast

private theorem squareRun_endpoint_le_rpow
    {ε : ℝ} (hε : 0 < ε) (b : ℕ) :
    ((((b + 1) ^ 2 : ℕ) : ℝ)) ≤
      Real.rpow ((((b + 1) ^ 2 : ℕ) : ℝ)) (1 + ε) := by
  have hbase : (1 : ℝ) ≤ ((((b + 1) ^ 2 : ℕ) : ℝ)) := by
    positivity
  have h := Real.rpow_le_rpow_of_exponent_le hbase
    (by linarith : (1 : ℝ) ≤ 1 + ε)
  simpa using h

/-- Mertens energy control bounds the natural prime-leaf top escape.  The leaf
itself costs only one linear window term, so all critical-scale content lies in
the original run mass. -/
theorem squareRunPrimeLeafTopEscapeBounded_of_mertensEnergy
    (p : ℕ) (hM : MertensEnergyBoundedStatement) :
    SquareRunTopEscapeCovarianceBoundedStatement
      (squareRunPrimeLeafCovariance p) := by
  intro ε hε
  have hS := squarePrefixEnergyBounded_of_mertensEnergyBounded hM
  rcases hS (2 * ε) (by linarith) with ⟨C, hC, hbound⟩
  refine ⟨2 * C + 1, by linarith, ?_⟩
  intro a b hab
  let P : ℝ := Real.rpow ((((b + 1) ^ 2 : ℕ) : ℝ)) (1 + ε)
  have hB :
      realMertensLength ((b + 1) ^ 2) ^ 2 ≤ C * P := by
    have hb := hbound b
    have hnorm :=
      norm_mertensSummatory_sq_eq_realMertensLength_sq (squarePrefixEndpoint b)
    rw [squarePrefixEndpoint_add_one b] at hnorm
    rw [← hnorm]
    have hroot := squareRun_root_rpow_eq_endpoint_rpow b ε
    simpa [squarePrefixMertens, P, hroot] using hb
  have hA : realMertensLength (a ^ 2) ^ 2 ≤ C * P := by
    by_cases ha0 : a = 0
    · subst a
      simp [realMertensLength, P, hC]
    · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
      have haB : a ≤ b + 1 := by omega
      have haBase : (((a : ℕ) : ℝ)) ≤ (((b + 1 : ℕ) : ℝ)) := by
        exact_mod_cast haB
      have hpowRoot :
          Real.rpow (a : ℝ) (2 + 2 * ε) ≤
            Real.rpow ((b + 1 : ℕ) : ℝ) (2 + 2 * ε) :=
        Real.rpow_le_rpow (by positivity) haBase (by linarith)
      have ha := hbound (a - 1)
      have hnorm :=
        norm_mertensSummatory_sq_eq_realMertensLength_sq
          (squarePrefixEndpoint (a - 1))
      rw [squarePrefixEndpoint_add_one (a - 1)] at hnorm
      have hpred : a - 1 + 1 = a := Nat.sub_add_cancel ha1
      rw [hpred] at hnorm
      have haReal :
          realMertensLength (a ^ 2) ^ 2 ≤
            C * Real.rpow (a : ℝ) (2 + 2 * ε) := by
        rw [← hnorm]
        simpa [squarePrefixMertens, hpred] using ha
      have hmono :
          C * Real.rpow (a : ℝ) (2 + 2 * ε) ≤
            C * Real.rpow ((b + 1 : ℕ) : ℝ) (2 + 2 * ε) :=
        mul_le_mul_of_nonneg_left hpowRoot hC
      have hroot := squareRun_root_rpow_eq_endpoint_rpow b ε
      exact haReal.trans (by simpa [P, hroot] using hmono)
  have hmass : squareRunMass a b ^ 2 ≤ 4 * C * P := by
    unfold squareRunMass
    nlinarith [sq_nonneg
      (realMertensLength ((b + 1) ^ 2) + realMertensLength (a ^ 2))]
  have hdiag := squareRunDiagonal_nonneg a b hab
  have hid := squareRunMass_sq_eq a b
  have hcov : squareRunCovariance a b ≤ 2 * C * P := by
    nlinarith
  have hleaf := neg_squareRunPrimeLeafCovariance_le_windowLength p a b hab
  have hwindow :
      ((((b + 1) ^ 2 - a ^ 2 : ℕ) : ℝ)) ≤
        ((((b + 1) ^ 2 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.sub_le ((b + 1) ^ 2) (a ^ 2)
  have hlin : ((((b + 1) ^ 2 : ℕ) : ℝ)) ≤ P := by
    dsimp [P]
    exact squareRun_endpoint_le_rpow hε b
  unfold squareRunEscapeCovariance
  calc
    squareRunCovariance a b - squareRunPrimeLeafCovariance p a b ≤
        2 * C * P + (-squareRunPrimeLeafCovariance p a b) := by
      linarith
    _ ≤ 2 * C * P + ((((b + 1) ^ 2 - a ^ 2 : ℕ) : ℝ)) :=
      add_le_add_left hleaf _
    _ ≤ 2 * C * P + P := by
      gcongr
      exact hwindow.trans hlin
    _ = (2 * C + 1) * P := by ring

/-- **Quantitative classification of the resulting top escape.**  Once the
nonpositive same-prime leaves are charged, an RH-scale square-time top-escape
bound is not a weaker remaining estimate: it is exactly equivalent to the
repository's global Mertens energy criterion. -/
theorem squareRunPrimeLeafTopEscapeBounded_iff_mertensEnergy
    (p : ℕ) :
    SquareRunTopEscapeCovarianceBoundedStatement
        (squareRunPrimeLeafCovariance p) ↔
      MertensEnergyBoundedStatement := by
  constructor
  · intro hesc
    exact mertensEnergyBounded_of_topEscapeCovarianceBounded
      (squareRunPrimeLeafDescendedNonpositive p) hesc
  · exact squareRunPrimeLeafTopEscapeBounded_of_mertensEnergy p

end RHLean.Analysis

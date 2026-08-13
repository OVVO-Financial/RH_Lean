import Mathlib
import RHLean.Analysis.PrimeSieveDyadicPacketDissipation

/-!
# Block-local reduction of signed packet reverse Carleson

PR #327 isolates the remaining packet-side arithmetic input as the signed
reverse-Carleson estimate

`D_J <= C_epsilon * (x+1)^epsilon * L_J`.

This module does not introduce another residual coordinate.  It localizes the
existing #327 energies block by block and identifies exactly which blocks need
new prime-number information.

For one occupied dyadic reciprocal block of depth `j`, define its contribution
to the released level `J` and to the remaining deep tail by the same differences
of #324 packet-tree energies already used in #326 and #327.  Then:

* the global `L_J` and `D_J` are exactly the sums of the block contributions;
* a live block with `j = J+1` is terminal, so its entire deep tail is exactly its
  released level energy -- reverse Carleson holds there with constant one;
* dead blocks `j <= J` contribute zero;
* therefore only genuinely nonterminal blocks `J+1 < j` require arithmetic
  input.

The new named arithmetic premise is consequently a block-local signed sibling
persistence estimate on those nonterminal blocks.  It is strictly more local
than the global reverse-Carleson statement: there is no cancellation between
unrelated dyadic reciprocal blocks left to exploit or to lose.

The module also exposes the exact prime-minus-Li content of every sibling packet:
the normalized packet is the signed contrast of the two child sums of the
existing reciprocal prime discrepancies, and each discrepancy is itself the
finite prime-indicator-minus-Li-density mass on its quotient interval.

No instance of the nonterminal persistence premise is proved here.  The terminal
fragment is unconditional.  Thus the remaining open statement is precisely new
prime-number information about persistence of signed discrepancy energy under a
midpoint refinement, rather than another algebraic reparameterization.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-! ## Exact signed arithmetic at one sibling split -/

/-- The width-normalized sibling packet written directly as a signed contrast of
prime-indicator-minus-Li-density masses on the two child reciprocal intervals.
No triangle split of the prime and Li pieces is used. -/
theorem primeSieveSignedSiblingPacketResidual_eq_signed_reciprocalPrimeMass
    {y x a m b : ℕ}
    (ha : 1 ≤ a) (ham : a ≤ m) (hmb : m ≤ b)
    (hb : b ≤ x / (y + 1) + 1) :
    primeSieveSignedSiblingPacketResidual y x a m b =
      (((b - a : ℕ) : ℂ)⁻¹) *
        ((((m - a : ℕ) : ℂ) *
            (∑ d ∈ Finset.Ico m b,
              ∑ q ∈ primeSieveReciprocalInterval y x d,
                (primeSievePrimeIndicator q - primeSievePNTDensity q))) -
          (((b - m : ℕ) : ℂ) *
            (∑ d ∈ Finset.Ico a m,
              ∑ q ∈ primeSieveReciprocalInterval y x d,
                (primeSievePrimeIndicator q - primeSievePNTDensity q)))) := by
  have hright :
      (∑ d ∈ Finset.Ico m b,
        primeSieveReciprocalPrimeDiscrepancy y x d) =
        ∑ d ∈ Finset.Ico m b,
          ∑ q ∈ primeSieveReciprocalInterval y x d,
            (primeSievePrimeIndicator q - primeSievePNTDensity q) := by
    apply Finset.sum_congr rfl
    intro d _hd
    rw [sum_primeIndicator_sub_density_reciprocalInterval]
  have hleft :
      (∑ d ∈ Finset.Ico a m,
        primeSieveReciprocalPrimeDiscrepancy y x d) =
        ∑ d ∈ Finset.Ico a m,
          ∑ q ∈ primeSieveReciprocalInterval y x d,
            (primeSievePrimeIndicator q - primeSievePNTDensity q) := by
    apply Finset.sum_congr rfl
    intro d _hd
    rw [sum_primeIndicator_sub_density_reciprocalInterval]
  unfold primeSieveSignedSiblingPacketResidual
  rw [primeSieveSignedSiblingPacket_eq_weighted_intervalDiscrepancies
    ha ham hmb hb, hright, hleft]

/-! ## Block-local copies of the existing global energies -/

/-- Contribution of one dyadic reciprocal block to the released level `J`. -/
def primeSieveDyadicPacketBlockLevelEnergy
    (y x j J : ℕ) : ℝ :=
  primeSieveDyadicPacketTreeBlockEnergy y x j (min (J + 1) j) -
    primeSieveDyadicPacketTreeBlockEnergy y x j (min J j)

/-- Contribution of one dyadic reciprocal block to the deep tail beyond `J`. -/
def primeSieveDyadicPacketBlockDeepEnergy
    (y x j J : ℕ) : ℝ :=
  primeSieveDyadicPacketTreeBlockEnergy y x j j -
    primeSieveDyadicPacketTreeBlockEnergy y x j (min J j)

/-- The global released level is exactly the sum of its block contributions. -/
theorem primeSieveDyadicPacketLevelEnergy_eq_sum_blockLevelEnergy
    (y x J : ℕ) :
    primeSieveDyadicPacketLevelEnergy y x J =
      ∑ j ∈ primeSieveDyadicBlockIndices y x,
        primeSieveDyadicPacketBlockLevelEnergy y x j J := by
  rfl

/-- The global deep tail is exactly the sum of its block contributions. -/
theorem primeSieveDyadicPacketDeepEnergy_eq_sum_blockDeepEnergy
    (y x J : ℕ) :
    primeSieveDyadicPacketDeepEnergy y x J =
      ∑ j ∈ primeSieveDyadicBlockIndices y x,
        primeSieveDyadicPacketBlockDeepEnergy y x j J := by
  rfl

/-- A block released-level contribution is nonnegative. -/
theorem primeSieveDyadicPacketBlockLevelEnergy_nonneg
    (y x j J : ℕ) :
    0 ≤ primeSieveDyadicPacketBlockLevelEnergy y x j J := by
  unfold primeSieveDyadicPacketBlockLevelEnergy
    primeSieveDyadicPacketTreeBlockEnergy
  apply sub_nonneg.mpr
  exact primeSieveDyadicPacketIntervalTreeEnergy_mono y x (by omega)

/-- A block deep-tail contribution is nonnegative. -/
theorem primeSieveDyadicPacketBlockDeepEnergy_nonneg
    (y x j J : ℕ) :
    0 ≤ primeSieveDyadicPacketBlockDeepEnergy y x j J := by
  unfold primeSieveDyadicPacketBlockDeepEnergy
    primeSieveDyadicPacketTreeBlockEnergy
  apply sub_nonneg.mpr
  exact primeSieveDyadicPacketIntervalTreeEnergy_mono y x (min_le_right J j)

/-- Exact one-step decomposition on one block. -/
theorem primeSieveDyadicPacketBlockDeepEnergy_eq_level_add_succ
    (y x j J : ℕ) :
    primeSieveDyadicPacketBlockDeepEnergy y x j J =
      primeSieveDyadicPacketBlockLevelEnergy y x j J +
        primeSieveDyadicPacketBlockDeepEnergy y x j (J + 1) := by
  unfold primeSieveDyadicPacketBlockDeepEnergy
    primeSieveDyadicPacketBlockLevelEnergy
  ring

/-- Once the cutoff has reached the block depth, the block contributes no deep
energy. -/
theorem primeSieveDyadicPacketBlockDeepEnergy_eq_zero_of_depth_le
    {y x j J : ℕ} (h : j ≤ J) :
    primeSieveDyadicPacketBlockDeepEnergy y x j J = 0 := by
  unfold primeSieveDyadicPacketBlockDeepEnergy
  rw [min_eq_right h]
  ring

/-- Once the cutoff has reached the block depth, that block also releases no new
level energy. -/
theorem primeSieveDyadicPacketBlockLevelEnergy_eq_zero_of_depth_le
    {y x j J : ℕ} (h : j ≤ J) :
    primeSieveDyadicPacketBlockLevelEnergy y x j J = 0 := by
  have h' : j ≤ J + 1 := by omega
  unfold primeSieveDyadicPacketBlockLevelEnergy
  rw [min_eq_right h, min_eq_right h']
  ring

/-- **Unconditional terminal fragment.**  If exactly one refinement level is
left in a block, then the complete remaining deep tail is precisely the level
that is released now.  Reverse Carleson therefore holds with constant one on
such a block. -/
theorem primeSieveDyadicPacketBlockDeepEnergy_eq_levelEnergy_of_depth_eq_succ
    (y x J : ℕ) :
    primeSieveDyadicPacketBlockDeepEnergy y x (J + 1) J =
      primeSieveDyadicPacketBlockLevelEnergy y x (J + 1) J := by
  unfold primeSieveDyadicPacketBlockDeepEnergy
    primeSieveDyadicPacketBlockLevelEnergy
  simp only [min_self, min_eq_left (Nat.le_succ J)]

/-- On a live block, its released contribution is literally the #327 signed
packet energy on recursive level `J`. -/
theorem primeSieveDyadicPacketBlockLevelEnergy_eq_intervalLevelEnergy
    {y x j J : ℕ} (hJ : J < j) :
    primeSieveDyadicPacketBlockLevelEnergy y x j J =
      primeSieveDyadicPacketIntervalLevelEnergy y x J
        (primeSieveDyadicBlockLeft j)
        (primeSieveDyadicBlockRight y x j + 1) := by
  have hmin : min J j = J := min_eq_left hJ.le
  have hminSucc : min (J + 1) j = J + 1 := min_eq_left (by omega)
  unfold primeSieveDyadicPacketBlockLevelEnergy
    primeSieveDyadicPacketTreeBlockEnergy
  rw [hmin, hminSucc]
  exact primeSieveDyadicPacketIntervalTreeEnergy_succ_sub_eq_levelEnergy
    y x J (primeSieveDyadicBlockLeft j)
      (primeSieveDyadicBlockRight y x j + 1)

/-! ## The genuinely arithmetic nonterminal premise -/

/-- **Nonterminal signed sibling persistence.**  Only blocks with at least two
unresolved recursive levels are quantified here.  The terminal live blocks are
already controlled unconditionally by the exact theorem above.

This is the first genuinely new prime-number input in the reduction.  Through
`primeSieveDyadicPacketBlockLevelEnergy_eq_intervalLevelEnergy` and
`primeSieveSignedSiblingPacketResidual_eq_signed_reciprocalPrimeMass`, its right
side is the actual signed prime-minus-Li sibling energy released by the first
unresolved midpoint refinement. -/
def DyadicPacketNonterminalBlockSiblingPersistenceStatement
    (cutoff : DyadicPacketCutoff) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (k x j : ℕ),
        2 ≤ k →
        primorialBlockLower k ≤ x →
        x ≤ primorialBlockUpper k →
        j ∈ primeSieveDyadicBlockIndices
          (primorialPNTPrimeSieveCutoff k) x →
        cutoff k x + 1 < j →
        primeSieveDyadicPacketBlockDeepEnergy
            (primorialPNTPrimeSieveCutoff k) x j (cutoff k x) ≤
          C * Real.rpow ((x : ℝ) + 1) ε *
            primeSieveDyadicPacketBlockLevelEnergy
              (primorialPNTPrimeSieveCutoff k) x j (cutoff k x)

/-- The nonterminal block statement, plus the unconditional terminal fragment,
proves the full global reverse-Carleson estimate.  No cross-block cancellation is
used. -/
theorem dyadicPacketReverseCarlesonBlockBounded_of_nonterminalBlockPersistence
    (cutoff : DyadicPacketCutoff)
    (hB : DyadicPacketNonterminalBlockSiblingPersistenceStatement cutoff) :
    DyadicPacketReverseCarlesonBlockBoundedStatement cutoff := by
  intro ε hε
  obtain ⟨C, hC, hCb⟩ := hB ε hε
  refine ⟨C, hC.trans' (by norm_num), ?_⟩
  intro k x hk hlow hup
  let y := primorialPNTPrimeSieveCutoff k
  let J := cutoff k x
  let P := Real.rpow ((x : ℝ) + 1) ε
  have hP0 : 0 ≤ P := by
    dsimp [P]
    exact Real.rpow_nonneg (by positivity) _
  have hP1 : 1 ≤ P := by
    dsimp [P]
    have hbase : (1 : ℝ) ≤ (x : ℝ) + 1 := by positivity
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hbase hε.le
    simpa using h
  have hCP1 : 1 ≤ C * P := by
    calc
      (1 : ℝ) ≤ C := hC
      _ = C * 1 := by ring
      _ ≤ C * P :=
        mul_le_mul_of_nonneg_left hP1 (by linarith)
  have hblock :
      ∀ j ∈ primeSieveDyadicBlockIndices y x,
        primeSieveDyadicPacketBlockDeepEnergy y x j J ≤
          C * P * primeSieveDyadicPacketBlockLevelEnergy y x j J := by
    intro j hj
    by_cases hdead : j ≤ J
    · rw [primeSieveDyadicPacketBlockDeepEnergy_eq_zero_of_depth_le hdead]
      exact mul_nonneg (mul_nonneg (by linarith) hP0)
        (primeSieveDyadicPacketBlockLevelEnergy_nonneg y x j J)
    · have hlive : J < j := Nat.lt_of_not_ge hdead
      by_cases hterm : j = J + 1
      · subst j
        rw [primeSieveDyadicPacketBlockDeepEnergy_eq_levelEnergy_of_depth_eq_succ]
        have hL :=
          primeSieveDyadicPacketBlockLevelEnergy_nonneg y x (J + 1) J
        calc
          primeSieveDyadicPacketBlockLevelEnergy y x (J + 1) J =
              1 * primeSieveDyadicPacketBlockLevelEnergy y x (J + 1) J := by ring
          _ ≤ (C * P) *
              primeSieveDyadicPacketBlockLevelEnergy y x (J + 1) J :=
            mul_le_mul_of_nonneg_right hCP1 hL
      · have hnonterminal : J + 1 < j := by omega
        simpa [y, J, P] using
          hCb k x j hk hlow hup hj hnonterminal
  calc
    primeSieveDyadicPacketDeepEnergy y x J =
        ∑ j ∈ primeSieveDyadicBlockIndices y x,
          primeSieveDyadicPacketBlockDeepEnergy y x j J :=
      primeSieveDyadicPacketDeepEnergy_eq_sum_blockDeepEnergy y x J
    _ ≤ ∑ j ∈ primeSieveDyadicBlockIndices y x,
        C * P * primeSieveDyadicPacketBlockLevelEnergy y x j J := by
      exact Finset.sum_le_sum hblock
    _ = C * P *
        (∑ j ∈ primeSieveDyadicBlockIndices y x,
          primeSieveDyadicPacketBlockLevelEnergy y x j J) := by
      rw [Finset.mul_sum]
    _ = C * P * primeSieveDyadicPacketLevelEnergy y x J := by
      rw [← primeSieveDyadicPacketLevelEnergy_eq_sum_blockLevelEnergy]

/-- Terminal RH reduction with the global reverse-Carleson hypothesis replaced
by the genuinely local nonterminal signed sibling persistence statement. -/
theorem riemannHypothesis_of_dyadicPacketNonterminalBlockPersistenceAnalyticPackage
    (cutoff : DyadicPacketCutoff)
    (hC : DyadicCoherentChannelRHScale)
    (hS : DyadicPacketShallowEnergyBlockBoundedStatement
      (dyadicPacketSuccCutoff cutoff))
    (hB : DyadicPacketNonterminalBlockSiblingPersistenceStatement cutoff)
    (hD : DyadicMobiusDispersionBlockBoundedStatement) :
    RiemannHypothesisStatement := by
  apply riemannHypothesis_of_dyadicPacketReverseCarlesonAnalyticPackage
    cutoff hC hS
  · exact dyadicPacketReverseCarlesonBlockBounded_of_nonterminalBlockPersistence
      cutoff hB
  · exact hD

end RHLean.Analysis

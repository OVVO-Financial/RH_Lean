import Mathlib

/-!
# First-bad minimal payment — exact parity-compressed algebra

This is a SMALL, warning-fatal, Mathlib-only kernel test. It does not import
the expensive native StrongPNT/research graph. The native definitions are
w_R = V_R / R, C_R = R - P_R and D_R = pi(R^2)-VF_mid(R^2).

The ONLY open mathematical requirement is to establish the final balance
on ACTUAL primes under an ACTUAL first-bad hypothesis. Every theorem here
is an unconditional algebraic identity, not that requirement.
-/

noncomputable section

namespace RHLean.Analysis

/-- Upper zero-target partial mass: actual odd composites plus the negative
historical endpoint anchor. NO EVEN SITES are introduced. -/
def vfV2Upper (D w C : ℝ) : ℝ :=
  (|D| - D) / 2 + w * C

/-- Lower zero-target partial mass: actual odd prime seats plus the positive
historical endpoint anchor. -/
def vfV2Lower (D w P : ℝ) : ℝ :=
  (|D| + D) / 2 + (1 - w) * P

/-- Next actual signed endpoint defect after a block with P primes and
C composites on its R=P+C odd physical seats. -/
def vfV2Next (D w P C : ℝ) : ℝ :=
  D + P - w * (P + C)

/-- The squared anchored L1 NNS mass, NOT a statistical variance. -/
def vfV2OriginalMass (D w P C : ℝ) : ℝ :=
  (|D| + w * C + (1 - w) * P) ^ 2

/-- The exact ORIGINAL one-half contraction slack. -/
def vfV2Balance (D w P C : ℝ) : ℝ :=
  (vfV2Upper D w C + vfV2Lower D w P) ^ 2 -
    2 * (vfV2Upper D w C - vfV2Lower D w P) ^ 2

theorem vfV2Upper_sub_lower_eq_neg_next (D w P C : ℝ) :
    vfV2Upper D w C - vfV2Lower D w P =
      -vfV2Next D w P C := by
  unfold vfV2Upper vfV2Lower vfV2Next
  ring

theorem vfV2Upper_add_lower_eq_original_abs (D w P C : ℝ) :
    vfV2Upper D w C + vfV2Lower D w P =
      |D| + w * C + (1 - w) * P := by
  unfold vfV2Upper vfV2Lower
  ring

/-- Every bit of reference mass R*w is absorbed into R odd physical seats.
The even lattice is already included in V_R=R*w. -/
theorem vfV2ReferenceCompressedToOdd (R w V : ℝ)
    (hcalibrated : V = R * w) :
    R * w = V := by
  rw [hcalibrated]

/-- Algebraic original-budget weld: the source is NEXT DEFECT squared,
and the original NNS denominator is never enlarged. -/
theorem vfV2Balance_eq_originalMass_sub_two_next_sq (D w P C : ℝ) :
    vfV2Balance D w P C =
      vfV2OriginalMass D w P C -
        2 * (vfV2Next D w P C) ^ 2 := by
  unfold vfV2Balance vfV2OriginalMass
  rw [vfV2Upper_add_lower_eq_original_abs]
  rw [vfV2Upper_sub_lower_eq_neg_next]
  ring

/-- The hbalance obligation, with no extra sites and no unproved arithmetic
condition smuggled into the definition. -/
theorem vfV2Payment_iff_exactSignedBalance (D w P C : ℝ) :
    0 ≤ vfV2Balance D w P C ↔
      2 * (vfV2Next D w P C) ^ 2 ≤
        vfV2OriginalMass D w P C := by
  rw [vfV2Balance_eq_originalMass_sub_two_next_sq]
  constructor <;> intro h <;> linarith

/-- The equivalent nonnegative co-partial versus divergent two-sector payment. -/
theorem vfV2Balance_eq_neg_coDivExcess (D w P C : ℝ) :
    vfV2Balance D w P C =
      -(vfV2Upper D w C ^ 2 + vfV2Lower D w P ^ 2 -
        6 * vfV2Upper D w C * vfV2Lower D w P) := by
  unfold vfV2Balance
  ring

theorem vfV2Payment_iff_twoSector (D w P C : ℝ) :
    0 ≤ vfV2Balance D w P C ↔
      vfV2Upper D w C ^ 2 + vfV2Lower D w P ^ 2 ≤
        6 * vfV2Upper D w C * vfV2Lower D w P := by
  rw [vfV2Balance_eq_neg_coDivExcess]
  constructor <;> intro h <;> linarith

/-! ## True prime-minus-discrete-Li signed margins ## -/

def vfV2LiPlus (D w F R : Real) : Real :=
  |D| + w*R + (1-2*w)*F + Real.sqrt 2*(D+F-w*R)

def vfV2LiMinus (D w F R : Real) : Real :=
  |D| + w*R + (1-2*w)*F - Real.sqrt 2*(D+F-w*R)

theorem vfV2LiPlus_actual (D w F d R : Real) :
    vfV2Upper D w (R-(F+d)) + vfV2Lower D w (F+d) +
        Real.sqrt 2*vfV2Next D w (F+d) (R-(F+d)) =
      vfV2LiPlus D w F R + (1-2*w+Real.sqrt 2)*d := by
  rw [vfV2Upper_add_lower_eq_original_abs]
  unfold vfV2Next vfV2LiPlus
  ring

theorem vfV2LiMinus_actual (D w F d R : Real) :
    vfV2Upper D w (R-(F+d)) + vfV2Lower D w (F+d) -
        Real.sqrt 2*vfV2Next D w (F+d) (R-(F+d)) =
      vfV2LiMinus D w F R + (1-2*w-Real.sqrt 2)*d := by
  rw [vfV2Upper_add_lower_eq_original_abs]
  unfold vfV2Next vfV2LiMinus
  ring

/-- Factored original NNS payment; no new reference mass. -/
theorem vfV2Balance_factor (D w P C : Real) :
    vfV2Balance D w P C =
      (vfV2Upper D w C + vfV2Lower D w P +
        Real.sqrt 2*vfV2Next D w P C) *
      (vfV2Upper D w C + vfV2Lower D w P -
        Real.sqrt 2*vfV2Next D w P C) := by
  have hs : Real.sqrt (2 : Real) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0 : Real) <= 2)
  unfold vfV2Balance
  rw [vfV2Upper_sub_lower_eq_neg_next]
  calc
    (vfV2Upper D w C + vfV2Lower D w P)^2 -
        2 * (-vfV2Next D w P C)^2 =
      (vfV2Upper D w C + vfV2Lower D w P)^2 -
        (Real.sqrt 2 * vfV2Next D w P C)^2 := by
          rw [mul_pow, hs]
          ring
    _ = _ := by ring

/-- An exact CONDITIONAL certificate using the SIGNED ACTUAL prime
error d = (pi(X)-Q(X))-(pi(R^2)-Q(R^2)), with Q=floor Li2.
The conditions themselves require true prime arithmetic. -/
theorem vfV2Payment_of_floorLi_actual_signed_bounds
    (D w F d R : Real)
    (hplus : 0 <= vfV2LiPlus D w F R + (1-2*w+Real.sqrt 2)*d)
    (hminus : 0 <= vfV2LiMinus D w F R + (1-2*w-Real.sqrt 2)*d) :
    0 <= vfV2Balance D w (F+d) (R-(F+d)) := by
  rw [vfV2Balance_factor]
  rw [vfV2LiPlus_actual, vfV2LiMinus_actual]
  exact mul_nonneg hplus hminus

/-- Actual prime and both composite-sector discrepancies against
floor Li sum to zero on the ORIGINAL R odd candidate seats.
The weighted physical VF correction therefore equals -dP, exactly.
This cannot be separately credited as fresh negative NNS heat. -/
theorem vfV2OddCohortFloorLi_restores_primeError
    (w dP dHigh dSmooth : Real)
    (hcount : dP + dHigh + dSmooth = 0) :
    (w - 1)*dP + w*dHigh + w*dSmooth = -dP := by
  calc
    (w - 1)*dP + w*dHigh + w*dSmooth =
      w*(dP + dHigh + dSmooth) - dP := by ring
    _ = -dP := by rw [hcount]; ring

/-! ## Historical wall-relative restoration, with true floor-Li backlog ## -/

/-- Exact positive-wall clearance across a historical run. The bridge is
DETERMINISTIC and the error is the ACTUAL prime-minus-floor-Li backlog. -/
theorem vfV2HistoricalPositiveWallClearance
    (WA WB DA DB EA EB bA bB : Real)
    (hA : DA = EA+bA) (hB : DB = EB+bB) :
    WB-DB = (WA-DA)+(WB-WA)-(EB-EA)-(bB-bA) := by
  linarith

/-- Exact negative-wall clearance: no forced sign reversal is assumed. -/
theorem vfV2HistoricalNegativeWallClearance
    (WA WB DA DB EA EB bA bB : Real)
    (hA : DA = EA+bA) (hB : DB = EB+bB) :
    WB+DB = (WA+DA)+(WB-WA)+(EB-EA)+(bB-bA) := by
  linarith

/-- Positive first badness REQUIRES a large POSITIVE accumulated
true-prime error over the entire prior historical run, since the square
floor-Li/VF bridge is uniformly bounded. This is a NECESSARY condition,
not an unconditional bound that would rule out the first bad. -/
theorem vfV2PositiveFirstBad_requires_historicalPrimeLiExcess
    (WA WB DA DB EA EB bA bB C : Real)
    (hprior : DA <= WA) (hbad : WB < DB)
    (hA : DA = EA+bA) (hB : DB = EB+bB)
    (hbA : |bA| <= C) (hbB : |bB| <= C) :
    WB-WA-2*C < EB-EA := by
  have hbAlo : -C <= bA := (abs_le.mp hbA).1
  have hbBhi : bB <= C := (abs_le.mp hbB).2
  linarith

/-- Negative first badness REQUIRES an equally large NEGATIVE
historical prime-minus-floor-Li drift. Neither owner counts nor the
Li telescope automatically prevent it. -/
theorem vfV2NegativeFirstBad_requires_historicalPrimeLiDeficit
    (WA WB DA DB EA EB bA bB C : Real)
    (hprior : -WA <= DA) (hbad : DB < -WB)
    (hA : DA = EA+bA) (hB : DB = EB+bB)
    (hbA : |bA| <= C) (hbB : |bB| <= C) :
    WB-WA-2*C < EA-EB := by
  have hbAhi : bA <= C := (abs_le.mp hbA).2
  have hbBlo : -C <= bB := (abs_le.mp hbB).1
  linarith

/-- The cost of changing an anchored denominator from M to M+delta.
It is not additional physical budget. -/
theorem vfV2ParityRepacking_squares_cost (M delta : ℝ) :
    (M + delta) ^ 2 - M ^ 2 = 2 * M * delta + delta ^ 2 := by
  ring

/-- WARNING: a universal all-state one-half cone is FALSE even with
0 <= w <= 1, P,C >= 0. Arithmetic about actual primes is indispensable.
This concrete w=1/4, P=0, C=8 has negative slack. -/
theorem vfV2NoUnconditionalAllStateCone :
    ¬ ∀ D w P C : ℝ, 0 ≤ vfV2Balance D w P C := by
  intro hall
  have h := hall 0 (1 / 4) 0 8
  norm_num [vfV2Balance, vfV2Upper, vfV2Lower] at h


/-! ## Exact sparse-tier transport and half-run geometry

These lemmas do not assert the missing first-bad signed Co/Div inequality.
Their input is the ORIGINAL physical odd-seat owner partition. In particular,
a sparse owner p has p^2 > R and the open endpoint n < (R+1)^2.
-/

/-- Any sparse owner p at R>=9 is at least 4. Consequently, every
cofactor c of a physical composite p*c lies STRICTLY below the square
of A=R/2+1. This makes its prime ancestors prior-good under a first-bad
hypothesis, but does not make their earlier signed charge spendable twice. -/
theorem vfV2SparseCofactorBeforeHalfAnchor (R p c : ℕ)
    (hR : 9 ≤ R) (hp : R < p ^ 2)
    (hopen : p * c < (R + 1) ^ 2) :
    c < (R / 2 + 1) ^ 2 := by
  have hp4 : 4 ≤ p := by nlinarith
  have hhalf : R + 1 ≤ 2 * (R / 2 + 1) := by omega
  have hsq : (R + 1) ^ 2 ≤ (2 * (R / 2 + 1)) ^ 2 := by
    nlinarith
  have hmult : 4 * c ≤ p * c :=
    Nat.mul_le_mul_right c hp4
  nlinarith

/-- An owner p with p^2>R cannot occur four times in the prime
factorization of any number in the STRICTLY OPEN current square block.
Thus the entire intermediate tier consists only of 2- and 3-almost-primes. -/
theorem vfV2SparseFourFactorImpossible (R p n : ℕ)
    (hp : R < p ^ 2) (hopen : n < (R + 1) ^ 2)
    (hfour : p ^ 4 ≤ n) : False := by
  have hle : R + 1 ≤ p ^ 2 := by omega
  have hsquare : (R + 1) ^ 2 ≤ (p ^ 2) ^ 2 := by
    nlinarith
  have hpower : (p ^ 2) ^ 2 = p ^ 4 := by ring
  omega

/-- Weight-preserving finite Fubini over ALL sparse owners before taking
absolute values or a Co/Div bound. The same w_R is kept on every site.
This is a classification identity, NOT nonpositivity of the global Gram. -/
theorem vfV2SparseOwnerFubini (A B : ℕ) (owners : Finset ℕ)
    (w : ℕ → ℝ) (N : ℕ → ℕ → ℝ) :
    (∑ r ∈ Finset.Ico A B,
        w r * ∑ p ∈ owners,
          if p ≤ r ∧ r < p ^ 2 then N r p else 0) =
      ∑ p ∈ owners, ∑ r ∈ Finset.Ico A B,
        if p ≤ r ∧ r < p ^ 2 then w r * N r p else 0 := by
  calc
    _ = ∑ r ∈ Finset.Ico A B, ∑ p ∈ owners,
          if p ≤ r ∧ r < p ^ 2 then w r * N r p else 0 := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp_mem
        by_cases h : p ≤ r ∧ r < p ^ 2 <;> simp [h]
    _ = _ := by rw [Finset.sum_comm]

/-- The mature-survivor count T=P+S converts the ACTUAL prime error
against the floor-Li demand F into the negative sparse-owner residual
against T-F. This is an exact arithmetic telescope, not a probabilistic
estimate of the residual. -/
theorem vfV2SparseOwnerFloorLiResidual (T S F : ℝ) :
    (T - S) - F = -(S - (T - F)) := by
  ring

/-- The sparse component must be assembled BEFORE squaring. Its cross
term can help or hurt the native Co/Div sign and cannot be discarded. -/
theorem vfV2SparseCoDivFullCrossTerms (U0 L s : ℝ) :
    (U0 + s + L) ^ 2 - 2 * (U0 + s - L) ^ 2 =
      (6 * U0 * L - U0 ^ 2 - L ^ 2) +
        (6 * s * L - 2 * s * U0 - s ^ 2) := by
  ring


/-- No high-q factor q>R can produce TWO distinct ODD descendants
inside the same OPEN square block. Two odd cofactors differ by >=2,
and their products by >=2*q>2*R+1, exceeding the block width.
This is the occurrence-matching injection at ONE fixed R only;
across many distinct roots the same earlier prime may recur. -/
theorem vfV2HighFactorOneOddChildPerOpenBlock
    (R q a b : ℕ) (hq : R < q)
    (haLower : R ^ 2 < q * (2 * a + 1))
    (haUpper : q * (2 * a + 1) < (R + 1) ^ 2)
    (hbLower : R ^ 2 < q * (2 * b + 1))
    (hbUpper : q * (2 * b + 1) < (R + 1) ^ 2) :
    a = b := by
  rcases lt_trichotomy a b with hab | heq | hba
  · have hgap : 2 * a + 3 ≤ 2 * b + 1 := by omega
    have hm : q * (2 * a + 3) ≤ q * (2 * b + 1) :=
      Nat.mul_le_mul_left q hgap
    nlinarith
  · exact heq
  · have hgap : 2 * b + 3 ≤ 2 * a + 1 := by omega
    have hm : q * (2 * b + 3) ≤ q * (2 * a + 1) :=
      Nat.mul_le_mul_left q hgap
    nlinarith



/-! ## Oct 9: ALL odd high-owner children project to the half-run
anchor, except the single live factor-3 channel.

For A <= r < B <= 2*A, an odd physical composite has a prime
least owner p >= 3. If p >= 5, removing p moves the child below
A^2, even WITHOUT the previous sparse condition p^2>r.
If its child remains in the current A^2..B^2 history, p MUST be 3.
That one live 3-channel is time-separated: the parent is below
(4/3)*A^2 and the child is above 3*A^2. Removing TWO odd
prime factors always lands below A^2.

No probabilistic prime statement or cancellation estimate is assumed.
-/

/-- All owners p>=5 of any odd composite in a SUBDOUBLING completed
square run have cofactor strictly below the fixed early square anchor.
This applies to mature as well as sparse owners. -/
theorem vfV2HalfRunOwnerFiveChild_beforeAnchor
    (A B p c : ℕ) (hA : 1 ≤ A) (hBA : B ≤ 2 * A)
    (hp : 5 ≤ p) (hn : p * c < B ^ 2) :
    c < A ^ 2 := by
  have hBsq : B ^ 2 ≤ (2 * A) ^ 2 :=
    Nat.pow_le_pow_left hBA 2
  have hpc : 5 * c ≤ p * c :=
    Nat.mul_le_mul_right c hp
  have hApos : 1 ≤ A ^ 2 := by nlinarith [hA]
  by_contra hnot
  have hc : A ^ 2 ≤ c := Nat.le_of_not_gt hnot
  nlinarith

/-- The SOLE possible least-prime owner of an odd composite whose
stripped child stays IN the half-run is prime 3. Owner 2 is absent
from the original odd NNS carrier, and every p>=5 exits the run. -/
theorem vfV2HalfRunOnlyThreePrimeOwnerCanStayLive
    (A B p c : ℕ) (hA : 1 ≤ A) (hBA : B ≤ 2 * A)
    (hpPrime : p.Prime) (hpge3 : 3 ≤ p)
    (hn : p * c < B ^ 2) (hlive : A ^ 2 ≤ c) :
    p = 3 := by
  have hp4 : p ≠ 4 := by
    intro heq
    subst p
    norm_num at hpPrime
  by_contra hpNe3
  have hp5 : 5 ≤ p := by omega
  have hprior :=
    vfV2HalfRunOwnerFiveChild_beforeAnchor
      A B p c hA hBA hp5 hn
  omega

/-- Same conclusion for a LARGE PRIME q born after A², viewed as
a factor in an odd composite c*q: if the odd cofactor c>=3 and
the descendant lies before B²<=4A², then c=3 exactly.

Unlike an arbitrary sum over high owners, this is a SINGLE
occurrence-preserving q -> 3*q projection in the half-run. -/
theorem vfV2HalfRunLiveHighPrime_oddMultiplier_eq_three
    (A B c q : ℕ) (hBA : B ≤ 2 * A)
    (hcOdd : c % 2 = 1) (hc3 : 3 ≤ c)
    (hqLive : A ^ 2 ≤ q) (hchild : c * q < B ^ 2) :
    c = 3 := by
  have hBsq : B ^ 2 ≤ (2 * A) ^ 2 :=
    Nat.pow_le_pow_left hBA 2
  by_contra hcNe3
  have hc5 : 5 ≤ c := by omega
  have hprod : 5 * (A ^ 2) ≤ c * q := by
    calc
      5 * (A ^ 2) ≤ 5 * q := Nat.mul_le_mul_left 5 hqLive
      _ ≤ c * q := Nat.mul_le_mul_right q hc5
  nlinarith

/-- The live parent of a 3-child is forced into the EARLY run
below (4/3)*A², while the child lies in the LATE run above
3*A². Both restrictions are deterministic and strictly
separate the two root-scale windows. -/
theorem vfV2HalfRunThreeParent_earlyChild_late
    (A B q : ℕ) (hBA : B ≤ 2 * A)
    (hqLive : A ^ 2 ≤ q) (hchild : 3 * q < B ^ 2) :
    3 * q < 4 * A ^ 2 ∧ 3 * A ^ 2 ≤ 3 * q := by
  have hBsq : B ^ 2 ≤ (2 * A) ^ 2 :=
    Nat.pow_le_pow_left hBA 2
  constructor
  · nlinarith
  · exact Nat.mul_le_mul_left 3 hqLive

/-- Even the p=3 case has no indefinite within-half-run owner
tower: two successive ODD factor strips (both factors >=3)
always produce a child below the historical A² anchor. -/
theorem vfV2HalfRunTwoOddPrimeStrips_beforeAnchor
    (A B p q d : ℕ) (hA : 1 ≤ A) (hBA : B ≤ 2 * A)
    (hp : 3 ≤ p) (hq : 3 ≤ q)
    (hchild : p * (q * d) < B ^ 2) :
    d < A ^ 2 := by
  have hBsq : B ^ 2 ≤ (2 * A) ^ 2 :=
    Nat.pow_le_pow_left hBA 2
  have hprod : 3 * 3 ≤ p * q :=
    Nat.mul_le_mul hp hq
  have hqd : 9 * d ≤ p * (q * d) := by
    calc
      9 * d = (3 * 3) * d := by ring
      _ ≤ (p * q) * d := Nat.mul_le_mul_right d hprod
      _ = p * (q * d) := by ring
  have hApos : 1 ≤ A ^ 2 := by nlinarith [hA]
  by_contra hnot
  have hd : A ^ 2 ≤ d := Nat.le_of_not_gt hnot
  nlinarith

/-! ## The LATE A-wheel packet projects to prime-pair factors < 4*A

The ALREADY COMPILED native dyadic-owner decoder proves that every
composite survivor of the frozen initial wheel through A in any
subdoubling square band is n=p*q with primes A<p<q and n<B².
This arithmetic lemma supplies the stronger uniform projection:
q<4A, not merely q<A². All these prime vertices are known
long before the ORIGINAL square-run anchor. This is the exact
low-root-scale analogue of the upper-prime / reciprocal buckets.
-/

/-- If the least owner p is above the frozen root A, its partner
cofactor q is below 4*A throughout a subdoubling window.
No PNT, RH, primality or distribution hypothesis is needed here. -/
theorem vfV2HalfRunLateOwnerPartner_lt_fourAnchor
    (A B p q : ℕ) (hBA : B ≤ 2 * A)
    (hp : A < p) (hn : p * q < B ^ 2) :
    q < 4 * A := by
  have hBsq : B ^ 2 ≤ (2 * A) ^ 2 :=
    Nat.pow_le_pow_left hBA 2
  by_contra hnot
  have hq : 4 * A ≤ q := Nat.le_of_not_gt hnot
  have hp' : A + 1 ≤ p := by omega
  have hprod : (A + 1) * (4 * A) ≤ p * q :=
    Nat.mul_le_mul hp' hq
  nlinarith

/-- For A>=5 the SAME partner is strictly below the original
historical square anchor A², so the rank-two prime incidence
uses no as-yet-unknown prime identities. -/
theorem vfV2HalfRunLateOwnerPartner_beforeAnchor
    (A B p q : ℕ) (hA : 5 ≤ A) (hBA : B ≤ 2 * A)
    (hp : A < p) (hn : p * q < B ^ 2) :
    q < A ^ 2 := by
  have hq :=
    vfV2HalfRunLateOwnerPartner_lt_fourAnchor A B p q hBA hp hn
  have hlinear : 4 * A < A ^ 2 := by nlinarith [hA]
  exact hq.trans hlinear

/-- No prime parent q is consumed more than once by the one possible
within-run 3q-child map. Pairing is an injection on the REAL
physical integer sites, but is NOT itself a Co/Div sign estimate. -/
theorem vfV2HalfRunThreeChild_injective
    (q r : ℕ) (h : 3 * q = 3 * r) :
    q = r := by omega

/-! ## Cross-block high-prime parent-charge conservation

The old prime q is ONE negative original physical site (already inside
the earlier historical anchor). Its positive q-multiple descendants at
different R are distinct sites with their OWN native w_R.
An operation subtracting q's original negative site separately for EACH
later child does NOT preserve the physical source. -/

/-- Finite Fubini grouped by the genuine high prime q, with exactly ONE
historical negative charge per parent q. It must remain OUTSIDE the inner
sum over all later blocks R. This is only source-preserving accounting:
the sign of the resulting owner Gram remains arithmetic and OPEN. -/
theorem vfV2HighParentChargeOnceFubini
    (roots parents : Finset ℕ)
    (w : ℕ → ℝ) (children : ℕ → ℕ → ℝ)
    (oldNegative : ℕ → ℝ) :
    (∑ r ∈ roots, ∑ q ∈ parents,
      if r < q then w r * children r q else 0)
      - (∑ q ∈ parents, oldNegative q) =
      ∑ q ∈ parents,
        ((∑ r ∈ roots,
          if r < q then w r * children r q else 0)
          - oldNegative q) := by
  calc
    _ = (∑ q ∈ parents, ∑ r ∈ roots,
          if r < q then w r * children r q else 0)
          - (∑ q ∈ parents, oldNegative q) := by
        rw [Finset.sum_comm]
    _ = _ := by
        rw [Finset.sum_sub_distrib]

/-- The EXACT overcount from subtracting the SAME old parent's negative
charge h independently at every later child: (number of children - 1)*h.
For more than one child and positive h this is STRICT extra (fake)
restoring capacity, not a true first-bad Co/Div contraction. -/
theorem vfV2HighParentRepeatedChargeOvercount
    (kids : Finset ℕ) (childMass : ℕ → ℝ) (oldNegative : ℝ) :
    (∑ c ∈ kids, (childMass c - oldNegative)) +
        ((kids.card : ℝ) - 1) * oldNegative =
      (∑ c ∈ kids, childMass c) - oldNegative := by
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring


theorem vfV2SparseCrossOwnerSquare (s₁ s₂ : ℝ) :
    (s₁ + s₂) ^ 2 = s₁ ^ 2 + s₂ ^ 2 + 2 * s₁ * s₂ := by
  ring


/-! ## Fully generic unit-step + uniquely-owned carrier rules

These claims HOLD FOR EVERY Boolean unit-jump selection and every finite
owner assignment that covers its seats. They establish precisely what the
generic monotonically increasing arithmetic-step/owner model grants, before
any actual-prime-specific restriction on its signed historical phases.
They DO NOT imply a radial cone: a trivial zero-prime binary selector and
the separately checked all-state counterexample refute such an inference. -/

/-- A completely generic integer unit-step count; prime counting is the
specific selector \`fun n => decide n.Prime\`. -/
def vfV2GenericUnitStepCount (isJump : ℕ → Bool) (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range N, if isJump n then 1 else 0

/-- The next integer changes a generic counting staircase by exactly one
unit or by zero. No arithmetic distribution assumptions enter. -/
theorem vfV2GenericUnitStepCount_succ (isJump : ℕ → Bool) (N : ℕ) :
    vfV2GenericUnitStepCount isJump (N + 1) =
      vfV2GenericUnitStepCount isJump N +
        (if isJump N then 1 else 0) := by
  exact Finset.sum_range_succ (fun n => if isJump n then 1 else 0) N

theorem vfV2GenericUnitStepCount_monotone (isJump : ℕ → Bool) :
    Monotone (vfV2GenericUnitStepCount isJump) := by
  apply monotone_nat_of_le_succ
  intro N
  rw [vfV2GenericUnitStepCount_succ]
  omega

/-- The exact finite prime/nonprime seat population, with neither even
sites nor manufactured reference mass added. -/
theorem vfV2FiniteActualPrimeNonprimePopulation (seats : Finset ℕ) :
    (∑ n ∈ seats, if Nat.Prime n then (1 : ℝ) else 0) +
      (∑ n ∈ seats, if ¬ Nat.Prime n then (1 : ℝ) else 0) =
        (seats.card : ℝ) := by
  classical
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ _n ∈ seats, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro n _hn
      by_cases hp : Nat.Prime n <;> simp [hp]
    _ = (seats.card : ℝ) := by simp

/-- The actual-prime 0/1 selector has the correct affine VF-minus-prime
signed mass on EVERY finite carrier, regardless of distribution. -/
theorem vfV2FiniteActualPrimeSignedSeatMass
    (seats : Finset ℕ) (w : ℝ) :
    (∑ n ∈ seats,
        (w - if Nat.Prime n then (1 : ℝ) else 0)) =
      w * (seats.card : ℝ) -
        ∑ n ∈ seats, if Nat.Prime n then (1 : ℝ) else 0 := by
  classical
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

/-- A UNIQUE owner function partitions any finite weighted source exactly
once; it does NOT make the resulting signed quadratic form nonpositive. -/
theorem vfV2UniqueOwnerFiniteFubini
    (seats owners : Finset ℕ) (owner : ℕ → ℕ) (charge : ℕ → ℝ)
    (howner : ∀ n ∈ seats, owner n ∈ owners) :
    (∑ n ∈ seats, charge n) =
      ∑ p ∈ owners, ∑ n ∈ seats,
        if p = owner n then charge n else 0 := by
  classical
  calc
    _ = ∑ n ∈ seats, ∑ p ∈ owners,
          if p = owner n then charge n else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [howner n hn]
    _ = _ := by rw [Finset.sum_comm]

/-- Generic once-counted parent incidence carries the cross-block sum
without supplying a new historical negative copy per child. -/
theorem vfV2UniqueOwnerOnceCharge
    (seats owners : Finset ℕ) (owner : ℕ → ℕ)
    (charge : ℕ → ℝ) (historicalCharge : ℕ → ℝ)
    (howner : ∀ n ∈ seats, owner n ∈ owners) :
    (∑ n ∈ seats, charge n) -
      (∑ p ∈ owners, historicalCharge p) =
      ∑ p ∈ owners,
        ((∑ n ∈ seats,
          if p = owner n then charge n else 0) -
          historicalCharge p) := by
  rw [vfV2UniqueOwnerFiniteFubini seats owners owner charge howner]
  rw [Finset.sum_sub_distrib]



/-! ## Actual-owner age, strict-past conditioning, and delayed signed flux

These are UNCONDITIONAL finite conservation and algebra lemmas.  The observed
higher-wall-occupancy / older-parent conditional inward drift is empirical;
NO expectation, regression coefficient, near-wall feedback inequality or
Sector Six payment is asserted here. -/

/-- The four exact numerical parent-age cohorts.  If b is the square-root
birth index of a genuine high prime q, the age is (R-b)/R.
0: age < 0.55; 1: 0.55..0.70; 2: 0.70..0.85; 3: >=0.85.
Integer comparisons avoid any floating-point classification. -/
def vfV2HighPrimeParentAgeBucket (R birth : ℕ) : Fin 4 :=
  if 20 * birth ≤ 3 * R then 3
  else if 10 * birth ≤ 3 * R then 2
  else if 20 * birth ≤ 9 * R then 1
  else 0

/-- When a genuine prime q>R is an odd composite factor n=c*q with c>=3
in the original strict OPEN square band, q already predates R^2. -/
theorem vfV2HighPrimeParentPrecedesCurrentSquare
    (R c q birth : ℕ) (hR : 3 ≤ R) (hc : 3 ≤ c)
    (hsite : c * q < (R + 1) ^ 2)
    (hbirth : birth ^ 2 ≤ q) :
    q < R ^ 2 ∧ birth < R := by
  have hthree : 3 * q ≤ c * q :=
    Nat.mul_le_mul_right q hc
  have hroot : (R + 1) ^ 2 ≤ 3 * R ^ 2 := by
    nlinarith
  have hq : q < R ^ 2 := by
    nlinarith
  constructor
  · exact hq
  · nlinarith

/-- There cannot be two distinct genuine prime factors q,s>R in the
original strict OPEN square band.  If they were distinct, their coprime
product would be at least (R+1)^2 and would divide n<(R+1)^2.
This makes the high-prime ancestor classification genuinely intrinsic. -/
theorem vfV2HighPrimeFactorUniqueOnOpenSquare
    {R n q s : ℕ} (hsite : R ^ 2 < n ∧ n < (R + 1) ^ 2)
    (hqPrime : q.Prime) (hsPrime : s.Prime)
    (hq : R < q) (hs : R < s)
    (hqn : q ∣ n) (hsn : s ∣ n) :
    q = s := by
  by_contra hne
  have hcop : q.Coprime s := by
    rw [hqPrime.coprime_iff_not_dvd]
    intro hdiv
    exact hne ((Nat.prime_dvd_prime_iff_eq hqPrime hsPrime).mp hdiv)
  have hqsn : q * s ∣ n :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hqn hsn
  have hqsnLe : q * s ≤ n :=
    Nat.le_of_dvd (by omega) hqsn
  have hqge : R + 1 ≤ q := by omega
  have hsge : R + 1 ≤ s := by omega
  have hprod : (R + 1) ^ 2 ≤ q * s := by
    calc
      (R + 1) ^ 2 = (R + 1) * (R + 1) := by ring
      _ ≤ q * (R + 1) := Nat.mul_le_mul_right (R + 1) hqge
      _ ≤ q * s := Nat.mul_le_mul_left q hsge
  omega

/-- Age classification partitions EXISTING sites; each site supplies its
original single weight exactly once, not an independent ancestor payment. -/
def vfV2AgeCohortNativeMass
    (R : ℕ) (sites : Finset ℕ) (birthRoot : ℕ → ℕ)
    (weight : ℕ → ℝ) (bucket : Fin 4) : ℝ :=
  ∑ n ∈ sites,
    if vfV2HighPrimeParentAgeBucket R (birthRoot n) = bucket
    then weight n else 0

theorem vfV2AgeCohortNativeMass_sum
    (R : ℕ) (sites : Finset ℕ) (birthRoot : ℕ → ℕ)
    (weight : ℕ → ℝ) :
    (∑ bucket : Fin 4,
      vfV2AgeCohortNativeMass R sites birthRoot weight bucket) =
      ∑ n ∈ sites, weight n := by
  classical
  simp only [vfV2AgeCohortNativeMass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  simp

/-- A site cannot simultaneously be paid by two different age cohorts. -/
theorem vfV2AgeCohortNativeMass_disjoint
    (R n : ℕ) (birthRoot : ℕ → ℕ) (weight : ℕ → ℝ)
    (a b : Fin 4) (hab : a ≠ b) :
    (if vfV2HighPrimeParentAgeBucket R (birthRoot n) = a
       then weight n else 0) *
    (if vfV2HighPrimeParentAgeBucket R (birthRoot n) = b
       then weight n else 0) = 0 := by
  by_cases ha : vfV2HighPrimeParentAgeBucket R (birthRoot n) = a
  · simp [ha, hab]
  · simp [ha]

/-- Cross-cohort Gram products cannot be omitted or replaced by a sum
of squares: owner splitting does NOT automatically give contraction. -/
theorem vfV2AgeFourCohortFullGram (a b c d : ℝ) :
    (a + b + c + d) ^ 2 =
      a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 +
        2 * (a*b + a*c + a*d + b*c + b*d + c*d) := by
  ring

/-- Prime and mature/high-parent/smooth composite corrections at one block
still total -deltaPrime in original VF currency after age partition.
No age bucket contributes independent negative material. -/
theorem vfV2FourAgeCohorts_do_not_create_restoringMass
    (w dP d0 d1 d2 d3 dSmooth : ℝ)
    (hseats : dP + d0 + d1 + d2 + d3 + dSmooth = 0) :
    (w - 1) * dP +
      w * d0 + w * d1 + w * d2 + w * d3 + w * dSmooth =
      -dP := by
  calc
    _ = w * (dP + d0 + d1 + d2 + d3 + dSmooth) - dP := by ring
    _ = -dP := by rw [hseats]; ring

/-- The age reference differs from the actual age census only through
signed, once-counted cohort discrepancies. -/
theorem vfV2AgeCohortReferenceDifference
    (actual reference : Fin 4 → ℝ) :
    (∑ bucket : Fin 4, (actual bucket - reference bucket)) =
      (∑ bucket : Fin 4, actual bucket) -
      (∑ bucket : Fin 4, reference bucket) := by
  rw [Finset.sum_sub_distrib]

/-- The occupancy conditioning window strictly PRECEDES the response root. -/
def vfV2StrictPastRoots (R span : ℕ) : Finset ℕ :=
  Finset.Ico (R - span) R

theorem vfV2StrictPastRoots_lt_current
    {R span k : ℕ} (hk : k ∈ vfV2StrictPastRoots R span) :
    k < R := by
  exact (Finset.mem_Ico.mp hk).2

/-- Finite historical occupancy rank; NO future score is inspected.
The score can be the actual |D_R|/(2R log R), but is not assumed random. -/
def vfV2PastOnlyRank (score : ℕ → ℝ) (R span : ℕ) : ℕ :=
  ((vfV2StrictPastRoots R span).filter
      (fun t => score t ≤ score R)).card

/-- Historical high/low wall-occupancy classifications used by the audit.
These are definitions, not unproved arithmetic claims. -/
def vfV2PastOnlyHighOccupancy
    (score : ℕ → ℝ) (R span : ℕ) : Prop :=
  4 * (vfV2StrictPastRoots R span).card ≤
    5 * vfV2PastOnlyRank score R span

def vfV2PastOnlyLowOccupancy
    (score : ℕ → ℝ) (R span : ℕ) : Prop :=
  5 * vfV2PastOnlyRank score R span ≤
    (vfV2StrictPastRoots R span).card

/-- The exact signed actual minus floor-Li block flux when
E(R) = pi(R^2) - Q(R^2). -/
def vfV2BlockFlux (E : ℕ → ℝ) (R : ℕ) : ℝ :=
  E (R + 1) - E R

theorem vfV2BlockFlux_telescope
    (E : ℕ → ℝ) {A B : ℕ} (hAB : A ≤ B) :
    (∑ r ∈ Finset.Ico A B, vfV2BlockFlux E r) =
      E B - E A := by
  induction B, hAB using Nat.le_induction with
  | base =>
      simp
  | succ B hAB ih =>
      rw [Finset.sum_Ico_succ_top hAB, ih]
      unfold vfV2BlockFlux
      ring

/-- Past-oriented future observation excludes block R itself and starts at
R+1.  orientation=-1 in the observed negative-D cohort. -/
def vfV2DelayedOrientedFlux
    (E : ℕ → ℝ) (orientation : ℝ)
    (R horizon : ℕ) : ℝ :=
  orientation * (E (R + 1 + horizon) - E (R + 1))

theorem vfV2DelayedFlux_eq_futureBlockSum
    (E : ℕ → ℝ) (orientation : ℝ)
    (R horizon : ℕ) :
    vfV2DelayedOrientedFlux E orientation R horizon =
      orientation *
      (∑ r ∈ Finset.Ico (R + 1) (R + 1 + horizon),
        vfV2BlockFlux E r) := by
  unfold vfV2DelayedOrientedFlux
  rw [vfV2BlockFlux_telescope E (by omega)]

theorem vfV2CurrentPlusDelayedFlux
    (E : ℕ → ℝ) (orientation : ℝ)
    (R horizon : ℕ) :
    orientation * (E (R + 1 + horizon) - E R) =
      orientation * vfV2BlockFlux E R +
        vfV2DelayedOrientedFlux E orientation R horizon := by
  unfold vfV2BlockFlux vfV2DelayedOrientedFlux
  ring

/-- Exact channel-clearance motion. No age-correlated inward drift is
inferred from the identity or introduced as a hypothesis. -/
theorem vfV2DelayedMovingWallClearance
    (W D E b : ℕ → ℝ) (orientation : ℝ)
    (R horizon : ℕ)
    (hstart : D (R + 1) = E (R + 1) + b (R + 1))
    (hend : D (R + 1 + horizon) =
      E (R + 1 + horizon) + b (R + 1 + horizon)) :
    (W (R + 1 + horizon) - orientation * D (R + 1 + horizon)) -
      (W (R + 1) - orientation * D (R + 1)) =
    (W (R + 1 + horizon) - W (R + 1)) -
      vfV2DelayedOrientedFlux E orientation R horizon -
      orientation * (b (R + 1 + horizon) - b (R + 1)) := by
  rw [hstart, hend]
  unfold vfV2DelayedOrientedFlux
  ring

/-- Conditional two-way state-age stratification is a finite partition:
all nine joint-cell weighted fluxes reassemble exactly, without independence
assumptions, future peeking or a new absolute denominator. -/
def vfV2JointDelayedFluxCell
    (roots : Finset ℕ) (occ : ℕ → Fin 3) (age : ℕ → Fin 3)
    (E : ℕ → ℝ) (orientation : ℕ → ℝ) (horizon : ℕ)
    (o : Fin 3) (a : Fin 3) : ℝ :=
  ∑ R ∈ roots,
    if occ R = o ∧ age R = a
    then vfV2DelayedOrientedFlux E (orientation R) R horizon
    else 0

theorem vfV2JointDelayedFluxCell_sum
    (roots : Finset ℕ) (occ : ℕ → Fin 3) (age : ℕ → Fin 3)
    (E : ℕ → ℝ) (orientation : ℕ → ℝ) (horizon : ℕ) :
    (∑ o : Fin 3, ∑ a : Fin 3,
      vfV2JointDelayedFluxCell roots occ age E orientation horizon o a) =
      ∑ R ∈ roots, vfV2DelayedOrientedFlux E (orientation R) R horizon := by
  classical
  simp only [vfV2JointDelayedFluxCell]
  calc
    _ = ∑ o : Fin 3, ∑ R ∈ roots, ∑ a : Fin 3,
          (if occ R = o ∧ age R = a
           then vfV2DelayedOrientedFlux E (orientation R) R horizon
           else 0) := by
      apply Finset.sum_congr rfl
      intro o _
      rw [Finset.sum_comm]
    _ = ∑ R ∈ roots, ∑ o : Fin 3, ∑ a : Fin 3,
          (if occ R = o ∧ age R = a
           then vfV2DelayedOrientedFlux E (orientation R) R horizon
           else 0) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro R _
      calc
        (∑ o : Fin 3, ∑ a : Fin 3,
            (if occ R = o ∧ age R = a
             then vfV2DelayedOrientedFlux E (orientation R) R horizon
             else 0)) =
          ∑ o : Fin 3,
            (if occ R = o
             then vfV2DelayedOrientedFlux E (orientation R) R horizon
             else 0) := by
            apply Finset.sum_congr rfl
            intro o _
            by_cases ho : occ R = o
            · simp [ho]
            · simp [ho]
        _ = vfV2DelayedOrientedFlux E (orientation R) R horizon := by simp

/-- Pure finite classification cannot force arbitrary future prime-like
staircases to mean-revert: a nontrivial signed arithmetic result is needed. -/
theorem vfV2NoUniversalDelayedInwardFlux :
    ¬ ∀ E : ℕ → ℝ, ∀ (R horizon : ℕ),
      vfV2DelayedOrientedFlux E 1 R horizon ≤ 0 := by
  intro hall
  have h := hall (fun n : ℕ => (n : ℝ)) 0 1
  norm_num [vfV2DelayedOrientedFlux] at h


/-! ## First-bad wall-normal form: necessary, never sufficient

These are pure algebraic implications of a prior-good endpoint and a later
wall breach. They add NO prime-distribution hypothesis, no new physical seat,
and no unwarranted sign estimate on the actual owner Gram.
-/

/-- Any breach from inside the previous wall requires a current signed
increment larger in magnitude than the wall growth. -/
theorem vfV2FirstBad_requires_strictCurrentDeviation
    (D delta WA WB : ℝ)
    (hprior : |D| ≤ WA)
    (hbad : WB < |D + delta|) :
    WB - WA < |delta| := by
  have htri := abs_add_le D delta
  linarith

/-- Upper first bad forces a genuine positive outward increment. -/
theorem vfV2FirstBad_positive_outward
    (D delta WA WB : ℝ)
    (hprior : |D| ≤ WA) (hwallGrowth : WA ≤ WB)
    (hbad : WB < D + delta) :
    0 < delta ∧ WB - D < delta := by
  have hD : D ≤ WA := (abs_le.mp hprior).2
  constructor <;> linarith

/-- Lower first bad forces a genuine negative outward increment. -/
theorem vfV2FirstBad_negative_outward
    (D delta WA WB : ℝ)
    (hprior : |D| ≤ WA) (hwallGrowth : WA ≤ WB)
    (hbad : D + delta < -WB) :
    delta < 0 ∧ delta < -WB - D := by
  have hD : -WA ≤ D := (abs_le.mp hprior).1
  constructor <;> linarith

/-- A supposed first bad has the same strict sign as the increment causing
it, regardless of the sign of the earlier defect. -/
theorem vfV2FirstBad_outward_orientation
    (D delta WA WB : ℝ)
    (hprior : |D| ≤ WA) (hwallGrowth : WA ≤ WB)
    (hbad : WB < |D + delta|) :
    (0 < D + delta ∧ 0 < delta) ∨
      (D + delta < 0 ∧ delta < 0) := by
  rcases lt_or_ge (D + delta) 0 with hneg | hnonneg
  · have hbadneg : D + delta < -WB := by
      rw [abs_of_neg hneg] at hbad
      linarith
    exact Or.inr ⟨hneg,
      (vfV2FirstBad_negative_outward D delta WA WB
        hprior hwallGrowth hbadneg).1⟩
  · have hbadpos : WB < D + delta := by
      rwa [abs_of_nonneg hnonneg] at hbad
    have hsign :=
      (vfV2FirstBad_positive_outward D delta WA WB
        hprior hwallGrowth hbadpos).1
    have hWA0 : 0 ≤ WA := (abs_nonneg D).trans hprior
    exact Or.inl ⟨by linarith, hsign⟩

/-- The prior-good wall does NOT provide a nonnegative anchored NNS
potential, even if the next endpoint ALSO remains inside its wall.
This is a scalar counterstate, NOT an actual-prime counterexample. -/
theorem vfV2PriorGoodEvenNextGood_doesNotForcePhi_nonneg :
    ∃ D w P C WA WB : ℝ,
      |D| ≤ WA ∧ WA ≤ WB ∧
      |vfV2Next D w P C| ≤ WB ∧
      vfV2Balance D w P C < 0 := by
  refine ⟨20, 1 / 4, 4, 4, 20, 23, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [vfV2Next, vfV2Balance, vfV2Upper, vfV2Lower]

/-! ## Adversarial-to-adversarial: historical factor locks and finite sieve

An artificial prime drought can breach the K=2 wall. The past primes up to
A^2, however, already determine the complete primality of every integer
A^2 < n < A^4: all composite witnesses lie below sqrt(n) < A^2.
This is an EXACT structural sieve lock, not a lower prime-density estimate.

The finite Bonferroni owner bound below is an actual combinatorial inequality.
It explicitly retains every unresolved high-owner union occurrence; it cannot
produce a UNIFORM numerical saving without additional arithmetic information.
-/

/-- Every composite in a historical-prefix-locked range must present an
actual prime-factor certificate from the ORIGINAL historical prefix. -/
def vfV2HistoricalCompositeWitness (A n : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ≤ A ^ 2 ∧ p ∣ n

/-- Historical genuine prime owners up through A² already decide primality
from A² up to (A²)². The proof uses literal least prime factors, not PNT. -/
theorem vfV2HistoricalPrefixLocksPrime
    {A n : ℕ} (hA : 2 ≤ A) (hlo : A ^ 2 < n)
    (hhi : n < (A ^ 2) ^ 2) :
    n.Prime ↔ ¬ vfV2HistoricalCompositeWitness A n := by
  constructor
  · intro hnprime ⟨p, hpprime, hpbound, hpdvd⟩
    have hpeq : p = n :=
      (Nat.prime_dvd_prime_iff_eq hpprime hnprime).mp hpdvd
    omega
  · intro hnone
    by_contra hnprime
    have hnpos : 0 < n := by omega
    have hnnotone : n ≠ 1 := by
      have hAsq : 4 ≤ A ^ 2 := by nlinarith [hA]
      omega
    let p := n.minFac
    have hpprime : p.Prime := by
      simpa [p] using Nat.minFac_prime hnnotone
    have hpdvd : p ∣ n := by
      simpa [p] using Nat.minFac_dvd n
    have hpsq : p ^ 2 ≤ n := by
      simpa [p] using Nat.minFac_sq_le_self hnpos hnprime
    have hpbound : p ≤ A ^ 2 := by
      by_contra hpnot
      have hle : A ^ 2 ≤ p := by omega
      have hpow : (A ^ 2) ^ 2 ≤ p ^ 2 :=
        Nat.pow_le_pow_left hle 2
      omega
    exact hnone ⟨p, hpprime, hpbound, hpdvd⟩

/-- All-drought is EQUIVALENT to a complete historical-prime covering of
the same range, not something that can be posited independently. -/
theorem vfV2HistoricalDrought_iff_completeFactorCover
    {A L U : ℕ}
    (hA : 2 ≤ A) (hL : A ^ 2 ≤ L) (hU : U ≤ (A ^ 2) ^ 2) :
    (∀ n : ℕ, L < n → n < U → ¬ n.Prime) ↔
      (∀ n : ℕ, L < n → n < U →
        vfV2HistoricalCompositeWitness A n) := by
  constructor
  · intro hdrought n hnL hnU
    have hiff :=
      vfV2HistoricalPrefixLocksPrime hA
        (lt_of_le_of_lt hL hnL) (lt_of_lt_of_le hnU hU)
    by_contra hnowitness
    exact (hdrought n hnL hnU) (hiff.mpr hnowitness)
  · intro hcover n hnL hnU hnprime
    have hiff :=
      vfV2HistoricalPrefixLocksPrime hA
        (lt_of_le_of_lt hL hnL) (lt_of_lt_of_le hnU hU)
    exact (hiff.mp hnprime) (hcover n hnL hnU)

/-- The physical sites that pass only a selected SMALL prime wheel. -/
def vfV2PartialWheelSites (sites small : Finset ℕ) : Finset ℕ :=
  sites.filter (fun n => ∀ p ∈ small, ¬ p ∣ n)

/-- A high-prime owner p captures just its genuine occurrences on the
small-wheel survivors. Each physical n is a site, not a reusable credit. -/
def vfV2PartialWheelOwnerHits
    (sites small : Finset ℕ) (p : ℕ) : Finset ℕ :=
  (vfV2PartialWheelSites sites small).filter (fun n => p ∣ n)

/-- The whole owner-union has cardinality at most the sum of individual
owner-fiber cardinalities. This is deliberately the one-sided Bonferroni
INEQUALITY rather than a false disjoint-owner identity. -/
theorem vfV2FiniteOwnerUnion_card_le_sum
    (high : Finset ℕ) (hits : ℕ → Finset ℕ) :
    (high.biUnion hits).card ≤ ∑ p ∈ high, (hits p).card := by
  classical
  induction high using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      calc
        ((insert p s).biUnion hits).card =
            ((hits p) ∪ (s.biUnion hits)).card := by simp
        _ ≤ (hits p).card + (s.biUnion hits).card :=
          Finset.card_union_le _ _
        _ ≤ (hits p).card + ∑ q ∈ s, (hits q).card :=
          Nat.add_le_add_left ih _
        _ = ∑ q ∈ insert p s, (hits q).card := by
          simp [Finset.sum_insert, hp]

/-- TRUE finite partial-wheel sieve lower bound.

If every nonprime site is covered by a prime factor in small U high, then:
rough survivors <= genuine primes + counted high-factor hits.
The high-factor hits may overlap; all are kept, so no independence,
equidistribution or signed owner cancellation is assumed. -/
theorem vfV2PartialWheelForcedPrimeLower
    (sites small high : Finset ℕ)
    (hfactor : ∀ n ∈ sites, ¬ n.Prime →
      ∃ p ∈ small ∪ high, p ∣ n) :
    (vfV2PartialWheelSites sites small).card ≤
      (sites.filter Nat.Prime).card +
        ∑ p ∈ high, (vfV2PartialWheelOwnerHits sites small p).card := by
  classical
  let rough := vfV2PartialWheelSites sites small
  let hits := fun p => vfV2PartialWheelOwnerHits sites small p
  have hsub : rough ⊆
      (sites.filter Nat.Prime) ∪ high.biUnion hits := by
    intro n hnrough
    have hnsite : n ∈ sites := (Finset.mem_filter.mp hnrough).1
    have hsmall : ∀ p ∈ small, ¬ p ∣ n :=
      (Finset.mem_filter.mp hnrough).2
    by_cases hnprime : n.Prime
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨hnsite, hnprime⟩))
    · obtain ⟨p, hpunion, hpdiv⟩ :=
        hfactor n hnsite hnprime
      have hphigh : p ∈ high := by
        rcases Finset.mem_union.mp hpunion with hpsmall | hphigh
        · exact False.elim ((hsmall p hpsmall) hpdiv)
        · exact hphigh
      apply Finset.mem_union.mpr
      right
      exact Finset.mem_biUnion.mpr
        ⟨p, hphigh, Finset.mem_filter.mpr ⟨hnrough, hpdiv⟩⟩
  calc
    rough.card ≤
        ((sites.filter Nat.Prime) ∪ high.biUnion hits).card :=
      Finset.card_le_card hsub
    _ ≤ (sites.filter Nat.Prime).card + (high.biUnion hits).card :=
      Finset.card_union_le _ _
    _ ≤ (sites.filter Nat.Prime).card +
          ∑ p ∈ high, (hits p).card :=
      Nat.add_le_add_left
        (vfV2FiniteOwnerUnion_card_le_sum high hits) _

/-! ## Specialize the union bound to genuine historical prime-factor incidence -/

/-- The ACTUAL primes known at or before the historical anchor A². -/
def vfV2HistoricalPrimeIndex (A : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (A ^ 2)).filter Nat.Prime

/-- The subset of historical owners already in the selected small wheel. -/
def vfV2HistoricalSmallPrimeIndex (A y : ℕ) : Finset ℕ :=
  (vfV2HistoricalPrimeIndex A).filter (fun p => p ≤ y)

/-- The remaining historical owners, with NO hypothetical future primes. -/
def vfV2HistoricalHighPrimeIndex (A y : ℕ) : Finset ℕ :=
  (vfV2HistoricalPrimeIndex A).filter (fun p => y < p)

/-- The original OPEN square-run integer sites, not invented synthetic seats. -/
def vfV2HistoricalSquareRunSites (A B : ℕ) : Finset ℕ :=
  Finset.Ioo (A ^ 2) (B ^ 2)

/-- ACTUAL factorization supplies the complete cover hypothesis in the
finite wheel Bonferroni inequality. Every factor p<=B is already present
in the genuine prefix through A² whenever B<=A².

The arithmetic conclusion is an UNCONDITIONAL exact finite lower bound,
NOT a uniform positive bound for all root scales. -/
theorem vfV2HistoricalPrimePartialWheelBonferroni
    {A B y : ℕ} (hA : 2 ≤ A) (hB : B ≤ A ^ 2) :
    (vfV2PartialWheelSites
      (vfV2HistoricalSquareRunSites A B)
      (vfV2HistoricalSmallPrimeIndex A y)).card ≤
    ((vfV2HistoricalSquareRunSites A B).filter Nat.Prime).card +
      ∑ p ∈ vfV2HistoricalHighPrimeIndex A y,
        (vfV2PartialWheelOwnerHits
          (vfV2HistoricalSquareRunSites A B)
          (vfV2HistoricalSmallPrimeIndex A y) p).card := by
  classical
  apply vfV2PartialWheelForcedPrimeLower
  intro n hn hncomp
  have hnI : A ^ 2 < n ∧ n < B ^ 2 := by
    exact Finset.mem_Ioo.mp hn
  have hUB : B ^ 2 ≤ (A ^ 2) ^ 2 :=
    Nat.pow_le_pow_left hB 2
  have hw : vfV2HistoricalCompositeWitness A n := by
    by_contra hnowitness
    have hp := (vfV2HistoricalPrefixLocksPrime
      hA hnI.1 (lt_of_lt_of_le hnI.2 hUB)).mpr hnowitness
    exact hncomp hp
  rcases hw with ⟨p, hpPrime, hpBound, hpDvd⟩
  have hpKnown : p ∈ vfV2HistoricalPrimeIndex A := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨hpPrime.two_le, hpBound⟩, hpPrime⟩
  refine ⟨p, ?_, hpDvd⟩
  by_cases hpy : p ≤ y
  · exact Finset.mem_union.mpr (Or.inl
      (Finset.mem_filter.mpr ⟨hpKnown, hpy⟩))
  · have hpy' : y < p := by omega
    exact Finset.mem_union.mpr (Or.inr
      (Finset.mem_filter.mpr ⟨hpKnown, hpy'⟩))

/-- Exact LOWER-wall first-crossing condition in historical-buffer currency.
No arbitrary first-bad state can replace the genuine historical D_R. -/
theorem vfV2LowerWallBreach_iff_historicalBufferShortfall
    (D P V WR Wnext : ℝ) :
    D + P - V < -Wnext ↔
      D + WR < (V - P) - (Wnext - WR) := by
  constructor <;> intro h <;> linarith

/-- Exact UPPER-wall counterpart. Genuine history must retain this buffer too. -/
theorem vfV2UpperWallBreach_iff_historicalBufferShortfall
    (D P V WR Wnext : ℝ) :
    Wnext < D + P - V ↔
      WR - D < (P - V) - (Wnext - WR) := by
  constructor <;> intro h <;> linarith

/-! ## Completed square blocks INSIDE an incomplete wheel

A fixed finite wheel may have an enormous CRT period Q, with no full
Q-period contained in the tested interval. This does NOT prevent signed
complete square-band errors from telescoping: after every completed band
the carry is a single prefix residual. Over any consecutive run the
net cost is only the TWO boundary prefix errors, not the sum of
individual per-band absolute errors. This is genuine cancellation in the
fixed small-wheel *geometry*, not yet cancellation of the residual
actual high-prime composite owners.

The following floor-prefix estimate is UNIFORM even when Q greatly
exceeds the physical run: for an actual squarefree-divisor carrier its
cardinality is 2^(number of selected primes), rather than Q.
-/

/-- The exact centered phase of ANY fixed-wheel counting prefix. -/
def vfV2FixedWheelPrefixPhase
    (F : ℕ → ℝ) (density : ℝ) (x : ℕ) : ℝ :=
  F x - density * (x : ℝ)

/-- Signed phase on a COMPLETED square band, with the exact 2R+1 width. -/
def vfV2CompletedSquareWheelBandPhase
    (F : ℕ → ℝ) (density : ℝ) (R : ℕ) : ℝ :=
  F ((R + 1) ^ 2) - F (R ^ 2) -
    density * ((2 * R + 1 : ℕ) : ℝ)

/-- Every consecutive run of COMPLETED square blocks has only TWO
incomplete-wheel endpoint phases, irrespective of the CRT period.
No pointwise bound or probabilistic cancellation is assumed. -/
theorem vfV2CompletedSquareWheelBandPhase_telescope
    (F : ℕ → ℝ) (density : ℝ) (A B : ℕ)
    (hAB : A ≤ B) :
    (∑ R ∈ Finset.Ico A B,
      vfV2CompletedSquareWheelBandPhase F density R) =
      vfV2FixedWheelPrefixPhase F density (B ^ 2) -
      vfV2FixedWheelPrefixPhase F density (A ^ 2) := by
  induction B, hAB using Nat.le_induction with
  | base =>
      simp [vfV2FixedWheelPrefixPhase]
  | succ B hAB ih =>
      rw [Finset.sum_Ico_succ_top hAB, ih]
      unfold vfV2CompletedSquareWheelBandPhase
        vfV2FixedWheelPrefixPhase
      push_cast
      ring

/-- A uniform endpoint wheel-residual bound costs only twice that
bound over arbitrarily many completed square blocks, with NO block
count factor. This does not supply such a bound for the prime owner
remainder; only for the selected wheel. -/
theorem vfV2CompletedSquareWheelBandPhase_le_two_boundary
    (F : ℕ → ℝ) (density C : ℝ) (A B : ℕ)
    (hAB : A ≤ B)
    (hbound : ∀ x : ℕ,
      |vfV2FixedWheelPrefixPhase F density x| ≤ C) :
    |∑ R ∈ Finset.Ico A B,
      vfV2CompletedSquareWheelBandPhase F density R| ≤ 2 * C := by
  rw [vfV2CompletedSquareWheelBandPhase_telescope F density A B hAB]
  calc
    |vfV2FixedWheelPrefixPhase F density (B ^ 2) -
        vfV2FixedWheelPrefixPhase F density (A ^ 2)| ≤
      |vfV2FixedWheelPrefixPhase F density (B ^ 2)| +
        |vfV2FixedWheelPrefixPhase F density (A ^ 2)| :=
      by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (vfV2FixedWheelPrefixPhase F density (B ^ 2)) 0 (vfV2FixedWheelPrefixPhase F density (A ^ 2)))
    _ ≤ C + C :=
      add_le_add (hbound _) (hbound _)
    _ = 2 * C := by ring

/-! ## Literal OPEN square physical carrier: the SECOND root-scale telescope

The original VF block is (R²,(R+1)²), OPEN at both square ends.
A fixed-wheel coprime square endpoint contributes a ROUGH COMPOSITE,
never an actual prime or a new NNS physical site. Thus one must also
subtract the corresponding ROOT-wheel increment F(R+1)-F(R), because
gcd((R+1)²,Q)=1 iff gcd(R+1,Q)=1.

The result is a DOUBLE endpoint telescope. Dropping the root-scale
correction would accidentally introduce squareful sites into the odd
physical carrier and invalidate the original NNS denominator.
-/

/-- Signed one-step root-wheel phase. -/
def vfV2FixedWheelRootStepPhase
    (F : ℕ → ℝ) (density : ℝ) (R : ℕ) : ℝ :=
  F (R + 1) - F R - density

/-- The centered OPEN square-block wheel phase: completed square-phase
minus the root phase for the potentially surviving terminal square. -/
def vfV2CompletedOpenSquareWheelBandPhase
    (F : ℕ → ℝ) (density : ℝ) (R : ℕ) : ℝ :=
  vfV2CompletedSquareWheelBandPhase F density R -
    vfV2FixedWheelRootStepPhase F density R

/-- Root-level deletion of the square endpoint ALSO telescopes. -/
theorem vfV2FixedWheelRootStepPhase_telescope
    (F : ℕ → ℝ) (density : ℝ) (A B : ℕ)
    (hAB : A ≤ B) :
    (∑ R ∈ Finset.Ico A B,
      vfV2FixedWheelRootStepPhase F density R) =
      vfV2FixedWheelPrefixPhase F density B -
      vfV2FixedWheelPrefixPhase F density A := by
  induction B, hAB using Nat.le_induction with
  | base =>
      simp [vfV2FixedWheelPrefixPhase]
  | succ B hAB ih =>
      rw [Finset.sum_Ico_succ_top hAB, ih]
      unfold vfV2FixedWheelRootStepPhase
        vfV2FixedWheelPrefixPhase
      push_cast
      ring

/-- Exact TWO-SCALE telescope of EVERY complete OPEN square block
INSIDE a potentially incomplete prime wheel. Four ENDPOINT prefix
phases survive: at A², B², A, and B. No interior block phases survive. -/
theorem vfV2CompletedOpenSquareWheelBandPhase_double_telescope
    (F : ℕ → ℝ) (density : ℝ) (A B : ℕ)
    (hAB : A ≤ B) :
    (∑ R ∈ Finset.Ico A B,
      vfV2CompletedOpenSquareWheelBandPhase F density R) =
      (vfV2FixedWheelPrefixPhase F density (B ^ 2) -
        vfV2FixedWheelPrefixPhase F density (A ^ 2)) -
      (vfV2FixedWheelPrefixPhase F density B -
        vfV2FixedWheelPrefixPhase F density A) := by
  unfold vfV2CompletedOpenSquareWheelBandPhase
  rw [Finset.sum_sub_distrib,
    vfV2CompletedSquareWheelBandPhase_telescope F density A B hAB,
    vfV2FixedWheelRootStepPhase_telescope F density A B hAB]

/-- Four endpoint phases, not 2*(number of square blocks) phases. -/
theorem vfV2CompletedOpenSquareWheelBandPhase_abs_le_four_boundary
    (F : ℕ → ℝ) (density C : ℝ) (A B : ℕ)
    (hAB : A ≤ B)
    (hbound : ∀ x : ℕ,
      |vfV2FixedWheelPrefixPhase F density x| ≤ C) :
    |∑ R ∈ Finset.Ico A B,
      vfV2CompletedOpenSquareWheelBandPhase F density R| ≤ 4 * C := by
  rw [vfV2CompletedOpenSquareWheelBandPhase_double_telescope
    F density A B hAB]
  have hsq :
      |vfV2FixedWheelPrefixPhase F density (B ^ 2) -
        vfV2FixedWheelPrefixPhase F density (A ^ 2)| ≤ 2 * C := by
    calc
      |vfV2FixedWheelPrefixPhase F density (B ^ 2) -
          vfV2FixedWheelPrefixPhase F density (A ^ 2)| ≤
        |vfV2FixedWheelPrefixPhase F density (B ^ 2)| +
          |vfV2FixedWheelPrefixPhase F density (A ^ 2)| :=
        by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (vfV2FixedWheelPrefixPhase F density (B ^ 2)) 0 (vfV2FixedWheelPrefixPhase F density (A ^ 2)))
      _ ≤ C + C := add_le_add (hbound _) (hbound _)
      _ = 2 * C := by ring
  have hroot :
      |vfV2FixedWheelPrefixPhase F density B -
        vfV2FixedWheelPrefixPhase F density A| ≤ 2 * C := by
    calc
      |vfV2FixedWheelPrefixPhase F density B -
          vfV2FixedWheelPrefixPhase F density A| ≤
        |vfV2FixedWheelPrefixPhase F density B| +
          |vfV2FixedWheelPrefixPhase F density A| :=
        by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (vfV2FixedWheelPrefixPhase F density B) 0 (vfV2FixedWheelPrefixPhase F density A))
      _ ≤ C + C := add_le_add (hbound _) (hbound _)
      _ = 2 * C := by ring
  calc
    |(vfV2FixedWheelPrefixPhase F density (B ^ 2) -
          vfV2FixedWheelPrefixPhase F density (A ^ 2)) -
        (vfV2FixedWheelPrefixPhase F density B -
          vfV2FixedWheelPrefixPhase F density A)| ≤
      |vfV2FixedWheelPrefixPhase F density (B ^ 2) -
          vfV2FixedWheelPrefixPhase F density (A ^ 2)| +
      |vfV2FixedWheelPrefixPhase F density B -
          vfV2FixedWheelPrefixPhase F density A| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (vfV2FixedWheelPrefixPhase F density (B ^ 2) - vfV2FixedWheelPrefixPhase F density (A ^ 2)) 0 (vfV2FixedWheelPrefixPhase F density B - vfV2FixedWheelPrefixPhase F density A))
    _ ≤ 2 * C + 2 * C := add_le_add hsq hroot
    _ = 4 * C := by ring

/-- Signed divisor-floor expansion for a FINITE selected wheel. -/
def vfV2FiniteSignedWheelFloorPrefix
    (divs : Finset ℕ) (mu : ℕ → ℝ) (x : ℕ) : ℝ :=
  ∑ d ∈ divs, mu d * ((x / d : ℕ) : ℝ)

/-- Exact mean density of the same finite divisor-floor expansion. -/
def vfV2FiniteSignedWheelDensity
    (divs : Finset ℕ) (mu : ℕ → ℝ) : ℝ :=
  ∑ d ∈ divs, mu d / (d : ℝ)

/-- An individual floor term differs from its unrounded divisor density
by at most one, uniformly in the integer prefix and divisor size. -/
theorem vfV2FiniteWheelFloorDivError_le_one
    (x d : ℕ) (hd : 0 < d) :
    |((x / d : ℕ) : ℝ) - (x : ℝ) / (d : ℝ)| ≤ 1 := by
  have hdreal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hrem : x % d < d := Nat.mod_lt x hd
  have hremreal : ((x % d : ℕ) : ℝ) < (d : ℝ) := by
    exact_mod_cast hrem
  have heq : ((x % d : ℕ) : ℝ) +
      (d : ℝ) * ((x / d : ℕ) : ℝ) = (x : ℝ) := by
    exact_mod_cast (Nat.mod_add_div x d)
  have hfloor :
      (x : ℝ) / (d : ℝ) - ((x / d : ℕ) : ℝ) =
        ((x % d : ℕ) : ℝ) / (d : ℝ) := by
    apply (sub_eq_iff_eq_add).2
    apply (div_eq_iff hdreal.ne').2
    rw [add_mul, div_mul_cancel₀ _ hdreal.ne']
    nlinarith [heq]
  rw [abs_sub_comm, hfloor, abs_of_nonneg (by positivity)]
  exact (div_le_one hdreal).2 hremreal.le

/-- UNIFORM incomplete-CRT wheel discrepancy, independent of Q:
the only cost is the NUMBER OF DIVISOR FACES. This applies even
when NO complete CRT period lies in the whole square run. -/
theorem vfV2FiniteSignedWheelPrefixPhase_abs_le_card
    (divs : Finset ℕ) (mu : ℕ → ℝ)
    (hdiv : ∀ d ∈ divs, 0 < d)
    (hmu : ∀ d ∈ divs, |mu d| ≤ 1)
    (x : ℕ) :
    |vfV2FixedWheelPrefixPhase
       (vfV2FiniteSignedWheelFloorPrefix divs mu)
       (vfV2FiniteSignedWheelDensity divs mu) x| ≤
      (divs.card : ℝ) := by
  classical
  have heq :
      vfV2FixedWheelPrefixPhase
          (vfV2FiniteSignedWheelFloorPrefix divs mu)
          (vfV2FiniteSignedWheelDensity divs mu) x =
      ∑ d ∈ divs,
        mu d * (((x / d : ℕ) : ℝ) - (x : ℝ) / (d : ℝ)) := by
    unfold vfV2FixedWheelPrefixPhase
      vfV2FiniteSignedWheelFloorPrefix vfV2FiniteSignedWheelDensity
    rw [Finset.sum_mul]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [heq]
  calc
    |∑ d ∈ divs,
        mu d * (((x / d : ℕ) : ℝ) - (x : ℝ) / (d : ℝ))| ≤
      ∑ d ∈ divs,
        |mu d * (((x / d : ℕ) : ℝ) - (x : ℝ) / (d : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ divs, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      have hx := vfV2FiniteWheelFloorDivError_le_one x d (hdiv d hd)
      have hm := hmu d hd
      have hx0 : 0 ≤ |((x / d : ℕ) : ℝ) - (x : ℝ) / (d : ℝ)| :=
        abs_nonneg _
      have hm0 : 0 ≤ |mu d| := abs_nonneg _
      nlinarith [mul_nonneg (sub_nonneg.mpr hm) hx0,
        mul_nonneg hm0 (sub_nonneg.mpr hx)]
    _ = (divs.card : ℝ) := by simp

/-- The completed-square run of an actual finite signed divisor wheel
therefore has magnitude at most twice the NUMBER OF DIVISOR FACES.
This is a proved, all-scale *small-wheel* bound but it says nothing
about the high-prime owner correction needed for Sector Six. -/
theorem vfV2FiniteSignedWheelCompletedSquares_abs_le_two_card
    (divs : Finset ℕ) (mu : ℕ → ℝ)
    (hdiv : ∀ d ∈ divs, 0 < d)
    (hmu : ∀ d ∈ divs, |mu d| ≤ 1)
    (A B : ℕ) (hAB : A ≤ B) :
    |∑ R ∈ Finset.Ico A B,
        vfV2CompletedSquareWheelBandPhase
          (vfV2FiniteSignedWheelFloorPrefix divs mu)
          (vfV2FiniteSignedWheelDensity divs mu) R| ≤
      2 * (divs.card : ℝ) := by
  exact vfV2CompletedSquareWheelBandPhase_le_two_boundary
    _ _ _ A B hAB
    (vfV2FiniteSignedWheelPrefixPhase_abs_le_card
      divs mu hdiv hmu)

/-! ## Original Sector Six sign audit: signed/absolute active pair products

The six oriented raw-parent sectors reindex the signed active Gram Z.
For P negative prime charges (w-1) and F positive squarefree-composite
charges w, the absolute Gram is A and the signed Gram is Z.
The original Co/Div excess is G+4Z-2A and the six-sector upper budget
is G+2Z. Hence budget = excess + a NONNEGATIVE opposite-sign correction.
These are exact scalar identities; they do not prove the open payment.
-/

def vfV2ActiveSignedPairGram (w P F : ℝ) : ℝ :=
  ((w * F - (1 - w) * P) ^ 2 -
    ((1 - w) ^ 2 * P + w ^ 2 * F)) / 2

def vfV2ActiveAbsolutePairGram (w P F : ℝ) : ℝ :=
  (((1 - w) * P + w * F) ^ 2 -
    ((1 - w) ^ 2 * P + w ^ 2 * F)) / 2

/-- Sign and factor audit: SIX_BUDGET = ORIGINAL_EXCESS + positive correction.
In particular, reversing this correction would be an algebraic error. -/
theorem vfV2SixBudget_eq_originalExcess_add_pairCorrection
    (G w P F : ℝ) :
    G + 2 * vfV2ActiveSignedPairGram w P F =
      (G + 4 * vfV2ActiveSignedPairGram w P F -
        2 * vfV2ActiveAbsolutePairGram w P F) +
          4 * w * (1 - w) * P * F := by
  unfold vfV2ActiveSignedPairGram vfV2ActiveAbsolutePairGram
  ring

theorem vfV2SixPairCorrection_nonneg
    {w P F : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hP : 0 ≤ P) (hF : 0 ≤ F) :
    0 ≤ 4 * w * (1 - w) * P * F := by
  have hwComplement : 0 ≤ 1 - w := by linarith
  exact mul_nonneg
    (mul_nonneg (mul_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hw0)
      hwComplement) hP) hF

/-- A positive original Co/Div excess automatically forces POSITIVE six-sector
upper budget. This is expected at a hypothetical first bad endpoint, not
a sign inconsistency in the intended contradiction proof. -/
theorem vfV2SixBudget_pos_of_originalExcess_pos
    (G w P F : ℝ)
    (hE : 0 <
      G + 4 * vfV2ActiveSignedPairGram w P F -
        2 * vfV2ActiveAbsolutePairGram w P F)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hP : 0 ≤ P) (hF : 0 ≤ F) :
    0 < G + 2 * vfV2ActiveSignedPairGram w P F := by
  rw [vfV2SixBudget_eq_originalExcess_add_pairCorrection]
  exact add_pos_of_pos_of_nonneg hE
    (vfV2SixPairCorrection_nonneg hw0 hw1 hP hF)


end RHLean.Analysis

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
  · have hb :
        vfV2HighPrimeParentAgeBucket R (birthRoot n) ≠ b := by
      rw [ha]
      exact hab
    simp [ha, hb]
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
all joint-cell weighted fluxes reassemble exactly, without independence
assumptions, future peeking or a new absolute denominator. -/
def vfV2JointDelayedFluxCell
    (roots : Finset ℕ) (occ : ℕ → Fin 3) (age : ℕ → Fin 4)
    (E : ℕ → ℝ) (orientation : ℕ → ℝ) (horizon : ℕ)
    (o : Fin 3) (a : Fin 4) : ℝ :=
  ∑ R ∈ roots,
    if occ R = o ∧ age R = a
    then vfV2DelayedOrientedFlux E (orientation R) R horizon
    else 0

theorem vfV2JointDelayedFluxCell_sum
    (roots : Finset ℕ) (occ : ℕ → Fin 3) (age : ℕ → Fin 4)
    (E : ℕ → ℝ) (orientation : ℕ → ℝ) (horizon : ℕ) :
    (∑ o : Fin 3, ∑ a : Fin 4,
      vfV2JointDelayedFluxCell roots occ age E orientation horizon o a) =
      ∑ R ∈ roots, vfV2DelayedOrientedFlux E (orientation R) R horizon := by
  classical
  simp only [vfV2JointDelayedFluxCell]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro R hR
  rw [Finset.sum_comm]
  simp

/-- Pure finite classification cannot force arbitrary future prime-like
staircases to mean-revert: a nontrivial signed arithmetic result is needed. -/
theorem vfV2NoUniversalDelayedInwardFlux :
    ¬ ∀ E : ℕ → ℝ, ∀ (R horizon : ℕ),
      vfV2DelayedOrientedFlux E 1 R horizon ≤ 0 := by
  intro hall
  have h := hall (fun n : ℕ => (n : ℝ)) 0 1
  norm_num [vfV2DelayedOrientedFlux] at h


end RHLean.Analysis

import Mathlib
import RHLean.Analysis.BlockCovarianceRefinement
import RHLean.Analysis.SquareWheelSurvivorRun
import RHLean.Arithmetic.SquarefreePrimeFaceSurjectivity

open scoped BigOperators

/-!
# The run-level seam: escape covariance across square time

`SquareWheelSurvivorRun` proves

```text
SquareRunEnergyBoundedStatement
  <-> PrimeWheelResidualBoundedStatement primorialWheelFamily
  <-> MertensEnergyBoundedStatement,
```

so a uniform bound on every consecutive complete-square run finishes the wheel
and the arbitrary-`x` interpolation as deterministic bookkeeping.  The seam
should therefore be stated at run level, and this file does that.

For a run `I = [a, b]` of complete square blocks, write the window objects

```text
squareRunMass       a b = M((b+1)^2) - M(a^2)
squareRunDiagonal   a b = Q((b+1)^2) - Q(a^2)
squareRunCovariance a b = the exact within-window Möbius pair covariance.
```

`squareRunMass_sq_eq` is the exact window Green--Kubo identity

```text
(sum_{j in I} Delta_j)^2 = Q_I + 2 * C_I,
```

with `Q_I` the singleton squarefree diagonal, hence at most the window length.

Splitting `C_I` into a *descended* part and an *escape* part gives

```text
(sum_{j in I} Delta_j)^2 = Q_I + 2 * descended + 2 * escape.
```

The escape part is defined as the remainder, so the decomposition below is exact for any
proposed descended part.  Two hypotheses then finish the criterion:

* `SquareRunDescendedNonpositive` — the descended contribution does not add
  positive covariance.  This is what complete fresh-prime pair-cube cancellation
  and lower-scale family covariance descent are for: every post-root family is
  covariance-isomorphic to a prefix below `sqrt W`
  (`largePrimeFamilyPairSum_postRoot`), and complete pair cubes cancel.
* `SquareRunTopEscapeCovarianceBoundedStatement` — the escape covariance is of
  RH scale, uniformly over consecutive runs.

`squareRunEnergyBounded_of_topEscapeCovarianceBounded` proves those two give
`SquareRunEnergyBoundedStatement`, and
`mertensEnergyBounded_of_topEscapeCovarianceBounded` chains through the existing
equivalence to the global Mertens energy criterion.

**What the escape part must contain.**  It is *not* enough to control
family interaction separately inside each `Delta_j`.  The window covariance
`C_I` contains the cross-square-block pairs `2 * sum_{a <= i < j <= b} Delta_i
Delta_j` as well, and any descended part that omits them leaves them in the
escape remainder by construction.  That is deliberate: the definition of escape
as a remainder makes the identity exact and makes the omission visible instead
of silent.

**What this file does not do.**  Nesting supplies a chronological coordinate and
proves that controlling the escape on every signed run suffices.  It does not
produce the cancellation.  The negative feedback still has to come from the
fresh-prime arithmetic as square time advances — the four-corner pair identity
of `DeterministicTGreenKuboComparison` cancels every interior order-crossing
shell and leaves the top-escape shell, and the remaining native theorem is that
those escapes cannot maintain a positive supercritical record through square
time.

No estimate, asymptotic input or RH hypothesis is proved here.
-/

noncomputable section

namespace RHLean.Analysis

open RHLean.Proof
open RHLean.Arithmetic

/-! ## Exact window objects for a consecutive square run -/

/-- Signed Möbius mass of the complete-square run `[a, b]`. -/
def squareRunMass (a b : ℕ) : ℝ :=
  realMertensLength ((b + 1) ^ 2) - realMertensLength (a ^ 2)

/-- Squarefree diagonal of the same window. -/
def squareRunDiagonal (a b : ℕ) : ℝ :=
  realMertensDiagonal ((b + 1) ^ 2) - realMertensDiagonal (a ^ 2)

/-- Exact Möbius pair covariance carried strictly inside the window. -/
def squareRunCovariance (a b : ℕ) : ℝ :=
  signedBlockInnerCovariance realMoebiusStep (a ^ 2) ((b + 1) ^ 2)

/-- **Window Green--Kubo for a square run.**  No absolute value is taken and no
block is bounded on its own. -/
theorem squareRunMass_sq_eq (a b : ℕ) :
    squareRunMass a b ^ 2 =
      squareRunDiagonal a b + 2 * squareRunCovariance a b :=
  signedBlockPrefix_sub_sq_eq_energy_sub_add_two_mul_inner realMoebiusStep
    (a ^ 2) ((b + 1) ^ 2)

/-- The run diagonal is at most the window's right endpoint: no conjecture. -/
theorem squareRunDiagonal_le (a b : ℕ) :
    squareRunDiagonal a b ≤ (((b + 1) ^ 2 : ℕ) : ℝ) := by
  have hle := realMertensDiagonal_le ((b + 1) ^ 2)
  have hnn := realMertensDiagonal_nonneg (a ^ 2)
  unfold squareRunDiagonal
  linarith

/-- **Sharp run-diagonal bound.**  Only sites actually traversed by the run can
contribute to its squarefree diagonal, so the diagonal is bounded by the exact
window length `(b+1)^2-a^2`, not by the whole prefix up to `(b+1)^2`. -/
theorem squareRunDiagonal_le_windowLength (a b : ℕ) (hab : a ≤ b) :
    squareRunDiagonal a b ≤
      ((((b + 1) ^ 2 - a ^ 2 : ℕ) : ℝ)) := by
  have hsq : a ^ 2 ≤ (b + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hsplit :=
    Finset.sum_range_add_sum_Ico (fun n => realMoebiusStep n ^ 2) hsq
  have hdiag :
      squareRunDiagonal a b =
        ∑ n ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2), realMoebiusStep n ^ 2 := by
    unfold squareRunDiagonal realMertensDiagonal
    linarith [hsplit]
  rw [hdiag]
  calc
    (∑ n ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2), realMoebiusStep n ^ 2) ≤
        ∑ n ∈ Finset.Ico (a ^ 2) ((b + 1) ^ 2), (1 : ℝ) := by
      exact Finset.sum_le_sum (fun n _hn => realMoebiusStep_sq_le_one n)
    _ = ((Finset.Ico (a ^ 2) ((b + 1) ^ 2)).card : ℝ) := by simp
    _ = ((((b + 1) ^ 2 - a ^ 2 : ℕ) : ℝ)) := by
      rw [Nat.card_Ico]

/-! ## Splitting the window covariance -/

/-- Whatever a descent argument does not account for.  Defined as a remainder,
so the decomposition below is exact for every proposed `descended`. -/
def squareRunEscapeCovariance (descended : ℕ → ℕ → ℝ) (a b : ℕ) : ℝ :=
  squareRunCovariance a b - descended a b

/-- **Exact escape decomposition of a signed square run.** -/
theorem squareRunMass_sq_eq_diagonal_add_descended_add_escape
    (descended : ℕ → ℕ → ℝ) (a b : ℕ) :
    squareRunMass a b ^ 2 =
      squareRunDiagonal a b + 2 * descended a b +
        2 * squareRunEscapeCovariance descended a b := by
  have h := squareRunMass_sq_eq a b
  unfold squareRunEscapeCovariance
  linarith

/-- The descended contribution adds no positive covariance.  This is the target
of complete fresh-prime pair-cube cancellation together with lower-scale family
covariance descent. -/
def SquareRunDescendedNonpositive (descended : ℕ → ℕ → ℝ) : Prop :=
  ∀ a b : ℕ, a ≤ b → descended a b ≤ 0

/-- **The final native seam.**  Uniformly over consecutive complete-square runs,
the escape covariance is of RH scale. -/
def SquareRunTopEscapeCovarianceBoundedStatement
    (descended : ℕ → ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a b : ℕ, a ≤ b →
        squareRunEscapeCovariance descended a b ≤
          C * Real.rpow (((squarePrefixEndpoint b + 1 : ℕ) : ℝ)) (1 + ε)

/-! ## Coherent persistence pressure -/

/-- A run `[a,b]` carries coherent average bias at least `eta` when the absolute
signed run mass is at least `eta` times the number of complete square blocks in
the run.  This is deliberately a run-level condition: no pointwise bound on an
individual square block is imposed. -/
def SquareRunCoherentBiasAtLeast (eta : ℝ) (a b : ℕ) : Prop :=
  eta * (((b + 1 - a : ℕ) : ℝ)) ≤ |squareRunMass a b|

/-- **Unconditional covariance pressure.**  A coherent run of
`ell = b+1-a` square blocks with average signed bias at least `eta` forces the
actual within-window Möbius covariance to be at least

`(eta^2 * ell^2 - ((b+1)^2-a^2)) / 2`.

No Euler-descent hypothesis enters this statement.  It is the exact
Green--Kubo cost of coherent persistence after charging only the sites actually
visited by the run to the diagonal. -/
theorem squareRunCovariance_ge_of_coherentBias
    (a b : ℕ) (hab : a ≤ b)
    (eta : ℝ) (heta : 0 ≤ eta)
    (hcoh : SquareRunCoherentBiasAtLeast eta a b) :
    ((eta * (((b + 1 - a : ℕ) : ℝ))) ^ 2 -
        ((((b + 1) ^ 2 - a ^ 2 : ℕ) : ℝ))) / 2 ≤
      squareRunCovariance a b := by
  have hlen : 0 ≤ (((b + 1 - a : ℕ) : ℝ)) := by positivity
  have hleft : 0 ≤ eta * (((b + 1 - a : ℕ) : ℝ)) :=
    mul_nonneg heta hlen
  have habs : 0 ≤ |squareRunMass a b| := abs_nonneg _
  have hmassSq :
      (eta * (((b + 1 - a : ℕ) : ℝ))) ^ 2 ≤ squareRunMass a b ^ 2 := by
    calc
      (eta * (((b + 1 - a : ℕ) : ℝ))) ^ 2 ≤ |squareRunMass a b| ^ 2 := by
        unfold SquareRunCoherentBiasAtLeast at hcoh
        nlinarith
      _ = squareRunMass a b ^ 2 := sq_abs _
  have hid := squareRunMass_sq_eq a b
  have hdiag := squareRunDiagonal_le_windowLength a b hab
  nlinarith

/-- **Coherent persistence has to escape.**  If the descended Euler interior is
nonpositive, every covariance unit forced by the preceding unconditional
pressure law must be carried by the top-escape remainder. -/
theorem squareRunEscapeCovariance_ge_of_coherentBias
    {descended : ℕ → ℕ → ℝ}
    (hneg : SquareRunDescendedNonpositive descended)
    (a b : ℕ) (hab : a ≤ b)
    (eta : ℝ) (heta : 0 ≤ eta)
    (hcoh : SquareRunCoherentBiasAtLeast eta a b) :
    ((eta * (((b + 1 - a : ℕ) : ℝ))) ^ 2 -
        ((((b + 1) ^ 2 - a ^ 2 : ℕ) : ℝ))) / 2 ≤
      squareRunEscapeCovariance descended a b := by
  have hraw := squareRunCovariance_ge_of_coherentBias a b hab eta heta hcoh
  have hdesc := hneg a b hab
  unfold squareRunEscapeCovariance
  linarith

/-- **Persistence-length budget.**  If the top escape covariance on the same
run is at most `B`, then coherent average bias `eta` can persist only while

`(eta * ell)^2 <= ((b+1)^2-a^2) + 2 B`.

The diagonal term is now the exact physical run length.  Large individual
square blocks remain allowed; only sustained signed alignment consumes the
quadratic left-hand side. -/
theorem squareRunCoherentBias_sq_le_of_escape_le
    {descended : ℕ → ℕ → ℝ}
    (hneg : SquareRunDescendedNonpositive descended)
    (a b : ℕ) (hab : a ≤ b)
    (eta : ℝ) (heta : 0 ≤ eta) (B : ℝ)
    (hcoh : SquareRunCoherentBiasAtLeast eta a b)
    (hesc : squareRunEscapeCovariance descended a b ≤ B) :
    (eta * (((b + 1 - a : ℕ) : ℝ))) ^ 2 ≤
      ((((b + 1) ^ 2 - a ^ 2 : ℕ) : ℝ)) + 2 * B := by
  have hpressure :=
    squareRunEscapeCovariance_ge_of_coherentBias
      hneg a b hab eta heta hcoh
  nlinarith

/-- **Literal non-persistence contrapositive.**  Under a top-escape budget `B`,
a proposed coherent run is impossible as soon as its squared coherent mass
exceeds the exact run-diagonal budget plus twice the escape budget. -/
theorem squareRunCoherentBias_cannot_persist_of_escape_budget
    {descended : ℕ → ℕ → ℝ}
    (hneg : SquareRunDescendedNonpositive descended)
    (a b : ℕ) (hab : a ≤ b)
    (eta : ℝ) (heta : 0 ≤ eta) (B : ℝ)
    (hesc : squareRunEscapeCovariance descended a b ≤ B)
    (hsuper :
      ((((b + 1) ^ 2 - a ^ 2 : ℕ) : ℝ)) + 2 * B <
        (eta * (((b + 1 - a : ℕ) : ℝ))) ^ 2) :
    ¬ SquareRunCoherentBiasAtLeast eta a b := by
  intro hcoh
  have hbudget :=
    squareRunCoherentBias_sq_le_of_escape_le
      hneg a b hab eta heta B hcoh hesc
  linarith

/-! ## The run mass is the square-run energy coordinate -/

private theorem natCast_le_rpow_one_add {ε : ℝ} (hε : 0 < ε) (x : ℕ) :
    (((x + 1 : ℕ) : ℝ)) ≤ Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε) := by
  have hbase : (1 : ℝ) ≤ (((x + 1 : ℕ) : ℝ)) := by
    have hone : (1 : ℕ) ≤ x + 1 := Nat.le_add_left 1 x
    exact_mod_cast hone
  have h := Real.rpow_le_rpow_of_exponent_le hbase
    (by linarith : (1 : ℝ) ≤ 1 + ε)
  simpa using h

theorem sum_canonicalTotalIncrement_eq_squareRunMass_cast
    (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b + 1) :
    (∑ j ∈ Finset.Ico a (b + 1), canonicalTotalIncrement j) =
      ((squareRunMass a b : ℝ) : ℂ) := by
  have hb : squarePrefixMertens b = ((realMertensLength ((b + 1) ^ 2) : ℝ) : ℂ) := by
    have h1 := realMertensLength_cast_eq_mertensSummatory (squarePrefixEndpoint b)
    rw [squarePrefixEndpoint_add_one b] at h1
    exact h1.symm
  have ha' : squarePrefixMertens (a - 1) =
      ((realMertensLength (a ^ 2) : ℝ) : ℂ) := by
    have h1 :=
      realMertensLength_cast_eq_mertensSummatory (squarePrefixEndpoint (a - 1))
    rw [squarePrefixEndpoint_add_one (a - 1)] at h1
    have hpred : a - 1 + 1 = a := Nat.sub_add_cancel ha
    rw [hpred] at h1
    exact h1.symm
  rw [sum_canonicalTotalIncrement_Ico_eq_squarePrefix_sub a b ha hab, hb, ha']
  unfold squareRunMass
  push_cast
  ring

theorem norm_sum_canonicalTotalIncrement_sq_eq_squareRunMass_sq
    (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b + 1) :
    ‖∑ j ∈ Finset.Ico a (b + 1), canonicalTotalIncrement j‖ ^ 2 =
      squareRunMass a b ^ 2 := by
  rw [sum_canonicalTotalIncrement_eq_squareRunMass_cast a b ha hab,
    Complex.norm_real, Real.norm_eq_abs]
  exact sq_abs _

/-! ## The reduction -/

/-- **Escape control gives the maximal signed square-run criterion.** -/
theorem squareRunEnergyBounded_of_topEscapeCovarianceBounded
    {descended : ℕ → ℕ → ℝ}
    (hneg : SquareRunDescendedNonpositive descended)
    (hesc : SquareRunTopEscapeCovarianceBoundedStatement descended) :
    SquareRunEnergyBoundedStatement := by
  intro ε hε
  rcases hesc ε hε with ⟨C, hC, hbound⟩
  refine ⟨1 + 2 * C, by linarith, ?_⟩
  intro k a b ha hab _hleft _hright
  rw [norm_sum_canonicalTotalIncrement_sq_eq_squareRunMass_sq a b ha (by omega)]
  have hid := squareRunMass_sq_eq_diagonal_add_descended_add_escape descended a b
  have hd := hneg a b hab
  have he := hbound a b hab
  have hdiagRaw := squareRunDiagonal_le a b
  have hcast : (((b + 1) ^ 2 : ℕ) : ℝ) =
      (((squarePrefixEndpoint b + 1 : ℕ) : ℝ)) := by
    rw [squarePrefixEndpoint_add_one b]
  rw [hcast] at hdiagRaw
  have hlin := natCast_le_rpow_one_add hε (squarePrefixEndpoint b)
  linarith

/-- **Hence the global Mertens energy criterion**, through the equivalence
already proved for maximal signed square runs. -/
theorem mertensEnergyBounded_of_topEscapeCovarianceBounded
    {descended : ℕ → ℕ → ℝ}
    (hneg : SquareRunDescendedNonpositive descended)
    (hesc : SquareRunTopEscapeCovarianceBoundedStatement descended) :
    MertensEnergyBoundedStatement :=
  squareRunEnergyBounded_iff_mertensEnergy.mp
    (squareRunEnergyBounded_of_topEscapeCovarianceBounded hneg hesc)

/-! ## Canonical first-separation ownership of every physical covariance atom -/

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

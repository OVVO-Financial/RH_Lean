import Mathlib
import RHLean.Arithmetic.PrimeProductFrontierExhaustion
import RHLean.Proof.LowWheelCanonicalOrientedRunFibres
import RHLean.Proof.LowWheelFaceTailToggle

/-!
# Square-root contraction of predecessor-dense frozen cubes

The ordered dense-divisibility split becomes quantitative at the root scale.
Let `s = Nat.sqrt R`.  If a face has product at most `R` and is triply
predecessor-dense above the smooth threshold `s`, then every prime coordinate
of that face is already at most `s`.

Indeed, a hypothetical coordinate `p > s` would satisfy

`p^4 <= s * primeFaceProduct t <= s * R`,

while `R < (s+1)^2` and `s+1 <= p` force

`s * R < (s+1)^4 <= p^4`.

Consequently the dense part of every frozen predecessor window with upper
product cutoff at most `R` collapses *exactly* to the smaller Boolean cube
`primesUpTo (Nat.sqrt R)`.  The complementary first-jump mass is left signed.
Thus a high-owner frozen window admits the exact contraction

`F_{q^-} = F_{sqrt R} + J_{q,sqrt R}`

before any norm or triangle inequality.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis
open LowWheelCanonicalDowncrossOwnership
open SignedOwnershipInterval

attribute [local instance] Classical.propDecidable

/-- Elementary clock inequality behind the contraction. -/
theorem sqrt_mul_root_lt_succ_fourth (R : ℕ) :
    Nat.sqrt R * R < (Nat.sqrt R + 1) ^ 4 := by
  let s := Nat.sqrt R
  have hR : R < (s + 1) ^ 2 := by
    dsimp [s]
    exact Nat.lt_succ_sqrt' R
  by_cases hs : s = 0
  · subst s
    simp
  · have hspos : 0 < s := Nat.pos_of_ne_zero hs
    have hleft : s * R < s * (s + 1) ^ 2 :=
      Nat.mul_lt_mul_of_pos_left hR hspos
    have hsle : s ≤ (s + 1) ^ 2 := by
      nlinarith
    have hright :
        s * (s + 1) ^ 2 ≤ (s + 1) ^ 2 * (s + 1) ^ 2 :=
      Nat.mul_le_mul_right ((s + 1) ^ 2) hsle
    calc
      Nat.sqrt R * R = s * R := by rfl
      _ < s * (s + 1) ^ 2 := hleft
      _ ≤ (s + 1) ^ 2 * (s + 1) ^ 2 := hright
      _ = (s + 1) ^ 4 := by ring
      _ = (Nat.sqrt R + 1) ^ 4 := by rfl

/-- A triply predecessor-dense prime face of product at most `R` contains no
prime above `sqrt R`.  This is the strict multiplicative contraction. -/
theorem predecessorDensePrimeFace_subset_primesUpTo_sqrt
    {R : ℕ} {t : Finset ℕ}
    (hprime : ∀ p ∈ t, p.Prime)
    (hdense : PredecessorDenseFace 3 (Nat.sqrt R) t)
    (hprod : primeFaceProduct t ≤ R) :
    t ⊆ primesUpTo (Nat.sqrt R) := by
  intro p hpt
  have hpPrime := hprime p hpt
  apply mem_primesUpTo.mpr
  refine ⟨hpPrime, ?_⟩
  by_contra hnot
  have hsp : Nat.sqrt R < p := Nat.lt_of_not_ge hnot
  have hp4 : p ^ 4 ≤ Nat.sqrt R * primeFaceProduct t := by
    have h :=
      predecessorDenseFace_coordinate_power_succ_le_of_large
        hprime hdense hpt hsp
    simpa using h
  have hp4R : p ^ 4 ≤ Nat.sqrt R * R :=
    hp4.trans (Nat.mul_le_mul_left (Nat.sqrt R) hprod)
  have hclock := sqrt_mul_root_lt_succ_fourth R
  have hsucc : Nat.sqrt R + 1 ≤ p := by omega
  have hpow : (Nat.sqrt R + 1) ^ 4 ≤ p ^ 4 :=
    Nat.pow_le_pow_left hsucc 4
  have : p ^ 4 < p ^ 4 := hp4R.trans_lt (hclock.trans_le hpow)
  exact (Nat.lt_irrefl _ this)

/-- Dense faces in an old owner window are already supported on the square-root
prime universe as soon as the window product is bounded by `R`. -/
theorem predecessorDenseFrozenWindowFace_subset_sqrt
    {R q A B : ℕ} {t : Finset ℕ}
    (hBR : B ≤ R)
    (ht : t ∈ predecessorDenseFrozenWindowFaces 3 (Nat.sqrt R)
      (primesUpTo (q - 1)) A B) :
    t ∈ (primesUpTo (Nat.sqrt R)).powerset := by
  rcases mem_predecessorDenseFrozenWindowFaces.mp ht with
    ⟨hwindow, hdense⟩
  rcases mem_frozenPrimeUniverseWindowFaces.mp hwindow with
    ⟨htOld, _hlo, hup⟩
  have hOldSub := Finset.mem_powerset.mp htOld
  have hprime : ∀ p ∈ t, p.Prime := by
    intro p hpt
    exact prime_of_mem_primesUpTo (hOldSub hpt)
  have hprod : primeFaceProduct t ≤ R := hup.trans hBR
  exact Finset.mem_powerset.mpr
    (predecessorDensePrimeFace_subset_primesUpTo_sqrt
      hprime hdense hprod)

/-- **Exact dense-face contraction.**  If the old owner lies above `sqrt R`,
the predecessor-dense portion of its frozen window is literally the same face
set as the full frozen window in the smaller prime universe through `sqrt R`. -/
theorem predecessorDenseFrozenWindowFaces_sqrt_eq
    (R q A B : ℕ)
    (hqroot : Nat.sqrt R < q)
    (hBR : B ≤ R) :
    predecessorDenseFrozenWindowFaces 3 (Nat.sqrt R)
        (primesUpTo (q - 1)) A B =
      frozenPrimeUniverseWindowFaces
        (primesUpTo (Nat.sqrt R)) A B := by
  ext t
  constructor
  · intro ht
    have htSmall :=
      predecessorDenseFrozenWindowFace_subset_sqrt hBR ht
    rcases mem_predecessorDenseFrozenWindowFaces.mp ht with
      ⟨hwindow, _hdense⟩
    rcases mem_frozenPrimeUniverseWindowFaces.mp hwindow with
      ⟨_htOld, hlo, hup⟩
    exact mem_frozenPrimeUniverseWindowFaces.mpr
      ⟨htSmall, hlo, hup⟩
  · intro ht
    rcases mem_frozenPrimeUniverseWindowFaces.mp ht with
      ⟨htSmall, hlo, hup⟩
    have hSmallSub := Finset.mem_powerset.mp htSmall
    have htOld : t ∈ (primesUpTo (q - 1)).powerset := by
      apply Finset.mem_powerset.mpr
      intro p hpt
      rcases mem_primesUpTo.mp (hSmallSub hpt) with ⟨hpPrime, hpLe⟩
      apply mem_primesUpTo.mpr
      refine ⟨hpPrime, ?_⟩
      omega
    have hdense : PredecessorDenseFace 3 (Nat.sqrt R) t := by
      intro p hpt hlarge
      have hpLe := (mem_primesUpTo.mp (hSmallSub hpt)).2
      omega
    exact mem_predecessorDenseFrozenWindowFaces.mpr
      ⟨mem_frozenPrimeUniverseWindowFaces.mpr ⟨htOld, hlo, hup⟩,
        hdense⟩

/-- Signed version of the exact dense-face contraction. -/
theorem predecessorDenseFrozenWindowMass_sqrt_eq
    (R q A B : ℕ)
    (hqroot : Nat.sqrt R < q)
    (hBR : B ≤ R) :
    predecessorDenseFrozenWindowMass 3 (Nat.sqrt R)
        (primesUpTo (q - 1)) A B =
      frozenPrimeUniverseWindowMass
        (primesUpTo (Nat.sqrt R)) A B := by
  unfold predecessorDenseFrozenWindowMass frozenPrimeUniverseWindowMass
  rw [predecessorDenseFrozenWindowFaces_sqrt_eq R q A B hqroot hBR]

/-- **Square-root signed contraction of one high-owner frozen window.**
The dense contribution is exactly the lower prime universe; all unresolved
arithmetic is confined to the signed first-jump residual. -/
theorem frozenPrimeUniverseWindowMass_eq_sqrtContraction_add_firstJump
    (R q A B : ℕ)
    (hqroot : Nat.sqrt R < q)
    (hBR : B ≤ R) :
    frozenPrimeUniverseWindowMass (primesUpTo (q - 1)) A B =
      frozenPrimeUniverseWindowMass (primesUpTo (Nat.sqrt R)) A B +
        predecessorFirstJumpFrozenWindowMass
          3 (Nat.sqrt R) (primesUpTo (q - 1)) A B := by
  rw [frozenPrimeUniverseWindowMass_eq_dense_add_firstJump
      3 (Nat.sqrt R) (primesUpTo (q - 1)) A B,
    predecessorDenseFrozenWindowMass_sqrt_eq R q A B hqroot hBR]

/-- The predecessor cube attached to the canonical first high jump is itself
entirely supported below `sqrt R`. -/
theorem firstJumpFrozenWindowFace_sqrt_exists_highPrime_lowPredecessor
    {R q A B : ℕ} {t : Finset ℕ}
    (hqroot : Nat.sqrt R < q)
    (hBR : B ≤ R)
    (ht : t ∈ predecessorFirstJumpFrozenWindowFaces 3 (Nat.sqrt R)
      (primesUpTo (q - 1)) A B) :
    ∃ p ∈ t,
      Nat.sqrt R < p ∧ p < q ∧
      Nat.sqrt R * predecessorPrimeFaceProduct t p < p ^ 3 ∧
      predecessorPrimeFace t p ∈
        (primesUpTo (Nat.sqrt R)).powerset := by
  rcases mem_predecessorFirstJumpFrozenWindowFaces.mp ht with
    ⟨hwindow, hnotDense⟩
  rcases exists_first_predecessorDenseFailure_with_densePredecessor hnotDense with
    ⟨p, hpt, hsp, hfail, hpredDense⟩
  rcases mem_frozenPrimeUniverseWindowFaces.mp hwindow with
    ⟨htOld, _hlo, hup⟩
  have hOldSub := Finset.mem_powerset.mp htOld
  have hpOld := hOldSub hpt
  rcases mem_primesUpTo.mp hpOld with ⟨hpPrime, hpLeOld⟩
  have hpLtQ : p < q := by omega
  have hprimePred : ∀ r ∈ predecessorPrimeFace t p, r.Prime := by
    intro r hr
    exact prime_of_mem_primesUpTo
      (hOldSub (mem_predecessorPrimeFace.mp hr).1)
  have hprefix :=
    prime_mul_predecessorPrimeFaceProduct_le
      (fun r hr => prime_of_mem_primesUpTo (hOldSub hr)) hpt
  have hpredLeMul :
      predecessorPrimeFaceProduct t p ≤
        p * predecessorPrimeFaceProduct t p := by
    have hpOne : 1 ≤ p := hpPrime.one_le
    simpa [one_mul, Nat.mul_comm] using
      Nat.mul_le_mul_right (predecessorPrimeFaceProduct t p) hpOne
  have hpredLeR : predecessorPrimeFaceProduct t p ≤ R :=
    (hpredLeMul.trans hprefix).trans (hup.trans hBR)
  have hpredSmall :
      predecessorPrimeFace t p ⊆ primesUpTo (Nat.sqrt R) :=
    predecessorDensePrimeFace_subset_primesUpTo_sqrt
      hprimePred hpredDense hpredLeR
  exact ⟨p, hpt, hsp, hpLtQ, hfail,
    Finset.mem_powerset.mpr hpredSmall⟩

/-- **Oriented-state specialization.**  Every oriented state whose fresh owner
is above `sqrt R` has its signed Boolean mass split into an exact square-root
frozen cube plus a signed first-high-jump residual. -/
theorem sum_booleanCubeSign_orientedChargingFaces_eq_sqrtFrozen_add_firstJump
    {R c k : ℕ}
    (hne : (lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k)).Nonempty)
    (hqroot : Nat.sqrt R < lowWheelCanonicalDowncrossPivot (c, k)) :
    (∑ t ∈ lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k),
        booleanCubeSign t) =
      frozenPrimeUniverseWindowMass
        (primesUpTo (Nat.sqrt R))
        (R / k)
        (lowWheelCanonicalDowncrossOwnershipUpper R c k) +
      predecessorFirstJumpFrozenWindowMass
        3 (Nat.sqrt R)
        (primesUpTo (lowWheelCanonicalDowncrossPivot (c, k) - 1))
        (R / k)
        (lowWheelCanonicalDowncrossOwnershipUpper R c k) := by
  have hupper : lowWheelCanonicalDowncrossOwnershipUpper R c k ≤ R := by
    unfold lowWheelCanonicalDowncrossOwnershipUpper
    exact (min_le_left _ _).trans (Nat.div_le_self _ _)
  rw [sum_booleanCubeSign_orientedChargingFaces_eq_frozenWindowMass hne,
    frozenPrimeUniverseWindowMass_eq_sqrtContraction_add_firstJump
      R (lowWheelCanonicalDowncrossPivot (c, k))
      (R / k) (lowWheelCanonicalDowncrossOwnershipUpper R c k)
      hqroot hupper]

/-! ## Canonical first-jump Fubini

The square-root contraction above leaves one signed first-high-jump residual.
We now open that residual without losing its sign.  Every non-dense face has a
unique first failing prime `p`; after fixing `p`, the face splits canonically as

`u ∪ {p} ∪ v`,

where `u` is the already-dense predecessor and `v` contains only later Euler
coordinates.  For fixed `(p,u)`, the `v`-population is exactly one frozen window
on the strict tail universe above `p`.  The existing fresh-prime recurrence
therefore acts on the tail cube verbatim.
-/

/-- `p` is the canonical first large predecessor-density failure of `t`. -/
def IsPredecessorFirstJumpAt
    (d Y : ℕ) (t : Finset ℕ) (p : ℕ) : Prop :=
  p ∈ t ∧
    Y < p ∧
    Y * predecessorPrimeFaceProduct t p < p ^ d ∧
    ∀ q ∈ t, q < p → Y < q →
      q ^ d ≤ Y * predecessorPrimeFaceProduct t q

/-- The first predecessor jump is unique. -/
theorem isPredecessorFirstJumpAt_unique
    {d Y : ℕ} {t : Finset ℕ} {p q : ℕ}
    (hp : IsPredecessorFirstJumpAt d Y t p)
    (hq : IsPredecessorFirstJumpAt d Y t q) :
    p = q := by
  rcases hp with ⟨hpt, hYp, hpfail, hprevP⟩
  rcases hq with ⟨hqt, hYq, hqfail, hprevQ⟩
  by_cases hpq : p = q
  · exact hpq
  · by_cases hpLtQ : p < q
    · have hgood := hprevQ p hpt hpLtQ hYp
      omega
    · have hqLtP : q < p := by omega
      have hgood := hprevP q hqt hqLtP hYq
      omega

/-- Every first-jump frozen face has a canonical first-jump coordinate. -/
theorem firstJumpFrozenWindowFace_exists_isPredecessorFirstJumpAt
    {d Y : ℕ} {S : Finset ℕ} {A B : ℕ} {t : Finset ℕ}
    (ht : t ∈ predecessorFirstJumpFrozenWindowFaces d Y S A B) :
    ∃ p, IsPredecessorFirstJumpAt d Y t p := by
  rcases firstJumpFrozenWindowFace_exists_firstFailure ht with
    ⟨p, hpt, hYp, hfail, hprev⟩
  exact ⟨p, hpt, hYp, hfail, hprev⟩

/-- Faces in the first-jump residual whose canonical first failure is `p`. -/
def predecessorFirstJumpFrozenWindowSlice
    (d Y : ℕ) (S : Finset ℕ) (A B p : ℕ) : Finset (Finset ℕ) :=
  (predecessorFirstJumpFrozenWindowFaces d Y S A B).filter fun t =>
    IsPredecessorFirstJumpAt d Y t p

@[simp] theorem mem_predecessorFirstJumpFrozenWindowSlice
    {d Y : ℕ} {S : Finset ℕ} {A B p : ℕ} {t : Finset ℕ} :
    t ∈ predecessorFirstJumpFrozenWindowSlice d Y S A B p ↔
      t ∈ predecessorFirstJumpFrozenWindowFaces d Y S A B ∧
        IsPredecessorFirstJumpAt d Y t p := by
  simp [predecessorFirstJumpFrozenWindowSlice]

/-- The first-jump slices are pairwise disjoint. -/
theorem predecessorFirstJumpFrozenWindowSlice_pairwise
    (d Y : ℕ) (S : Finset ℕ) (A B : ℕ) :
    Set.PairwiseDisjoint (↑S)
      (predecessorFirstJumpFrozenWindowSlice d Y S A B) := by
  intro p _hpS q _hqS hpq
  change Disjoint
    (predecessorFirstJumpFrozenWindowSlice d Y S A B p)
    (predecessorFirstJumpFrozenWindowSlice d Y S A B q)
  rw [Finset.disjoint_left]
  intro t htp htq
  have hpFirst := (mem_predecessorFirstJumpFrozenWindowSlice.mp htp).2
  have hqFirst := (mem_predecessorFirstJumpFrozenWindowSlice.mp htq).2
  exact hpq (isPredecessorFirstJumpAt_unique hpFirst hqFirst)

/-- The entire first-jump residual is the disjoint union over its canonical
first jump `p`. -/
theorem predecessorFirstJumpFrozenWindowFaces_eq_biUnion_slices
    (d Y : ℕ) (S : Finset ℕ) (A B : ℕ) :
    predecessorFirstJumpFrozenWindowFaces d Y S A B =
      S.biUnion (predecessorFirstJumpFrozenWindowSlice d Y S A B) := by
  ext t
  constructor
  · intro ht
    rcases firstJumpFrozenWindowFace_exists_isPredecessorFirstJumpAt ht with
      ⟨p, hpFirst⟩
    have hwindow := (mem_predecessorFirstJumpFrozenWindowFaces.mp ht).1
    have htPow := (mem_frozenPrimeUniverseWindowFaces.mp hwindow).1
    have hpS := (Finset.mem_powerset.mp htPow) hpFirst.1
    exact Finset.mem_biUnion.mpr
      ⟨p, hpS,
        mem_predecessorFirstJumpFrozenWindowSlice.mpr ⟨ht, hpFirst⟩⟩
  · intro ht
    rcases Finset.mem_biUnion.mp ht with ⟨p, _hpS, htp⟩
    exact (mem_predecessorFirstJumpFrozenWindowSlice.mp htp).1

/-- Signed mass of one canonical first-jump slice. -/
def predecessorFirstJumpFrozenWindowSliceMass
    (d Y : ℕ) (S : Finset ℕ) (A B p : ℕ) : ℤ :=
  ∑ t ∈ predecessorFirstJumpFrozenWindowSlice d Y S A B p,
    booleanCubeSign t

/-- **First Fubini step.**  The signed first-jump residual is exactly the sum of
its canonical first-jump slices. -/
theorem predecessorFirstJumpFrozenWindowMass_eq_sum_slices
    (d Y : ℕ) (S : Finset ℕ) (A B : ℕ) :
    predecessorFirstJumpFrozenWindowMass d Y S A B =
      ∑ p ∈ S,
        predecessorFirstJumpFrozenWindowSliceMass d Y S A B p := by
  unfold predecessorFirstJumpFrozenWindowMass
    predecessorFirstJumpFrozenWindowSliceMass
  rw [predecessorFirstJumpFrozenWindowFaces_eq_biUnion_slices]
  exact Finset.sum_biUnion
    (predecessorFirstJumpFrozenWindowSlice_pairwise d Y S A B)

/-! ### Canonical predecessor / jump / tail coordinates -/

/-- Coordinates strictly after the first jump `p`. -/
def firstJumpTailFace (t : Finset ℕ) (p : ℕ) : Finset ℕ :=
  t.filter fun q => p < q

@[simp] theorem mem_firstJumpTailFace
    {t : Finset ℕ} {p q : ℕ} :
    q ∈ firstJumpTailFace t p ↔ q ∈ t ∧ p < q := by
  simp [firstJumpTailFace]

/-- Prime coordinates of `S` strictly before `p`. -/
def firstJumpPredecessorPrimeUniverse
    (S : Finset ℕ) (p : ℕ) : Finset ℕ :=
  S.filter fun q => q < p

/-- Prime coordinates of `S` strictly after `p`. -/
def firstJumpTailPrimeUniverse
    (S : Finset ℕ) (p : ℕ) : Finset ℕ :=
  S.filter fun q => p < q

@[simp] theorem mem_firstJumpPredecessorPrimeUniverse
    {S : Finset ℕ} {p q : ℕ} :
    q ∈ firstJumpPredecessorPrimeUniverse S p ↔ q ∈ S ∧ q < p := by
  simp [firstJumpPredecessorPrimeUniverse]

@[simp] theorem mem_firstJumpTailPrimeUniverse
    {S : Finset ℕ} {p q : ℕ} :
    q ∈ firstJumpTailPrimeUniverse S p ↔ q ∈ S ∧ p < q := by
  simp [firstJumpTailPrimeUniverse]

/-- Every face containing `p` decomposes uniquely into predecessor, jump, and
tail coordinates. -/
theorem face_eq_insert_predecessor_union_firstJumpTail
    {t : Finset ℕ} {p : ℕ} (hpt : p ∈ t) :
    t = insert p (predecessorPrimeFace t p ∪ firstJumpTailFace t p) := by
  ext q
  constructor
  · intro hqt
    by_cases hqp : q = p
    · subst q
      simp
    · by_cases hlt : q < p
      · exact Finset.mem_insert_of_mem
          (Finset.mem_union_left _
            (mem_predecessorPrimeFace.mpr ⟨hqt, hlt⟩))
      · have hgt : p < q := by omega
        exact Finset.mem_insert_of_mem
          (Finset.mem_union_right _
            (mem_firstJumpTailFace.mpr ⟨hqt, hgt⟩))
  · intro hq
    rcases Finset.mem_insert.mp hq with hEq | hrest
    · simpa [hEq] using hpt
    · rcases Finset.mem_union.mp hrest with hpred | htail
      · exact (mem_predecessorPrimeFace.mp hpred).1
      · exact (mem_firstJumpTailFace.mp htail).1

/-- Predecessor and strict-tail coordinates are disjoint. -/
theorem predecessorPrimeFace_disjoint_firstJumpTailFace
    (t : Finset ℕ) (p : ℕ) :
    Disjoint (predecessorPrimeFace t p) (firstJumpTailFace t p) := by
  rw [Finset.disjoint_left]
  intro q hpred htail
  have hpq := (mem_predecessorPrimeFace.mp hpred).2
  have hqp := (mem_firstJumpTailFace.mp htail).2
  omega

/-- The first-jump coordinate is in neither the predecessor nor tail face. -/
theorem firstJump_not_mem_predecessor_union_tail
    (t : Finset ℕ) (p : ℕ) :
    p ∉ predecessorPrimeFace t p ∪ firstJumpTailFace t p := by
  simp

/-- Product factorization along the canonical `u,p,v` decomposition. -/
theorem primeFaceProduct_eq_predecessor_mul_jump_mul_tail
    {t : Finset ℕ} {p : ℕ} (hpt : p ∈ t) :
    primeFaceProduct t =
      p * primeFaceProduct (predecessorPrimeFace t p) *
        primeFaceProduct (firstJumpTailFace t p) := by
  rw [face_eq_insert_predecessor_union_firstJumpTail hpt]
  rw [primeFaceProduct_insert_eq_mul
    (firstJump_not_mem_predecessor_union_tail t p)]
  rw [primeFaceProduct_union_of_disjoint
    (predecessorPrimeFace_disjoint_firstJumpTailFace t p)]
  ring

/-- Sign factorization along the canonical `u,p,v` decomposition. -/
theorem booleanCubeSign_eq_neg_predecessor_mul_tail
    {t : Finset ℕ} {p : ℕ} (hpt : p ∈ t) :
    booleanCubeSign t =
      -(booleanCubeSign (predecessorPrimeFace t p) *
        booleanCubeSign (firstJumpTailFace t p)) := by
  rw [face_eq_insert_predecessor_union_firstJumpTail hpt]
  have hpNot := firstJump_not_mem_predecessor_union_tail t p
  rw [booleanCubeSign_insert_eq_neg hpNot]
  unfold booleanCubeSign
  rw [Finset.card_union_of_disjoint
    (predecessorPrimeFace_disjoint_firstJumpTailFace t p), pow_add]
  ring

/-- At a canonical first jump, the complete predecessor face is already dense. -/
theorem isPredecessorFirstJumpAt_predecessor_dense
    {d Y : ℕ} {t : Finset ℕ} {p : ℕ}
    (hfirst : IsPredecessorFirstJumpAt d Y t p) :
    PredecessorDenseFace d Y (predecessorPrimeFace t p) := by
  exact predecessorPrimeFace_dense_of_previous hfirst.2.2.2

/-- The old part of a first-jump face lies in the strict predecessor universe. -/
theorem predecessor_of_firstJumpSlice_mem_predecessorUniverse
    {d Y : ℕ} {S : Finset ℕ} {A B p : ℕ} {t : Finset ℕ}
    (ht : t ∈ predecessorFirstJumpFrozenWindowSlice d Y S A B p) :
    predecessorPrimeFace t p ∈
      (firstJumpPredecessorPrimeUniverse S p).powerset := by
  rcases mem_predecessorFirstJumpFrozenWindowSlice.mp ht with
    ⟨hjump, _hfirst⟩
  have hwindow := (mem_predecessorFirstJumpFrozenWindowFaces.mp hjump).1
  have htPow := (mem_frozenPrimeUniverseWindowFaces.mp hwindow).1
  have htSub := Finset.mem_powerset.mp htPow
  apply Finset.mem_powerset.mpr
  intro q hq
  rcases mem_predecessorPrimeFace.mp hq with ⟨hqt, hqp⟩
  exact mem_firstJumpPredecessorPrimeUniverse.mpr ⟨htSub hqt, hqp⟩

/-- The later part lies in the strict tail universe. -/
theorem tail_of_firstJumpSlice_mem_tailUniverse
    {d Y : ℕ} {S : Finset ℕ} {A B p : ℕ} {t : Finset ℕ}
    (ht : t ∈ predecessorFirstJumpFrozenWindowSlice d Y S A B p) :
    firstJumpTailFace t p ∈
      (firstJumpTailPrimeUniverse S p).powerset := by
  rcases mem_predecessorFirstJumpFrozenWindowSlice.mp ht with
    ⟨hjump, _hfirst⟩
  have hwindow := (mem_predecessorFirstJumpFrozenWindowFaces.mp hjump).1
  have htPow := (mem_frozenPrimeUniverseWindowFaces.mp hwindow).1
  have htSub := Finset.mem_powerset.mp htPow
  apply Finset.mem_powerset.mpr
  intro q hq
  rcases mem_firstJumpTailFace.mp hq with ⟨hqt, hpq⟩
  exact mem_firstJumpTailPrimeUniverse.mpr ⟨htSub hqt, hpq⟩

/-- At the first jump, the predecessor is already dense and the failure
inequality depends only on its product. -/
theorem firstJumpSlice_predecessor_dense_and_jump
    {d Y : ℕ} {S : Finset ℕ} {A B p : ℕ} {t : Finset ℕ}
    (ht : t ∈ predecessorFirstJumpFrozenWindowSlice d Y S A B p) :
    PredecessorDenseFace d Y (predecessorPrimeFace t p) ∧
      Y < p ∧
      Y * primeFaceProduct (predecessorPrimeFace t p) < p ^ d := by
  have hfirst := (mem_predecessorFirstJumpFrozenWindowSlice.mp ht).2
  refine ⟨isPredecessorFirstJumpAt_predecessor_dense hfirst,
    hfirst.2.1, ?_⟩
  simpa [predecessorPrimeFaceProduct] using hfirst.2.2.1

/-! ### Second Fubini step: fix the predecessor `u` -/

/-- First-jump faces with fixed canonical predecessor `u`. -/
def predecessorFirstJumpFrozenWindowPredecessorSlice
    (d Y : ℕ) (S : Finset ℕ) (A B p : ℕ) (u : Finset ℕ) :
    Finset (Finset ℕ) :=
  (predecessorFirstJumpFrozenWindowSlice d Y S A B p).filter fun t =>
    predecessorPrimeFace t p = u

@[simp] theorem mem_predecessorFirstJumpFrozenWindowPredecessorSlice
    {d Y : ℕ} {S : Finset ℕ} {A B p : ℕ} {u t : Finset ℕ} :
    t ∈ predecessorFirstJumpFrozenWindowPredecessorSlice d Y S A B p u ↔
      t ∈ predecessorFirstJumpFrozenWindowSlice d Y S A B p ∧
        predecessorPrimeFace t p = u := by
  simp [predecessorFirstJumpFrozenWindowPredecessorSlice]

/-- Fixed-predecessor slices are pairwise disjoint. -/
theorem predecessorFirstJumpFrozenWindowPredecessorSlice_pairwise
    (d Y : ℕ) (S : Finset ℕ) (A B p : ℕ) :
    Set.PairwiseDisjoint
      (↑((firstJumpPredecessorPrimeUniverse S p).powerset))
      (predecessorFirstJumpFrozenWindowPredecessorSlice d Y S A B p) := by
  intro u _hu v _hv huv
  change Disjoint
    (predecessorFirstJumpFrozenWindowPredecessorSlice d Y S A B p u)
    (predecessorFirstJumpFrozenWindowPredecessorSlice d Y S A B p v)
  rw [Finset.disjoint_left]
  intro t htu htv
  have huEq :=
    (mem_predecessorFirstJumpFrozenWindowPredecessorSlice.mp htu).2
  have hvEq :=
    (mem_predecessorFirstJumpFrozenWindowPredecessorSlice.mp htv).2
  exact huv (huEq.symm.trans hvEq)

/-- One `p`-slice is the disjoint union over its canonical predecessors. -/
theorem predecessorFirstJumpFrozenWindowSlice_eq_biUnion_predecessors
    (d Y : ℕ) (S : Finset ℕ) (A B p : ℕ) :
    predecessorFirstJumpFrozenWindowSlice d Y S A B p =
      (firstJumpPredecessorPrimeUniverse S p).powerset.biUnion
        (predecessorFirstJumpFrozenWindowPredecessorSlice d Y S A B p) := by
  ext t
  constructor
  · intro ht
    let u := predecessorPrimeFace t p
    have hu := predecessor_of_firstJumpSlice_mem_predecessorUniverse ht
    exact Finset.mem_biUnion.mpr
      ⟨u, hu,
        mem_predecessorFirstJumpFrozenWindowPredecessorSlice.mpr ⟨ht, rfl⟩⟩
  · intro ht
    rcases Finset.mem_biUnion.mp ht with ⟨u, _hu, htu⟩
    exact (mem_predecessorFirstJumpFrozenWindowPredecessorSlice.mp htu).1

/-- Signed mass of a fixed `(p,u)` first-jump slice. -/
def predecessorFirstJumpFrozenWindowPredecessorSliceMass
    (d Y : ℕ) (S : Finset ℕ) (A B p : ℕ) (u : Finset ℕ) : ℤ :=
  ∑ t ∈ predecessorFirstJumpFrozenWindowPredecessorSlice d Y S A B p u,
    booleanCubeSign t

/-- **Second Fubini step.** -/
theorem predecessorFirstJumpFrozenWindowSliceMass_eq_sum_predecessors
    (d Y : ℕ) (S : Finset ℕ) (A B p : ℕ) :
    predecessorFirstJumpFrozenWindowSliceMass d Y S A B p =
      ∑ u ∈ (firstJumpPredecessorPrimeUniverse S p).powerset,
        predecessorFirstJumpFrozenWindowPredecessorSliceMass
          d Y S A B p u := by
  unfold predecessorFirstJumpFrozenWindowSliceMass
    predecessorFirstJumpFrozenWindowPredecessorSliceMass
  rw [predecessorFirstJumpFrozenWindowSlice_eq_biUnion_predecessors]
  exact Finset.sum_biUnion
    (predecessorFirstJumpFrozenWindowPredecessorSlice_pairwise
      d Y S A B p)

/-! ### The fixed `(p,u)` remainder is exactly a frozen tail cube -/

/-- The strict tail window after fixing predecessor `u` and jump `p`. -/
def predecessorFirstJumpTailWindowFaces
    (S : Finset ℕ) (A B p : ℕ) (u : Finset ℕ) : Finset (Finset ℕ) :=
  frozenPrimeUniverseWindowFaces
    (firstJumpTailPrimeUniverse S p)
    (A / (p * primeFaceProduct u))
    (B / (p * primeFaceProduct u))

/-- Signed mass of that strict tail cube. -/
def predecessorFirstJumpTailWindowMass
    (S : Finset ℕ) (A B p : ℕ) (u : Finset ℕ) : ℤ :=
  frozenPrimeUniverseWindowMass
    (firstJumpTailPrimeUniverse S p)
    (A / (p * primeFaceProduct u))
    (B / (p * primeFaceProduct u))

/-- Reassemble a face from its predecessor, jump coordinate, and strict tail. -/
def assembleFirstJumpFace
    (u : Finset ℕ) (p : ℕ) (v : Finset ℕ) : Finset ℕ :=
  insert p (u ∪ v)

/-- Reassembly recovers the fixed predecessor. -/
theorem predecessorPrimeFace_assembleFirstJumpFace
    {u v : Finset ℕ} {p : ℕ}
    (huLt : ∀ q ∈ u, q < p) (hvGt : ∀ q ∈ v, p < q) :
    predecessorPrimeFace (assembleFirstJumpFace u p v) p = u := by
  ext q
  constructor
  · intro hq
    rcases mem_predecessorPrimeFace.mp hq with ⟨hqFace, hqp⟩
    rcases Finset.mem_insert.mp hqFace with hEq | hUnion
    · subst q
      omega
    · rcases Finset.mem_union.mp hUnion with hqu | hqv
      · exact hqu
      · exact (not_lt_of_ge (hvGt q hqv).le hqp).elim
  · intro hqu
    exact mem_predecessorPrimeFace.mpr
      ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ hqu), huLt q hqu⟩

/-- Reassembly recovers the strict tail. -/
theorem firstJumpTailFace_assembleFirstJumpFace
    {u v : Finset ℕ} {p : ℕ}
    (huLt : ∀ q ∈ u, q < p) (hvGt : ∀ q ∈ v, p < q) :
    firstJumpTailFace (assembleFirstJumpFace u p v) p = v := by
  ext q
  constructor
  · intro hq
    rcases mem_firstJumpTailFace.mp hq with ⟨hqFace, hpq⟩
    rcases Finset.mem_insert.mp hqFace with hEq | hUnion
    · subst q
      omega
    · rcases Finset.mem_union.mp hUnion with hqu | hqv
      · exact (not_lt_of_ge (huLt q hqu).le hpq).elim
      · exact hqv
  · intro hqv
    exact mem_firstJumpTailFace.mpr
      ⟨Finset.mem_insert_of_mem (Finset.mem_union_right _ hqv), hvGt q hqv⟩

/-- Earlier predecessor faces are unchanged by the first jump and its tail. -/
theorem predecessorPrimeFace_assembleFirstJumpFace_of_lt
    {u v : Finset ℕ} {p q : ℕ} (hqp : q < p)
    (hvGt : ∀ r ∈ v, p < r) :
    predecessorPrimeFace (assembleFirstJumpFace u p v) q =
      predecessorPrimeFace u q := by
  ext r
  constructor
  · intro hr
    rcases mem_predecessorPrimeFace.mp hr with ⟨hrFace, hrq⟩
    rcases Finset.mem_insert.mp hrFace with hEq | hUnion
    · subst r
      omega
    · rcases Finset.mem_union.mp hUnion with hru | hrv
      · exact mem_predecessorPrimeFace.mpr ⟨hru, hrq⟩
      · have hpr := hvGt r hrv
        omega
  · intro hr
    rcases mem_predecessorPrimeFace.mp hr with ⟨hru, hrq⟩
    exact mem_predecessorPrimeFace.mpr
      ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ hru), hrq⟩

/-- Reassembly stays inside the original prime universe. -/
theorem assembleFirstJumpFace_mem_powerset
    {S u v : Finset ℕ} {p : ℕ}
    (hpS : p ∈ S)
    (hu : u ∈ (firstJumpPredecessorPrimeUniverse S p).powerset)
    (hv : v ∈ (firstJumpTailPrimeUniverse S p).powerset) :
    assembleFirstJumpFace u p v ∈ S.powerset := by
  have huSub := Finset.mem_powerset.mp hu
  have hvSub := Finset.mem_powerset.mp hv
  apply Finset.mem_powerset.mpr
  intro q hq
  rcases Finset.mem_insert.mp hq with hEq | hUnion
  · simpa [hEq] using hpS
  · rcases Finset.mem_union.mp hUnion with hqu | hqv
    · exact (mem_firstJumpPredecessorPrimeUniverse.mp (huSub hqu)).1
    · exact (mem_firstJumpTailPrimeUniverse.mp (hvSub hqv)).1

/-- Reassembly has `p` as its canonical first jump whenever `u` is already
dense and the jump inequality fails at `p`. -/
theorem assembleFirstJumpFace_isPredecessorFirstJumpAt
    {d Y : ℕ} {S u v : Finset ℕ} {p : ℕ}
    (hu : u ∈ (firstJumpPredecessorPrimeUniverse S p).powerset)
    (hv : v ∈ (firstJumpTailPrimeUniverse S p).powerset)
    (huDense : PredecessorDenseFace d Y u)
    (hYp : Y < p) (hfail : Y * primeFaceProduct u < p ^ d) :
    IsPredecessorFirstJumpAt d Y (assembleFirstJumpFace u p v) p := by
  have huSub := Finset.mem_powerset.mp hu
  have hvSub := Finset.mem_powerset.mp hv
  have huLt : ∀ q ∈ u, q < p := by
    intro q hqu
    exact (mem_firstJumpPredecessorPrimeUniverse.mp (huSub hqu)).2
  have hvGt : ∀ q ∈ v, p < q := by
    intro q hqv
    exact (mem_firstJumpTailPrimeUniverse.mp (hvSub hqv)).2
  refine ⟨by simp [assembleFirstJumpFace], hYp, ?_, ?_⟩
  · rw [predecessorPrimeFaceProduct]
    rw [predecessorPrimeFace_assembleFirstJumpFace huLt hvGt]
    exact hfail
  · intro q hqFace hqp hYq
    have hqPred : q ∈ predecessorPrimeFace (assembleFirstJumpFace u p v) p :=
      mem_predecessorPrimeFace.mpr ⟨hqFace, hqp⟩
    rw [predecessorPrimeFace_assembleFirstJumpFace huLt hvGt] at hqPred
    have hgood := huDense q hqPred hYq
    rw [predecessorPrimeFaceProduct]
    rw [predecessorPrimeFace_assembleFirstJumpFace_of_lt hqp hvGt]
    exact hgood

/-- Every fixed-slice tail is a face of the scaled frozen tail window. -/
theorem tail_of_firstJumpPredecessorSlice_mem_tailWindow
    {d Y : ℕ} {S : Finset ℕ} {A B p : ℕ} {u t : Finset ℕ}
    (hprimeS : ∀ q ∈ S, q.Prime)
    (ht : t ∈ predecessorFirstJumpFrozenWindowPredecessorSlice
      d Y S A B p u) :
    firstJumpTailFace t p ∈ predecessorFirstJumpTailWindowFaces S A B p u := by
  have htSlice :=
    (mem_predecessorFirstJumpFrozenWindowPredecessorSlice.mp ht).1
  have huEq :=
    (mem_predecessorFirstJumpFrozenWindowPredecessorSlice.mp ht).2
  have hfirst := (mem_predecessorFirstJumpFrozenWindowSlice.mp htSlice).2
  have hjump := (mem_predecessorFirstJumpFrozenWindowSlice.mp htSlice).1
  have hwindow := (mem_predecessorFirstJumpFrozenWindowFaces.mp hjump).1
  rcases mem_frozenPrimeUniverseWindowFaces.mp hwindow with
    ⟨htPow, hlo, hup⟩
  have htSub := Finset.mem_powerset.mp htPow
  have hpPrime : p.Prime := hprimeS p (htSub hfirst.1)
  have huPos : 0 < primeFaceProduct u := by
    rw [← huEq]
    unfold primeFaceProduct
    exact Finset.prod_pos fun q hq =>
      (hprimeS q (htSub (mem_predecessorPrimeFace.mp hq).1)).pos
  have hbasePos : 0 < p * primeFaceProduct u := Nat.mul_pos hpPrime.pos huPos
  apply mem_frozenPrimeUniverseWindowFaces.mpr
  refine ⟨tail_of_firstJumpSlice_mem_tailUniverse htSlice, ?_, ?_⟩
  · apply (Nat.div_lt_iff_lt_mul hbasePos).2
    have hprod := primeFaceProduct_eq_predecessor_mul_jump_mul_tail hfirst.1
    rw [huEq] at hprod
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using (hprod ▸ hlo)
  · apply (Nat.le_div_iff_mul_le hbasePos).2
    have hprod := primeFaceProduct_eq_predecessor_mul_jump_mul_tail hfirst.1
    rw [huEq] at hprod
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using (hprod ▸ hup)

/-- Conversely, every face of the scaled strict tail window reassembles to the
fixed first-jump slice. -/
theorem assembleFirstJumpFace_mem_predecessorSlice_of_tailWindow
    {d Y : ℕ} {S : Finset ℕ} {A B p : ℕ} {u v : Finset ℕ}
    (hprimeS : ∀ q ∈ S, q.Prime) (hpS : p ∈ S)
    (hu : u ∈ (firstJumpPredecessorPrimeUniverse S p).powerset)
    (huDense : PredecessorDenseFace d Y u)
    (hYp : Y < p) (hfail : Y * primeFaceProduct u < p ^ d)
    (hv : v ∈ predecessorFirstJumpTailWindowFaces S A B p u) :
    assembleFirstJumpFace u p v ∈
      predecessorFirstJumpFrozenWindowPredecessorSlice d Y S A B p u := by
  rcases mem_frozenPrimeUniverseWindowFaces.mp hv with
    ⟨hvPow, hlo, hup⟩
  have huSub := Finset.mem_powerset.mp hu
  have hvSub := Finset.mem_powerset.mp hvPow
  have huLt : ∀ q ∈ u, q < p := by
    intro q hqu
    exact (mem_firstJumpPredecessorPrimeUniverse.mp (huSub hqu)).2
  have hvGt : ∀ q ∈ v, p < q := by
    intro q hqv
    exact (mem_firstJumpTailPrimeUniverse.mp (hvSub hqv)).2
  have hpPrime := hprimeS p hpS
  have huPos : 0 < primeFaceProduct u := by
    unfold primeFaceProduct
    exact Finset.prod_pos fun q hq =>
      (hprimeS q
        (mem_firstJumpPredecessorPrimeUniverse.mp (huSub hq)).1).pos
  have hbasePos : 0 < p * primeFaceProduct u := Nat.mul_pos hpPrime.pos huPos
  have hfirst := assembleFirstJumpFace_isPredecessorFirstJumpAt
    hu hvPow huDense hYp hfail
  have htPow := assembleFirstJumpFace_mem_powerset hpS hu hvPow
  have hpredEq := predecessorPrimeFace_assembleFirstJumpFace huLt hvGt
  have htailEq := firstJumpTailFace_assembleFirstJumpFace huLt hvGt
  have hprod :
      primeFaceProduct (assembleFirstJumpFace u p v) =
        p * primeFaceProduct u * primeFaceProduct v := by
    have h := primeFaceProduct_eq_predecessor_mul_jump_mul_tail hfirst.1
    simpa [hpredEq, htailEq] using h
  have hloFull : A < primeFaceProduct (assembleFirstJumpFace u p v) := by
    have h := (Nat.div_lt_iff_lt_mul hbasePos).1 hlo
    rw [hprod]
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  have hupFull : primeFaceProduct (assembleFirstJumpFace u p v) ≤ B := by
    have h := (Nat.le_div_iff_mul_le hbasePos).1 hup
    rw [hprod]
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  have hwindow :
      assembleFirstJumpFace u p v ∈ frozenPrimeUniverseWindowFaces S A B :=
    mem_frozenPrimeUniverseWindowFaces.mpr ⟨htPow, hloFull, hupFull⟩
  have hnotDense : ¬ PredecessorDenseFace d Y (assembleFirstJumpFace u p v) := by
    intro hdense
    have hgood := hdense p hfirst.1 hYp
    rw [predecessorPrimeFaceProduct] at hgood
    rw [hpredEq] at hgood
    omega
  have hjump :
      assembleFirstJumpFace u p v ∈ predecessorFirstJumpFrozenWindowFaces
        d Y S A B :=
    mem_predecessorFirstJumpFrozenWindowFaces.mpr ⟨hwindow, hnotDense⟩
  have hslice :
      assembleFirstJumpFace u p v ∈ predecessorFirstJumpFrozenWindowSlice
        d Y S A B p :=
    mem_predecessorFirstJumpFrozenWindowSlice.mpr ⟨hjump, hfirst⟩
  exact mem_predecessorFirstJumpFrozenWindowPredecessorSlice.mpr
    ⟨hslice, hpredEq⟩

/-- **Exact fixed-`(p,u)` tail-cube factorization.**  The fixed predecessor
slice is not merely bounded by a tail cube: it is in signed bijection with it.
The only scalar left outside the tail is the predecessor Boolean sign. -/
theorem predecessorFirstJumpFrozenWindowPredecessorSliceMass_eq_tailWindowMass
    {d Y : ℕ} {S : Finset ℕ} {A B p : ℕ} {u : Finset ℕ}
    (hprimeS : ∀ q ∈ S, q.Prime) (hpS : p ∈ S)
    (hu : u ∈ (firstJumpPredecessorPrimeUniverse S p).powerset)
    (huDense : PredecessorDenseFace d Y u)
    (hYp : Y < p) (hfail : Y * primeFaceProduct u < p ^ d) :
    predecessorFirstJumpFrozenWindowPredecessorSliceMass
        d Y S A B p u =
      -booleanCubeSign u * predecessorFirstJumpTailWindowMass S A B p u := by
  classical
  unfold predecessorFirstJumpFrozenWindowPredecessorSliceMass
    predecessorFirstJumpTailWindowMass frozenPrimeUniverseWindowMass
    predecessorFirstJumpTailWindowFaces
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun t _ht => firstJumpTailFace t p) ?_ ?_ ?_ ?_
  · intro t ht
    exact tail_of_firstJumpPredecessorSlice_mem_tailWindow hprimeS ht
  · intro t₁ ht₁ t₂ ht₂ htail
    have hdata₁ :=
      mem_predecessorFirstJumpFrozenWindowPredecessorSlice.mp ht₁
    have hdata₂ :=
      mem_predecessorFirstJumpFrozenWindowPredecessorSlice.mp ht₂
    have hp₁ :=
      (mem_predecessorFirstJumpFrozenWindowSlice.mp hdata₁.1).2.1
    have hp₂ :=
      (mem_predecessorFirstJumpFrozenWindowSlice.mp hdata₂.1).2.1
    calc
      t₁ = insert p (u ∪ firstJumpTailFace t₁ p) := by
        rw [face_eq_insert_predecessor_union_firstJumpTail hp₁, hdata₁.2]
      _ = insert p (u ∪ firstJumpTailFace t₂ p) := by rw [htail]
      _ = t₂ := by
        rw [← face_eq_insert_predecessor_union_firstJumpTail hp₂, hdata₂.2]
  · intro v hv
    have ht := assembleFirstJumpFace_mem_predecessorSlice_of_tailWindow
      hprimeS hpS hu huDense hYp hfail hv
    refine ⟨assembleFirstJumpFace u p v, ht, ?_⟩
    have huSub := Finset.mem_powerset.mp hu
    have hvPow := (mem_frozenPrimeUniverseWindowFaces.mp hv).1
    have hvSub := Finset.mem_powerset.mp hvPow
    have huLt : ∀ q ∈ u, q < p := by
      intro q hqu
      exact (mem_firstJumpPredecessorPrimeUniverse.mp (huSub hqu)).2
    have hvGt : ∀ q ∈ v, p < q := by
      intro q hqv
      exact (mem_firstJumpTailPrimeUniverse.mp (hvSub hqv)).2
    exact firstJumpTailFace_assembleFirstJumpFace huLt hvGt
  · intro t ht
    have hdata :=
      mem_predecessorFirstJumpFrozenWindowPredecessorSlice.mp ht
    have hfirst := (mem_predecessorFirstJumpFrozenWindowSlice.mp hdata.1).2
    have hsign := booleanCubeSign_eq_neg_predecessor_mul_tail hfirst.1
    rw [hdata.2] at hsign
    simpa [mul_assoc] using hsign

/-- A fixed predecessor slice is empty unless its predecessor is dense and its
jump really fails at `p`. -/
theorem predecessorFirstJumpFrozenWindowPredecessorSlice_eq_empty_of_inactive
    {d Y : ℕ} {S : Finset ℕ} {A B p : ℕ} {u : Finset ℕ}
    (hinactive : ¬ (PredecessorDenseFace d Y u ∧
      Y < p ∧ Y * primeFaceProduct u < p ^ d)) :
    predecessorFirstJumpFrozenWindowPredecessorSlice d Y S A B p u = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro t ht
  have hdata :=
    firstJumpSlice_predecessor_dense_and_jump
      (mem_predecessorFirstJumpFrozenWindowPredecessorSlice.mp ht).1
  have huEq :=
    (mem_predecessorFirstJumpFrozenWindowPredecessorSlice.mp ht).2
  apply hinactive
  simpa [huEq] using hdata

/-- The exact signed first-jump slice indexed by `p`, written in the desired
`u,p,v` coordinates.  Inactive predecessor cubes contribute zero. -/
def predecessorFirstJumpEulerSliceMass
    (d Y : ℕ) (S : Finset ℕ) (A B p : ℕ) : ℤ :=
  ∑ u ∈ (firstJumpPredecessorPrimeUniverse S p).powerset,
    if PredecessorDenseFace d Y u ∧
        Y < p ∧ Y * primeFaceProduct u < p ^ d then
      -booleanCubeSign u * predecessorFirstJumpTailWindowMass S A B p u
    else 0

/-- One canonical `p`-slice is exactly its signed low-predecessor / tail-cube
Fubini expansion. -/
theorem predecessorFirstJumpFrozenWindowSliceMass_eq_eulerSliceMass
    {d Y : ℕ} {S : Finset ℕ} {A B p : ℕ}
    (hprimeS : ∀ q ∈ S, q.Prime) (hpS : p ∈ S) :
    predecessorFirstJumpFrozenWindowSliceMass d Y S A B p =
      predecessorFirstJumpEulerSliceMass d Y S A B p := by
  rw [predecessorFirstJumpFrozenWindowSliceMass_eq_sum_predecessors]
  unfold predecessorFirstJumpEulerSliceMass
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hactive : PredecessorDenseFace d Y u ∧
      Y < p ∧ Y * primeFaceProduct u < p ^ d
  · rw [if_pos hactive]
    exact predecessorFirstJumpFrozenWindowPredecessorSliceMass_eq_tailWindowMass
      hprimeS hpS hu hactive.1 hactive.2.1 hactive.2.2
  · rw [if_neg hactive]
    rw [predecessorFirstJumpFrozenWindowPredecessorSlice_eq_empty_of_inactive
      hactive]
    simp [predecessorFirstJumpFrozenWindowPredecessorSliceMass]

/-- **Exact first-jump ledger.**  The whole residual is now one signed sum over
first jumps `p`, each carrying only an already-dense predecessor `u` and an
unestimated tail cube `v`. -/
theorem predecessorFirstJumpFrozenWindowMass_eq_sum_eulerSlices
    {d Y : ℕ} {S : Finset ℕ} {A B : ℕ}
    (hprimeS : ∀ q ∈ S, q.Prime) :
    predecessorFirstJumpFrozenWindowMass d Y S A B =
      ∑ p ∈ S, predecessorFirstJumpEulerSliceMass d Y S A B p := by
  rw [predecessorFirstJumpFrozenWindowMass_eq_sum_slices]
  apply Finset.sum_congr rfl
  intro p hpS
  exact predecessorFirstJumpFrozenWindowSliceMass_eq_eulerSliceMass hprimeS hpS

/-! ### Sequential Euler recurrence on the strict tail cube -/

/-- Adding a new coordinate `r > p` inserts it exactly into the strict tail
universe. -/
theorem firstJumpTailPrimeUniverse_insert_of_gt
    {S : Finset ℕ} {p r : ℕ} (hpr : p < r) :
    firstJumpTailPrimeUniverse (insert r S) p =
      insert r (firstJumpTailPrimeUniverse S p) := by
  ext q
  simp [firstJumpTailPrimeUniverse, hpr]

/-- A fresh later prime is not already in the old strict tail universe. -/
theorem not_mem_firstJumpTailPrimeUniverse_of_not_mem
    {S : Finset ℕ} {p r : ℕ} (hrS : r ∉ S) :
    r ∉ firstJumpTailPrimeUniverse S p := by
  intro hr
  exact hrS (mem_firstJumpTailPrimeUniverse.mp hr).1

/-- **Tail Euler recurrence.**  Once `(p,u)` is fixed, adding one later fresh
prime subtracts exactly the reciprocal-compressed old tail cube. -/
theorem predecessorFirstJumpTailWindowMass_insert_later
    {S : Finset ℕ} {A B p r : ℕ} {u : Finset ℕ}
    (hrS : r ∉ S) (hrPrime : r.Prime) (hpr : p < r) (hAB : A ≤ B) :
    predecessorFirstJumpTailWindowMass (insert r S) A B p u =
      predecessorFirstJumpTailWindowMass S A B p u -
        frozenPrimeUniverseWindowMass
          (firstJumpTailPrimeUniverse S p)
          ((A / (p * primeFaceProduct u)) / r)
          ((B / (p * primeFaceProduct u)) / r) := by
  unfold predecessorFirstJumpTailWindowMass
  rw [firstJumpTailPrimeUniverse_insert_of_gt hpr]
  exact frozenPrimeUniverseWindowMass_insert
    (not_mem_firstJumpTailPrimeUniverse_of_not_mem hrS)
    hrPrime
    (Nat.div_le_div_right hAB)

/-! ### Square-root specialization and explicit remaining seam -/

/-- On the #567 square-root residual, every canonical first jump lies strictly
between the fourth-root cutoff and the old owner. -/
theorem sqrtFirstJumpSlice_coordinate_band
    {R q A B p : ℕ} {t : Finset ℕ}
    (ht : t ∈ predecessorFirstJumpFrozenWindowSlice
      3 (Nat.sqrt R) (primesUpTo (q - 1)) A B p) :
    Nat.sqrt R < p ∧ p < q := by
  have hfirst := (mem_predecessorFirstJumpFrozenWindowSlice.mp ht).2
  have hjump := (mem_predecessorFirstJumpFrozenWindowSlice.mp ht).1
  have hwindow := (mem_predecessorFirstJumpFrozenWindowFaces.mp hjump).1
  have htPow := (mem_frozenPrimeUniverseWindowFaces.mp hwindow).1
  have hpOld := (Finset.mem_powerset.mp htPow) hfirst.1
  rcases mem_primesUpTo.mp hpOld with ⟨_hpPrime, hpLe⟩
  exact ⟨hfirst.2.1, by omega⟩

/-- The remaining quantitative target is deliberately stated on the complete
signed first-jump ledger, never on fixed `p`-slices separately. -/
def SqrtFirstJumpSignedBoundStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R q A B : ℕ,
        Nat.sqrt R < q → B ≤ R →
        ‖((predecessorFirstJumpFrozenWindowMass
          3 (Nat.sqrt R) (primesUpTo (q - 1)) A B : ℤ) : ℂ)‖ ^ 2 ≤
          C * Real.rpow (R : ℝ) (1 + ε)

end RHLean.Proof
import Mathlib
import RHLean.Proof.LowWheelCanonicalOrientedRunFibres

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
  · -- `subst` on the let-bound `s` replaces it by its definition `Nat.sqrt R`,
    -- not by `0`, so `hs` has to be handed to `simp` explicitly; the goal is
    -- then `0 * R < (0 + 1) ^ 4`.
    subst s
    simp [hs]
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

end RHLean.Proof

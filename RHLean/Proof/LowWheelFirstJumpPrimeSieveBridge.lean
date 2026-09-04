import Mathlib
import RHLean.Proof.LowWheelCanonicalSqrtDenseContraction
import RHLean.Analysis.PrimeSieveCollapseIdentity

/-!
# First-jump residual in the canonical prime-sieve coordinates

The square-root contraction leaves the exact signed column

`J(A,B) = sum_{s < p <= K} (M(A/p) - M(B/p))`,

with `s = sqrt R` and `K = q-1`.  This file identifies that column with the
repository's existing post-cutoff Mertens prime tail and then with the existing
quotient-reindexed reciprocal-Mertens signed sum.

The key point is that the reindexing itself needs **no** strict square-root
hypothesis.  The theorem
`primeSieveMertensPrimeTail_eq_reciprocalPrimeTail` is a finite quotient Fubini
identity for every pair `(y,x)`.  Hence the possible equality

`Nat.sqrt X = Nat.sqrt R`

is not an obstruction to this coordinate bridge.  That root equality becomes
relevant only if one subsequently invokes the separate high-source/all-plus
interpretation, whose current API assumes `Nat.sqrt X < y`.

No norm, triangle inequality, PNT estimate, prime-gap input, or new axiom is
introduced here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

/-- The literal high-prime Mertens column between prime cutoffs `s` and `K`. -/
def firstJumpPrimeSieveMertensBand (s K X : ℕ) : ℂ :=
  ∑ p ∈ frozenPrimeUniverseHighPrimeSet s K,
    mertensSummatory (X / p)

/-- The frozen high-prime set is exactly the prime-filtered integer interval
`(s,K]`. -/
theorem frozenPrimeUniverseHighPrimeSet_eq_Ioc_filter_prime
    (s K : ℕ) :
    frozenPrimeUniverseHighPrimeSet s K =
      (Finset.Ioc s K).filter Nat.Prime := by
  ext p
  simp [mem_frozenPrimeUniverseHighPrimeSet, and_left_comm,
    and_comm, and_assoc]

/-- Interval form of the high-prime Mertens column. -/
theorem firstJumpPrimeSieveMertensBand_eq_Ioc
    (s K X : ℕ) :
    firstJumpPrimeSieveMertensBand s K X =
      ∑ p ∈ Finset.Ioc s K,
        if p.Prime then mertensSummatory (X / p) else 0 := by
  unfold firstJumpPrimeSieveMertensBand
  rw [frozenPrimeUniverseHighPrimeSet_eq_Ioc_filter_prime]
  rw [Finset.sum_filter]

/-- Terms beyond the physical endpoint `X` vanish because their reciprocal
quotient is zero and `M(0)=0`. -/
theorem sum_Ioc_mertens_div_eq_zero_of_endpoint_le
    {X a b : ℕ} (hXa : X ≤ a) :
    (∑ p ∈ Finset.Ioc a b,
      if p.Prime then mertensSummatory (X / p) else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  have hap : a < p := (Finset.mem_Ioc.mp hp).1
  have hXp : X < p := hXa.trans_lt hap
  have hdiv : X / p = 0 := Nat.div_eq_of_lt hXp
  simp [hdiv]

/-- **Prime-band = difference of the repository prime tails.**

For `s <= K`, the literal prime band `(s,K]` equals the difference between the
post-`s` and post-`K` Mertens prime tails.  This remains exact when `K > X`:
the apparent extra primes have quotient zero and therefore vanish. -/
theorem firstJumpPrimeSieveMertensBand_eq_tail_sub_tail
    {s K X : ℕ} (hsK : s ≤ K) :
    firstJumpPrimeSieveMertensBand s K X =
      primeSieveMertensPrimeTail s X -
        primeSieveMertensPrimeTail K X := by
  rw [firstJumpPrimeSieveMertensBand_eq_Ioc]
  unfold primeSieveMertensPrimeTail
  let f : ℕ → ℂ := fun p =>
    if p.Prime then mertensSummatory (X / p) else 0
  change (∑ p ∈ Finset.Ioc s K, f p) =
    (∑ p ∈ Finset.Ioc s X, f p) -
      ∑ p ∈ Finset.Ioc K X, f p
  by_cases hKX : K ≤ X
  · have hsplit := Finset.sum_Ioc_consecutive (f := f) hsK hKX
    exact (eq_sub_iff_add_eq).2 hsplit
  · have hXK : X < K := Nat.lt_of_not_ge hKX
    have htailK : (∑ p ∈ Finset.Ioc K X, f p) = 0 := by
      rw [Finset.Ioc_eq_empty_of_le hXK.le]
      simp
    by_cases hsX : s ≤ X
    · have hsplit := Finset.sum_Ioc_consecutive (f := f) hsX hXK.le
      have hzero : (∑ p ∈ Finset.Ioc X K, f p) = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        have hXp : X < p := (Finset.mem_Ioc.mp hp).1
        have hdiv : X / p = 0 := Nat.div_eq_of_lt hXp
        simp [f, hdiv]
      rw [hzero, add_zero] at hsplit
      rw [htailK, sub_zero]
      exact hsplit.symm
    · have hXs : X < s := Nat.lt_of_not_ge hsX
      have hband : (∑ p ∈ Finset.Ioc s K, f p) = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        have hsp : s < p := (Finset.mem_Ioc.mp hp).1
        have hXp : X < p := hXs.trans hsp
        have hdiv : X / p = 0 := Nat.div_eq_of_lt hXp
        simp [f, hdiv]
      have htailS : (∑ p ∈ Finset.Ioc s X, f p) = 0 := by
        rw [Finset.Ioc_eq_empty_of_le hXs.le]
        simp
      rw [hband, htailS, htailK, sub_zero]

/-- The same prime band in the quotient-reindexed prime-count coordinates.  No
square-root hypothesis appears: this is pure finite Fubini. -/
theorem firstJumpPrimeSieveMertensBand_eq_reciprocalSignedSum_sub
    {s K X : ℕ} (hsK : s ≤ K) :
    firstJumpPrimeSieveMertensBand s K X =
      primeSieveReciprocalMertensSignedSum s X -
        primeSieveReciprocalMertensSignedSum K X := by
  rw [firstJumpPrimeSieveMertensBand_eq_tail_sub_tail hsK]
  rw [primeSieveReciprocalMertensSignedSum_eq_mertensPrimeTail,
    primeSieveReciprocalMertensSignedSum_eq_mertensPrimeTail]

/-- Cast the integer #569 residual to the complex prime-sieve coordinate without
changing its sign structure. -/
theorem sqrtFirstJumpResidual_cast_eq_band_sub_band
    {R q A B : ℕ}
    (hqroot : Nat.sqrt R < q) (hBR : B ≤ R) (hAB : A ≤ B) :
    ((predecessorFirstJumpFrozenWindowMass
        3 (Nat.sqrt R) (primesUpTo (q - 1)) A B : ℤ) : ℂ) =
      firstJumpPrimeSieveMertensBand (Nat.sqrt R) (q - 1) A -
        firstJumpPrimeSieveMertensBand (Nat.sqrt R) (q - 1) B := by
  have hJ := sqrtFirstJumpResidual_eq_neg_sum_mertensGaps
    hqroot hBR hAB
  have hcast := congrArg (fun z : ℤ => (z : ℂ)) hJ
  push_cast at hcast
  rw [mertensSummatoryInt_cast] at hcast
  unfold firstJumpPrimeSieveMertensBand
  rw [Finset.sum_sub_distrib] at hcast
  simpa only [neg_sub] using hcast

/-- **#569 -> canonical prime-sieve Mertens tails.**
The first-jump residual is the difference of two high-prime bands, each written
as a difference of the already-existing prime tails. -/
theorem sqrtFirstJumpResidual_cast_eq_mertensPrimeTailDifference
    {R q A B : ℕ}
    (hqroot : Nat.sqrt R < q) (hBR : B ≤ R) (hAB : A ≤ B) :
    ((predecessorFirstJumpFrozenWindowMass
        3 (Nat.sqrt R) (primesUpTo (q - 1)) A B : ℤ) : ℂ) =
      (primeSieveMertensPrimeTail (Nat.sqrt R) A -
        primeSieveMertensPrimeTail (q - 1) A) -
      (primeSieveMertensPrimeTail (Nat.sqrt R) B -
        primeSieveMertensPrimeTail (q - 1) B) := by
  have hsK : Nat.sqrt R ≤ q - 1 := by omega
  rw [sqrtFirstJumpResidual_cast_eq_band_sub_band hqroot hBR hAB,
    firstJumpPrimeSieveMertensBand_eq_tail_sub_tail hsK,
    firstJumpPrimeSieveMertensBand_eq_tail_sub_tail hsK]

/-- The exact signed reciprocal-Mertens object left after the geometric
contractions.  It is deliberately a signed difference; no norm is built into
the definition. -/
def firstJumpReciprocalMertensDifference
    (s K A B : ℕ) : ℂ :=
  (primeSieveReciprocalMertensSignedSum s A -
      primeSieveReciprocalMertensSignedSum K A) -
    (primeSieveReciprocalMertensSignedSum s B -
      primeSieveReciprocalMertensSignedSum K B)

/-- **#569 -> reciprocal-prime-count/Mertens coordinate.**
This is the exact bridge requested for the next seam.  The right side expands
to lower-scale Mertens values paired with differences of reciprocal prime-count
weights. -/
theorem sqrtFirstJumpResidual_cast_eq_reciprocalMertensDifference
    {R q A B : ℕ}
    (hqroot : Nat.sqrt R < q) (hBR : B ≤ R) (hAB : A ≤ B) :
    ((predecessorFirstJumpFrozenWindowMass
        3 (Nat.sqrt R) (primesUpTo (q - 1)) A B : ℤ) : ℂ) =
      firstJumpReciprocalMertensDifference
        (Nat.sqrt R) (q - 1) A B := by
  have hsK : Nat.sqrt R ≤ q - 1 := by omega
  rw [sqrtFirstJumpResidual_cast_eq_band_sub_band hqroot hBR hAB]
  unfold firstJumpReciprocalMertensDifference
  rw [firstJumpPrimeSieveMertensBand_eq_reciprocalSignedSum_sub hsK,
    firstJumpPrimeSieveMertensBand_eq_reciprocalSignedSum_sub hsK]

/-! ## The root equality edge

The finite quotient bridge above is unconditional.  For later composition with
the high-source/all-plus theorems, record explicitly that an endpoint `X <= R`
has either strict lower square root or the single equality case.  Nothing is
silently strengthened to a strict inequality here.
-/

/-- Endpoints below `R` have no larger square root. -/
theorem sqrt_le_root_of_endpoint_le
    {R X : ℕ} (hXR : X ≤ R) :
    Nat.sqrt X ≤ Nat.sqrt R :=
  Nat.sqrt_le_sqrt hXR

/-- Explicit strict/equality split at the root boundary. -/
theorem sqrt_endpoint_root_boundary_dichotomy
    {R X : ℕ} (hXR : X ≤ R) :
    Nat.sqrt X < Nat.sqrt R ∨ Nat.sqrt X = Nat.sqrt R := by
  have hle := sqrt_le_root_of_endpoint_le hXR
  omega

end RHLean.Proof

import Mathlib
import RHLean.Analysis.MertensEnergyRHForward
import RHLean.Analysis.PrimeSieveCollapseIdentity
import RHLean.Proof.LowWheelCanonicalDefectReduction
import RHLean.Proof.LowWheelCanonicalSqrtDenseContraction

/-!
# Canonical root-downcross final seam

The orientation-split route exposes an ancestral Mertens transform, but that
quantity is not the primitive obstruction.  In the unsplit `S = A - T`
coordinates the complete smooth population `A_R` is already removed exactly by
the canonical low-wheel involution.  What survives is one signed adjacent
multiplicative root-downcross ledger:

`M(R^2 - 1) = M(R) - D_R`.

The same endpoint also has the compiled three-section description

`M(R^2 - 1) = A_R - Middle_R - Top_R`,

where the top block is deterministic and the middle block is the only
nontrivial post-root fresh-prime evolution.  Combining the two descriptions
therefore gives one simultaneous-coordinate seam for the same signed mass.

This file names the only new quantitative proposition needed at this seam:

`||D_R|| <= C * R`.

No estimate for `D_R` is proved here.  The rest of the file proves that this
single linear bound implies the square-prefix energy criterion and then the
repository's native formal Riemann hypothesis theorem.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic

/-- **Primitive final quantitative seam.**  The canonical adjacent root-downcross
ledger has uniformly linear signed mass.  This is deliberately stated on the
unsplit `S = A - T` residual rather than on either smooth orientation. -/
def SquareRootCanonicalDowncrossLinearBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 3 ≤ R →
      ‖lowWheelCanonicalDowncrossLedger R‖ ≤ C * (R : ℝ)

/-- The square-prefix jump from the lower Mertens state is exactly the negative
canonical downcross ledger. -/
theorem squarePrefixMertens_sub_mertens_eq_neg_canonicalDowncross
    (R : ℕ) (hR : 3 ≤ R) :
    squarePrefixMertens (R - 1) - mertensSummatory R =
      -lowWheelCanonicalDowncrossLedger R := by
  rw [squarePrefixMertens_eq_mertens_sub_canonicalDowncross R hR]
  ring

/-- Norm form of the primitive seam: no inequality or asymptotic input is used. -/
theorem norm_squarePrefixMertens_sub_mertens_eq_canonicalDowncross
    (R : ℕ) (hR : 3 ≤ R) :
    ‖squarePrefixMertens (R - 1) - mertensSummatory R‖ =
      ‖lowWheelCanonicalDowncrossLedger R‖ := by
  rw [squarePrefixMertens_sub_mertens_eq_neg_canonicalDowncross R hR]
  simp

/-- **Simultaneous-coordinate identity.**  The same downcross ledger is what is
left when the middle fresh-prime evolution and deterministic top block are read
against the complete smooth stopping state. -/
theorem canonicalDowncross_eq_lower_sub_smooth_add_middle_add_topCard
    (R : ℕ) (hR : 3 ≤ R) :
    lowWheelCanonicalDowncrossLedger R =
      mertensSummatory R - squareRootSmoothMass (R - 1) +
        squareRootMiddleMertensTail R +
          ((squareRootTopFibrePrimes R).card : ℂ) := by
  have hdown := squarePrefixMertens_eq_mertens_sub_canonicalDowncross R hR
  have hmiddle := squarePrefixMertens_eq_smooth_sub_middle_sub_topCard R hR
  calc
    lowWheelCanonicalDowncrossLedger R =
        mertensSummatory R - squarePrefixMertens (R - 1) := by
      rw [hdown]
      ring
    _ = mertensSummatory R -
          (squareRootSmoothMass (R - 1) -
            squareRootMiddleMertensTail R -
              ((squareRootTopFibrePrimes R).card : ℂ)) := by
      rw [hmiddle]
    _ = mertensSummatory R - squareRootSmoothMass (R - 1) +
          squareRootMiddleMertensTail R +
            ((squareRootTopFibrePrimes R).card : ℂ) := by
      ring

/-- A linear downcross bound immediately gives a linear square-prefix Mertens
bound, using only the trivial interval bound `|M(R)| <= R`. -/
theorem norm_squarePrefixMertens_le_of_canonicalDowncrossLinear
    {C : ℝ} (_hC : 0 ≤ C)
    (hdown : ∀ R : ℕ, 3 ≤ R →
      ‖lowWheelCanonicalDowncrossLedger R‖ ≤ C * (R : ℝ))
    {R : ℕ} (hR : 3 ≤ R) :
    ‖squarePrefixMertens (R - 1)‖ ≤ (C + 1) * (R : ℝ) := by
  have hMstep := norm_mertensSummatory_sub_le 0 R (Nat.zero_le R)
  have hM : ‖mertensSummatory R‖ ≤ (R : ℝ) := by
    simpa using hMstep
  rw [squarePrefixMertens_eq_mertens_sub_canonicalDowncross R hR]
  calc
    ‖mertensSummatory R - lowWheelCanonicalDowncrossLedger R‖ ≤
        ‖mertensSummatory R‖ + ‖lowWheelCanonicalDowncrossLedger R‖ :=
      norm_sub_le _ _
    _ ≤ (R : ℝ) + C * (R : ℝ) := add_le_add hM (hdown R hR)
    _ = (C + 1) * (R : ℝ) := by ring

/-- The primitive linear downcross seam supplies the repository's current
square-prefix pointwise energy criterion. -/
theorem squarePrefixCurrentPointwiseBounded_of_canonicalDowncrossLinear
    (hdown : SquareRootCanonicalDowncrossLinearBound) :
    SquarePrefixCurrentPointwiseBoundedStatement := by
  obtain ⟨C, hC, hD⟩ := hdown
  intro ε hε
  refine ⟨4 * (C + 1) ^ 2 + 9, by positivity, ?_⟩
  intro N hN
  by_cases hN1 : N = 1
  · subst N
    have hinterval :=
      norm_mertensSummatory_sub_le 0 (squarePrefixEndpoint 1)
        (Nat.zero_le (squarePrefixEndpoint 1))
    have hnorm : ‖squarePrefixMertens 1‖ ≤ 3 := by
      simpa [squarePrefixMertens, squarePrefixEndpoint] using hinterval
    have hsq : ‖squarePrefixMertens 1‖ ^ 2 ≤ 9 := by
      nlinarith [norm_nonneg (squarePrefixMertens 1)]
    have hcoef : 9 ≤ 4 * (C + 1) ^ 2 + 9 := by
      nlinarith [sq_nonneg (C + 1)]
    simpa using hsq.trans hcoef
  · have hN2 : 2 ≤ N := by omega
    have hR : 3 ≤ N + 1 := by omega
    have hlin :=
      norm_squarePrefixMertens_le_of_canonicalDowncrossLinear
        hC hD (R := N + 1) hR
    have hlinN :
        ‖squarePrefixMertens N‖ ≤
          (C + 1) * (((N + 1 : ℕ) : ℝ)) := by
      simpa using hlin
    have hC1 : 0 ≤ C + 1 := by linarith
    have hNplus : (((N + 1 : ℕ) : ℝ)) ≤ 2 * (N : ℝ) := by
      exact_mod_cast (by omega : N + 1 ≤ 2 * N)
    have hlin2 :
        ‖squarePrefixMertens N‖ ≤ 2 * (C + 1) * (N : ℝ) := by
      calc
        ‖squarePrefixMertens N‖ ≤
            (C + 1) * (((N + 1 : ℕ) : ℝ)) := hlinN
        _ ≤ (C + 1) * (2 * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hNplus hC1
        _ = 2 * (C + 1) * (N : ℝ) := by ring
    have hright : 0 ≤ 2 * (C + 1) * (N : ℝ) := by positivity
    have hsq :
        ‖squarePrefixMertens N‖ ^ 2 ≤
          (2 * (C + 1) * (N : ℝ)) ^ 2 := by
      nlinarith [norm_nonneg (squarePrefixMertens N)]
    have hsq' :
        ‖squarePrefixMertens N‖ ^ 2 ≤
          4 * (C + 1) ^ 2 * (N : ℝ) ^ 2 := by
      calc
        ‖squarePrefixMertens N‖ ^ 2 ≤
            (2 * (C + 1) * (N : ℝ)) ^ 2 := hsq
        _ = 4 * (C + 1) ^ 2 * (N : ℝ) ^ 2 := by ring
    have hbase : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hrpow :
        (N : ℝ) ^ 2 ≤ Real.rpow (N : ℝ) (2 + ε) := by
      have hmono :=
        Real.rpow_le_rpow_of_exponent_le hbase
          (by linarith : (2 : ℝ) ≤ 2 + ε)
      have h2 : Real.rpow (N : ℝ) (2 : ℝ) = (N : ℝ) ^ 2 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num]
        exact Real.rpow_natCast (N : ℝ) 2
      calc
        (N : ℝ) ^ 2 = Real.rpow (N : ℝ) (2 : ℝ) := h2.symm
        _ ≤ Real.rpow (N : ℝ) (2 + ε) := hmono
    have hsmallCoeff : 0 ≤ 4 * (C + 1) ^ 2 := by positivity
    have hcoeff :
        4 * (C + 1) ^ 2 ≤ 4 * (C + 1) ^ 2 + 9 := by linarith
    calc
      ‖squarePrefixMertens N‖ ^ 2 ≤
          4 * (C + 1) ^ 2 * (N : ℝ) ^ 2 := hsq'
      _ ≤ 4 * (C + 1) ^ 2 * Real.rpow (N : ℝ) (2 + ε) :=
        mul_le_mul_of_nonneg_left hrpow hsmallCoeff
      _ ≤ (4 * (C + 1) ^ 2 + 9) *
          Real.rpow (N : ℝ) (2 + ε) :=
        mul_le_mul_of_nonneg_right hcoeff
          (Real.rpow_nonneg (by positivity) _)

/-- The primitive downcross bound therefore gives the exact square-prefix energy
criterion already consumed by the analytic bridge. -/
theorem squarePrefixEnergyBounded_of_canonicalDowncrossLinear
    (hdown : SquareRootCanonicalDowncrossLinearBound) :
    SquarePrefixEnergyBoundedStatement := by
  exact (squarePrefixEnergyBounded_iff_currentPointwise).2
    (squarePrefixCurrentPointwiseBounded_of_canonicalDowncrossLinear hdown)

/-- **Formal closure.**  A uniform linear bound on the one canonical root-downcross
ledger implies the repository's native formal Riemann hypothesis theorem. -/
theorem riemannHypothesis_of_canonicalDowncrossLinear
    (hdown : SquareRootCanonicalDowncrossLinearBound) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_mertensEnergy
  apply mertensEnergyBounded_of_squarePrefixEnergyBounded
  exact squarePrefixEnergyBounded_of_canonicalDowncrossLinear hdown

/-! ## First-jump residual in canonical prime-sieve coordinates

After the square-root tail-empty contraction, the first-jump residual is a
literal high-prime Mertens band.  The following exact identities place that band
in the repository's existing `primeSieveMertensPrimeTail` and
`primeSieveReciprocalMertensSignedSum` coordinates.  No norm is taken.

The finite quotient reindexing is unconditional: `Nat.sqrt X < s` is not a
hypothesis here.  Root equality matters only for later high-source/all-plus
interpretations, not for this coordinate conversion.
-/

/-- Literal Mertens column carried by primes in the frozen band `(s,K]`. -/
def firstJumpPrimeSieveMertensBand (s K X : ℕ) : ℂ :=
  ∑ p ∈ frozenPrimeUniverseHighPrimeSet s K,
    mertensSummatory (X / p)

/-- The frozen high-prime band is exactly the prime-filtered integer interval. -/
theorem frozenPrimeUniverseHighPrimeSet_eq_Ioc_filter_prime
    (s K : ℕ) :
    frozenPrimeUniverseHighPrimeSet s K =
      (Finset.Ioc s K).filter Nat.Prime := by
  ext p
  simp [mem_frozenPrimeUniverseHighPrimeSet, and_comm, and_assoc]

/-- Interval form of the literal Mertens band. -/
theorem firstJumpPrimeSieveMertensBand_eq_Ioc
    (s K X : ℕ) :
    firstJumpPrimeSieveMertensBand s K X =
      ∑ p ∈ Finset.Ioc s K,
        if p.Prime then mertensSummatory (X / p) else 0 := by
  unfold firstJumpPrimeSieveMertensBand
  rw [frozenPrimeUniverseHighPrimeSet_eq_Ioc_filter_prime]
  rw [Finset.sum_filter]

/-- **Prime band = difference of repository prime tails.**
This includes `K > X`; primes beyond `X` have quotient zero and vanish. -/
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

/-- The same prime band in the quotient-reindexed reciprocal prime-count
coordinate.  No strict square-root assumption is needed for this finite Fubini
identity. -/
theorem firstJumpPrimeSieveMertensBand_eq_reciprocalSignedSum_sub
    {s K X : ℕ} (hsK : s ≤ K) :
    firstJumpPrimeSieveMertensBand s K X =
      primeSieveReciprocalMertensSignedSum s X -
        primeSieveReciprocalMertensSignedSum K X := by
  rw [firstJumpPrimeSieveMertensBand_eq_tail_sub_tail hsK]
  rw [primeSieveReciprocalMertensSignedSum_eq_mertensPrimeTail,
    primeSieveReciprocalMertensSignedSum_eq_mertensPrimeTail]

/-- Cast the integer first-jump residual without changing its signed structure. -/
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
  unfold firstJumpPrimeSieveMertensBand
  rw [Finset.sum_sub_distrib]
  simpa only [mertensSummatoryInt_cast, neg_sub] using hcast

/-- The exact signed reciprocal-Mertens object left after the geometric
contractions.  No norm is built into this definition. -/
def firstJumpReciprocalMertensDifference
    (s K A B : ℕ) : ℂ :=
  (primeSieveReciprocalMertensSignedSum s A -
      primeSieveReciprocalMertensSignedSum K A) -
    (primeSieveReciprocalMertensSignedSum s B -
      primeSieveReciprocalMertensSignedSum K B)

/-- **#569 -> reciprocal-prime-count/Mertens coordinate.** -/
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

/-- Endpoints `X <= R` have no larger square root. -/
theorem sqrt_le_root_of_endpoint_le
    {R X : ℕ} (hXR : X ≤ R) :
    Nat.sqrt X ≤ Nat.sqrt R :=
  Nat.sqrt_le_sqrt hXR

/-- The strict/equality root edge is explicit.  The reciprocal reindex above
works in both cases; this dichotomy is only needed by later high-source APIs. -/
theorem sqrt_endpoint_root_boundary_dichotomy
    {R X : ℕ} (hXR : X ≤ R) :
    Nat.sqrt X < Nat.sqrt R ∨ Nat.sqrt X = Nat.sqrt R := by
  have hle := sqrt_le_root_of_endpoint_le hXR
  omega

end RHLean.Proof

import RHLean.Analysis.PrimeSieveCollapseIdentity
import RHLean.Proof.CanonicalGapAncestryQuadraticClosure
import RHLean.Proof.LowPrimeCombinedBornHighFirstFailure
import RHLean.Proof.LowPrimeCombinedBornHighTransition
import RHLean.Proof.LowPrimeCompletedPartnerWindowFold
import RHLean.Proof.LowWheelCanonicalSqrtDenseContraction
import RHLean.Proof.SquareRootAncestryParentFibres
import RHLean.Proof.SquareRootBornPostTailLowPrimeCollapse
import RHLean.Proof.SquareRootBornPostTailLowPrimeRemainder
import RHLean.Proof.SquareRootLowPrimeSequentialDissipation
import RHLean.Proof.SquareRootLowPrimeTerminalHighPrimeIntegration
import RHLean.Proof.SquareRootLowPrimeSmoothTransportRecoupling
import RHLean.Proof.SquareRootLowPrimeMatchedCoreMertensObstruction
import RHLean.Proof.SquareRootMertensMiddleTracking
import RHLean.Proof.SquareRootMertensPositiveTracking
import RHLean.Proof.TerminalMertensForward

/-!
# Axiom footprint of the terminal reduction

`scripts/audit_assumptions.sh` greps the sources for unfinished-proof placeholders and
for declared opaque constants. That is necessary but not sufficient: it inspects text,
not the kernel's record of what a proof actually depends on, and it cannot see anything
inherited through an import.

This module closes that gap for the theorems that carry the reduction to RH. Each
`#print axioms` below asks the kernel directly, while `#guard_msgs` makes the expected
answer part of the build: an added dependency changes the message and fails compilation.
The expected answer for every theorem is exactly

```text
[propext, Classical.choice, Quot.sound]
```

the three standard axioms of Lean's logic used throughout Mathlib. Any other name in
these lists -- in particular `sorryAx`, which is what an unfinished proof compiles to,
or any project-declared axiom -- fails this module and invalidates the corresponding
reduction claim.

A clean axiom list is necessary but does not by itself certify that a theorem has no
ordinary hypothesis representing an external criterion.  The historical equivalences
below still accept `ClassicalMertensRHCriterion` as an ordinary theorem argument, so
that conditionality remains visible in their signatures even though it is absent from
`#print axioms`.  The new guarded theorem
`TerminalMertensForward.riemannHypothesis_of_squarePrefixEnergy` is different: its only
hypothesis is the square-prefix energy estimate itself.  The forward Mertens-to-RH
criterion is constructed internally by `MertensEnergyRHForward`, so this is the terminal
unconditional analytic consumer for the arithmetic project.

The square-root legal-ancestry Gram reduction is imported here as well so the ordinary
root build type-checks its exact endpoint and parent-fibre identities. Its new analytic
amplification statement remains an explicitly open proposition and is not added to the
axiom guards below.

The terminal high-prime integration is imported here for the same reason: the ordinary
root build type-checks the exact #497 high-prime splice on the canonical processed
terminal frontier.

The smooth/transport recoupling is also imported here.  It proves that the terminal
running imbalance is the historical matched born-smooth/transport residual minus only
the partial crossing packet and the near-root rectangle, whose combined norm is at
most `R + K`.  It also proves that a `3 R sqrt(K)` bound for that matched residual
implies the exact `25 R^2 K` terminal-square bound and hence the signed response-child
energy decrement through the pre-existing exact telescope.  The `3 R sqrt(K)` matched
bound itself is not proved here: that signed `BornSmooth - Transport` / `A - T`
correlation is the remaining arithmetic input.  In particular, no independent
low-prime frontier estimate is introduced as a new analytic obligation.

The final low-prime branch now exposes the same arithmetic input in two exact Mertens
tracking coordinates.  First, the matched core is `M(R^2-1)` minus one literal
positive-orientation middle source mass.  Second, and more economically,
`M(R^2-1) - PositiveSmooth(R)` is exactly the matched channel itself.  The corresponding
`O(R)` tracking estimates remain explicit theorem hypotheses.  The guards below certify
that the exact identities and the implications *from* those hypotheses have no hidden
project axiom.
-/

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

namespace TerminalAxiomAudit

-- The direct terminal arithmetic-to-RH consumer.  Unlike the historical
-- equivalences below, its only ordinary hypothesis is the square-prefix energy bound.
/--
info: 'RHLean.Proof.TerminalMertensForward.riemannHypothesis_of_squarePrefixEnergy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Proof.TerminalMertensForward.riemannHypothesis_of_squarePrefixEnergy

-- The terminal equivalence: the projected-renewal quadratic bound is RH, given the
-- classical Mertens criterion.
/--
info: 'RHLean.Proof.CanonicalGapAncestryQuadraticClosure.projectedRenewalQuadraticBounded_iff_riemannHypothesis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  RHLean.Proof.CanonicalGapAncestryQuadraticClosure.projectedRenewalQuadraticBounded_iff_riemannHypothesis

-- The algebraic half of the chain: the projected-renewal bound is exactly canonical
-- (HS). This one is unconditional.
/--
info: 'RHLean.Proof.CanonicalGapAncestryQuadraticClosure.projectedRenewalQuadraticBounded_iff_canonicalHigh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  RHLean.Proof.CanonicalGapAncestryQuadraticClosure.projectedRenewalQuadraticBounded_iff_canonicalHigh

-- The analytic half: canonical (HS) is RH, given the criterion.
/--
info: 'RHLean.Proof.canonicalHighUniformLocalBounded_iff_riemannHypothesis_realized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Proof.canonicalHighUniformLocalBounded_iff_riemannHypothesis_realized

-- Exact source-form obstruction: no estimate is used here.
/--
info: 'RHLean.Proof.squareRootLowPrimeMatchedCore_eq_mertens_sub_middleSourceMass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Proof.squareRootLowPrimeMatchedCore_eq_mertens_sub_middleSourceMass

-- Conditional terminal implication from the explicit Mertens/middle tracking
-- proposition.  The tracking proposition is an ordinary theorem argument, not an axiom.
/--
info: 'RHLean.Proof.abs_squareRootLowPrimeRunningImbalanceReal_le_of_mertensMiddleTracking' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Proof.abs_squareRootLowPrimeRunningImbalanceReal_le_of_mertensMiddleTracking

-- Shortest conditional endpoint: M(R^2-1) - PositiveSmooth(R) is exactly the matched
-- channel, so this route incurs no seven-strip loss.
/--
info: 'RHLean.Proof.abs_squareRootLowPrimeRunningImbalanceReal_le_of_mertensPositiveTracking' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RHLean.Proof.abs_squareRootLowPrimeRunningImbalanceReal_le_of_mertensPositiveTracking

end TerminalAxiomAudit

open RHLean.Analysis
open RHLean.Arithmetic

/-! ## First-jump residual in canonical prime-sieve coordinates

After the #569 tail-empty contraction, the first-jump residual is a literal
high-prime Mertens band.  The finite quotient reindex below is unconditional:
root equality matters only if a later theorem invokes the separate high-source
interpretation, not for this coordinate conversion.
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

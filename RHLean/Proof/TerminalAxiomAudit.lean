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

end RHLean.Proof

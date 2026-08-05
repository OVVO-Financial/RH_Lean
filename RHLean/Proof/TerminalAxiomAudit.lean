import RHLean.Proof.CanonicalGapAncestryQuadraticClosure

/-!
# Axiom footprint of the terminal reduction

`scripts/audit_assumptions.sh` greps the sources for unfinished-proof placeholders and
for declared opaque constants.  That is necessary but not sufficient: it inspects text,
not the kernel's record of what a proof actually depends on, and it cannot see anything
inherited through an import.

This module closes that gap for the theorems that carry the reduction to RH.  Each
`#print axioms` below asks the kernel directly, and its answer appears in the build
log.  The expected answer for every one of them is exactly

```text
[propext, Classical.choice, Quot.sound]
```

the three standard axioms of Lean's logic, which Mathlib assumes throughout.  As of
the run recorded in this module's history, all three print exactly that list.  Any
other name appearing in these lists -- in particular `sorryAx`, which is what an
unfinished proof compiles to, or any project-declared axiom -- means the corresponding
statement is not proved and the reduction claim must be withdrawn.

Note what this does **not** certify.  These are equivalences and implications, not
proofs of their left-hand sides.  `ProjectedRenewalQuadraticBoundedStatement` is an
open analytic estimate; it is a hypothesis here and nothing in the project proves it.
Likewise `ClassicalMertensRHCriterion` is a structure taken as an argument, not an
axiom, which is why it does not appear in these lists -- the reduction is conditional
on being supplied with it.
-/

namespace RHLean.Proof

namespace TerminalAxiomAudit

-- The terminal equivalence: the projected-renewal quadratic bound is RH, given the
-- classical Mertens criterion.
#print axioms
  RHLean.Proof.CanonicalGapAncestryQuadraticClosure.projectedRenewalQuadraticBounded_iff_riemannHypothesis

-- The algebraic half of the chain: the projected-renewal bound is exactly canonical
-- (HS).  This one is unconditional.
#print axioms
  RHLean.Proof.CanonicalGapAncestryQuadraticClosure.projectedRenewalQuadraticBounded_iff_canonicalHigh

-- The analytic half: canonical (HS) is RH, given the criterion.
#print axioms RHLean.Proof.canonicalHighUniformLocalBounded_iff_riemannHypothesis_realized

end TerminalAxiomAudit

end RHLean.Proof

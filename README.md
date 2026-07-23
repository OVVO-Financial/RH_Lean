# RH_Lean

Lean 4 formalization of the square-prefix Möbius program.

This repository is the focused formalization initiative. It is intentionally developed through small, reviewable pull requests. Only fully proved, machine-checked statements belong in the compiled Lean library.

## Verification

Every pull request runs:

```bash
bash scripts/audit_assumptions.sh
lake build RHLean --wfail
```

`RH_Lean` is currently a library-only Lake project, so CI does not invoke `lake test` until a dedicated test runner is added.

The source audit rejects `sorry`, `admit`, axioms, and opaque constants. Open analytic inputs remain documented project obligations outside the compiled theorem graph until they are proved.

## Formalization invariants

No pull request may introduce `sorry`, `admit`, a new axiom, an opaque constant standing in for a theorem, a weakened statement, changed indexing, or a circular assumption of RH or an equivalent result.

## Planned PR sequence

1. Project scaffold, CI, Fermat coordinates, and fixed-packet identities.
2. Exact Möbius doubling: `μ (2*a) = -μ a` for odd `a`.
3. Exact four-slot compression `(+,-,+,0)` and packet/cell equivalence.
4. Universal prime-3 activation and the deterministic three-cycle.
5. Squared complex recovery, cofactor parabolas, conformal Jacobian, and `2ab` lifetime.
6. Low-height spacing and incidence bounds.
7. Prefix kernels, directional Gram identities, and uniform closure.
8. Prove the actual-start signed-frame theorem and only then formalize the RH bridge.

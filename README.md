# RH_Lean

Lean 4 formalization of the square-prefix Möbius program.

This repository is the focused formalization initiative. It is intentionally developed through small, reviewable pull requests. Machine-checked theorems are kept separate from the explicitly isolated open actual-start signed-frame input.

## Verification

Every pull request runs:

```bash
bash scripts/audit_assumptions.sh
lake build RHLean --wfail
```

`RH_Lean` is currently a library-only Lake project, so CI does not invoke `lake test` until a dedicated test runner is added.

The source audit rejects `sorry` and `admit`. Axioms are rejected everywhere except the dedicated file `RHLean/Open/ActualStartFrame.lean`, where the remaining analytic input will be stated explicitly and never hidden inside definitions.

## Planned PR sequence

1. Project scaffold, CI, Fermat coordinates, and fixed-packet identities.
2. Exact Möbius doubling: `μ (2*a) = -μ a` for odd `a`.
3. Exact four-slot compression `(+,-,+,0)` and packet/cell equivalence.
4. Universal prime-3 activation and the deterministic three-cycle.
5. Squared complex recovery, cofactor parabolas, conformal Jacobian, and `2ab` lifetime.
6. Low-height spacing and incidence bounds.
7. Prefix kernels, directional Gram identities, and uniform closure.
8. Isolated actual-start signed-frame statement and conditional RH bridge.

No pull request may silently strengthen an open statement into a theorem.

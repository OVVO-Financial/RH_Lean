# RH_Lean

Lean 4 formalization of the square-prefix Möbius program.

This repository is the focused formalization initiative. It is intentionally developed through small, reviewable pull requests. Only fully proved, machine-checked statements belong in the compiled Lean library.

The project now has two distinct structural branches that meet only at the final analytic closure:

- the exact Möbius/cell-mask branch;
- the quadratic prime-phase resonance branch over modulus `2r`.

See [`ARCHITECTURE.md`](ARCHITECTURE.md) for the full dependency graph, theorem targets, namespaces, and revised PR sequence.

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

The prime-3 cell-mask energy and the prime-3 quadratic phase factor are different mathematical objects. They must remain in separate namespaces and modules:

```text
RHLean.CellMask
RHLean.QuadraticPrimePhase
```

In particular, a cell-mask energy factor such as `1/9` may not be used as a bound for the coherent quadratic prime-phase factor at `r = 3`.

## Revised formalization sequence

Completed exact foundations:

1. Project scaffold, CI, Fermat coordinates, and fixed-packet identities.
2. Exact Möbius doubling: `μ (2*a) = -μ a` for odd `a`.
3. Exact four-slot compression `(+,-,+,0)`.
4. Universal prime-3 activation and deterministic three-cycle.

Current and next focused PRs:

5. Squared complex recovery.
6. Prime-square congruences, culminating in `q^2 ≡ 1 (mod 24)` for primes `q > 3`.
7. Quadratic phase periodicity modulo `2r` and the exact shift-by-`r` sign law.
8. Corrected reduced quadratic Gauss factor over the units of `ZMod (2*r)`.
9. Exact modulus-6 and modulus-24 resonance theorems, including norm-one coherence at `(a,r)=(1,3)`.
10. Cofactor parabolas, conformal Jacobian, and `2ab` lifetime geometry.
11. Type-separated prime-3 cell-mask mean-energy theorem.
12. Resonant/nonresonant decomposition.
13. Explicit resonant cancellation across Möbius-weighted cofactor channels.
14. Low-height spacing and incidence bounds.
15. Prefix kernels, directional Gram identities, and uniform closure.
16. Actual-start signed-frame theorem.
17. RH bridge only after every unconditional obligation is discharged.

The corrected analytic architecture is:

```text
explicit resonant cancellation
+
nonresonant frame contraction
→
uniform cubic residual bound.
```

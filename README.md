# RH_Lean

Lean 4 formalization of the square-prefix Möbius program.

This repository is the focused formalization initiative. It is intentionally developed through small, reviewable pull requests. Only fully proved, machine-checked statements belong in the compiled Lean library.

The project has distinct structural branches that meet only at the final analytic closure:

- the exact Möbius/cell-mask branch;
- the quadratic prime-phase resonance branch over modulus `2r`;
- the exact factor-geometry/cofactor-channel branch;
- the full signed Gram and block-contraction closure branch.

See [`ARCHITECTURE.md`](ARCHITECTURE.md) for the arithmetic and resonance dependency graph, and [`SIGNED_GRAM_ARCHITECTURE.md`](SIGNED_GRAM_ARCHITECTURE.md) for the cross-shell, projection, leakage, and Lyapunov closure architecture.

## Verification

Every pull request runs:

```bash
bash scripts/audit_assumptions.sh
lake build RHLean --wfail
```

`RH_Lean` is currently a library-only Lake project, so CI does not invoke `lake test` until a dedicated test runner is added.

The source audit rejects `sorry`, `admit`, axioms, and opaque constants. Open analytic inputs remain documented project obligations outside the compiled theorem graph until they are proved.

Finite-range numerical observations are not ordinary theorems. They must enter only through a certified-computation layer whose checker is proved correct in Lean.

## Formalization invariants

No pull request may introduce `sorry`, `admit`, a new axiom, an opaque constant standing in for a theorem, a weakened statement, changed indexing, or a circular assumption of RH or an equivalent result.

The prime-3 cell-mask energy and the prime-3 quadratic phase factor are different mathematical objects. They must remain in separate namespaces and modules:

```text
RHLean.CellMask
RHLean.QuadraticPrimePhase
```

In particular, a cell-mask energy factor such as `1/9` may not be used as a bound for the coherent quadratic prime-phase factor at `r = 3`.

The high sector must not be formalized as a sum of independently small positive shell energies. The target is the full signed Gram form, retaining cross-shell, cross-cofactor, resonant/nonresonant, and denominator-mode terms.

A theorem-predicted rank-one subtraction is not an orthogonal projection unless equality of the coefficients is separately proved. Pythagorean identities may be used only for genuinely orthogonal projections.

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
12. Exact mod-40 reduced square classes: `q^2 ≡ 1` or `9 (mod 40)` for primes `q > 5`.
13. Exact height-shell recombination and full signed Gram identity.
14. Orthogonal projection residual and energy decomposition, separated from theorem-predicted subtraction.
15. Scale-dependent major-arc projection with corrected modulus-`2r` modes.
16. Explicit resonant/nonresonant leakage block operator.
17. Abstract affine block contraction in a weighted Lyapunov norm with forcing.
18. Certified finite-range certificate checker.
19. Explicit resonant cancellation across Möbius-weighted cofactor channels.
20. Low-height spacing and incidence bounds.
21. Joint Gram control indexed by height shell, cofactor block, and denominator mode.
22. Actual-start signed-frame theorem.
23. RH bridge only after every unconditional obligation is discharged.

The corrected analytic architecture is:

```text
exact Möbius and factor geometry
+
correct modulus-2r resonant phase model
+
scale-dependent major-arc projection
+
full signed shell/cofactor/mode Gram identity
+
explicit resonant/nonresonant leakage operator
+
weighted affine block contraction with forcing
→
uniform full residual bound
→
actual-start signed-frame theorem
→
RH bridge only after unconditional closure.
```

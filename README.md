# RH_Lean

Lean 4 formalization of the square-prefix Möbius program.

This repository is the focused formalization initiative. It is intentionally developed through small, reviewable pull requests. Only fully proved, machine-checked statements belong in the compiled Lean library.

The project has distinct structural branches that meet only at the final analytic closure:

- the exact Möbius/cell-mask branch;
- the quadratic prime-phase resonance branch over modulus `2r`;
- the exact factor-geometry/cofactor-channel branch;
- the full signed Gram and block-contraction closure branch.

See [`FORMALIZATION_SEQUENCE.md`](FORMALIZATION_SEQUENCE.md) for the canonical compiled inventory, current checkpoint, and implementation order. See [`ARCHITECTURE.md`](ARCHITECTURE.md) for the arithmetic and resonance dependency graph, and [`SIGNED_GRAM_ARCHITECTURE.md`](SIGNED_GRAM_ARCHITECTURE.md) for the cross-shell, projection, leakage, and Lyapunov closure architecture.

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

## Current status

The compiled library now contains:

- exact Möbius doubling, four-slot compression, and universal prime-3 activation;
- prime-square congruences modulo `24` and the exact `1`/`9` dichotomy modulo `40`;
- corrected modulus-`2r` quadratic numerator periodicity, exponent congruence, and the exact shift-by-`r` arithmetic dichotomy;
- Fermat midpoint/half-gap coordinates, squared complex recovery, exact cofactor parabolas, conformal Jacobian identities, and the two-to-one complex-square fiber theorem;
- fixed-packet kernel foundations.

The next dependency is the complex quadratic phase API and exact additive-character sign law. The reduced Gauss factor, exact small-modulus resonance, signed Gram machinery, leakage operator, Lyapunov closure, certified computation layer, and RH bridge remain open obligations.

The numbered implementation order is maintained only in [`FORMALIZATION_SEQUENCE.md`](FORMALIZATION_SEQUENCE.md).

## Closure architecture

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

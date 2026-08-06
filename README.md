# RH_Lean

Lean 4 formalization of the square-prefix Möbius program.

This repository is the focused formalization initiative. It is intentionally developed through small, reviewable pull requests. Only fully proved, machine-checked statements belong in the compiled Lean library.

The project has distinct structural branches that meet only at the final analytic closure:

- the exact Möbius/cell-mask branch;
- the quadratic prime-phase resonance branch over modulus `2r`;
- the exact factor-geometry/cofactor-channel branch;
- the full signed Gram and block-contraction closure branch.

See [`FORMALIZATION_SEQUENCE.md`](FORMALIZATION_SEQUENCE.md) for the canonical compiled inventory, current checkpoint, and implementation order. See [`ARCHITECTURE.md`](ARCHITECTURE.md) for the arithmetic and resonance dependency graph, and [`SIGNED_GRAM_ARCHITECTURE.md`](SIGNED_GRAM_ARCHITECTURE.md) for the cross-shell, projection, leakage, and Lyapunov closure architecture.

The exploratory note [`LEAST_PRIME_PARABOLA_ENDPOINT_CUBES.md`](LEAST_PRIME_PARABOLA_ENDPOINT_CUBES.md) records the exact first-hit least-prime parabola, double-endpoint core, and truncated Boolean-cube decompositions. These identities are not yet part of the compiled Lean theorem graph. The companion script [`experiments/least_prime_endpoint_cubes.py`](experiments/least_prime_endpoint_cubes.py) is diagnostic only and does not replace certified computation.

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

**The formal reduction chain is complete.** For every `Λ ≥ 0`, `RH_Lean` proves the unconditional structural equivalence

```text
ProjectedRenewalQuadraticBoundedStatement Λ
  ↔ CanonicalHighUniformLocalBoundedStatement Λ.
```

Given an ordinary theorem argument

```text
criterion : ClassicalMertensRHCriterion,
```

the repository also proves

```text
CanonicalHighUniformLocalBoundedStatement Λ
  ↔ RiemannHypothesisStatement,
```

and therefore the terminal theorem

```text
ProjectedRenewalQuadraticBoundedStatement Λ
  ↔ RiemannHypothesisStatement.
```

These results are in
[`RHLean/Proof/CanonicalGapAncestryQuadraticClosure.lean`](RHLean/Proof/CanonicalGapAncestryQuadraticClosure.lean).
`RiemannHypothesisStatement` is Mathlib's `RiemannHypothesis`. The three terminal
carrying theorems depend on exactly `[propext, Classical.choice, Quot.sound]` and
nothing else. The kernel output is regression-checked with `#guard_msgs` in
[`RHLean/Proof/TerminalAxiomAudit.lean`](RHLean/Proof/TerminalAxiomAudit.lean), so an
additional axiom dependency fails the build.

### The two remaining obligations

Being axiom-clean is not the same as being unconditional. Two mathematical obligations remain visible:

1. **`ProjectedRenewalQuadraticBoundedStatement`** is the open analytic proposition.
   Once `ClassicalMertensRHCriterion` is supplied, the proved equivalence shows that
   establishing this proposition establishes RH. Nothing in this repository proves it
   or claims to.
2. **`ClassicalMertensRHCriterion`** is declared once in
   [`RHLean/Analysis/SquarePrefixMertensBridge.lean`](RHLean/Analysis/SquarePrefixMertensBridge.lean)
   and is passed explicitly through the theorem signatures that use the classical
   Mertens/RH equivalence. It is never constructed in the repository. Formalizing this
   known classical theorem would eliminate the externally supplied theorem argument
   and make the reduction chain end-to-end; it would not prove or weaken the remaining
   analytic proposition.

### `Λ = 0` is the canonical terminal formulation

The theorem holds for every `Λ ≥ 0`, so changing `Λ` does not change the logical
strength of the terminal proposition. The finite diagnostic
[`scripts/TwoAnchorSlackCoverage/terminal_lambda_dependence.c`](scripts/TwoAnchorSlackCoverage/terminal_lambda_dependence.c)
finds no sustained gain from increasing `Λ`: the values for `Λ = 0, 1, 2` are
essentially flat with small nonmonotone variation, while `Λ = 5, 10, 25` are materially
worse on the tested windows. This is numerical evidence, not an asymptotic theorem.

The structural reason for preferring `Λ = 0` is that
`S^high = S_total − S^low`, while the low-band counting theorem permits a prefix of
size `O(Λn)`. Removing more of an already controlled low band can therefore introduce
rather than remove a coherent drift. With no observed benefit and the simplest
statement at `Λ = 0`, that endpoint is the canonical formulation for future work.
There the proposition is the square-endpoint local energy estimate

```text
Σ_{h<H} |M((N+h+1)² − 1)|² ≪_ε H·N^{2+ε}.
```

The proved square-prefix bridge identifies this formulation with the classical Mertens
criterion at the level required for the terminal equivalence; the displayed estimate
should not be read as a separately proved pointwise bound. See route 7 in
[`RESEARCH_ROUTE_REGISTRY.md`](RESEARCH_ROUTE_REGISTRY.md).

### Priorities

Publication of the completed reduction; formalization of
`ClassicalMertensRHCriterion`; and preservation of the negative experimental registry,
which records seven closed routes and the finite diagnostics that closed them. A new
route requires a mechanism with a falsifiable numerical prediction differing from
those seven — repackaging the same cross-term cancellation, sector subtraction, or
prime-pair obstruction under another decomposition does not qualify.

### Compiled inventory

The compiled library also contains:

- exact Möbius doubling, four-slot compression, and universal prime-3 activation;
- prime-square congruences modulo `24` and the exact `1`/`9` dichotomy modulo `40`;
- corrected modulus-`2r` quadratic numerator periodicity, exponent congruence, and the exact shift-by-`r` arithmetic dichotomy;
- Fermat midpoint/half-gap coordinates, squared complex recovery, exact cofactor parabolas, conformal Jacobian identities, and the two-to-one complex-square fiber theorem;
- fixed-packet kernel foundations.

This inventory predates the closure above and is no longer the frontier; see
[`FORMALIZATION_SEQUENCE.md`](FORMALIZATION_SEQUENCE.md) for the current compiled
list. In particular the signed Gram machinery and the RH bridge, listed here as open
in earlier revisions, are complete — the bridge is the equivalence recorded at the top
of this section.

What remains open is stated above: the analytic proposition and the formalization of
`ClassicalMertensRHCriterion`. Separately, the certified-computation layer described
under **Verification** is still open, so every finite-range measurement in
[`scripts/`](scripts/) — including those that closed the routes in the registry — is
diagnostic only and carries no theorem status.

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

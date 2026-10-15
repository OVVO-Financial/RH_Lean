# Direct Mertens exponent-to-zero-strip formalization

User-directed PR: [#948](https://github.com/OVVO-Financial/RH_Lean/pull/948).
Baseline: `2ad3ee9a980cd73995a481cb9b2a9f58ea955108`, Lean 4.24.0.
Namespace: `RHLean.Analysis.MertensExponent`.

## Scope

This is an arbitrary-exponent **forward** analytic map on the original
`mertensSummatory` / `mertensStep` definitions, not a new number-theoretic
cancellation bound. Compilation status is the actual PR Actions result at its
current head; a source declaration is not certified before that check succeeds.
The canonical VF target, finite A/C, and RH are not closed by these changes.

## Independent arithmetic definitions

`MertensPowerBound a` means there exists a real constant `C >= 0` such that
`norm (M n) <= C * n^a` for every positive integer `n`.
`MertensGrowthAtMost a` means `MertensPowerBound (a + epsilon)` for every
`epsilon > 0`. The constant may depend on epsilon.

`mertensGrowthExponent` is the infimum of **nonnegative** admissible power
exponents. The set is nonempty because the elementary triangle inequality
proves `norm (M n) <= n`, with constant exactly 1. Bounds are monotone in the
exponent. For every `a >= 0`, the envelope module proves

```text
MertensGrowthAtMost a <-> mertensGrowthExponent <= a.
```

No bound at the exact infimum is asserted.

The logarithmic module proves the exact **integer-scale** identification

```text
limsup_{n -> infinity} log(max(1, norm(M n))) / log(n)
  = mertensGrowthExponent.
```

This is not a definition through zeta zeros. It follows from the actual
arithmetic linear bound, monotonicity of logarithms, absorption of a constant
by any positive exponent increase, and absorption of a finite initial segment
into the multiplicative constant. A separate real-variable limsup theorem for
the floor-step function is not included; the implemented limsup runs over n.

## Forward analytic chain

1. The classical Abel identity is established unconditionally using the
   exponent-one bound and the genuine Mobius Dirichlet series.
2. A power bound at `a >= 0` gives holomorphy of the actual Mertens Mellin
   continuation for `Re(s) > a`.
3. The identity theorem propagates `zeta(s) * F(s) = 1` into that half-plane,
   explicitly excluding the zeta pole `s = 1`.
4. This rules out zeta zeros to the right of `a`.
5. The completed-zeta functional equation reflects each nontrivial zero.

`strip_of_growthAtMost` therefore proves, for `a >= 0`,

```text
MertensGrowthAtMost a ->
  forall rho, NontrivialZetaZero rho -> 1-a <= Re(rho) <= a.
```

`strip_at_growthExponent` proves both walls for the independently defined
arithmetic infimum itself, without an endpoint-attainment assumption.
`strip_at_logLimsup` expresses the same enclosure using the literal logarithmic
limsup. The left-zero contrapositive explicitly uses the opposite exponent
`1 - Re(rho)`, not `Re(rho)`.

## Independent zeta coordinate

`zeroRealParts` is defined from actual zeros of `riemannZeta` in the open
critical strip. `zetaRightmostRealPart` is its supremum. Given explicit
nonemptiness of that zero set, the diagnostics module proves

```text
zetaRightmostRealPart <= mertensGrowthExponent
ZerosInSymmetricStrip a <-> zetaRightmostRealPart <= a.
```

The assumption of a nontrivial zero is visible in the relevant declarations;
no empirical zero or external existence theorem is inserted as an axiom.
The pointwise strip theorem needs no global nonemptiness premise.

## Endpoint and quantifier regressions

The exact finite arithmetic `M(5) = -2` refutes the unit exponent-zero envelope.
This does **not** refute an arbitrary constant envelope merely from that one
sample. Every finite prefix admits a constant envelope (`C = N` suffices for
`n <= N`), so finite census evidence alone is not a global big-O contradiction.

The correct negation of epsilon-loss control is

```text
not (MertensGrowthAtMost a) <->
  exists epsilon > 0, not (MertensPowerBound (a + epsilon)).
```

It is **some** positive epsilon, not all positive epsilons. The linear cone
already guarantees sufficiently large exponents work.

Acceptance examples include exponent 1/2, exponent 7/8 giving the symmetric
1/8 wall, a hypothetical zero at 1/16 ruling out the 7/8 power bound, and
incompatibility of exponent-level 1/4 control with a supplied nontrivial zero.

## Explicitly not proved here

The reverse Perron/Littlewood implication

```text
ZerosInSymmetricStrip a -> MertensGrowthAtMost a
```

is not assumed, exported as a theorem, or hidden in a typeclass. Consequently
`mertensGrowthExponent = zetaRightmostRealPart` is **not** a result of this PR.
The remaining analytic work is reciprocal-zeta control on interior vertical
lines of a zero-free region and an appropriately quantified inversion argument.
No unconditional seven-eighths estimate or numerical existence of a zeta zero
is newly claimed.

## Verification and source map

- `MERTENS_EXPONENT_ENVELOPES.lean`: actual arithmetic envelopes and infimum.
- `MERTENS_EXPONENT_STRIP_MAP.lean`: unconditional classical identity, conditional
  analytic continuation, reflection, pointwise map and contrapositives.
- `MERTENS_EXPONENT_DIAGNOSTICS.lean`: exact finite witness and independent zero
  supremum coordinate.
- `MERTENS_EXPONENT_LOG_LIMSUP.lean`: exact integer logarithmic-limsup coordinate.
- `MERTENS_EXPONENT_STRIP_ACCEPTANCE.lean`: exact signatures and 24 kernel axiom
  printouts, checked by the dedicated workflow.

Actions compiles the complete import closure using
`python3 scripts/compile_research_import_closure.py --build-library` with target
`research/MERTENS_EXPONENT_STRIP_ACCEPTANCE.lean`. Every research compile uses
`-DwarningAsError=true`. The dedicated workflow rechecks acceptance and rejects
any dependency axiom other than `propext`, `Classical.choice`, or `Quot.sound`.
Existing repository source, root-import, proof inventory, export, and targeted
Lean checks remain enabled and unchanged. Human review/merge is required.

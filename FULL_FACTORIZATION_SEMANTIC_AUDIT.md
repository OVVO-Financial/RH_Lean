# Full Prime-Factorization Semantic Audit

## Scope

This audit reviews every repository concept using Möbius parity together with
parent, cofactor, terminal-prime, factor-depth, or prime-extension language.
The governing rule is:

> Möbius parity is read only from the complete prime factorization of the
> integer whose Möbius value is being evaluated.

A compressed identity such as `102 = 6 * 17` is a valid transport edge between
two distinct arithmetic states.  It is not a two-prime factorization.  The
complete child factorization is `102 = 2 * 3 * 17`, so `μ(102) = -1`, while the
separate parent state is `6 = 2 * 3`, so `μ(6) = +1`.

## Semantic invariants

1. Every integer is interpreted through its complete prime factorization.
2. Prime multiplicity is retained; a repeated prime forces Möbius value zero.
3. On squarefree integers, Möbius sign is `(-1)^Ω(n) = (-1)^ω(n)`.
4. A cofactor or parent remains a complete integer with its own full
   factorization and its own Möbius value.
5. `n = c * q` is transport notation.  It never licenses reading the factor
   depth of `n` as two unless both displayed factors are prime.
6. A fresh-prime recurrence `μ(cq) = -μ(c)` is valid because it appends one
   prime to the complete factorization of `c`.
7. A collision `q ∣ c` creates a repeated prime in the complete child state and
   therefore gives `μ(cq) = 0`.

## Lean guardrail added

`RHLean/Arithmetic/FullPrimeFactorizationState.lean` now provides:

- `fullPrimeFactorDepth`, using `ArithmeticFunction.cardFactors`, so
  multiplicity is retained;
- `distinctPrimeFactorDepth`, using `cardDistinctFactors`;
- `fullPrimeSupport`, using `Nat.primeFactors`;
- the exact squarefree parity theorem
  `moebius_eq_negOnePow_fullPrimeFactorDepth`;
- the repeated-prime zero theorem
  `moebius_eq_zero_of_not_squarefree_fullState`;
- reconstruction of a squarefree integer from its complete prime support;
- equality of full and distinct depth on squarefree support;
- `PrimeTransportEdge`, deliberately containing no factor-depth field;
- fresh-edge sign reversal and collision-zero theorems;
- the exact finite square-block depth-parity identity
  `squareBlockMoebius_eq_fullDepthParity`.

## Classification of audited Lean modules

### Formally sound full-factorization use

These modules explicitly use complete prime sets, squarefreeness, or mathlib's
factor-count arithmetic functions.  No compressed factor-count error was found.

- `RHLean/Arithmetic/LeastPrimeDepthHierarchy.lean`
  - uses `n.primeFactors.card` for distinct prime depth;
  - reconstructs squarefree integers with
    `Nat.prod_primeFactors_of_squarefree`;
  - correctly proves semiprime and low-depth statements.
- `RHLean/Proof/LowOmegaHighOrientation.lean`
  - explicitly identifies `n.primeFactors.card` with `ω(n)`;
  - uses the complete cofactor prime set, not the visible pair count.
- `RHLean/Proof/DeathShellCofactorParity.lean`
  - correctly proves `μ(m) = (-1)^(ω(c)+1)` only after showing the cofactor is
    squarefree and the terminal prime is coprime to it;
  - the `+1` represents one appended prime, not one visible factor beside an
    opaque cofactor.
- prime-face / Boolean-cube modules
  - model squarefree states by actual prime subsets and therefore retain full
    factor depth.
- log-weighted child-fiber modules
  - remove one actual prime from a squarefree endpoint and use the exact
    Möbius sign reversal.

### Formally sound transport, terminology hardened by the new guardrail

These constructions use a parent/cofactor and terminal prime.  Their recurrence
statements are valid, but they must always be read as maps between distinct full
arithmetic states.

- `RHLean/Arithmetic/CanonicalEndpointCore.lean`
- `RHLean/Arithmetic/CanonicalTerminalPrimeExtension.lean`
- `RHLean/Analysis/CanonicalSquareBlockZones.lean`
- `RHLean/Analysis/DyadicTransportCanonicalForm.lean`
- `RHLean/Analysis/DyadicTransportCompression.lean`
- `RHLean/Analysis/FreshPrimeOscillationTransfer.lean`
- `RHLean/Proof/DeathProcessArithmetic.lean`
- `RHLean/Proof/DeathShellDivisorFibers.lean`
- `RHLean/Analysis/CanonicalLowOccupancy.lean`
- `RHLean/Analysis/CanonicalHighSectorCore.lean`
- normalized-cofactor and high-family decomposition modules.

The audit found no proved theorem in these files whose conclusion derives
Möbius parity merely from the two displayed factors `c` and `q`.  The main risk
was semantic compression in prose and future downstream use.

### Research prose and numerical scripts requiring explicit semantic labels

The following areas use parent/cofactor shorthand heavily and should be read or
updated under the invariants above:

- `research/OMEGA_PARITY_ORIENTATION.md`
- `research/DYADIC_MOBIUS_SIGNED_RESIDUAL.md`
- `research/PR99_CORRECTION_EXACT_ACTIVITY.md`
- `research/DYNAMIC_VIOLE_BASELINE.md`
- `BIG_PICTURE_PROOF_MAP.md`
- `RESEARCH_ROUTE_REGISTRY.md`
- `FORMALIZATION_SEQUENCE.md`
- `FORMALIZATION_CHECKLIST.md`
- death-shell and dyadic transport experiment scripts.

No numerical result should call the number of displayed factors in `c*q` the
Möbius depth.  Scripts must compute depth from a full prime factorization,
`Ω(n)`, or an equivalent exact sieve state.

## Audit conclusion

The serious conceptual error occurred in the interpretation of compressed
parent notation, not broadly in the existing proved Lean theorems.  Several
existing modules already do the correct full-factorization work explicitly.
The new guard module makes that distinction a first-class dependency and
prevents future proof layers from treating a composite parent as one prime.

The remaining mathematical problem is unchanged: the exact elementary identity

```text
sum_{n in I} μ(n) = sum_k (-1)^k * #{n in I : n squarefree and Ω(n)=k}
```

must be supplemented by a nontrivial estimate showing near-balance between the
even- and odd-depth populations.

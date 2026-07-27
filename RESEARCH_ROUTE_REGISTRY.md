# Research route registry

This file is the permanent trail marker for analytic routes explored around the
square-prefix Mertens program. It records which mechanisms are exact, which
finite experiments have been run, which mechanisms have failed their declared
tests, and which routes remain materially distinct.

The protected target does not change:

```text
SquarePrefixUniformLocalBoundedStatement
  -> MertensEnergyBoundedStatement
  -> ClassicalMertensRHCriterion
  -> RiemannHypothesisStatement.
```

Numerical experiments are diagnostics only. A route marked **closed** must not
be restarted by merely increasing the finite range, renaming the same
components, or replacing one sign-blind inequality by another.

## Closed route: single-prime dyadic Li-residual cancellation

**Status: CLOSED AS AN RH MECHANISM. Recorded by PR #105.**

The route tested the following proposed mechanism:

1. use the exact active-prime intervals;
2. pair each odd cofactor `c` with its doubled child `2c`;
3. retain the exact joint `K+J` paired residual;
4. expect the remaining true Möbius signs to give random-like or better
   cancellation across cofactors;
5. expect the complementary main term and odd tail to absorb the remaining
   coherent mode.

The exact parent/child and `K+J` identities are valid and remain useful. Steps
4 and 5 failed the predeclared finite falsification tests.

Permanent findings:

- the exact within-pair `K/J` cancellation is strong;
- the aggregate cross-cofactor system is frequently nearly rank one;
- the dominant obstruction is a slow coherent mode, not centered noise;
- the true Möbius signs frequently reinforce that mode relative to random signs;
- full recombination with the complementary main and odd tail does not
  consistently cancel it;
- there is no additional exact identity placing the coherent paired mode inside
  the complementary main or tail;
- the only exact full relation is the tautological reconstruction

  ```text
  Main - P - T = squarePrefixMertens.
  ```

See [`research/DYADIC_LI_ROUTE_FALSIFICATION.md`](research/DYADIC_LI_ROUTE_FALSIFICATION.md)
and [`scripts/DyadicLiRouteFalsification/`](scripts/DyadicLiRouteFalsification/).

### Do not repeat this route by

- rerunning the same aggregate Möbius-versus-random statistic only at larger
  `N`;
- deriving more centered Vaughan/Type-I/II bounds while leaving the coherent
  mode untouched;
- treating PCA or high finite correlation as an arithmetic identity;
- claiming that Abel summation, telescoping, or the Li baseline alone gives the
  needed signed estimate;
- claiming that the complementary main or odd tail contains an exact negative
  copy of the paired coherent mode;
- invoking a zeta-zero explicit formula as the primary proof architecture.

A future theorem may revisit this branch only if it introduces a genuinely new
mechanism that controls the coherent mode itself.

## Exact results retained from the closed route

The following are not withdrawn:

- exact active-prime endpoints;
- exact odd-parent/even-child Möbius pairing;
- exact paired/transition/tail decomposition;
- exact `K+J` recombination and the necessity of keeping the pair joint;
- exact complementary-main decomposition;
- finite Hilbert-space projection-defect and excess-energy identities;
- finite Abel identities, with no claim that absolute variation proves the
  signed estimate.

## Active, materially distinct routes

### 1. Multi-prime Möbius cubes

**Status: UNTESTED.**

Replace the one-prime operator `(I-T_2)` by finite products such as

```text
(I-T_2)(I-T_3),
(I-T_2)(I-T_3)(I-T_5),
(I-T_2)(I-T_3)(I-T_5)(I-T_7).
```

The required diagnostic must include complete interior cubes, every boundary
face, the rough-core tail, and coherent/centered energies. Interior improvement
is insufficient if boundary faces inherit the full coherent obstruction.

### 2. Fixed multiplicative wavelets

**Status: UNTESTED.**

Use predetermined arithmetic low-pass and mean-zero wavelet channels on the
log-cofactor axis, not data-fitted PCA modes. The decisive question is whether
the low-pass obstruction has an elementary exact description genuinely easier
than the original Mertens object.

### 3. Birth/death packet-start representation

**Status: OPEN AND DISTINCT.**

This representation changes the primitive variables from persistent active
intervals to sparse packet-start/death events. Earlier finite diagnostics found
modular structure in raw death shells and much weaker fixed-lag structure after
packet compression and centering. It still requires an exact energy bridge and
must retain the survivor discrepancy.

### 4. High-cofactor parabola kernel

**Status: OPEN, BUT REQUIRES AN EQUIVALENCE TEST FIRST.**

Before further analytic or Lean investment, test whether the open high-sector
kernel estimate is merely the same coherent obstruction expressed in squared
complex/cofactor-parabola coordinates. If so, it is a reparameterization rather
than a new route.

## Acceptance rule for future routes

A proposed route must state:

1. the exact object it changes;
2. why it is not the closed single-prime dyadic Li-residual mechanism;
3. its predeclared numerical or algebraic continue/stop criterion;
4. how coherent and `H=1` behavior are controlled;
5. every boundary or unmatched term;
6. whether the result is an exact identity, finite diagnostic, sufficient
   criterion, or open analytic premise.

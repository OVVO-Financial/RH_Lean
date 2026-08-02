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

## Closed route: fixed consecutive omega-class (2-vs-3) parity

**Status: CLOSED AS A LEVER. Recorded by this note.**

The route proposed proving a parity balance between the 2-prime-factor and
3-prime-factor classes (`Q_2 ~ Q_3`, pairwise `Q_{2j} ~ Q_{2j+1}`) to force
`M(N)` small, using the already-compiled cofactor-`omega` coordinate
(`RHLean.Proof.DeathShellCofactorParity`, `N_k`).

Predeclared falsification (survives only if `|Q_2 - Q_3|` stays `o(|Q_2|)` and
keeps its sign) failed: the gap is orders larger than `M`, grows, and changes
sign by `X = 4e6`. `M` is small by simultaneous cancellation across all classes,
not by any two-class balance — confirming `BIG_PICTURE_PROOF_MAP.md` §3.

The parity instinct is not wasted: reorganizing the same alternating sum by
largest-prime orientation (`P+(m)` above/below `sqrt(m)`) gives
`M = A_high + A_low` with `A_high ~ -A_low` and `|M|/|A_high|` decreasing
(0.174 -> 0.0087 through `4e6`). But that is exactly the smooth/transport
residual the program already protects, not a new mechanism.

See [`research/OMEGA_PARITY_ORIENTATION.md`](research/OMEGA_PARITY_ORIENTATION.md)
and [`experiments/omega_parity_orientation.py`](experiments/omega_parity_orientation.py).

### Do not repeat this route by

- enlarging `X` and re-checking `Q_2` versus `Q_3`;
- renaming `N_2/N_3` or pairing a different fixed consecutive `omega` class;
- treating the orientation near-cancellation `A_high ~ -A_low` as new — it is the
  existing smooth-minus-transport target re-encoded.

A future omega-parity theorem must control the full transport sum `A_high`
itself, with the `sqrt(m)` boundary geometry retained.

## Closed sub-route: single-wheel Gram/Lyapunov feasibility search

**Status: CLOSED AS A DISCOVERY METHOD. Recorded by this note.**

This closes the search *method* used by PRs #176 and #177 — fixing one primorial
extension `W -> pW` and testing whether some positive quadratic form satisfies
output domination, the seed budget, and extension compatibility there. It does
**not** close obligation A, and it does **not** close any route in the sense of
the analytic premise being refuted.

Two exact theorems, in
[`research/GRAM_LYAPUNOV_DICHOTOMY.md`](research/GRAM_LYAPUNOV_DICHOTOMY.md) and
verified by
[`scripts/GramLyapunovDichotomy/verify.py`](scripts/GramLyapunovDichotomy/verify.py):

- **Dichotomy.** A PSD form with zero direct target square dominates the target
  on the compatibility space `V` **iff** `e_0 notin V`, i.e. iff the compatibility
  annihilator determines the target coordinate. So "annihilator independence" and
  "zero direct target square" — the two conditions declared admissible by
  PR #177 — are jointly unsatisfiable.
- **Regeneration.** For consecutive primorials the full **old**-wheel divisibility
  mask is never realized in `(W, pW]` (the only multiple of `W` there that is
  squarefree and coprime-compatible is `n = pW`, which carries the full **new**
  mask). Hence `e_0 notin V` at every level and the tautological rank-one form
  regenerates at every level — checked at `30 -> 210`, `210 -> 2310`,
  `2310 -> 30030`.
- **Trajectory pinning.** Any admissible form obeys
  `R_U^2 <= Q(s_U) <= 2 phi(pW)` on realized states. The band factor is exact and
  below 5 for every primorial block through `(30030, 510510]`, so no admissible
  form carries independent arithmetic content along the trajectory.

### Corrections to previously recorded verdicts

- PR #177's `V_210` is misidentified: it is defined by `chi_31`, but mask `31` is
  realized (by `n = 2310`); the missing mask is `15 = {2,3,5,7}`. The published
  `-2` survives on the correct quotient, but the verdict "not quotient-stable" is
  **withdrawn** — the mechanism regenerates and is instead eliminated by the
  dichotomy.
- PR #176's certificate is exact and reproduces, but its classification is
  narrowed from **CLOSED** to **OPEN AT A LARGER CONSTANT**: the seed constant
  `2` in `2 phi(W)` is free (the extension law `b(pW) = (p-1) b(W)` holds for any
  `c`, and `|R| <~ sqrt(c phi(W))` is RH-strength for any fixed `c`), so the
  certificate proves `c >= 46/3`, not nonexistence.

### Do not repeat this route by

- running another one-wheel feasibility search with a different sparsity pattern,
  symmetry reduction, or rank bound — every wheel is feasible, for a reason now
  fully characterized;
- reporting a separating certificate at a single wheel as a family closure
  without exhibiting growth of the required constant `c_k` across at least two
  consecutive extensions;
- treating the `210 -> 2310` check as a discriminating test of quotient
  stability.

### Growth test discharged: the required constant does not grow

The predeclared growth test has been run at the first two consecutive primorial
extensions, for the canonical test family (all realized prefix states of the
block). See
[`research/DIAGONAL_REQUIRED_CONSTANT_GROWTH.md`](research/DIAGONAL_REQUIRED_CONSTANT_GROWTH.md)
and [`scripts/DiagonalConstantGrowth/verify.py`](scripts/DiagonalConstantGrowth/verify.py).

Two-sided exact rational certificates give

```text
c_1 >= 7819/1728   = 4.5248843...      (30 -> 210,   exact dual certificate)
c_2 <= 7837117/4e6 = 1.9592793...      (210 -> 2310, exact primal certificate)
```

so the required constant **falls** by a factor of about `0.43`. The same
direction is reproduced by four independent test families. The LP dual used is
exactly PR #176's certificate structure, and the method reproduces PR #176's
`368/3` as the exact optimum of its own test family.

Under the predeclared criterion this is the FEASIBLE branch: **the non-circular
mask-specific diagonal family is not closed, and PR #176 stays OPEN AT A LARGER
CONSTANT** — now on direct measurement, not only on the logical objection.

These are bounds for declared finite test families; they do **not** prove the
true minimal constants decrease. The bounds are strongly family-dependent (at
`30 -> 210` the value rises from `4.52` to `66.25` as the family is enriched),
and a fixed rule covers a smaller fraction of the larger cube at the higher
level. What is established is that the certificate method, at comparable
strength, produces no growth — and closure requires growth.

`c_3` at `2310 -> 30030` was attempted and is **not** reported: the
floating-point LP breaks down at that dynamic range.

### State closure: SOLVED, and it was not the bottleneck

**Status: SOLVED. Recorded by
[`research/PRIME_EXTENSION_STATE_CLOSURE.md`](research/PRIME_EXTENSION_STATE_CLOSURE.md)
and [`scripts/PrimeExtensionStateClosure/verify.py`](scripts/PrimeExtensionStateClosure/verify.py).**

A genuinely closed prime-extension state exists. It is not an enlargement of the
packet state — it is a change of index. Take as state the whole **scale-indexed**
rough summatory function `T_W : y |-> sum_{n <= y, (n,W)=1} mu(n)`, and as the
level-`W` assertion a sup bound `|T_W(y)| <= Phi(y)` for `y <= X`. Parent and
child assertions are then the same predicate on the same kind of object over the
same scales. The exact transfer law is

```text
T_{pW}(x) = T_W(x) + T_{pW}(floor(x/p)),
T_{pW}(x) = sum_{j >= 0} T_W(floor(x/p^j)),
```

and reading it downward gives the exact telescope
`M(x) = sum_{d|W} mu(d) T_W(floor(x/d))`.

**Having this changes nothing**, for two independently sufficient reasons:

1. **The generic descent costs a factor `2` per prime.** The triangle inequality
   gives only `|M(x)| <= 2^k sup_{y<=x} |T_{W_k}(y)|`. Measured at `x = 20000`
   where `|M(x)| = 26`, the slack runs `19x, 80x, 265x, 745x` for
   `W_k = 6, 30, 210, 2310`. With `W_k` the primorial of primes up to `z` the
   loss is `2^{pi(z)}`.
2. **The base case is RH-equivalent.** For `p_k < y < p_{k+1}^2` one has exactly
   `T_{W_k}(y) = 1 + k - pi(y)`, verified for `k = 1..5`. A sup bound on the base
   is a prime-counting error bound; at RH strength it is the conclusion.

So state closure is **not** the bottleneck, and the earlier framing that listed
it as the remaining content of obligation A is corrected here. The bottleneck is
signed cancellation.

### Reframing of obligation A

Obligation A should no longer be stated as "construct an enlarged
extension-compatible state with a positive quadratic form": that formulation is
now closed from three directions (the dichotomy, the trajectory pinning, and the
state closure above). State it as what it always reduced to:

> Exhibit signed cancellation between `T_{pW}(x)` and `T_{pW}(floor(x/p))` — or
> equivalently among the `2^k` terms of the exact telescope
> `M(x) = sum_{d|W} mu(d) T_W(floor(x/d))` — strong enough to beat the `2^k`
> triangle-inequality loss.

Three successive cycles have found the same shape: an exact structure that
reproduces the target rather than controlling it. Full telescoping is
tautological; the zero-direct-square Gram class exists exactly when the
annihilator reconstructs the target; and the closed induction has an
RH-equivalent base. Any proposal that does not address the signed sum directly
is, on that evidence, a reparameterization.

### Superseded: the interval-mismatch diagnosis

The enlarged extension state has components on different intervals: `A_C(U)` sums
over the child block `(W, pW]` while `B_C(U)` sums over the dilate `(W/p, U/p]`,
and `W/p` is never the previous primorial `W_{k-1}`. Two distinct failures follow:

- **scale** — `A` is child-scale (`max|A_C| = 92` against `max|B_C| = 11` over
  `(30,210]`, under a declared budget of `16`);
- **direction** — the extension law is a recursion in *wheel depth at fixed
  interval*, while the budget is a statement *per block*. These are different
  recursions and the framework supplies no bridge.

No positive form on the current enlarged state can close the induction, whatever
its feasibility at any single wheel.

That diagnosis stands for the packet state. Its **prescription** — enlarge the
packet state — was wrong: the fix is to stop indexing by block, as recorded in
the state-closure entry above.

A future Gram argument must first solve the state-closure problem: exhibit an
induction state preserved by prime extension on which the parent and child bounds
are statements about the same object. The current enlarged state mixes scales
(`max|A_C| = 92` child-scale against `max|B_C| = 11` parent-scale over
`(30, 210]`, under a declared budget of `16`).

## Active, materially distinct routes

### 1. Multi-prime Möbius cubes

**Status: TESTED / OPEN. Recorded by Issue #171.**

Replace the one-prime operator `(I-T_2)` by finite products such as

```text
(I-T_2)(I-T_3),
(I-T_2)(I-T_3)(I-T_5),
(I-T_2)(I-T_3)(I-T_5)(I-T_7).
```

The required diagnostic must include complete interior cubes, every boundary
face, the rough-core tail, and coherent/centered energies. Interior improvement
is insufficient if boundary faces inherit the full coherent obstruction.

Issue #171 ran this diagnostic on completed primorial blocks up to
`W = 9,699,690`. Keep the four statuses below distinct.

**Exact algebra established (identities, not estimates).**

- The primorial-block residual is exactly the top Walsh coefficient of the
  cofactor field on the Boolean divisor cube: `R_N = 2^k \hat f_N([k])`.
- The comb–cofactor and mixed-Boolean-difference identities hold exactly.
- The Euler–CRT roughness recursion `D_p T_W = T_{W/p}` (and its iterate
  `prod_{p|d} D_p T_W = T_{W/d}`, telescoping to `M`) holds coefficientwise for
  squarefree `W`, elementarily.
- The completed prime-extension endpoint identity
  `Z_{W->pW} = A_p(W,pW] + U_p A_p(W/p,W]` holds, with the local `{2,3}`-channel
  maps acting as exact isometries of `N(T + D sqrt(-2)) = T^2 + 2 D^2`
  (`z -> -z` for `p = 1 mod 6`, `z -> conj z` for `p = 5 mod 6`; square
  deletion is contractive).

**Falsified sub-mechanism (predeclared test).**

- Pure CRT boundary sparsity does **not** explain the high-degree collapse.
  High-degree packets are abundant (top-degree support fraction ~0.82 at
  `W = 2310`, ~0.83 at `W = 30030`); geometric degree energy alone suppresses
  the top layer only to the percent scale. This kills the "few packets reach
  high codimension" explanation.

**Diagnostic observation (numeric, not a theorem).**

- The decisive high-degree suppression is Euler-weighted destructive
  interference across the surviving packets: the degree-coherence ratio
  `kappa_j` shows a transition from strong constructive coherence at low degree
  to sub-incoherent recombination near the cube dimension.
- The two-channel ellipse `D^2 + (1/2) T^2 <= phi(W)` held at every tested
  prefix, at utilization ~0.61–0.93. This is evidence of near-sharpness, **not**
  evidence of eventual failure and **not** a proof; the sequence is neither
  monotone nor shown to stay below 1.

**Unresolved analytic premise (open, RH-scale).**

- The missing theorem is a degree-by-degree Euler–CRT coherence / spectral-gap
  bound controlling energy propagation into the highest Boolean layers,
  equivalently a completed-wheel non-zero-frequency lower bound. In the
  two-channel contrast coordinate `T(x) = sum mu(n) eta(n)`, the twisted series
  is governed by `1/L(s, chi_{-3})` while `M` is governed by `1/zeta`; a
  full-prefix bound of the conjectured strength would therefore **imply** both
  RH for `zeta` and the corresponding statement for `L(s, chi_{-3})`, and is at
  least as deep as their conjunction. The two-coordinate endpoint state is
  **not closed** (the child endpoint is not a function of the parent `(T,D)`
  pair alone), so any proof needs an enlarged packet/character/Gram state; the
  interior no-overshoot bound is a separate open target.

### Do not repeat this route by

- rerunning the same completed-wheel prefix statistic only at a larger `W` and
  reporting "no violation found" as if it settled the constant;
- renaming the same two-dimensional `(T,D)` state (8-channel, 2-channel,
  `Z[sqrt(-2)]`, spectral-gap, backward-descent) and presenting it as a new
  mechanism — the missing coordinates are not added by any of these;
- introducing the analytic coherence bound as a Lean `axiom`, a `sorry`, or a
  hypothesis wired into the protected RH theorem chain.

The exact-identity layer above is suitable for independent formalization; the
analytic premise must remain a named, unproven `Prop`.

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

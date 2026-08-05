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

## Closed route: Euler–CRT roughness as an RH mechanism

**Status: CLOSED AS A STANDALONE RH-DISCOVERY ROUTE. Owner decision recorded by PR #180.**

The exact Euler–CRT identities, their Lean formalizations, and the finite no-go
certificates are retained. What is closed is the proposal that repeated wheel
extension, packet enlargement, positive Gram/Lyapunov control, or cancellation
inside the exact divisor telescope supplies an independent RH mechanism.

The closure rests on four convergent findings:

1. **Single-wheel positive forms are tautological or trajectory-pinned.** The
   zero-direct-square class exists exactly when a compatibility annihilator
   reconstructs the target; pointwise variants are pinned to the target scale.
2. **The required diagonal constant does not exhibit growth.** Exact finite-family
   certificates remain bounded through three consecutive primorial extensions;
   the separating-certificate program therefore does not close the family.
3. **A prime-extension-closed state exists, but its base is RH-equivalent.** The
   scale-indexed rough summatory function closes exactly under prime extension,
   yet the resulting descent merely reproduces the target and loses cancellation.
4. **The telescope-cancellation target is not viable.** Marginal bounds make the
   triangle inequality optimal; the honest cancellation requirement worsens with
   every prime added; regrouping exactly undoes the expansion; and bounded-depth
   truncation misses the last-mile parity cancellation.

See
[`research/GRAM_LYAPUNOV_DICHOTOMY.md`](research/GRAM_LYAPUNOV_DICHOTOMY.md),
[`research/DIAGONAL_REQUIRED_CONSTANT_GROWTH.md`](research/DIAGONAL_REQUIRED_CONSTANT_GROWTH.md),
[`research/PRIME_EXTENSION_STATE_CLOSURE.md`](research/PRIME_EXTENSION_STATE_CLOSURE.md),
and
[`research/TELESCOPE_CANCELLATION_LIMITS.md`](research/TELESCOPE_CANCELLATION_LIMITS.md).

### Exact results retained

- coefficientwise Euler–CRT roughness removal;
- interval roughness recursion;
- prime-extension transfer for the scale-indexed rough summatory function;
- Boolean/Walsh and packet identities already formalized or recorded;
- exact rational finite certificates and route-falsification verifiers.

### Do not repeat this route by

- enlarging the primorial wheel and asking the same telescope to create more
  cancellation;
- regrouping, truncating, or reweighting the invertible divisor expansion without
  introducing genuinely new joint arithmetic information;
- searching another one-wheel positive form, sparsity pattern, symmetry class,
  or coordinate renaming;
- treating a closed-state identity or an RH-equivalent base estimate as a
  reduction;
- importing centered Type-I/II estimates that leave the coherent mode untouched,
  which is already forbidden by the closed dyadic Li-residual route.

A successor may reuse the exact Euler–CRT infrastructure only if it introduces a
materially new, non-invertible mechanism—such as a bilinear decomposition with
an explicit coherent-mode estimate—and passes the registry acceptance rule from
the outset.

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

### Telescope-cancellation target: WITHDRAWN

**Status: NOT VIABLE. Recorded by
[`research/TELESCOPE_CANCELLATION_LIMITS.md`](research/TELESCOPE_CANCELLATION_LIMITS.md)
and [`scripts/TelescopeCancellationLimits/verify.py`](scripts/TelescopeCancellationLimits/verify.py).**

The reframing below was tested and fails. Four exact checks:

1. **Marginal no-go (proved).** With only per-term bounds
   `|T_W(x/d)| <= Phi_d`, the best derivable bound is `sum_d Phi_d`, attained at
   `t_d = mu(d) Phi_d`. The triangle inequality is optimal among arguments using
   per-term bounds; joint information across `d` is required.
2. **Monotone worsening (measured).** The honest triangle bound
   `sum_{d|W} |T_W(x/d)|` divided by `|M(x)|` is exactly `1` at the **empty**
   wheel and increases monotonically with every prime added — `1.0, 1.4, 10.8,
   41.4, 105.5, 189.2, 289.2` for `k = 0..6` at `x = 100000`. The optimal wheel
   is the empty one; the telescope is an expansion, not a reduction.
3. **Regrouping collapse (proved).** Pairing `d` with `pd` along any wheel prime
   returns the telescope for `W/p`. The expansion is exactly invertible, so no
   grouping extracts information.
4. **Truncation failure (measured).** Brun-style truncation at `omega(d) <= r`
   oscillates (`-773, +1142, -573, +21, -48` at `W = 210`, `x = 100000`,
   `M = -48`) with error above the target at every depth short of full. The
   cancellation is entirely last-mile, and the `L1` mass is spread — the largest
   term is `12-15%`, the top four `34-46%`.

Also corrected: earlier notes quote the loss as `2^k sup |T_W|`. The honest
triangle bound is `sum_{d|W}|T_W(x/d)|`, about `8x` smaller at
`W = 30030, x = 100000` (`13882` against `107840`). The conclusion is unchanged.

Classically this is the **Legendre sieve** for `mu`, and the blow-up is its known
failure mode. Brun/Selberg escapes buy bounds for sifted counts, but `M` is
parity-sensitive (`mu(n) = (-1)^{omega(n)}` on squarefree `n`), so Selberg's
parity phenomenon obstructs them here.

### Do not repeat this route by

- seeking cancellation among telescope terms at a larger wheel — the requirement
  strictly grows with the wheel;
- regrouping, pairing, or reordering the telescope — every grouping collapses it;
- truncating the inclusion-exclusion at bounded level and bounding the tail;
- restating the roughness recursion in new coordinates and calling the result a
  new mechanism.

### Superseded reframing of obligation A

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

**Status: CLOSED AS A STANDALONE RH MECHANISM. See the Euler–CRT route closure above.**

The exact algebra and finite diagnostics below are retained as infrastructure,
but this item is no longer an active route unless a successor introduces a
materially new non-invertible mechanism satisfying the acceptance rule.

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

**Former analytic premise (withdrawn as a route target).**

- The degree-by-degree Euler–CRT coherence / spectral-gap premise remains a
  mathematically meaningful statement, but within this branch it is not a
  reduction: the surrounding exact structures are invertible re-expressions of
  the target, and the full-prefix strength would already imply RH-scale control
  for both `zeta` and `L(s, chi_{-3})`.
- It must not be reintroduced as a Lean `axiom`, `sorry`, or protected-chain
  hypothesis, nor presented as progress without a genuinely new mechanism that
  controls the coherent mode.

### Do not repeat this route by

- rerunning the same completed-wheel prefix statistic only at a larger `W` and
  reporting "no violation found" as if it settled the constant;
- renaming the same two-dimensional `(T,D)` state (8-channel, 2-channel,
  `Z[sqrt(-2)]`, spectral-gap, backward-descent) and presenting it as a new
  mechanism — the missing coordinates are not added by any of these;
- introducing the analytic coherence bound as a Lean `axiom`, a `sorry`, or a
  hypothesis wired into the protected RH theorem chain.

The exact-identity layer above remains suitable for independent formalization.

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

### 5. Anchor coverage of the frozen-prefix slack invariant

**Status: EXACT LAYER FORMALIZED. THE ESTIMATE IT REDUCES TO IS OPEN.**

The forward and backward slack identities for `S_K(x) = K^2 Q(x) - M(x)^2` are
the *same* statement about an anchor value `c` and an interior value `y = M(x)`:
`c` covers `y` when `c(y-c) <= 0`, and the cross-term-free obligation is then
`c^2 + (y-c)^2 <= K^2 Q(x)`. Formalized in
[`RHLean/Proof/TwoAnchorSlackCoverage.lean`](RHLean/Proof/TwoAnchorSlackCoverage.lean),
with the exact recomputations in
[`scripts/TwoAnchorSlackCoverage/`](scripts/TwoAnchorSlackCoverage/) and the
discussion in
[`research/TWO_ANCHOR_SLACK_COVERAGE.md`](research/TWO_ANCHOR_SLACK_COVERAGE.md).

Settled by this route:

- opposite-sign frozen endpoints cover every interior value, and same-sign
  endpoints leave exactly the excursions beyond both anchors;
- no single anchor is universal, so neither left- nor right-orientation alone can
  be the pointwise mechanism;
- the price of discarding a favourable cross term is exactly that cross term,
  `-2c(y-c)`, so coverage is free but the constant is not;
- consecutive primorial endpoints are **not** always opposite in sign: four of
  the nine consecutive pairs through `29#` are same-sign, including
  `(19#, 23#]`, which has `7933289` uncovered prefixes. An anchor-bracketing
  property for consecutive primorial endpoints is false as stated.

### 6. Stage energy recurrence `E_q <= A E_{q^-} + C x`

**Status: ALGEBRAIC LAYER FORMALIZED. THE `(A, C)` INEQUALITY IS THE OPEN THEOREM.**

The iterated consequence of a one-stage affine energy recurrence is exact algebra
and is proved in
[`RHLean/Proof/AbstractEnergyRecurrence.lean`](RHLean/Proof/AbstractEnergyRecurrence.lean):
from `E_{j₀} <= B x` and `E_{j+1} <= A_j E_j + C_j x`,

```text
E_n <= (prod_r A_r) B x + x sum_s C_s prod_{r>s} A_r,
|Λ_n V_n|^2 <= D_n x [ B prod_r A_r + sum_s C_s prod_{r>s} A_r ].
```

Measured so far: `B_{<=7}^emp = 29.850695` on every prefix of `(30030, 510510]`,
with mature-prefix inflations `A_11 = 1.179208`, `A_13 = 1.125960`,
`A_17 = 1.289167`, and a largest post-`7` inflation `A_11 = 3.624432` at the `29#`
bottleneck declining to `1.265988` at `29`. The honest status is
`A_q^emp < 3.7` on the tested stages. See
[`research/STAGE_ENERGY_RECURRENCE.md`](research/STAGE_ENERGY_RECURRENCE.md).

### Do not repeat this route by

- reading the iterated estimate as progress toward `M(x)`: it is an implication
  from constants nobody has proved exist;
- folding the asymptotic specialization `D_n = 3^n` and
  `n = O(log x / log log x)` into the algebraic lemma — that converts a lemma
  into a conditional theorem;
- quoting `A_q^emp < 3.7` as a bound: it is a finite measurement on tested
  stages, and the unrestricted-prefix column of the same table is where the
  boundary regime shows;
- guessing the `C/S/W` operators in order to recompute the energy — two published
  prime-`3` triples do not determine them.

### 7. Signed canonical height, balanced factor pairs

**Status: THE FINITE LAYER IS FORMALIZED. THE RAW PIECEWISE STRATEGY IS CLOSED; THE
MAIN-TERM-SUBTRACTED ONE IS OPEN AND PASSES ON THE MEASURED RANGE.**

The corrected clock, the low-imbalance counting theorem and the low-band energy are
exact and formalized in
[`RHLean/Proof/SignedCanonicalHeight.lean`](RHLean/Proof/SignedCanonicalHeight.lean);
the balanced regime `0 < d < u` is exact and formalized in
[`RHLean/Proof/BalancedCanonicalGap.lean`](RHLean/Proof/BalancedCanonicalGap.lean).
Both are re-verified by direct enumeration in
`scripts/TwoAnchorSlackCoverage/signed_height_check.py` and
`scripts/TwoAnchorSlackCoverage/balanced_gap_check.py`.

What the balanced layer buys: the largest-prime condition collapses to primality of
one endpoint, the doubled height is pinned to `dn` within constants `2` and `3`
(measured range `[2.0014, 2.6667]`), and the canonical coefficient becomes the
symmetric `beta = mu(u) mu(u+d) 1_{u or u+d prime}`.

The exact prefix-energy ledger `E(bal + ext) = E(bal) + 2 Cross + E(ext)`, with the
Gram kernel `H - max(i,j)`, is formalized in
[`RHLean/Proof/CanonicalGapPrefixGram.lean`](RHLean/Proof/CanonicalGapPrefixGram.lean).

What none of this buys, measured in
`scripts/TwoAnchorSlackCoverage/balanced_split_frontier.py` over blocks `n <= 1900`.
The diagnostic is `|prefix|/N`, since the target's prefix form is `<< N^{1+eps}`; a
piece passes if that stays bounded. The balanced and extreme halves each drift to
`13.2 N` and are still climbing, against the true total's `0.43 N`, and each is
roughly `500x` its own sum at `N = 1900`. Inside `beta`, the failure is carried by
exactly one term: the overlap count `C` reaches `12.9 N`, while `A`, `B` and `A + B`
are all bounded at `0.309`, `0.245` and `0.394` — the same scale as the truth.

`scripts/TwoAnchorSlackCoverage/prefix_gram_cross.py` says the same thing in the
energy norm the target actually uses. The prefix correlation
`rho = Cross / sqrt(E(bal) E(ext))` converges to `-1` (`-0.989, -0.992, -0.998,
-0.999` at `(N,H) = (400,100), (700,175), (1000,250), (1400,350)`). Against the budget
`H N^2`, `E(total)/HN^2` sits at the `10^-2` level with no drift while `E(bal)/HN^2`
runs `1.51, 2.09, 4.69, 9.44` and keeps climbing: the total meets the target and each
half fails it alone.

**But the excess is a main term, not unstructured growth.**
`scripts/TwoAnchorSlackCoverage/balanced_main_term_repair.py` identifies it in closed
form: the three primality cases contribute `+N_pp, -N_pp, -N_pp`, so the balanced
half's main term is `-N_pp`, exactly the overlap term `C`, and `N_pp` can be replaced
by a prime-density prediction `Cpred` carrying no Möbius input. Subtracting it moves
the balanced half from `13.2 N` to **`0.44 N`** (prefix `+126` at `N = 1900`), and
subtracting the exact count instead gives `0.39 N` — either way indistinguishable in
scale from the true total's `0.43 N`. It repairs the extreme half at the same time,
since the two sum to the true total. So the split **is** usable, after main-term
subtraction and only then. See
[`research/SIGNED_CANONICAL_HEIGHT.md`](research/SIGNED_CANONICAL_HEIGHT.md) §4.

### Do not repeat this route by

- bounding the **raw** balanced and extreme parts separately and adding them: both are
  `n^{0.6}` too large, so the sum of any two valid bounds misses the target by that
  factor no matter how sharp each one is — subtract `Cpred` first;
- conversely, reading the frontier table as closing the split: it closes the raw
  split only, and the subtracted version passes on the whole measured range;
- fitting a log-log exponent to any of these prefix series except `C`: they change
  sign repeatedly, `log |prefix|` plunges at each crossing, and least squares then
  reports growth that is not there. An earlier pass recorded `1.338` for `B` and
  `1.406` for `A + B` this way; both are artifacts. Use `|prefix|/N`;
- treating `highBandBlockIncrement_eq_balanced_add_extreme`,
  `beta_symmetric_identity` or `prefixEnergy_add` as reductions: they are exact
  rewritings that say what the object is, and they license no piecewise estimate;
- reading the prefix-Gram scan's long-window bridge failure as closing the sector
  split: that failure is a property of **mean** subtraction, which can only remove a
  drift linear across the window. Substituting the explicit main term `Cpred` holds
  both diagonals at the budget scale where the bridge is two orders above it —
  `0.071/0.253/0.973/1.009` against `0.65/11.14/27.50/105.21` at `N = 1000` to
  `20000` (`scripts/TwoAnchorSlackCoverage/main_term_vs_bridge.c`, which reproduces
  that scan's raw and bridge columns to every reported digit);
- dropping the ledger's cross term or bounding it by Cauchy–Schwarz: `Cross` is the
  dominant term, two to three orders of magnitude above `E(total)`, and
  `|Cross| <= sqrt(E(bal) E(ext))` is near-equality here, so applying it yields
  `E(total) <= (sqrt(E(bal)) + sqrt(E(ext)))^2`, built from two quantities that are
  each already over budget;
- carrying the endpoint-prime characterization outside `0 < d < u`: it genuinely
  fails there, first coprime witness `u = 2`, `v = 9`, `d = 7`;
- quoting the counting theorem `#{Z <= H} <= 1 + floor(H/n)` as controlling the high
  band — it is a low-imbalance statement and says nothing above the threshold.

### Do not repeat the anchor route by

- asserting that anchor selection bounds anything: it converts a signed
  obligation into a magnitude obligation and leaves the shell estimate untouched;
- quoting an all-frozen-anchor constant as progress — `M(2#) = 0` is a frozen
  anchor, a zero anchor is lossless, and the resulting excursion is the whole
  Mertens value, i.e. the original problem;
- assuming completed endpoints bracket the interior excursions of their own
  block;
- treating an unfavourable cross term as a refutation of backward filling: it is
  a demand on the endpoint reserve.

## Acceptance rule for future routes

A proposed route must state:

1. the exact object it changes;
2. why it is not the closed single-prime dyadic Li-residual mechanism;
3. its predeclared numerical or algebraic continue/stop criterion;
4. how coherent and `H=1` behavior are controlled;
5. every boundary or unmatched term;
6. whether the result is an exact identity, finite diagnostic, sufficient
   criterion, or open analytic premise.

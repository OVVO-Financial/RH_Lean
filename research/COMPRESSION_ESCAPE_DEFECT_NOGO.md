# Compression-escape defect: diagnostic and no-go

**Status: route killed.** The proposal to replace the signed low/high contraction
by a positive *escape energy* coercivity statement,

```text
Esc_{t,ell}(f) = || (I - P_t) U_ell P_t f ||^2  >=  delta_t || f ||^2
  =>  || P_t U_ell P_t f ||^2 <= (1 - delta_t) || f ||^2,
```

fails for a structural reason that is visible in closed form and confirmed
numerically. The failure is *not* that coercivity is hard to prove. It is that
coercivity, where it holds, is empty, and where it would be useful, it is false.

Diagnostic: `experiments/compression_escape_defect.py` (actual Moebius data,
`N = 2 * 10^7`, repository square-prefix endpoints `X_t = (t+1)^2 - 1`).

## The operator

`U_ell` is the `ell`-adic toggle involution on `N`:

```text
v_ell(n) = 0  ->  ell * n
v_ell(n) = 1  ->  n / ell
v_ell(n) >= 2 ->  n         (fixed; mu = 0 there anyway)
```

This is exactly the transport already formalized in
`RHLean/Proof/SurvivorResiduePrimeToggle.lean`. It is a permutation of `N`,
hence unitary on `l^2(N)`. `P_t` is the orthogonal projection onto the physical
window `[1, X_t]`. The Pythagoras identity

```text
|| P_t U_ell P_t f ||^2 + || (I - P_t) U_ell P_t f ||^2 = || f ||^2
```

is correct, and correct for free: it is orthogonal decomposition plus unitarity.
Everything turns on what `|| . ||` measures.

## T1 -- the escape band carries 100% of the amplitude

Splitting `M(X)` by divisibility and using `mu(ell*m) = -mu(m)` for `ell !| m`:

```text
M(X) = sum_{n <= X, ell !| n} mu(n) - sum_{m <= X/ell, ell !| m} mu(m)
     = sum_{X/ell < n <= X, ell !| n} mu(n).
```

Verified exactly at all 25 tested `(X, ell)` pairs, `X` up to `9,006,000`,
`ell` in `{2,3,5,7,11}`.

The toggle interior cancels *completely*. So the compression defect does not
*bound* `M(X)`; it **is** `M(X)`, rewritten. This is the same first-failure
frontier collapse already proved by `SurvivorPrimeFaceFrontier`, stated in
Mertens coordinates. Retained mass is zero and escape is everything: the
contraction inequality degenerates to `0 <= 0`.

## T2 -- coercivity holds, with an exact constant, and is useless

For the Moebius state `f = mu * 1_W`, the escape fraction is exactly

```text
delta_ell = (ell - 1) / (ell + 1)
```

(measured 0.3333 / 0.5000 / 0.6667 for `ell = 2, 3, 5`, matching to four
places at every tested `X`). So the coercivity the proposal asks for is *true*,
uniform in `t`, and available with no work.

It buys nothing, because the only route from an `l^2` mass contraction to the
amplitude is Cauchy-Schwarz against the window:

```text
|M(X)|^2 <= X * || C f ||^2 <= X * (1 - delta) * ||f||^2,   ||f||^2 ~ (6/pi^2) X.
```

That is a bound of order `X`, against the truth of order `sqrt(X)`:

| X | implied \|M\| | true \|M\| | loss |
|---|---|---|---|
| 1,002,000 | 637,890 | 234 | 2,726x |
| 4,004,000 | 2,549,062 | 195 | 13,072x |
| 9,006,000 | 5,733,410 | 301 | 19,048x |

A full power of `X` is lost at the Cauchy-Schwarz step. This is precisely the
loss that `SurvivorResidueCovarianceCriterion` was written to avoid, reappearing
with `s = X` instead of `s = 2`. The `l^2` norm of the Moebius state is `~0.6X`
whatever the cancellation does, so it carries no information about `M(X)` at all.

## T3 -- sigma_max(P U P) = 1 identically, so delta_t = 0

The requested singular-value experiment has a closed-form answer, and it kills
the route without any numerics.

`U_ell` acts on two-element orbits `{n, ell*n}`. If both endpoints lie in the
window, `P U P` maps that two-dimensional subspace to itself by the swap:
singular values `1, 1`. If `ell*n > X`, the basis vector is annihilated:
singular value `0`. Hence

```text
spec(P_t U_ell P_t) = {0, 1},   sigma_max = 1,   delta_t = 1 - sigma_max^2 = 0
```

for every `t` and every `ell` with `ell <= X_t`. At `X = 9,006,000, ell = 2` the
`sigma = 1` eigenspace has dimension `3,650,010` against a kernel of `1,824,977`.

So uniform coercivity `Esc(f) >= delta ||f||^2` with `delta > 0` is **false**:
any `f` supported on an intact orbit has `Esc(f) = 0` exactly. Coercivity holds
only for particular states -- and by T1, for the state that matters it holds
with `delta` so large that the retained part is zero and no information remains.

The route fails the kill criterion stated in the proposal itself ("if
`sigma_max -> 1` and its extremizer resembles the actual Moebius trajectory,
kill immediately"). It is worse than that: `sigma_max = 1` exactly, not
asymptotically, and the intact-orbit extremizers are the generic state.

## T4 -- the toggle strictly worsens the normalized discrepancy

The amplitude is preserved and the support shrinks, so the normalized
discrepancy `|mass| / sqrt(support)` moves the wrong way, by exactly
`sqrt((ell+1)/(ell-1))`:

| ell | measured ratio | sqrt((ell+1)/(ell-1)) |
|---|---|---|
| 2 | 1.7321 | 1.7321 |
| 3 | 1.4142 | 1.4142 |
| 5 | 1.2247 | 1.2247 |

## T5 -- the logarithmic ceiling of iterated toggles

Iterating toggles over all primes `<= y` leaves the sieve support
`A_y = {n <= X : P^-(n) > y}`. At `X = 9,006,000`:

| y | \|A_y\| / X | 1/log y | signed mass | \|mass\|/sqrt\|A_y\| |
|---|---|---|---|---|
| 2 | 0.50000 | 1.44270 | -255 | 0.12 |
| 11 | 0.20779 | 0.41703 | -5,318 | 3.89 |
| 101 | 0.11919 | 0.21668 | -151,983 | 146.69 |
| 1,009 | 0.07754 | 0.14458 | -507,222 | 606.96 |
| 100,003 | 0.06587 | 0.08686 | -593,236 | 770.22 |

Support tracks Mertens' `1/log y`. Reaching `sqrt(X)` support would need
`log y ~ sqrt(X)`, i.e. `y ~ exp(sqrt(X))`, unreachable by toggles over primes
inside the window. Meanwhile the normalized discrepancy of the surviving object
*inflates by a factor of ~6000* while the support shrinks only ~15x.

**Each toggle stage buys a factor of `log`, and costs a power of cancellation.**
This is the quantitative signature of the recurring duality: it is not an
artifact of presentation, it is the per-stage exchange rate of the entire
toggle/sieve family. It is consistent with the empirical inflation constant
`A_q^emp < 3.7` recorded in `research/TWO_ANCHOR_SLACK_COVERAGE.md` -- inflation
per stage strictly above 1.

## Why this was predictable: the parity problem

Every identity of the form "toggle one prime, the Moebius sign flips" is
**parity-blind**. It cannot distinguish integers with an even number of prime
factors from those with an odd number -- which is exactly the quantity `M(X)`
measures. This is the classical parity obstruction of sieve theory. The
"parity algebra" row of the duality table is not one instance among nine; it is
the *reason* for the other eight.

The escape-energy framing does not escape it. Making the defect positive does
not add information; it relocates the same signed sum. The recurring low/high
duality is the parity problem re-expressed in each successive coordinate system,
and no re-coordinatization within the single-variable toggle family can reach
the square-root scale.

## The channel-space variant is also dead

T2's objection is the dimension of the norm, and that objection weakens on a
low-dimensional channel space, where the Cauchy-Schwarz tax is the channel count
`s` rather than `X`. This is the setting of
`SurvivorResidueCovarianceCriterion`, which pays only `s = 2`. On channel space
`SurvivorResiduePrimeToggle` gives the transport

```text
u  |->  ell^2 * u + (1 - ell^2) * q^2   (mod s),
```

so `ell^2 = 1 mod s` makes the toggle act as `-I`, which commutes with every
projection and has compression defect identically zero. The remaining hope was
`ell^2 != 1 mod s`, where the transport genuinely moves fibres.

That hope is false, and for an exact reason rather than a statistical one.
Diagnostic: `experiments/channel_toggle_defect.py`.

**S1. The transport is an isometry of channel space.** Whenever
`gcd(ell, s) = 1` the transport is a *permutation* of `Z/s`, so bucketing by the
transported residue is a relabelling of bucketing by the untransported one and
the two channel vectors have identical norm. Verified exactly in all 24 tested
`gcd = 1` cases -- **for fibre-moving and fibre-preserving `ell` alike**. A
permutation is an isometry, and an isometry has zero compression defect. The
`ell^2 = 1` versus `ell^2 != 1` distinction is therefore invisible to the energy:
it was never the relevant dichotomy.

**S2. The measured "retained/input" ratio is only a change of scale.** Given S1,
`rho = ||retained||^2 / ||input||^2` reduces to the ratio of channel energies at
scales `X/ell` and `X`, carrying no information about the toggle, the
projection, or their commutator. It behaves accordingly: normalized by the
trivial `1/ell` scale factor it ranges over `0.19` to `27.2`, and at
`X = 9,006,000` the raw ratio **exceeds 1 in 5 of 24 cases** -- retained energy
above input energy, which no genuine compression can produce.

**S3. The one norm drop is a channel merge.** When `gcd(ell, s) = g > 1` the
transport collapses `Z/s` onto a subgroup of index `g` and the norm does fall --
but the result is *exactly* the coarser partition mod `s/g` (verified exactly in
all three such cases). That partition is available directly with no toggle, and
it reduces `sum_u a_u^2` while preserving `sum_u a_u`: bookkeeping, not
cancellation.

So the escape-energy mechanism has no surviving form inside the single-variable
toggle family.

## What this does not kill

**Bilinear (Type-II) structure.** Power savings in `sum mu(n)` classically
require two free variables, not one toggled prime. The obstruction above is
specific to compressions of a *single-variable* transport: T3 kills it on the
window state, S1 kills it on channel space, and both failures trace to the same
source -- a one-variable toggle is a permutation, and permutations do not lose
energy. Nothing in the current architecture is bilinear, and that is the actual
gap.

## Recommendation

Do not build the compression operator on the survivor or degree-one state as
proposed (step 1 of the plan): T3 gives the answer before any code is written,
and the singular-value experiment of step 3 has the closed-form answer
`sigma_max = 1`, `delta_t = 0`.

Do not fall back to the channel-space version either: S1 shows the defect is
zero there by permutation-invariance, independently of the `ell^2 = 1 mod s`
condition that the fallback was designed around.

The toggle family is closed. Recording it as a formal no-go alongside
`PrimeBoundaryCollisionQuotientNoGo` is worthwhile -- both the escape identity
(T1) and the intact-orbit obstruction (T3) are short, finite, and kernel-checkable:

```text
mertensSummatory X = sum over {n in (X/ell, X] : ell !| n} of mu n
exists f, ||f|| = 1 and Esc_{X,ell}(f) = 0          (so no delta > 0 coercivity)
```

The `sigma_max = 1` statement is the one worth having in Lean, because it closes
the whole family rather than one construction.

---

# Follow-up: the reported degree-one gap, the R-2H ratio, and the bilinear opening

Three further measurements, prompted by follow-up experiments.

## The degree-one Walsh sigma ~ 0.283 is sign algebra, not geometry

Diagnostic: `experiments/walsh_degree_one_average.py`, which reproduces the
reported value independently (0.28332 against 0.283, and 0.08839 for the (3,5)
average).

On squarefree support write `chi_p(n) = -1` if `p | n`, else `+1`. Then
`chi_p(U_p n) = -chi_p(n)` and `chi_q(U_p n) = +chi_q(n)` for `q != p`, so each
toggle negates exactly its own coordinate on the degree-one span. Averaging `k`
toggles over the span of the same `k` characters therefore gives
`((k-2)/k) * I`:

```text
k = 3, toggles {2,3,5}  ->  1/3 = 0.3333    (reported 0.283)
k = 2, toggles {3,5}    ->  0               (reported 0.08 - 0.12)
```

Measured on the *interior* -- the states whose complete toggle cube lies inside
the window, where the physical projection is inert -- the value is 0.33333 and
0.00000 to five places. The window moves 0.3333 to 0.2833: a 15% effect.

So the gap is ~85% pure linear algebra, holds on any space, and does not depend
on `t`. That is why it looked "strikingly stable" across `t = 64 ... 2048`:
genuine arithmetic quantities do not behave that way. And an average of toggles
is not a transport -- no identity connects `(U_2+U_3+U_5)/3` back to `M(X)`, so
contracting it contracts nothing that is needed. The `k = 2` case makes this
plain: it achieves `sigma = 0`, a perfect gap, and proves nothing at all.

## The R-2H amplitude ratio is a measurement of M(X), not a mechanism

`PrimeWheelThreeSlotRecovery.lean` proves `raw - 2*smooth = mu` pointwise, hence
`R - 2H = M` exactly. Everything else follows from that identity plus the
relative sizes:

* `1 - cos(R, 2H) ~ (1/2)|R-2H|^2 / |R|^2`, so `cos = 0.9999894` and the
  amplitude ratio `rho_R ~ 0.003` are the same measurement reported twice;
* both are forced by `|M(X)| << |R(X)|`, i.e. by the Prime Number Theorem. They
  are not evidence at the square-root scale.

Diagnostic: `experiments/three_slot_smooth_core_scale.py`, which reproduces the
note's `x = 10^7` values (`R - 2H = (459, 468, 110)`, total `1037 = M(10^7)`).

The number that decides the route is the size of the channels themselves:

| X | \|sum H_j\| | sqrt(X) | \|H\|/sqrt(X) |
|---|---|---|---|
| 10^4 | 125 | 100 | 1.25 |
| 10^5 | 919 | 316 | 2.91 |
| 10^6 | 6,356 | 1,000 | 6.36 |
| 10^7 | 47,293 | 3,162 | 14.96 |

`|H|/sqrt(X)` grows by a steady factor of ~2.3 per decade, giving a local
log-log slope of ~0.86 with no sign of levelling. So `M = R - 2H` writes a
target of size `X^0.5` as the difference of two channels of size `X^0.86`, and
`rho_R ~ X^{0.5-0.86} ~ 0.003` at `X = 10^7` is exactly that exponent gap --
which is why the ratio *improves* with `X`. A shrinking `rho_R` is the channels
growing away from the target, not a contraction.

Getting `M` out of this decomposition needs `R` and `2H` to relative precision
`X^-0.36`, finer than the channels' own scale; and `|H| <= X^{1/2+eps}` is
itself a Moebius sum over smooth numbers, no easier than the Mertens bound
sought.

## The bilinear (c,q) opening: right diagnosis, and the precise obstruction

The Type I / Type II reading is correct and is a real improvement on the
low/high framing. `TwoABPrimeDilation.lean` and
`PrimeDilateCofactorPrimeWindows.lean` do supply the exact cofactor-first
reindexing with the reciprocal window and the PNT-centered discrepancy, as
described.

Diagnostic: `experiments/cofactor_prime_bilinear_cost.py`, with
`D(c) = primeCount(W(c)) - singletonLiMass(W(c))` and
`B = sum_{c<R, p!|c} mu(c) D(c)`:

| R | X | S_signed | S_abs | S_abs/R |
|---|---|---|---|---|
| 800 | 639,999 | 19.2 | 870.7 | 1.09 |
| 1,600 | 2,559,999 | -166.5 | 2,506.6 | 1.57 |
| 3,200 | 10,239,999 | -587.1 | 5,931.4 | 1.85 |
| 4,400 | 19,359,999 | 701.5 | 9,797.9 | 2.23 |

**The good news is real:** `S_signed` stays at or below the square-root target
at every scale, roughly an order of magnitude below `S_abs`. The reindexing does
not destroy the cancellation -- unlike the toggle routes, this decomposition
keeps the signed object at the right scale.

**The obstruction is the kernel.** `K(c,q) = 1[q in W(c)]` is nonnegative, and
for any nonnegative kernel

```text
sup_{|alpha_c| <= 1, |beta_q| <= 1} |sum_{c,q} alpha_c beta_q K(c,q)| = sum K,
```

attained at `alpha = beta = 1`. So no bound beating the trivial one holds for
general bounded coefficients. Concretely, Cauchy-Schwarz over `c` produces the
off-diagonal correlations `sum_c K(c,q1) K(c,q2) = #{c <= X/max(q1,q2)}`, which
for `q1, q2 ~ Q` is the same size as the diagonal: **zero Type II saving**.
Bilinear savings come from an *oscillating* kernel -- `e(alpha mn)`, `chi(mn)`,
`(mn)^{-it}` -- which is what Vinogradov/Vaughan exploit and what a hyperbola
indicator does not provide. Centering `beta` makes the coefficient signed but
leaves the kernel nonnegative, and collapses the `q`-sum to one number per `c`,
returning a Type I sum.

`S_abs` grows like `R^1.313` in the tested range (`R^1.5 = X^0.75` predicted
asymptotically under RH), against the `R^1.0` target. So any step taking
absolute values inside the `c`-sum fails by `X^0.157` already, and by `X^0.25`
asymptotically.

## Where that leaves the two bilinearizations

The `c x q` factor side has a nonnegative kernel and therefore no Type II
content on its own. The `r x s` spectral side of `FiniteTorusFourierPairing` is
the more promising of the two precisely because its kernel *does* oscillate
(incomplete quadratic Gauss sums `G_I(r-s)`). But that is also where classical
analytic number theory already operates, and unconditionally it reaches
`X exp(-c (log X)^{3/5})`, not `X^{1/2+eps}`; the remaining distance is
zero-density input, not bookkeeping.

**The single cheap experiment that decides the r x s route** is off-diagonal
decay of the quadratic kernel: measure

```text
G_I(r - s) / sqrt(G_I(0) G_I(0))
```

over the physical interval `I` and the wheel modulus `Q`. If it decays like
`|r-s|^{-1/2}` (square-root Gauss-sum cancellation) across the relevant range,
a large-sieve saving is available and the route is worth building. If it stays
`O(1)` off-diagonal -- as the hyperbola kernel does -- the second
bilinearization is closed for the same reason as the first, and the honest
conclusion is that the architecture needs analytic input it does not currently
contain.

---

# Follow-up: the balanced/coherent bilinear centering split

Diagnostic: `experiments/balanced_bilinear_centering_check.py`.

## The identity is exact

```text
mu(u) mu(v) 1[u prime or v prime]
  = -mu(u) 1_P(v) - mu(v) 1_P(u) - 1_P(u) 1_P(v)
```

Verified exhaustively over all 40,000 pairs `u, v <= 200`, zero mismatches. Four
cases on `(u prime?, v prime?)`; the third term is the inclusion-exclusion
correction for the both-prime overlap. The centering
`beta = beta_coh + beta_II` via `1_P = rho + e` then follows by expansion, and
`beta_II` is genuinely two-free-variable and centered in both.

This is the first object in the programme with real Type-II shape, and unlike
every toggle route it does not destroy the cancellation.

## But the reported normalized energies are not flat

The obligation is `E_loc <= H N^{2+eps}` with `H = N`, i.e. the tabulated
`E_loc / N^3` column must be **flat** -- a fitted power growth is a failure of
the obligation, not a blemish.

| N | C | G | actual | C/actual | G/actual |
|---|---|---|---|---|---|
| 256 | 0.102 | 0.195 | 0.052 | 1.96 | 3.75 |
| 512 | 0.066 | 0.159 | 0.074 | 0.89 | 2.15 |
| 1,024 | 0.120 | 0.377 | 0.122 | 0.98 | 3.09 |
| 2,048 | 0.200 | 0.315 | 0.078 | 2.56 | 4.04 |
| 4,096 | 0.185 | 0.237 | 0.065 | 2.85 | 3.65 |
| 8,192 | 0.403 | 0.493 | 0.076 | 5.30 | 6.49 |

```text
C ~ N^+0.432    G ~ N^+0.233    actual ~ N^+0.044
C/actual ~ N^+0.388             G/actual ~ N^+0.189
```

The `actual` column is flat, as it must be. Both new pieces grow. Dropping the
last point still leaves `C ~ N^0.33`.

**The gain is real and large:** the old split needed cancellation of order
`2689/0.076 ~ 35,000x`; the new one needs `5.3x` at `N = 8192`, about 3.8 orders
of magnitude better. But the residual requirement is *growing* at `~N^0.39`, so
the cancellation between `C` and `G` has been reduced in size, not eliminated in
kind. That is the same disease as the balanced/extreme cross-term, four orders
of magnitude smaller.

## An independent probe of the Type-II object disagrees

Taking the balanced region as `n = u*v` with both factors within a factor 2 of
`sqrt(n)` over `n in [R^2, (R+1)^2)`, and forming the translated-prefix energy of
`C_R = sum_balanced beta_II` with the same `H N^2` normalization:

| N | E_loc(C)/N^3 | E_loc(actual)/N^3 |
|---|---|---|
| 128 | 1.8516 | 0.1241 |
| 256 | 1.3500 | 0.0525 |
| 512 | 1.5700 | 0.0738 |
| 1,024 | 1.7417 | 0.1217 |

```text
C ~ N^-0.005     actual ~ N^+0.041
```

**Flat.** The absolute level differs (this is a different balanced region, and
not the repository's), so only the exponent transfers -- but on this reading the
centered Type-II object does not grow at all over `N = 128 ... 1024`.

## What to do about the disagreement

Two readings of the same object give `N^+0.43` and `N^-0.005`. Possible causes:
different balanced regions; the growth living in the `G`-matching rather than in
`C`; or noise (6 non-monotone points on one side, 4 small-`N` points on the
other). This is not resolvable by argument.

**The decisive test is cheap and should come before any Lean.** Extend the
reported table to `N = 16384, 32768, 65536` and check whether the `C` and `G`
columns flatten. Separately, split the growth: recompute `C` alone under the
repository's exact balanced region, without the `G`-matching, to see which of
the two pieces carries the `N^0.4`.

If both columns flatten, the pair of obligations is the right target and
`BalancedPrimeBilinearCentering` is worth formalizing. If `C/N^3` keeps tracking
`N^0.4`, then `E_loc(C) << H N^{2+eps}` is false as stated and the split needs
rebalancing before it is formalized -- the algebra would still be correct, but
the division of labour between `C` and `G` would be wrong.

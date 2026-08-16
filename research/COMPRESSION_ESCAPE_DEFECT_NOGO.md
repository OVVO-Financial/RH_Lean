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

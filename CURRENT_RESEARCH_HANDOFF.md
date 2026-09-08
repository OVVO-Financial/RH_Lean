# Current RH_Lean research handoff

This file records the current mathematical frontier for any research agent continuing the repository. It is intentionally model-agnostic.

## Governing rule

Do not search for a new coordinate system first. The recent formalization has proved that several historically separate descriptions are exact representations of the same signed endpoint/run object. The task is now to exploit the strongest theorem available in each representation on that common carrier.

Keep the proof elementary and Eulerian. The genuine arithmetic operation is adjoining a fresh prime.

## Current prime-wheel frontier: collapse every signed band before estimating

PR #604 now goes beyond the finite 2310 overlap.  The separate-band route is
formally spent as a source of asymptotic gain: its density contraction is paired
with child-band growth, and its endpoint error grows with the wheel.  The right
object is the exact signed aggregate before any band norm is taken.

`RHLean.Proof.PrimeWheelRoughSeatCorrelation` defines the truncated signed wheel
kernel

```text
K_S(X) = sum_{d | primorial(S), d <= X} mu(d)
```

and proves the exact fresh-prime recurrence

```text
K_{S union {p}}(X) = K_S(X) - K_S(floor(X/p)).
```

Fubini reindexing then collapses all divisor bands onto one physical rough-seat
carrier:

```text
M(B) = sum_{B/W < n <= B, (n,W)=1} mu(n) * K_S(floor(B/n)),
W = primorial(S),
```

for every nontrivial finite prime wheel.  The complete-divisor region below
`B/W` vanishes exactly, so no absolute value, residue-density estimate, or
wheel-depth loss is used to reach this correlation.

The square-root specialization is kernel-checked in
`research/PRIME_WHEEL_ROUGH_SEAT_SQRT_SPECIALIZATION.lean`.  If
`S = primesUpTo R` and `B = R^2-1`, every rough seat above `R` is prime and its
reciprocal kernel cutoff is below `R`, hence already the ordinary lower Mertens
prefix.  Therefore the full root wheel collapses back to the known high-prime
transport

```text
M(R^2-1) = K_R(R^2-1)
             - sum_{R < q <= R^2-1, q prime} M(floor((R^2-1)/q)).
```

This is an important no-go for *completing* the wheel: at the full root cutoff
the outer Mobius field has become the constant prime sign `-1`, so the new
bilinear parity information has been spent.

The stronger synthesis is kernel-checked in
`research/PRIME_WHEEL_ROUGH_SEAT_FROZEN_BRIDGE.lean`: by induction on fresh
prime insertion,

```text
K_S(X) = frozenPrimeUniverseMass(S,X)
```

for every finite prime set.  Thus the image-derived rough-seat kernel is
literally the repository's existing frozen prime cube.  All frozen-window,
first-owner, and Go-wall recurrences can therefore be used on the new
correlation without another coordinate change.

The genuinely new quantitative target is consequently a **proper subwheel**.
For every `Y` the exact square-endpoint coordinate

```text
sum_{n <= R^2-1, (n,primorial(primesUpTo Y))=1}
  mu(n) * frozenPrimeUniverseMass(primesUpTo Y, floor((R^2-1)/n))
```

is still exactly `M(R^2-1)`.  Choosing `Y < R` deliberately retains composite
rough seats, hence a nonconstant outer Mobius factor.  This is the signed
correlation to estimate; enlarging the wheel itself is only an exact change of
coordinates.

Targeted hosted CI is green through the finite interval count, 210 staircase,
2310 overlap identity, signed aggregate, truncated kernel, promoted rough-seat
correlation, square-root specialization, and frozen-cube bridge.  No new power
saving or RH closure is claimed by these exact identities.

## Earlier finite-wheel continuation: explicit counts and a signed 2310 overlap

`RoughWheelFiniteCounting.lean` injects each interval into its intersecting
wheel periods and reduced residues.  If `r(W)` is the number of reduced
residue classes, the finite, wheel-uniform bound is

```text
card roughWheelInterval(W,a,b) <= r(W)/W * (b-a) + 2*r(W),  a <= b.
```

`PostRootCovarianceWheelCounting.lean` applies this after the exact signed
wheel identities. It gives the following explicit Mertens majorants and
transfers each to `E(W) <= majorant(W)^2/2` by the existing Bessel theorem:

```text
6:     |M(B)| <= (2/9) B + 9
30:    |M(B)| <= (16/75) B + 66
210:   |M(B)| <= (256/1225) B + 770
2310:  |M(B)| <= (17648/88935) B + 15364
```

The last estimate uses a new exact signed cancellation. Adjoining `11` to the
210-wheel creates a negative band `(B/22,B/11]`, overlapping the positive
15-band `(B/30,B/15]`. Their common interval `(B/22,B/15]` cancels before
absolute values. This reduces the 2310 leading coefficient from `6144/29645`
to `17648/88935`, a gain of `16/1815`. The exact overlap-cancelled identity was
also checked numerically at every integer endpoint from 0 through 100000;
that finite computation is a sanity check, not a substitute for the kernel.

The elementary factor audit reuses `PrimorialReciprocalMobiusFactorization`:
separate-band counting has density factor `1-1/p` but gains child interval
length `1+1/p`. Its leading coefficient is therefore

```text
c(P) = (1/4) * prod_{p in P} (1 - 1/p^2),  P the selected odd primes.
```

An elementary finite telescope proves `c(P) >= 1/6` even when all integers
at least three are allowed as factors. Thus the separate-band estimate alone
cannot force a power saving by enlarging the wheel. This is NOT a lower bound
on Mertens and NOT an obstruction to signed correlation cancellation.

## Current continuation: the tower is one proposition, and the exchange rate is exact

`PostRootCovarianceGlobalExponentTransfer.lean` supplies the return path that
every reduction from #596 to #602 was missing, and thereby settles what the
record machinery can and cannot do to the unconditional global exponent.

### The return path is one line

In the compiled Bessel identity

```text
2*E(W) = M(W)^2 - complementDiagonalResidual(W) - familyMertensSquareEnergy(W)
```

both subtracted terms are already proved nonnegative.  Hence, unconditionally,
with no cancellation, no record hypothesis and no sieve,

```text
E(W) <= M(W)^2 / 2.
```

### Consequence: every seam in the tower is the same proposition

```text
MertensPowerSavingStatement                          (|M(x)| << x^((1+eps)/2))
  <-> MertensEnergyBoundedStatement
  <-> MertensSquarePowerEnvelopeBoundedStatement
  <-> PostRootCovariancePowerRemainderStatement
  <-> PostRootCovariancePowerEnvelopeBoundedStatement
  <-> PostRootCovariancePowerRecordExcessBoundedStatement
  <-> PostRootFallingEnergyFiniteDifferencePowerStatement
```

All of these are now compiled bi-implications.  Nothing in the post-root,
LCM-wall, envelope, or record layers has cost anything, and nothing in them has
gained anything either.

### The exchange rate, and the no-go it implies

`postRootCovarianceRemainder_le_of_mertensPowerBound` is pointwise and
unconditional:

```text
|M(W)| <= B * W^theta   ==>   E(W) <= (B^2/2) * W^(2*theta).
```

Together with the equivalence above the rate is exact.  No post-root, wall,
envelope, or record reduction can improve the unconditional global exponent
without an improvement of the Mertens exponent itself.  Record that no-go; do
not re-derive a weaker version of it.

# Cumulative carriers: pairing, adaptive matching, and lifetimes

**Status: exact layer formalized for all three notions. The raw prefix carrier
is CLOSED for both matching notions, by two proved no-go theorems and their
finite diagnostics. The lifetime notion is open and lives on a different
carrier.**

Three different things were being conflated. They are separated here, and only
the first was what the initial branch proved.

```text
fixed-prime pairing      : cumulative interval pairing under one frozen prime
adaptive matching        : carrier-wide matching, prime chosen per state
lifetime cancellation    : birth/death over square time
```

## 1. Fixed-prime pairing — proved, and narrower than it sounds

For a prime `p` define the carrier toggle

```text
tau_p(n) = n * p    if p does not divide n
           n / p    if p divides n but p^2 does not
           n        if p^2 divides n.
```

`RHLean/Proof/GlobalPrefixCarrierOthello.lean` proves this is an involution of
`N` whose moving states reverse the Moebius sign and whose frozen states carry
no Moebius mass, hence for an **arbitrary** finite region `S`

```text
sum over S of mu = sum over { n in S : tau_p n not in S } of mu.
```

It is exact, it is genuinely cumulative, and the completion form
(`sum_moebius_eq_neg_sdiff_of_toggleClosed`) is useful. On the prefix carrier
`(L, x]` the surviving set is two explicit walls
(`RHLean/Proof/PrefixCarrierOthelloWalls.lean`).

**What it does not prove.** For a fixed `p` every orbit of `tau_p` is a two
cycle or a fixed point. There are no long alternating components and no
trajectories, so no statement about path length or about birth-to-capture
cancellation follows from it. The earlier prose in this repository claiming
otherwise was wrong and has been corrected in place.

Likewise, in `RHLean/Analysis/PrimeWheelRunOthelloBoundary.lean` the square-run
statement composes two independent steps: the **pre-existing telescope**
`sum Delta_j = M(X_b) - M(X_{a-1})` removes the block count, and the pairing
then acts on the resulting cumulative arithmetic interval. `(X_{a-1}, X_b]` is
an interval of integers, not a space-time carrier of survivors.

## 2. Adaptive carrier-wide matching — formalized, and the raw carrier is dead

`RHLean/Proof/AdaptivePrimeMatching.lean` gives the notion the no-liberty
architecture actually uses. `AdaptivePrimeMate S m` asks that `m` preserve `S`,
be involutive on `S`, and move only along prime-toggle edges — with the prime
free to depend on the state, subject to both endpoints choosing each other.
Sign reversal is then a *consequence*: a toggle that moves cannot be a square
hit.

`HasLiberty S n` says some prime edge at `n` moves and lands inside `S`, and
`trueNoLibertyBoundary S` collects the states with no legal move left anywhere
in the geometry. This is the right boundary notion, and it is strictly stronger
than "my mate under one selected prime is outside". A no-liberty state is fixed
by every adaptive mate, so the true boundary always sits inside the fixed set,
and the two coincide exactly when the mate is liberty exhausting — in which case

```text
R_k(x) = sum over the true no-liberty boundary of mu.
```

That is the target statement. **On the raw prefix carrier it cannot hold**, for
two independent proved reasons.

* `not_libertyExhausting_Ioc_of_sum_ne_zero`. Every squarefree site of `(0, x]`
  has a legal move: divide out its least prime factor, or at `1` multiply one
  in. So the true no-liberty boundary of `(0, x]` consists of square hits only
  and carries **no Moebius mass at all**. A liberty-exhausting mate would force
  `M(x) = 0`.
* `card_topHalfPrimes_le_fixedCard_succ`. A prime `p` with `x < 2p` has exactly
  one legal move in `(0, x]`, namely `p -> 1`: every other prime edge multiplies
  and overshoots `x`. All such primes compete for the single site `1`, and an
  involution serves at most one of them. Hence the fixed set of **any** adaptive
  mate on `(0, x]` has at least `pi(x) - pi(x/2) - 1` states, which is of order
  `x / (2 log x)`, not `x^(1/2+eps)`.

Neither uses an estimate or an asymptotic input.

## 3. Lifetime cancellation over square time — this is where path length drops out

`RHLean/Proof/LifetimeRunCancellation.lean` states the Go theorem on the object
that actually has trajectories. With birth stage `beta` and capture stage
`delta`, the activity indicator is `A_t = 1` exactly when `beta <= t < delta`,
and the run telescopes:

```text
sum over k in [a,b) of (A_{k+1} - A_k) = A_b - A_a.
```

Therefore an atom born after the run starts and captured before it ends
contributes `0 - 0 = 0`. The length `delta - beta` appears nowhere in the
statement or the proof: a stone that lived one stage and a stone that lived ten
thousand stages cost the run the same, namely nothing. The population form says
a run is carried entirely by the atoms alive at one of its two ends.

Two bridges to the repository's own process are proved:

* `isLifetimeActive_of_le_of_birth_le` — for a nonnegative cutoff slope the
  moving-high threshold `2 * Lambda * t` is nondecreasing, so `IsLifetimeActive`
  really is a lifetime *interval*. Death is permanent; there is no resurrection
  between birth and capture, which is what makes the indicator model faithful.
* `sum_lifetimeActiveAtomMass_increment_Ico_eq_birthDeath_endpoints` — the
  aggregate run identity in the existing `Active = Birth - Death` coordinates.

## 4. Finite diagnostics

`scripts/CumulativeOthelloBoundary/peel_diagnostic.py`, at `x = 20000`:

```text
fixed-prime peel      |fixed|/x descends to 0.2047 after p = 19
                      limit (1/4) * prod_{q>=3} (1 - 1/q^2) = 2/pi^2 = 0.20264
prime order           ascending, descending, mixed: |fixed| identical (4048)
maximum matching      exposed = 3314, exposed/x = 0.1657, exposed mass = M(x)
top-half primes       1033 primes p with x < 2p, each with the single move p -> 1
```

Three readings.

* The signed mass never moves under any peel, at any `x` tested. That is the
  exact layer confirming itself.
* The peel **order** is not the free parameter: the repository's own
  chronological matching takes primes in descending order, and on this carrier
  descending, ascending and mixed leave the identical fixed set. The greedy
  frontier destroys liberties by shrinking the carrier, so after the first prime
  almost every remaining edge already points outside.
* Restoring the full state-dependent freedom is **also** not enough. A maximum
  matching in the whole prime-toggle graph — every state free to choose any
  prime edge — still leaves a positive proportion exposed, and the exposed
  signed mass is exactly `M(x)`, as the theorem requires. The structural cause
  is the top-half primes above, which is the Lean no-go.

## What this leaves

The carrier is the free parameter, not the matching and not the prime order. A
raw interval of integers is provably the wrong geometry for either matching
notion: it has a Hall-type bottleneck of density order `1 / log x` that no
adaptive choice can route around. The processed-seat carrier of the no-liberty
architecture restricts which moves are legal and compresses the unmatched states
into root/frontier fibres; that restriction is not a technical convenience, it is
what removes the bottleneck.

The lifetime statement of section 3 is on a different carrier again — canonical
atoms in square time — and is the one place where an interior trajectory of any
length is proved to cost zero.

## Do not repeat this route by

* rerunning the fixed-prime peel at larger `x`, with more primes, or in a
  different prime order: the limiting proportion `2/pi^2` is structural, and
  order independence is measured;
* proposing an adaptive or "smarter" matching on the raw interval carrier: the
  top-half prime bottleneck is proved, and a maximum matching is measured;
* reporting the first peel `x -> x/4` as progress; one bounded factor is not a
  power saving;
* describing a fixed-prime pairing as a birth/death or alternating-path
  cancellation. It is a pairing of two cycles. The lifetime statement is
  separate and lives in `LifetimeRunCancellation`;
* calling a cumulative arithmetic interval a space-time carrier.

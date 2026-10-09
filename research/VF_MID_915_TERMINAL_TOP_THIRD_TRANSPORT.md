# #915 — Full sqrt / half partition, parity owner-2 slice, and Li restoration

Date: October 8, 2026. **Unconditional geometry and exact finite accounting; NOT an RH proof.**
This attacks the cofactor-first Abel route to production `hbalance` and corrects
the original top-third-only presentation: `x/2` is the TRUE full-integer
terminal cutoff; `x/3` applies only after removing owner-2 even sites.
Both cuts must be retained. All comparisons use original VF scalars,
compressed historical anchor, and unchanged NNS denominator.

## 1. The full three prime-factor buckets, plus the parity overlay

At a physical cutoff `X=B^2`, the natural complete-integer partition is:

1. `p<=B=sqrt(X)`: actual low-prime sieve coordinates; EVERY composite
   `n<=X` has a prime factor here. These are the least-prime owners.
2. `B<p<=floor(X/2)`: post-root primes with genuine composite multiples,
   starting with `2p<=X`. Such `p` is a large factor of `2p`, NOT the
   least-prime owner. This is a historical prime/descendant coupling sector.
3. `p>floor(X/2)`: genuinely terminal prime events with NO proper
   integer multiple `c*p<=X` for ANY `c>=2`.

**Parity overlay inside bucket 2:**

- `B<p<=floor(X/3)`: both `2p` and, possibly, `3p` are below `X`;
  more cofactor descendants appear as p decreases.
- `floor(X/3)<p<=floor(X/2)`: the unique proper multiple is
  **`2p`**, which has least-prime owner 2. This is NOT a terminal sector
  in the full integer carrier, although it is terminal after restriction
  to the odd-seat carrier.

The earlier top-third argument proved only that odd descendants cannot
occur. It **did not** justify treating this entire top third as physically
unpaired; the even `2p` parent/child relation must be restored before the
original signed Fubini or NNS payment is attempted.

New exact Lean facts:

- `vfMid915_aboveHalf_noProperMultiple`;
- `vfMid915_middleFull_2q_exists`;
- `vfMid915_aboveThird_onlyDoubleMultiple`;
- `vfMid915_halfRun_floorLiMismatch_eq_upperHalf_add_lower`;
- `vfMid915_halfRun_floorLiMismatch_eq_threeUpperStrata`.

### Why the odd-only top-third observation remains useful

Put `a=floor(R/2)+1`, `B=R+1`, `X=B^2` and `T=floor(X/3)`.
Write `E(n)=pi(n)-floor(Li_2(n))`. The exact primitive mismatch splits as

    E(X)-E(a^2) = [E(X)-E(T)] + [E(T)-E(a^2)].

For any integer q>T and any odd proper cofactor c>=3, we have

    c*q >= 3*(T+1) > X.

Therefore **NO** prime q>T, and indeed no floor-Li-only event at q>T,
can have a proper odd composite descendant c*q in ANY of the historical
square bands r=a,...,R. This is a geometric theorem independent of
prime distribution, with new Lean statements:

- `vfMid915_topThird_noOddDescendant`
- `vfMid915_topThird_notHistoricalOddComposite`
- `vfMid915_halfRun_floorLiMismatch_eq_topThird_add_lower`

in `research/VF_MID_915_TERMINAL_TOP_THIRD_TRANSPORT.lean`.

It is important that this excludes descendants only **up to X**. A
prime q in the top third may act as a small-owner parent at a later
square scale after 3q enters the clock, but such *future* mass cannot be
spent at a first-bad boundary B.

**What does control terminal q itself?** A genuine low-owner sieve. For
B>=4, every q in (T,B^2] satisfies B<q<=B^2. The existing least-prime
factor arithmetic therefore proves

    q is prime  <=>  lowWheelHighSurvivor(B,q).

New theorem `vfMid915_topThird_lowWheelSurvivors_eq_primes` identifies the
entire terminal actual-prime SET with the full low-prime wheel survivors.
This is the viable occurrence carrier for terminal events: ascending
composite removals of the q-sites by small p<=B, not imaginary proper
odd descendants c*q within the earlier half-run. It is an exact sieve,
**not an estimate** of survivors versus Li jumps.

### Exact floor-Li discrepancies in the full buckets at two historical anchors

| Quantity | R=317 | R=1027 |
|---|---:|---:|
| a | 159 | 514 |
| T=floor((R+1)^2/3) | 33,708 | 352,261 |
| H=floor((R+1)^2/2) | 50,562 | 528,392 |
| E(a^2) | -26 | -64 |
| E(T) | -24 | -50 |
| E(H) | -31 | -60 |
| E(B^2) | -41 | -122 |
| q<=X/3, including odd cofactor descendants: E(T)-E(a^2) | **+2** | **+14** |
| X/3<q<=X/2, only even `2q` descendants: E(H)-E(T) | **-7** | **-10** |
| q>X/2, NO proper descendants: E(B^2)-E(H) | **-10** | **-62** |
| Upper-third subtotal E(B^2)-E(T) | **-17** | **-72** |
| Net historical mismatch | **-15** | **-58** |
| Actual top-third primes | 6,076 | 52,454 |
| Top-third floor-Li jumps | 6,093 | 52,526 |

**Corrected finding:** The region above X/3 supplies -17 and -72, but
**part of that discrepancy is still paired physically with even `2q`**:
-7 and -10. The genuinely descendant-free region q>X/2 supplies -10
and -62. The lower region, with odd composite descendants, contributes
+2 and +14. An odd-only cofactor proof cannot control either the
owner-2-only mixed interval or the genuinely terminal prime-only interval
without the corresponding full-carrier arithmetic accounting.

This does NOT say that the lower sector contributes nothing to historical
physical energy, or that its primitive mismatch controls its large
cofactor-weighted composite response. They are different ledgers.

## 2. Correct complementary smooth-sector restoration

For each native square band r, let

    P_r = actual prime seats
    F_r = integer floor-Li prime increments
    G_r = sum over odd 3<=c<=r of actual primes
          in (floor(r^2/c), floor((r+1)^2/c)]
    GL_r = same cofactor count using integer floor-Li jumps
    S_r = r - P_r - G_r
    SL_r = r - F_r - GL_r   (formal Li benchmark, NOT physical smooth set)
    w_r = (2r+1)/(r*log(r^2+r+1/2)).

By unique post-root prime factor geometry G is the number of literal
composite odd physical sites with a unique prime factor >r, and S
is the remaining smooth-odd seat count. The regression independently
checks this using the largest actual prime factor of EVERY odd physical
site, not by defining it as the cofactor complement.

The exact signed restoration is

    (w_r-1)*(P_r-F_r)
      + w_r*(G_r-GL_r)
      + w_r*(S_r-SL_r) = F_r-P_r.

This is algebraic, valid even if SL is negative: it is **not** an
inequality, and supplies no free negative Co/Div payment. It proves
that the large composite cofactor/Li discrepancy has to be accompanied
by the complementary smooth difference when reassembling the original
source. The reference Li smooth seats are NOT extra sieve capacity.

### Full native half-run (original VF charge)

| Component of actual-minus-reference *physical charge* | R=317 | R=1027 |
|---|---:|---:|
| Prime seats, (w-1)(P-F) | +12.253334 | +49.424639 |
| High-prime composites, w(G-GL) | **-80.533792** | **-284.788121** |
| Complementary smooth seats, w(S-SL) | **+83.280459** | **+293.363482** |
| **Reassembled signed moving-owner correction F-P** | **+15.000000** | **+58.000000** |

The raw local absolute cofactor charge (taking absolute values before
time/cofactor cancellation) is **2,205.880216** and **17,884.620225**,
respectively. The sum of absolute *time-telescoped* charges by cofactor
is only **81.263616** and **309.192317**. The native signed high-composite
totals remain **-80.533792** and **-284.788121**: 99.10% and 92.11%
of the sum of the absolute per-cofactor totals. Thus almost all of
the enormous local-composite cancellation happens **within each
cofactor across historical time**, not across cofactor families.
At these two samples, cross-sector smooth restoration is indispensable.

The existing *compiled* native weighted Abel identity is checked again,
independently, for all cofactors with their real VF weights. Summed
across cofactors its boundary/variation decomposition reads

    R=317:  -62.456525 - 18.077267 = -80.533792
    R=1027: -222.749426 - 62.038694 = -284.788121.

This is a decomposition of an actual arithmetic charge, not a sign bound.

## 3. First-bad consequence: a forced terminal-prime discrepancy

At a hypothetical first-bad B for K=2, write J=floor(sqrt(T)),
where T may be either floor(B^2/3) or floor(B^2/2).
The earlier square J^2 is inside the first-bad wall. Define the
uniformly bounded square-endpoint Li/VF bridge
`b_j = floor(Li_2(j^2))-VF_mid(j^2)`. Then (for J>=2):

    |D_B| > 2 B log B,       |D_J| <= 2 J log J,
    |b_B|, |b_J| <= C.

Since J^2<=T<(J+1)^2 and both prime counts and the integer floor-Li
staircase increase by at most one at an integer site above 4,

    |E(T)-E(J^2)| <= T-J^2 <= 2J.

The triangle inequality therefore forces

    |E(B^2)-E(T)|
      > 2 B log B - 2 J log J - 2 C - (T-J^2).

Asymptotically the right side is

    2*(1-1/sqrt(3))*B*log(B) - O(B),

roughly **0.8453 B log B** for T=floor(B^2/3). At the FULL-integer
terminal boundary T=floor(B^2/2), the analogous leading coefficient is
`2*(1-1/sqrt(2)) = 0.585786...`. Both are only necessary lower
bounds if the first-bad hypothesis actually holds.

This is a sign-independent **necessary condition**, not a proved
upper bound. The full terminal interval is `(B^2/2,B^2]`, while
`(B^2/3,B^2/2]` MUST retain its genuine even `2q` descendants.
The missing arithmetic is either an actual-prime discrepancy estimate
strong enough to defeat the full terminal threshold, or a rigorously
favorable *joint signed* comparison including both the owner-2-only
and lower odd-cofactor sectors.
Neither follows from PNT, the finite Li transport pairing statistics,
or the geometry of missing odd descendants.

A general bound of RH order on that terminal relative interval would
itself already be RH-strength (geometrically telescope the intervals),
so it must not be inserted as a disguised assumption.

## 4. Consequences for the production #915 payment

1. The **upper-half terminal prime-only mismatch** must remain a separate
   signed source. For `X/3<q<=X/2`, preserve the distinct genuine
   historical **`2q`, least-owner-2** occurrence; suppressing it through
   an odd-only projection is not a proof of compensation.
2. The **lower cofactor ancestry** cannot be estimated by spending
   historical blockwise absolute mass. First restore the *actual*
   smooth complement with original w_r and original NNS denominator.
3. The opposite-signed observed +2/+14 lower mismatch is not a
   universal inequality. Neither terminal nor descendant-eligible
   transport may be declared small from the exact identity alone.
4. The truly open mathematical requirement remains the
   **first-bad-specific joint signed arithmetic payment** in
   `VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean` at `hbalance`.
   This attack has not proved it; do not claim that cofactor-Abel or
   exact owner-2 correspondence alone controls the terminal discrepancy.

### Reproducible independent audit

`python3 scripts/vf_mid_915_top_third_sector_restoration_regression.py`

Uses genuine sieved primes, integer floor-Li jumps, all odd physical
sites and their largest prime factors, exact cofactor-interval counts,
and native VF weights. It verifies the numerical table, full three-sector
restoration, and every cofactor's Abel endpoint-plus-variation identity.

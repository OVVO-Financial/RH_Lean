# Truncated upper-middle reciprocal packet gate

**Status:** exact packet formalized; quantitative bound remains open.

This note corrects the earlier diagnostic that isolated the middle terminal-flip
sector.  The top sector `X_R/2 < q <= X_R` is dynamically inert but
arithmetically active: its untouched prime seat contributes `-1`.  It is the
leading cancellation partner for the middle and must not be discarded.

Let

\[
X_R=R^2-1,
\qquad
N_R(k)=\#\{q\text{ prime}:R<q\le X_R,\ \lfloor X_R/q\rfloor=k\}.
\]

For a post-root prime in reciprocal layer `k`, the proper-multiple terminal
flips contribute `1-M(k)`, while the untouched prime seat contributes `-1`.
Thus the complete fibre is

\[
\boxed{-M(k)}.
\]

The natural incomplete packet is therefore

\[
\boxed{
U_R(K)=-\sum_{1\le k\le K}N_R(k)M(k),
\qquad K<R.
}
\]

The coordinate `k=1` is the upper block and remains inside the packet from the
start.

## Exact Abel form

Define the clipped post-root prime prefix

\[
P_R(d)
=
\pi\!\left(\max\!\left(R,\left\lfloor\frac{X_R}{d}\right\rfloor\right)\right)
-\pi(R).
\]

Then for every `1 <= d < R`,

\[
N_R(d)=P_R(d)-P_R(d+1).
\]

Finite summation by parts gives

\[
\boxed{
U_R(K)
=-\sum_{1\le d\le K}\mu(d)P_R(d)
+M(K)P_R(K+1).
}
\]

For `K>=1`, separating the unit term gives

\[
U_R(K)
=-P_R(1)
-\sum_{2\le d\le K}\mu(d)P_R(d)
+M(K)P_R(K+1).
\]

Note that `P_R(1)` is the **whole post-root prime prefix**.  The actual top
`k=1` layer is `P_R(1)-P_R(2)`.  The formal packet definition, rather than a
verbal interpretation of the Abel terms, is the safe source of bookkeeping.

These identities are formalized in
`RHLean/Proof/LargePrimeTerminalFlipLayers.lean` on PR #457.

## Finite gate

For each tested `R`, let `K_cross(R)` be the first reciprocal depth for which
`U_R(K) >= 0`, starting from the negative upper block.  Let `K_best(R)` minimize
`|U_R(K)|` over the scanned shallow range.

| `R` | `K_cross` | best `K` | best `|U_R(K)|/R` | best `K/log R` |
|---:|---:|---:|---:|---:|
| 200 | 24 | 24 | 0.0050 | 4.530 |
| 500 | 30 | 29 | 0.0400 | 4.666 |
| 1000 | 31 | 31 | 0.1730 | 4.488 |
| 2000 | 33 | 32 | 0.0290 | 4.210 |
| 5000 | 37 | 36 | 0.0578 | 4.227 |
| 10000 | 43 | 42 | 0.0106 | 4.560 |
| 20000 | 45 | 44 | 0.2198 | 4.443 |
| 50000 | 48 | 47 | 0.1605 | 4.344 |
| 100000 | 49 | 49 | 0.3222 | 4.256 |

Thus the data do **not** support a bounded reciprocal depth.  They support a
slowly growing depth, numerically close to

\[
K_*(R)\asymp 4.3\log R
\]

on the tested range.  This is a diagnostic, not a theorem.

For the dense finite scan `3 <= R <= 5000`, only 13 very small endpoints failed
to cross within the scanned range; from the stable range onward the same
upper-to-middle crossing is persistent.  The largest best-packet ratio observed
in that dense scan was about `0.27 R`.

## Why a fixed K cannot be the asymptotic mechanism

For fixed `K`, ordinary PNT expansion gives

\[
N_R(k)
\sim
\frac{R^2}{2\log R}\frac1{k(k+1)}.
\]

Hence

\[
U_R(K)
\sim
-\frac{R^2}{2\log R}
S_K,
\qquad
S_K:=\sum_{k\le K}\frac{M(k)}{k(k+1)}.
\]

The coefficient has the exact finite Abel form

\[
\boxed{
S_K
=\sum_{k\le K}\frac{\mu(k)}k
-\frac{M(K)}{K+1}.
}
\]

Direct exact arithmetic gives `S_K>0` for every `K<=10000` checked.  Typical
values are

| `K` | `S_K` | `K S_K` |
|---:|---:|---:|
| 50 | 0.0383134 | 1.916 |
| 100 | 0.0212305 | 2.123 |
| 200 | 0.00903583 | 1.807 |
| 500 | 0.00345519 | 1.728 |
| 1000 | 0.00241387 | 2.414 |
| 2000 | 0.000820805 | 1.642 |
| 5000 | 0.000378297 | 1.891 |
| 10000 | 0.000217070 | 2.171 |

So on this range `S_K` behaves numerically like a constant multiple of `1/K`.
Combining this with the prime-count expansion explains why the balancing depth
appears proportional to `log R`.

This does **not** prove `S_K=O(1/K)`.  The exact identity shows that such a claim
is a statement about the reciprocal Möbius sum

\[
\sum_{k\le K}\frac{\mu(k)}k.
\]

The repository currently has the elementary bound

\[
\left|\sum_{k\le K}\frac{\mu(k)}k\right|\le1,
\]

but that is too weak to prove the observed logarithmic balancing depth.

## Route decision

The next analytic target is now sharply separated into two possibilities.

1. **Depth theorem.**  Prove existence/control of a shallow `K(R)` (the data
   suggest `K(R)=O(log R)`) for which the upper and first middle layers balance.
   This requires enough control of the lower-scale reciprocal Möbius coefficient
   and the fixed-ratio prime-count weights.

2. **Direct packet theorem.**  Avoid estimating `K(R)` as an intermediate
   object and prove directly that a deliberately incomplete packet satisfies

   \[
   |U_R(K(R))|\ll R^{1+\varepsilon/2}
   \]

   for an explicit elementary choice of `K(R)`, while preserving the remaining
   reciprocal tail for its separate smooth/cross-root pairing.

A constant `K` is not the viable asymptotic route.  Completing `K` through
`R-1` is also not the route: that recovers the already-known full transport and
erases the restricted nonconstant fibre that this gate is designed to preserve.

The critical invariant is therefore

\[
\boxed{
\text{upper }k=1\text{ boundary}
\;\text{plus a growing but shallow reciprocal packet, kept incomplete.}
}

# Truncated upper-middle reciprocal packet gate

**Status:** eventual shallow crossing formalized; a root-scale packet bound
remains open.

This note corrects the earlier diagnostic that isolated the middle terminal-flip
sector. The top sector `X_R/2 < q <= X_R` is dynamically inert but
arithmetically active: its untouched prime seat contributes `-1`. It is the
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
P_R(d)=
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

`P_R(1)` is the **whole post-root prime prefix**. The actual top `k=1` layer is
`P_R(1)-P_R(2)`. The formal packet definition, rather than a verbal
interpretation of the Abel terms, is the safe source of bookkeeping.

These identities are formalized in
`RHLean/Proof/LargePrimeTerminalFlipLayers.lean` on PR #457.

## Exact finite gate

For each tested `R`, let `K_cross(R)` be the first reciprocal depth for which
`U_R(K) >= 0`, starting from the negative upper block. Let `K_best(R)` minimize
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
| 200000 | 52 | 51 | 1.0795 | 4.178 |
| 500000 | 54 | 54 | 4.6258 | 4.115 |

Two distinct conclusions must therefore be kept separate.

1. The **crossing depth remains shallow**. Through the extended scan,
   `K_cross/log R` continues to drift slowly downward near `4`.
2. The **nearest crossing is not uniformly root-scale**. The strong empirical
   conjecture `min_K |U_R(K)| = O(R)` already fails as a stable numerical law:
   the best shallow residual is about `1.08 R` at `R=200000` and `4.63 R` at
   `R=500000`.

So the finite evidence supports a slowly growing crossing depth, but it does
**not** support the claim that a raw sign crossing by itself proves the desired
packet bound.

For the dense finite scan `3 <= R <= 5000`, only 13 very small endpoints failed
to cross within the scanned range. That small-scale success was useful for
finding the packet, but the extended gate shows it must not be promoted into an
asymptotic bound.

## The endpoint-parametric fixed-depth mechanism

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
-\frac{R^2}{2\log R}S_K,
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

The theorem is parameterized by any fixed `K_0` for which `S_{K_0}<0`; no
particular numerical depth belongs in its statement.  The original finite scan
stopped at `K=10000`, where `S_K` is still positive.  Extending the search gives
one convenient unconditional witness, certified at `K_0=18800` by exact
rational computation:

\[
\boxed{S_{18800}<0.}
\]

The certificate uses `native_decide` after a proved rational Abel identity, so
it contains no floating-point approximation or imported numerical data.
Typical diagnostic values, including the certified depth, are

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
| 18800 | -0.0000190870 | -0.359 |

More generally, let `x_n` be any endpoint sequence tending to infinity and let
`y_n` be any lower prime cutoff satisfying

\[
y_n\le \frac{x_n}{K_0+1}
\]

eventually.  The native PNT gives the formal limit

\[
\frac{U_{y_n,x_n}(K_0)\log x_n}{x_n}\longrightarrow -S_{K_0}.
\]

Thus `S_{K_0}<0` forces eventual positivity at `K_0`.  The depth-one packet is
the negative, nonempty Bertrand block whenever `y_n<=x_n/2`; taking the least
nonnegative depth gives a genuine crossing at some `K<=K_0`.  If also
`K_0<y_n` eventually, then for **every** `C>0`, eventually

\[
K<y_n,qquad K\le C\log x_n,qquad
U_{y_n,x_n}(K-1)<0\le U_{y_n,x_n}(K).
\]

The square construction is only the specialization

\[
x_R=R^2-1,qquad y_R=R.
\]

For every fixed positive `K`, this recovers the former limit

\[
\frac{U_R(K)\log X_R}{X_R}\longrightarrow -S_K.
\]

This is formalized in
`RHLean/Analysis/SquareRootShallowReciprocalCrossing.lean`.  The primary theorem
`endpointPacket_eventual_log_crossing_of_coefficient_neg` is the general
`(x_n,y_n,K_0,C)` statement above.  Its square-endpoint corollary
`squareRootPacket_eventual_log_endpoint_crossing` states, for every `C>0`,

\[
\exists R_0\;\forall R\ge R_0\;\exists K<R,
\quad K\le C\log X_R,
\quad U_R(K-1)<0\le U_R(K).
\]

The exact `S_{18800}<0` computation now appears only in the final witness
corollary that discharges the general coefficient hypothesis.  It proves the
stronger absolute bound `K<=18800`, but `18800` is not part of the architecture
and is not a claim about the typical crossing depth.

## Why the observed depth is near `4 log R`

Put `L = log X_R`. Expanding the reciprocal prime density formally gives

\[
\frac1{\log(X_R/d)}
=\frac1L+\frac{\log d}{L^2}+\cdots.
\]

The first two truncated coefficients are

\[
S_K=
\sum_{d\le K}\frac{\mu(d)}d-\frac{M(K)}{K+1},
\]

and

\[
B_K=
\sum_{d\le K}\frac{\mu(d)\log d}{d}
-\frac{M(K)\log(K+1)}{K+1}.
\]

Exact finite arithmetic gives

| `K` | `K S_K` | `B_K` |
|---:|---:|---:|
| 20 | 1.843 | -0.717 |
| 30 | 1.989 | -0.774 |
| 40 | 2.019 | -0.814 |
| 42 | 2.049 | -0.819 |
| 49 | 1.935 | -0.845 |
| 50 | 1.916 | -0.849 |
| 100 | 2.123 | -0.903 |
| 200 | 1.807 | -0.951 |
| 500 | 1.728 | -0.978 |
| 1000 | 2.414 | -0.984 |
| 10000 | 2.171 | -0.998 |

On this finite range, `S_K` behaves roughly like `2/K` while `B_K` approaches
`-1`. Balancing the first two terms

\[
\frac{S_K}{L}+\frac{B_K}{L^2}
\]

therefore predicts

\[
K\approx 2L\approx4\log R,
\]

which explains the observed crossing depths remarkably well.

This remains a **diagnostic explanation of the small finite crossing**, not the
mechanism used by the eventual theorem. The eventual theorem needs no
quantitative rate for a growing reciprocal coefficient: it uses the one exact
negative coefficient at `K=18800` and qualitative PNT at finitely many fixed
dilations.

The repository already has the elementary bound

\[
\left|\sum_{d\le K}\frac{\mu(d)}d\right|\le1,
\]

and it formalizes the complementary first logarithmic Möbius moment in
`NativePNTMobiusMoments`. Those are exactly the right lower-scale objects, but
the currently proved bounds are too weak to force the observed depth or a
root-scale packet residual.

## Direct cap interpretation

The Abel boundary cancels every prime below `X_R/(K+1)`. Hence, after swapping
the finite sums, the same packet can be read as the Möbius mass of the shallow
high-prime cap

\[
\boxed{
U_R(K)
=
\sum_{d\le K}
\sum_{\substack{X_R/(K+1)<q\le X_R/d\\q\text{ prime}}}
\mu(dq).
}
\]

Because `K<R` and `q>X_R/(K+1)>R`, the prime `q` is fresh and larger than the
cofactor, so `mu(dq)=-mu(d)` whenever the cofactor survives. This is the direct
upper-plus-middle object; it is not a difference of independently estimated
upper and middle masses.

This cap form is the more promising object for a direct argument, because it
preserves the exact cancellation that motivated the truncation while avoiding
a separate estimate of the huge upper block.

## Route decision

The analytic target is now sharper than the initial proposal.

1. **Crossing-depth theorem:** proved, in the stronger eventual form
   `K_cross(R)<=18800`, hence in particular `K_cross(R)=O(log R)`.
2. **Nearest-crossing root bound:** rejected as a naive finite conjecture. The
   extended exact gate already shows `min |U_R(K)|/R` growing beyond `1` and
   then `4`.
3. **Direct signed-cap theorem:** the viable quantitative target. Estimate the
   entire cap before splitting its prime-count and Möbius pieces, or find an
   additional signed refinement inside the cap. A successful proof must explain
   more than the existence of a sign crossing.

Completing `K` through `R-1` is still not the route: that recovers the
already-known full transport and erases the restricted nonconstant fibre. The
fixed-depth crossing settles the sign-crossing target, but it does not by itself
give a root-scale bound for the packet value at the crossing.

The critical invariant remains

\[
\boxed{
\text{upper }k=1\text{ boundary}
\;\text{plus a growing but shallow reciprocal packet, kept incomplete.}
}

# Prime-Density Packet Operator: Corrected Exact-Activity Formulation

## Correction to PR #99

PR #99 introduced a deterministic midpoint-lifetime model for the high packet process and reported a numerically stable decomposition

\[
S=(L+\widehat H_{\mathrm{mid}})+(H-\widehat H_{\mathrm{mid}}).
\]

The exact algebraic recombination and the cofactor packet-start identity remain valid. The later cofactor-resolved diagnostics, however, showed that the midpoint-lifetime model is **not** the correct object for diagnosing the prime-count residual.

The large cofactor diagonal, near-rank-one singular mode, and apparent Mellin structure reported after PR #99 were produced almost entirely by the deterministic mismatch between:

1. the exact packet lifetime of each prime source; and
2. the single lifetime assigned to all prime mass in a birth interval through its midpoint.

Those features belong to the approximation error, not to the true prime-count discrepancy. They must not be used as evidence for a Mellin-separable parity problem or a Möbius power-saving theorem.

The canonical model is now the **exact-activity density model** defined below.

## Repository classification

This document keeps four layers separate:

- **exact finite identities:** packet activity, cofactor reindexing, and algebraic decompositions;
- **deterministic approximation:** logarithmic-integral mass on the exact active prime interval;
- **finite diagnostics:** scaling, rank, and projection measurements over finite ranges;
- **open analytic premises:** uniform local-energy bounds.

No finite computation in this directory proves an asymptotic estimate or an RH implication.

## 1. Exact cofactor packet-start identity

For square block `n >= 2`, every retained odd-cofactor packet start has a unique representation

\[
m=cq,
\]

where `c` is odd and squarefree, `c <= n`, and `q` is prime with

\[
q\ge n+2,
\qquad
n^2\le cq <(n+1)^2.
\]

Since `q>c`, it is the largest prime factor and

\[
\mu(cq)=-\mu(c).
\]

Define

\[
U_n(c)=\left\lfloor\frac{(n+1)^2-1}{c}\right\rfloor,
\]

\[
L_n(c)=\max\!\left(n+1,\left\lceil\frac{n^2}{c}\right\rceil-1\right),
\]

and

\[
W_n(c)=\pi(U_n(c))-\pi(L_n(c)).
\]

Then the signed packet-start count is exactly

\[
F_n=-\sum_{\substack{c\le n\\c\text{ odd}}}\mu(c)W_n(c).
\]

The independent finite verifier reports zero integer error through `n=4000`. This lower-dimensional identity remains the durable exact result of PR #99.

## 2. Exact activity at time `t`

A source `m=cq` born at entry shell

\[
e(c,q)=\lfloor\sqrt{cq}\rfloor
\]

remains in the compressed high packet until

\[
\min\bigl(\lfloor\sqrt{2cq}\rfloor,q-1\bigr).
\]

For fixed time `t` and odd cofactor `c`, the source is active exactly when the prime `q` lies in the integer interval

\[
L(t,c)\le q\le U(t,c),
\]

where

\[
L(t,c)=\max\!\left(
 t+2,
 \left\lceil\frac{(t+1)^2}{2c}\right\rceil
\right),
\]

\[
U(t,c)=\left\lfloor\frac{(t+1)^2-1}{c}\right\rfloor.
\]

Thus the exact cofactor contribution to the high packet process is

\[
H_{t,c}
=-\mu(c)\Bigl(\pi(U(t,c))-\pi(L(t,c)-1)\Bigr).
\]

This is the activity-level identity that the Lean formalization should expose.

## 3. Canonical exact-activity density model

Define

\[
\widehat H^{\mathrm{active}}_{t,c}
=-\mu(c)
\int_{L(t,c)-1/2}^{U(t,c)+1/2}\frac{dq}{\log q}.
\]

Summing over odd squarefree cofactors gives

\[
\widehat H^{\mathrm{active}}_t
=\sum_c \widehat H^{\mathrm{active}}_{t,c}.
\]

The corrected residual is therefore

\[
R_t^{\mathrm{prime}}
=H_t-\widehat H^{\mathrm{active}}_t
\]

\[
=-\sum_c\mu(c)\left[
\pi(U(t,c))-\pi(L(t,c)-1)
-
\int_{L(t,c)-1/2}^{U(t,c)+1/2}\frac{dq}{\log q}
\right].
\]

The complete square-prefix process has the exact algebraic decomposition

\[
S
=
\underbrace{L+\widehat H^{\mathrm{active}}}_{\text{complementary main term}}
+
\underbrace{H-\widehat H^{\mathrm{active}}}_{\text{prime-count residual}}.
\]

The deterministic midpoint-lifetime mismatch is thereby absorbed into the complementary main term, where structured geometric contributions belong.

## 4. Why the midpoint model was misleading

Let `H_mid` denote the historical PR #99 model, which replaced every prime in one birth interval by the interval midpoint and assigned the resulting expected mass one common packet endpoint. Then identically

\[
H-H_{\mathrm{mid}}
=
\underbrace{H-H_{\mathrm{li,active}}}_{\text{pure prime discrepancy}}
+
\underbrace{H_{\mathrm{li,active}}-H_{\mathrm{mid}}}_{\text{lifetime mismatch}}.
\]

In the dominant cofactor band at `N=5000`:

| matrix | diagonal / `HN^2` | signed energy / `HN^2` | top singular-mode share |
|---|---:|---:|---:|
| historical midpoint residual | `1.770249` | `0.710138` | `99.492%` |
| pure prime discrepancy | `0.001432` | `0.001068` | `51.856%` |
| deterministic lifetime mismatch | `1.699036` | `0.682913` | `99.526%` |

The lifetime mismatch accounts for approximately `95.98%` of the oversized diagonal and essentially all of the near-rank-one phenomenon.

Therefore:

- the midpoint model remains a useful aggregate predictor;
- it is noncanonical for cofactor-resolved energy analysis;
- its rank-one and Mellin diagnostics must not be transferred to the exact prime discrepancy.

## 5. Corrected finite scaling evidence

The exact-activity prime discrepancy was tested in dyadic cofactor bands through `N=200000`. For `N>10000`, the computation sampled 1000 evenly spaced times in `[N,2N)` and searched the dangerous large-cofactor region `c >= N/64`.

| `N` | dominant band | sign-blind diagonal / `HN^2` | signed energy / `HN^2` |
|---:|:---:|---:|---:|
| 1,000 | `[512,1024)` | `0.00222918` | `0.000949265` |
| 2,000 | `[1024,2048)` | `0.00169418` | `0.000748006` |
| 5,000 | `[2048,4096)` | `0.00143206` | `0.0010653` |
| 10,000 | `[4096,8192)` | `0.0011979` | `0.000534473` |
| 20,000 | `[8192,16384)` | `0.00100999` | `0.000734911` |
| 50,000 | `[16384,32768)` | `0.000888216` | `0.000578571` |
| 100,000 | `[32768,65536)` | `0.000803612` | `0.000599927` |
| 200,000 | `[65536,131072)` | `0.000667425` | `0.000194819` |

The finite power fit for the dominant sign-blind diagonal is `-0.214`; the polylogarithmic fit is approximately `(log N)^(-2.009)` and has the lower log-residual sum of squares.

This evidence does **not** prove a uniform theorem. It does show that the true prime discrepancy has no observed positive-power diagonal excess over this range, so no Möbius off-diagonal power saving is numerically required for the residual.

## 6. Corrected analytic target

For every translated window `[N,N+H)` and every dyadic cofactor band `c ~ C`, the first analytic premise should be the sign-blind variance estimate

\[
\sum_{t=N}^{N+H-1}
\sum_{c\sim C}
\left|
\pi(U(t,c))-\pi(L(t,c)-1)
-
\int_{L(t,c)-1/2}^{U(t,c)+1/2}\frac{dq}{\log q}
\right|^2
\ll_\varepsilon HN^{2+\varepsilon}.
\]

There are only logarithmically many dyadic bands. A suitable bandwise estimate can therefore feed the full residual through standard norm inequalities with an `N^epsilon` allowance.

The second premise remains the complementary-main estimate

\[
\sum_{t=N}^{N+H-1}
\left|L_t+\widehat H^{\mathrm{active}}_t\right|^2
\ll_\varepsilon HN^{2+\varepsilon}.
\]

Once the residual premise is established, this second estimate is the RH-strength component expressed in explicit exact-activity coordinates.

## 7. Permanent nonclaims

The corrected evidence does not establish:

- a uniform short-interval prime-variance theorem for this reciprocal interval family;
- applicability of a specific Gallagher, Selberg, Goldston--Montgomery, or pair-correlation theorem without an endpoint and averaging reduction;
- a low-rank Mellin description of the pure prime discrepancy;
- a Möbius Type-II power saving;
- an unconditional RH implication.

The exact-activity interval identity and its conditional bridge should be formalized first. Any external analytic theorem must then be matched to the precise discrete two-parameter interval family rather than invoked by analogy.

# Twisted Euler accounting: the two real walls of finite C

**Date:** 2026-10-11  
**Status:** Exact finite arithmetic identity; numerical tests through square root 317; **no new finite-C bound, finite-A bound or RH proof.** This note is a follow-up to [the complete finite-C/A handoff](SEQUENTIAL_EULER_SQUARE_BLOCK_FINITE_C_A_RESEARCH_NOTE.md).

## 1. The same exact target, as one signed Euler population

Write \(\mu\) for the genuine Möbius function, \(M(x)=\sum_{n\le x}\mu(n)\), and for each integer \(R\ge2\) put
\[
X=R^2-1,\qquad
K_R=\max_{0\le y<R}\frac{(M(y)-1)^2}{y+1},\qquad
Q_R=2M(R-1)-M(X).
\]
Define the **twisted sign**
\[
w_R(n)=\begin{cases}+1,&1\le n<R,\\-1,&R\le n\le X,\end{cases}
\qquad
\sigma_R(n)=w_R(n)\mu(n).
\]
Then, with exactly the original finite-C numerator,
\[
\boxed{Q_R=\sum_{n=1}^{X}\sigma_R(n).}\tag{1}
\]
The requested theorem remains \(\exists C<\infty\,\forall R\ge2:\ |Q_R|\le CR\sqrt{K_R}\).

The ordinary Möbius parity of a fresh prime **flips**. But at the historical threshold \(R\), the weight \(w_R\) also flips. This makes some opposite-Möbius-sign pairs *reinforce* in the actual finite-C kernel.

## 2. Exact two-wall prime-pivot decomposition

**Theorem (elementary; no averaging).** Fix a prime \(p\le X\). Every squarefree \(m\le X\) is either free of \(p\) or contains \(p\) exactly once; terms containing \(p^2\) have weight zero. Pair each \(p\)-free squarefree \(n\) with \(pn\) when \(pn\le X\).

The signed contributions obey
\[
\sigma_R(n)+\sigma_R(pn)
=\mu(n)\bigl(w_R(n)-w_R(pn)\bigr).
\]
This is zero if both products are on the same side of \(R\), but equals \(2\mu(n)\) if \(n<R\le pn\le X\). When \(pn>X\), there is no child; \(\sigma_R(n)\) remains.

Consequently the **complete**, occurrence-preserving, finite identity is
\[
\boxed{
Q_R =
2\!\!\!\!\sum_{\substack{1\le n<R,\ p\nmid n,\ \mu(n)\ne0\\
                         R\le pn\le X}}\!\!\!\!\mu(n)
+
\sum_{\substack{1\le n\le X,\ p\nmid n,\ \mu(n)\ne0\\pn>X}}
w_R(n)\mu(n).
}\tag{2}
\]
Define the first term as \(\mathrm{Cross}_R(p)\), the second as
\(\mathrm{Exit}_R(p)\). The two genuine walls are **the historical
twist at \(R\)** and **the physical product cutoff \(X=R^2-1\)**. Every
interior pair cancels exactly. The identities have no stochastic assumption.

**Important diagnostic:** a single pivot is *not* an independent bound.

For \(p<R\), every parent \(n<R\) has \(pn\le p(R-1)\le X\).
The p-free decomposition of the ordinary Möbius sum gives
\[
\boxed{\mathrm{Cross}_R(p)=2M(R-1),\qquad
\mathrm{Exit}_R(p)=-M(X).}\tag{3}
\]
Thus for *every* low pivot, (2) simply reproduces the original
\(2M(R-1)-M(X)\). Bounding or averaging these scalar frontier masses
independently is circular.

For \(p\ge R\), \(k=\lfloor X/p\rfloor<R\), every proper cofactor is
already historical, and
\[
\boxed{\mathrm{Cross}_R(p)=2M(k),\qquad
\mathrm{Exit}_R(p)=Q_R-2M(k).}\tag{4}
\]
This is exactly the high-prime cofactor mechanism, not a separate
contraction estimate.

## 3. A rigorous no-go for one-edge matching

Take a prime \(p\in(X/2,X]\). Its face \(\{p\}\) is squarefree and has
twisted sign \(\sigma_R(p)=+1\). Its only Boolean-cube neighbor is the
empty face corresponding to \(1\), with twisted sign \(\sigma_R(1)=+1\).
No two-prime product containing \(p\) fits below \(X\), because
\(2p>X\). Thus this \(p\)-vertex has **no sign-reversing one-prime
Boolean-cube edge**.

There are precisely \(\pi(X)-\pi(\lfloor X/2\rfloor)\) such isolated
positive vertices. By PNT,
\[
\pi(X)-\pi(X/2)\sim\frac{X}{2\log X}.
\]
Meanwhile \(K_R\le R\) trivially, so \(R\sqrt{K_R}\le R^{3/2}\).
The ratio of these isolated single-edge vertices to the target
normalization diverges at least like a positive constant times
\(\sqrt R/\log R\).

**No one-prime-edge-only sign-reversing matching can leave
\(O(R\sqrt{K_R})\) *unsigned* unmatched faces.** This does *not* imply
\(Q_R\) is large: the isolated plus faces are compensated in the full
signed sum by other, nonadjacent Euler factor families. It is a no-go
for an overly local proof method, not a refutation of finite C.

This also explains why naive sign-blind counting of unmatched
prime-owner seats loses the essential cancellation.

## 4. Independent finite ledger

The exact elementary identity (2) was independently tested using a
fresh integer Möbius sieve for each listed \(X\):

| R | p | Historical-cross wall | Upper-exit wall | Total \(Q_R\) |
|---:|---:|---:|---:|---:|
| 10 | 2 | -4 | -1 | -5 |
| 10 | 11 | -4 | -1 | -5 |
| 56 | 2 | -4 | -6 | -10 |
| 56 | 59 | -6 | -4 | -10 |
| 317 | 2 | -6 | +28 | +22 |
| 317 | 331 | -4 | +26 | +22 |
| 317 | 439 | +6 | +16 | +22 |
| 317 | 1009 | +2 | +20 | +22 |

At \(R=317\), \(X=100488\), \(K_R=1.5\), and
\(R\sqrt{K_R}\approx388.2441\). There are **4,474** isolated upper-half
prime singleton faces, while the actual \(|Q_R|=22\), giving
\(C_R\approx0.05666538\). A successful proof must explain the
cross-owner signed compensation; the count of isolated faces alone is
not an estimate of \(|Q_R|\).

Reproduce: \`python3 scripts/euler_twisted_two_wall_audit.py\` (standard
library only, no external arithmetic packages).

## 5. Existing formal accounting and the precise next mathematical step

The following *existing* Lean modules should be used instead of
introducing another renamed Mobius prefix:
- \`RHLean/Arithmetic/TruncatedBooleanCube.lean\`: exact first-failure
  pairing of downward-closed product faces.
- \`RHLean/Arithmetic/TruncatedBooleanCubeSecondToggle.lean\`: exact
  signed two-corner decomposition of a second pivot.
- \`RHLean/Arithmetic/PrimeProductCubeFrontier.lean\`: literal
  endpoint product condition \(m\le X<pm\).
- \`research/LARGE_PRIME_EULER_RESPONSE.lean\`: actual large-prime
  \`N_X(m)\` response, one-/two-prime finite differences, and signed
  energy/covariance identity.
- \`RHLean/Analysis/PrimeAveragedCubeEnergy.lean\`: a **proved no-go**:
  averaging already-aggregated pivot frontier scalars gives exactly
  \(\pi(X)M(X)^2\); no new cancellation appears.
- \`RHLean/Proof/SquareRootLowPrimeMatchingDisplacement.lean\`: strictly
  decreasing blocker chains for matching instability.
- \`research/BOUNDARY_SHADOW_MORSE.lean\`: a conditional
  boundary-shadow involution transfers a *different* original physical
  running imbalance into a \(\le4R\) estimate. The matching's
  existence and any carrier-specific splice to our **current**
  \(Q_R\) must be established; this module is **not** an unconditional
  finite-C theorem.

The next genuinely useful theorem is **not** another equality of
scalar frontier totals. It must construct a **cross-owner,
occurrence-preserving, sign-reversing transport** for the *combined*
\(\mathrm{Cross}_R\) and \(\mathrm{Exit}_R\) populations (or a more refined
two-prime corner decomposition) with a provably controlled signed
terminal defect. In particular it must transport upper-half singleton
primes to opposite-sign *nonadjacent* factor families without dropping
Möbius parity or multiplicities.

A valid proof certificate could be a combinatorially defined
near-involution whose unmatched signed mass is controlled by
independently proven boundary geometry at \(O(R\sqrt{K_R})\). Merely
postulating such a matching, or choosing it from an already known
small \(M(X)\), is the original unproved claim in disguise.

**Status:** exact 2-wall accounting and one-edge matching obstruction;
**open:** all-root signed nonlocal compensation and finite C.

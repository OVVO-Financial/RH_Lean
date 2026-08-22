# Predecessor-prime / reciprocal-label cross-root gate

**Status:** route closed in this coordinate family.

The literal cumulative `(p,k)` cell fails the finite local-cancellation gate. Its
fresh-prime derivative does contain a real exact terminal-prime cancellation and
an exact `p^3 < R^2` support law, which explains the striking high-`p`
anti-alignment seen numerically. But completing the predecessor chronology gives
an even stronger exact statement:

\[
\boxed{\sum_p \Delta_R^{\rm step}(p,k)=N_R(k)-|J_R(k)|,}
\]

namely **minus the number of composites in the reciprocal fibre**. If that
composite channel is further split by its first-hit prime `r`, completion of the
predecessor coordinate gives exactly `-H_r(k)`. Thus merely exposing an ordered
future first-hit prime `(p,r,k)` is another refinement of the same one-sign
composite population, not a new cancellation mechanism.

No analytic estimate, asymptotic, PNT input, zeta input, or RH hypothesis is
introduced.

## 1. Reciprocal and predecessor-prime coordinates

Let

\[
X_R=R^2-1,\qquad 2\le k<R,
\]

and

\[
J_R(k)=\{q:R<q\le X_R/2,\ \lfloor X_R/q\rfloor=k\}.
\]

Let

\[
N_R(k)=\#\{q\in J_R(k):q\text{ prime}\}.
\]

For a low prime `p`, define

\[
C_{<p}(k)=F_{<p}(k),
\qquad
A_p(k)=F_{<p}(\lfloor k/p\rfloor),
\]

where `F_<p` is the truncated Boolean cube on primes strictly below `p`. On
squarefree support,

\[
A_p(k)=\sum_{\substack{d\le k/p\\P^+(d)<p}}\mu(d).
\]

The fresh-prime recurrence is exact:

\[
\boxed{C_{\le p}(k)=C_{<p}(k)-A_p(k).}
\]

This is formalized as
`frozenPrimeUniverseMass_primesUpTo_step_eq_sub_predecessor`.

## 2. The literal `k`-cell is exactly the repository double-cube state

The new module does not introduce a surrogate scalar. It defines
`lowWheelPKReciprocalSurvivorSet` and `lowWheelPKCumulativeCell` directly from
the existing q-first sequential state, and proves

\[
\boxed{L_p(k)=C_{\le p}(k)\,Q_{\le p}(k),}
\]

where `Q_<=p(k)` is the number of integers in `J_R(k)` surviving every prime
through `p`.

The exact Lean interfaces are:

- `lowWheelPKCumulativeCell_eq_shell_mul_survivorCard`;
- `lowWheelPKCumulativeCell_eq_frozen_mul_survivorCard`;
- `lowWheelDoubleCubePrimePrefix_step_eq_sum_pkCumulativeCells`.

Thus the complete state through `p` is literally the sum of its reciprocal
`(p,k)` cells. The finite scan is an exact image of the formal ledger.

## 3. Exact primorial deletion and the `k=2` null band

If `k/p` contains the complete Boolean cube on primes below `p`, then

\[
A_p(k)=0.
\]

For prime `p>2`, a sufficient exact condition is

\[
p\prod_{r<p\atop r\text{ prime}}r\le k.
\]

The first thresholds are

| `p` | predecessor primorial | first `k` forcing `A_p(k)=0` |
|---:|---:|---:|
| 3 | 2 | 6 |
| 5 | 6 | 30 |
| 7 | 30 | 210 |
| 11 | 210 | 2310 |
| 13 | 2310 | 30030 |

This is theorem `predecessorPrimeMass_eq_zero_of_predPrimeCube_complete`.

At the first channel, `A_2(2)=1`, so the prime edge `-1` and the `p=2`
predecessor term cancel identically. This is the face-level version of the
already-formalized zero harmonic band `X_R/3 < q <= X_R/2`, where the reciprocal
quotient is `2` and `M(2)=0`.

## 4. Cumulative state versus additive fresh-prime change

Let

\[
Q_{<p}(k)=\#\{q\in J_R(k):q\text{ survives every prime }<p\}
\]

and

\[
H_p(k)=\#\{q\in J_R(k):\minFac(q)=p\}.
\]

Then

\[
Q_{\le p}(k)=Q_{<p}(k)-H_p(k).
\]

The cumulative low state is

\[
L_p(k)=(C_{<p}-A_p)(Q_{<p}-H_p).
\]

Its additive change across `p` is

\[
\begin{aligned}
D_p(k)
&=L_p(k)-C_{<p}(k)Q_{<p}(k)\\
&=-A_p(k)Q_{\le p}(k)-C_{<p}(k)H_p(k).
\end{aligned}
\]

This is theorem `freshPrimePKCell_eq_cofactorDeletion_add_hitDeletion`.

The separate identity

\[
\operatorname{Shell}_p(k)+A_p(k)=F_{<p}(k)
\]

is formalized as
`lowWheelSmoothFaceShellMass_add_predecessor_eq_parentPrefix`; it warns that the
cumulative state contains an inherited parent mode.

## 5. The literal cumulative cross-root cell fails

The literal proposal is

\[
\Delta_R^{\rm cum}(p,k)=L_p(k)+N_R(k)A_p(k).
\]

Lean records the exact decomposition

\[
\boxed{
\Delta_R^{\rm cum}(p,k)
=C_{<p}(k)Q_{<p}(k)
+\Delta_R^{\rm step}(p,k),
}
\]

where

\[
\Delta_R^{\rm step}(p,k)=D_p(k)+N_R(k)A_p(k).
\]

This is theorem `cumulativePKCrossRoot_eq_parent_add_futureHitResidual`. The
literal cell therefore retains the complete parent product and should not be
expected to be small.

Restricting to cells with `N_R(k)A_p(k) != 0`, the scan gives:

| `R` | fraction `rho_cum<=0.1` | weighted residual | dyadic weighted residual |
|---:|---:|---:|---:|
| 500 | 0.0446 | 0.7808 | 0.6847 |
| 1000 | 0.0265 | 0.8478 | 0.7657 |
| 2000 | 0.0154 | 0.8959 | 0.8223 |
| 5000 | 0.0074 | 0.9405 | 0.8879 |
| 10000 | 0.0043 | 0.9621 | 0.9224 |

Thus the literal cumulative `(p,k)` local-cancellation lane is decisively closed.

## 6. The derivative has an exact terminal-prime cancellation

For the additive change,

\[
\Delta_R^{\rm step}(p,k)=D_p(k)+N_R(k)A_p(k).
\]

Then

\[
\boxed{
\Delta_R^{\rm step}(p,k)
=-A_p(k)\bigl(Q_{\le p}(k)-N_R(k)\bigr)
-C_{<p}(k)H_p(k).
}
\]

This is theorem `freshPrimePKCrossRoot_eq_futureHitResidual`. Since

\[
Q_{\le p}(k)-N_R(k)=\sum_{r>p}H_r(k),
\]

we can write

\[
\boxed{
\Delta_R^{\rm step}(p,k)
=-A_p(k)\sum_{r>p}H_r(k)-C_{<p}(k)H_p(k).
}
\]

The terminal prime population has disappeared exactly, before any norm. This is
a real local mechanism; it is also the source of the strong high-`p`
anti-alignment seen in the finite data.

## 7. Exact two-thirds support law

If a supported reciprocal cell satisfies `p<=k` and an unresolved composite
`q` remains with

\[
R<q,\qquad \lfloor X_R/q\rfloor=k,\qquad p\le\minFac(q),
\]

then

\[
p^2\le q,
\qquad
pq\le X_R<R^2,
\]

hence

\[
\boxed{p^3<R^2.}
\]

This is theorem
`reciprocalMiddle_composite_survivor_forces_predCube_lt_square`, with the
contrapositive also formalized.

Thus the derivative residual has no supported current/future composite hit once
`p^3>=R^2`. The observed disappearance near `R^(2/3)` is an exact geometric
support fact, not an asymptotic phenomenon.

## 8. Why the high-p scan looked promising

On cells with `N_R(k)A_p(k) != 0`, the derivative pieces are strongly
anti-aligned. At `R=10000`:

| cut | corr `(D,NA)` | fraction `rho_step<=0.01` | weighted residual | `sum|D|/sum|NA|` |
|---|---:|---:|---:|---:|
| `p>=R^(1/4)` | -0.9875 | 0.9468 | 0.2444 | 1.6263 |
| `p>=R^(1/3)` | -0.9884 | 0.9521 | 0.1646 | 1.3709 |
| `p>=R^(2/5)` | -0.9876 | 0.9579 | 0.1249 | 1.2614 |
| `p>=R^(1/2)` | -0.9788 | 0.9738 | 0.0686 | 1.1204 |
| `p>=R^(3/5)` | -0.9685 | 0.9942 | 0.0146 | 1.0281 |

For `p>=R^(3/5)`, the absolute residual at the tested scales is still about
`10^-3 R^2`:

| `R` | `sum|Delta_step| / R` | `sum|Delta_step| / R^2` |
|---:|---:|---:|
| 500 | 0.6080 | 0.001216 |
| 1000 | 0.8340 | 0.000834 |
| 2000 | 2.1035 | 0.001052 |
| 5000 | 4.7858 | 0.000957 |
| 10000 | 9.6107 | 0.000961 |

The exact support theorem explains both facts: composites with large least prime
factor are sparse, so terminal-prime matching is almost exact there. But the
missing mass must reappear in the low-prime cells.

## 9. Definitive completed-p collapse: every composite survives once

The predecessor recurrence telescopes from the empty old-prime universe to the
completed lower-scale Mertens state:

\[
\sum_p A_p(k)=1-M(k).
\]

The product-state increments telescope from the initial integer population to
the terminal prime/Mertens state:

\[
\sum_p D_p(k)=N_R(k)M(k)-|J_R(k)|.
\]

Therefore

\[
\begin{aligned}
\sum_p\Delta_R^{\rm step}(p,k)
&=N_R(k)M(k)-|J_R(k)|+N_R(k)(1-M(k))\\
&=\boxed{N_R(k)-|J_R(k)|}.
\end{aligned}
\]

Since `N_R(k)` counts primes inside `J_R(k)`, this is

\[
\boxed{-\#\{q\in J_R(k):q\text{ composite}\}.}
\]

The endpoint algebra is formalized as
`completedPKCrossRoot_endpointCollapse`.

This explains the finite-scale obstruction more strongly than an energy table:
the derivative cannot have an RH-size completed sum. Its low-prime sector is
**forced** to carry the negative composite population left over from the
near-perfect high-prime matching.

## 10. Unsumming the future first-hit prime does not escape

Fix a first-hit prime `r`. Its contributions are

\[
-H_r(k)\sum_{p<r}A_p(k)-C_{<r}(k)H_r(k).
\]

But the predecessor recurrence gives

\[
C_{<r}(k)+\sum_{p<r}A_p(k)=1.
\]

Hence the whole first-hit fibre is

\[
\boxed{-H_r(k).}
\]

The algebra is formalized as
`completedPredecessorFirstHit_eq_neg_hitCount`.

Therefore a plain ordered `(p,r,k)` first-hit refinement is **not** a new open
Type-II mechanism. It merely distributes the coefficient `-1` of each composite
among predecessor coordinates and recombines to the positive first-hit count.

## 11. Route decision

The scan and exact algebra now agree completely:

1. **Literal cumulative `(p,k)` cell:** closed by the inherited-parent identity
   and a strongly negative finite gate.
2. **Fresh-prime derivative:** contains a real local terminal-prime cancellation
   and exact support `p^3<R^2`, but after completing `p` it is exactly minus the
   composite population.
3. **Plain `(p,r,k)` first-hit refinement:** also closed; completing `p` in each
   fixed `r` fibre gives exactly `-H_r(k)`.

So the next viable route cannot merely expose another positive first-hit label.
It must introduce an operation or weight that **does not complete to coefficient
`1` across the predecessor divisor fibre** — for example a genuinely restricted
proper subregion whose complement is controlled separately, or a second
Möbius-bearing/bilinear factor rather than a positive first-hit count.

This is precisely the post-#453 survival criterion in sharper form: preserving
more labels is not enough; the surviving weight must remain nonconstant on the
completed divisor fibre.

Reproduce the literal and derivative finite gates with
`research/pk_fresh_step_gate.cpp`.

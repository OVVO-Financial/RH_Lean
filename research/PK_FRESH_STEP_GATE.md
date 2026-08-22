# Predecessor-prime / reciprocal-label cross-root gate

**Status:** the completed and cumulative `(p,k)` coordinates are reconstructive,
but the correctly signed **cross-root additive cell** has a real exact
anti-alignment mechanism. The terminal-prime term cancels cell by cell, and the
remaining supported residual is forced into `p^3 < R^2`. The finite data show
very strong high-`p` cancellation, but the residual below that exact cutoff is
still too large to constitute an RH-scale estimate.

No analytic Lean proposition or asymptotic estimate is introduced by this note.

## 1. Reciprocal and predecessor-prime coordinates

Let

\[
X_R=R^2-1,
\qquad
2\le k<R,
\]

and

\[
J_R(k)=\{q:R<q\le X_R/2,\ \lfloor X_R/q\rfloor=k\}.
\]

Let

\[
N_R(k)=\#\{q\in J_R(k):q\text{ prime}\}.
\]

For a low prime `p`, write

\[
C_{<p}(k)=F_{<p}(k),
\]

where `F_<p` is the truncated Boolean-cube mass on primes strictly below `p`,
and define

\[
A_p(k)=F_{<p}(\lfloor k/p\rfloor).
\]

On squarefree support,

\[
A_p(k)=
\sum_{\substack{d\le k/p\\P^+(d)<p}}\mu(d).
\]

The fresh-prime recurrence is exact:

\[
C_{\le p}(k)=C_{<p}(k)-A_p(k).
\]

This is formalized in `SquareRootPredecessorPrimeCells.lean` as
`frozenPrimeUniverseMass_primesUpTo_step_eq_sub_predecessor`.

## 2. Exact primorial deletion and the `k=2` null band

If the cutoff `k/p` contains the complete Boolean cube on primes below `p`, then

\[
A_p(k)=0.
\]

For prime `p>2`, a sufficient exact condition is

\[
p\prod_{r<p\atop r\text{ prime}}r\le k.
\]

The first deletion thresholds are

| `p` | predecessor primorial | first `k` forcing `A_p(k)=0` |
|---:|---:|---:|
| 3 | 2 | 6 |
| 5 | 6 | 30 |
| 7 | 30 | 210 |
| 11 | 210 | 2310 |
| 13 | 2310 | 30030 |

This is theorem `predecessorPrimeMass_eq_zero_of_predPrimeCube_complete`.

At the opposite edge, `A_2(2)=1`, so the prime edge `-1` and the `p=2`
predecessor contribution cancel exactly. This is the local face version of the
already-formalized middle null band

\[
X_R/3<q\le X_R/2,
\qquad
\lfloor X_R/q\rfloor=2,
\qquad
M(2)=0.
\]

## 3. Cumulative `(p,k)` state is a reconstruction

The sequential smooth-shell coefficient is

\[
\operatorname{Shell}_p(k)
=F_{<p}(k)-F_{<p}(\lfloor k/p\rfloor)
=C_{\le p}(k).
\]

Hence

\[
\boxed{
\operatorname{Shell}_p(k)+A_p(k)=C_{<p}(k).
}
\]

This is theorem
`lowWheelSmoothFaceShellMass_add_predecessor_eq_parentPrefix`.

Therefore pairing `A_p(k)` against the **cumulative** state after processing
`p` is not a new cancellation test: it reconstructs the parent prefix exactly.
The cross-root statistic has to use the additive fresh-prime change.

## 4. Additive fresh-prime step

Let

\[
Q_{<p}(k)=\#\{q\in J_R(k):q\text{ has no prime divisor }<p\}
\]

and

\[
H_p(k)=\#\{q\in J_R(k):\minFac(q)=p\}.
\]

Then

\[
Q_{\le p}(k)=Q_{<p}(k)-H_p(k).
\]

The product state changes by

\[
\begin{aligned}
D_p(k)
&=C_{\le p}(k)Q_{\le p}(k)-C_{<p}(k)Q_{<p}(k)\\
&=-A_p(k)Q_{\le p}(k)-C_{<p}(k)H_p(k).
\end{aligned}
\]

The polynomial identity is formalized as
`freshPrimePKCell_eq_cofactorDeletion_add_hitDeletion`.

## 5. The correct cross-root cell

The proposed post-root predecessor term in the same reciprocal cell is

\[
N_R(k)A_p(k).
\]

Define

\[
\boxed{
\Delta_R(p,k)=D_p(k)+N_R(k)A_p(k).
}
\]

Then the terminal-prime component cancels **algebraically before any norm**:

\[
\boxed{
\Delta_R(p,k)
=-A_p(k)\bigl(Q_{\le p}(k)-N_R(k)\bigr)
-C_{<p}(k)H_p(k).
}
\]

Since

\[
Q_{\le p}(k)-N_R(k)=\sum_{r>p}H_r(k),
\]

this is equivalently

\[
\boxed{
\Delta_R(p,k)
=-A_p(k)\sum_{r>p}H_r(k)-C_{<p}(k)H_p(k).
}
\]

The first displayed identity is formalized as
`freshPrimePKCrossRoot_eq_futureHitResidual`.

This is the genuinely new structural point. The final prime population is gone;
the residual is pure **current/future composite chronology**.

## 6. Exact two-thirds support law

Suppose a cross-root cell is supported in the predecessor sense `p<=k`, and an
unresolved composite `q` remains with

\[
R<q,
\qquad
\lfloor X_R/q\rfloor=k,
\qquad
p\le\minFac(q).
\]

Because `q` is composite,

\[
p^2\le \minFac(q)^2\le q.
\]

Also `p<=k` and `kq<=X_R`, hence

\[
pq\le X_R<R^2.
\]

Therefore

\[
\boxed{p^3<R^2.}
\]

This is theorem
`reciprocalMiddle_composite_survivor_forces_predCube_lt_square`, with the
contrapositive recorded separately.

Consequently, on the supported cross-root corridor, once

\[
R^2\le p^3
\]

there is no current or future composite hit at all. Thus the residual
`Delta_R(p,k)` is identically zero above the exact `R^(2/3)` predecessor scale.

This is stronger than the empirical high-`p` decay: it is a geometric support
theorem.

## 7. Finite cross-root gate

For cells with an actual post-root predecessor term `N_R(k) A_p(k) != 0`, use

\[
\rho_{p,k}
=
\frac{|\Delta_R(p,k)|}
{|D_p(k)|+|N_R(k)A_p(k)|}.
\]

The executable checks the residual identity exactly and verifies that the
q-survivor state terminates at `N_R(k)` with zero error.

The all-`p` supported cells already show strong sign anti-alignment:

| `R` | `corr(D,NA)` | fraction `rho<=0.1` | fraction `rho<=0.01` | weighted residual |
|---:|---:|---:|---:|---:|
| 500 | -0.9263 | 0.8615 | 0.8486 | 0.6182 |
| 1000 | -0.9273 | 0.8957 | 0.8817 | 0.6336 |
| 2000 | -0.9283 | 0.9172 | 0.9045 | 0.6480 |
| 5000 | -0.9292 | 0.9408 | 0.9288 | 0.6651 |
| 10000 | -0.9297 | 0.9543 | 0.9441 | 0.6768 |

Here “weighted residual” is

\[
\frac{\sum|\Delta|}{\sum(|D|+|NA|)}.
\]

The apparent contradiction — more than 94% of cells are nearly canceled while
the weighted residual is still large — is caused by a small number of early-`p`
cells carrying most of the mass.

## 8. Moving predecessor cuts

Peeling those finite low-prime modes reveals a much cleaner bulk. At `R=10000`:

| cut | corr `(D,NA)` | fraction `rho<=0.01` | weighted residual | `sum|D| / sum|NA|` |
|---|---:|---:|---:|---:|
| `p>=R^(1/4)` | -0.9875 | 0.9468 | 0.2444 | 1.6263 |
| `p>=R^(1/3)` | -0.9884 | 0.9521 | 0.1646 | 1.3709 |
| `p>=R^(2/5)` | -0.9876 | 0.9579 | 0.1249 | 1.2614 |
| `p>=R^(1/2)` | -0.9788 | 0.9738 | 0.0686 | 1.1204 |
| `p>=R^(3/5)` | -0.9685 | 0.9942 | 0.0146 | 1.0281 |

The `R^(3/5)` line is stable across the tested scales: roughly 99% of cells are
within one percent, and the low/post absolute masses are almost equal.

This is the first finite gate in the sequence where the intended cross-root
anti-alignment is visible both in sign and magnitude.

## 9. But the absolute residual is still too large

A small ratio is not a power saving. The same scan records the absolute residual
scale. For `p>=R^(3/5)`:

| `R` | `sum|Delta| / R` | `sum|Delta| / R^2` |
|---:|---:|---:|
| 500 | 0.6080 | 0.001216 |
| 1000 | 0.8340 | 0.000834 |
| 2000 | 2.1035 | 0.001052 |
| 5000 | 4.7858 | 0.000957 |
| 10000 | 9.6107 | 0.000961 |

On these finite scales the absolute residual is therefore approximately a
small constant times `R^2`, not `R^(1+epsilon)`. The 1--2% local cancellation
ratio is real but does not by itself close an RH-scale estimate.

For comparison, at `R=10000`:

| cut | `sum|Delta| / R^2` |
|---|---:|
| `p>=R^(1/4)` | 0.059412 |
| `p>=R^(1/3)` | 0.028887 |
| `p>=R^(2/5)` | 0.017892 |
| `p>=R^(1/2)` | 0.006771 |
| `p>=R^(3/5)` | 0.000961 |

The exact `p^3<R^2` theorem explains why this rapidly collapses as the cut
approaches `R^(2/3)`.

## 10. Route decision

The `(p,k)` coordinate is **not closed negatively**. It has produced a genuine
cross-root mechanism:

1. terminal primes cancel exactly in every cell;
2. the remaining state is explicitly current/future composite chronology;
3. completed predecessor cubes delete exactly by primorial cancellation;
4. the supported residual vanishes identically for `p^3>=R^2`;
5. the high-`p` bulk exhibits strong finite local anti-alignment.

But no RH estimate has been obtained. The unresolved analytic core is now
sharply confined to

\[
\boxed{p^3<R^2,}
\]

with the low-prime modes carrying most of the observed absolute residual.

The next elementary continuation should therefore **not** collapse the future
hit sum `sum_{r>p} H_r(k)`. It should retain the ordered next-prime coordinate

\[
(p,r,k),\qquad p<r,
\]

or an equivalent genuinely bilinear first-hit representation, and ask whether
the remaining `R^2` mass is canceled there before any norm is taken.

Reproduce with:

```bash
g++ -O3 -std=c++17 research/pk_fresh_step_gate.cpp -o /tmp/pk_gate
/tmp/pk_gate
```

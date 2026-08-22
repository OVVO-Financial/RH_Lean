# Predecessor-prime / reciprocal-label cross-root gate

**Status:** the literal cumulative `(p,k)` cell proposed from
`LowWheelDoubleCubeWindowFold` fails the finite local-cancellation gate.  The
reason is exact: it retains the entire inherited parent product.  Subtracting
that inherited parent — equivalently taking the additive fresh-prime change —
exposes a genuine terminal-prime cancellation, a pure current/future composite
residual, and an exact `p^3 < R^2` support law.  That derivative residual shows
strong high-`p` anti-alignment, but its absolute size below the cutoff is still
too large to constitute an RH-scale estimate.

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

For a low prime `p`, put

\[
C_{<p}(k)=F_{<p}(k),
\qquad
A_p(k)=F_{<p}(\lfloor k/p\rfloor),
\]

where `F_<p` is the truncated Boolean-cube mass on primes strictly below `p`.
On squarefree support,

\[
A_p(k)=
\sum_{\substack{d\le k/p\\P^+(d)<p}}\mu(d).
\]

The fresh-prime recurrence is exact:

\[
C_{\le p}(k)=C_{<p}(k)-A_p(k).
\]

This is theorem
`frozenPrimeUniverseMass_primesUpTo_step_eq_sub_predecessor`.

## 2. Exact primorial deletion and the `k=2` null band

If the cutoff `k/p` contains the complete Boolean cube on the primes below `p`,
then

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
predecessor contribution cancel exactly.  This is the local face version of the
already-formalized `k=2` middle null band.

## 3. Cumulative state versus additive change

Let

\[
Q_{<p}(k)=\#\{q\in J_R(k):q\text{ has no prime divisor }<p\},
\]

and

\[
H_p(k)=\#\{q\in J_R(k):\minFac(q)=p\}.
\]

Then

\[
Q_{\le p}(k)=Q_{<p}(k)-H_p(k).
\]

There are two different low `(p,k)` objects.

### Cumulative low state

The state **through** prime `p` is

\[
L_p(k)=C_{\le p}(k)Q_{\le p}(k)
      =(C_{<p}(k)-A_p(k))(Q_{<p}(k)-H_p(k)).
\]

This is the scalar analogue of retaining the complete state through `p`, as in
the cumulative double-cube/window fold.

### Additive fresh-prime change

The change across the `p` step is

\[
\begin{aligned}
D_p(k)
&=L_p(k)-C_{<p}(k)Q_{<p}(k)\\
&=-A_p(k)Q_{\le p}(k)-C_{<p}(k)H_p(k).
\end{aligned}
\]

This is theorem `freshPrimePKCell_eq_cofactorDeletion_add_hitDeletion`.

The distinction is essential.  The cumulative state contains an inherited
parent mode; the derivative does not.

## 4. The literal proposed cell fails, for an exact reason

The literal cross-root cell proposed from the cumulative low state is

\[
\boxed{
\Delta_R^{\rm cum}(p,k)=L_p(k)+N_R(k)A_p(k).
}
\]

The new theorem
`cumulativePKCrossRoot_eq_parent_add_futureHitResidual` gives

\[
\boxed{
\Delta_R^{\rm cum}(p,k)
=C_{<p}(k)Q_{<p}(k)
+\Delta_R^{\rm step}(p,k),
}
\]

where

\[
\Delta_R^{\rm step}(p,k)
=D_p(k)+N_R(k)A_p(k).
\]

So the literal cell is not expected to be locally small: it still contains the
entire parent product `C_<p Q_<p`.

The finite scan confirms this decisively.  Restricting to cells with an actual
post-root predecessor term `N_R(k)A_p(k) != 0`, the literal ratio

\[
\rho^{\rm cum}_{p,k}
=\frac{|L_p(k)+N_R(k)A_p(k)|}
       {|L_p(k)|+|N_R(k)A_p(k)|}
\]

behaves as follows:

| `R` | fraction `rho_cum<=0.1` | weighted residual | dyadic weighted residual |
|---:|---:|---:|---:|
| 500 | 0.0446 | 0.7808 | 0.6847 |
| 1000 | 0.0265 | 0.8478 | 0.7657 |
| 2000 | 0.0154 | 0.8959 | 0.8223 |
| 5000 | 0.0074 | 0.9405 | 0.8879 |
| 10000 | 0.0043 | 0.9621 | 0.9224 |

The literal cumulative `(p,k)` local-cancellation proposal therefore **fails**.
The failure gets stronger with scale.

This is not a failure of the predecessor-prime idea itself; it identifies the
inherited parent mode that has to be removed before the new prime step can be
measured.

## 5. The derivative cross-root residual

For the additive step, define

\[
\boxed{
\Delta_R^{\rm step}(p,k)=D_p(k)+N_R(k)A_p(k).
}
\]

Then the terminal-prime component cancels algebraically:

\[
\boxed{
\Delta_R^{\rm step}(p,k)
=-A_p(k)\bigl(Q_{\le p}(k)-N_R(k)\bigr)
-C_{<p}(k)H_p(k).
}
\]

This is theorem `freshPrimePKCrossRoot_eq_futureHitResidual`.

Since

\[
Q_{\le p}(k)-N_R(k)=\sum_{r>p}H_r(k),
\]

we obtain

\[
\boxed{
\Delta_R^{\rm step}(p,k)
=-A_p(k)\sum_{r>p}H_r(k)-C_{<p}(k)H_p(k).
}
\]

Thus the final prime population disappears **cell by cell before any norm**.
The remaining derivative is pure current/future composite first-hit chronology.

## 6. Exact two-thirds support law

Suppose `p<=k` and an unresolved composite `q` remains with

\[
R<q,
\qquad
\lfloor X_R/q\rfloor=k,
\qquad
p\le\minFac(q).
\]

Then

\[
p^2\le\minFac(q)^2\le q,
\]

while `p<=k` and `kq<=X_R` give

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

Hence on the supported derivative cross-root corridor, once

\[
R^2\le p^3,
\]

there is no current or future composite hit.  The derivative residual is
identically zero above the exact `R^(2/3)` predecessor scale.

## 7. Finite derivative gate

For supported cells use

\[
\rho^{\rm step}_{p,k}
=\frac{|\Delta_R^{\rm step}(p,k)|}
       {|D_p(k)|+|N_R(k)A_p(k)|}.
\]

The all-`p` supported cells show increasingly widespread local anti-alignment:

| `R` | `corr(D,NA)` | fraction `rho_step<=0.1` | fraction `rho_step<=0.01` | weighted residual |
|---:|---:|---:|---:|---:|
| 500 | -0.9263 | 0.8615 | 0.8486 | 0.6182 |
| 1000 | -0.9273 | 0.8957 | 0.8817 | 0.6336 |
| 2000 | -0.9283 | 0.9172 | 0.9045 | 0.6480 |
| 5000 | -0.9292 | 0.9408 | 0.9288 | 0.6651 |
| 10000 | -0.9297 | 0.9543 | 0.9441 | 0.6768 |

The large weighted residual despite tiny ratios in most cells is caused by a
small number of early-prime modes carrying most of the absolute mass.

## 8. Moving predecessor cuts

At `R=10000`:

| cut | corr `(D,NA)` | fraction `rho_step<=0.01` | weighted residual | `sum|D| / sum|NA|` |
|---|---:|---:|---:|---:|
| `p>=R^(1/4)` | -0.9875 | 0.9468 | 0.2444 | 1.6263 |
| `p>=R^(1/3)` | -0.9884 | 0.9521 | 0.1646 | 1.3709 |
| `p>=R^(2/5)` | -0.9876 | 0.9579 | 0.1249 | 1.2614 |
| `p>=R^(1/2)` | -0.9788 | 0.9738 | 0.0686 | 1.1204 |
| `p>=R^(3/5)` | -0.9685 | 0.9942 | 0.0146 | 1.0281 |

So after the inherited parent is removed, the high-`p` bulk is strongly aligned
both in sign and magnitude.

## 9. But the derivative residual is still too large

A small cancellation ratio is not a power saving.  For `p>=R^(3/5)`:

| `R` | `sum|Delta_step| / R` | `sum|Delta_step| / R^2` |
|---:|---:|---:|
| 500 | 0.6080 | 0.001216 |
| 1000 | 0.8340 | 0.000834 |
| 2000 | 2.1035 | 0.001052 |
| 5000 | 4.7858 | 0.000957 |
| 10000 | 9.6107 | 0.000961 |

On these finite scales the absolute derivative residual is still approximately
a small constant times `R^2`, not an RH-scale `R^(1+epsilon)` object.  No
analytic bound is claimed.

The exact `p^3<R^2` theorem explains why this residual collapses rapidly as the
predecessor cut approaches `R^(2/3)`.

## 10. Route decision

The requested finite test gives a clean two-part answer.

1. **Literal cumulative `(p,k)` cell:** killed.  It contains the inherited
   parent `C_<p Q_<p`, and the local cancellation ratio tends toward `1`.
2. **Fresh-prime derivative after removing that parent:** genuinely new
   structure.  Terminal primes cancel exactly, completed predecessor cubes
   delete exactly, and the supported residual is confined to `p^3<R^2`.

This still does **not** produce an RH estimate.  The unresolved core is the
low-prime part of the derivative residual.  Its exact form already displays the
next unsummed coordinate:

\[
-A_p(k)\sum_{r>p}H_r(k)-C_{<p}(k)H_p(k).
\]

The next elementary continuation, if pursued, should therefore retain the
future first-hit prime `r` explicitly:

\[
(p,r,k),\qquad p<r,
\]

or an equivalent genuinely bilinear first-hit representation, rather than
summing `r` into `Q_{<=p}-N_R` before the estimate.

Reproduce both gates with:

```bash
g++ -O3 -std=c++17 research/pk_fresh_step_gate.cpp -o /tmp/pk_gate
/tmp/pk_gate
```

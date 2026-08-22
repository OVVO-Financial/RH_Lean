# Predecessor-prime / reciprocal-label fresh-step gate

**Status:** exact `(p,k)` additive gate is negative.  The cumulative `(p,k)`
coefficient also has an exact reconstruction identity, so it is not a valid
independent anti-alignment statistic.

No Lean analytic proposition or asymptotic estimate is introduced by this note.
The purpose is to identify the correct finite state after the completed-fibre
no-go and decide whether the remaining predecessor-prime coordinate supplies a
local cancellation mechanism.

## 1. Coordinates

Let

\[
X_R=R^2-1,
\qquad
2\le k<R,
\]

and let

\[
J_R(k)=\{q:R<q\le X_R/2,\ \lfloor X_R/q\rfloor=k\}.
\]

The final prime population in this reciprocal fibre is

\[
N_R(k)=\#\{q\in J_R(k):q\text{ prime}\}.
\]

For a low prime `p`, write

\[
C_{<p}(k)=F_{<p}(k),
\]

where `F_<p` is the truncated Boolean-cube mass on the prime universe strictly
below `p`.  Define the predecessor-prime decrement

\[
A_p(k)=F_{<p}(\lfloor k/p\rfloor).
\]

On squarefree support this is

\[
A_p(k)
=\sum_{\substack{d\le k/p\\P^+(d)<p}}\mu(d).
\]

The fresh-prime recurrence is therefore

\[
C_{\le p}(k)=C_{<p}(k)-A_p(k).
\]

This is exactly the finite-universe recurrence already used by the repository's
increasing-prime chronology.

## 2. Exact primorial deletion

If the cutoff `k/p` contains the complete Boolean cube on the primes below `p`,
then

\[
A_p(k)=0.
\]

Equivalently, for prime `p>2`,

\[
p\prod_{r<p\atop r\text{ prime}}r\le k
\quad\Longrightarrow\quad
A_p(k)=0.
\]

The first thresholds are therefore

| `p` | predecessor primorial | first `k` forcing `A_p(k)=0` |
|---:|---:|---:|
| 3 | 2 | 6 |
| 5 | 6 | 30 |
| 7 | 30 | 210 |
| 11 | 210 | 2310 |
| 13 | 2310 | 30030 |

The `p=2, k=2` channel is the opposite edge case: `A_2(2)=1`, so the prime edge
`-1` and the `p=2` predecessor contribution cancel identically.  At the middle
level this is the already-formalized zero band `X_R/3 < q <= X_R/2`, where the
reciprocal quotient is `2` and `M(2)=0`.

## 3. The cumulative `(p,k)` pairing is not a test

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

Thus pairing `A_p(k)` with the **cumulative** state after prime `p` merely
reconstructs the parent prefix before `p`.  A correlation between those two
quantities is therefore algebraically contaminated and cannot be interpreted as
new cancellation.

This is formalized in `SquareRootPredecessorPrimeCells.lean` as
`lowWheelSmoothFaceShellMass_add_predecessor_eq_parentPrefix`.

## 4. Correct additive fresh-prime cell

Let

\[
Q_{<p}(k)=\#\{q\in J_R(k):q\text{ has no prime divisor }<p\}
\]

and

\[
H_p(k)=\#\{q\in J_R(k):\minFac(q)=p\}.
\]

Processing `p` gives

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

This is the genuine additive two-coordinate fresh-prime cell.  It is the
scalar form of the repository's `+,-,-,+` mixed fresh-prime update; unlike the
cumulative shell it telescopes over `p`.

Every composite `q in J_R(k)` has `minFac(q)<R`, because `q<X_R<R^2`.
Therefore after all primes through `R` have been processed,

\[
Q_{\le R}(k)=N_R(k),
\qquad
C_{\le R}(k)=M(k).
\]

Consequently the executable checks the exact identity

\[
\boxed{
|J_R(k)|+\sum_{p\le R}D_p(k)=N_R(k)M(k)
}
\]

for every reciprocal fibre `k`.

## 5. Finite gate

For every active exact cell define

\[
\rho_{p,k}
=
\frac{|D_p(k)|}
{|A_p(k)Q_{\le p}(k)|+|C_{<p}(k)H_p(k)|}.
\]

For dyadic rectangles in `log p x log k`, aggregate the two signed components
first and apply the same ratio to the cell totals.  A local anti-alignment
mechanism would require these ratios to be substantially below `1`, and in the
strong version motivating this test close to `0` across most of the mass.

The exact output is:

| `R` | exact median | exact fraction `<=0.1` | exact `sum|D|/sum(parts)` | dyadic `sum|cell|/sum(parts)` |
|---:|---:|---:|---:|---:|
| 200 | 1.000000 | 0.000963 | 0.982274 | 0.937991 |
| 500 | 1.000000 | 0.002160 | 0.980214 | 0.933153 |
| 1000 | 1.000000 | 0.001766 | 0.978392 | 0.929516 |
| 2000 | 1.000000 | 0.000941 | 0.976719 | 0.928286 |
| 5000 | 1.000000 | 0.000702 | 0.974859 | 0.926648 |
| 10000 | 1.000000 | 0.000509 | 0.973751 | 0.925510 |

At every scale the independent consistency checks are exactly zero:

* final q-survivor vector equals `N_R(k)`;
* final cofactor cube equals `M(k)`;
* every fibre telescope closes;
* the global sum of initial state plus all fresh-prime increments equals
  `sum_k N_R(k) M(k)`.

The largest dyadic cells are usually ratio `1`: the two fresh-prime components
reinforce rather than cancel.  Dyadic localization changes only a few percent of
the total `L1` mass.

## 6. Why the proposed `N_R(k) A_p(k)` term is incomplete

The exact cofactor piece uses `Q_{<=p}(k)`, not the final prime multiplicity
`N_R(k)`.  In fact

\[
Q_{\le p}(k)
=N_R(k)+\sum_{r>p}H_r(k),
\]

so

\[
-A_p(k)Q_{\le p}(k)
=-A_p(k)N_R(k)
 -A_p(k)\sum_{r>p}H_r(k).
\]

Thus replacing the evolving q-survivor population by the terminal positive
weight `N_R(k)` deletes the exact future-hit channel.  That missing term already
contains another ordered prime coordinate `r>p`.

This is the structural diagnosis of the negative `(p,k)` gate:

\[
\boxed{
\text{the additive chronology is not genuinely two-dimensional after }r
\text{ is summed out.}
}
\]

## 7. Route decision

The predecessor-prime coordinate is useful and should be retained as exact
bookkeeping, but the local `(p,k)` anti-alignment proposal fails the finite gate
strongly.  No `(p,k)` analytic bound is proposed.

The next candidate, if this elementary line is continued, must preserve the
future first-hit coordinate before summation, for example an ordered

\[
(p,r,k),\qquad p<r,
\]

state, or an equivalent genuinely bilinear expansion of the long cofactor.
That is the first place where the exact term `A_p(k) H_r(k)` remains visible
instead of being absorbed into the cumulative q-survivor count.

This conclusion is narrower than the completed-fibre no-go: it does not kill
multi-prime Type-II structure.  It says that **one predecessor prime plus one
reciprocal quotient is still not enough once the future prime-hit chronology is
summed away**.

Reproduce with:

```bash
g++ -O3 -std=c++17 research/pk_fresh_step_gate.cpp -o /tmp/pk_gate
/tmp/pk_gate
```

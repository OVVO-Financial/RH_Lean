# Centered distinguished-prime cross-q Gram falsification

## Verdict

The natural unweighted coefficient-space Gram built from the exact physical
centered distinguished-prime coefficients of PR #422 fails the predeclared
anti-correlation test by a very large margin.

For this object the signed off-diagonal term is not near

\[
O_R \approx -\tfrac12 D_R.
\]

It is large and positive, and the positive coherence strengthens with scale.
The failure persists after the exact reciprocal-window regrouping

\[
Q_d=\{q:R<q\le R^2-1,\ q\text{ prime},\ \lfloor(R^2-1)/q\rfloor=d\}.
\]

Therefore this coefficient-space interpretation of the centered cross-q Gram
should not be promoted to the open `O_epsilon(R^(2+epsilon))` theorem in
`MertensEnergyRHForward.lean`.

This is an empirical route falsification, not an RH theorem and not a formal
no-go theorem for every possible weighted input. The existing Lean definition
`centeredCrossQGram R q q' x` is input-dependent. No concrete reconstruction
input or nontrivial weight matrix `W` is currently formalized there. Any future
weighted variant must fix that arithmetic input before a new finite test is run;
the unit coefficient Gram tested here is closed as the intended mechanism.

## Exact coefficient object tested

For one distinguished prime `q`, PR #422 gives the exact arithmetic coefficient
families

- `physicalDistinguishedPrimeA`,
- `physicalDistinguishedPrimeCenteredB`,
- `physicalDistinguishedPrimeC`.

The diagnostic follows those definitions directly. A nonzero local physical
fibre mass forces one of the two adjacent physical states to be active, so the
inactive-to-inactive transition contributes zero in this extracted coefficient
ledger. The tested vector is therefore

\[
v_R(q)=(B^c_{R,q,t})_{t\in\mathcal A}\oplus(C_{R,q,s})_{s\in\mathcal A},
\]

with six centered `B` coordinates and six `C` coordinates. The implementation
multiplies all coordinates by six so the entire computation is integral:

\[
6B^c_t=6B_t-\sum_u B_u,\qquad 6C_s=6C_s.
\]

No empirical row normalization is introduced.

For `X=R^2-1` and `q in Q_d`, the exact cofactor range is simply
`1 <= c <= d`. Each nonzero `mu(c)` produces the same physical slot and visible
sign label used by #422, with `mu(c q)=-mu(c)` because `c<R<q` and `q` is prime.
Boundary cells are handled exactly as in the adjacent transition ledger:

- a hit outside the first cell contributes to `B`,
- a hit before the last carrier cell contributes to `C`.

## No pairwise Gram bounds or pairwise loop

The diagnostic never forms `abs(G_R(q,q'))` and never loops over pairs of
primes.

Let the integer-scaled vector be `w_q=6 v_R(q)`. It computes

\[
36D_R=\sum_q \|w_q\|^2
\]

and only after the full signed sum is assembled uses polarization:

\[
36O_R=
\frac12\left(
\left\|\sum_q w_q\right\|^2-
\sum_q\|w_q\|^2
\right).
\]

The reciprocal-window version first forms

\[
S_d=\sum_{q\in Q_d}w_q.
\]

Then

\[
36O_R^{\rm within}
=
\frac12\left(
\sum_d\|S_d\|^2-36D_R
\right),
\]

and

\[
36O_R^{\rm cross-window}
=
\frac12\left(
\left\|\sum_d S_d\right\|^2-
\sum_d\|S_d\|^2
\right).
\]

Thus the reported cross-window number is itself a fully signed global object.

## Numerical result

The reproducible scan is recorded in
`experiments/centered_cross_q_gram_results.csv`.

| R | O_R / D_R | within-window O_R / D_R | cross-window O_R / D_R |
|---:|---:|---:|---:|
| 500 | 945.5228 | 36.6429 | 908.8799 |
| 1000 | 2104.3953 | 65.7184 | 2038.6770 |
| 2000 | 4627.3648 | 119.7761 | 4507.5887 |
| 4000 | 9989.3582 | 217.4963 | 9771.8619 |
| 5561 | 14367.6571 | 289.7499 | 14077.9073 |
| 8000 | 21399.2414 | 397.5526 | 21001.6888 |
| 10000 | 27369.6508 | 484.8308 | 26884.8200 |

The required viability signature is approximately `-0.5`. The observed sign is
opposite and the magnitude grows by four to five orders relative to the target.
Most of the coherence is genuinely between different reciprocal windows, so
regrouping by `Q_d` does not reveal hidden anti-correlation.

At `R=5561`, for example,

\[
D_R\approx 2.2346\times10^9,
\qquad
O_R\approx 3.2106\times10^{13},
\qquad
O_R/D_R\approx 14367.6571.
\]

By contrast, the already-recorded square-root root/smooth scalar diagnostic at
the same scale has

\[
U=125204,\qquad V=-127749,
\]

so

\[
\frac{UV}{U^2+V^2}
\approx -0.4998988.
\]

That is the anti-correlation signature the coefficient-space distinguished-prime
Gram fails to reproduce.

## Why the Li split is not promoted

The repository already has the legal reciprocal-window decomposition of the
prime indicator into singleton Li density plus prime-count discrepancy. That
split is an exact change of proof coordinates. It cannot change the value or
sign of the fully recombined Gram.

The declared workflow required the finite anti-correlation gate before a formal
Li/discrepancy attack. Since the exact physical coefficient Gram fails that gate,
no new Lean theorem is added that decomposes this failed object into Li bulk and
discrepancy. Doing so would only repartition the same large positive
cross-window coherence and risk mistaking a decomposition for contraction.

The centering order remains non-negotiable for any successor route: remove the
active constant mode first, then split the prime indicator. The present failure
occurs even after the #422 centered `B` coefficients are used.

## Consequence for the analytic route

Do not attempt to rescue this object with

- pairwise bounds on `|G_R(q,q')|`,
- a fixed-q contraction,
- separate positive shell estimates,
- or a Li/discrepancy triangle inequality.

The finite evidence points back to the cross-region mechanism already isolated
in `SQUARE_ROOT_LEGAL_GRAM_ATTACK.md`: the dominant cancellation is lower-prime
smooth mass against upper-prime transport mass. That signed root/smooth object
passes the `O/D approximately -1/2` test, while the centered upper-prime
coefficient Gram tested here does not.

A successor Gram should therefore contain both sides of that cross-region
interaction before any norm is taken.

## Reproduction

Compile and run the diagnostic with, for example,

```text
g++ -O3 -std=c++17 -Wall -Wextra experiments/centered_cross_q_gram_diagnostic.cpp -o centered_cross_q_gram_diagnostic
./centered_cross_q_gram_diagnostic 500 1000 2000 4000 5561
```

The `8000` and `10000` rows use the same program with those scales supplied on
the command line. The computation uses exact integer accumulation for all Gram
quantities; floating point is used only when printing ratios.

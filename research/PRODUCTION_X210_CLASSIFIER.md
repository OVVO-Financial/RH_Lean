# Production analogue of the x = 210 amplitude census

The finite x=210 model is useful for bookkeeping, but it is not itself a
production endpoint. This note evaluates the same exact first parent/child
pairing at

\[
X_R=R^2-1.
\]

The diagnostic is reproducible with

```bash
python3 experiments/production_x210_classifier.py
```

## Exact general accounting

Let \(n\le X_R\) be squarefree and have a prime factor \(p>R\).
Because \(X_R<R^2\), there is at most one such prime. Hence

\[
n=c p,\qquad c<R.
\]

Pair every odd outer state \(cp\) with \(2cp\) whenever the child is still
below the endpoint. The pair cancels exactly because

\[
\mu(2cp)=-\mu(cp).
\]

Therefore the unpaired population is exactly

\[
X_R/2 < cp\le X_R,
\]

and for each odd squarefree cofactor \(c<R\) its cardinality is

\[
H_R(c)-H_R(2c),
\qquad
H_R(c)=\#\{p>R:\ p\text{ prime},\ cp\le X_R\}.
\]

Its signed contribution is

\[
-\mu(c)\bigl(H_R(c)-H_R(2c)\bigr).
\]

This is the direct production analogue of the five-row table in
`AMPLITUDE_X210_EXACT_EXAMPLE.md`.

## R = 15, X_R = 224

The outer squarefree population is

\[
104=62+42,
\]

with 31 exact parent/child pairs and 42 unpaired boundary survivors.

The cofactor table is

| c | mu(c) | H(c) | H(2c) | survivors | amplitude |
|---:|---:|---:|---:|---:|---:|
| 1 | 1 | 42 | 23 | 19 | -19 |
| 3 | -1 | 15 | 6 | 9 | 9 |
| 5 | -1 | 8 | 2 | 6 | 6 |
| 7 | -1 | 5 | 0 | 5 | 5 |
| 11 | -1 | 2 | 0 | 2 | 2 |
| 13 | -1 | 1 | 0 | 1 | 1 |

Thus

\[
-19+9+6+5+2+1=4.
\]

So the x=210 exact cancellation does **not** persist even at the nearest genuine
square endpoint.

## R = 56, X_R = 3135

At the repository's standard production threshold,

\[
1475=918+557
\]

outer squarefree states split into 459 exact parent/child pairs and 557 boundary
survivors. Their signs are

\[
255\text{ negative},\qquad302\text{ positive},
\]

so the surviving signed amplitude is

\[
\boxed{47}.
\]

The same cofactor formula reconstructs every one of the 557 survivors exactly.
There are 22 nonempty cofactor rows.

## What this settles

The x=210 example *does* generalize as a clean accounting identity:

1. unique high-prime factorization \(n=cp\);
2. exact \(2\)-parent/child cancellation;
3. a residual boundary table indexed only by \(c<R\);
4. no unclassified states in this first-stage census.

But the final boundary sum is not identically zero at production endpoints.
The zero at x=210 is a special finite cancellation.

Therefore the remaining proof cannot be closed by declaring the x=210 terminal
balance universal. The correct formal next step is to feed the residual
cofactor table into the repository's later response/re-entry classification:

\[
\text{boundary survivor}
\to
\text{completed second contact}
\sqcup
\text{second-boundary defect},
\]

where the second-boundary defect already has a full-face mate.

This diagnostic sharply separates the tasks:

- the first-stage x=210 bookkeeping is fully general and exact;
- the unresolved content begins only after the nonzero production boundary
  amplitude is handed to the later response/q^2 machinery.

No asymptotic claim is made here.

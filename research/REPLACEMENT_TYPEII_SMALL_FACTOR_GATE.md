# Small-factor Type-II finite gate

This is the last one-variable finite test after the reciprocal fibre label `z` has been collapsed exactly.

The scalar state remains

\[
B_R=B_R^{\mathrm{root}}+B_R^{\mathrm{smooth}}
=M(R-1)-M(R^2-1).
\]

No new state, Gram, or analytic Lean proposition is introduced.

## Correct geometric length variable

For a canonical oriented atom `n=cq` with `q=P+(n)`, define

\[
s(c,q)=\min(c,q),\qquad \ell(c,q)=\max(c,q).
\]

On the root orientation, `c<q`, so `s=c` and `ell=q`.  On the smooth orientation, `q<c`, so `s=q` and `ell=c`, with the existing roughness condition `P+(c)<q`.

The Type-I / Type-II cut is therefore

\[
\mathrm{I}: s\le R^\theta,
\qquad
\mathrm{II}: s>R^\theta.
\]

This fixes the geometric defect of the ancestry-cofactor cut: smooth Type I is no longer forbidden merely because the ancestry cofactor is the long factor there.

## Exact collapsed forms

The root scalar is

\[
B_R^{\mathrm{root}}
=\sum_{1\le c<R}\mu(c)
\#\{q\text{ prime}:c<q,\ R\le cq\le X_R\},
\qquad X_R=R^2-1.
\]

The smooth scalar is

\[
B_R^{\mathrm{smooth}}
=\sum_{q<R\atop q\text{ prime}}
\sum_{\substack{c>q\\P^+(c)<q\\R\le cq\le X_R}}\mu(c).
\]

For the small-factor cut, root Type I is `c<=R^theta`, while smooth Type I is `q<=R^theta`.

The total dictionary remains exact.  For all tested `R`,

| `R` | `B_root` | `B_smooth` | `B` | `M(R-1)-M(X_R)` | error |
|---:|---:|---:|---:|---:|---:|
| 200 | -477 | 479 | 2 | 2 | 0 |
| 500 | -2101 | 2134 | 33 | 33 | 0 |
| 1000 | -6729 | 6519 | -210 | -210 | 0 |
| 2000 | -22096 | 21909 | -187 | -187 | 0 |

So only the length decomposition is being tested.

## A finite geometric sparsity effect on smooth Type I

The small-factor split is geometrically correct, but for the requested moderate `R` it admits very few smooth squarefree atoms at the tested cutoffs.

If `mu(c) != 0` and `P+(c)<q`, then every prime factor of `c` is below `q`, hence

\[
c\le \prod_{p<q}p.
\]

The support condition `R<=cq` therefore requires

\[
q\prod_{p<q}p\ge R.
\]

This is only a necessary condition, but it explains why the first smooth Type-I atoms occur late at the present scales.  For example, at `R=2000`, `q=11` is the first possible small prime because

\[
7(2\cdot3\cdot5)=210<2000,
\qquad
11(2\cdot3\cdot5\cdot7)=2310>2000.
\]

Thus the small-factor cut is not empty by theorem, but it is still very sparse in the requested finite gate.

## Exact small-factor table

The cut is `C=floor(R^theta)` for `theta in {1/4,1/3,2/5}`.  `smooth I edges` is the unweighted number of canonical smooth pairs in Type I; `smooth I` is their signed Möbius mass.

| `R` | `theta` | `C` | root I | smooth I | smooth I edges | root II | smooth II | signed II |
|---:|:---:|---:|---:|---:|---:|---:|---:|---:|
| 200 | 1/4 | 3 | 355 | 0 | 0 | -832 | 479 | -353 |
| 200 | 1/3 | 5 | -640 | 0 | 0 | 163 | 479 | 642 |
| 200 | 2/5 | 8 | -535 | -1 | 1 | 58 | 480 | 538 |
| 500 | 1/4 | 4 | 2172 | 0 | 0 | -4273 | 2134 | -2139 |
| 500 | 1/3 | 7 | -2375 | 0 | 0 | 274 | 2134 | 2408 |
| 500 | 2/5 | 12 | -2154 | -1 | 3 | 53 | 2135 | 2188 |
| 1000 | 1/4 | 5 | -9649 | 0 | 0 | 2920 | 6519 | 9439 |
| 1000 | 1/3 | 10 | 1887 | 0 | 0 | -8616 | 6519 | -2097 |
| 1000 | 2/5 | 15 | -743 | -1 | 15 | -5986 | 6520 | 534 |
| 2000 | 1/4 | 6 | 21945 | 0 | 0 | -44041 | 21909 | -22132 |
| 2000 | 1/3 | 12 | -22108 | 1 | 1 | 12 | 21908 | 21920 |
| 2000 | 2/5 | 20 | -40159 | -5 | 141 | 18063 | 21914 | 39977 |

The symmetric cut therefore does not create the requested two-sided Type-I cancellation at these scales.  Even at `R=2000`, `theta=2/5`, there are 141 smooth Type-I edges but their signed mass is only `-5`, against root Type-I mass `-40159`.

## Type-I main-mode diagnostic

For the root Type-I prime increment only, use the same finite PNT proxy as the preceding gate,

\[
P(x)=x/\log x.
\]

Let `Main_root,I` be the Möbius-weighted difference of these endpoint proxies and

\[
E_{\pi,I}=B_{R,I}^{\mathrm{root}}-\mathrm{Main}_{\mathrm{root},I}.
\]

If the exact smooth Type-I term were already cancelling the root Type-I main mode down to prime-error size, the quantity

\[
\frac{|\mathrm{Main}_{\mathrm{root},I}+B_{R,I}^{\mathrm{smooth}}|}
{|E_{\pi,I}|}
\]

would be expected to be at most order one.  The observed values are:

| `R` | `theta` | ratio |
|---:|:---:|---:|
| 200 | 1/4 | 92.08 |
| 200 | 1/3 | 4.73 |
| 200 | 2/5 | 4.24 |
| 500 | 1/4 | 31.68 |
| 500 | 1/3 | 5.11 |
| 500 | 2/5 | 4.82 |
| 1000 | 1/4 | 6.08 |
| 1000 | 1/3 | 7.04 |
| 1000 | 2/5 | 0.38 |
| 2000 | 1/4 | 60.38 |
| 2000 | 1/3 | 5.81 |
| 2000 | 2/5 | 7.27 |

The favorable `R=1000`, `theta=2/5` row again does not persist at `R=2000`.

This proxy is only a diagnostic, not an analytic theorem.  Its role is to test the proposed finite acceptance criterion before formalization.

## Type-II scale gate

The decisive ratio is the signed Type-II remainder against the endpoint scale.

| `R` | `theta` | `|B_II| / |M(X_R)-1|` | `|B_II| / |U_R|` |
|---:|:---:|---:|---:|
| 200 | 1/4 | 32.09 | 0.743 |
| 200 | 1/3 | 58.36 | 1.352 |
| 200 | 2/5 | 48.91 | 1.133 |
| 500 | 1/4 | 53.48 | 1.014 |
| 500 | 1/3 | 60.20 | 1.142 |
| 500 | 2/5 | 54.70 | 1.037 |
| 1000 | 1/4 | 44.73 | 1.398 |
| 1000 | 1/3 | 9.94 | 0.311 |
| 1000 | 2/5 | 2.53 | 0.079 |
| 2000 | 1/4 | 115.87 | 1.000 |
| 2000 | 1/3 | 114.76 | 0.990 |
| 2000 | 2/5 | 209.30 | 1.806 |

At `R=2000`, every requested small-factor cut leaves the Type-II remainder at root scale or larger, and roughly two orders of magnitude above endpoint scale.

## Decision

The two failed one-variable tests should be distinguished:

1. The ancestry-cofactor cut fails **geometrically**: below `sqrt(R)` it can contain no smooth Type-I edge at all because ancestry `c` is the long factor on the smooth side.
2. The small-factor cut uses the correct geometry and does admit smooth Type-I atoms, but it **fails the requested finite acceptance gate** at `R=2000`.  It does not produce stable Type-I root-smooth main-mode cancellation, and its Type-II remainder remains root-scale.

Therefore the one-variable length program is closed on the requested finite evidence.  No analytic Lean proposition should be introduced for either split.

The next candidate is genuinely two-dimensional inside the existing canonical `(c,q)` incidence: expand only the long composite cofactor in the smooth Type-II piece, for example by one order-3 Heath-Brown/Vaughan-style Möbius identity, while retaining the orientation and hyperbolic support.  The auxiliary factors are a partition of the existing cofactor, not a new state.

The executable reproducing this table is `research/replacement_typeii_small_factor_gate.cpp`.

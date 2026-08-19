# Collapsed Type-II scalar finite gate

This note tests the post-#430 scalar route after summing the reciprocal fibre label `z` exactly and retaining only the canonical cofactor-prime pair `(c,q)`.

No Lean proposition or analytic estimate is added here. The purpose is to decide whether the proposed one-variable Type-I / Type-II split on the cofactor `c` survives the requested finite gate.

## Exact collapsed dictionaries

At

\[
X_R=R^2-1,
\]

define

\[
B_R^{\mathrm{root}}
=\sum_{1\le c<R}\mu(c)
\#\{q\text{ prime}:c<q,\ R\le cq\le X_R\},
\]

and

\[
B_R^{\mathrm{smooth}}
=\sum_{1\le c\le X_R}\mu(c)
\#\{q\text{ prime}:P^+(c)<q<c,\ R\le cq\le X_R\}.
\]

These are exactly the sums of the root and smooth dictionaries from `ReplacementFibreCofactorWindows.lean` after summing over `z`.

The root count is evaluated as the exact prime increment

\[
\pi\!\left(\left\lfloor\frac{X_R}{c}\right\rfloor\right)
-
\pi\!\left(\max\!\left(c,\left\lceil\frac Rc\right\rceil-1\right)\right).
\]

The smooth count keeps the canonical roughness condition `P+(c) < q < c`; it is not replaced by a generic composite condition.

With

\[
B_R=B_R^{\mathrm{root}}+B_R^{\mathrm{smooth}},
\]

the exact sign convention is

\[
B_R=M(R-1)-M(X_R),
\qquad
M(X_R)-1=M(R-1)-1-B_R.
\]

The computation constructs `B_root` and `B_smooth` directly from the dictionaries. `M` is computed separately only as a consistency check.

## Exact total check

| `R` | `B_root` | `B_smooth` | `B` | `M(R-1)-M(X_R)` | error | `U_R` | `V_R` | `M(R-1)-1` | `M(X_R)-1` |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 200 | -477 | 479 | 2 | 2 | 0 | 475 | -486 | -9 | -11 |
| 500 | -2101 | 2134 | 33 | 33 | 0 | 2109 | -2149 | -7 | -40 |
| 1000 | -6729 | 6519 | -210 | -210 | 0 | 6752 | -6541 | 1 | 211 |
| 2000 | -22096 | 21909 | -187 | -187 | 0 | 22140 | -21949 | 4 | 191 |

So collapsing `z` is exact and preserves the global root-smooth cancellation. The question is whether the usual length split in the single cofactor variable preserves enough of it.

## The proposed Type-I cut has no smooth edges

For every requested exponent `theta < 1/2`, if

\[
c\le R^\theta
\]

and `(c,q)` is smooth-oriented, then `q<c`, hence

\[
cq<c^2\le R^{2\theta}<R.
\]

This contradicts the physical support `R <= cq`.

Therefore

\[
\boxed{B_{R,\mathrm{I}}^{\mathrm{smooth}}=0}
\]

identically for the proposed Type-I region. In particular, root-smooth cancellation cannot occur *inside* Type I for any of the requested cuts. The whole smooth dictionary is automatically placed in Type II.

## Finite Type-I / Type-II split

The exact cut is `c <= floor(R^theta)` for `theta in {1/4,1/3,2/5}`.

| `R` | `theta` | cut | root I | smooth I | root II | smooth II | signed II |
|---:|:---:|---:|---:|---:|---:|---:|---:|
| 200 | 1/4 | 3 | 355 | 0 | -832 | 479 | -353 |
| 200 | 1/3 | 5 | -640 | 0 | 163 | 479 | 642 |
| 200 | 2/5 | 8 | -535 | 0 | 58 | 479 | 537 |
| 500 | 1/4 | 4 | 2172 | 0 | -4273 | 2134 | -2139 |
| 500 | 1/3 | 7 | -2375 | 0 | 274 | 2134 | 2408 |
| 500 | 2/5 | 12 | -2154 | 0 | 53 | 2134 | 2187 |
| 1000 | 1/4 | 5 | -9649 | 0 | 2920 | 6519 | 9439 |
| 1000 | 1/3 | 10 | 1887 | 0 | -8616 | 6519 | -2097 |
| 1000 | 2/5 | 15 | -743 | 0 | -5986 | 6519 | 533 |
| 2000 | 1/4 | 6 | 21945 | 0 | -44041 | 21909 | -22132 |
| 2000 | 1/3 | 12 | -22108 | 0 | 12 | 21909 | 21921 |
| 2000 | 2/5 | 20 | -40159 | 0 | 18063 | 21909 | 39972 |

The isolated `R=1000`, `theta=2/5` row looks favorable, but it is not stable: at `R=2000` all three cuts return to root-scale remainders.

## Type-I PNT main-term diagnostic

For the finite diagnostic only, use the elementary PNT proxy

\[
P(x)=\frac{x}{\log x}
\]

and define the signed interval main term

\[
\mathcal P_{R,\mathrm I}
=
\sum_{c\le R^\theta}\mu(c)
\left[
P\!\left(\frac{X_R}{c}\right)
-
P\!\left(\max\!\left(c,\left\lceil\frac Rc\right\rceil-1\right)\right)
\right].
\]

Let

\[
E_{R,\mathrm I}=B_{R,\mathrm I}-\mathcal P_{R,\mathrm I}.
\]

If the Möbius-weighted Type-I main mode had already canceled to prime-error scale, one would expect `|P_I|` to be at most comparable with `|E_I|`. The observed ratio is:

| `R` | `theta` | `|P_I| / |E_I|` |
|---:|:---:|---:|
| 200 | 1/4 | 92.08 |
| 200 | 1/3 | 4.73 |
| 200 | 2/5 | 4.23 |
| 500 | 1/4 | 31.68 |
| 500 | 1/3 | 5.11 |
| 500 | 2/5 | 4.82 |
| 1000 | 1/4 | 6.08 |
| 1000 | 1/3 | 7.04 |
| 1000 | 2/5 | 0.37 |
| 2000 | 1/4 | 60.38 |
| 2000 | 1/3 | 5.81 |
| 2000 | 2/5 | 7.27 |

Again the single favorable `R=1000`, `theta=2/5` row is not stable. At `R=2000` the signed PNT main term is between about six and sixty times the corresponding prime-counting error for the requested cuts.

## Type-II scale diagnostic

The decisive requested gate is whether the signed Type-II remainder is endpoint-scale rather than root-scale.

| `R` | `theta` | `|B_II| / |M(X_R)-1|` | `|B_II| / |U_R|` |
|---:|:---:|---:|---:|
| 200 | 1/4 | 32.09 | 0.743 |
| 200 | 1/3 | 58.36 | 1.352 |
| 200 | 2/5 | 48.82 | 1.131 |
| 500 | 1/4 | 53.48 | 1.014 |
| 500 | 1/3 | 60.20 | 1.142 |
| 500 | 2/5 | 54.68 | 1.037 |
| 1000 | 1/4 | 44.73 | 1.398 |
| 1000 | 1/3 | 9.94 | 0.311 |
| 1000 | 2/5 | 2.53 | 0.079 |
| 2000 | 1/4 | 115.87 | 1.000 |
| 2000 | 1/3 | 114.77 | 0.990 |
| 2000 | 2/5 | 209.28 | 1.805 |

At `R=2000`, for all three requested cuts, the Type-II remainder is essentially `U_R` scale or larger and is more than two orders of magnitude larger than the endpoint scale.

## Gate decision

The exact scalar collapse passes, but the proposed **one-variable cofactor length split fails the finite gate**.

1. `B_root + B_smooth = M(R-1)-M(X_R)` holds exactly for every tested `R`.
2. For `theta < 1/2`, the smooth Type-I region is empty identically, so a Type-I root-smooth main-term cancellation cannot occur there.
3. The Möbius-weighted Type-I PNT main term is not stably reduced to prime-error scale on the requested data.
4. Most decisively, at `R=2000` the Type-II remainder is still root-scale for every requested cut.

Therefore no `ReplacementTypeIIBound` Lean proposition is introduced from this decomposition. The finite gate says that collapsing `z` is harmless, but splitting only by the single cofactor length cuts across the actual root-smooth cancellation.

The next analytic candidate, if pursued, must keep a genuinely bilinear or multilinear prime interaction inside the existing `(c,q)` incidence—for example an in-place Heath-Brown style expansion of the Möbius cofactor—rather than turning the scalar into a one-variable `mu(c) * pi(X/c)` estimate or adding a new combinatorial state.

The executable reproducing these values is `research/replacement_typeii_scalar_gate.cpp`.

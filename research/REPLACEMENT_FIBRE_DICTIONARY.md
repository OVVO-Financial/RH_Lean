# Replacement fibre dictionary

At the square endpoint

\[
X_R=R^2-1,
\]
write

\[
b_R(y)=\sum_{\substack{R\le n\le X_R\\\lfloor X_R/n\rfloor=y}}C_R(n),
\qquad
t_R(y)=\sum_{\substack{R\le n\le X_R\\\lfloor X_R/n\rfloor=y}}\mu(n),
\]

and

\[
a_R(y)=\mathbf 1_{y=R-1}-b_R(y).
\]

The finite computation was run at `R = 100, 200, 500, 1000` using exact integer arithmetic. It checks the physical replacement row, the complementary Möbius fibres, and the lower-triangular quotient kernel.

## Exact quotient-kernel dictionary

Define

\[
K(z,y)=\#\{1\le k\le z:\lfloor z/k\rfloor=y\}.
\]

Equivalently, for `y >= 1`,

\[
K(z,y)=\left\lfloor\frac zy\right\rfloor-
       \left\lfloor\frac z{y+1}\right\rfloor.
\]

The exact Type-II relation is

\[
\boxed{
 b_R(y)=-\sum_{z<R}K(z,y)t_R(z).
}
\]

This is not a nearest-neighbour transfer in `y`; it is the hyperbola transform obtained by writing the complementary large divisor as `d` and the remaining factor as `k`.

The kernel is lower triangular:

\[
K(z,y)=0\quad(y>z),
\qquad
K(z,z)=1.
\]

Hence

\[
b_R(y)=-t_R(y)-\sum_{z>y}K(z,y)t_R(z).
\]

This dictionary is the structural theorem. It shows that `C_R`, `b_R`, and hence `a_R` are linear images of the complementary fibre state `t_R` rather than independent arithmetic data.

## The surviving fibre state

For `1 <= z < R`, the physical tail clipping is automatic and the fibre is exactly

\[
I_z=
\left(
\left\lfloor\frac{X_R}{z+1}\right\rfloor,
\left\lfloor\frac{X_R}{z}\right\rfloor
\right].
\]

Therefore

\[
\boxed{
 t_R(z)
 =M\!\left(\left\lfloor\frac{X_R}{z}\right\rfloor\right)
 -M\!\left(\left\lfloor\frac{X_R}{z+1}\right\rfloor\right).
}
\]

Thus the only surviving arithmetic state after the dictionary is the signed vector of hyperbola Mertens increments `(t_R(z))_{z<R}`.

The geometry is strongly nonuniform:

| fibres | length of `I_z` | role |
|---|---:|---|
| `z = 1` | `~ R^2 / 2` | old top half |
| `z << R` | `~ R^2 / z^2` | long Type-II intervals |
| `z ~ R` | `O(1)` | already root-scale |

The top-prime obstruction is therefore transported to the long first fibres, especially `t_R(1)`; it is not removed by the dictionary.

## Classical renewal and the tautological reconstruction

For every `z >= 1`, the classical Möbius unit identity gives

\[
\sum_{k=1}^{z}M(\lfloor z/k\rfloor)=1.
\]

Grouping the `k` values by their quotient `y` gives

\[
\sum_y K(z,y)(M(y)-1)=1-z.
\]

Composing this identity with `b_R=-K t_R` is legitimate algebra, but it does not produce a new analytic cancellation theorem. It gives

\[
\sum_y b_R(y)(M(y)-1)
 =\sum_{z<R}t_R(z)(z-1).
\]

After adding the first moment

\[
S_R=-\sum_{z<R}z\,t_R(z),
\]

the weights cancel algebraically:

\[
-(z-1)t_R(z)+z t_R(z)=t_R(z).
\]

What remains is only

\[
\boxed{
\sum_{z<R}t_R(z)=M(X_R)-M(R-1),
}
\]

which is the ordinary partition of the Möbius sum over `[1,X_R]` into `[1,R-1]` and `[R,X_R]`.

Consequently

\[
\sum_y a_R(y)(M(y)-1)+\sum_{z<R}z\,t_R(z)=M(X_R)-1
\]

is a consistency reconstruction of the definition of `M`, rewritten on reciprocal hyperbola fibres. It carries no additional power-saving information.

## Finite diagnostics

Let

\[
P_R=\sum_y a_R(y)(M(y)-1),
\qquad
Q_R=\sum_y y\,t_R(y)=-S_R,
\qquad
J_R=P_R+Q_R=M(X_R)-1.
\]

The exact values are:

| `R` | `M(X_R)` | `S_R` | `P_R` | `Q_R` | `J_R` |
|---:|---:|---:|---:|---:|---:|
| 100 | -23 | 310 | 286 | -310 | -24 |
| 200 | -10 | -1228 | -1239 | 1228 | -11 |
| 500 | -39 | -2127 | -2167 | 2127 | -40 |
| 1000 | 212 | 4406 | 4617 | -4406 | 211 |

These values are consistency checks for the exact reindexing. In particular, `P_R+Q_R=211` at `R=1000` must hold because the two terms are complementary rewritings of the same tail partition; it is not an independent cancellation estimate.

### Is the raw same-`y` joint term sparse?

No. Define

\[
j_R(y)=a_R(y)(M(y)-1)+y\,t_R(y).
\]

The fraction of `sum_y |j_R(y)|` carried by the 50 largest fibres is:

| `R` | top 50 fraction |
|---:|---:|
| 100 | 83.26% |
| 200 | 50.89% |
| 500 | 24.72% |
| 1000 | 13.58% |

At `R=1000`, the top five fibres carry only 1.67% of the absolute mass. The raw same-`y` residue is therefore broadly distributed rather than concentrated in one extra Farey window.

### Is `b_R(y)` locally proportional to `y t_R(y)`?

No. The Pearson correlation of the two exact vectors is near zero:

| `R` | correlation `corr(b_R, y t_R)` |
|---:|---:|
| 100 | -0.0865 |
| 200 | -0.0118 |
| 500 | -0.0176 |
| 1000 | -0.0072 |

The correct relation is the quotient-kernel transform, not `b_R(y)=y t_R(y)` plus a nearest-neighbour correction.

### Abel comparison

For

\[
S_R=M(R-1)(R+1)-1+
\sum_{n=1}^{R-2}M(n)
\left(\left\lfloor\frac{X_R}{n}\right\rfloor-
      \left\lfloor\frac{X_R}{n+1}\right\rfloor\right),
\]

the main term and residual are:

| `R` | Abel main | Abel residual | `S_R` |
|---:|---:|---:|---:|
| 100 | 100 | 210 | 310 |
| 200 | -1609 | 381 | -1228 |
| 500 | -3007 | 880 | -2127 |
| 1000 | 2001 | 2405 | 4406 |

Crude absolute-value treatment of these two Abel pieces destroys the same sign information that survives in the fibre vector. The Abel form is therefore another coordinate system for the problem, not an independent route to a bound on `S_R`.

## Route decision

The involution search is closed. The dictionary has eliminated `C_R`, `b_R`, `a_R`, and `S_R` as independent state. The remaining arithmetic object is

\[
(t_R(z))_{z<R},
\qquad
 t_R(z)=M(H_z)-M(L_z-1).
\]

The next exact task is to split this same fibre state into prime-supported and composite-supported increments and identify those pieces with differences of the existing root/transport and smooth operators on the same hyperbola intervals.

The analytic obligation is then a single Type-II estimate:

> bound the signed sum of hyperbola Mertens increments jointly with the existing root-smooth state, using the hyperbolic incidence `K` or its prime restriction before any `l1` or `l2` norm, without estimating the first moment `S_R` separately.

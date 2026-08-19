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

The finite computation was run at `R = 100, 200, 500, 1000` using exact integer arithmetic. It checks the physical replacement row, the complementary Möbius fibres, the joint shifted row, and the lower-triangular quotient kernel.

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

The computation verifies identically at every tested scale that

\[
\boxed{
 b_R(y)=-\sum_{z<R}K(z,y)t_R(z).
}
\]

This is not a nearest-neighbour transfer in `y`; it is the exact Type-II hyperbola transform obtained by writing the complementary large divisor as `d` and the remaining factor as `k`.

The diagonal is `K(y,y)=1`, so

\[
b_R(y)=-t_R(y)-\sum_{z>y}K(z,y)t_R(z).
\]

Thus the fibre dictionary is genuinely lower triangular.

## Renewal inside one `z` fibre

For every `z >= 1`, the classical Möbius unit identity gives

\[
\sum_{k=1}^{z}M(\lfloor z/k\rfloor)=1.
\]

Grouping the `k` values by their quotient `y` gives

\[
\boxed{
\sum_y K(z,y)(M(y)-1)=1-z.
}
\]

Consequently

\[
\sum_y b_R(y)(M(y)-1)
 =\sum_{z<R}t_R(z)(z-1).
\]

The final row therefore satisfies

\[
\sum_y a_R(y)(M(y)-1)
 =M(R-1)-1-\sum_{z<R}t_R(z)(z-1).
\]

Adding the complementary first moment gives cancellation **term by term in `z`**:

\[
-(z-1)t_R(z)+z t_R(z)=t_R(z).
\]

Hence

\[
\boxed{
\sum_y a_R(y)(M(y)-1)+\sum_{z<R}z\,t_R(z)=M(X_R)-1.
}
\]

Since

\[
S_R=-\sum_{z<R}z\,t_R(z),
\]

this is exactly the observed cancellation between the two large quantities. It does not estimate either quantity separately.

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

So the small endpoint is the difference of two large terms, exactly as expected.

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

At `R=1000`, the top five fibres carry only 1.67% of the absolute mass. The cancellation is therefore not concentrated in one extra Farey window; the raw same-`y` joint mode is broadly distributed.

### Is `b_R(y)` locally proportional to `y t_R(y)`?

No. The Pearson correlation of the two exact vectors is already near zero:

| `R` | correlation `corr(b_R, y t_R)` |
|---:|---:|
| 100 | -0.0865 |
| 200 | -0.0118 |
| 500 | -0.0176 |
| 1000 | -0.0072 |

The correct relation is the quotient-kernel transform above, not `b_R(y)=y t_R(y)` plus a nearest-neighbour correction.

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

The Abel residual is not itself the shifted replacement row. The exact reorder occurs one level earlier, through the Type-II quotient kernel, where the unit renewal identity cancels `z-1` against the first moment `z` before summing over `z`.

## Route decision

The involution program has completed its useful role. The data rejects both a sparse-window explanation and a nearest-neighbour `y` derivative. The next exact structure is the quotient-kernel dictionary already present in the Möbius renewal architecture:

\[
C_R\text{-fibres}
\longleftrightarrow
K\,t_R
\longrightarrow
\sum_y K(z,y)(M(y)-1)=1-z.
\]

The remaining analytic problem is therefore to exploit this lower-triangular renewal jointly with the square-root root-smooth state, not to bound `S_R` or the shifted replacement row separately.

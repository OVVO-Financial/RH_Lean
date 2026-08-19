# Preferred end-to-end Lean closure via the already-formalized strong PNT

The direct sharp-Mertens contour is not yet a finished public Lean theorem, so for a machine-checked completion the preferred route is through the already formalized strong PNT for Chebyshev's `psi`.

Define

\[
A(N)=\sum_{n\le N}\frac{\Lambda(n)}n,
\qquad
B(N)=A(N)-H_N.
\]

Finite summation by parts gives the exact identity

\[
B(N)=\frac{E(N)}N+\sum_{m<N}\frac{E(m)}{m(m+1)},
\qquad E(m)=\psi(m)-m.
\]

The formal strong PNT gives

\[
E(x)=O\bigl(xe^{-c\sqrt{\log x}}\bigr).
\]

Therefore the series on the right converges absolutely and its tail has the same stretched-exponential logarithmic decay. Thus `B(N)` converges rapidly.

To identify the limit, use the Dirichlet series

\[
\sum_{n\ge1}\frac{\Lambda(n)-1}{n^s}
=-\frac{\zeta'(s)}{\zeta(s)}-\zeta(s),
\qquad \Re s>1.
\]

Mathlib's `ZetaAsymptotics` namespace proves

\[
\frac{\zeta'(s)}{\zeta(s)}
=-\frac1{s-1}+\gamma+O(s-1),
\]

and

\[
\zeta(s)=\frac1{s-1}+\gamma+O(s-1),
\]

so the boundary value is `-2 * gamma`. Abel continuity for an ordinarily convergent Dirichlet series then gives

\[
B(N)\to-2\gamma.
\]

Write

\[
e(N)=B(N)+2\gamma.
\]

The strong PNT gives a rapidly summable tail for `e`.

Now work with the von-Mangoldt form of K2. Let

\[
a_n=\Lambda(n)/n,
\qquad
D(N)=\sum_{n\le N}a_n\log n.
\]

The convolution term is

\[
C(N)=\sum_{d\le N}a_d A(\lfloor N/d\rfloor).
\]

Since `A(q)=H_q-2 * gamma+e(q)` and

\[
\sum_{d\le N}a_d H_{\lfloor N/d\rfloor}
=\sum_{n\le N}\frac{\log n}{n},
\]

one gets an exact decomposition of `F=C-D` into:

1. the difference between the ordinary log-reciprocal mass and the von-Mangoldt log-reciprocal mass;
2. `-2 * gamma * A(N)`;
3. the quotient transform `sum a_d * e(floor(N/d))`.

A second finite Abel summation cancels the constant mode `-2 * gamma` in item 1. The rapid decay of `e` makes item 3 uniformly bounded after grouping equal quotients. Hence

\[
F(N)+2\gamma\log N=O(1).
\]

For the exact limiting constant, either:

- return to the Möbius-moment proof in `K2_CENTERED_CLASSICAL_PROOF_COMPLETE.md`, or
- differentiate Mathlib's entire regular part `riemannZeta0` once more and define the first Stieltjes constant as the negative derivative of that regular part at `1`.

This route uses only a checked strong PNT and Mathlib zeta asymptotics; it avoids assuming the unfinished public sharp-Mertens contour theorem.

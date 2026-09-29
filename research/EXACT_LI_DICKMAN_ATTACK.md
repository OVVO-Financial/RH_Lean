# Exact-Li continuous model: Dickman attack

## Status

This note is an analytic derivation for the **continuous exact-Li fresh-prime
model**.  It is not yet Lean-certified.

The kernel-checked discrete structural layer is in
\`research/ALL_SCALE_LI_DISPLACEMENT_REDUCTION.lean\`.  In particular, under
\`SquareRootExactLiAllocation\`, the prime-displacement channel is exactly zero.

The point here is to attack the intrinsic continuous model after setting
\(\Delta=\pi_{\rm model}-\operatorname{Li}\equiv0\) by definition.

## 1. Continuous fresh-prime Li model

Put

\[
dL(t)=1_{t\ge2}\frac{dt}{\log t}.
\]

The all-scale signed fresh-prime model is the multiplicative convolution
exponential

\[
d\nu
=
\delta_1
+
\sum_{k\ge1}\frac{(-1)^k}{k!}\,dL^{*_\times k}.
\]

For every finite endpoint \(x\), this sum is finite because a product of
\(k\) fresh factors is at least \(2^k\).

Equivalently, its cumulative diagonal state is the expansion of the
largest-prime recursion

\[
\mathcal S(x,y)
=
1-\int_2^{\min(x,y)}
\mathcal S(x/t,t)\frac{dt}{\log t},
\qquad
\mathcal M_{\rm Li}(x)=\mathcal S(x,x).
\]

The ordering by the current largest factor counts every unordered fresh-prime
tuple once; in the continuous model the equality diagonals have measure zero,
giving the factor \(1/k!\).

## 2. Mellin identity

For \(\Re s>1\), let

\[
F(s)=\int_{1^-}^{\infty}x^{-s}\,d\nu(x).
\]

Multiplicative convolution gives

\[
F(s)
=
\exp\!\left(
-\int_2^\infty \frac{t^{-s}}{\log t}\,dt
\right).
\]

Differentiate the exponent:

\[
\frac{F'(s)}{F(s)}
=
\int_2^\infty t^{-s}\,dt
=
\frac{2^{1-s}}{s-1}.
\]

Hence

\[
F'(s)
=
F(s)\frac{2^{1-s}}{s-1}.
\tag{1}
\]

This step uses only the exact Li density; no actual-prime discrepancy appears.

## 3. Real-space Volterra identity

Let \(d\lambda(t)=1_{t\ge2}\,dt\).  Its Mellin transform is

\[
\int_2^\infty t^{-s}\,dt
=
\frac{2^{1-s}}{s-1}.
\]

Also,

\[
F'(s)
=
-\int (\log x)x^{-s}\,d\nu(x).
\]

Comparing with (1) and using multiplicative convolution gives the signed
measure identity

\[
(\log x)\,d\nu(x)
=
-\,d(\nu *_\times \lambda)(x).
\tag{2}
\]

Define

\[
A(x)=\int_{1^-}^{x}\frac{1}{u}\,d\nu(u).
\]

For fixed \(u\), the map \(t\mapsto ut\) sends Lebesgue measure \(dt\) to
\(dx/u\), so

\[
d(\nu *_\times\lambda)(x)
=
A(x/2)\,dx.
\]

Therefore, for \(x>2\),

\[
d\nu(x)
=
-\frac{A(x/2)}{\log x}\,dx
\tag{3}
\]

and hence

\[
A'(x)
=
-\frac{A(x/2)}{x\log x}.
\tag{4}
\]

Because the fresh-prime support begins at \(2\), the only mass below \(2\) is
the atom \(\delta_1\), so

\[
A(x)=1,\qquad 1\le x\le2.
\]

## 4. Dickman equation

Set

\[
\rho(u)=A(2^u).
\]

For \(0\le u\le1\),

\[
\rho(u)=1.
\]

For \(u>1\), (4) gives

\[
\rho'(u)
=
-\frac{\rho(u-1)}{u},
\]

or

\[
\boxed{
u\rho'(u)+\rho(u-1)=0.
}
\tag{5}
\]

Thus the weighted cumulative state \(A\) is exactly the Dickman function on
logarithmic base-\(2\) scale:

\[
\boxed{
A(x)=\rho(\log_2 x).
}
\]

The standard Dickman identity is

\[
u\rho(u)=\int_{u-1}^{u}\rho(v)\,dv
\qquad(u\ge1),
\tag{6}
\]

and \(\rho\) is positive and decreasing.

## 5. Explicit density and cumulative Li-Mobius mass

From (3),

\[
\boxed{
d\nu(x)
=
-\frac{\rho(\log_2 x-1)}{\log x}\,dx,
\qquad x>2.
}
\tag{7}
\]

Therefore

\[
\boxed{
\mathcal M_{\rm Li}(x)
=
1-\int_2^x
\frac{\rho(\log_2 t-1)}{\log t}\,dt.
}
\tag{8}
\]

This is the intrinsic exact-Li diagonal.  There is no \(\Delta\) term.

## 6. Elementary uniform bound

From positivity, monotonicity, and (6), if \(u\in[n,n+1]\), then inductively

\[
0\le \rho(u)\le\frac1{n!}.
\tag{9}
\]

Indeed, assuming \(\rho(v)\le1/(n-1)!\) for \(v\ge n-1\),

\[
u\rho(u)
=
\int_{u-1}^{u}\rho(v)\,dv
\le \frac1{(n-1)!},
\]

and \(u\ge n\).

Now substitute \(u=\log_2 t-1\) into the total variation of (8):

\[
\int_2^\infty
\frac{\rho(\log_2 t-1)}{\log t}\,dt
=
\int_0^\infty
\frac{2^{u+1}}{u+1}\rho(u)\,du.
\]

On \(u\in[n,n+1]\), (9) gives

\[
\int_n^{n+1}
\frac{2^{u+1}}{u+1}\rho(u)\,du
\le
\frac{2^{n+2}}{(n+1)!}.
\]

Hence

\[
\int_2^\infty
\frac{\rho(\log_2 t-1)}{\log t}\,dt
\le
\sum_{n\ge0}\frac{2^{n+2}}{(n+1)!}
=
2(e^2-1).
\]

Consequently

\[
\boxed{
|\mathcal M_{\rm Li}(x)|
\le
2e^2-1
\qquad(x\ge1).
}
\tag{10}
\]

This is much stronger than the desired root-scale model estimate.

At \(X=R^2-1\),

\[
\boxed{
|\mathcal M_{\rm Li}(R^2-1)|^2
\le
(2e^2-1)^2
\le
(2e^2-1)^2 R^2
\qquad(R\ge1).
}
\]

Thus the **continuous exact-Li fresh-prime model is uniformly bounded**, once
the measure/convolution derivation above is justified.

## 7. What remains to certify

The Lean path should be split into four independent pieces:

1. define the finite-at-each-endpoint multiplicative convolution exponential
   for \(dL(t)=dt/\log t\);
2. prove that its cumulative state equals the continuous largest-prime
   recursion;
3. prove the Volterra identity (2)--(4) and identify the rescaled solution with
   a Dickman-type delay equation;
4. prove the elementary factorial envelope (9) and the convergent integral
   bound (10).

No actual-prime discrepancy is needed anywhere in these four steps.

Only **after** this continuous exact-Li theorem is certified should the project
reintroduce actual primes and study the separate transfer error.

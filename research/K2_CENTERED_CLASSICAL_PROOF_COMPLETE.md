# Centered reciprocal signed K2: complete classical proof

## Statement

Let

\[
K_2(n)=(\Lambda*\Lambda)(n)-\Lambda(n)\log n.
\]

Define

\[
F(N)=\sum_{n\le N}\frac{K_2(n)}{n}.
\]

Then

\[
\boxed{
F(N)=-2\gamma\log N+4\gamma^2+6\gamma_1+o(1)
}
\]

with the convention

\[
\zeta(1+z)=\frac1z+\gamma-\gamma_1z+O(z^2).
\]

In particular,

\[
\boxed{
\sup_{N\ge 3}|F(N)+2\gamma\log N|<\infty.
}
\]

The limiting centered constant is

\[
4\gamma^2+6\gamma_1=0.8958166223288143481\ldots
\]

## 1. Finite signed coordinate

The RH_Lean signed second-Selberg development exposes

\[
K_2(n)=\sum_{d\mid n}\mu(d)(\log d)^2.
\]

Therefore, after reversing the finite divisor sum,

\[
\begin{aligned}
F(N)
&=\sum_{n\le N}\frac1n\sum_{d\mid n}\mu(d)(\log d)^2\\
&=\sum_{d\le N}\frac{\mu(d)(\log d)^2}{d}
  \sum_{m\le N/d}\frac1m.
\end{aligned}
\]

Hence

\[
\boxed{
F(N)=\sum_{d\le N}\frac{\mu(d)(\log d)^2}{d}
H_{\lfloor N/d\rfloor}.
}
\]

This is the exact finite hyperbola coordinate used below.

## 2. Reciprocal Möbius moments

Put

\[
A_2(X)=\sum_{n\le X}\frac{\mu(n)(\log n)^2}{n},
\qquad
C_3(X)=\sum_{n\le X}\frac{\mu(n)(\log n)^3}{n}.
\]

A classical zero-free-region estimate gives

\[
M(x)=\sum_{n\le x}\mu(n)
\ll x\exp(-c\sqrt{\log x})
\]

for some absolute constant \(c>0\). Repeated partial summation therefore implies convergence of both reciprocal moment series and, more precisely, tails strong enough that

\[
A_2(X)-A_2(\infty)=o(1/\log X).
\]

For \(\Re s>1\),

\[
\frac1{\zeta(s)}=\sum_{n\ge1}\frac{\mu(n)}{n^s}.
\]

Differentiating termwise,

\[
\left(\frac1\zeta\right)''(s)
=\sum_{n\ge1}\frac{\mu(n)(\log n)^2}{n^s},
\]

and

\[
\left(\frac1\zeta\right)'''(s)
=-\sum_{n\ge1}\frac{\mu(n)(\log n)^3}{n^s}.
\]

Near \(s=1\), write \(s=1+z\). From

\[
\zeta(1+z)=z^{-1}+\gamma-\gamma_1z+O(z^2),
\]

series inversion gives

\[
\frac1{\zeta(1+z)}
=z-\gamma z^2+(\gamma^2+\gamma_1)z^3+O(z^4).
\]

Consequently

\[
\boxed{A_2(\infty)=-2\gamma}
\]

and

\[
\boxed{C_3(\infty)=-6(\gamma^2+\gamma_1)}.
\]

Define the centered second moment

\[
r(X)=A_2(X)+2\gamma.
\]

Then

\[
r(X)\to0,
\qquad
r(X)\log X\to0.
\]

## 3. First Abel transform

Apply finite Abel summation to

\[
C_3(Q)=\sum_{n\le Q}
\frac{\mu(n)(\log n)^2}{n}\log n.
\]

Since \(A_2(n)=r(n)-2\gamma\), the constant center telescopes exactly and yields

\[
\boxed{
C_3(Q)
=r(Q)\log Q
-\sum_{q<Q}r(q)\log\left(1+\frac1q\right).
}
\]

Because \(r(Q)\log Q\to0\) and
\(C_3(Q)\to-6(\gamma^2+\gamma_1)\),

\[
\boxed{
\sum_{q<Q}r(q)\log\left(1+\frac1q\right)
\longrightarrow
6(\gamma^2+\gamma_1).
}
\]

## 4. Second Abel transform: the K2 hyperbola

Starting from

\[
F(N)=\sum_{d\le N}(A_2(d)-A_2(d-1))H_{\lfloor N/d\rfloor},
\]

finite Abel summation gives

\[
F(N)=
A_2(N)H_1+
\sum_{d<N}A_2(d)
\left(
H_{\lfloor N/d\rfloor}
-H_{\lfloor N/(d+1)\rfloor}
\right).
\]

The differences telescope:

\[
H_1+
\sum_{d<N}
\left(
H_{\lfloor N/d\rfloor}
-H_{\lfloor N/(d+1)\rfloor}
\right)=H_N.
\]

Substituting \(A_2(d)=r(d)-2\gamma\),

\[
\boxed{
F(N)+2\gamma H_N
=r(N)+
\sum_{d<N}r(d)
\left(
H_{\lfloor N/d\rfloor}
-H_{\lfloor N/(d+1)\rfloor}
\right).
}
\]

## 5. Lower half of the hyperbola

For \(d\le\sqrt N\), use

\[
H_m=\log m+\gamma+O(1/m).
\]

Since

\[
\left\lfloor\frac Nd\right\rfloor\asymp\frac Nd,
\qquad
\left\lfloor\frac N{d+1}\right\rfloor\asymp\frac N{d+1},
\]

uniformly in this range,

\[
H_{\lfloor N/d\rfloor}
-H_{\lfloor N/(d+1)\rfloor}
=
\log\left(1+\frac1d\right)
+O\left(\frac{d+1}{N}\right).
\]

Hence

\[
\sum_{d\le\sqrt N}r(d)
\left(
H_{\lfloor N/d\rfloor}
-H_{\lfloor N/(d+1)\rfloor}
\right)
\]

is

\[
\sum_{d\le\sqrt N}r(d)
\log\left(1+\frac1d\right)+o(1).
\]

The error is \(o(1)\) because \(r(d)\to0\), so for every \(\varepsilon>0\), after discarding a fixed initial segment one has \(|r(d)|\le\varepsilon\), and

\[
\frac1N\sum_{d\le\sqrt N}(d+1)=O(1).
\]

The fixed initial segment contributes \(O(N^{-1})\).

By the first Abel transform,

\[
\sum_{d\le\sqrt N}r(d)
\log\left(1+\frac1d\right)
\longrightarrow
6(\gamma^2+\gamma_1).
\]

## 6. Upper half of the hyperbola

For \(d>\sqrt N\), the harmonic differences are nonnegative. Therefore

\[
\begin{aligned}
&\left|
\sum_{\sqrt N<d<N}r(d)
\left(
H_{\lfloor N/d\rfloor}
-H_{\lfloor N/(d+1)\rfloor}
\right)
\right|\\
&\quad\le
\sup_{d>\sqrt N}|r(d)|
\sum_{\sqrt N<d<N}
\left(
H_{\lfloor N/d\rfloor}
-H_{\lfloor N/(d+1)\rfloor}
\right).
\end{aligned}
\]

The last sum telescopes and is at most

\[
H_{\lfloor\sqrt N\rfloor}=O(\log N).
\]

Since \(r(d)=o(1/\log d)\),

\[
\sup_{d>\sqrt N}|r(d)|\log N=o(1).
\]

Thus the upper half contributes \(o(1)\).

Also \(r(N)=o(1)\). Therefore

\[
\boxed{
F(N)+2\gamma H_N
\longrightarrow
6(\gamma^2+\gamma_1).
}
\]

Finally,

\[
H_N-\log N\longrightarrow\gamma,
\]

so

\[
\begin{aligned}
F(N)+2\gamma\log N
&=
\bigl(F(N)+2\gamma H_N\bigr)
-2\gamma(H_N-\log N)\\
&\longrightarrow
6(\gamma^2+\gamma_1)-2\gamma^2\\
&=
4\gamma^2+6\gamma_1.
\end{aligned}
\]

Hence

\[
\boxed{
F(N)+2\gamma\log N
\to
4\gamma^2+6\gamma_1.
}
\]

This proves the centered boundedness theorem.

## 7. Independent Dirichlet-series check

Since

\[
K_2=\mu(\log)^2*1,
\]

its Dirichlet series is

\[
\sum_{n\ge1}\frac{K_2(n)}{n^s}
=\zeta(s)\left(\frac1{\zeta(s)}\right)''.
\]

Using

\[
\frac1{\zeta(1+z)}
=z-\gamma z^2+(\gamma^2+\gamma_1)z^3+O(z^4),
\]

we have

\[
\left(\frac1\zeta\right)''(1+z)
=-2\gamma+6(\gamma^2+\gamma_1)z+O(z^2).
\]

Multiplying by

\[
\zeta(1+z)=z^{-1}+\gamma-\gamma_1z+O(z^2),
\]

produces

\[
\boxed{
\sum_{n\ge1}\frac{K_2(n)}{n^{1+z}}
=-\frac{2\gamma}{z}
+4\gamma^2+6\gamma_1+O(z).
}
\]

This matches the finite hyperbola proof exactly.

## 8. Formalization boundary

The finite identities used above are formalized in `RHLean.Analysis.K2CenteredFinite`.

The remaining unconditional Lean closure should preferably use the already formalized strong-PNT estimate for `psi` together with Mathlib's zeta asymptotics near `1`, rather than depending on an unfinished sharp-Mertens contour development. See `research/STRONG_PNT_CLOSURE_ROUTE.md` and `RHLean.Analysis.K2CenteredClassicalInterface`.

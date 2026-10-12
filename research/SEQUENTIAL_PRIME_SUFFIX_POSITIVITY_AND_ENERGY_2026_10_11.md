# Actual sequential-prime suffix positivity and an outward-energy no-go

**11 October 2026. Scope:** Exact arithmetic and an unconditional paper-level theorem for all sufficiently large roots; no new Lean compilation; finite C/A and RH remain OPEN. Uses the literal prime-comb candidate field, not an alternative prime model.

## Exact chronological object

For integer R >= 2, X=R^2-1, b(k)=1-M(k), and actual successive primes R<=p<=X/2,

\[
\Delta_p=2b(\lfloor X/p\rfloor),\quad
D_R(y)=2M(R-1)-J_y(X),\quad
Q_R=2M(R-1)-M(X).
\]

Writing the *completed future response*

\[
T_R(y)=\sum_{\substack{y<p\le X/2\\p\text{ prime}}}b(\lfloor X/p\rfloor),
\]

the exact sequential-insertion identity is

\[
\boxed{D_R(y)=Q_R+2T_R(y).} \tag{1}
\]

Every cofactor appearing after the root is historical, and different such primes act on disjoint composite sites.

## Elementary all-prefix positivity: proved

For every integer t>=2 let

\[
B(t)=\sum_{k=2}^{t}\frac{1-M(k)}{k(k+1)}
=1-\sum_{n=1}^{t}\frac{\mu(n)}n+\frac{M(t)-1}{t+1}.
\]

Let A_+(t) and A_-(t) count positive and negative Mobius coefficients through t, including mu(1)=+1. From the exact divisor inversion

\[
\sum_{n\le t}\mu(n)\lfloor t/n\rfloor=1
\]

we obtain

\[
\sum_{n\le t}\mu(n)/n
=\bigl(1+\sum_{n\le t}\mu(n)\{t/n\}\bigr)/t
\le A_+(t)/t.
\]

Indeed, the n=1 fractional part is zero; each other positive term contributes <1, and the negative ones contribute <=0. Since M(t)=A_+(t)-A_-(t) and A_+(t)+A_-(t)<=t, this proves

\[
\boxed{B(t)\ge
\frac{t^2-A_+(t)-tA_-(t)}{t(t+1)}
\ge\frac{(t-1)A_+(t)}{t(t+1)}>0.} \tag{2}
\]

This is fully elementary and holds at *every* historical cutoff, even though b(95)=-1 and many individual prime updates are negative. Classical unconditional PNT gives B(t)->1.

## Uniform genuine-prime future-response profile: proved for sufficiently large roots

Define for u in [0,1/2]

\[
F(u)=\sum_{k=2}^{\infty} b(k)
\left(\frac1k-\max\left(u,\frac1{k+1}\right)\right)_+ .
\]

Unconditional quantitative Mertens bounds imply absolute convergence. At each reciprocal knot, F(1/(t+1))=B(t)>0; between successive knots it interpolates linearly. Also F(0)=1, F(1/2)=0, and F(u)=1/2-u on [1/3,1/2]. Hence

\[
F(u)>0\ (0\le u<1/2),\qquad
\min_{0\le u\le1/3}F(u)>0. \tag{3}
\]

The prime number theorem gives for each fixed quotient k

\[
\pi(X/k)-\pi(X/(k+1))
\sim \frac{X}{k(k+1)\log X}.
\]

Here is the uniform-tail step, keeping actual primes:

\[
\lim_{K\to\infty}\limsup_{R\to\infty}
\frac{\log X}{X}
\sum_{\substack{R\le p\le X/K\\p\text{ prime}}}
|b(\lfloor X/p\rfloor)|=0. \tag{4}
\]

Proof: when K<k<=X^{1/4}, Brun--Titchmarsh bounds each actual prime quotient-band count by O(X/(k^2 log X)); the sum is bounded by a constant times \(\sum_{k>K}|b(k)|/k^2\to0\). When k>X^{1/4}, use the unconditional Mertens estimate \(b(k)=O_B(k/(\log k)^B)\) for any B>1, and \(\sum_{R\le p\le X^{3/4}}1/p=O(1)\), giving \(O_B(X/(\log X)^B)=o(X/\log X)\).

Uniform finite-band PNT together with (4) establishes

\[
\boxed{\sup_{R\le y\le X/2}
\left|\frac{\log X}{X}T_R(y)-F(y/X)\right|\to0.} \tag{5}
\]

For y<=X/3, (3) and (5) imply T_R(y)>0 for all sufficiently large roots, uniformly in y. For y>X/3, every remaining actual prime has quotient k=2, and T_R(y)>=0 *exactly*. Therefore the genuine-prime chronological suffix sign satisfies the unconditional theorem

\[
\boxed{\exists R_0<\infty\ \forall R\ge R_0\ \forall y\ge R:
T_R(y)\ge0.} \tag{6}
\]

This supplies an existential large-root threshold, **not** a verified explicit R_0, and it does not establish the separate original finite-C bound.

## Unconditional failure of an independent outward-energy budget

At each insertion \(D_p=D_{p^-}-\Delta_p\), hence

\[
D_p^2-D_{p^-}^2=-2D_{p^-}\Delta_p+\Delta_p^2.
\]

Let \(E_R^+=\sum_p (D_p^2-D_{p^-}^2)_+\). A uniform inequality \(E_R^+\le C R^2K_R\) is **false**.

In the literal quotient-95 band \(X/96<p\le X/95\), each actual prime has b(95)=-1 and raises D by 2. Because all later quotient classes <=94 have nonnegative b(k), every such step has

\[
D_{p^-}\ge Q_R+
2[\pi(X/2)-\pi(X/3)]-
2[\pi(X/95)-\pi(X/96)].
\]

Unconditionally \(Q_R=o(X/\log X)\), while PNT makes the right-hand side \((1/3-2/(95\cdot96)+o(1))X/\log X>0\). There are \(\sim X/(95\cdot96\log X)\) actual primes in this band; each causes outward energy \(4D_{p^-}+4\gg X/\log X\). Thus

\[
\boxed{E_R^+\gg X^2/(\log X)^2,\qquad
E_R^+/(R^2K_R)\gg R/(\log R)^2\to\infty,} \tag{7}
\]

using the elementary K_R<=R. Any proposed prime-step proof bounding outward energy independently is therefore impossible; inward and outward payments must remain jointly signed.

## Exact integer audit

A fresh C++17 linear Mobius sieve tracks **every actual post-root prime** and tests every future suffix, then independently computes the full forward squared-energy changes.

| R | X | Active primes | Negative steps | Negative signed mass | Forced terminal 2p mass | Outward energy | Outward/(R^2 K_R) |
|--:|--:|--:|--:|--:|--:|--:|--:|
|317|100488|5092|9|30|3142|1242084|8.240265|
|1000|999999|41370|102|444|25746|149069384|99.379589|
|2000|3999999|148630|429|2102|93100|2531877544|421.979591|
|5561|30924720|997847|3159|20128|629788|162767647232|3508.9|

Every one of **1,999 square roots R=2..2000** passed all literal future-suffix checks. Independent moving-endpoint checks passed for **all integers x=3..50000** and an additional 4,000 deterministically seeded sampled x<=1,000,000. The smallest historical B(t) for t=2..1999 was exactly 1/6 at t=2. This census is *not* a proof for all small roots; (6) is an unconditional **eventual** theorem.

Reproduction source: experiments/PrimePopulationCutoff/prime_suffix_chronology_audit.cpp (also available as a local standalone reproducible C++ tool).

## What still has to be proved

The original objective is unchanged:

\[
\boxed{\exists C<\infty:\quad
|Q_R|=|D_R(R)-2T_R(R)|\le C R\sqrt{K_R}
\quad\forall R\ge2.}
\]

Positive future suffixes restrict the actual prime sequence directionally but do **not** bound terminal overshoot. The energy no-go proves one cannot separately bound the outward portion at the desired scale. A further *signed matched-return theorem coupling the originally prepared field with the completed prime response* remains essential. No finite C, finite A or RH closure is claimed.

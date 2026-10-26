# CORR-4: low-quotient Mellin audit and constant-four quotient tail (2026-10-26)

**Status:** The genuine constant-four upper-quotient bound has a warning-fatal Lean-certified proof in PR #1026 (Targeted Lean iteration run 40274162531). This document records a separate, **unclosed** Mellin reduction of the low-quotient source. No strict Mertens exponent improvement or RH theorem is claimed.

## 1. Complete Eisenstein decoder

Let \(\chi=\chi_{-3}\), \(\mu_6(n)=\mathbf 1_{(n,6)=1}\mu(n)\), and

\[
a_6(n)=\mathbf 1_{(n,6)=1}\bigl(\mu*(\chi\mu)\bigr)(n).
\]

For \(\Re s>1\), the exact Euler factorization is

\[
F_6(s)=\sum_{m\ge1}\frac{a_6(m)}{m^s}
=\frac{1}{(1-3^{-s})(1-4^{-s})\zeta(s)L(s,\chi)}.
\tag{1}
\]

The excluded factors at \(p=3\) and the inert prime \(p=2\) are **both retained in the denominator**. The actual period-36 quotient decoder is

\[
\mathcal K(v)=C_\chi(v)-C_\chi(\lfloor v/3\rfloor)
-C_\chi(\lfloor v/4\rfloor)+C_\chi(\lfloor v/12\rfloor),
\quad
C_\chi(v)=\sum_{1\le n\le v}\chi(n).
\]

Its first discrete difference \(d(u)=\mathcal K(u)-\mathcal K(u-1)\) has Dirichlet series

\[
D(s)=\sum_{u\ge1}\frac{d(u)}{u^s}
=(1-3^{-s})(1-4^{-s})L(s,\chi),\qquad
\boxed{F_6(s)D(s)=\zeta(s)^{-1}.}
\tag{2}
\]

This is a precise algebraic explanation of the complete cross-quotient cancellation: the full decoder removes the quadratic \(L\)-factor and both excluded Euler factors. The truncated decoder \(D_{L-1}(s)=\sum_{u<L}d(u)u^{-s}\) no longer cancels the whole norm source.

## 2. Unconditional high-u tail and exact low-u reduction

Let \(X=R^2-1\), integers \(H,T\ge1\), and use the literal normalized discrete tent

\[
\mathcal A_H f(X)=\frac1{H^2}\sum_{|h|<H}(H-|h|)f(X+h),
\quad
\Phi_{H,X}(n)=\mathcal A_H \mathbf 1_{\{n\le X+h\}}.
\]

Set \(B_u=\sum_{m>T}a_6(m)\Phi_{H,X}(um)\) and \(U_*=\lfloor(X+H-1)/(T+1)\rfloor\). Using a **single** signed Abel identity, monotonicity of each ramp, the original period-36 bound \(|\mathcal K|\le2\), and the existing genuine coefficient mass bound \(\sum_{m\le N}|a_6(m)|\le N\), yields the unconditional inequality

\[
\boxed{\left|\sum_{u=L}^{U_*}d(u)B_u\right|
\le4\left\lfloor\frac{X+H-1}{L}\right\rfloor}
\quad(1\le L\le U_*).
\tag{3}
\]

The Lean theorem for the physical tent occurs in research/CORR4_PHYSICAL_TENT_CONSTANT_FOUR_20261026.lean and uses the equal-weight two-box convolution representation of the exact Fejér tent. The abstract coefficient-mass/monotone-Abel theorem is in research/CORR4_HIGH_QUOTIENT_TAIL_CONSTANT_FOUR_20261026.lean.

If \((L-1)T\le X-H+1\), the low-u gate is identically on across the entire tent window and

\[
\boxed{\sum_{1\le u<L}d(u)B_u
=\sum_{1\le u<L}d(u)\,
\mathcal A_H A_6\!\left(\left\lfloor\frac{X+h}{u}\right\rfloor\right)
-\mathcal K(L-1)A_6(T).}
\tag{4}
\]

The last term has magnitude at most \(2T\). With \(X\asymp H^{8/7}\), \(T=H^{1-\delta}\), \(L=H^{1/7+2\kappa}\), the gate holds eventually if \(\delta>2\kappa\), while the high-u tail is \(O(H^{1-2\kappa})\).

## 3. Exact Perron/Mellin interface

For \(\Re s=c>1\), define the discrete kernel

\[
W_{X,H}(s)=\frac1{H^2s}\sum_{|h|<H}
(H-|h|)(X+h+\tfrac12)^s.
\tag{5}
\]

The half-integer shift makes every sharp integer cutoff exact, with no Perron boundary half-weight. For the low quotient source (including all \(a_6\) occurrences, prior to subtracting the finite \(T\)-boundary),

\[
\boxed{
S_{<L}(X,H)
=\lim_{V\to\infty}\frac1{2\pi i}
\int_{c-iV}^{c+iV}F_6(s)D_{L-1}(s)W_{X,H}(s)\,ds.}
\tag{6}
\]

There is a useful unconditional *decoder-tail* estimate. Since \(\sum_{j\le u}d(j)=\mathcal K(u)\) and \(|\mathcal K(u)|\le2\), summation by parts gives, for \(\sigma=\Re s>0\),

\[
\left|D(s)-D_{L-1}(s)\right|
\le2L^{-\sigma}\left(1+\frac{|s|}{\sigma}\right).
\tag{7}
\]

The exact identity

\[
F_6(s)D_{L-1}(s)
=\frac1{\zeta(s)}-
F_6(s)\bigl(D(s)-D_{L-1}(s)\bigr)
\tag{8}
\]

shows why the decoder-tail saving alone is not enough: the remainder retains inverse zeta and Dirichlet \(L\)-function factors and can be amplified near their zeros.

## 4. Continuous smoothing is not an automatic conductor saving

The continuous tent, which is **not** the literal physical lattice tent, has the exact Mellin kernel

\[
W^{\rm cont}_{X,H}(s)
=\frac{(X+H)^{s+2}-2X^{s+2}+(X-H)^{s+2}}
{H^2s(s+1)(s+2)}.
\tag{9}
\]

This attenuates frequencies \(|t|\gg X/H\) quadratically. It does **not** bound frequencies \(|t|\lesssim X/H\), and reducing a Mellin vertical frequency range is not the same as reducing an auxiliary Hecke conductor or OpenAI Gaussian detector family.

Moreover, the exact discrete kernel (5) is a finite exponential polynomial in \(t\), divided by \(s\). It does not inherit the same uniform continuous \(t^{-2}\) attenuation at arbitrarily high frequencies; possible lattice aliasing and the Perron truncation tail must be controlled separately.

The standard fixed-conductor zero-free region supplies subexponential-in-logarithms bounds, not the **fixed negative power** needed on the short windows of relative width \(H/X\asymp H^{-1/7}\). Nor does an already-known \(7/8\) rational Möbius estimate directly imply a pointwise \(7/8\) estimate for \(A_6\) without new analytic control of the inverse \(L\)-factor.

**Remaining independent analytic theorem:** prove uniformly

\[
\left|S_{<L}(X,H)\right|\ll H^{1-\kappa}
\]

with the complete low-frequency integral, all retained \(a_6\) coefficients, the truncated decoder, true finite tent, boundary term, and every contour pole/residue paid. This is a genuine arithmetic cancellation estimate, **OPEN**.

## 5. Acceptance artifacts

- research/VF_MID_919_QUOTIENT_SIGNED_RETURN.lean — original exact period-36 decoder, primitive, and signed Abel.
- research/VF_MID_919_GENERAL_X_HIGH_QUOTIENT_ISOLATION.lean — original coefficient mass \(\sum_{m\le N}|a_6(m)|\le N\).
- research/CORR4_FIXED_HYPERBOLA_DOUBLE_ABEL_20261026.lean — fixed-owner partition and double Abel.
- research/CORR4_HIGH_QUOTIENT_TAIL_CONSTANT_FOUR_20261026.lean — monotone Abel and actual coefficient mass.
- research/CORR4_PHYSICAL_TENT_CONSTANT_FOUR_20261026.lean — exact physical tent and all-source upper-u bound.

Warning-fatal selected research closure: GitHub Actions Targeted Lean iteration run 40274162531, conclusion **success**. No `sorryAx` was reported for the target theorems.

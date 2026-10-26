# CORR-4: six-point B6 branch collapse and zero-cut audit (2026-10-26)

**Proof status.** The genuine six-point Euler polynomial is Lean-certified in
research/CORR4_SIX_POINT_ORTHOGONALITY_20261026.lean. The period-36
zero-boundary low-quotient support is Lean-certified in
research/CORR4_ZERO_CUT_QUOTIENT_SUPPORT_20261026.lean. Their combination
with the full finite-convolution/physical-tent transport has not yet
been formalized as a Lean theorem. The Branch-I/overlap estimate below
is an unconditional mathematical argument; the residual power saving
remains OPEN.

## Exact excluded-six convolution

Write \(\chi=\chi_{-3}\), \(\mu_6(n)=\mu(n)1_{(n,6)=1}\),
\(b_6(n)=\chi(n)\mu_6(n)\), \(B_6(Y)=\sum_{n\le Y}b_6(n)\),
\(M_6(Y)=\sum_{n\le Y}\mu_6(n)\), and \(a_6=\mu_6*b_6\).
For the genuine #919 decoder \(d(u)=\mathcal K(u)-\mathcal K(u-1)\),
\[
\sum b_6(n)n^{-s}=[(1+2^{-s})L(s,\chi)]^{-1},\qquad
\sum d(u)u^{-s}=(1-3^{-s})(1-4^{-s})L(s,\chi).
\]
Hence the *coefficient identity*
\[
\boxed{d*b_6=\delta_1-\delta_2-\delta_3+\delta_6,}
\tag{1}
\]
which implies, for each integer \(Z\ge6\),
\[
\boxed{\sum_{1\le u\le Z}d(u)B_6(\lfloor Z/u\rfloor)=0.}
\tag{2}
\]
The plus sign in the inert \(2\)-Euler factor is essential.

## True arbitrary-cutoff asymmetric hyperbola

For **any fixed** \(r\ge1\), with no requirement
\(r=\lfloor\sqrt Y\rfloor\), the exact formula is
\[
\boxed{
A_6(Y)=\sum_{a\le r}\mu_6(a)B_6(\lfloor Y/a\rfloor)
+\sum_{b\le\lfloor Y/(r+1)\rfloor}
 b_6(b)M_6(\lfloor Y/b\rfloor)
-M_6(r)B_6(\lfloor Y/(r+1)\rfloor).}
\tag{3}
\]
The second sum's moving \(b\)-gate cannot be discarded. Its final
overlap has B6 denominator \(r+1\), not \(r\).

If \(X=R^2-1\), **\(\lfloor\sqrt X\rfloor=R-1\)**, so taking
\(r=R\) means intentionally using an arbitrary fixed hyperbola cutoff.

## Branch I and overlap: unconditional constant-four payment

Define the literal finite tent
\[
\Phi_{H,X}(n)=H^{-2}\sum_{|h|<H}(H-|h|)
\mathbf1_{\{n\le X+h\}},\quad Y_{\max}=X+H-1.
\]
Assume \(H,L,r\ge1\) and
\[
\boxed{X-H+1\ge6(r+1).}\tag{4}
\]
This gives \(\lfloor(X+h)/a\rfloor\ge6\) throughout the tent for
every \(1\le a\le r+1\), so (2) applies pointwise in \(h\).
The claim \(Z_a(h)\ge R-1\) is false at the proposed critical
smoothing scale; condition (4) is the correct weaker gate.

The low-\(u\) B6 source is the *negative* of the upper-\(u\)
source. Swap the finite \(b_6\) sum and apply one Abel transform to
each monotone ramp, using \(|\mathcal K(u)|\le2\) and
\(|b_6(m)|\le1\). This proves
\[
\boxed{\left|\sum_{1\le u<L}d(u)\sum_{m\ge1}b_6(m)
\Phi_{H,X}(uam)\right|
\le4\left\lfloor\frac{Y_{\max}}{aL}\right\rfloor.}
\tag{5}
\]
The upper tail may be empty; then (2) makes the low sum zero.

The first hyperbola term satisfies
\[
|\mathrm{Branch\ I}|
\le\frac{4Y_{\max}}L\sum_{a\le r}\frac{|\mu_6(a)|}{a}
\le\frac{4Y_{\max}}L(1+\log r).
\tag{6}
\]
For the overlap,
\[
|\mathrm{overlap}|
\le4|M_6(r)|\left\lfloor\frac{Y_{\max}}{(r+1)L}\right\rfloor
\le\frac{4Y_{\max}}L.
\tag{7}
\]
Thus
\[
\boxed{|\mathrm{Branch\ I}-\mathrm{overlap}|
\le \frac{4(X+H-1)}{L}(2+\log r).}
\tag{8}
\]
At \(X\asymp H^{8/7}\) and \(L\asymp H^{1/7+2\kappa}\),
this is \(O(H^{1-2\kappa}\log H)=O(H^{1-\kappa})\).

## Low-u does not literally mean ultra-high norm without an endpoint choice

Because \(B_u\) is cumulative, its \(u=1\) summand contains all
\(T<m\lesssim X\), *not only the top octave*. The latter is the
physical sharp quotient bucket \(\lfloor X/m\rfloor=1\).
For smaller m, \(\Phi(um)=1\) for every \(u<L\); their entire
low-u weight is \(\mathcal K(L-1)\).

Choose \(L=36q+1\). The exact period-36 kernel then has
\(\mathcal K(L-1)=0\), so the Lean-certified theorem gives
\[
Lm+H-1\le X\implies
\boxed{\sum_{1\le u<L}d(u)\Phi_{H,X}(um)=0.}\tag{9}
\]
Taking the least integer \(L\equiv1\bmod36\) above the desired
asymptotic scale changes it by at most 35, not its exponent.
The cumulative low-u source is now *genuinely supported* on
\(m>(X-H+1)/L\), up to integer rounding.

## Residual independent arithmetic theorem

After removing (6) and (7), the exact remaining piece is
\[
\boxed{
\sum_{1\le u<L}d(u)\,
\mathcal A_H\sum_{b\le\lfloor(X+h)/(u(r+1))\rfloor}
b_6(b)M_6\!\left(\left\lfloor\frac{X+h}{ub}\right\rfloor\right).
}\tag{10}
\]
Expanding \(M_6\) and recombining all branches only reconstructs
\(A_6\); this is *not* a cancellation theorem.

A potentially noncircular split-prime/cofactor route must retain
the high-prime lower gate \(p>\sqrt Y\), the smooth complement, the
actual \(a_6(c)\) coefficients (and \(p\nmid c\)), the moving
\(u\)-dependent gates and all tent collars. Writing
\(\pi_{1,3}=\tfrac12\operatorname{Li}_2+\Delta_{1,3}\) does not
bound the resulting signed short-interval remainder. A small
sample value of \(\sum_{c\le r}a_6(c)/c\) gives no uniform
negative-power saving.

**Lean acceptance still to add:** (i) actual decoder coefficient
equals \(d(u)\), (ii) finite convolution-prefix transport of (1)
into (2), (iii) actual B6 coefficient mass and physical-tent tail
(5), and (iv) their composition with the fixed hyperbola (3).
The six-point coefficient algebra and 36-zero support were checked
independently, but do not yet constitute these four Lean theorems.

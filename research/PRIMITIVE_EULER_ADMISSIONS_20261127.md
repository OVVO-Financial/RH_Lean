# Primitive Euler admissions and the signed residual

The [alternating split-factorial exchange](SIGNED_MOBIUS_SPLIT_COMPENSATION_20261127.md) is the benchmark for forced compensation. Here the test is a cyclic shift on ordinary integer slots. Its primitive part has determinant \(e^{\Lambda(n)}\) at the endpoint and first trace \(\mu(n)\). For a large prime entering this space, a common integer of log size \(O(\sqrt x\log x)\) controls all exceptional valuations **at the entering primes**. The real determinant admits a separate estimate on the same cyclic spaces.

The complete signed lower bound remains open. Two issues can be located explicitly. One routed direction per native star layer loses the dependence on its prime. The full primitive orbit retains that dependence, and its remaining signed contribution can be localized to short traces with a reference computable from small integers. The new results are paper deductions at RH_Lean head d9c30d7.

## 1. A primitive integral section on real quotient slots

On \(n\) consecutive slots let \(S\) cyclically permute their addresses in residue order. Put
\[
L_n=\ker_{\mathbb Z}\Phi_n(S),\qquad U_n=S|_{L_n},
\]
where \(\Phi_n\) is the cyclotomic polynomial. This saturated lattice has rank \(\varphi(n)\). A single vector whose translates generate it integrally is
\[
v_n=\prod_{q\mid n,\ q\ {\rm prime}}(I-S^{n/q})e_0 .
\]
Its zeroth entry is one and its squared norm is \(2^{\omega(n)}\). Indeed, in the CRT coordinates for \(n\), each factor is an adjacent difference along a subgroup of order \(q\). The subset sums giving its entries are distinct modulo \(n\). For a prime power \(q^a\), all translates generate the lattice of vectors of sum zero on each fibre of reduction to \(q^{a-1}\). This lattice splits integrally as a direct summand of the coordinate lattice. Taking tensor products of these splittings proves the generation assertion for general \(n\).

On an actual layer served by \(p>x^{3/4}\) one may reserve disjoint \(pk\)-cycles for \(1\le k\le x/p\). They require \(\sum_{k\le x/p}pk=O(x^{5/4})\) slots. The native lower bound \(e^{x^\varepsilon}/x^2-2\) exceeds this eventually, including on the common core of the allowed widths. Sending a constant amplitude to copies of that amplitude times \(v_{pk}\) has an integral left inverse by reading a designated zeroth entry. The other integers can be kept as a separate complete reference table, using \(\sum_{n\le x}n=O(x^2)\) addresses. Served incidences refer only to actual partner sites. Their original multiplicities follow from the native counting identity. The translates within one cycle are additional test directions. [Layer cardinalities and star columns](https://github.com/OVVO-Financial/RH_Lean/blob/d9c30d780b9fa5b82173cc20e6f6ebc53b10689d/research/NativeMeasuredSlotProjector.lean#L35-L52) · [Partner incidences](https://github.com/OVVO-Financial/RH_Lean/blob/d9c30d780b9fa5b82173cc20e6f6ebc53b10689d/research/NativeTranslatedSlotFrame.lean#L313-L345)

For \(n\ge2\) define \(A_n=I-U_n\). Its determinant equals \(\Phi_n(1)=e^{\Lambda(n)}\). This follows by evaluating \((X^n-1)/(X-1)\) at \(1\) and inducting over divisors. The trace of \(U_n^j\) is the Ramanujan sum
\[
c_n(j)=\sum_{d\mid(n,j)}d\,\mu(n/d).
\]
In particular \(c_n(1)=\mu(n)\). Write \(\widehat E(s)=\int_0^1 E(y)y^{s-1}\,dy\) for the previous three-scale residual. For the complete trace \(T_j(x)=\sum_{2\le n\le x} E(n/x)c_n(j)\), Mellin integration in \(x\) gives
\[
\int_1^\infty T_j(x)x^{-s-1}\,dx
=\widehat E(s)\left(\frac{\sigma_{1-s}(j)}{\zeta(s)}-1\right)
\quad(\Re s>1).
\]
The formula follows by substituting the divisor sum and continues meromorphically to the critical strip. For \(0<\Re s<1\), every Euler factor of \(\sigma_{1-s}(j)\) is a geometric sum with ratio of modulus greater than one. At a nontrivial zero \(\rho\), \(\widehat E(\rho)=1/[\rho(1-\rho)]\). Thus **each fixed positive trace order** sees a pole of the multiplicity of that zero. [Ramanujan sum Dirichlet series, Theorem 2.8](https://ltoth.ttk.pte.hu/Ramanujan07.pdf)

## 2. A single integer controlling the admitted places

Let \(c=\lfloor\sqrt x\rfloor\), \(r=c/(c+1)\), and consider on the same section
\[
B_n=(c+1)I-cU_n=I+cA_n,\qquad D_n=\det B_n>0.
\]
Use \(U_1=1\) and \(D_1=1\). The identity \(B_n-cA_n=I\) gives an integral left inverse for the stacked pair \((A_n,B_n)\) at every place. Moreover \(B_n\) acts as the identity on \(L_n/A_nL_n\). This is a statement on the common integral module.

For an odd admitted prime \(p>x^{3/4}\) and \(1\le k\le x/p\), one has \(p\nmid k\,c(c+1)\) eventually. The exact local relation is
\[
v_p(D_{pk})=\begin{cases}1,&p\mid D_k,\\0,&p\nmid D_k.\end{cases}
\]
In particular \(v_p(D_p)=0\). To prove the relation put \(a=c+1,\ b=c\) and write \(D_n=\prod_{d\mid n}(a^d-b^d)^{\mu(n/d)}\). If \(h\) is the order of \(a/b\bmod p\), then \(p\mid D_k\) exactly when \(h=k\), because \(p\nmid k\). The \(p\)-valuation of \((a^{pd}-b^{pd})/(a^d-b^d)\) is one when \(h\mid d\) and zero otherwise, by the odd-prime binomial expansion. In the expression for \(D_{pk}\) the valuation sums to \(\sum_{h\mid d\mid k}\mu(k/d)=\mathbf1_{h=k}\).

Now set
\[
K=\lfloor x^{1/4}\rfloor,\qquad \Xi_x=\prod_{k=1}^K D_k .
\]
The scalar can be constructed before selecting any served prime. Its size bounds all the above charges simultaneously, with their actual multiplicity in \(k\):
\[
\boxed{\displaystyle
\sum_{\substack{x^{3/4}<p\le x\\ p\ {\rm prime}}}
 \sum_{1\le k\le x/p}v_p(D_{pk})\log p
\le \log\Xi_x
\le \frac{K(K+1)}2\log(2c+1).}
\]
The last inequality uses the unit-modulus eigenvalues of \(U_k\). A bounded signed weight costs at most its supremum times this bound. Repeating the estimate per original top retains the native incidence normalization. For example, \(x=178084,\ c=422,\ p=8779,\ k=3\) give \(pk<x/6\), \(D_3=535519=61\cdot8779\), and \(v_{8779}(D_{3\cdot8779})=1\). A height bound on an arbitrary inverse \(B_{pk}^{-1}\) would also have to account for its other prime divisors.

## 3. Real reciprocity and the original star rank

Put \(F_n(t)=\det(I-tU_n)\) for \(0<t<1\), including \(F_1(t)=1-t\). For \(p\nmid k\), summation over the \(p\)-coordinate in \(\mathbb Z[C_p]\otimes L_k\) gives an integral quotient onto \(L_k\) with kernel \(L_{pk}\). The shift acts on all three spaces. Equivalently, the cyclotomic factorization gives
\[
F_{pk}(r)F_k(r)=F_k(r^p).
\]
Consequently, independently of the placement of other primes,
\[
|\log F_{pk}(r)+\log F_k(r)|
\le \frac{\varphi(k)r^p}{1-r^p}.
\]
For \(p>x^{3/4}\), \(r^p\le\exp(-p/(c+1))\). Summed over the whole range \(pk\le x\) with bounded weights, this upper bound is \(o(1)\). The endpoint for \(k=1\) is decisive. Exactly \(F_p(1)=p\) and \(F_p(r)=(c+1)(1-r^p)\). The log change retains \(\log(p/(c+1))\) up to an exponentially small error.

On any real matrix \(Z\) of tested sections the same pair satisfies
\[
(BZ)^*(BZ)=Z^*Z+c(c+1)(AZ)^*(AZ),
\]
since \(U\) is an isometry and \(A+A^*=A^*A\). Consider the original star routed to one \(p\)-contrast \(v_p=e_0-e_1\) per actual large-prime layer. Its constant amplitude and depth multiply that contrast. For every odd \(p\), \(\|v_p\|^2=2\) and \(\|A_pv_p\|^2=6\). Disjoint support therefore gives, **on the same selected star columns**,
\[
(AZ)^*(AZ)=3Z^*Z,\qquad
(BZ)^*(BZ)=(1+3c(c+1))Z^*Z.
\]
This particular restriction reads a common scalar. More generally the Gram of \(\ell\) consecutive translates of \(v_p\), \(1\le\ell<p\), is tridiagonal with diagonal \(2\) and adjacent entries \(-1\). Its determinant is \(\ell+1\) by the continuant recurrence. A full basis of \(p-1\) translates gives \(p\). A comparison on the original star must explain how it captures this dependence on the full orbit. The physical availability of the addresses alone gives no such inequality.

The same loss of the prime label holds for any fixed collection \(f_i(S)v_p\) with prime-independent Laurent polynomial coefficients when the supports of \((1-X)f_i(X)\) lie in a common exponent interval of diameter less than \(p\). No two distinct exponents in that interval coincide modulo \(p\), so the measured Gram is the ordinary coefficient Gram. In the consecutive-shift case, retaining at most \(O(\sqrt x\log x)\) shifts at \(p>x^{3/4}\) loses at least \(\tfrac14\log x-\log\log x-O(1)\) in log squared covolume against the full basis. This concerns the range of physical shifts used in a section. The short spectral traces in §4 are taken on the **full** primitive section.

## 4. A square-root comparison for the complete residual

Put \(P_E(x)=\sum_{n\le x}\Lambda(n)E(n/x)\). The small divisors and proper prime powers differ from the remaining prime sum by \(O_E(\sqrt x)\), as in the alternating-exchange note. Write
\[
h=\log(1+1/c),\quad \tau=xh,\quad H=\lceil4\log(2x)/h\rceil .
\]
There is an independently computable real reference \(R_E(x)\), specified below, for which
\[
\boxed{\displaystyle
P_E(x)=-\sum_{j=1}^H\frac{r^j}{j}\,T_j(x)-R_E(x)
          +O_E(\sqrt x\log(2x)).}
\]
Here \(H=O(\sqrt x\log x)\). The reference uses Möbius values only at integers \(k\le c\), ordinary integrals and zeta values in the absolutely convergent half-plane. In particular its evaluation needs no membership or weight of any prime in the unresolved band.

For the proof, the regularized log determinant \(W=\sum_{2\le n\le x} E(n/x)\log F_n(r)\) is minus the indicated trace sum with error \(O_E(1)\), by the logarithm series and \(\sum_{n\le x}|c_n(j)|=O(x^2)\). For \(j\le H<p\), eventually, the actual cyclic trace on each large-prime admission satisfies \(c_{pk}(j)=-c_k(j)\).

Define \(f(u)=\log((1-e^{-u})/u)\), extending by \(f(0)=0\). Cyclotomic factorization gives exactly
\[
\log F_n(r)-\Lambda(n)=\sum_{d\mid n}\mu(n/d) f(hd)\qquad(n\ge2).
\]
On the residual from the earlier note, \(E(y)=O(y)\), and \(|E'(y)|\ll1/y\) almost everywhere. For the derivative bound, use \(E(y)=\sum_a V(ay)-(1/y-1)\). The function \(tV'(t)\) has bounded variation on its smooth pieces with finite total variation and integral \(-1\). Its Riemann sum is \(-1/y+O(1)\). Differentiation away from the finitely many breakpoints on each compact subinterval of \((0,1]\) gives the claim. Now \(|f'(u)|\le1\) and \(|f(u)|\le u\), so \(E(y)f(\tau y/k)\) has total variation \(O_E(\tau/k)\). Reindex by \(n=kd\) and replace the inner sum over \(d\) by its integral. Adding the \(n=1\) correction costs \(O_E(1)\). The uniform error is \(O_E(\tau\log(2x))\). Extending the integral sum beyond \(k=x\) costs \(O_E(\tau)\). This proves
\[
W-P_E(x)=x\sum_{k\ge1}\frac{\mu(k)}k
  \int_0^1 E(y)f(\tau y/k)\,dy+O_E(\sqrt x\log(2x)).
\]

To evaluate the reference independently of the large primes, keep only \(k\le c\) in the displayed integral sum. To this partial sum, including its prefactor \(x\), add
\[
x\sum_{j=1}^{J} a_j\tau^j
 \left(\int_0^1 y^j E(y)\,dy\right)
 \left(\frac1{\zeta(j+1)}-\sum_{k\le c}\frac{\mu(k)}{k^{j+1}}\right),
\quad J=\lceil\log(2x)/\log\pi\rceil .
\]
The result is \(R_E(x)\). Here \(a_1=-1/2\), \(a_{2l}=(-1)^{l+1}\zeta(2l)/(l(2\pi)^{2l})\), and the other coefficients vanish. These follow by expanding \(f(u)=-u/2+\log(\sinh(u/2)/(u/2))\). Eventually \(\tau\le2c\). On \(k>c\), the discarded tail after summing over \(k\) costs \(O_E(x\pi^{-J})=O_E(1)\), using \(\sum_{k>c} k^{-j-1}\le c^{-j}/j\). All constants in this calculation can be evaluated by convergent sums over ordinary integers. [Hyperbolic sine product](https://dlmf.nist.gov/4.36)

In this formulation an independent estimate still needed on the native windows is
\[
\sum_{j\le H}\frac{r^j}{j}T_j(x)+R_E(x)
\le C_\varepsilon x^{1/2+K_0\varepsilon}
\]
for a fixed budget exponent \(K_0\). The indices in \(T_j\) include the complementary population. The finite-place bound in §2 and the real comparison in §3 pay for local operations. They leave the signed sum in this last inequality. In the compact proof the common global coefficient is accompanied by an additional bound on qualified tests across the selected family. [Upstream coefficient and fit test](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Rows/GluedFormTheta.lean#L27-L88) · [Native acceptance criterion](https://github.com/OVVO-Financial/RH_Lean/pull/1214)

**Checks.** Exact checks covered the primitive lattice for every \(2\le n\le38\), 629 Ramanujan trace readings, and 1,133 admitted-place valuations, including 63 nonunit cases. The path Gram formula was checked for 312 pairs \((p,\ell)\). At four integer scales from 128 to 1,024, direct finite sums for the residual and the regularized log determinant agreed with the corresponding divisor and truncated trace calculations to \(2\cdot10^{-12}\), using the numerical calibration from the earlier note. The new estimates use regularity of \(E\) and its analytic Mellin value and do not require a new numerical enclosure for that calibration. The calculations and paper proof have not been Lean-verified.

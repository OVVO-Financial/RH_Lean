# Signed Möbius compensation on the physical wheel

There is an unconditional square-root compensation for the entire surplus of the uniform split on \(m/2<p<m\). A pair of integer split-factorial products forces the opposite contribution at smaller primes. The corresponding two profiles fit inside the original wheel, and their measured star determinants recover the served part. This establishes a signed comparison for a specified arithmetic contribution.

For the principal target \(S(m)=\sum_{d\le m}\Lambda(d)(m/d-1)\) and \(M(m)=m\log m-(1+\gamma)m\), a second construction below matches every odd divisor \(d\ge m/6\) and has normalized real size \(M(m)+O(\sqrt m)\). Its residual has both signs and a nonzero Mellin reading at every nontrivial zeta zero. Its square-root lower bound remains open. All new results here are paper deductions.

## A forced exchange for the large-prime surplus

Use \(4\mid m\), \(n=m/2\) and \(c=\lfloor\sqrt x\rfloor\) with \(m=4\lfloor x/4\rfloor\). For \(1/2\le t\le1\) put
\[
g(t)=2(1-t)-(1/t-1)=\frac{(1-t)(2t-1)}{t}.
\]
Extend by \(g(1-t)=-g(t)\) and by zero outside \([0,1]\). This is exactly the previous uniform-split surplus at a prime \(p>m/2\). The uniform split sees that prime with multiplicity \(2(1-p/m)\), while the principal target assigns \(m/p-1\).

At upper addresses \(n<k<m\) put
\[
b^0_k=\lfloor 2c(1-k/m)\rfloor,\qquad
b^1_k=b^0_k+(-1)^{k+1}\lfloor c g(k/m)\rfloor .
\]
Both lie in \([0,2c]\) because \(0\le g(t)\le1-t\) on the upper half. Use the two actual integers
\[
J_i=n^c\prod_{n<k<m} k^{b^i_k}(m-k)^{2c-b^i_k},\qquad i=0,1 .
\]
Their ratio is a product of adjacent split-factorial exchanges \(k/(m-k)\). In particular
\[
\frac1c\log\frac{J_1}{J_0}
=\frac1c\sum_{n<k<m}(-1)^{k+1}\lfloor c g(k/m)\rfloor
                    \log\frac{k}{m-k}.
\]
In fact \(\left|\log(J_1/J_0)\right|/c\le1\) for every positive integer \(c\). Expand the floor as a sum of indicators \(g(k/m)\ge j/c\). Unimodality makes each level set a consecutive interval. The alternating sum of the increasing log factor over that interval is bounded in absolute value by its largest term. Since \(g(t)\le1-t\), this term is at most \(\log(c/j)\). Thus the unnormalized absolute log is at most \(\sum_{j=1}^c\log(c/j)=\log(c^c/c!)\le c\). For the unrounded exchange \(g(t)\log(t/(1-t))\) has bounded variation, giving \(O(1)\) directly.

Write \(\delta_p=v_p(J_1)-v_p(J_0)\). For every odd prime \(m/2<p<m\), \(\delta_p=\lfloor c g(p/m)\rfloor\) exactly. One interval pays pointwise. For an odd prime \(m/3<p<m/2\), \(p^2>m\), the only multiples are \(p\) and \(2p\), giving exactly
\[
\delta_p=-\lfloor c g(1-p/m)\rfloor-\lfloor c g(2p/m)\rfloor\le0.
\]
The inequality is strict throughout any fixed compact subinterval of this rescaled band for large \(m\). For the full smaller-prime population, factorization forces
\[
\boxed{\displaystyle
\frac1c\sum_{p\le m/2}\delta_p\log p
=-\sum_{m/2<p<m}g(p/m)\log p+O(\sqrt m).}
\]
The only rounding charge on the right is \(\vartheta(m)/c=O(\sqrt m)\). The positive side is \((3/4-\log2)m+o(m)\) by the ordinary PNT and direct integration of \(g\). The square-root comparison itself uses only the integer identity, bounded variation and Chebyshev's bound.

The unrounded version locates the payment more precisely. For odd \(d\), the signed first-power response at \(y=d/m\) is \(K_g(y)=\sum_{a\ge1}(-1)^{a+1}g(ay)\). For even \(d\) it is \(-\sum_{a\ge1}g(ay)\). Both are \(O(y)\) by the trapezoidal bound in §4, since \(\int g=0\), \(g(0)=g(1)=0\), and \(g'\) has bounded variation. For odd \(d\) use \(K_g(y)=\sum_a g(ay)-2\sum_a g(2ay)\). Removing small divisors and proper powers as in §4 proves
\[
\sum_{m^{3/4}<p\le m/2}K_g(p/m)\log p
=-\sum_{m/2<p<m}g(p/m)\log p+O(\sqrt m).
\]

**The same exchange on physical sections.** Let \(P\) be the actual served set, \(d_p=\lfloor cx/p\rfloor-c\) its native exponent, and \(h_{i,p}=v_p(J_i)\). Remove \(r_{i,p}=\lfloor(h_{i,p}-4)_+/8\rfloor\) independently from the two copies of the native wheel. Each obeys \(2r_{i,p}\le d_p\). Indeed \(h_{i,p}=0\) for \(p\ge m\). For \(m/2<p<m\), \(h_{i,p}\le3c(1-p/m)\le3(d_p+1)\). For \(p\le m/2\) in \(P\) we have \(p^2\ge m\), whence \(h_{i,p}\le2cm/p\le4(d_p+1)\). Thus both removals together fit within the original capacity.

Use the original site and row sum, divided by \(ck|\mathcal T|/8\), of the difference of native log covolumes at depths \(d-r_0\) and \(d-r_1\), in that order. Denote this signed value by \(G^{\rm alt}_x\). The original slots, ranks, top set \(\mathcal T\), and \(k\) active rows per site are as in §5. On a served layer \(|\delta_p|/c=O(1)\). Indeed \(p^2\ge m\), and the response is one alternating sum sampled at \(p,2p,\ldots\) of the bounded-variation extension of the rounded \(g\) (using odd reflection about the midpoint). Its total variation is \(O(c)\). Also \(|8(r_{1,p}-r_{0,p})-\delta_p|=O(1)\).

The exact star cofactor formula in §5 therefore prices the complementary normal by \(O(\log x)\) per site after division by \(c\). Summing the exponent-rounding units costs \(O(\vartheta(x)/c)\). The original prime incidences and the independently evaluated integer ratio give
\[
\boxed{\displaystyle
G^{\rm alt}_x+\frac1c\sum_{p\notin P}\delta_p\log p
=O\!\left(\sqrt x+\frac{|W|}{|\mathcal T|}\log x\right),}
\]
where \(W\) is the set of occupied partner sites. The native density hypothesis gives \(|W|/|\mathcal T|\le2x^{\varepsilon/8}\). The second term on the left includes all unserved valuations, including those at small primes. This is an independent two-sided bound for this signed exchange on the physical family with its complementary arithmetic mass.

## 1. Which negative contribution is forced

Write \(F_m(j)=j!(m-1-j)!\). Moving an upper split by one has an exact rational reading. Whenever \(a\mid m\) and \(1\le j<m/a\),
\[
\frac{F_m(aj)}{F_m(aj-1)}=\frac{aj}{m-aj}
=\frac{F_{m/a}(j)}{F_{m/a}(j-1)}.
\]
Using \(a=2,4\) lets one move an exchange to a different scale with the same numerator-to-denominator ratio at every place. Its two valuation changes are tied.

Extend \(L(y)=(1/y-1)_+\) to \(y>0\) and set
\[
U(y)=\sum_{j\le 1/y}\mu(j)L(jy).
\]
Finite Möbius inversion gives \(\sum_{r\ge1}U(ry)=L(y)\). On \(1/6\le y\le1/5\) the terms with \(j=1,2,3,5\) give \(U(y)=2-1/(30y)\), including both endpoints by continuity. Thus a tail reproducing this interval carries signed mass \(U(1/6)-U(1/5)=-1/30\).

## 2. A signed family of split factorials

Take \(4\mid m\), \(n=m/2\). Define \(A,B,C_0,D\) on \([0,1]\), all zero outside that interval. On the upper half set
\[
\begin{aligned}
A(t)&=1/t-1,\\
B(t)&=U(t/2)-A(t/2),\\
C_0(t)&=\begin{cases}
0,&1/2\le t\le2/3,\\
U(t/4)-A(t/4)-B(t/2),&2/3\le t\le1,
\end{cases}\\
D(t)&=(1-|12t-7|)_+ .
\end{aligned}
\]
Complete each function on the lower half before defining the next. Use \(A(1-t)=2-A(t)\) and \(f(1-t)=-f(t)\) for the other three. The formulas agree at the joins. For example \(U(1/4)=5/3\), \(U(1/3)=3/2\), and \(U(1/6)=9/5\). Put \(C=C_0+\eta D\), with \(\eta\) determined below. The multiplicity of the factor \(k\), for \(1\le k<m\), is
\[
T_m(k)=A(k/m)+\mathbf1_{2\mid k}B(k/m)+\mathbf1_{4\mid k}C(k/m).
\]
Then \(T_m(k)+T_m(m-k)=2\) and \(T_m(n)=1\). Set \(H(k)=T_m(k)\) for \(n\le k<m\) and \(H(m)=0\). The coefficients \(H(j)-H(j+1)\) on \(F_m(j)\), \(n\le j<m\), sum to one. Summation by parts gives the actual log reading
\[
L_m=\sum_{k=1}^{m-1} T_m(k)\log k
=\log(n!(n-1)!)+\sum_{n<k<m} H(k)\log\frac{k}{m-k}.
\]
The differences of \(H\) may have either sign.

For odd \(d\) let \(y=d/m\) and \(V(y)=A(y)+B(2y)+C(4y)\). Reindex the even and fourfold multiples of \(d\) to get
\[
\sum_{1\le r,\ rd<m}T_m(rd)=\sum_{r\ge1} V(ry).
\]
Endpoint terms at \(rd=m\) vanish. On \([1/2,1]\) the first summand of \(V\) gives \(U\). On \([1/4,1/2]\) the second supplies \(U(y)-A(y)\). On \([1/6,1/4]\) the third supplies the remaining difference. The upper support of \(D\) is inside \((1/2,2/3)\), so this last statement holds for every \(\eta\). Consequently
\[
\boxed{\displaystyle \sum_{1\le r,\ rd<m}T_m(rd)=m/d-1\quad
(d\ \mathrm{odd},\ m/6\le d\le m).}
\]
This also covers every unserved odd divisor in that range.

## 3. Independent real size and integer rounding

Let \(I(f)=\int_{1/2}^1 f(t)\log(t/(1-t))\,dt\). Choose the one free scalar using the integer main term
\[
\eta=4\,\frac{\log2-\gamma-I(A)-I(B)/2-I(C_0)/4}{I(D)}.
\]
Here \(I(D)>0\), and \(0.039<\eta<0.044\) (bounds below). This calibration uses ordinary integrals independently of the prime distribution. Each integrand has bounded variation, including at \(1\), because its coefficient vanishes there at least linearly. The three upper sums of mesh \(1/m,2/m,4/m\) equal \(mI(A),mI(B)/2,mI(C)/4\), respectively, with \(O(1)\) errors. Stirling for \(n!(n-1)!\) now gives
\[
L_m=M(m)+O(\log m).
\]

The occupied factors obey \(0\le T_m(k)\le2\). Here are algebraic checks on the upper half. Throughout, \(B\le0\). On \([1/2,2/3]\),
\(A+B=(9t^2-16t+8)/(3t(2-t))>0\), \(C_0=0\), and \(0\le\eta D<0.044\). On \([2/3,1]\), \(A+B=4(1-t)^2/[t(2-t)]\) and \(0\le C_0\le1/6\). For the last lower bound the expression for \(C_0\), on the two sides of \(4/5\), is
\[
\frac{(3t-2)(-15t^3+46t^2-20t+16)}{15t(4-t)(2-t)(2+t)}
\quad\text{and}\quad
\frac{4(1-t)^2(8+6t-3t^2)}{3t(4-t)(2-t)(2+t)} .
\]
For the upper bound use \(U(t/4)\le11/6\), \(A(t/4)\ge5/3\), and \(B(t/2)\ge0\) there. Reflection gives the lower-half bounds.

Take \(m=4\lfloor x/4\rfloor\), \(c=\lfloor\sqrt x\rfloor\), for large \(x\). Round once at each upper address with \(b_k=\lfloor cH(k)\rfloor\). The associated rational exchanges multiply to an integer
\[
J=(n!(n-1)!)^c\prod_{n<k<m}\left(\frac{k}{m-k}\right)^{b_k}
=n^c\prod_{n<k<m}k^{b_k}(m-k)^{2c-b_k}.
\]
The normalized difference from \(L_m\) is at most \(\log\binom{m-1}{n}/c=O(\sqrt m)\). For an odd prime \(m/6\le p\le m\), eventually \(p^2>m\). Each of its at most six address readings has rounding error at most one, so \(|v_p(J)-c(m/p-1)|\le6\). If literal domination on this band is wanted, the single integer \(J\,\mathrm{lcm}(1,\ldots,m)^7\) gives it even for the native depth \(\lfloor cx/p\rfloor-c\). Its added log cost divided by \(c\) is \(7\psi(m)/c=O(\sqrt m)\). The physical comparison below uses \(J\) itself.

## 4. The signed prime sum that survives

For \(0<y\le1\) put \(E(y)=\sum_{r\ge1}V(ry)-(1/y-1)\) and set \(E=0\) for \(y>1\). It vanishes on \([1/6,1]\). Direct substitution gives
\[
E(1/7)=-1/18+6\eta/7<0,\qquad
E(1/10)=17/252-4\eta/5>0 .
\]

There is a useful uniform small-divisor saving. For arbitrary \(d\) replace \(V\) by
\[
V_d(y)=A(y)+B\bigl((2/\gcd(2,d))y\bigr)+C\bigl((4/\gcd(4,d))y\bigr).
\]
All three possible functions have integral one, value two at zero and value zero at one. Their derivatives on the positive half-line, with the functions extended by zero after one, have bounded variation. The trapezoidal rule on intervals of length \(y\), with total error bounded by \(O(y^2\operatorname{Var}(V_d'))\), gives
\[
\sum_{r\ge1}V_d(ry)=1/y-1+O(y)
\]
uniformly. The contribution of \(d\le m^{3/4}\) to the error is therefore \(O(m^{-1}\sum_{d\le m^{3/4}}d\Lambda(d))=O(\sqrt m)\) by Chebyshev's bound. Proper prime powers together cost \(O(\sqrt m)\) since \(\psi(m)-\vartheta(m)\ll\sqrt m\). Using \(\log k=\sum_{d\mid k}\Lambda(d)\) yields
\[
\boxed{\displaystyle L_m-S(m)
=\sum_{m^{3/4}<p<m/6}E(p/m)\log p+O(\sqrt m).}
\]
Replacing \(m\) by \(x\) in \(S-M\) costs \(O(\log m)\) because \(0\le x-m<4\) and \(\sum_{d\le x}\Lambda(d)/d=O(\log x)\).

The two signs both carry linear mass. To compute the mean of \(E\), Mellin integration first for \(\Re s>1\) gives
\[
\int_0^1 E(y)y^{s-1}\,dy
=\zeta(s)\int_0^1 V(y)y^{s-1}\,dy-\frac{1}{s(s-1)} .
\]
Taking \(s\downarrow1\) gives \(\int E=1+\gamma+\int V(y)\log y\,dy\). Reflection shows that \(\int A(y)\log y\,dy=-(1+\log2)+I(A)\), and the two antisymmetric terms contribute \(I(B)/2+I(C)/4\) after dilation. The calibration therefore gives \(\int E=0\). For \(E_\pm=\max(\pm E,0)\) put \(\kappa=\int_0^{1/6}E_+(y)\,dy=\int_0^{1/6}E_-(y)\,dy\). Continuity and the two strict signs give \(\kappa>0\). The ordinary PNT applied to the continuous weights \(E_\pm\), extended by zero at the origin, now gives
\[
\sum_{m^{3/4}<p<m/6}E_\pm(p/m)\log p=\kappa m+o(m).
\]
This conclusion is for the complete prime population. The signed square-root rate is a stronger assertion.

The force and the limitation of the alternating exchange can be distinguished analytically. Its Mellin transform for \(\Re s>1\), continued to \(\Re s>0\), is
\[
\widehat K_g(s)=\zeta(s)(1-2^{1-s})\widehat g(s).
\]
At a nontrivial zeta zero \(\rho\), \(\widehat K_g(\rho)=0\), while the preceding formula for the residual gives \(\widehat E(\rho)=1/[\rho(1-\rho)]\). Thus adding any finite sum of these alternating exchanges leaves the residual's critical-zero reading unchanged.

There is also a version with strictly positive surplus above \(m/2\) on the calibrated profile itself. Add \((-1)^{k+1}g_0(k/m)\) to its upper \(H(k)\), with \(g_0(t)=(2t-1)(1-t)^2\) for \(t\ge1/2\) and the same antisymmetric extension. This preserves \(0\le H\le2\). Indeed on \([1/2,2/3]\) the expression for \(A+B\) in §3 is at least \(4/9\), and on \([2/3,1]\) it is at least \(4(1-t)^2\). The real log changes by \(O(1)\). Every prime \(p>m/2\), \(p<m\), gains \(g_0(p/m)\), whose total is \(m/96+o(m)\). The opposite movement at smaller primes matches that gain to \(O(\sqrt m)\) by the same alternating argument. This preserves the unresolved residual \(E\) after subtracting the explicitly paid exchange.

## 5. Two profiles on the actual partner sites

Use the served high first-prime set \(P\), where \(p^2\ge x\) and \(p+1\le x\). Let
\[
d_p=\lfloor cx/p\rfloor-c,\qquad h_p=v_p(J),\qquad
u_p=\lfloor d_p/6\rfloor,\qquad v_p^*=\left\lfloor(h_p-6)_+/6\right\rfloor.
\]
The factor six reserves capacity in the original wheel. The fixed subtraction protects primes very close to the top where the available exponent can be zero. The second removal is determined solely by \(J\) and the label \(p\).

Both removals satisfy \(2u_p,\,2v_p^*\le d_p\). For \(p\ge m/6\) use \(h_p-6\le c(m/p-1)\) when \(p\le m\), and \(h_p=0\) when \(p>m\). For \(p<m/6\), each address has exponent at most \(2c\) and \(p^2\ge m\), so \(h_p\le 2cm/p\). Since \(m/p>6\), \(2cm/(3p)\le c(m/p-1)-1\le d_p\). This proves simultaneous availability. Use the residual exponents \(\beta_p=d_p-u_p\) and \(\alpha_p=d_p-v_p^*\) on the original layer of \(p\). Their depth powers divide the original \(p^{d_p}\) integrally.

Write \(\mathscr L_{sj}(a)\) for the native log covolume of the star at occupied site \(s\), active row \(j\), using powers \(p_i^{a_i}\). If \(n_i\) are the original layer sizes, the omit-one Gram formula gives the exact identity
\[
\mathscr L_{sj}(\beta)-\mathscr L_{sj}(\alpha)
=\sum_i(\beta_i-\alpha_i)\log p_i+
\frac12\log\frac{\sum_i p_i^{-2\beta_i}/n_i}{\sum_i p_i^{-2\alpha_i}/n_i}.
\]
The absolute value of the last term is at most \(\max_i\bigl(|\beta_i-\alpha_i|\log p_i\bigr)\). This follows by bounding every term in the numerator against its corresponding denominator term.

On \(P\), normalized valuation rounding gives
\[
\frac6c(\beta_p-\alpha_p)=E(p/m)+
O\!\left(\frac{m}{cp}+\frac1c+\frac1p\right).
\]
Indeed at most \(m/p\) factors contribute a rounding unit each, passing from \(x\) to \(m\) costs at most \(4/p\), and clearing the two integer sixths costs \(O(1/c)\). For \(m<p\le x\) the same bound holds directly. The right-hand side, including \(E\), is uniformly bounded, since \(p\ge\sqrt x\). Summing the displayed error against \(\log p\) costs \(O(\sqrt x\log x)\).

Let \(k=|T|n_{\rm lift}>0\) be the common number of active rows per site and let the original top set \(\mathcal T\) be nonempty. With \(W\) the set of occupied sites, define
\[
G_x=\frac6{ck|\mathcal T|}\sum_{s\in W}\sum_{j\in\mathrm{siteRows}(s)}
\bigl(\mathscr L_{sj}(\beta)-\mathscr L_{sj}(\alpha)\bigr).
\]
Every served prime occurs once per original top in the site sum. The complementary normal costs \(O((|W|/|\mathcal T|)\log x)\) in total by the pointwise bound. Under the native top-density hypothesis \(|W|/|\mathcal T|\le 2x^{\varepsilon/8}\), this proves
\[
\boxed{\displaystyle
G_x=\sum_{p\in P} E(p/m)\log p+
O\!\left(\sqrt x\log x+x^{\varepsilon/8}\log x\right).}
\]
All determinants here use the original star rank, slots, partner incidences and row multiplicities. These deductions use the existing Gram and counting theorems. [Physical Gram determinant](https://github.com/OVVO-Financial/RH_Lean/blob/d9c30d780b9fa5b82173cc20e6f6ebc53b10689d/research/NativeMeasuredSlotProjector.lean#L363-L400) · [Site multiplicities and prime incidences](https://github.com/OVVO-Financial/RH_Lean/blob/d9c30d780b9fa5b82173cc20e6f6ebc53b10689d/research/NativeTranslatedSlotFrame.lean#L222-L345) · [Native depth and density hypotheses](https://github.com/OVVO-Financial/RH_Lean/blob/d9c30d780b9fa5b82173cc20e6f6ebc53b10689d/research/NativeTranslatedSlotFrame.lean#L621-L675)

The two signs can also be measured individually. Take the intermediate depth \(\max(\beta,\alpha)\) coordinatewise. The increments from \(\alpha\) and from \(\beta\) to this common profile are nonnegative by the Gram formula. Their difference is exactly \(G_x\) after normalization. The same cofactor bound and the Lipschitz property of the positive part identify these two increments with \(\sum_{p\in P}E_\pm(p/m)\log p\), respectively, to the displayed accuracy. Adding the respective unserved masses yields \(\kappa m+o(m)\) for each sign under the native density hypothesis.

To bound \(S(x)-M(x)\) from above, the required direction is
\[
G_x+\sum_{\substack{m^{3/4}<p<m/6\\p\notin P}}E(p/m)\log p
\ \ge\ -O_\varepsilon(x^{1/2+K\varepsilon}).
\]
The exchange and Gram identities force the readings in this inequality. An independent lower bound for their sum on the required windows is still missing. [Native window acceptance criterion](https://github.com/OVVO-Financial/RH_Lean/pull/1214)

## 6. Checks and numerical enclosure

The sole numerical fact used in the proofs is the coarse bound on \(\eta\). A reproducible enclosure uses the composite midpoint rule on the dyadic cuts \(1-2^{-j}\), \(1\le j\le26\), inserting \(7/12,2/3,4/5\) and using 2,048 equal pieces between successive cuts. For \(f=A,B,C_0,D\) on each smooth piece, the explicit formulas give \(|f'|\le32,\ |f''|\le500\). Writing \(u=1-t\), one has \(|f|\le32u\) and \(\left|(f(t)\log(t/(1-t)))''\right|\le700/u\). Each block has width \(b\le\min u\), so the sum of its midpoint error bounds is at most \(700/(96\cdot2048^2)\). The discarded tail beyond \(1-2^{-26}\) contributes less than \(10^{-12}\). The four midpoint sums, rounded to nine decimals, are
\[
0.129319853,\quad -0.033786716,\quad 0.012864151,\quad 0.028177079.
\]
Allow \(0.0000018\) on either side of each. For \(\gamma\) use the interval from \(H_{1024}-\log1024-1/2048\) to that value plus \(1/(12\cdot1024^2)\), by the harmonic Euler–Maclaurin bounds. Substitution gives \(0.04057<\eta<0.04149\). The checks used 48-decimal arithmetic for the midpoint sums. For the alternating exchange, exact tests checked 24 full prime factorizations and their archimedean ratio bounds, 2,492 upper-prime readings, 5,099 two-profile capacity cases, and 6,480 odd-divisor kernel evaluations.

Exact rational tests for \(4\mid m,\ 4\le m\le320\) checked 5,400 outer odd-divisor identities separately in their constant and \(\eta\) coefficients, and 12,880 reflection identities. Integer tests using the rational sample \(\eta=41/1000\) checked 2,968 half-capacity cases and 42 exact Gram comparisons. As an arithmetic example at \(m=x=10^8\), using the entire interval \(0.039<\eta<0.044\) encloses \(h_p-d_p\) in \([-220,-177]\) at \(p=14{,}285{,}693\), and in \([324,364]\) at \(p=9{,}999{,}991\). These examples assert no particular Frobenius class. The paper comparison has not been formalized in Lean.

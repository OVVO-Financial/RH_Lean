# CORR-4: exact quotient-bucket Abel pilot and the moving hyperbola diagonal (2026-10-26)

**Status:** independent, reproducible finite tests added to PR #1026. The exact Abel identity is proved here by finite interchange on paper and exhaustively checked numerically in integer tent numerators; **not yet formalized in Lean**. A uniform high-source signed power saving and an RH consequence remain **OPEN**.

Reproduce with:

```bash
python scripts/corr4_bucket_hyperbola_pilot.py --R 1027 --H 5000 --T 150
python scripts/corr4_bucket_hyperbola_pilot.py --R 1027 --H 3000 --T 250
python scripts/corr4_bucket_hyperbola_pilot.py --R 317 --H 1000 --T 90
```

Requires Python and numpy. The original, not simulated, coefficients are computed multiplicatively via the local Eisenstein inverse polynomials. The code independently verifies the sharp #919 \(M(Y)=\sum_{m\le Y}a_6(m)K(\lfloor Y/m\rfloor)\) on three tent sites, with the 36-period kernel and all 2/3 exclusions restored.

## A. Exact finite quotient Abel identity

Put \(X=R^2-1\), integers \(H,T\ge1\), \(X\ge H\), and \(a_6(m)=1_{(m,6)=1}(\mu*(\chi_{-3}\mu))(m)\). Let \(K(0)=0\) be the actual 36-period integer quotient kernel, \(d(u)=K(u)-K(u-1)\), and \(A_6(y)=\sum_{m\le y}a_6(m)\). Define the genuine discrete tent:

\[
\mathcal A_Hf(X)=H^{-2}\sum_{|h|<H}(H-|h|)f(X+h),\qquad
\Phi_{H,X}(v)=\mathcal A_H\mathbf1_{X+h\ge v}.
\]

For the **high source** with \(m>T\) the exact finite interchange is

\[
\boxed{\mathrm{High}_{T,H}(X)=
\sum_{u=1}^{\lfloor(X+H-1)/(T+1)\rfloor}
 d(u)\sum_{m>T}a_6(m)\Phi_{H,X}(um).}\tag{A}
\]

The upper limit is the **sharp nonzero-bucket limit** because \(m\ge T+1\) and \(h\le H-1\). Every inner sum is finite, supported on \(m\le(X+H-1)/u\). This identity keeps all signs, prime-power coefficients, quotient buckets and boundary ramps. It has **no** cancellation hypothesis.

Equivalently, let \(U_0=\lfloor(X+H-1)/T\rfloor\). Then

\[
\boxed{\begin{aligned}
\mathrm{High}_{T,H}(X)
={}&\sum_{u=1}^{U_0} d(u)\,
\mathcal A_H\!\left[
 A_6\!\left(\left\lfloor\frac{X+h}{u}\right\rfloor\right)
 \mathbf1_{X+h\ge uT}\right]\\
&-A_6(T)\mathcal A_H K\!\left(\left\lfloor\frac{X+h}{T}\right\rfloor\right).
\end{aligned}}\tag{B}
\]

The \(\mathbf1\) gate is essential: removing it when \((X+h)/u<T\) makes (B) false. In (B) the upper limit \(U_0\) is needed for the **separated** boundary term, even though the combined bracket vanishes for \(u>\lfloor(X+H-1)/(T+1)\rfloor\). The paper-level bound on that boundary term is \(2592T^3/H^2\), using the prior Lean-proved \(\sum_{m\le T}|a_6(m)|\le T\).

## B. Exact first pilot (R=1027, H=5000, T=150)

Here \(X=1,054,728\). Using integer numerators for all tent ramps:

| Quantity | Value |
|---|---:|
| \(M(X)\) | +367 |
| \(\mathcal A_HM(X)\) | +355.54652308 |
| Low \(m\le150\) | -0.04506604 |
| High \(m>150\) | +355.59158912 |
| High from exact Abel (A) | +355.59158912 |
| **Difference of integer tent numerators** | **0** |
| Sharp nonzero \(U_*=\lfloor(X+H-1)/(T+1)\rfloor\) | 7,018 |
| Original separated \(U_0=\lfloor(X+H-1)/T\rfloor\) | 7,064 |
| \(\sum_{u} |d(u)B_u|\), \(B_u=\sum_{m>T}a_6(m)\Phi_{H,X}(um)\) | **93,335.21720752** |
| \(\sum_u d(u)B_u\) | **355.59158912** |

Thus the **inter-quotient signed cancellation is itself essential**: the absolute bucket bill is approximately 262.5 times the signed output. Bounding each bucket separately with no saving on the \(U_*\) summation will not establish the desired high-source theorem.

The **sharp quotient-1 bucket** \(A_6(X)-A_6(\lfloor X/2\rfloor)\) is **+82**, not +75:

| Actual \(m\in(X/2,X]\) population | Value |
|---|---:|
| 19,398 split primes \(m=p>R,\ p\equiv1\pmod3\) | -38,796 |
| Nonprime terms with \(P^+(m)>R\) (including \(m=cp\)) | +49,446 |
| \(R\)-smooth terms \(P^+(m)\le R\) | **-10,568** |
| All composites | +38,878 |
| **Net** | **+82** |

These values independently reproduce the existing **+82** in `CORR4_MIXED_TAIL_RECORD_PLATEAU_FEJER_20261026.md`. The proposed -10,575 smooth subtotal is not consistent with the original \(a_6\) sequence.

Additional independent pilots:
- \(R=317,H=1000,T=90\): high -26.249308, exact Abel numerator error 0; absolute quotient bill 10,967.206964.
- \(R=1027,H=3000,T=250\): high +362.695810111111..., exact Abel numerator error 0; absolute quotient bill 57,182.094555.

**Note:** this finite pilot is not in the asymptotic critical scaling \(H\asymp R^{7/4-\eta/2}\), so its approximately 7,000 quotient slots are not a refutation of the asymptotic \(R^{1/4+O(\eta+\delta)}\) count.

## C. Hyperbola test: frozen square-root cutoff fails

Write \(\mu_6(n)=1_{(n,6)=1}\mu(n)\), \(b_6(n)=\chi_{-3}(n)\mu_6(n)\), \(M_6(y)=\sum_{n\le y}\mu_6(n)\), and \(B_6(y)=\sum_{n\le y}b_6(n)\). Since \(a_6=\mu_6*b_6\), the **correct** Dirichlet hyperbola with \(z=\lfloor\sqrt Y\rfloor\) is

\[
\boxed{
A_6(Y)=
 \sum_{a\le z}\mu_6(a)B_6(\lfloor Y/a\rfloor)
 +\sum_{b\le z}b_6(b)M_6(\lfloor Y/b\rfloor)
 - M_6(z)B_6(z).}\tag{C}
\]

It holds **for each \(Y\)**. When \(Y=\lfloor(X+h)/u\rfloor\), its cutoff \(z(h)\) moves with \(h\). Since \(H/u\gg\sqrt{X/u}\) in the proposed regime, the moving diagonal is not optional: there is generally no fixed \(z\) satisfying \(z^2\le Y<(z+1)^2\) across the tent.

For \(u=1,R=1027,H=5000\), freezing \(z=\lfloor\sqrt X\rfloor=1026\) makes the hyperbola formula differ from the true \(A_6(X+h)\) at **4,999** of the 9,999 tent sites. It is **one unit too low at every \(h=1,\ldots,4999\)**. Exactly at \(h=1\), the omitted pair \(a=b=1027\) enters since \(1027^2=X+1\), with \(\mu_6(1027)b_6(1027)=+1\).

Its **tent-averaged** loss is -0.4999:

| \(u=1\) tent-smoothed quantity | Value |
|---|---:|
| First frozen hyperbola sum | -266.05910416 |
| Second frozen hyperbola sum | -279.63770264 |
| Frozen intersection \(-M_6(1026)B_6(1026)\) | +141 |
| Frozen hyperbola result | **-404.69680680** |
| Exact \(\mathcal A_H A_6(X+h)\) | **-404.19690680** |
| Frozen minus exact | **-0.49990000** |

At \(R=317,H=1000\), the analogous frozen error is +0.4995 (the square-root crossing has opposite \(\chi_{-3}\) sign). In both pilots the **moving-cutoff** formula (C) reproduces \(A_6(Y)\) exactly at the checked window endpoints and center.

## D. Why the proposed sawtooth smoothing is insufficient

The two hyperbola summands in (C) contain \(M_6(\lfloor Y/b\rfloor)\) and \(B_6(\lfloor Y/a\rfloor)\), **nonperiodic signed arithmetic prefix sums**, not bare floor sawtooths. The \(\mathcal A_H\) operator may smooth a periodic discontinuity but does not bound those prefix sums merely because \(ua\ll H\).

One must also distinguish a continuously centered sawtooth \(\{n/q\}-1/2\), which on the integer lattice has average \(-1/(2q)\), from a *discretely centered* periodic remainder. At \(q=1\) the former is identically -1/2. Consequently a bound \(O(q^2/H^2)\) for the former without centering and its divisibility correction is **false**. Even after proper centering, the arithmetic main and moving diagonal remain.

**The outstanding mathematics is now sharply localized:** obtain a uniform signed estimate on the full Abel pairing
\[
\left|\sum_{u\le U_*}\Delta K(u) B_u(X,H,T)\right|\ll H^{1-\kappa}
\]
at the critical exponents, **retaining** the quotient-1 principal split-prime mode, the fixed/nonfixed hyperbola diagonal and all boundary collars. A genuine cross-quotient arithmetic cancellation estimate is required; the 36-period oscillation of \(K\), the numerical 262-to-1 cancellation ratio, or tent smoothing of isolated sawteeth do not establish it.

In the zero-target NNS/Co-Div vocabulary, the missing input can equivalently be framed as a bound on the complete signed Gram:
\[
\left(\sum_u d(u)B_u\right)^2
=\sum_u d(u)^2 B_u^2+2\sum_{u<v}d(u)d(v)B_uB_v
=O(H^{2-2\kappa}).
\]
That equality is algebraic; **its uniform upper bound is not proved**.

**Next Lean acceptance:** port (A)/(B) as finite `Finset.sum_comm` + `K(0)=0` + discrete telescoping, with exact strict \(m>T\) gate and \(U_*,U_0\) distinction. Keep (C) with a moving \(z(h)\) or an explicit correction collar. Do not upgrade either to a claimed analytic improvement.


## E. New fixed-cutoff and second-Abel audit (2026-10-26)

**Independent execution:** `/mnt/data/corr4_second_abel_audit.py` in the analysis container (not a repository fixture) reproduced the integer tent numerators and verified the fixed asymmetric hyperbola at 15 sample (u,Y) pairs with u in {1,2,5,100,500}. The repository acceptance script `scripts/corr4_bucket_hyperbola_pilot.py` now includes the same fixed-cutoff and first/second Abel assertions. The new Lean module `research/CORR4_FIXED_HYPERBOLA_DOUBLE_ABEL_20261026.lean` has been committed for CI; compilation must be checked, not presumed.

### E.1 The exact asymmetric hyperbola identity

Let f=mu_6, g=chi_-3*mu_6 pointwise (NOT a Dirichlet convolution in this notation), F(z)=sum_{a<=z}f(a), G(z)=sum_{b<=z}g(b). For an arbitrary integer y0>=1, entirely independent of h,

\[
\boxed{A_6(Y)
=\sum_{a\le y_0}f(a)G(\lfloor Y/a\rfloor)
+\sum_{b\le\lfloor Y/(y_0+1)\rfloor}
 g(b)\left[F(\lfloor Y/b\rfloor)-F(y_0)\right].}\tag{D}
\]

It partitions a<=y0 and a>y0, so there is no moving square-root overlap correction. The **b cutoff still varies with Y**. Replacing it with y0 or dropping its gate is not justified.

The previous symmetric frozen-root error at (R,H,u)=(1027,5000,1) is -1 at all 4999 sites h=1..4999 and 0 elsewhere; exact tent-averaged defect is **-0.4999**. A reported 41.34 is not the defect in this genuine coefficient audit. The moving sqrt boundary crosses more than one integer, but the *signed omitted region* reduces to this single unit in this pilot.

### E.2 First and second Abel, with endpoints

For B_u=sum_{m>T} a6(m) Phi_{H,X}(um), K(0)=0, d(u)=K(u)-K(u-1), P(u)=sum_{j=1}^u K(j), B_{U+1}=B_{U+2}=0, finite telescoping yields

\[
\boxed{\sum_{u=1}^{U}d(u) B_u
=\sum_{u=1}^{U}K(u)(B_u-B_{u+1})
=\sum_{u=1}^{U}P(u)(B_u-2B_{u+1}+B_{u+2}).}\tag{E}
\]

**The exact primitive range [-4,4], step rule, and first quotient Abel lemma are already Lean-certified** in `research/VF_MID_919_QUOTIENT_SIGNED_RETURN.lean`: `vf919QuotientKernelPrimitive36_bounds`, `vf919QuotientKernelPrimitive36_step`, `vf919QuotientKernel36_signed_abel`. New proof work must reuse these declarations instead of reproving them. The real new formalization is the difference-kernel Abel identity and its composition with the existing primitive, including b(U+1)=b(U+2)=0.

**Executed R=1027,H=5000,T=150**: first Abel, second Abel and original high-source tent pairing have **identical integer numerators 8,889,789,728**. The absolute sums of first/second differences are 4,199.22532216 and 5,766.53300356, giving the rigorous but loose second-Abel upper bound 23,066.13201424 compared with the signed total 355.59158912. The earlier 93,335.21720752 is **sum |d(u)B_u|, not sum |B_u|**; it suppresses the d(u)=0 buckets.

### E.3 Stronger high-quotient tail: the entire range can be paid unconditionally

The monotone tent ramp gives 0<=Phi(um)<=1 and Phi(um)>=Phi((u+1)m). For 1<=L<=U_* and B_{U_*+1}=0, the **range-restricted** first Abel identity is

\[
\sum_{u=L}^{U_*}d(u)B_u
=-K(L-1)B_L+\sum_{u=L}^{U_*}K(u)(B_u-B_{u+1}).\tag{F}
\]

Use the same original occurrence coefficients and DO NOT replace B_u by absolute masses. The triangle inequality **after** Abel is legal because
\[
\begin{aligned}
|B_L|&\le\sum_{m>T}|a_6(m)|\Phi(Lm),\\
\sum_{u=L}^{U_*}|B_u-B_{u+1}|
&\le\sum_{m>T}|a_6(m)|\sum_{u=L}^{U_*}(\Phi(um)-\Phi((u+1)m))\\
&=\sum_{m>T}|a_6(m)|\Phi(Lm).
\end{aligned}
\]
The inner difference of Phi is nonnegative: it is the essential monotonicity that permits **telescoping before absolute summation over all u**. Since |K(u)|<=2 and the already-proved genuine coefficient mass is sum_{m<=N}|a6(m)|<=N,

\[
\boxed{
\left|\sum_{u=L}^{U_*}d(u)B_u\right|
\le4\sum_{T<m\le\lfloor(X+H-1)/L\rfloor}|a_6(m)|
\le4\left\lfloor\frac{X+H-1}{L}\right\rfloor.}\tag{G}
\]

This is an **unconditional deterministic high-u tail estimate** on the genuine signed high-norm source. No heuristic n^epsilon divisor bound, Mertens saving, special Hecke phase or second Abel estimate is needed. At the critical scaling X~H^(8/7), choosing L=ceil(H^(1/7+2kappa)) yields a high-u tail O(H^(1-2kappa)), subject to the exponent bookkeeping and rounding. If L>U_*, the high-u tail is empty.

**This does NOT bound the remaining low-u term.** The independent missing inequality is precisely
\[
\left|\sum_{1\le u<L}d(u)B_u\right|\ll H^{1-\kappa}
\]
with the true y0-fixed asymmetric hyperbola and the principal split-prime source intact.

### E.4 The proposed low-u proof has an analytic gap

Even with fixed y0=H^(4/7), the first hyperbola term contains G(floor((X+h)/(ua))) with argument t~X/(ua) and tent-window length W~H/(ua). Their ratio is W/t~H/X~H^(-1/7), a **fixed power-short relative window**. The classical fixed-conductor zero-free region yields a global bound of the form |G(t)|<=t exp(-c(log t)^alpha) (log refinements omitted). Difference of two such global bounds supplies at best t exp(-c(log t)^alpha), **larger than W=t H^(-1/7)** for asymptotically large H. Hence this theorem does *not* establish signed power cancellation for the hyperbola's short arithmetic increments, even when ua<<H.

Furthermore, the term `F(floor(Y/b))-F(y0)` from (D) can be as hard as the original Mobius signed cancellation. The Euler identity of 1/zeta_K eliminates a limiting average/main pole, but does not prove finite-cutoff cancellation of the split-prime, cofactor and smooth populations with the required power rate.

**Precise new input needed:** a uniform bilinear/Type-II or short-interval signed estimate on the actual f/g convolution, with all (u,a,b) weights, moving b gate, y0 cutoff and boundary collars, strong enough to sum u<L. Existing PNT/zero-free estimates alone do not discharge this obligation. No RH or 7/8 improvement has been proved by (D)-(G).

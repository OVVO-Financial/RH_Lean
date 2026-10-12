# Exact density-preserving multiplicative Möbius correlations (all prime dilations)

**11 October 2026.** This records a universal UNCONDITIONAL multiplicative dependence theorem, including the genuine known Möbius densities, rather than inferring weak dependence from near-zero fixed-additive-lag correlations of square-block aggregates. The exact coefficient identity is finite arithmetic; the squarefree density estimate is elementary, and the equal positive/negative sign densities follow from the classical prime number theorem. Does NOT establish finite A/C or RH. Not newly compiled in Lean.

## 1. Complete conditional SIGN theorem, without a random model

For **all integers** n,k>=1, the actual Möbius function obeys
\[
\boxed{\mu(n)\mu(kn)=\mu(k)\mu(n)^2\,{\bf1}_{\gcd(n,k)=1}.}\tag{1}
\]
If k is squarefree, its prime-factor parity \(\mu(k)=(-1)^{\omega(k)}\) determines the sign of EVERY nonzero matched pair, not just its mean. If k is not squarefree, the child always has Möbius weight zero. In particular for ANY prime p,
\[
\boxed{\mu(pn)=-\mu(n){\bf1}_{p\nmid n}}\tag{2}
\]
identically, including squareful zeros. On the actual p-free squarefree carrier the masked parent and child are perfectly anticorrelated at EVERY FINITE endpoint, with no stochastic independence hypothesis.

## 2. The unconditional true squarefree/zero/sign densities

Put
\[
Z_k(N)=\sum_{\substack{1\le n\le N\\\gcd(n,k)=1}}\mu(n)^2,\quad
\delta_k=\frac6{\pi^2}\prod_{p\mid k}\frac p{p+1},
\quad\omega(k)=\#\{p:p\mid k\}.
\]
The product is over the DISTINCT actual prime divisors of k.

A fully uniform elementary bound is
\[
\boxed{|Z_k(N)-\delta_k N|
\le(2^{\omega(k)}+2)\sqrt N
\qquad(k,N\ge1).}\tag{3}
\]
Here is the finite arithmetic proof. The exact square-divisor Möbius inversion
\(\mu(n)^2=\sum_{d^2\mid n}\mu(d)\) gives
\[
Z_k(N)=\sum_{\substack{d\le\sqrt N\\(d,k)=1}}\mu(d)
\,C_k(\lfloor N/d^2\rfloor),
\quad C_k(y)=\#\{m\le y:(m,k)=1\}.
\]
Divisor inclusion/exclusion gives \(C_k(y)=\frac{\varphi(k)}k y+O(2^{\omega(k)})\) with absolute coefficient at most \(2^{\omega(k)}\). After summing floor errors there are at most \(\sqrt N\) terms, and extending the square-divisor sum to infinity costs at most \(N/\lfloor\sqrt N\rfloor<2\sqrt N\). The exact Euler product then yields \(\delta_k\). No use of RH, randomness, ergodicity or an unknown correlation conjecture.

For ONE prime p the sharper identity
\[
Z_p(N)=\sum_{\substack{d\le\sqrt N\\p\nmid d}}\mu(d)
\left(\lfloor N/d^2\rfloor-\lfloor N/(p d^2)\rfloor\right)
\]
has at most ONE floor-unit error per d. Therefore the striking uniform-in-p inequality holds:
\[
\boxed{
\left|\sum_{n\le N}\mu(n)\mu(pn)
+\frac6{\pi^2}\frac p{p+1}\,N\right|
\le3\sqrt N
\quad\forall\,N\ge1,\ \forall\,p\ {\rm prime}.}\tag{4}
\]
The coefficient 3 is a direct elementary conservative bound, NOT fitted. Crucially this works even if p grows with N, although summing the O(sqrt N) errors naively over many p can still be too expensive for finite A.

The true zero density is \(1-6/\pi^2\), and the positive and negative Möbius sign densities are each \(3/\pi^2\). The last two facts use PNT. For each FIXED k,
\[
\lim_{N\to\infty}\frac1N\#\{n\le N:(n,k)=1,\ \mu(n)=\pm1\}
=\frac{\delta_k}{2}.
\tag{5}
\]
This is precisely the actual joint zero/sign distribution needed in the conditional parent/child ledger. We must NOT assign these densities to arbitrary selected subfamilies or individual growing square blocks without a theorem transferring them there.

## 3. Full multiplicative signed-correlation theorem: NOT zero!

Define \(C_k(N)=\sum_{n\le N}\mu(n)\mu(kn)\).
The exact identity (1) and density (3) give
\[
\boxed{C_k(N)=\mu(k)\delta_k N
+O\big((2^{\omega(k)}+2)\sqrt N\big).}\tag{6}
\]
The signs alternate with the parity of the actual factor depth, not with an assumed random process.

For every FIXED squarefree k, using the unconditional PNT for centered first moments, the ordinary raw Pearson correlation along the CORRECT MULTIPLICATIVE MATCHING has the explicit limit
\[
\boxed{
\lim_{N\to\infty}\mathrm{Corr}_{1\le n\le N}(\mu(n),\mu(kn))
=\mu(k)\sqrt{\prod_{p\mid k}\frac p{p+1}}.}\tag{7}
\]
In particular k=2 gives -sqrt(2/3)=-0.81649658..., k=3 gives -sqrt(3/4)=-0.86602540..., k=6 gives +1/sqrt2=+0.70710678..., and k=30 gives -sqrt(5/12)=-0.64549722....

Thus the near-zero adjacent-square-block Pearson/Spearman tests did NOT find weak intrinsic arithmetic dependence. The **correctly factor-matched** raw Pearson correlation is PROVABLY large and nonzero, and the appropriately masked correlation is **exactly** mu(k)=+-1. These statements are separate from additive-shift correlations mu(n)mu(n+h), which are not fixed by multiplicativity.

## 4. Why square-block time looks fractal: prime dilation becomes logarithmic translation

For a parent n in square block r and child kn in square block t,
\[
r=\lfloor\sqrt n\rfloor,\quad t=\lfloor\sqrt{kn}\rfloor,
\quad t\approx\sqrt k\,r,\quad
\log t-\log r\approx\tfrac12\log k.
\]
The arithmetic signed interaction kernel is
\[
H_k(r,t)=
\sum_{\substack{r^2\le n<(r+1)^2\\t^2\le kn<(t+1)^2}}
\mu(n)\mu(kn)
=\mu(k)\times\#\{\text{actual squarefree k-coprime parents in this cell}\}.
\tag{8}
\]
Every cell is sign-pure once conditioned on the actual factor dilation k. Its support lies on a multiplicative moving-lag ridge; taking fixed adjacent r-lags mixes these with nonrelated families and can conceal them.

Summing ALL child clocks t (including future, not-yet-reached child blocks) for all parent blocks below R gives exactly
\[
\sum_{r<R}\sum_t H_k(r,t)
=\mu(k)Z_k(R^2-1)
=\mu(k)\delta_k R^2+O\big((2^{\omega(k)}+2)R\big).
\tag{9}
\]
If BOTH parent and child square clocks must be <R, replace the parent upper endpoint by \(\lfloor(R^2-1)/k\rfloor\). This distinction is essential: future anticorrelated children cannot be spent as current cancellation.

## 5. Independently compiled numerical check on actual Möbius integers

Using a genuine linear Mobius sieve over **n<=15,000,000** and sampling parent n<=500,000:

| k | exact sum mu(n)mu(kn) | theoretical delta_k*N with sign | actual raw Pearson | proved limiting raw Pearson | failures of (1) |
|---:|---:|---:|---:|---:|---:|
|2|-202640|-202642.367|-0.816499285|-0.816496581|0|
|3|-227973|-227972.663|-0.866033953|-0.866025404|0|
|5|-253298|-253302.959|-0.912870333|-0.912870929|0|
|6|+151983|+151981.775|+0.707116260|+0.707106781|0|
|30|-126652|-126651.480|-0.645506279|-0.645497224|0|

Reproducible [mobius_prime_dilation_density.cpp](../experiments/PrimePopulationCutoff/mobius_prime_dilation_density.cpp), compiled with -Wall -Wextra -Werror and run as advertised. These finite checks are illustrative; (1)-(4) are ALL-SCALE theorems already proved above.

## 6. The correctly delimited finite A/C obstacle

The exact perfect anticorrelation applies to DIVISIBILITY-LINKED parent/child pairs across DIFFERENT arithmetic scales. The still-live odd Möbius packets at one endpoint x lie in the strict annulus x/2<m<=x; two distinct live packets m<n<2m can NEVER satisfy n=km for any integer k>=2. Thus the negative prime-multiplication ridges are not direct negative pair terms in the *simultaneous live-population* Gamma_x.

Their real role is to explain how historical births are paid by descendant deaths across square-block time. Any all-R finite-A proof must transport the exact sign/density through the full chronology and retain all incomplete prime-factor cubes, occurrence multiplicities, survivor masks and cross-family interactions. The endpoint Gamma_(R²-1)<=B R²K_R remains unproved. Even the universal-in-p O(sqrt N) density bound (4) is NOT by itself a bound for a sum over all primes and all ancestry layers.

This is the correct use of established Möbius densities: prove them on the ACTUAL prime-conditioned carrier, push them along the exact multiplicative square-clock, and NEVER replace signed descendants with random independent populations or average away the moving lag.


## 7. Explicit assumptions audit: a conditional finite-A/finite-C theorem, and why it is not a proof

There are NO probability, stationarity, ergodicity, sign-independence or unknown Möbius-density assumptions in the following identities. The prime-multiplicativity, squarefree density, and square-block packet clocks are unconditional. **ONE genuinely new quantitative sign bound remains UNPROVED.** Naming it does not prove it.

For R>=2 put x=R²-1 and the original historical envelope
\[
K_R=\max_{0\le y<R}\frac{(M(y)-1)^2}{y+1}\ge1.
\]
The inequality K_R>=1 uses y=0 and M(0)=0. Let
\[
\mathcal L_R=\{m\ {\rm odd}:x/2<m\le x,\ \mu(m)^2=1\},\
L_R=|\mathcal L_R|,\
\Gamma_R=\sum_{m<n,\;m,n\in\mathcal L_R}\mu(m)\mu(n).
\]
The unconditional dyadic packet identity gives
\[
M(x)=\sum_{m\in\mathcal L_R}\mu(m),\quad
M(x)^2=L_R+2\Gamma_R,\quad 0\le L_R\le R²/2.
\]

**The ONE missing quantitative assumption H(B):**
\[
\boxed{B\ge0,\quad \forall R\ge2:\ \Gamma_R\le B R²K_R,\
B\text{ independent of }R.}
\]
It is a uniform bound on the **actual occurrence-preserving signed pair interaction**, not a consequence of proven density estimates. Fixed prime-dilation perfect anticorrelation provides NO direct negative pair INSIDE the simultaneously live set: each pair m<n has n<2m, so no n=pm with integer p>=2 is possible.

**Rigorous conditional proof with constants.** If H(B), then
\[
\begin{aligned}
M(x)^2&=L_R+2\Gamma_R\le(1/2+2B)R²K_R,\\
(M(x)-1)^2&\le2M(x)^2+2
\le(4B+1)R²K_R+2
\le(4B+3/2)R²K_R,
\end{aligned}
\]
using K_R>=1, R>=2. Therefore the repo's square-root endpoint amplification statement is obtained with A=4B+3/2. Historical K_R gives \(|M(R-1)-1|\le\sqrt{R K_R}\), so
\[
|Q_R|=|2M(R-1)-M(x)|
\le2+2\sqrt{R K_R}+\sqrt{1/2+2B}\,R\sqrt{K_R}
\le\boxed{[4+\sqrt{1/2+2B}]\,R\sqrt{K_R}.}
\]
Finite C holds with \(C=4+\sqrt{1/2+2B}\). Existing repository closure proves that fixed endpoint amplification implies the standard Mertens energy bound; RH follows under its standard classical equivalence.

**THIS HYPOTHESIS IS NOT AN INDEPENDENT PROOF.** Conversely, finite A with \((M(x)-1)^2\le A R²K_R\) yields
\[
\Gamma_R=(M(x)^2-L_R)/2
\le (M(x)-1)^2+1
\le (A+1/4)R²K_R.
\]
Therefore existence of fixed B in H(B) is equivalent (up to constants) to original finite-A existence. Simply ASSUMING H(B) would assume the unsolved theorem.

**The honest independent proof target:** derive H(B) directly from the exact sign-preserving physical gcd classifier
\[
\Gamma_R=\sum_{\substack{a<b<2a,\ a,b\ {\rm odd}\\
(a,b)=1,\ \mu(a)^2\mu(b)^2=1}}
\mu(ab)\,
\#\{g:\ x/(2a)<g\le x/b,\ \mu(g)^2=1,\ (g,2ab)=1\}.
\]
The proven per-sector squarefree density only evaluates fixed a,b leading counts; it does NOT establish a uniform **SIGNED bilinear** estimate when a,b grow with R. The unproved estimate must preserve all positive/negative cofactor sectors simultaneously. One sufficient combinatorial proof would construct an actual occurrence-preserving injection pairing positive live-pair charges to distinct negative charges, leaving at most BR²K_R unmatched positives. If its existence is just asserted instead of being constructed, that is H(B) in disguise. Alternatively prove the equivalent signed bilinear inequality by a genuinely new finite arithmetic argument. No future prime descendant outside the endpoint may be used to pay a current positive charge.

In brief: known density facts are unconditional, all algebraic deductions are closed, and the only additional assumption needed for a *conditional* theorem is the RH-strength uniform signed reassembly bound. A genuinely unconditional proof MUST DERIVE that bound, not assume it.

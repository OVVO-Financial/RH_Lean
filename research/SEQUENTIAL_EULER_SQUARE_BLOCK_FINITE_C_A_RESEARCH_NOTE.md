# Sequential Euler Prime Insertion, Mobius Densities, Square-Block CRT, and the Finite-C / Finite-A Criterion for RH

**Standalone research note — 11 October 2026**  
**Status:** Research synthesis and conditional theorem. Exact identities and the finite-\(C\) implication are rigorous; cited asymptotic refinements are paper-level; **no universal finite \(C\), finite \(A\), or proof of RH is claimed**. This note uses only the actual Mobius function and genuine primes. In this note \(C\) is a constant for a bilinear floor kernel, not the original VF-mid constant.

## Abstract

Euler's reciprocal product generates the Mobius function by adding distinct prime factors sequentially. Each insertion changes sign parity, kills repeated-prime factors, and moves squarefree integers between adjacent factor-count layers. On a complete finite CRT wheel this operation determines exact sign and zero densities; its signed mean contracts as \(\prod_{p\le y}(1-1/p)^2\). The square-root cutoff \(X_R=R^2-1\) makes these operations especially explicit: no integer below \(X_R\) contains two prime factors \(\ge R\), and the quadratic tail of the historically truncated reciprocal zeta series vanishes exactly. Consequently the bilinear floor kernel
\[
Q_R=\sum_{1\le a,b<R}\mu(a)\mu(b)
 \left\lfloor\frac{R^2-1}{ab}\right\rfloor
\]
satisfies \(Q_R=2M(R-1)-M(R^2-1)\).

The **single open quantitative target** in this approach is a fixed finite \(C\) satisfying \(|Q_R|\le CR\sqrt{K_R}\) for every root \(R\), where \(K_R\) is the strict historical Mertens energy below \(R\). Such a bound gives a fixed finite square-root amplification \(A\), then a polylogarithmic square-root bound for \(M(x)\) by repeated descent, and hence RH. The paper also records the exact sequential prime-comb feedback, finite-wheel densities, square-block telescoping and CRT orthogonality, canonical \(U_R,V_R\) anti-alignment, reproducible numerics, and the crucial distinction between **phase-averaged independence** and a worst-case bound at the moving physical square endpoints.

## Postscript: what thorough Euler accounting must preserve (2026-10-11)

The follow-up [Twisted Euler two-wall finite-C ledger](TWISTED_EULER_TWO_WALL_FINITE_C_LEDGER.md) rewrites the **original** (Q_R=2M(R-1)-M(R^2-1)) as a single signed Euler population, proving an exact prime-toggle decomposition into a historical-crossing wall and an upper product-exit wall. This identifies a strict no-go for **one-edge-only** sign-reversing matchings: every prime in ((X/2,X]) is an isolated positive vertex of the twisted Boolean-cube adjacency graph; there are \(\asymp X/\log X\) such vertices, far above the target \(R\sqrt{K_R}\). The successful transport must connect different prime-owner families and preserve all signed boundary multiplicities. This is an obstruction to one particular local matching technique, **not** an obstruction to finite C. Its [independent audit](../scripts/euler_twisted_two_wall_audit.py) verifies the literal identities through \(R=317\).

## 1. Definitions, scope, and the single target

For \(n\ge1\), the Mobius function is \(\mu(1)=1\), \(\mu(n)=0\) if a prime square divides \(n\), and \(\mu(n)=(-1)^{\omega(n)}\) otherwise, where \(\omega(n)\) counts *distinct* prime factors. Set \(M(x)=\sum_{1\le n\le x}\mu(n)\), including \(M(0)=0\). For each integer \(R\ge2\), put
\[
X_R=R^2-1,\quad
K_R=\max_{0\le y<R}\frac{(M(y)-1)^2}{y+1},\quad
Q_R=\sum_{1\le a,b<R}\mu(a)\mu(b)
 \left\lfloor\frac{X_R}{ab}\right\rfloor .
\]
Define normalized actual quantities
\[
C_R=\frac{|Q_R|}{R\sqrt{K_R}},\quad
A_R=\frac{(M(X_R)-1)^2}{R^2K_R},\qquad
C_*=\sup_{R\ge2}C_R,\quad A_*=\sup_{R\ge2}A_R.
\]
The lower envelope includes \(y=0\), giving \(K_R\ge1\); since \(|M(y)-1|\le y+1\), also \(K_R\le R\).

**Target C:** prove \(\exists C\in\mathbb R,\ 0\le C<\infty,\ \forall R\ge2:\ |Q_R|\le CR\sqrt{K_R}\).

**Equivalent finite-amplification target A:** prove \(\exists A\in\mathbb R,\ 0\le A<\infty,\ \forall R\ge2:\ (M(X_R)-1)^2\le AR^2K_R\).

We do **not** demand \(C<1\), \(A<1\), a fixed upper bound on \(K_R\), random Mobius signs, or a specific magnitude for either constant. At \(R=2\), \(Q_2=3\), \(K_2=1\), \(M(3)=-1\), hence \(C_*\ge3/2\) and \(A_*\ge1\). A historical approximately 0.44 *large-root* necessary threshold, based on a Hurst argument, is separate and weaker than the universal \(A_*\ge1\); it is not needed below.

The finite-\(C\) property is a sufficient condition for RH. **The reverse implication from RH to this particular uniform finite-\(C\) statement is not established.** The criterion may be stronger than RH.

## 2. Euler's product gives the exact historical bilinear kernel

For \(\Re(s)>1\), or as formal Dirichlet series,
\[
F(s)=\frac1{\zeta(s)}=\prod_p(1-p^{-s})
     =\sum_{n\ge1}\mu(n)n^{-s}.
\]
Let \(Z_R(s)=\sum_{n<R}\mu(n)n^{-s}\) and \(T_R(s)=F(s)-Z_R(s)\). Since \(\zeta F=1\),
\[
\boxed{\zeta Z_R^2=F-2T_R+\zeta T_R^2.}\tag{2.1}
\]
Every coefficient in \(T_R\) has an integer index at least \(R\); every coefficient in \(\zeta T_R^2\) has index at least \(R^2\). Hence the latter contributes **exactly zero** to the cumulative coefficient sum through \(X_R=R^2-1\). The left side's cumulative coefficient sum is the *original* \(Q_R\), because
\[
\sum_{n\le X_R}\operatorname{coeff}_n(\zeta Z_R^2)
=\sum_{a,b<R}\mu(a)\mu(b)\#\{k\ge1:k ab\le X_R\}
=Q_R .
\]
The right side is \(M(X_R)-2(M(X_R)-M(R-1))\). Thus
\[
\boxed{Q_R=2M(R-1)-M(X_R).}\tag{2.2}
\]
This is a finite convolution identity closely related to the classical hyperbola method; it is **not a bound**. The factorization holds without analytic continuation of Euler's infinite product into the critical strip.

A second exact square-root observation is that \(n<X_R+1=R^2\) has **at most one** prime factor \(p\ge R\). If such a factor is present, \(n=pc\), \(c<R\), and \(\mu(pc)=-\mu(c)\). The high-prime Euler product consequently contributes only its constant and *linear* terms below \(R^2\).

## 3. Complete proof of finite C -> finite A -> RH

Rewrite (2.2):
\[
M(X_R)-1=2(M(R-1)-1)+1-Q_R .
\]
From the definition of \(K_R\),
\(|M(R-1)-1|\le\sqrt{R K_R}\).
If \(|Q_R|\le CR\sqrt{K_R}\), the triangle inequality yields
\[
\frac{|M(X_R)-1|}{R\sqrt{K_R}}
\le C+\frac2{\sqrt R}+\frac1{R\sqrt{K_R}}
\le C+\sqrt2+\tfrac12 .
\]
Therefore
\[
\boxed{A_*\le(C+\sqrt2+\tfrac12)^2<\infty.}\tag{3.1}
\]
Conversely, (2.2) gives \(C_*\le\sqrt{A_*}+\sqrt2+\tfrac12\). Thus finite \(C\) and finite \(A\) are equivalent **as existence statements**, though neither inequality provides new cancellation on its own.

Here is a self-contained square-root descent proving that **any** finite \(A\) suffices for RH. Define
\[
H(N)=\max_{0\le y<N}\frac{|M(y)-1|}{\sqrt{y+1}}=\sqrt{K_N}\ge1,
\qquad B=\sqrt A+2.
\]
For each \(x\ge3\), take \(R=\lfloor\sqrt{x+1}\rfloor\). Then \(R^2-1\le x<(R+1)^2-1\), and there are at most \(2R\) terms of magnitude at most one between \(R^2-1\) and \(x\). Consequently,
\[
|M(x)-1|\le\sqrt A\,R H(R)+2R,\qquad
\frac{|M(x)-1|}{\sqrt{x+1}}\le B H(R).
\]
Taking maxima over \(x<N\) (small \(x\) are covered by \(B\ge2\)) gives for \(N\ge4\)
\[
H(N)\le B H(\lfloor\sqrt N\rfloor).
\]
Iterate only \(\lceil\log_2\log_2 N\rceil\) times to reach \(N\le2\), where \(H(N)=1\). Therefore
\[
\boxed{H(N)\le B(\log_2N)^{\log_2 B}\quad(N\ge4),}\tag{3.2}
\]
and hence for some fixed \(d<\infty\),
\[
\boxed{M(x)=O(\sqrt x(\log x)^d)
       =O_\varepsilon(x^{1/2+\varepsilon})
       \quad\text{for every }\varepsilon>0.}\tag{3.3}
\]
Partial summation continues \(1/\zeta(s)=s\int_1^\infty M(t)t^{-s-1}\,dt\) holomorphically to \(\Re(s)>1/2\). Thus zeta has no zeros there; its functional equation reflects any nontrivial zero with real part below \(1/2\) to one above \(1/2\). Hence **RH follows**. The conditional fixed-\(A\) implication and Mertens-energy-to-RH implication are already Lean-checked in:
- RHLean/Proof/SquareRootAmplificationClosure.lean
- RHLean/Analysis/MertensEnergyRHForward.lean

This is a **conditional theorem**, not an unconditional RH proof. In particular, allowing \(A=\infty\) makes the endpoint inequality vacuous and destroys the fixed exponent \(d\).

## 4. Sequential insertion: the four physical effects of one prime

For a finite set \(P\) of primes define the *all-plus* finite Euler field
\[
f_P(n)=\prod_{p\in P}\left(
  1-2\mathbf1_{p\mid n}+\mathbf1_{p^2\mid n}
  \right).
\]
For a fresh prime \(q\notin P\), the new factor:
1. preserves the entry if \(q\nmid n\);
2. reverses its sign if \(q\mid n\) but \(q^2\nmid n\);
3. permanently kills it if \(q^2\mid n\);
4. raises its number of distinct prime factors by one on surviving \(q\)-multiples, moving contributions between **odd and even factor-depth layers**.

For \(F_P(X)=\sum_{n\le X}f_P(n)\), direct divisor reindexing proves the **exact one-prime insertion recurrence**
\[
\boxed{
F_{P\cup\{q\}}(X)=F_P(X)
-2F_P(\lfloor X/q\rfloor)
+F_P(\lfloor X/q^2\rfloor).
}\tag{4.1}
\]
There is no independence premise in this identity.

To retain factor depth, let \(E_j(P,X)\) count squarefree products at most \(X\) of exactly \(j\) distinct primes from \(P\), with \(E_0=1\). Then
\[
\boxed{
E_j(P\cup\{q\},X)=E_j(P,X)
+E_{j-1}(P,\lfloor X/q\rfloor)
}\tag{4.2}
\]
for \(j\ge1\). The completed Boolean cube for primes \(\{2,3,5\}\) is \(1-3+3-1=0\): \(1\), \(2,3,5\), \(6,10,15\), \(30\). At a cutoff below 30 the last negative face is missing. **Endpoints govern incomplete cubes; parity governs their signs.** Comparing only semiprimes to triple-prime products cannot control the whole alternating sum: the repository's exact omega-parity census shows the individual fixed-depth gaps can be far larger than \(M(X)\).

The user's prime-comb animation uses a *different but equivalent final-state convention*: the **prime-candidate** seed \(J_0(1)=1\) and \(J_0(n)=-1\) for \(n\ge2\); the first proper prime hit leaves that provisional value, later distinct-prime hits reverse it, and prime-square hits kill it. The distinction matters when stating a prime's update. RHLean/Proof/PrimeCombVisualizationFrames.lean and PrimeCombVisualizationRecurrence.lean formalize this physical state machine.

## 5. Euler densities are exact wheel laws; incomplete endpoints are the hard part

For a fixed finite prime set \(P\), sample \(n\) uniformly over one complete period \(L_P=\prod_{p\in P}p^2\). CRT makes **different selected prime coordinates independent under this specific finite uniform measure**, even though every sampled value is generated deterministically. A newly inserted prime \(p\) acts with exact fractions
\[
\Pr(\text{miss})=1-1/p,\quad
\Pr(\text{single prime hit})=1/p-1/p^2,\quad
\Pr(\text{square kill})=1/p^2.
\]
If \(d_+,d_-,d_0\) are the finite-wheel sign/zero fractions, the exact transition is
\[
\begin{aligned}
d_+'&=(1-1/p)d_++(1/p-1/p^2)d_-,\\
d_-'&=(1-1/p)d_-+(1/p-1/p^2)d_+,\\
d_0'&=d_0+(d_++d_-)/p^2.
\end{aligned}
\]
Consequently
\[
\boxed{d_+'-d_-'=(1-1/p)^2(d_+-d_-),\qquad
d_+'+d_-'=(1-1/p^2)(d_++d_-).}\tag{5.1}
\]
Starting with all \(+1\), a full period after primes \(P\) has
\[
d_+-d_-=\prod_{p\in P}(1-1/p)^2,\quad
d_++d_-=\prod_{p\in P}(1-1/p^2).
\]
As primes are added, the support tends to \(6/\pi^2\) and the signed mean to zero. The **natural densities of actual Mobius values** are therefore
\[
\boxed{\Pr(\mu=+1)=\Pr(\mu=-1)=3/\pi^2\approx30.3964\%,\quad
\Pr(\mu=0)=1-6/\pi^2\approx39.2073\%.}
\]
These are global natural densities and exact complete-wheel transition laws, not pointwise bounds on a truncated signed prefix.

At the actual square endpoint the **entire squarefree support is exactly historical**:
\[
\boxed{\#\{n\le X_R:\mu(n)^2=1\}
 =\sum_{d<R}\mu(d)\lfloor X_R/d^2\rfloor.}\tag{5.2}
\]
The zero count is \(X_R\) minus this expression. Walfisz's unconditional squarefree-count estimate furthermore implies each sufficiently large *individual* square block contains \((6/\pi^2)(2R+1)+o(R)\) squarefree integers. **This still does not control their plus-minus difference.** A density argument that omits the magnitude and sign of its truncated endpoint error cannot prove finite \(C\).

## 6. The literal post-root prime-candidate feedback

Set \(X=X_R\). After all primes \(<R\) have acted on the candidate seed, write \(J_R\) for its **signed running field total**, not for a random model. For each actual later prime \(R\le p\le X\), put \(k_p=\lfloor X/p\rfloor<R\). Because \(p^2>X\), there is no new square kill; the candidate prime seat \(p\) is already \(-1\), and only proper multiples \(cp\), \(2\le c\le k_p\), change. Their lower cofactors have already been reconstructed. The resulting exact physical increment is
\[
\boxed{\Delta_p=2(1-M(k_p))=-2\sum_{c=2}^{k_p}\mu(c).}\tag{6.1}
\]
If \(p>X/2\), then \(k_p=1\) and \(\Delta_p=0\). With \(P_R^{\rm active}=\{p\text{ prime}:R\le p\le X/2\}\),
\[
\boxed{M(X)=J_R+\sum_{p\in P_R^{\rm active}}\Delta_p.}\tag{6.2}
\]
The strict historical signal is \(b(k)=1-M(k)\). Exact reciprocal-quotient bands have actual prime multiplicities
\[
h_R(k)=\pi(\lfloor X/k\rfloor)-\pi(\lfloor X/(k+1)\rfloor),\qquad2\le k<R,
\]
and
\[
\boxed{M(X)=J_R+2\sum_{k=2}^{R-1}b(k)h_R(k).}\tag{6.3}
\]
This preserves all actual prime arrivals and all occurrence multiplicities.

The elementary finite harmonic identity
\[
\boxed{\sum_{k=2}^N\frac{1-M(k)}{k(k+1)}
=1-\sum_{n=1}^N\frac{\mu(n)}n+\frac{M(N)-1}{N+1}}\tag{6.4}
\]
implies, using classical PNT consequences, the infinite sum equals 1. For **fixed** \(k\), PNT gives
\[
\frac{h_R(k)}{\#P_R^{\rm active}}\longrightarrow\frac2{k(k+1)}.
\]
The research calculation, with a weighted-tail justification using quantitative PNT/Brun-Titchmarsh, consequently yields the **paper-level** mean update
\[
\boxed{\frac1{\#P_R^{\rm active}}\sum_{p\in P_R^{\rm active}}\Delta_p\longrightarrow4.}\tag{6.5}
\]
This is a deterministic *frequency law*, not a uniform \(C\) estimate. Since \(M(k)\le1\) for all \(1\le k\le94\) (first exception \(M(95)=2\)), **every** active prime \(p>X/95\) has \(\Delta_p\ge0\). In the \(R\to\infty\) limit this provably nonnegative terminal range represents a fraction \(1-2/95\approx97.89\%\) of the active prime count. The final large-prime increments are thus largely **same-sign corrections of a large pre-existing field**, not independently canceling random jumps.

An unconditional diagonal energy estimate follows without an explicit small numerical prime-reciprocal constant. The prime reciprocal theorem implies
\(\Lambda:=\sup_{R\ge2}\sum_{R\le p<R^2}1/p<\infty\).
Because \(k_p<R\), \((M(k_p)-1)^2\le(k_p+1)K_R\). Hence
\[
\boxed{\sum_{p\in P_R^{\rm active}}\Delta_p^2
\le 4K_R\left(X\sum_{R\le p<R^2}\frac1p+\#P_R^{\rm active}\right)
\le(4\Lambda+2)R^2K_R.}\tag{6.6}
\]
The companion Euler note reports the sharper explicit \(\Lambda\le5/6\), giving \(16R^2K_R/3\); **verify the all-root explicit reciprocal-prime certificate independently before relying on this numerical constant**. Finiteness of the diagonal bound follows already from the classical reciprocal-prime theorem.

The diagonal \(\sum_p\Delta_p^2\) being controlled does **not** imply control of \((\sum_p\Delta_p)^2\), much less the **combined** cancellation with \(J_R\). That signed cross-interaction is the actual difficulty.

## 7. A separate exact canonical ancestry decomposition and its limit

For each squarefree \(n\ge2\), write \(n=qc\) with \(q=P^+(n)\) its largest prime. The canonical two-channel partition classifies \(q>c\) (prime-root orientation) and \(q<c\) (smooth ancestry). Squarefreeness excludes equality. Define
\[
U_R=\sum_{\substack{2\le n\le X_R\\\mu(n)\ne0,\ q>c}}\mu(n),\qquad
V_R=\sum_{\substack{2\le n\le X_R\\\mu(n)\ne0,\ q<c}}\mu(n).
\]
Then
\[
\boxed{U_R+V_R=M(X_R)-1.}\tag{7.1}
\]
**Do not confuse** this orientation split with the *fixed prime-cutoff* smooth/high-prime split in section 6. Both reconstruct the same sum but their pieces differ.

Where \(U_R^2+V_R^2>0\), define the normalized signed interaction
\[
\rho_R=\frac{2U_RV_R}{U_R^2+V_R^2},\quad
1+\rho_R=\frac{(U_R+V_R)^2}{U_R^2+V_R^2}.
\]
The paper-level Selberg-Delange / PNT comparison reported in the Euler synthesis gives
\[
U_R\sim\frac{X_R}{(\log X_R)^2},\qquad
V_R\sim-\frac{X_R}{(\log X_R)^2},
\quad\text{hence}\quad\rho_R\to-1.
\]
One route begins with the established signed \(\omega\)-weighted sum
\(\sum_{n\le X}\mu(n)\omega(n)\sim X/(\log X)^2\) and compares it to \(U_R\), with the remaining prime/cofactor sector bounded by quantitative PNT. This comparison is not a newly compiled Lean theorem and should receive an independent analytic check before publication.

**The limit does not establish finite \(A\).** Exactly,
\[
\boxed{A_R=\frac{U_R^2+V_R^2}{R^2K_R}(1+\rho_R).}\tag{7.2}
\]
The first factor grows, while \(1+\rho_R\to0\). A sufficient rate (given the displayed population asymptotic) is
\[
1+\rho_R=O\left(\frac{K_R(\log X_R)^4}{R^2}\right).
\]
Asserting that rate without an independent argument is **just another form of the open finite-\(A\) statement**. Nonnegativity of \((U_R+V_R)^2\) is automatic; some endpoints exhibit exact zero, so strict positivity is not required.

## 8. Square-block partitions: exact CRT orthogonality, not assumed randomness

The physical square block is \(I_R=[R^2,(R+1)^2)\), of length \(2R+1\). For a **fixed** positive divisor \(d\), define its multiple-count discrepancy
\[
\epsilon_R(d)=\#\{n\in I_R:d\mid n\}-\frac{2R+1}{d}.
\]
Floor arithmetic gives
\[
\boxed{
\epsilon_R(d)
=\left\{\frac{R^2-1}{d}\right\}
-\left\{\frac{(R+1)^2-1}{d}\right\}.
}\tag{8.1}
\]
Therefore \(|\epsilon_R(d)|<1\), it is periodic in \(R\bmod d\), and **every arbitrary run telescopes**:
\[
\boxed{\left|\sum_{R=A}^{B-1}\epsilon_R(d)\right|<1.}\tag{8.2}
\]
A fixed divisor's square-block counting error cannot drift indefinitely.

For coprime \(d,e\), the CRT maps uniform \(R\bmod de\) to independent coordinates \(R\bmod d\) and \(R\bmod e\). Each \(\epsilon\) has mean zero over its coordinate, so
\[
\boxed{\frac1{de}\sum_{R=0}^{de-1}\epsilon_R(d)\epsilon_R(e)=0
\quad(\gcd(d,e)=1).}\tag{8.3}
\]
This is exact **finite-ensemble orthogonality** and genuine independence of those two coordinate functions **if the root phase is chosen uniformly over the joint period**. It is *not* a statement that the actual deterministic sequence of physical blocks comprises independent draws.

Dependent same-prime phases can instead cancel **algebraically** through Euler:
\[
\epsilon_R(2)=\frac{(-1)^R}{2},\quad
\epsilon_R(4)=\frac{3(-1)^R}{4},\quad
\boxed{-2\epsilon_R(2)+\epsilon_R(4)
=-\frac{(-1)^R}{4}.}\tag{8.4}
\]
The 2/4 errors are perfectly correlated, yet Euler's correctly signed combination reduces their magnitude.

**Two essential scope cautions:**

1. Quadratic sampling is not uniform sampling of wheel residues: for example \(R^2\bmod3\) visits only 0 and 1, never 2. CRT independence across **coprime root coordinates** therefore does not imply uniformity of each squared coordinate, nor independence of successive physical blocks.
2. The natural full wheel period \(L_P=\prod_{p\in P}p^2\) quickly exceeds the physical block's length \(2R+1\). For \(R=10{,}000\), already \(L_{\{2,3,5,7\}}=44{,}100>20{,}001\). The Lean module PhysicalSquareCRTPeriodNoGo.lean proves that the complete-period core of certain physical CRT block partitions is empty once this threshold is crossed. **Averaging a full wheel is then insufficient to bound the incomplete physical boundary.**

RHLean/Analysis/SquareWheelQuadraticSampling.lean proves exact square-endpoint quadratic Fourier phase identities and annihilation of completed reduced-conductor periods. FinitePrimeTMixing.lean proves local nonconstant Walsh-mode contractions for selected finite-prime coordinates. The latter module explicitly does *not* infer that the actual Mobius process satisfies the same distribution; rough-prime and square-boundary transport remain separate obligations.

These facts support the suggested square-clock mechanism but **do not yet give pointwise finite \(C\)**. All signed errors from moving divisors, incomplete CRT periods, and simultaneous prime insertions must be controlled together.

## 9. Finite arithmetic census (not a global bound)

**Follow-up spectral experiment (2026-10-11).** The [staggered prime-wave / CRT / Euler / Perron / finite-C report](PRIME_PERRON_STAGGERED_PHASE_FINITE_C_EXPERIMENT_2026_10_11.md), with [reproducible source and workflow](../experiments/prime_phase_finite_c/README.md), tests the physical square-root phases against ordinary CRT phase sampling. Exact ten-prime sine maxima drop from +8.763 to +6.622, while the worst absolute maximum only drops from 8.763 to 8.451. Local Euler square-root phases show 67.27% zero states versus 38.77% for uniform integer phases; however the exhaustive four-prime signed Fourier **prefix energy** improves only 2.74% and the schematic wave amplitudes correlate essentially zero with genuine \(C_R\) through \(R=6000\). The original user's staggered R script is archived. This is a useful *negative* test: nonalignment and local density alone do not provide the signed all-root \(Q_R\) bound. The genuine cofactor-weighted nonzero conductor response remains the open component.


The following exact-root summaries use the strict \(K_R\) and the actual Mobius sequence. Roots through \(1{,}000\), the double floor kernel for smaller roots, and the prime-comb correction formula were independently recomputed for this synthesis. The larger rows are from the reproducible repository censuses.

| \(R\) | \(M(R^2-1)\) | \(Q_R\) | \(K_R\) | \(C_R\) | \(A_R\) |
|---:|---:|---:|---:|---:|---:|
| 2 | -1 | +3 | 1 | 1.500000 | 1.000000 |
| 56 | +6 | -10 | 1.5 | 0.145803 | 0.005315 |
| 317 | -28 | +22 | 1.5 | 0.056665 | 0.005579 |
| 5,561 | -2,544 | +2,554 | 1.5 | 0.374992 | 0.139630 |
| 10,000 | +1,928 | -1,974 | 1.5 | 0.161176 | 0.024756 |
| 20,000 | -1,599 | +1,651 | 1.5 | 0.067402 | 0.004267 |

The prime-candidate reconstruction exhibits **enormous signed feedback**:

| \(R\) | \(J_R\): after primes \(<R\) | Sum of actual later-prime updates | Final \(M(X_R)\) |
|---:|---:|---:|---:|
| 56 | -946 | +952 | +6 |
| 317 | -20,940 | +20,912 | -28 |
| 1,000 | -169,582 | +169,794 | +212 |
| 5,561 | -4,073,166 | +4,070,622 | -2,544 |
| 10,000 | -12,230,578 | +12,232,506 | +1,928 |
| 20,000 | -45,093,849 | +45,092,250 | -1,599 |

At \(R=10{,}000\), the number of active later primes is \(2{,}999{,}905\); \(2{,}982{,}696\) increments are positive and \(9{,}357\) negative. The dominant cancellation is **between the initially negative candidate field and its mostly positive actual prime corrections**; describing those increments as independent balanced random signs is inaccurate.

A second-order analytic calculation in research/EULER_PRIME_COMB_FEEDBACK_FINITE_C.md obtains the paper-level asymptotics, with \(N_R=\#P_R^{\rm active}\), \(X=X_R\), \(L=\log X\),
\[
J_R+4N_R\sim-2(1-\log2)\frac{X}{L^2},\qquad
\sum_p(\Delta_p-4)\sim+2(1-\log2)\frac{X}{L^2}.
\]
These opposite components are individually asymptotically larger than \(R\sqrt{K_R}\), since \(K_R\le R\). **They cannot be bounded separately at the required scale**; the simultaneous signed compensation is essential. Treat the displayed second-order derivation as paper-level research until separately reviewed and formalized.

No finite collection of these values, however large, implies \(\sup_R C_R<\infty\).

## 10. What is proved, what is not, and the next noncircular step

**Established:**
- Euler's finite-prime local parity/zero/depth rules and exact insertion recurrences (4.1), (4.2).
- Complete CRT wheel densities and their factorwise signed-mean contraction (5.1).
- Exact historical squarefree support (5.2).
- The literal post-root candidate increment (6.1), quotient-band recurrence (6.3), and finite harmonic identity (6.4).
- The prime-update diagonal bound with **some finite universal numerical factor**, from the classical reciprocal-prime theorem (6.6).
- Exact square-block telescoping, coprime CRT phase orthogonality and same-prime algebraic compensation (8.1)-(8.4).
- The algebraic equivalence of finite-\(C\) and finite-\(A\), and the **Lean-checked conditional implication finite \(A\) -> RH**.

**Paper-level / separate audit:** Selberg-Delange comparison for \(U_R,V_R\); the PNT/Brun-Titchmarsh mean-\(+4\) update law; the secondary \(X/\log^2X\) centered terms; explicit best constants; large-root computational tables. They are not newly Lean-compiled by this note.

**Not established:** the physical, unweighted, all-root, signed bound
\[
\boxed{
\exists C<\infty\quad\forall R\ge2:
\left|\sum_{a,b<R}\mu(a)\mu(b)
       \left\lfloor\frac{R^2-1}{ab}\right\rfloor\right|
       \le CR\sqrt{K_R}.}\tag{10.1}
\]
Equivalently the unproved quantitative \(U_R,V_R\) cross-cancellation is
\[
(U_R^2+V_R^2)+2U_RV_R\le AR^2K_R
\quad\text{for one fixed finite }A.
\]

**Concrete research program, without another disguised equivalent assumption:**

1. **Fix the physical carrier and preserve factor depth.** Use the actual prime-candidate state \(J_R\), the exact \(\Delta_p\), factor-depth \(\omega\), and genuine square-block endpoints. Keep first-hit, sign reversal, zero deletion, and historical cofactor labels distinct. Do not invent a random Mobius model.
2. **Write the true signed interaction before norming.** Expand \(Q_R=2M(R-1)-J_R-\sum_p\Delta_p\) and its square *with* the \(J_R\)-prime and prime-prime cross terms. The diagonal is already bounded; the coupled cross term is not. An equality alone is not progress.
3. **Exploit the two different cancellation laws correctly.** Across coprime prime coordinates use complete-period CRT orthogonality and exact square-phase Fourier responses. Within shared-prime coordinates use Euler's signed factor layers, including \((p,p^2)\)-dependence and zero hits. Prove how much of both laws survives on the *actual truncated square-clock carrier*, with a bound uniform as the wheel grows.
4. **Control incomplete periods rather than assuming independence.** Quantify the nonzero reduced-conductor square phases and the physical CRT boundary (PhysicalSquareCRTPeriodNoGo and SquareWheelZeroModeElimination show why naive full-wheel averaging is insufficient). The historical \(K_R\) must appear in a genuine derived inequality, not as an assumed RH-strength premise.
5. **Falsify candidates at finite scale before formalizing.** Check every claimed local inequality against the original \(Q_R\), not merely a normed proxy; run first-bad/large-root scans, vary included prime layers, track zero/odd/even depth and actual cross terms, and keep explicit counterexamples.
6. **Complete a Lean theorem only when the independent arithmetic inequality exists.** Derive (10.1) from already justified facts, instantiate SquareRootMertensEndpointAmplificationStatement via (2.2), and invoke the existing SquareRootAmplificationClosure.lean and MertensEnergyRHForward.lean consumers. New equivalent definitions, randomness assumptions, unproved all-scale mixing, and fitted finite constants do not close the gap.

An acceptable new theorem must quantitatively control a genuine arithmetic component using independently proven incidence/phase information **before** it is reassembled into \(Q_R\). Proving only an exact reassembly, complete-period average, mean-square over artificial frequencies, or asymptotic \(\rho_R\to-1\) does not meet this standard.

## 11. Repository starting points and reproducibility

**Primary mathematical notes**
- [Euler product -> finite C -> finite A](EULER_PRODUCT_SQUARE_ROOT_FINITE_C_A.md).
- [Sequential prime-comb feedback, harmonic mean-four, and second-order correction](EULER_PRIME_COMB_FEEDBACK_FINITE_C.md).
- [Factor-count parity tests and known failures of fixed-depth pairing](OMEGA_PARITY_ORIENTATION.md).
- [Prime-wheel animation and its exact terminal ledger](../export_prime_wheel/README.md).

**Existing formal results**
- RHLean/Proof/PrimeCombVisualizationFrames.lean
- RHLean/Proof/PrimeCombVisualizationRecurrence.lean
- RHLean/Proof/PrimeCombReciprocalBandCancellation.lean
- RHLean/Proof/SquareRootLegalAncestryGramReduction.lean
- RHLean/Proof/SquareRootMertensEndpointAmplification.lean
- RHLean/Proof/SquareRootAmplificationClosure.lean
- RHLean/Analysis/MertensEnergyRHForward.lean
- RHLean/Analysis/SquareWheelQuadraticSampling.lean
- RHLean/Analysis/SquareWheelZeroModeElimination.lean
- RHLean/Analysis/FinitePrimeTMixing.lean
- RHLean/Analysis/PhysicalSquareCRTTransfer.lean
- RHLean/Analysis/PhysicalSquareCRTPeriodNoGo.lean

**Independent audit entry points**

~~~bash
python3 scripts/euler_finite_ca_cutoff_audit.py 2 3 5 10 56 317
python3 scripts/euler_prime_comb_terminal_probe.py --roots 56 317 1000 --limit 1000000
g++ -O3 -std=c++17 experiments/euler_prime_comb_full_field_audit.cpp -o /tmp/euler_audit
/tmp/euler_audit 10000
/tmp/euler_audit 20000
~~~

The C++ audit computes both the candidate field and the actual final Mobius field separately and checks equality against accumulated genuine prime insertions. These finite audits do not certify a universal bound.

**Classical references**
- [NIST DLMF, Mobius partial sums and reciprocal identities](https://dlmf.nist.gov/27.11).
- [NIST DLMF, Euler products](https://dlmf.nist.gov/27.4).
- [Alladi and Johnson, prime-factor weighted Mobius sums](https://people.clas.ufl.edu/alladik/files/alladi-johnson-l.pdf).
- [Walfisz squarefree-count estimate: mathematical background](https://www.sciencedirect.com/science/article/abs/pii/S0022314X2300152X).

## Final research contract

**Euler prime insertion is deterministic; Mobius densities and factor parity emerge from that insertion; square endpoints provide exact divisor telescoping and coprime CRT phase orthogonality; the missing quantitative theorem concerns the simultaneous, physical, growing-wheel signed remainder.** A single uniform finite \(C\), of any magnitude, would give finite \(A\), a fixed-power logarithmic square-root Mertens bound, and RH. Such a \(C\) has **not** been proved.

Keep the goal fixed: bound the original \(Q_R\), using the actual Euler operators and historical \(K_R\), without assuming the needed rate of cancellation.

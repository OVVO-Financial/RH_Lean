# Euler product and the finite-C / finite-A square-root target

**Status (2026-10-11):** Exact finite Euler identities and historical weighted-energy estimates are established mathematically; the universal unweighted bound defining finite C remains **open**. This is a research proof map, not a claim that RH has been proved.

**Fixed objective.** Prove one real constant C < infinity for all integers R >= 2:

\[
\boxed{\left|\sum_{1\le a,b<R}\mu(a)\mu(b)
  \left\lfloor\frac{R^2-1}{ab}\right\rfloor\right|
  \le C R\sqrt{K_R}.}
\]

No other criterion, small-constant condition, stochastic assumption, or new prime model is substituted for this objective.

## 1. The exact C and A quantities

Put X = R^2 - 1 and let M(x) = \sum_{n\le x}\mu(n), with M(0)=0. Define the **strict historical** budget

\[
K_R=\max_{0\le y<R}\frac{(M(y)-1)^2}{y+1}\ge1,
\quad
Q_R=\sum_{a,b<R}\mu(a)\mu(b)\left\lfloor\frac{X}{ab}\right\rfloor.
\]

Here the bilinear sum has 1 <= a,b < R; all Mobius coefficients are *historical*.

\[
C_R=\frac{|Q_R|}{R\sqrt{K_R}},\quad C_*=\sup_{R\ge2}C_R,\qquad
A_R=\frac{(M(X)-1)^2}{R^2K_R},\quad A_*=\sup_{R\ge2}A_R.
\]

The exact arithmetic identity is

\[
\boxed{Q_R=2M(R-1)-M(X).} \tag{1}
\]

Consequently

\[
M(X)-1=1+2(M(R-1)-1)-Q_R.
\]

Since |M(R-1)-1| <= \sqrt{R K_R}, R >= 2, and K_R >= 1,

\[
\frac{|M(X)-1|}{R\sqrt{K_R}}
 \le C_R+\frac{2}{\sqrt R}+\frac{1}{R\sqrt{K_R}}
 \le C_R+\sqrt2+\frac12.
\]

Thus any universal bound C_R <= C proves

\[
\boxed{A_*\le\left(C+\sqrt2+\frac12\right)^2<\infty.} \tag{2}
\]

Conversely the same identity gives

\[
\boxed{C_R\le\sqrt{A_R}+\sqrt2+\tfrac12.} \tag{3}
\]

Finite C and finite A are therefore equivalent **as existence statements**, not two independent estimates. The finite-A premise implies the Mertens energy criterion and RH by the existing Lean consumer in RHLean/Proof/SquareRootAmplificationClosure.lean. This conditional implication is proved; its premise has not been established.

The first root forces C_* >= 3/2: Q_2=3, K_2=1. It also forces A_* >= 1. We require **any finite C**, not C < 1.

## 2. Euler's product yields the exact R-to-R^2 arithmetic

For Re(s)>1, Euler's product is

\[
F(s)=\frac1{\zeta(s)}=\prod_p(1-p^{-s})
     =\sum_{n\ge1}\mu(n)n^{-s}.
\]

The following calculations may equally be read as **formal Dirichlet-series coefficient identities**; they make no unsupported analytic continuation claim.

Define a historical truncation and its tail:

\[
Z_R(s)=\sum_{n<R}\mu(n)n^{-s},\qquad T_R(s)=F(s)-Z_R(s).
\]

Since \zeta(s)F(s)=1, formal multiplication gives

\[
\boxed{\zeta(s)Z_R(s)^2
       =F(s)-2T_R(s)+\zeta(s)T_R(s)^2.} \tag{4}
\]

Every nonzero coefficient in T_R has index >= R. Accordingly, every term in \zeta T_R^2 has index >= R^2. **The square-root cutoff kills that entire quadratic tail exactly**, without a probabilistic cancellation hypothesis.

Take the **sum of coefficients with integer index n <= X=R^2-1** on both sides of (4). On the left,

\[
\sum_{n\le X}[n^{-s}](\zeta Z_R^2)
=\sum_{a,b<R}\mu(a)\mu(b)\#\{k\ge1:k ab\le X\}
=Q_R.
\]

On the right, the squared tail contributes zero and the other terms give M(X)-2(M(X)-M(R-1)). This proves identity (1).

**Euler-to-C-to-A chain (with exact scopes):**

\[
\boxed{
\begin{gathered}
\text{Euler product / formal inversion}
\ \Longrightarrow\
\text{exact coefficient identity }Q_R=2M(R-1)-M(R^2-1),\\
\text{OPEN: }\sup_R |Q_R|/(R\sqrt{K_R})=C_*<\infty\\
\Longrightarrow\ A_*<\infty
\Longrightarrow\ M(x)=O_\varepsilon(x^{1/2+\varepsilon})
\Longrightarrow\mathrm{RH}.
\end{gathered}}
\]

The first arrow is an identity, **not** a uniform estimate for Q_R.

## 3. The finite Euler product separates large-prime descendants at the square root

Let

\[
P_{<R}(s)=\prod_{p<R}(1-p^{-s}),\qquad
H_R(s)=1-\sum_{\substack{R\le p<R^2\\p\ \mathrm{prime}}}p^{-s}.
\]

An integer n < R^2 can contain **at most one prime factor >= R**. If it contains one, removing it leaves a cofactor c < R, and \mu(pc)=-\mu(c). Therefore the following is an exact coefficient identity:

\[
\boxed{[\ n<R^2\ ]\,P_{<R}(s)H_R(s)
       =\sum_{n<R^2}\mu(n)n^{-s}.} \tag{5}
\]

The brackets mean truncation by **integer index**, not convergence or evaluation of an infinite product outside Re(s)>1.

Define the complete low-prime smooth signed mass and the historical large-prime response:

\[
S_R=\sum_{\substack{1\le n\le X\\P^+(n)<R}}\mu(n),
\qquad
B_R=\sum_{\substack{R\le p\le X\\p\ \mathrm{prime}}}
               M\left(\left\lfloor\frac Xp\right\rfloor\right),
\]
where P^+(1)=1 and P^+(n) is the largest prime factor. Formula (5) gives

\[
\boxed{M(X)=S_R-B_R,\qquad
       Q_R=2M(R-1)-S_R+B_R.} \tag{6}
\]

Every historical cofactor argument floor(X/p) in B_R is **strictly below R**. The two large raw sums must be combined **with their signs intact** before bounding Q_R.

This high-prime/smooth split is **not** the repository's canonical largest-prime root-versus-smooth split U_R,V_R. Both splits reconstruct M(X), but they have different individual coordinates. The existing legal-ancestry Lean identity is U_R+V_R=M(X)-1.

## 4. What finite Euler energy already proves unconditionally

For the finite Dirichlet polynomial H_R, orthogonality of the different frequencies log p gives

\[
\lim_{T\to\infty}\frac1{2T}\int_{-T}^{T}
       |H_R(\tfrac12+it)|^2\,dt
     =1+\sum_{R\le p<R^2}\frac1p. \tag{7}
\]

A finite-prime check plus an explicit reciprocal-prime estimate, described in Finite_A_Mertens_Amplification_Revised (Section 11, paper-level), yields for all R >= 2

\[
\sum_{R\le p<R^2}\frac1p\le\frac56;
\quad\text{hence (7) is at most }\frac{11}{6}.
\]

The left side tends to 1+log 2 as R grows. The uniform bound is for a **frequency mean square**, not for every frequency nor the unweighted coefficient sum.

There is a second exact Euler contraction. For arbitrary coefficients a_c on c < R, adjoin one large prime p >= R, with new coefficient -a_c at n=pc <=X. These descendants are all distinct. In reciprocal coefficient energy,

\[
\boxed{
\sum_{\substack{pc\le X\\p\ge R\ \mathrm{prime},\,c<R}}
      \frac{|a_c|^2}{pc}
   =\sum_{c<R}\frac{|a_c|^2}{c}
       \sum_{R\le p\le X/c}\frac1p
   \le\frac56\sum_{c<R}\frac{|a_c|^2}{c}.} \tag{8}
\]

The squared energy of historical coordinates plus distinct high-prime descendants is thus <= 11/6 times the historical weighted energy. For a_c=\mu(c), squarefree density and the reciprocal-prime theorem further give the paper-level asymptotic

\[
\frac{\text{descendant weighted energy}}{\text{historical weighted energy}}
 \longrightarrow 2\log2-1\approx0.38629436.
\]

These results are **genuine finite-amplification facts inside Euler's product**, but their constants 5/6 and 11/6 are **not** C or A. They act on reciprocal weights and frequency averages, not the sharp unweighted summation that defines Q_R.

## 5. The exact obstacle: the Euler *signed projection*, not a missing prime factor

At R=10,000 the finite Euler coefficient split in (6) gives

\[
S_R=-354099,\quad -B_R=356027,\quad
M(X)=1928,\quad M(R-1)=-23,\quad Q_R=-1974.
\]

The signed low/high cancellation is indispensable. A bound on the high-prime operator's reciprocal-energy norm alone would not bound either raw mass: for a general coefficient vector supported at c=1, the high-prime raw sum has magnitude pi(X)-pi(R-1), about R^2/log(R^2), even though its reciprocal-energy norm obeys (8). This is an **operator counterexample**, not a counterexample to the actual Mobius finite-C conjecture.

Moreover, a mean-square bound for H_R(1/2+it) cannot bound its value at every individual t: already at t=0, the absolute value is of order R/log R, despite (7) remaining < 2.

Thus the unproved statement, kept in its original physical currency, is

\[
\boxed{
\forall R\ge2:\quad
|2M(R-1)-S_R+B_R|
\le C R\sqrt{K_R}
\quad\text{for one finite }C.} \tag{9}
\]

Equation (9) is equation (1) written through the **actual Euler coefficient split**, not an independently proved bound. A future proof must obtain a quantitative **signed** compensation of S_R with B_R at each moving square endpoint. It cannot take absolute values of the two terms separately, infer pointwise bounds from (7), or assume independence from the CRT.

The priority is exactly C, hence A; no weaker asymptotic anti-alignment, constructed floor-Li staircase, or separate stronger Mobius hypothesis is accepted as closure.

## 6. Reproducible finite arithmetic audit

Run the standard-library checker:

~~~bash
python3 scripts/euler_finite_ca_cutoff_audit.py 2 3 5 10 56 317
~~~

For each root it independently computes actual Mobius values, the low/high Euler signed masses, the **original double floor sum**, the historical K, the observed C and A ratios, and the reciprocal-prime/descendant energy.

Examples from the exact audit (the ratios are rounded):

| R | S_R | -B_R | M(X) | Q_R | C_R | A_R |
|---:|---:|---:|---:|---:|---:|---:|
| 2 | 1 | -2 | -1 | 3 | 1.500000 | 1.000000 |
| 56 | -41 | 47 | 6 | -10 | 0.145803 | 0.005315 |
| 317 | -918 | 890 | -28 | 22 | 0.056665 | 0.005579 |
| 5561 | -126917 | 124373 | -2544 | 2554 | 0.374992 | 0.139630 |
| 10000 | -354099 | 356027 | 1928 | -1974 | 0.161176 | 0.024756 |

The attached checker tests roots through 317 by default (larger roots require more time and memory); the 5561/10000 entries come from the earlier independent finite Euler/Mobius censuses. No finite census establishes a universal constant.

## 7. Existing repository proof consumers and provenance

- RHLean/Proof/SquareRootMertensEndpointAmplification.lean: open scalar amplification premise and proved equivalence to signed legal-ancestry anti-alignment.
- RHLean/Proof/SquareRootLegalAncestryGramReduction.lean: U_R+V_R=M(R^2-1)-1 (different partition from S_R-B_R).
- RHLean/Proof/SquareRootAmplificationClosure.lean: conditional fixed-A -> global Mertens energy.
- RHLean/Analysis/MertensEnergyRHForward.lean: Mertens energy -> RH.
- RHLean/Arithmetic/PrimorialTruncatedWheelBoundary.lean: exact truncated finite Euler cubes and prime insertion.
- RHLean/Proof/CanonicalRoughTruncatedWheelDefectTelescope.lean: exact signed Euler-wheel shell/telescope.
- RHLean/Proof/CanonicalRoughQuantitativeContraction.lean: reciprocal defect-ledger contraction and explicit need for an unweighted Abel return.

**Proof status:** Equations (1), (4)-(8) are finite algebraic/analytic derivations in this research note, not claimed as newly kernel-compiled Lean theorems. The existing amplification-to-RH bridge is already formalized conditionally. **Finite C and finite A remain open.**

## References

- Riemann zeta Euler product and Dirichlet coefficients: https://dlmf.nist.gov/27.4
- Meromorphic continuation of zeta (distinct from convergence of the prime Euler product): https://dlmf.nist.gov/25.2
- Rosser and Schoenfeld (1962), explicit prime reciprocal estimates: https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf
- Earlier research note in this conversation: Finite_C_A_Euler_Product_Square_Root_Attack.md (research source, not independently merged into Lean).

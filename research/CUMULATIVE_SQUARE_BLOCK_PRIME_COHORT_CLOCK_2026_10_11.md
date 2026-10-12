# Cumulative square blocks are the actual prime-family clock

**11 October 2026.** Interpretation: x can be arbitrarily large; its completed Mertens state is the cumulative outcome of every earlier square block, and each prime family's descendants enter at *different* square-block clocks. This note separates universal finite identities from the one missing uniform RH-scale bound. No new Lean compilation and no finite C/A/RH proof claimed.

## 1. The cumulative identity that targets ORIGINAL finite C

Let R>=2, X_R=R^2-1, and
\[
B_r=\sum_{n=r^2}^{(r+1)^2-1}\mu(n)
=M((r+1)^2-1)-M(r^2-1)\quad(r\ge2).
\]
Since M(3)=-1, the completed state is the sum of *every smaller block*:
\[
\boxed{M(X_R)=-1+\sum_{r=2}^{R-1}B_r.}\tag{1}
\]
At an arbitrary integer x>=4 with R=floor(sqrt x),
\[
\boxed{M(x)=-1+\sum_{r=2}^{R-1}B_r+
\sum_{n=R^2}^x\mu(n).}\tag{2}
\]
The last partial block has at most 2R+1 sites. Thus square endpoints control all x once a correct RH-scale endpoint theorem is proved.

The ORIGINAL floor kernel is Q_R=2M(R-1)-M(X_R). Using M(R-1)=1+sum_(r=2)^(R-1) mu(r),
\[
\boxed{Q_R=3+\sum_{r=2}^{R-1}f_r,\qquad f_r=2\mu(r)-B_r.}\tag{3}
\]
Thus
\[
Q_{r+1}=Q_r+f_r,\qquad
Q_{r+1}^2-Q_r^2=2Q_rf_r+f_r^2.
\]
The finite C criterion is EXACTLY
\[
\boxed{\exists C<\infty\ \forall R\ge2:
\left|3+\sum_{r=2}^{R-1}f_r\right|\le C R\sqrt{K_R},}
\]
where K_R=max_(0<=y<R)(M(y)-1)^2/(y+1). Bounding each |f_r| or adding its square independently does NOT establish this cumulative sign restriction.

## 2. Fully universal birth/death pairing across DIFFERENT square blocks

Every odd integer m obeys the exact Mobius doubling law mu(2m)=-mu(m). The two physical contributions have clocks
\[
r_{\mathrm{birth}}(m)=\lfloor\sqrt m\rfloor,\quad
r_{\mathrm{death}}(m)=\lfloor\sqrt{2m}\rfloor.
\]
For every square block r>=1,
\[
\boxed{
B_r=\sum_{\substack{m\ {\rm odd}\\r^2\le m<(r+1)^2}}\mu(m)
-\sum_{\substack{m\ {\rm odd}\\r^2\le2m<(r+1)^2}}\mu(m).}\tag{4}
\]
Here B_1 includes n=1,2,3; equation (4) also applies to B_1.

Summing all blocks through X_R proves the **exact universal complete-old-packet annihilation**
\[
\begin{aligned}
M(X_R)
&=\sum_{m\ {\rm odd}}\mu(m)\bigl(
{\bf1}_{m\le X_R}-{\bf1}_{2m\le X_R}\bigr)\\
&=\boxed{\sum_{\substack{X_R/2<m\le X_R\\m\ {\rm odd}}}\mu(m).}\tag{5}
\end{aligned}
\]
In fact (5) holds for every integer x>=1 with X_R replaced by x. All odd m<=x/2 have undergone both square-clock events and disappeared *exactly*. Only odd packets born at square-clock indices r approximately from R/sqrt(2) to R survive. This is a cross-block all-scale theorem, not a sampled fixed-x maximum.

For the actual odd prime p=97, its c=1 descendant at 97 appears in block 9 with weight -1; its c=2 descendant 194 enters block 13 with weight +1 and cancels it. Its c=3 descendant 291 enters block 17 with weight +1; later higher squarefree cofactor descendants add further parity-sensitive pulses. These are the same sequential prime-family operations, viewed along moving x.

## 3. The same cancellation extends to consecutive primes

For (m,6)=1, the complete Boolean cube for prime factors 2 and 3 is
\[
\mu(m)\left[{\bf1}_{m\le x}-{\bf1}_{2m\le x}
-{\bf1}_{3m\le x}+{\bf1}_{6m\le x}\right].
\]
It vanishes when x>=6m. Collecting the *incomplete* cubes at the top gives, for EVERY integer x,
\[
\boxed{
M(x)=
\sum_{\substack{x/2<m\le x\\(m,6)=1}}\mu(m)
-\sum_{\substack{x/6<m\le x/3\\(m,6)=1}}\mu(m).}\tag{6}
\]
This is the truly cumulative interpretation of adding primes 2 then 3; completed old cubes are gone and the remaining packets occupy two moving square-block clock windows. Higher primes generate the same finite alternating cube and new incomplete boundary windows. Exact cancellation of complete cubes alone does not bound their incomplete signed boundary at the RH scale.

## 4. Connect the surviving clock window to historical K_R: no independent prime randomness

For X=R^2-1 and R>=3, every odd squarefree m in (X/2,X] has either all prime factors <R, or one **unique** prime p>=R. In the latter case m=pc, c<R and c odd, with mu(m)=-mu(c). Therefore
\[
\boxed{
M(X)=S_R^{\rm old}-
\sum_{\substack{1\le c<R\\c\ {\rm odd}}}\mu(c)N_R(c),}\tag{7}
\]
where
\[
S_R^{\rm old}=
\sum_{\substack{X/2<m\le X\\m\ {\rm odd}\\P^+(m)<R}}\mu(m),\quad
N_R(c)=\#\{p\ge R:\ p\ {\rm prime},\ X/(2c)<p\le X/c\}.
\]
All child weights mu(c) occur strictly below R, hence within the historical K_R range. All prime populations N_R(c) are already determined by the earlier prime wheel:
\[
W_{R-1}(n)=\prod_{\substack{q<R\\q\ {\rm prime}}}
(1-{\bf1}_{q\mid n}),\qquad
W_{R-1}(n)={\bf1}_{n\ {\rm prime}}\quad(R\le n\le X),
\]
because every composite n<=X has a prime divisor <=sqrt n<R. Consequently
\[
N_R(c)=\sum_{\substack{R\le n\le X/c\\X/(2c)<n}}W_{R-1}(n).
\]
This is a *single* cumulative source: old primes generate the historical cofactor signs AND the survivor indicators for new square-clock packets. Do not treat those two factors as independent.

Equation (7) together with (3) is an exact formulation of the arithmetic object needing a uniform quantitative signed-return restriction. A bound on S_old or N_R separately is too weak.

## 5. Independent genuine-Mobius numerical audit of the cumulative packet flow

The companion C++ linear sieve independently checks the square-block telescope, floor-kernel recurrence, exact dyadic birth/death annulus, and exact two-prime Boolean-cube identity.

| R | X=R^2-1 | positive completed block totals | absolute negative completed block totals | sum | M(X) | Q_R | number of NONZERO surviving odd annulus coefficients |
|---:|---:|---:|---:|---:|---:|---:|---:|
|18|323|24|26|-2|-3|-1|67|
|56|3135|139|132|+7|+6|-10|634|
|317|100488|1725|1752|-27|-28|+22|20358|
|1000|999999|9423|9210|+213|+212|-208|202646|
|2000|3999999|25483|25290|+193|+192|-182|810554|
|5561|30924720|119471|122014|-2543|-2544|+2554|6266686|
|6000|35999999|136961|134704|+2257|+2256|-2256|7295158|

Here "sum" is positive minus negative block totals over r=2..R-1; add M(3)=-1 for M(X). For R=6000, the signed completed square-block masses have total variation 271665 but sum to +2257, while the 7,295,158 nonzero residual odd coefficients sum to just +2256. No result at finite R proves uniform suppression as R->infinity.

Exact two-prime cube checks:
- x=317: top (m,6)=1 signed -51, middle signed -23, difference -28.
- x=999999: top +86, middle -126, difference +212.
- x=35999999: top +1684, middle -572, difference +2256.

## 6. Link to EXISTING Lean architecture; do not reinvent another bridge

The following modules already formalize major pieces of the cumulative-clock viewpoint:
- RHLean/Analysis/SquareWheelNesting.lean: exact consecutive signed square-block telescopes into pinned wheel residuals; no all-scale analytic bound.
- RHLean/Proof/CanonicalGapAncestryBridge.lean: canonical parent-flow renewal, clock=sqrt(source product), complete finite alternating expansion, and telescoping source-block increments.
- RHLean/Analysis/SquareRunEscapeCovariance.lean: exact run-level squared signed mass = physical diagonal + 2 times cross-block covariance, explicit signed descended + escape split; stated outstanding quantitative escape bound.
- RHLean/Proof/RoughDyadicQ2Compression.lean and research/DYADIC_MOBIUS_SIGNED_RESIDUAL.md: exact odd/even pair cancellation and moving dyadic boundary families.

The all-R obstruction is no longer a lack of finite arithmetic or of a cumulative representation. It is the **uniform control of signed residual incomplete packets across square time**, especially their cross-block covariance and historical cofactor/survivor coupling. For finite C this must imply |3+sum_(r=2)^(R-1)f_r| <= C R sqrt(K_R) for every R, not merely a fraction of X, a local block upper bound, or cancellation of already-complete prime cubes.

A key scale distinction: at x about R^2, the historical envelope K_R uses M(y) for y<R; those older values come from square blocks of clock at most sqrt(R), i.e. the fourth-root scale of x. The signed-return theorem must propagate a bound across that much larger scale jump.


## 7. Exact all-x live-cohort squared energy: the diagonal is already correct scale

Let the surviving, still-live odd cohort at endpoint x be
\[
\mathcal L_x=\{m:\ x/2<m\le x,\ m\ {\rm odd},\ \mu(m)\ne0\},
\quad L_x=|\mathcal L_x|,
\]
and its fully signed **cross-cohort interaction**
\[
\Gamma_x=\sum_{\substack{m<n\\m,n\in\mathcal L_x}}\mu(m)\mu(n).
\]
The universal cross-square-block birth/death pairing (5) implies the exact integer identity
\[
\boxed{M(x)^2=L_x+2\Gamma_x.}\tag{8}
\]
Since there are at most x/4+1 odd integers in the upper half of [1,x],
\[
\boxed{L_x\le x/4+1.}\tag{9}
\]
So the diagonal is **unconditionally at the proper squared RH scale O(x)**. A fraction of x is useless as a bound on |M(x)|, but **a fixed multiple of x K_R in the square/covariance currency is precisely the target**.

If, and only if up to harmless absolute constants, the positive covariance obeys the still-unproved bound
\[
\boxed{\exists B<\infty:\quad
\Gamma_{R^2-1}\le B\,R^2K_R\quad\forall R\ge2,}\tag{10}
\]
then (8)-(9), K_R>=1, and (M-1)^2<=2M^2+2 imply a fixed finite-A amplification and hence the existing conditional RH closure. This is a genuinely cumulative physical target, but (10) is **not an independently proved saving**; it is essentially the original hard estimate moved into the live-cohort interaction, and must be established using the actual sign/factor ancestry.

### Nonpositive covariance fails for genuine primes

An independent genuine Mobius sieve checked **every R=2..6000** (5,999 square endpoints). The naive guess Gamma<=0 for every R is FALSE: **exactly three roots** have positive live-packet covariance:

| R | X=R²-1 | M(X) | L_X | 2 Gamma_X = M(X)²-L_X |
|---:|---:|---:|---:|---:|
|3|8|-2|2|+2|
|53|2808|-24|566|+10|
|5561|30924720|-2544|6266686|+205250|

For comparison at R=6000 the live count is 7295158 and M(X)=2256, yielding 2Gamma=-2205622. The positive R=5561 example is essential: no termwise all-R nonpositive covariance theorem is possible, even though it happens at most of the finite roots.

The reproducible C++ audit scans the live cohort cardinality incrementally as the square endpoint increases, checking these covariance exceptions alongside the signed block and Euler-cube identities. Its numerical range is not an all-scale bound.

This cleanly isolates the gap: **complete historical cross-block packets cancel exactly**, their incomplete odd packets have a diagonal already at O(x), but the SIGNED PAIR OVERLAP of the still-live cohorts must have a uniform finite upper bound in units x K_R. This cannot be obtained merely by counting the live packets or appealing to their common birth/death rule.


## 8. Explicit cumulative signed interaction: NO unknown covariance mechanism

The signed interaction is ALREADY fully determined by the chronological prime/square-cohort process. It is not a new stochastic or independent variable. The task is a universal quantitative bound on this exact arithmetic expression.

### A. Every pair has exact overlap clocks

For odd squarefree m define its lifetime indicator at square endpoint X_R=R²-1:
\[
I_R(m)={\bf1}_{\{\lfloor\sqrt m\rfloor<R\le\lfloor\sqrt{2m}\rfloor\}}.
\]
A pair m<n contributes \(\mu(m)\mu(n)I_R(m)I_R(n)\). Because n>m, its joint support simplifies to
\[
\boxed{\Gamma_R=
\sum_{\substack{m<n,\ m,n\ {\rm odd}}}
\mu(m)\mu(n)
{\bf1}_{\{\lfloor\sqrt n\rfloor<R\le\lfloor\sqrt{2m}\rfloor\}}.}\tag{11}
\]
The support is empty unless n<2m. In a whole interval of square clocks A<=R<=B, the EXACT cumulative signed exposure is
\[
\boxed{\sum_{R=A}^B\Gamma_R=
\sum_{\substack{m<n,\ m,n\ {\rm odd}}}\mu(m)\mu(n)
\left[\min(B,\lfloor\sqrt{2m}\rfloor)
-\max(A,\lfloor\sqrt n\rfloor+1)+1\right]_+,}\tag{12}
\]
where [t]_+=max(t,0). Thus every arithmetic pair has a definite sign and an EXACT finite interaction duration; there are no guessed independence assumptions. Each live pair is within one multiplicative factor 2.

**Non-obvious ancestry constraint:** Two simultaneously LIVE odd packets can NEVER divide one another. If odd m|n and m<n then n>=3m, whereas their joint lifetime requires n<2m. Hence direct opposite-signed odd-prime parent-child *edges* never appear as live-live covariance terms; their effects occur at different clock generations. Only the prime-2 partner annihilates a packet within its immediate dyadic lifetime. The concurrent interaction is between distinct, noncomparable ancestry branches.

### B. Common prime ancestry cancels from the pair SIGN

For squarefree odd m<n, put g=gcd(m,n), a=m/g, b=n/g. Necessarily gcd(a,b)=1 and gcd(g,ab)=1. Multiplicativity yields
\[
\boxed{\mu(m)\mu(n)=\mu(a)\mu(b)=\mu(ab).}\tag{13}
\]
The sign depends on the EXCLUSIVE prime factors; their shared ancestor g appears only in the physical availability and timing. Both live exactly when x/(2a)<g<=x/b. Therefore the ENTIRE physical interaction at ANY integer endpoint x is the exact *gcd-stripped finite ledger*
\[
\boxed{
\Gamma_x=
\sum_{\substack{1\le a<b<2a\\ a,b\ {\rm odd}\\ \mu(ab)\ne0}}
\mu(ab)
\sum_{\substack{x/(2a)<g\le x/b\\g\ {\rm odd},\ \mu(g)^2=1\\\gcd(g,ab)=1}}1.
}\tag{14}
\]
In particular all weights in the inner sum are NONNEGATIVE actual squarefree-coprime occurrence counts, while the outer signed coefficient is forced by prime factor parity. There is no free covariance to estimate; the needed estimate has to exploit these exact signs and the coupled gcd-availability counts.

Small exact census by direct enumeration of ALL simultaneous live pairs:

| x | M(x) | live L_x | Γ_x | pair coprime contribution | pair shared-gcd contribution |
|---:|---:|---:|---:|---:|---:|
| 8 | -2 | 2 | +1 | +1 | 0 |
| 317 | -4 | 66 | -25 | -31 | +6 |
| 2808 | -24 | 566 | +5 | +554 | -549 |
| 3135 | +6 | 634 | -299 | +4 | -303 |

The x=2808 example demonstrates dramatic cancellation between two **arithmetically coupled** ancestry sectors. The sign of a single sector is not a universal invariant.

### C. Exact signed-return update at EACH completed square block

Let X_r=r²-1. Define newly born and dying odd squarefree packets in block r:
\[
\mathcal B_r=\{m\ {\rm odd}:\mu(m)\ne0,\ r²\le m<(r+1)²\},\quad
\mathcal D_r=\{m\ {\rm odd}:\mu(m)\ne0,\ r²\le2m<(r+1)²\}.
\]
Let a_r=sum_(m in B_r)mu(m), d_r=sum_(m in D_r)mu(m);
let alpha_r=|B_r| and delta_r=|D_r|. Every dying packet belonged to the preceding live set, and every born packet is new. Thus the signed mass still surviving after the deaths is
\[
u_r=M(X_r)-d_r.
\]
The physical block increment is B_r=a_r-d_r. Partitioning the old-old, new-new, dying-dying and survivor-new signed pairs gives the EXACT identity
\[
\boxed{
\Gamma_{r+1}-\Gamma_r=
\underbrace{(a_r-d_r)u_r}_{\text{cross-generation signed return}}
+\underbrace{\frac{a_r²-\alpha_r}{2}}_{\text{new-birth pair signs}}
-\underbrace{\frac{d_r²-\delta_r}{2}}_{\text{completed-death pair signs}}.
}\tag{15}
\]
All quantities are explicitly computed from genuine Mobius prime-factor signs and the *same* cumulative previously constructed field. There are no assumed sign bounds here.

Telescoping (15) from r=2, where Gamma_2=0, reconstructs the complete live covariance. Independent exact C++ linear-sieve audit over EVERY r=2..5999 verifies this signed-return recurrence:

| R | cumulative cross-generation return | cumulative birth-pair signs | cumulative death-pair signs | resulting Γ_R |
|---:|---:|---:|---:|---:|
| 53 | +108 | -142 | -39 | +5 |
| 317 | -10399 | +738 | +126 | -9787 |
| 1000 | -79727 | +2946 | +2070 | -78851 |
| 5561 | +202813 | -151483 | -51295 | +102625 |
| 6000 | -1052177 | -101152 | -50518 | -1102811 |

For example, at R=5561, \(202813-151483-(-51295)=102625\). Thus positive cumulative covariance can be driven by cross-generation return despite negative signed interactions among new births; this is real arithmetic and does NOT mean the signed return is always negative or always positive.

### D. The only quantitative gate, still OPEN

The diagonal is already \(L_X\le X/4+1\). The original finite-A goal would follow from any proved universal positive-part upper budget on the **EXACT historical sum of (15)**:
\[
\boxed{
\sum_{r=2}^{R-1}\left[
(a_r-d_r)u_r
+\tfrac12(a_r²-\alpha_r-d_r²+\delta_r)
\right]\le C R² K_R,
}\tag{16}
\]
with one finite absolute C and every R. This is a precise sign-preserving arithmetic target, but it is not currently known, and merely calling it 'the exact interaction' or bounding lifetimes does not establish its scale. The bound is effectively the original finite-A difficulty expressed with true temporal packet interactions, not an additional independent premise.

The new structural facts (finite pair lifetimes, noncomparable simultaneous odd ancestors, and exclusive-factor sign formula) are useful restrictions to exploit in seeking an independent proof of (16). The needed inequality must be derived from actual factor/parity incidence; nothing stochastic or merely empirical closes it.

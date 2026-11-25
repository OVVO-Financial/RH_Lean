# Economical recovery on the square-clock source

The computation below uses the original prime-power, first-return and translated partner formulas. It produces a local image with positive quotient length at a high prime on an explicit native host. The integral module measured in that computation consists of width coordinates. A restriction of the native integral sections onto these coordinates remains to be constructed.

## Source and dependency check

The community head inspected on November 25 was `8e5cefeeaffe7e4c12153385b7bb33fb7223c41a`. The relevant source files for the following table agree with the earlier pin `251c7b05`. The two projects use Lean 4.37.0-rc1 and 4.34.1 respectively. [Upstream source](https://github.com/leanprover-community/riemann-hypothesis/tree/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a) · [pillar map](https://riemann.verifytask.cn/?lang=en) · [native directive](../docs/RHLEAN_NATIVE_ECONOMICAL_RECOVERY_20261125.md)

| Community declaration | Quantitative content | Native attachment |
|---|---|---|
| `EdgeFam` | Each source is integral in the selected edge and sufficiently deep in every other outgoing edge. One admissible dual tests each primitive combination while suppressing all other incoming edges. | Integral polynomial jets, the localized half-different pairing and the original translated arithmetic sites are available. The restriction of the actual section to the selected site and its competitors is open. |
| `EdgeStep` | Per-edge rank includes both weight multiplicity factors and the denominator $p^{n'r(m+1-r)}$. The bound on $D_1$ is $C_{D_1}|TT|(m+1)^2\log_p a$. Both source and target host cutoffs also have bounds. | The integral exponent decoder retains multiplicities. Native colour cardinality alone cannot supply the number of graph edges, and the rank $R^3-1$ measures the period lattice. |
| `SrcTests` and `goodRank_of_prim` | For a family of edges with common target, the primitive test and competing divisibilities imply simultaneous recovery. The sum of retained ranks is at least $(1-\kappa)\dim V$. | `exists_decoder_of_frame_congruence` turns a **single** frame meeting the selected and competing congruences into an exact integral decoder. |
| `admG1` | The served local quotient has a length bound with the original valuation of the rational prime. | `lengthFromAllBut_of_sandwich` needs exceptional generators at $\tau+\beta S$, the inverse shift, saturation, and $a^{VS}B\subseteq N_B$. Counts of divisible integers concern a different module. |
| `Conclusion1` and `linkG_at_core` | In the served branch the consumer reads the length from `hG1`. In the gain branch it reads the physical class-sum identification from `hfill` and both numerical inequalities from `h1`. | Use the actual index and placewise Gram costs on the same frame, the coupled degree/count and ordered-period inequalities, and both original signed means before invoking the #1205 window theorem. |

[Local contracts](https://github.com/leanprover-community/riemann-hypothesis/blob/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a/src/Formalism/SharpRestriction/GrowthBounds/ScaleEdges/ManyEdges.lean#L23-L106) · [numerical consumer](https://github.com/leanprover-community/riemann-hypothesis/blob/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a/src/Formalism/SharpRestriction/GrowthBounds/PlaneCountTheoremWithConstants.lean#L598-L646) · [native integral recovery](../RHLean/Geometry/NativeJointEvaluationRecovery.lean) · [served local application](../RHLean/Geometry/NativeServedPrimeApplication.lean) · [native signed payment](../RHLean/Analysis/AlpogeThin/NativeExistingRecoveryPayment.lean)

## Exact integral decoder and boundary

For $n>0$, factorization gives $n=\ell h$ with all prime factors of $\ell$ at most $z$, all prime factors of $h$ greater than $z$, and their full multiplicities. Fix $\ell$ and a finite divisor-closed set of such $h$. Write $b=v(h)$, $a=v(d)$, and $|b|=\Omega(h)$. The coefficient of $X^a$ in $(X+s)^b$ is $T_s[a,b]=\prod_i\binom{b_i}{a_i}s^{b_i-a_i}$ on $a\le b$, and zero otherwise. The multiplication $T_sT_t=T_{s+t}$ involves only intermediate divisors. Hence $J=T_1$ has inverse $K=T_{-1}$, with sign $(-1)^{|b|-|a|}$, and both matrices have determinant one. A partition of the prime axes factors the entry product. A truncated prefix need not be a Cartesian product.

The absolute column sum for either matrix is $2^{|b|}$. Since $z^{|b|}\le h\le N$, both induced column norms are at most $N^{\log 2/\log z}$. For $z\asymp\log N$ the exponent tends to zero. In the complete integer prefix the exact maximum is the largest $2^j$ such that $p_+^j\le N$, where $p_+$ is the least prime greater than $z$, provided $p_+\le N$. A proper divisor $d\mid h$ omits a prime larger than $z$, so $z\ell d<\ell h$. If $\ell h<(R+1)^2$, then $z\lfloor\sqrt{\ell d}\rfloor^2<(R+1)^2$. If $zR^2\ge(R+1)^2$, every such divisor is strictly before the current block. On any other block the last strict inequality is the boundary test. The decoder of a window alone must include the incoming prefix coordinates or explicitly account for them. [Prime-axis inverse](../RHLean/Geometry/NativePrimeExponentJet.lean) · [integer cutoff and descent](../RHLean/Analysis/AlpogeThin/NativePrimeExponentAncestry.lean) · [integral Hasse jets](../RHLean/Geometry/NativeThetaIntegralJets.lean)

At a single top, PageN gives $2N<2^{e+2}$. Two unramified positive prime powers at most $N$ having the same dyadic displacement must be equal as integers. The two bases and exponents then coincide, and inertia is trivial. The original integer incidence therefore contains the identity on **all** these rows. The normalized kernel multiplies those rows by two, a local unit at odd places. [Complete one-top prefix](../RHLean/Analysis/AlpogeThin/NativeDyadicUnramifiedPrefix.lean)

## A high-prime joint image on the actual arithmetic sites

Take $R=m=10^7$, $N=x=Y=R^2-1$, $\epsilon=9/560$, $e=99$, $q=3$ and $d=3814\cdot5^{400}+1$. The test certifies primality of $d$ by the prime factor $5^{400}>\sqrt d$ of $d-1$, modular exponentiation at base 2 and a gcd check. Rational Taylor bounds certify the `WinPair` inequalities and integer powers certify `PageN`. Take $TT=\{[1],[17],[47],[43^2]\}$, $T_2=H$, $b=\beta=w=16$, $h=1$ and $a_t=A_{\max}=16N$. Then $\Delta=1$ and the original $Q=|TT|mb\Delta/2=320000000$. This certifies the stated host and width data, including the tightened PageN cardinality band. The alternative $\epsilon=1/64$ certifies PageN alone. The four-top example fails the downstream geometric top-density condition and $26\le x^{3\epsilon/8}$. The analytic zero boxes and twisted estimates of `PairGood` have not been certified. Thus the example exercises original arithmetic rows on an admissible square host, before the full asymptotic hypotheses.

Fix a lift and member, vary the widths within their active intervals and take the integral coefficient of each width in the original site cut. On the tested sites it is $-1$. The unfactored scalar for an unramified active prime is $2\log p$. The selected rows come from top $[1]$. The competing matrix includes **all other active reads** that hit the same sites anywhere in the prefix. To enumerate them it suffices to check $t'n'=t p^i$ as ordinary integers, since $2\max(TT)N<2^{e+2}$. Widths at all other sites are independent coordinates of this width model. The first-excluded sites are exactly $([1],17,1)$ and $([1],47,1)$. At cutoff 32 the first retained high prime is 43.

| Local prime | Selected exponents | Exact Smith factors of $E(L_2)$ over $\mathbb Z_{(p)}$ | Quotient length | Counts $\#\{i:a_i>j\}$ for $j=0,1,2$ |
|---|---|---|---:|---|
| 13 | $1,3,5,7,9,11$ | $1,1,1,1,1,1$ | 0 | $0,0,0$ |
| 43 | $1,3,5,7$ | $1,43^2,43^2,43^2$ | 6 | $3,3,0$ |

At 43 the rows $i=3,5,7$ each read the same width as exponent $i-2$ at top $[43^2]$. The constant and cutoff terms still depend on the exponent. At precision $\pi^c$ the image of the selected width reads is exactly $\mathcal O\oplus(\pi^c\mathcal O)^3$. The three unit-coordinate obstructions survive any integral change of source basis. In this width quotient the minimal exceptional count is three before either of the first two uniformizer layers is exhausted. For example, a putative first grouped estimate with $d_{\rm rank}=4$, $\tau=0$ and $s\le1/2$ would allow at most two generators. Choosing $\tau\ge c$ would already charge the full depth. The actual section module and its grouped parameters have not been identified. For a one-unit width increase repeated over all members and lifts, the ASK change divided by the original $Q$ is $-\log(p)/16$ for one active preimage and $-\log(p)/8$ for the duplicated 43-sites. The original MAIN includes every positive width with coefficient $-a_t/|\Phi|$ on its logarithm. Thus raising this one width from 16 to 17, at every member and lift, gives the following exact change in the **complete** normalized arithmetic ASK minus MAIN:
$$
-\frac{\nu\log p}{16}+\frac{N}{2^{99}}\log(17/16),\qquad \nu=1\text{ or }2.
$$
It is strictly negative since $N/2^{99}<1$, $\log(17/16)<1/16$ and $p\ge13$. This variation is at the original $Q$ and measures every active preimage. The geometric cost of moving an actual section in that direction has not been obtained. The experiment computes a congruence-kernel basis by Bézout column operations and then takes gcds of minors of its selected image. It repeats the calculation in the original coordinates and after the divisor-closed basis changes at $z=16,32,64$. Extension by zero off the tested width sites realizes every listed image direction. The general one-prime fibre calculation also describes missed cosets and repeated labels. [Reproduce the host and Smith computation](../scripts/native_economical_recovery_widths.py) · [exact output](NATIVE_ECONOMICAL_WIDTH_IMAGE_20261125.json) · [translated width identity](../RHLean/Analysis/AlpogeThin/NativeDyadicShiftedWidthRows.lean) · [integral coset images](../RHLean/Analysis/AlpogeThin/NativeDyadicColourImage.lean)

## Signed ancestry and a paid terminal sector

For the principal weight $f_N(n)=\Lambda(n)(N/n-1)$, when $\ell>1$ the exact signed column is $(-1)^{\Omega(h)} f_N(\ell)$. Each term with a nontrivial high divisor is supported on at least two different primes and vanishes. On $\ell=1$, writing $a_p=v_p(h)$, the exact column is
$$
(K^\top f_N)(h)=(-1)^{\Omega(h)+1}
  \sum_{p\mid h}\log p\,[N(1-(1-1/p)^{a_p})-1].
$$
This follows by summing the binomial coefficients of each single-prime tower with their signs, before taking an absolute value. Given the original $f_N$, right multiplication by $J$ recovers its complete principal value site by site. Across $R=16,32,64,317,1027$ the exhaustive test verified both inverses on 805572 divisor intervals and the signed formula at all 1160589 physical integer sites. At $R=317$, the unweighted norm is 16, while the signed columns at 26 and 338 are respectively $-50243\log 2$ and $+50243\log 2$. At $R=1027$, sites 34 and 578 give $\mp527363\log 2$. [Run the full experiment with the --full option](../scripts/native_economical_recovery_exact.py)

Even for positive candidate weights $w_N(n)=\log(n)(N/n-1)$ the weighted matrix norm can grow polynomially. At $R=p+1$, $N=p^2+2p$, both $w_N(p)$ and $w_N(p^2)$ are positive and $|K[p,p^2]|=2$. Thus $2w_N(p)/w_N(p^2)=p(p+1)/2$. This sign obstruction is distinct from the archimedean Gram matrix on the section lattice.

There is nevertheless a uniform payment for **all higher prime powers** in the terminal source. Define
$$
c_{\rm pp}=\sum_{p}\frac{\log p}{p(p-1)},\qquad
B(t)=\psi(t)-\theta(t),\qquad
P_N=\sum_{p^a\le N,\ a\ge2}\log p\,(N/p^a-1).
$$
The Chebyshev bound $0\le B(t)\le C\sqrt t$ gives convergence of the series. Summing the complete towers gives $c_{\rm pp}=\sum_{n\text{ nonprime}}\Lambda(n)/n$. Abel summation with the endpoint retained gives
$$
0\le Nc_{\rm pp}-P_N=N\int_N^\infty B(t)t^{-2}\,dt\le 2C\sqrt N .
$$
The submitted Lean proof uses the discrete inequality $\sqrt m(1/m-1/(m+1))\le 2(1/\sqrt m-1/\sqrt{m+1})$ and passes to the limit in the finite sums. For $1\le N$ and $0\le z\le N$, put
$$
H_{N,z}=\sum_{z<p\le N}\log p\,(N/p-1)
 +N\sum_{p\le z}\frac{\log p}{p}
 +N(1+\gamma+c_{\rm pp}-\log N).
$$
Direct substitution in the existing arithmetic identification yields
$$
H_{N,z}-G_z(N)=\theta(z)+Nc_{\rm pp}-P_N,\qquad
0\le H_{N,z}-G_z(N)\le (\log 4)z+2C\sqrt N.
$$
In the left side $G_z$ denotes the repository's principal source; the new cutoff is used only in the explicit comparison $H_{N,z}$. The coefficient of the low-prime linear term varies with $z$ and is retained. At $N=R^2-1$ and $z\asymp\log N$ the discrepancy is $O(R)$ with a constant independent of the window. A remaining first-prime bound still has to cancel the displayed Euler and low-prime terms. [Terminal centering and complete prime-power estimate](../RHLean/Analysis/AlpogeNativeProperPowerCentering.lean) · [finite prime-tower payment](../RHLean/Analysis/AlpogeThin/NativePrimeTowerCentering.lean)

For the original ASK, the type-I sums at 2 and $q$ vanish by the actual character formulas. At each unramified inert prime, only odd powers survive. In a high-only column their signed weights all have the same parity. The $d$-term has the opposite sign at even powers. These statements retain the actual positive-part widths and all exponents. On a prefix $N\le Y^2$ for the **same** WinPair at sufficiently late $Y$, put $P=Y^{\epsilon/5}\ge3$ and $z\le P$. The selected pair forces $d>N$ and every active unramified inert prime exceeds $P$. At each fixed original top $t$, member and lift, the sum of the absolute transformed ASK columns is at most
$$
2Na_t\sum_{p>P}\frac{\log p}{p(p-1)-1}
\le16Na_t(1+\log P)/P .
$$
Indeed $\sum_{h\le N}\binom{v_p(h)}{k}=\sum_{b\ge k}\binom{b-1}{k-1}\lfloor N/p^b\rfloor\le N/(p-1)^k$. Multiply by $2a_t\log p/p^k$ and sum in $k$. This deterministic count has no independence premise. The estimate is per top and width. The actual complete ASK cutoff is $\lceil A_{\max}/\beta\rceil$ and may substantially exceed $N$. The original denominator, all terms beyond the square prefix, both means and MAIN still enter the signed comparison. [Signed original rows](../RHLean/Analysis/AlpogeThin/NativeSignedPrimeExponentAncestor.lean) · [original cutoff](../RHLean/Analysis/AlpogeThin/NativeDyadicCostWindows.lean)

## The full cutoff and repeated first primes

The arithmetic changes again beyond the square prefix. For a fixed odd base $p$ and any positive return $k$ in the dyadic factor, the local unit is $p$ modulo $2^{e+2}$ up to sign. Squaring and applying the $2$-adic lifting-the-exponent formula gives $2^{e+2}\mid(p^2-1)k$. Hence $(p^2-1)i<2^{e+2}$ excludes a return by exponent $i$. In the native scalar regime $N_{\rm ASK}\le4x^4\exp(x^{\epsilon/3})$ and PageN implies that for every $p\le x$ this test applies throughout the full cutoff once $x$ is sufficiently large. Cross-top coincidences use different tops and obey a different criterion. [Dyadic order and full scalar budget](../RHLean/Analysis/AlpogeThin/NativeDyadicReturnBudget.lean)

There are nevertheless genuine collisions among large **first** primes at one thin site in the complete source. This is a paper argument using classical Linnik, outside the Lean dependency chain. Write $M=2^{e+2}qd$, $T=\exp(x^{\epsilon/3})/3$. Native conductor bounds give $\log M\le 2x^{\epsilon/5}(\log x)^2$ on the late selected windows. Since $5\nmid M$, prescribe the class $-1$ modulo $M$ and independently each unit class modulo $5^k$. Linnik gives a prime in each of these reduced classes up to $(5^kM)^L$ for an absolute $L$. Choose the largest $5^k$ with $(5^kM)^L\le T/2$. The resulting $\varphi(5^k)$ distinct primes exceed $x$ and satisfy $p<T\le a_t/w$. All have the same original complex conjugation colour $((1,1),0)$ and thin partner $((0,0),t)$. Their original first-power contributions are strictly positive and proportional to $\log p\,(a_t/p-w)$. These scalar weights vary with $p$. This proves that one cannot give independent colour coordinates to all such labels, even after paying the proper-power tail. It creates no comparison between DVRs at different primes. [Conductor bound](../RHLean/Analysis/AlpogeThin/NativeDyadicHostWindows.lean) · [original colour and partner](../RHLean/Analysis/AlpogeNativeSharpASKBalance.lean) · [Linnik's theorem, 27.1](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf#page=298)

## First missing physical map

At a place above 43 the constructed host has its prescribed period lattice, its Hermitian pairings and a complex theta section. Translating a section through periods only rescales the value by its automorphy factor. Consequently every two-by-two value minor obtained from two such translates at one point has determinant zero. The short-section orbit constructor instead needs actual algebraic points, an integral lattice of sections, orbit independence and off-support vanishing. The Hasse tests alone act on the homogeneous symbols. [Native square host](../RHLean/Geometry/NativeSquareHostRealization.lean) · [period evaluation minor](../RHLean/Geometry/NativeThetaPeriodEvaluation.lean) · [graded integral section inputs](../RHLean/Geometry/NativeGradedShortSectionConstruction.lean) · [actual jet expression](../RHLean/Geometry/NativeThetaEvaluatedFamily.lean)

The missing constructor is an integral restriction from the localized geometric sections to edge-indexed germs, together with its admissible dual, whose normalized evaluation agrees with the original Frobenius, inertia and partner restrictions. The first nontrivial test on the displayed host is to distinguish the two reads $([1],43^3)$ and $([43^2],43)$ by that actual pairing while meeting every competing congruence. Any proposed common lift factoring only through the repeated width makes the two coefficient rows equal. On such a lift $\pi^c$ must divide $p^D$ if the selected coordinate recovers $p^D$. For the stricter competing depth this is impossible. A primitive geometric jet could distinguish these reads; its restriction and integrality on those sections have yet to be proved.

Without this map the section quotient has no computed Smith list, geometric exceptional-generator family or stopping inclusion. A basis change $U$ of determinant one preserves both an integral frame's index and $\det(U^*GU)=\det G$ at each archimedean place. The positive width-quotient length above gives no numerical signed gain on that frame. No bound for the complete $\mathcal S_x/Q$ or hypothesis-free RH theorem follows from these results. [Covolume](../RHLean/Geometry/NativeSummandCovolume.lean) · [ordered-period capacity](../RHLean/Geometry/NativeSquareCapacityPeriod.lean) · [native window handoff](../RHLean/Analysis/AlpogeNativeBoundHandoff.lean)

All seven existing roles consumed `NATIVE_ECONOMICAL_RECOVERY_V1` in this execution. Their assignments were COORDINATOR, OWNER, REFEREE, CENSUS, ANALYTIC, WHEEL and LEAN. Hosted verification is recorded on the exact revision of #1201.

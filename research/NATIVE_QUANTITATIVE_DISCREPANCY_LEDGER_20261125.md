# Quantitative discrepancy ledger for #1201

The three transfer errors below have a uniform bound with exponent coefficient 1. The independent bound derived below for the comparison source is weaker than the critical estimate. Existence of a measured geometric frame with the required signed gain at every anchor on cofinal windows remains open.

Hosted Lean verified the assembled inequality, its normalized price and the independent physical mass bound at commit `393cb5c`. The same job verified the refinement that freezes only the thick widths. [Proof and axiom audit](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45780078438/job/139773341050).

## Same-family cancellation in the pinned Sernau editions

The primary reference for #1214 is `lsernau/grh-lean@72fead102f663d5c7a407964a13dc0cf9d977207`. The original proof map and the community port remain available for the local valuations. [Readable guide](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/GUIDE.md) · [Original proof map](https://riemann.verifytask.cn/?lang=en) · [Independent verification of both editions](https://math.mit.edu/~drew/shortgrh/).

### What supplies one inverse ratio

Use the compact `Data.heightLe_inv_ratio` as the starting point for the lower comparison. In this subsection write $B_{\rm dir}=fa(\log b)^3/(mk)$ for the compact `Data.B₀`. The $B_0$ of the endgame table below is the **global** budget $mk B_{\rm dir}$. Let $n_\sigma=w(0,\sigma)$ be the integral base order and $v_\sigma$ the nominal width ($a/x$ thick and $a/x_1$ thin). Then
$$
 \mathcal U=\sum_\sigma\left[\log(n_\sigma!)-n_\sigma\log(\Omega/g)-\operatorname{primeSum}(v_\sigma,\sigma)\right],\qquad
 F(p)=\sum_\sigma\operatorname{localAsk}(p,v_\sigma,\sigma).
$$
The compact rank-one pair also has the required lift rank, $m<z\le r$, $1\le j\le m$, tame character $\omega^j$, and $c\le w_j$, $w_j+r\le c+t$ at every site. The numerator of the top-row ASK uses $a_t$ separately. Replacing $v_\sigma$ with $a_t$ here changes the common main amount. [Admissible data](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Data/AdmissibleData.lean#L126-L151) · [Forced part](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Curve/LiveSum.lean#L17-L29)

| Supplying step at the pinned commit | Quantity and order of the witnesses |
|---|---|
| [Indicator jet](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Rows/GluedFormTheta.lean#L26-L40) | For given integral orders $v_\sigma\le m_\sigma\le v_\sigma+x^{42}$, choose one nonzero $t$ with all conjugates bounded by $\exp(fmb/k)$. For every eligible ideal, prime and place choose a grid point and jet of those degrees with $\lvert\kappa_0^{12}(\prod m_\sigma!)\,\mathrm{coeff}/t\rvert_p\ge p^{-F(p)}$. This is an **upper** valuation bound. |
| [Untwisted norm](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Rows/Separation.lean#L80-L95) | An independent flat auxiliary pair $q$ supplies the global height witness $q.\mathrm{intAlgPart}(1)/\lVert T_1\rVert^2$. An all-embedding comparison and a finite integrality theorem yield $\operatorname{HeightLe}(B_{\rm dir}-\sum_\sigma\mathrm{jetSize}(n_\sigma),\lVert T_1\rVert^2)$. |
| [Rank-one repayment](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Rows/HeckeValueHeight.lean#L154-L216) | For each fit family, lift index $j$ and rank-one pair, form a common nonzero $V$ of conjugate size at most $e^{B_{\rm dir}}$. At each place the jet, finite character inversion, character factorization and a kernel pairing supply an actual test $\Xi$ with $\lvert V\rvert_p p^{-F(p)}\le \lvert N^2\langle\Xi,T_{\vartheta^j}\rangle/\rho_{q_2}\rvert_p$, where $N$ is the class number. Apply this at the identity and conjugation. The tested rank-one projector bounds $N\langle\Xi,\operatorname{pr}_T\Xi'\rangle$ by $e^{\gamma_p}$. The witness $V\bar V$ has local allowance $\gamma_p+2F(p)\log p$ and the auxiliary squared ratio has divisor $N^3$. |
| [Prime sum](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Columns/SizeEstimates.lean#L29-L45) and [fit](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/FitTwists.lean#L243-L263) | $\sum_{p<U}2F(p)\log p=\sum_\sigma\mathrm{primeSum}(v_\sigma,\sigma)$ for $U\ge\lceil x_1\rceil$. Every finite prime sum of $\gamma_p$ is at most $B_{\rm dir}$. The independent norm and the squared ramified-ratio allowance $2x^{999}$ complete $\operatorname{HeightLe}(6B_{\rm dir}-\mathcal U,\rho_p(\vartheta^j)^{-1})$. Height requires one nonzero global scalar, **all** archimedean embeddings, **each** prime-place map, and all sufficiently large prime cutoffs. [Height definition](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Heights/Heights.lean#L18-L24) |
| [Product](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Rows/HeckeValueHeight.lean#L218-L237), [comparison forms](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Rows/ComparisonForms.lean#L194-L227) and [volume](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Rows/LiftVolumeHeight.lean#L103-L127) | The specified pairs with their multiplicities give $10mx^{999}+k(6B_{\rm dir}-\mathcal U)$. The one surjection $A$ satisfies $T_\vartheta^*\mathrm{gl}_\vartheta=\gamma_\vartheta A$, $\lvert\gamma_\vartheta/\gamma_1\rvert^2=\Gamma(\vartheta)/\Gamma(1)$. Its testedness, integrality and hook-weighted untwisted squared norm bound $e^{2r B_{\rm dir}}$ times the input Weyl norm feed the compressed determinant. The volume-ratio height cost is $d k((\log b) B_{\rm dir}-\mathcal U)$ with $d=\mathrm{rowDim}$. |

#### Native valuation and norm on the wheel jet

For each prime $p$, a single $u_p\in I(p)$ works simultaneously for all nominal sites and powers. At exponent $e$ let $g=eF_p+u_p$ and $\sigma'=\sigma+\mathrm{partner}(0,g)$. At eligible colours use the actual multiples $kp^e$ with $\lceil v_{\sigma'}\rceil<k\le\lfloor v_\sigma/p^e\rfloor$. Each gcd grows by exactly $p$ when $p$ is admitted to an earlier coprime wheel. The count is bounded above by $(v_\sigma/p^e-v_{\sigma'})_+$. Minimizing the **sum** over the single inertia chart bounds its total integer depth by the inertia average $F_p$. The exact native identity `forced_sum_eq_nominal_ask` identifies $\sum_{p\le N}2F_p\log p$ with the original full kernel ASK summed at the nominal widths with the same finite cutoff $N$ once it covers all positive width ratios. It includes the actual inertia weights and proper powers. This statement holds for each such $N$ independently.

Write $A$ for the product of the measured gcd readings, $\alpha!=\prod_\sigma\alpha_\sigma!$ and $J=A X^\alpha/\alpha!$. The integral test $\alpha![X^\alpha]J=A$ has $v_p(A)\le F_p$ for every admitted prime. Independently, the Fock metric gives $\lVert sJ\rVert^2=s^2 A^2/\alpha!$ on that very polynomial. For interval indicator lengths $v_\sigma>0$, $s=\prod_\sigma v_\sigma^{\alpha_\sigma/2}$, so
$$
 \log\lVert sJ\rVert^2\le -\log(\alpha!)+2\log s
   +\sum_{\sigma\in\Phi}\Re\operatorname{ASK}_{N}(v_\sigma,0,\rho\mapsto v_{\sigma+\rho}).
$$
The metric term $2\log s$ remains in full. In a single interval of width $w\ge1$ at the first allowed order $m=\lceil w\rceil$, the untwisted squared norm $w^m/m!$ is at least $1/2$. In the unit-coordinate metric take the primitive test $E=X^\alpha/\alpha!$. Every nonzero Euler scalar spans the same line, whose projector fixes $E$. For a class multiplier $h$ the tested diagonal $dh\lVert E\rVert^2$ is integral exactly when $\alpha!\mid dh$. Thus the smallest positive clearing is $\alpha!/\gcd(\alpha!,h)$. At $h=1$ its log cost uses the entire factorial gain. This identifies the first unpaid comparison for this candidate. [Native wheel jet and denominator](NativeRankOneEulerRepayment.lean)

The physical specialization `dyadic_nominal_jet` uses the rec-map Frobenius and inertia of `alpogeNativeHostData e q d`. Its sites are the translated `alpogeNativeThickPositiveSites T2 t`, with widths $a/x$ and $\beta=a/x_1$. It takes $\alpha_\sigma=\lceil v_\sigma\rceil$ on $\Phi$ and zero elsewhere. The original cutoff $N=\lceil A_{\max}/\beta\rceil$ suffices from $0<a\le A_{\max}$ and $1\le x\le x_1$. The statement applies to any selected prime pair, arbitrary translate and thick set, with all width and height parameters shared.

**The derivative has the height orientation in Separation.** For $y>0$ rational, the witness $W=1/y$ gives $Wy=1$ at every finite place and $\log|\sigma W|=-\log y$ at every archimedean embedding. Multiplying by the corresponding witness for $1/y$ and applying `HeightLe.nonneg` shows that this budget is sharp. In the compact proof, `log_norm_map_norm_sq_trivialLift` has $+\sum\mathrm{jetSize}$ on the squared **lift** norm side, with an embedding-dependent common constant and remainder $r\ge-4f$ ($r\le4f$ for the flat comparison). The negative sign appears on taking the reciprocal in the height witness. [All-place product formula](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Heights/Heights.lean#L52-L83) · [Untwisted lift comparison](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/AlgebraicPartConjugates.lean#L48-L63)

In the native Fock pairing the measured top derivative has Riesz vector $T=X^\alpha/s$. For any complex read $z$, put $J(z)=szX^\alpha/\alpha!$. Then $\langle J(z),T\rangle=z$ and $\lVert T\rVert^2=\alpha!/s^2$. The choice of $T$ precedes the prime, embedding and character. When $r=s^2$ is positive rational, `rational_derivative_height` constructs $W=r/\alpha!$, proves $W\lVert T\rVert^2=1$ and computes its log size at **every** embedding as $\log r-\log(\alpha!)$. For general positive real interval widths the real norm identity still holds. At every positive real scale, take $k=\lfloor\log_2(s^2)\rfloor$ and the rational comparison $r=2^k$. Then $r\le s^2<2r$, the archimedean log discrepancy is less than $\log 2$, and all local character pairings still read the same $z$. The finite norm of the metric multiplier is $1$ at every odd prime and $2^{-k}$ at $2$. This replaces a rationality requirement on the real anchor by an explicit comparison. Its 2-adic cost and its fit on the physical section family still require payment.

For $p$ in the finite prime set keep every other chart fixed. The derivative reads the fixed global integer $A$ at $u_p$. Translate the chart function $a_p(v)=(\prod_{q\ne p} A_q)\operatorname{chartRead}_p(v)$ on the actual subgroup $I(p)$. Complete character inversion and the ultrametric triangle inequality select a character $\chi$ **after** the place. The sum $z=\sum_{v\in I(p)}\chi(v)a_p(u_p+v)$ is an algebraic integer, and
$$
 |\iota A|\le |\iota(\langle J(z),T\rangle/|I(p)|)|,\qquad
 |\sigma\langle J(z),T\rangle|\le\sum_{v\in I(p)}a_p(u_p+v)
$$
for every archimedean embedding $\sigma$. This is `common_jet_twisted_read`. The divisor is the cardinality of the **native inertia group**. Upstream $N$ counts global level classes. Identifying these normalizations or pricing their quotient is a further physical comparison.

On this candidate the tested projection has an exact finite cost. The Fock-orthogonal projection is $P\mapsto [X^\alpha]P\,X^\alpha$. In particular, $\langle J(z),\operatorname{pr}_T J(z')\rangle=s^2 z\overline{z'}/\alpha!$ for the two actual character readings. Both primitive and wheel tests lie in this line. With $s^2=B/C$, $C>0$, the wheel reading gives $\lVert J(A)\rVert^2=BA^2/(C\alpha!)$. For a class factor $h$ the positive clearings are exactly the multiples of
$$
 d_{\min}=\frac{C\alpha!}{\gcd(C\alpha!,hBA^2)}.
$$
The theorem `measured_line_denominator` proves the equivalent divisibility $C\alpha!\mid d h B A^2$. The primitive unit-metric case above is $A=B=C=1$. For positive $h,B$, this also forces $\log d_{\min}+\log h+2\log A\ge\log(\alpha!)-\log(s^2)$. There is a sharper local test on the actual dyadic host. At an unramified split prime $p$ with Jacobi symbol $(-d/p)=1$, its inertia is trivial and every Frobenius power has first bit zero. The entire wheel reading $A$ is a $p$-unit. If $p$ is also prime to $hB$, every clearing has $p^{v_p(\alpha!)}\mid d$. This applies at odd split primes of a dyadic metric prime to the class multiplier. It isolates a factorial cost untouched by the nominal ASK at that prime. The physical upstream fit bound applies to its specified test forms; transferring that tested lattice remains essential.

For a finite check, use the repository’s local host $e=0,q=11,d=7$ of conductor $308$, the singleton thick set, $a=A_{\max}=1800$, $x=30$, $x_1=60$. There is one thick and one thin positive site, so the two orders are $60,30$ and $N=60$. The dyadic squared dilation is $2^{501}$. The prime $29$ is unramified and split, and $v_{29}(60!30!)=2+1=3$. A class factor prime to $29$ therefore forces $29^3=24{,}389$ into the clearing already on this one measured line. This example checks the local arithmetic; the cofinal window theorem has additional size hypotheses. [Local host specification](../RHLean/Analysis/AlpogeThin/Formalism/FrobeniusOrbits/Statement.lean)

A physical inverse ratio still requires a tested lift of these evaluations into the retained signed family. Its normalization must match the twist/untwisted ratio, and the fit projector for two such integral tests must have a common summable allowance. The metric comparison from $s^2$ to the required period and the actual integral base orders remains open. The existing high thick-cut Gram and its integral duals apply to a different stage. Attaching the tests by a measured surjection, or giving a one-sided transport with its full index cost, remains necessary before their determinant can carry $-\mathcal U$ into C. [Lean declarations](NativeRankOneEulerRepayment.lean)

### The common amount in the endgame

Write $D$ for the target dimension, $n$ for the retained dimension, $H$ for the main amount, $B_0=fa(\log b)^3$, $L=(\log b)B_0$, and $R$ for the signed remainder in Sernau's data. On one selected independent family $y$, $V$ bounds its logarithmic squared covolume at every complex embedding. The index allowance $\delta$ is the sum of the local denominator-clearing determinant valuations weighted by $\log p$.

| Source input | Quantitative contribution on $y$ | What the native proof needs |
|---|---|---|
| A, short integral forms | A single integral spanning set gives $V\le n(H-mR+L)$ for the selected images. The readable index bound before choosing the translates is $2\lvert t\rvert\dim(\mathrm{source})B_0$. At an exceptional prime a common submodule supplies its gain and its colength before the twists are selected. | Bound the Gram volume of the **actual** retained columns with the signed $S(v)$ in it. Local primitive tests are one way to construct these columns. A direct same-family norm or Gram inequality could replace them. |
| B, enough forms | $n\ge(1-4/b^2)D$ and $\lvert t\rvert\dim(\mathrm{source})\le5D\log(1+2b^2)$ in the readable edition. The compact family has $\delta\le5D\log(1+b^2)B_0$. | Realize independent rows with a uniform missing-rank and denominator budget. An arbitrary number of downstream changes at one prime is allowed. The budget covers their common images. |
| C, long integral forms | $D(H-3L)\le V+2\delta$ on those same columns. Its proof extends to a basis, pays for the complement, and uses a ratio of twisted volumes. It uses the near-full rank from B. | `NativeIntegralCompletion` pays the auxiliary columns given a metric and integral basis. `NativeNumberFieldIntegralDescent.prod_gram_transport` accounts for the change of integral basis over the embeddings. Still needed is the lower bound with **the same** $H$ as in A. |
| Normalization | The readable argument divides by $ma\lvert\Phi_b\rvert$, controls two remainders at $x_1$, and at integer anchors obtains $(64\varphi(q_0)+3)x^{-1/2+6\varepsilon}$ for fixed admissible $(q_0,d)$. The compact argument gives an eventual $x^{-1/2+8\varepsilon}$ at its corresponding step. | Compare the native signed source with its own original $Q=\lvert TT\rvert mb\Delta/2$ on the moving pair and every real anchor. The fixed-discriminant upstream prime remainder has a different normalization. |

With $I=10\log(1+2b^2)B_0$, the readable inequalities imply $nmR\le D(4L+2I)$ since $H+L\ge0$ and $n\le D$. Only **after** using C does $D\le2n$ suffice. The compact calculation uses $h=H-mR+L$, $D-n\le4D/b^2$ and $-h\le b^2 x^{99}$ to obtain $mR\le4L+4x^{99}+10\log(1+b^2)B_0$. Both absorb the errors in $fa(\log b)^5$. Each permits a native calculation with a different metric if the discrepancy between its two main amounts is independently priced. [Readable A and B](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/ShortAndEnough.lean#L254-L286) · [Readable C](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Determinant/Twist/LongForms.lean#L209-L260) · [Readable cancellation](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/MainInequality.lean#L87-L155) · [Compact family](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Endgame/LongForms.lean#L73-L96) · [Compact cancellation](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Main.lean#L121-L151) · [Analytic normalization](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/OneSidedBound.lean).

In compact A, $H=mk\,\mathrm{dirCost}$ and $R=\sum_{\tau\in\mathrm{tops}}(\mathrm{primeSum}(a,\tau)-\mathrm{mainAsk})$. For the fixed set $P$ of nonsplit primes and the level prime $N$, the proof actually scales every translated form by the single positive rational
$$
 q_* = \prod_{p\in P\cup\{N\}}p^{e_p},\qquad
 e_p=\left\lfloor\mathrm{allowedLoss}(p)-\mathbf1_{p\in P}\,\mathrm{gain}(p)\right\rfloor .
$$
Its squared archimedean norm contributes $2\log q_*=2\sum e_p\log p$. The same exponents enter its $p$-adic absolute values, $|q_*|_p=p^{-e_p}$. Thus the subtraction of the aggregate gain in A must survive the finite-index calculation on the scaled forms. The native Euler factors give an arithmetic product and the measured layered Gram below determines its squared-volume change. To deduct that gain in the full physical source still requires the signed comparison with that source’s MAIN. [Compact common height and remainder](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Endgame/ShortAndEnough.lean#L30-L70) · [Scaling and index on the same family](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Endgame/ShortAndEnough.lean#L139-L171).

**A finite-index requirement that the compact proof removes.** In the readable `TwistedLattice.IndexLe`, one matrix at each $\iota$ clears every eligible twist. In the compact `Data.IndexLe`, the budget $e_\ell$ is fixed with $\sum_{\ell\in U}e_\ell\le\delta$ for every finite $U$, and the quantifiers on a retained family $y$ are
$$
 \forall\ell,\iota,\vartheta\ (\ell\nmid\mathrm{levelNorm}(\vartheta)),\quad
 \exists U_{\ell,\iota,\vartheta}:\quad |\det U_{\ell,\iota,\vartheta}|_\iota\ge e^{-e_\ell},
 \qquad \Theta_\vartheta(U_{\ell,\iota,\vartheta}y)_i\text{ integral for every }i.
$$
Here $\ell$ is prime. The log weight is already included in the compact $e_\ell$. A single clearing matrix valid for all twists is therefore dispensable. For example, the two lattices $p\mathbb Z\oplus\mathbb Z$ and $\mathbb Z\oplus p\mathbb Z$ each cost $\log p$ on the standard two-column family. Clearing both with one matrix costs $2\log p$. In compact C, `heightLe_volume_rows` uses the index witness at the one fit twist $\vartheta_\iota$ selected for each $\iota$. A direct adaptation of that proof can specialize the local work to this chosen fit family, provided it still proves its fit properties and the opposite volume-ratio height. The retained columns, all-column integrality at the chosen twist, common summable budget and archimedean comparison at every embedding remain necessary for that argument. [Readable index](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/Lattices/TwistedLattice.lean#L155-L164) · [Compact index](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Endgame/ShortAndEnough.lean#L128-L141) · [Use of the chosen twist](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Endgame/LongForms.lean#L39-L71).

### Recovery in native height coordinates and its exact denominator cost

On the full native dyadic host let $T_pu(t)=u(t+2\operatorname{Frob}_{p,H})$, $D_p=I-p^2 T_p$, and $B_p=p^{-2}D_p$. The two active reads at powers one and three give exactly $p^{-3}D_pa(t)$ at their common width. Since translation permutes the host coordinates, $(1-p^{-2})\lVert u\rVert_2\le\lVert B_pu\rVert_2\le(1+p^{-2})\lVert u\rVert_2$. For any ordered list of distinct primes the product $B$ obeys

$$\tfrac12\lVert u\rVert_2\le\lVert Bu\rVert_2\le2\lVert u\rVert_2.$$

Indeed $1+p^{-2}\le(1-p^{-2})^{-1}$, and the product over all integers from 2 to $N$ of $1-j^{-2}$ equals $(N+1)/(2N)$. Thus $B$ preserves the rank of every input frame. For any independent $n$-column height matrix $Y$, the quadratic forms satisfy $Y^*Y/4\le (BY)^*(BY)\le4Y^*Y$. Conjugating by $(Y^*Y)^{-1/2}$ shows that the logarithmic Gram determinant changes by at most $2n\log 2$. The norm estimate is `nativeDyadic_normalizedHeightShift_chain_norm`. The Gram consequence is a paper deduction for the ordinary Euclidean metric on the height coordinates.

For a single prime, $D_pU\equiv U\pmod{p^2}$ entry by entry. If $p^{-2}D_pU$ is integral, every entry of $U$ is divisible by $p^2$. Every retained $n$-row minor is therefore divisible by $p^{2n}$, as stated in `nativeDyadic_normalizedHeightShift_clearing_minor`. On the standard coordinate frame $p^2 I_n$ attains the bound. For the full host of dimension $D$, scalar normalization lowers the log Gram by $4D\log p$ and charges $2D\log p$ in $\delta$. The combination $V+2\delta$ is exactly invariant. For example, on a four-element cyclic host with shift by two and $p=3$, $|\det D_p|=6400$ and $|\det B_p|=6400/6561$. Both corrected log volumes equal $2\log 6400$.

For any list $P$ of distinct primes up to $Z$, the single scalar $M=\prod_{p\in P}p^2$ clears the images of **every** integral height column simultaneously. Its logarithm is $2\sum_{p\in P}\log p\le2(\log4)Z$. The retained frame therefore has a common denominator allowance $\delta/n\le2(\log4)Z$ in the standard height lattice. This is an upper allowance for the composite. A later factor can have valuation at an earlier prime. For the universally active range $2p^3\le x$, take $Z=\lfloor(x/2)^{1/3}\rfloor$. The doubled finite price per retained column is at most $4(\log4)(x/2)^{1/3}$. The declaration `nativeDyadic_normalizedHeightShift_chain_denominator` proves integrality and the logarithmic allowance.

**The direct same-prime payment fails on the outstanding thick first primes.** For $x\ge4$ and an integer $p>\sqrt{x}$, one has $p\ge3$ and $p^3\ge3x\ge x+1+2\sqrt x$. The frozen rounded-width cut vanishes beyond this last threshold. Thus at every thick site in the outstanding first-prime range the third cut is exactly zero. The two-active-read identity cannot recover that first cut there. The declaration is `nativeLedger_highPrime_thick_thirdCut_zero`. A cross-prime transport would need a signed inequality attaching the accessible small-prime gain to these different large-prime cuts and the exact MAIN on the same frame. A Euclidean rank certificate alone contributes no such signed term. [Native height operator and prices](../RHLean/Analysis/AlpogeThin/NativeDyadicShiftedWidthRows.lean) · [Original rounded thick cuts](../RHLean/Analysis/AlpogeThin/NativeExistingRecoveryPayment.lean).


### Two different first primes at one measured thick site

Take the actual unramified primes $\sqrt x<p\le x-1$ of the thick binary Frobenius colour. The finite set of addresses is $(t,p)\in TT\times P$. Assign an address to $y=t+\operatorname{Frob}_{p,H}$. Addresses at one $y$ have exactly the same full positive partner. For a fixed translate $u$ they are all thick precisely when $y\in u+T_2$. This alignment uses the original measured width at that $u$ and row $j$.

Reverse increasing prime order among the addresses with each $y$. This defines one involution on all addresses. Its two-cycles have disjoint endpoints. A fibre has at most one fixed point, since a reversed index $i$ is fixed exactly when $2i+1$ is the fibre size. Two different addresses in a fibre necessarily have different primes. Consequently the unmatched addresses $J$ satisfy
$$\lvert J\rvert\le\lvert H\rvert,\qquad \sum_{(t,p)\in J}\log p\le\lvert H\rvert\log x.$$
The proof constructs the matching without a prime-distribution hypothesis or an extra supply of tops. Its declaration is `nativeDyadic_firstPrime_sameWidth_matching`.

For every unpaired address the sum of the **thick saving** over translates has exactly $\lvert T_2\rvert$ terms per measured row. The original kernel weight is $2\log p$ and $\min(a_t/p,v)\le2b$. After summing the $m$ rows, averaging on $H$ and dividing by $Q$, the exceptional saving is at most $8(\lvert H\rvert/\lvert TT\rvert)\log x$. For the whole thick ASK cut the corresponding allowance is $8(\lvert H\rvert/\lvert TT\rvert)\sqrt{x}\log x$, since $a_t/p\le(x+1)b/\sqrt{x}\le2b\sqrt{x}$. The physical top-density hypothesis gives $\lvert H\rvert/\lvert TT\rvert\le2x^{\varepsilon/8}$. Both prices therefore fit $O_\varepsilon(x^{1/2+9\varepsilon/8})$. The omitted endpoint band $x-1<p<x$ contains at most one integer per top and has normalized saving $\le8\log x$. These allowances follow by finite summation of the matching bound and `alpogeNativeThickColour_translate_count`.

On a two-cycle order the primes $p<r$ and write $U_p=(a_t/p-v)_+$ and $U_r=(a_s/r-v)_+$. The original bound $v\le b+h\le b(1+1/x)$ eventually ensures that both first cuts are active for $r\le x-1$. Thus
$$pr(U_p-U_r)=r a_t-p a_s\ge b\{x(r-p)-p\}>0.$$
For integral heights its reductions modulo $p$ and $r$ read $r a_t$ and $-p a_s$, respectively, each with an invertible coefficient. The two reductions belong to the same measured pair. Even the actual logarithmic weights preserve a uniform signed margin. For $r-p\ge2$ and $\log p\ge3$,
$$pr(\log p\,U_p-\log r\,U_r)\ge b(x-2).$$
Indeed $\log(r/p)\le(r-p)/p$, $U_r\le(x+1)b/r$ and the preceding bound gives a lower numerator of $b[(x(r-p)-p)\log p-(x+1)(r-p)]$. This is at least $b(x-2)$. The two declarations are `nativeDyadic_sameWidth_firstPrime_signed` and `nativeDyadic_sameWidth_firstPrime_weighted_gain`.

The measured ASK sums both endpoints with positive kernel weights. Using the certified difference as a payment for the signed MAIN requires an independent bound for the sum of the remaining endpoints or an integral short-form realization giving them the subtractive sign. The arithmetic matching and its positive margin alone do not assert that connection. On these same-prime-power sites the completed estimates now price the unmatched part and remove endpoint multiplicity from the paired difference. In Sernau the corresponding link has two steps: `mainAmount_sub_add_two_mul_sum_gain` evaluates the unnormalized archimedean exponent with $+2\sum_p g_p\log p$, then `log_invGainFactor_le` and integrality of the very same forms justify subtracting that amount. A scalar chosen to cancel the gain may increase the finite denominator in C. [Archimedean gain identity](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/UpperBound/Size/ArchimedeanSize.lean#L139-L184) · [Normalization of the same forms](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/ShortAndEnough.lean#L265-L286).

Ordering each fibre by its prime before reversal gives a stronger aggregate estimate. This is possible because the prime determines the top within its fibre. Let $m_y$ denote the number of addresses over $y$, and let $\mathcal G$ be the sum over matched thick endpoints of the original smaller-prime weighted cut minus the larger-prime weighted cut, including the kernel factor 2, the $m$ rows and the full-host translate average. If $\log p\ge8$, $r\le x-1$, and $g=r-p\ge2$, the explicit lower numerator above is at least $bxg\log(p)/4$. Indeed $xg-p\ge xg/2$ and $1+1/x\le\log(p)/4$. Hence each pair contributes at least $bg\log(x)/(8x)$ before the common kernel factor. Its site is thick on exactly $\lvert T_2\rvert$ translates.

The increasing list of primes over $y$ has spacings of at least two. Pairing its $i$th prime with its $(m_y-1-i)$th prime gives
$\sum_{\mathrm{pairs}\text{ over }y}(r-p)\ge2\lfloor m_y^2/4\rfloor\ge(m_y^2-1)/2$. Cauchy–Schwarz and $\sum_y m_y=\lvert TT\rvert\lvert P\rvert$ now give the following paper consequence of the ordered matching and weighted margin:
$$
\boxed{\frac{\mathcal G}{Q}\ \ge\ \frac{\log x}{4x}
\left(\frac{\lvert TT\rvert}{\lvert H\rvert}\lvert P\rvert^2-
\frac{\lvert H\rvert}{\lvert TT\rvert}\right).}
$$
The signed difference enters the actual thick sum with a negative coefficient if the two endpoint contributions are written as twice the smaller-prime contribution minus their difference. Both sides of that identity use the same observed endpoints. In the selected-pair window, the sharp estimate for the three twists and the unconditional prime number theorem give $\sum_{p\in P}\log p=(1/4+o(1))x$, hence $\lvert P\rvert\gg x/\log x$. The displayed lower bound and the original top density therefore give $\mathcal G/Q\gg_\varepsilon x^{1-\varepsilon/8}/\log x$ for large anchors. The term twice the smaller-prime sum and the exact signed MAIN still have to be compared. In particular a power saving in their leading mismatch would be needed to turn this lower allowance alone into a square-root remainder.

### Primitive scalar evaluations on a single integral height profile

At the square clock take $b=\exp(x^\varepsilon)$, $1\le R\le x$ and the original collar length $W=xb/(xR x^{13})$. The selected dyadic host has $\lvert H\rvert\le x^3$ eventually. Since $x^{17}\le b$ eventually, $\lvert H\rvert\le W\le b$. Index $H$ from 0 and set $a_t=\lceil xb\rceil+\operatorname{index}(t)$. These are distinct positive integers in $[xb,xb+W)$ on every large anchor, and
$$\log a_t\le x^\varepsilon+\log(x+1).$$
This is `nativeSquareClock_injectiveHeights_log_eventually`. The construction has no product of the selected primes in its collar requirement.

For every matched address use its actual difference $D=r a_t-p a_s$ from the common first-prime cuts. At any depth $k$ it is a unit modulo $p^k$ whenever $p\nmid a_t$. Its inverse gives an admissible scalar dual with evaluation 1 in that residue ring. The exceptional primes at top $t$ satisfy the simultaneous bound $\sum_{p\mid D}\log p\le\log a_t$, since they divide the single integer $a_t$. Both conclusions are supplied by `nativeDyadic_firstPrime_paired_unit_price` and apply to the same height profile for every matched prime. No invertibility or per-prime height choice is a premise.

Drop an entire pair whenever either endpoint fails this unit test. Throughout the band $\sqrt x<p,r\le x$, the other prime's logarithm is at most twice the failing endpoint's logarithm. Disjointness makes the total discarded log weight at most $3\sum_t\log a_t$. The exact translates and original divisor used above then price the discarded thick saving by $24\max_t\log a_t$, and its entire thick ASK by $24\sqrt x\max_t\log a_t$. At the square clock this is $O_\varepsilon(x^{1/2+\varepsilon})$. Thus the aggregate signed margin survives deletion of nonunit pairs with an independently bounded square-root error. The remaining integral-section test is stronger: it must realize the scalar dual on the physical family while satisfying all competing edge conditions in the native lattice. Its simultaneous physical embedding and its denominator in Sernau C are open.

The cost of imposing **all** the associated vanishing conditions can also be calculated exactly. Let $P_t$ be the primes served at $t$ by the retained disjoint pairs. For each served address use the actual matched prime $r$ and top $s$. On an integral variation $u$ its row is $r u_t-pu_s$. Modulo $p$ this is $r u_t$ with $r$ a unit. Thus at each prime the rows for distinct served tops have independent reductions, and the simultaneous kernel is
$$\bigoplus_{t\in TT}M_t\mathbb Z e_t,\qquad M_t=\prod_{p\in P_t}p.$$
Every integral clearing matrix has determinant divisible by $\prod_t M_t$. The single diagonal matrix with entries $M_t$ attains the index. The exact Lean declaration is `nativeDyadic_firstPrime_matching_kernel_det`. This determinant measures the index of the height-coordinate vanishing lattice. Sernau's $\delta$ measures denominators on the chosen forms. Equating the two needs a map between those lattices.

On the square clock discard the fixed points and the pairs with a nonunit endpoint as above. The logarithm of the exact index per height coordinate then lies between
$$\sum_{p\in P}\log p-\frac{\lvert H\rvert}{\lvert TT\rvert}\log x-
3\max_t\log a_t\qquad\text{and}\qquad\sum_{p\in P}\log p.$$
At the selected-pair anchors both are $(1/4+o(1))x$. In particular, treating this whole logarithmic index directly as an error per height dimension costs order $x$. Increasing the number of primes in the matching does not give a square-root price that way. A signed upper norm estimate must recover this term with the correct coefficient on the same columns, or an actual section map must realize the valuations at a smaller denominator cost. The determinant calculation leaves that precise comparison open.

For arbitrary required depths the row map still has full simultaneous image. Fix $p$ and write $F_p u(t)=r_tu_t-pu_{s(t)}$ with $p$ coprime to every $r_t$. Unserved coordinates can be filled with $r_t=1$. Over $\mathbb Z/p^K$ the iteration $u_{j+1}(t)=r_t^{-1}(y_t+pu_j(s(t)))$ makes every residual divisible by $p^j$ after $j$ steps. This proves simultaneous surjectivity at depth $K$ for every target vector and any pattern of repeated second tops. Its declaration is `nativeDyadic_firstPrime_depth_surjective`.

A finite-index consequence attaches the measured thick cuts directly to a native height lattice. Fix a single measured translate and row. At each served thick address prescribe $k_{p,t}=\lfloor (a_t/p-v)_+\rfloor$ and prescribe zero at the other addresses. Reduce the surjective map at $K_p=\max_t k_{p,t}$ to the separate depths. Integral coordinatewise CRT now gives a surjection from $\mathbb Z^{TT}$ onto $\prod_{p,t}\mathbb Z/p^{k_{p,t}}$. The kernel $L_{u,j}$ is the intersection of these actual two-top congruences. As a result
$$\log[\mathbb Z^{TT}:L_{u,j}]=\sum_{p,t} k_{p,t}\log p.$$
Averaging $2\log[\mathbb Z^{TT}:L_{u,j}]$ over the same $u$ and summing the rows approximates the served high thick ASK with an independently bounded nonnegative normalized error at most $4\vartheta(x)/b\le4(\log4)x/b$. Each address loses less than a single $\log p$ before weighting by 2, and occurs on exactly $\lvert T_2\rvert$ translates. The submitted declaration `nativeDyadic_matchedRead_joint_index` computes this joint kernel index for arbitrary separate depths on the actual top coordinates. The declaration `nativeDyadic_firstPrime_measured_logIndex_price` bounds the row-level rounding error by one log weight per served address on exactly that mask. The normalized bound follows by the stated translate count. The admissible base heights above stay fixed. The computation bounds the rounding discrepancy; the signed difference between the measured log indices and the common archimedean MAIN still needs an independent estimate on the chosen sections.

An explicit integer supplies the high first-prime depths without reading the individual widths. For $x\ge4$, $b\ge1$, put $A=\lceil xb\rceil$, $B=\lfloor b\rfloor$. Let $P$ be the unramified thick-colour first primes $\sqrt{x}<p<x$ in the native cutoff. Define
$$J_p=(v_p(A!)-B)_+,\qquad D_P=\prod_{p\in P}p^{J_p}\mid A!.$$
This one integer is independent of the top, row, translate and measured widths. On every actual thick read at width $v$ the Legendre bounds $A/p-1\le v_p(A!)\le A/(p-1)$ and the Lipschitz constant one of the positive part give
$$\left|J_p-(a_t/p-v)_+\right|\le\frac{A}{p(p-1)}+\frac{|A-a_t|}{p}+|v-b|+2.$$
The pointwise declaration is `nativeDyadic_firstPrime_factorial_depth`. In the frozen ledger $|A-a_t|\le b$ and $|v-b|\le b\eta+h$. For these first primes the real kernel weight is $2\log p$ and the thick row occurs on exactly $|T_2|$ translates. For the sum $S_{P,\mathrm{thick}}$ of their ASK contributions, dividing by the original $Q$ gives
$$\left|\frac{S_{P,\mathrm{thick}}}{Q}-\frac4b\log D_P\right|\le
\frac{8(x+1)\log x}{\sqrt{x}}+4(\log4)\left(\sqrt{x}+x(\eta+h/b+2/b)\right).$$
Indeed $A/b\le x+1$, $\sum_{p\in P}\log(p)/(p(p-1))\le\log(x)/\lfloor\sqrt{x}\rfloor$, $\sum_{p\in P}\log(p)/p\le\vartheta(x)/\sqrt{x}$ and $\vartheta(x)\le (\log4)x$. At the square clock $b=\exp(x^\varepsilon)$ and on the frozen spacing $\eta\le1/(2\sqrt{x})$, $h/b\le1/x$ eventually, so the price is $O(\sqrt{x}\log x)$ uniformly in the measured family. This aggregate estimate is a paper consequence. The pointwise result supplies the arithmetic depth for each prime; the unresolved signed estimate must pay $4\log D_P/b$ together with the remaining ASK terms against the common MAIN on the same family.

The squarefree wheel removes the higher prime powers in that approximation and permits a polynomial cutoff. For the **same** $P$ and physical widths take $c=\lfloor\sqrt{x}\rfloor$, $N_w=\lfloor cx\rfloor$ and $W_P=\prod_{p\in P}p$. Form the integer
$$D_w=\frac{\prod_{n=1}^{N_w}\gcd(n,W_P)}{W_P^c}.$$
When a prime $p$ is admitted, every multiple of $p$ in the prefix contributes its single new factor $p$. This counts all downstream occurrences, including integers shared with another admitted prime. Since $p<x$, there are at least $c$ multiples. Thus $D_w=\prod_{p\in P}p^{\lfloor N_w/p\rfloor-c}$ exactly. Moreover $N_w\le x^{3/2}$, so no integer in this prefix has three distinct prime divisors greater than $\sqrt{x}$. Unlike two-cuts-at-one-prime, this accounts for the entire first-prime band. The product identity is `nativeDyadic_firstPrime_wheel_product`.

Let $k_p=\lfloor N_w/p\rfloor-c$. The identity $\lfloor N_w/p\rfloor=\lfloor cx/p\rfloor$, $x\le a_t/b\le x+1$, and the Lipschitz constant one of the positive part give on every original thick read
$$\left|\frac{(a_t/p-v)_+}{b}-\frac{k_p}c\right|\le\frac1p+|v/b-1|+\frac1c.$$
This is `nativeDyadic_firstPrime_wheel_depth`. The auxiliary $c$ counts integer multiples. All measured contributions still use the original $b,Q$. The declaration `nativeLedger_high_wheel_normalized_price` sums the rounded discrepancies over the actual thick mask, all original tops and rows with the exact normalized multiplier. The Chebyshev estimate $\vartheta(x)\le(\log4)x$ gives the following bound
$$\left|S_{P,\mathrm{thick}}/Q-(4/c)\log D_w\right|
\le 4(\log4)\left(\sqrt{x}+x(\eta+h/b+1/c)\right).$$
For $x\ge4$, $c\ge\sqrt{x}/2$. The frozen spacing and collars give $\eta\le1/(2\sqrt{x})$ and $h/b\le1/x$ eventually. The error is then at most $4(\log4)((7/2)\sqrt{x}+1)$. In particular the whole high thick first-prime price is $O(\sqrt{x})$ and the common arithmetic prefix has length at most $x^{3/2}$, independently of the exponential height scale. At this point the signed problem is to bound $(4/c)\log D_w+(S(v)-S_{P,\mathrm{thick}})/Q$ by $K_\varepsilon x^{1/2+C\varepsilon}$ through an independent upper norm and lower determinant comparison. The positive quotient supplies the first term. Its construction alone gives no sign for the second.

The same wheel yields primitive integral columns and their real Gram determinant together. At each downstream integer $1\le n\le N_w$ take
$$C_n=\prod_{p\in P:\;p\mid n,\;cp<n}p.$$
Their product is $D_w$ and $1\le C_n\le n$. Partition the actual prefix into consecutive blocks of length $c$, allowing a shorter last block. The $C_n$ in each block are pairwise coprime because a shared prime would divide a positive difference smaller than $p$. This arithmetic supplier is `nativeDyadic_firstPrime_wheel_block_coprime`. Choose the first integer $n_0$ of each block as pivot. For each other integer $n_i$ take the column $C_{n_i}e_i-C_{n_0}e_0$. Its two entries lie in the measured wheel's integral coordinate lattice. Prescribing arbitrary integral pairings $y_i$ with these columns is possible simultaneously: choose $v$ with $C_{n_0}v\equiv-y_i\pmod{C_{n_i}}$ by CRT, then take $u_i=(y_i+C_{n_0}v)/C_{n_i}$. This is `nativeDyadic_firstPrime_wheel_block_dual`. In particular the columns are independent and primitive. The direct sum loses exactly $J=\lceil N_w/c\rceil\le x+1$ dimensions across the full prefix, including blocks of length one. Each prime can affect many blocks while the rank loss is charged only once per block.

Let $B_j$ be these very columns in the ordinary real coordinate metric on block $j$. The rank-one determinant formula gives
$$\det(B_j^{\mathsf T}B_j)=\left(\prod_{n\in j} C_n\right)^2\sum_{n\in j}C_n^{-2}.$$
The factored Gram declaration is `nativeDyadic_firstPrime_wheel_block_gram`. The final sum lies between $N_w^{-2}$ and $c$. Thus, with $V_w=\sum_j\log\det(B_j^{\mathsf T}B_j)$,
$$\left|\frac{2V_w}c-\frac4c\log D_w\right|\le\frac{4J}{c}\log N_w
=O(\sqrt{x}\log x).$$
Together with the measured wheel price, this attaches the **positive high thick ASK** to the Gram volume of one explicit primitive family at a permitted loss. Dual existence uses the same columns. The simultaneous integer duals can have large archimedean entries. This calculation supplies no shortness estimate for those duals in the physical metric of #1201. The unpaid one-sided comparison on the original data is $2V_w/c+(S(v)-S_{P,\mathrm{thick}})/Q\le K_\varepsilon x^{1/2+C\varepsilon}$. It requires an independent relation with the signed MAIN and the other terms. The finite sum and normalization in this paragraph are paper consequences of the three submitted block theorems.

The missing column of each block admits a **short integral unimodular completion**. Write $M=\prod C_i$ and $z_i=M/C_i$ on a block of length $\ell$. These $z_i$ are the entries of its primitive normal, up to a common orientation. Select $0\le u_i<C_i$ with $z_i u_i\equiv1\pmod{C_i}$. The sum $T=\sum_i z_i u_i$ equals $1+rM$, since its residue is one modulo every pairwise coprime $C_i$. Also $0\le T\le\ell M$ gives $-1\le r\le\ell$. At one pivot replace $u_0$ by $w_0=u_0-r C_0$ and keep $w_i=u_i$ elsewhere. Then $z\cdot w=1$ and $|w_i|\le(\ell+1)C_i$. This simultaneous, polynomial-size integral witness is `nativeDyadic_firstPrime_wheel_short_completion`. Its actual consecutive-wheel specialization `nativeDyadic_firstPrime_wheel_block_supplied` constructs the simultaneous dual and the completing column together, proves the coprimality premises from prime admissions, and bounds each coefficient by $(\ell+1)n_i$ at the actual downstream integer.

The determinant after adjoining $w$ has absolute value one by cofactor expansion. Its ordinary norm is at most $\sqrt{\ell}(\ell+1)N_w$. Across all blocks, even charging this norm once per completing column costs $O(\sqrt{x}\log x)$ after division by $c$. Moreover the distance from $w$ to the span of the other columns is exactly $1/\lVert z\rVert$, and $\lVert z\rVert^2=\det(B_j^{\mathsf T}B_j)$. The sum of log squared distances therefore equals $-V_w$. This supplies a simultaneously realized opposite volume term in the native wheel metric. The missing signed comparison is whether the **original** remaining source $(S(v)-S_{P,\mathrm{thick}})/Q$ is at most that projected log volume times $2/c$, up to the permitted loss. No comparison between the original signed MAIN and this orthogonal projection has been assumed.

There is also an aggregate bound for the **integral duals** on these same blocks. Let $U=[B_j\;w]$ and write its integral inverse transpose as $U^{-\mathsf T}=[Y\;z]$. Then $B_j^{\mathsf T}Y=I$ and $w^{\mathsf T}Y=0$. The maximal minor of $Y$ omitting row $i$ is $\pm w_i$, by the complementary-minor identity and $|\det U|=1$. Cauchy–Binet gives
$$\det(Y^{\mathsf T}Y)=\sum_i w_i^2\le\ell(\ell+1)^2 N_w^2.$$
Thus the total *ordinary* dual log Gram divided by $c$ is $O(\sqrt{x}\log x)$ for an integral dual simultaneously realizing every retained column. The submitted exact integral Gram declaration is `nativeDyadic_firstPrime_wheel_dual_gram`. Its normalized paper consequence prices joint covolume even when an individual dual vector is long. Moving that bound to the native signed height metric, or paying its distortion against the common MAIN, remains necessary.

### Measured thick cuts, prime admission and the remaining signed count

Fix a real anchor on the selected pair and keep the original divisor, heights, Frobenius, inertia and cutoff. At one thick site of a fixed translate and row, order its interior unramified first-prime addresses by increasing prime. Each prime occurs at most once there, because the prime and partner determine the top. Write $U_i=(a_{t_i}/p_i-v)_+$, where $v$ is the site's common measured or rounded width. For $0<b$, $xb\le a_t\le(x+1)b$, $v\le b(1+1/x)$ and $\sqrt{x}<p_i\le x-1$, the previous two-prime comparison gives $U_0>\cdots>U_{\ell-1}>0$. The disjoint layers of these actual intervals have lengths $\lambda_i=U_i-U_{i+1}$, with $U_\ell=0$. The integral layer coordinates are obtained from the nested interval indicators by consecutive differences.

At the native square-block endpoint $x=X_R=R^2-1$, $R\ge2$, the inequalities $(R-1)^2\le X_R<R^2$ give $c=R-1$ exactly. The wheel prefix ends at $(R-1)(R^2-1)$ and the interior first primes are $R\le p\le R^2-2$. Away from the endpoints use $c=\lfloor\sqrt x\rfloor$ at each real anchor required by #1205. [Native square multiplicity](../RHLean/Analysis/AlpogeNativeSquareMultiplicity.lean)

Take the wheel factors $D_i=p_i^{\lfloor\lfloor cx\rfloor/p_i\rfloor-c}$, $c=\lfloor\sqrt{x}\rfloor$. They count the downstream multiples on the earlier wheel and are pairwise coprime. On the layer coordinates take $D_i e_i-D_0e_0$ for $i>0$. These columns realize arbitrary integral dual readings simultaneously, with one missing dimension per nonempty fibre. In this lattice the image of the integral readout map has index one. Give the layers their observed lengths as the diagonal metric. With squared covolume $V_D$ and baseline $V_1$ (all factors one), the exact determinants satisfy

$$
 V_D=\Big(\prod_i\lambda_iD_i^2\Big)\sum_i(\lambda_iD_i^2)^{-1},\qquad
 0\le 2\sum_i\log D_i-\log(V_D/V_1)\le 2c\sqrt{x}\log x .
$$

The ratio after division by $\prod_iD_i^2$ is a weighted average of the $D_i^{-2}$ with positive weights $\lambda_i^{-1}$. The common product of the measured lengths cancels, however small the shortest layer. Each $\log D_i\le c\sqrt{x}\log x$. These statements include $\ell=1$, with squared covolume one in dimension zero. With $K=|TT|m|T_2|$, the multiplier on the sum of the log ratios is $2/(cK)$, because one physical first-prime read carries $2\log p$ and the divisor includes $1/2$. There are at most $|H|m|T_2|$ nonempty thick fibres. The total one-column loss is therefore at most $4(|H|/|TT|)\sqrt{x}\log x$, in addition to the independently priced wheel rounding. The dyadic top-density condition bounds $|H|/|TT|$ by $2x^{\varepsilon/8}$. The finite fibre statements are in [NativeMeasuredCutGram.lean](NativeMeasuredCutGram.lean). The summation here uses the original translate multiplicity.

The earlier unimodular completion also applies to these pairwise coprime $D_i$ in the **measured** metric. Let $B_D$ be the difference columns and $w_D$ the integral completing column. Cofactor expansion with the proved Bézout identity gives $|\det[B_D,w_D]|=1$. Thus the completed squared Gram determinant for $\Lambda=\operatorname{diag}(\lambda_i)$ is $\det([B_D,w_D]^\mathsf{T}\Lambda[B_D,w_D])=\prod_i\lambda_i$. If $d_D$ is the distance of $w_D$ to the span of $B_D$ in this metric, the Schur complement gives $V_Dd_D^2=\prod_i\lambda_i$. Completing the unit-factor columns in the same metric yields the exact opposite comparison
$$
 \log(d_D^2/d_1^2)=-\log(V_D/V_1).
$$
The existing coefficient estimate $|(w_D)_i|\le(\ell+1)D_i$ also gives $\lVert w_D\rVert_\Lambda^2\le(\ell+1)^2(\max_i D_i)^2 U_0$. These are finite-dimensional deductions from the checked Gram and integral completion statements. The original signed MAIN has yet to be bounded by this opposite projected volume on the same sections. [Integral completion](../RHLean/Analysis/AlpogeThin/NativeDyadicShiftedWidthRows.lean) · [Measured Gram](NativeMeasuredCutGram.lean).

There is a precise limit to a direct application of Sernau B and C. On a fibre with $\ell<b^2/4$, the retained $\ell-1$ columns fall strictly below $(1-4/b^2)\ell$. Patching together these fibres preserves that deficit. An integral completion restores the dimension. Proving the required norm of the completed family with the arithmetic MAIN, or pricing the missing direction by an independent signed estimate, is still necessary. The readout index above belongs to the layer lattice. Sernau's index quantifies over all required prime-adic embeddings and twists of his sections.

The complete signed row admits a separate comparison on these same physical data. Write $X'=\exp(x^{\varepsilon/3})$, choose $s=3\min_{t\in TT}a_t/X'$, and cap the raw widths by $s$ before applying the original lower log grid. Denote the resulting widths by $l_\rho$ and the original rounded widths by $r_\rho$. The cap leaves the physical thin sites fixed and puts every reference site in the all-thin range for every top. Each height and canonical character term in MAIN cancels exactly between these two rows. At the original cutoff $N$, their signed difference is

$$
 \frac{a_t}{|\Phi|}\sum_{\rho\in\Phi}\log(r_\rho/l_\rho)
 -
 \sum_{n=1}^{N}\sum_{g\notin\Phi} K_{ng}
 \min\!\left((a_t/n-l_{\rho(t,g)})_+,\ r_{\rho(t,g)}-l_{\rho(t,g)}\right).
$$

Here $K_{ng}$ includes $\Lambda(n)$, the inertia multiplicity and the real Frobenius weight. The selected pair bounds the reference row above by $4|H|a_t\exp(-x^{\varepsilon/8})$ at every sufficiently large anchor, uniformly in $N$. After summing and dividing by $Q$ its allowance is $8|H|(\bar a/b)\exp(-x^{\varepsilon/8})/\Delta\le 2/(x\Delta)$ under the frozen host cost. At each layer the logarithm is its length in log-width coordinates. Its swept prime mass is the integral of $e^u$ over the part of that same interval below $\log(a_t/n)$. [NativeSignedWidthSweep.lean](NativeSignedWidthSweep.lean)

This gives an explicit comparison for the two frozen thick levels $0<l\le r$ with unchanged positive thin widths. Use, for example, $l=L_\eta(s)$ and $r=L_\eta(b)$ at large anchors. Put $k_n^{10}=\sum_{h\in H}K_{n,((1,0),h)}$ and $\Psi_{10,N}(y)=\sum_{1\le n\le\min(N,\lfloor y\rfloor)}k_n^{10}$. Exactly $|T_2|$ translates serve each such colour and none serve the other binary colour. The same $|T_2|$ occurs in the logarithmic term since $|\Phi|=2|H|$. Finite summation and the substitution $y=a_t/e^u$ give the following **signed difference divided by the original $Q$**:

$$
 \frac{1}{|TT|b}\sum_{t\in TT} a_t
 \int_{a_t/r}^{a_t/l}\!\left(1-\frac{2\Psi_{10,N}(y)}{y}\right)\frac{dy}{y}.
$$

Here $r,l$ are physical units of width. They do not replace $b$ in $Q$. Thin terms cancel in the difference, while the all-thin reference price covers their original signed contribution. A one-sided upper bound for this displayed integral average on every real anchor would pay the remaining signed comparison on frames with these levels. The signed comparison between the actual and frozen thick widths is priced elsewhere in this ledger. The finite layer identity and row bound are formalized; the integral average above is their analytic and finite-sum consequence.

Equivalently, define $R_N(y)=2\sum_{n=1}^N k_n^{10}(1/n-1/y)_+-\log y$. The numerator for each top is exactly $a_t[R_N(a_t/r)-R_N(a_t/l)]$. The declaration `two_cutoff_eq` keeps the identical $N$ at both arguments. The theorem `frozen_top_excess_eq` performs the full translate, top and row summation with the original $Q$. On every selected `PairGood` pair, `pairGood_frozen_top_le` bounds the full frozen $S(r)/Q$ above by this same top average plus $8|H|A_{\max}e^{-x^{\varepsilon/8}}/(b\Delta)$. Its hypotheses give the far reference widths and the conductor bound directly; it assumes no signed estimate. This is the same orientation as Sernau's small-cutoff remainder minus its far-cutoff remainder. His count uses $\Lambda(n)(1-(n/d))\mathbf1_{n\equiv1\pmod{q_0}}$ and drift $y/\varphi(q_0)$. The native count uses $2k_n^{10}$ and drift $y$. Matching the kernel shape leaves the comparison of these counts to be proved. [Upstream count-error integral](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/Zeros/PrimeNumberTheorem.lean#L74-L115) · [Upstream two-cutoff reduction](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/OneSidedBound.lean#L27-L69).

The Fourier representation uses these same intervals. With $L=\log l$, $B=\max(L,\log\min(r,a_t/n))$ for $a_t/n>0$, the squared norm of $e^{u/2}\mathbf1_{[L,B]}(u)$ is its swept mass. For transform convention $\widehat f(\xi)=\int f(u)e^{i\xi u}du$, its transform is $(e^{(1/2+i\xi)B}-e^{(1/2+i\xi)L})/(1/2+i\xi)$. At a first-prime endpoint and $\xi=2\tau$, the phase is the native critical Perron multiplier times $p$ and the height phase $e^{2i\tau\log a_t}$. Plancherel uses $d\xi/(2\pi)$. This identifies the measured energy and its frequency weight. Positivity gives a nonnegative mass. To obtain the required lower bound for that mass one must compare it with the displayed logarithmic main term, with a uniform error at the square-root scale.

## The two sources

Fix $0<\varepsilon<1/52$ and a window exponent $A\ge1$. Take $e(x)$ and the pair $(q,d)$ for the window $[Y,Y^A]$ from `nativeConstructedDyadicGzPayment`. The pair stays fixed throughout that window. On its actual reciprocity host $H$, use a nonempty physical top set $TT$, nonempty thick set $T_2$, $m>0$, positive $b$, heights $a_t$, positive widths $w_{uj\rho}$, and the density, cutoff and width conditions of that theorem. Write

$$
\Delta=|T_2|/|H|,\qquad Q=|TT|mb\Delta/2,\qquad N=\lceil A_{\max}/\beta\rceil .
$$

Here $a_t\le A_{\max}$ and $\beta$ is the original lower width bound. Require $x\ge1$ and the original height localization $x\le a_t/b\le x+1$ for every top. The upper endpoint follows from $A_{\max}/b\le x+1$. The original height window $xb\le a_t\le xb+xb/(k\sigma)$ gives both endpoints when $k\ge x$ and $\sigma\ge1$.

Let $S(v)$ be the **sum over tops and rows** of the physical $\operatorname{Re}(\mathrm{ASK}-\mathrm{MAIN})$, averaged over the whole host subgroup. Define

$$
\begin{aligned}
G_{\rm native}(x)&=\sum_{n\le x}\Lambda(n)(x/n-1)-x\log x+(1+\gamma)x,\\
\eta&=\frac{b\Delta\sqrt{x}}{2A_{\max}},\qquad
v_{uj\rho}=\exp\!\left(\eta\left\lfloor\frac{\log w_{uj\rho}}{\eta}\right\rfloor\right),\\
G_{\rm comparison}(x)&=S(v)/Q .
\end{aligned}
$$

The widths $v$ are computed from the measured widths. Both sources of physical excess, $S(w)$ and $S(v)$, use the same heights, top and thick sets, rows, inertia, Frobenius, canonical character term and cutoff $N$. A lower grid endpoint may fall below $\beta$. Keeping $N$ fixed is part of the comparison. The comparison does not require the grid endpoints to be integral sections.

## The ledger

Use $C_d=4+\log 4$ and $r=x^{1/2+\varepsilon}$. Each row gives an upper allowance in the indicated direction.

| Transfer on this frame | Allowance before dividing by $Q$ | Normalized allowance | Independent supplier |
|---|---:|---:|---|
| $G_{\rm native}(x)$ to the mean of $G_{\rm native}(a_t/b)$ | $Q C_d$ | $C_d$ | Global arithmetic Lipschitz estimate with constant $C_d$ and mean absolute height displacement at most 1 |
| Mean of $G_{\rm native}(a_t/b)$ to $S(w)/Q$ | $Qr$ | $r$ | Selected dyadic analytic payment with the complete prime-power source and its original cutoff |
| $S(w)/Q$ to $S(v)/Q$ | $\lvert TT\rvert mA_{\max}\eta$ | $2A_{\max}\eta/(b\Delta)=\sqrt{x}$ | Monotonicity of each real ASK cut and the change in the signed MAIN logarithm |

Let $E_{\rm total}$ be the sum of the three raw allowances. The resulting statement is

$$
G_{\rm native}(x)\le G_{\rm comparison}(x)+\frac{E_{\rm total}}{Q},
\qquad
\frac{E_{\rm total}}Q=C_d+r+\sqrt{x}\le (6+\log4)x^{1/2+\varepsilon}.
$$

For $x\ge (4+\log4)^2$ the coefficient can be reduced to 3. All constants in this price are independent of the frame, the selected pair, and the window. The signed width comparison uses $v\le w$ and $0\le\log w-\log v\le\eta$. The real ASK decreases as the width increases. The remaining positive change in $S(w)-S(v)$ is at most $a_t\eta$ per row. Paying that charge before division accounts for the factor $2/\Delta$.

## Independent bound for the comparison source

Write $L_N=\sum_{1\le n\le N}\Lambda(n)/n$, and let $M_{utj}=\operatorname{Re}\mathrm{MAIN}(\ell,a_t,v_{uj})$. The complete kernel on this host gives

$$
G_{\rm comparison}(x)\le
\frac{1}{Q|H|}\sum_{u\in H}\sum_{t\in TT}\sum_{j=1}^m
\bigl[2a_t L_N-M_{utj}\bigr].
$$

Indeed the real ASK weights $K_{ng}$ are nonnegative with $\sum_{g\notin\Phi}K_{ng}\le2\Lambda(n)$, including at ramified prime powers. Each cut is at most $a_t/n$. Subtracting the exact MAIN preserves its character and logarithmic terms. For $N\ge1$, the existing unconditional estimate gives $L_N\le\log N+\log4+2$. These bounds use quantities defined independently of $G_{\rm native}$. They do not give a square-root bound for $G_{\rm comparison}$.

There is a concrete way to measure what the coarse upper bound discarded. For each row set $z_n=a_t/n$, $c_{t,g}=v_{uj,\operatorname{partner}(t,g)}$, and $k_n=\sum_{g\notin\Phi}K_{ng}$. Its exact saving against the upper bound $2a_t L_N$ for ASK is

$$
\sum_{n=1}^N(2\Lambda(n)-k_n)z_n
+\sum_{n=1}^N\sum_{g\notin\Phi}K_{ng}\min(z_n,c_{t,g}).
$$

This follows from $z-(z-c)_+=\min(z,c)$. Both terms are nonnegative and can be computed from inertia, Frobenius and the measured widths. A lower estimate for these savings must be compared with the signed MAIN on the **same** frame. The identity itself gives no lower estimate of the required size.

The physical thick mask gives an independent lower bound for part of the second saving. Define
$\beta_0=\beta e^{-\eta}$, $b_0=b e^{-\eta}$ and $k^{10}_n=\sum_{h\in H}K_{n,((1,0),h)}$.
For $z_{tn}=a_t/n$ put $P_c(z)=(z-c)_+$ and
$D_{tn}=P_{\beta_0}(z_{tn})-P_{b_0}(z_{tn})\ge0$.
All grid widths are at least $\beta_0$. A selected thick partner has grid width at least $b_0$ because $v\ge e^{-\eta}w$. For fixed $t$ and $g=((1,0),h)$ there are exactly $|T_2|$ translates $u$ which select $g$. Indeed $s+u-t=h$ gives the distinct solutions $u=h+t-s$ for $s\in T_2$. The other first-bit-one colour occurs zero times in the thick mask. This calculation uses the full subgroup supplied by the selected payment.

Writing $\mathcal M=|H|^{-1}\sum_{u,t,j} M_{utj}$, the resulting stronger comparison estimate is

$$
G_{\rm comparison}(x)\le
 \frac{2}{|TT|b\Delta}\sum_{t\in TT}\sum_{n=1}^N k_n P_{\beta_0}(z_{tn})
 -\frac{2}{|TT|b}\sum_{t\in TT}\sum_{n=1}^N k^{10}_n D_{tn}
 -\frac{\mathcal M}{Q}.
$$

To verify the bound, each cut is at most $P_{\beta_0}(z_{tn})-\mathbf1_{g\text{ selected}}D_{tn}$. Multiply by the native nonnegative weight, average in $u$, and sum the $m$ rows. The factor $\Delta$ in the thick saving cancels **exactly** against the original divisor. This yields an explicit negative contribution, calculated from the actual thick translates with coefficient $2/(|TT|b)$. The cutoff and signed MAIN still contain the complete original thin and ramified data. The two positive-part functions coincide below $\beta_0$, differ by $z-\beta_0$ between the two thresholds, and differ by $b_0-\beta_0$ above $b_0$. These facts specify the contribution of each prime power. The bound for the sum over all translates of a fixed physical colour is formalized in `alpogeNativeLowerLogWidth_thick_translate_cuts_le`. The displayed aggregation multiplies those inequalities by the native weights and sums over colours, prime powers and rows. This last aggregation is a paper derivation.

### A finite signed bound using the native height, mask and kernel data

The full signed comparison also has an upper bound that preserves the interaction between the logarithm and the prime-power cuts. It can be evaluated without knowing the individual widths. Set $a_*=\sum_t a_t/|\Phi|$, $M_0=\sum_t a_t(\log a_t-1-\gamma+\operatorname{Re}\ell(\chi_C))$, with the sums over $TT$. For each positive site $\rho$, take the unique nonpositive-mask colour $g(t,\rho)$ whose partner is $\rho$. It exists because the partner is translation by $((1,1),t)$. Define the following function on $v>0$:

$$
F_\rho(v)=\sum_{t\in TT}\sum_{n=1}^N K_{n,g(t,\rho)}(a_t/n-v)_+ + a_*\log v .
$$

The same $v$ occurs for **all** tops and all prime powers at a site in a given row. Directly summing the complete signed source gives
$S(v)=|H|^{-1}\sum_{u,j}[\sum_{\rho\in\Phi} F_\rho(v_{uj\rho})-M_0]$.

Let $L(c)=\exp(\eta\lfloor\log c/\eta\rfloor)$, $X'=\exp(x^{\varepsilon/3})$ and $a_{\min}=\min_{t\in TT}a_t$. The native thick and thin conditions put the rounded widths in the respective intervals

$$
I_B=[L(b),L(b+h)],\qquad I_T=[L(\beta),L(3a_{\min}/X')].
$$

For the thin interval, apply the thin inequality to the inverse partner of $\rho$ for each top. The equivalence between a thick partner and a thick colour is `alpogeNativeFreezing_partner_mem_iff`. The logarithmic rounding function is increasing in the weak sense. Both intervals used by the physical profile are compact and strictly positive.

For either interval $I$, compute an upper bound $U_\rho(I)$ as follows. Split $I$ at the finitely many interior thresholds $a_t/n$. On each resulting open interval the active weight $k=\sum_{t,n:\ a_t/n>v}K_{n,g(t,\rho)}$ is constant and $F'_\rho(v)=a_*/v-k$. Evaluate $F_\rho$ at the two endpoints and, when $k>0$, at $v=a_*/k$ if it lies in the interval. Take the largest value, including the value at a singleton interval. This computes the continuous maximum exactly. Rounding each candidate on both sides to grid points in $I$ and retaining the endpoints also gives the exact maximum over allowable grid values, by monotonicity on either side of a stationary point. The continuous maximum already suffices.

Define $d_\rho=\Delta$ on sites with bits $(0,1)$ and $d_\rho=0$ on sites with bits $(0,0)$. The same translate count now yields an explicit signed upper bound independent of the individual widths,

$$
G_{\rm comparison}(x)\le
\frac{2}{|TT|b\Delta}
\left[\sum_{\rho\in\Phi}\left(
 d_\rho U_\rho(I_B)+(1-d_\rho)U_\rho(I_T)\right)-M_0\right].
$$

Indeed each $F_\rho(v_{uj\rho})$ is bounded on its own interval, precisely $d_\rho|H|$ translates use the thick interval, and the native divisor cancels the row count. This is a paper bound for the same comparison source in the ledger. Its inputs are the selected kernel, heights, scalar width ranges and original mask. A square-root estimate for this explicit expression would suffice. A large value of the expression alone would only rule out this uniform relaxation because maximizing independently over sites discards restrictions on jointly realizable widths. No critical bound for the maximum is established here.

## Outstanding supplier

The missing bound is $S(v)\le K_\varepsilon Qx^{1/2+C_0\varepsilon}$ on an admissible measured family for **every** anchor on arbitrarily distant complete windows $[Y,Y^{3/2}]$, with $C_0$ fixed before $\varepsilon$ and $K_\varepsilon$ independent of the window. The selected pair and host already exist; the theorem quantifies over physical profiles satisfying its explicit hypotheses. It does not establish cofinal existence of the required profiles with this signed payment. A local index contributes only through an estimate for the signed same-frame source or an independently priced one-sided comparison. The primitive evaluations and the joint finite-index, Gram and signed-slope payment are still open. No error row silently pays them.

## Lean declarations

- [nativeConstructedDyadicDiscrepancyLedger and nativeDiscrepancyPrice_le](../RHLean/Analysis/AlpogeThin/NativeExistingRecoveryPayment.lean) assemble the pointwise inequality from the selected host, price its errors, and retain the original height-window lemma.
- [nativeConstructedDyadicGzPayment](../RHLean/Analysis/AlpogeThin/NativeConstructedDyadicGzPayment.lean) supplies the analytic row. [alpogeNativeGzArithmetic_le_mean_add_move](../RHLean/Analysis/AlpogeThin/NativeScalarSupplierPayment.lean) supplies arithmetic movement.
- [alpogeNativePhysicalSubgroupTopExcess_logGrid_le and alpogeNativePhysicalSubgroupTopExcess_mass_bound](../RHLean/Analysis/AlpogeNativeThickFreezing.lean) give the physical width comparison and independent mass estimate. [nativeLambdaRecip_sub_log_abs_le](../RHLean/Analysis/NativePNTSelberg.lean) gives the numerical estimate for $L_N$.
- [Research audit roots](ALPOGE_EXISTING_RECOVERY_APPLICATION_AUDIT_20261124.lean) include the assembled ledger, normalized price and mass bound.

## Refining the width entry by freezing only the thick sites

Source: Alpöge's original `Compl3Record.lean` (lines 15–44, 217–287) and `AbsPhFSubLeOfLe.lean` (lines 52–153), pinned at [a6ac91a](https://github.com/TomasOrtega/RH/tree/a6ac91a412dcbaab31801355ec5707024a71bf65/extracted/lean/src/Formalism/SharpRestriction/Divisibility/HookProducts). This is an inequality transport, not a claim that Harish-Chandra coordinates equal native widths. The actual native signed row difference is the ASK difference plus the mean log-width difference multiplied by its height; all common character and height terms cancel. The ASK difference is nonpositive when the comparison is a lower width profile.

Use the same selected pair, host, rows, top heights, inertia/Frobenius, canonical character, cutoff and original divisor Q as above. Instead of rounding every width, let v = freezeThick(T2,u,b,w). The thin widths remain identical. The thick support has cardinal |T2|, exactly half the thick density among the 2|H| positive sites. At changed coordinates 0 <= log(w/b) <= h/b by log z <= z-1. Thus the mean log distortion is at most (Delta/2)(h/b). The existing one-sided signed-width theorem then gives

$$
S(w)/Q \le S(v)/Q + (A_{\max}/b)(h/b).
$$

The density cancels rather than being paid by an arbitrary grid tolerance. The comparison uses no manufactured geometric witnesses and no new assumptions. In the original size regime, the established numerical cost-window theorem (specialized at e=0, K=0 solely for its numerical inequality) gives (x+1)h/b <= 1/x eventually, uniformly in b,h. Since Amax/b <= x+1, the full native ledger becomes

$$
G_{\rm native}(x) \le S(v)/Q + C_d + x^{1/2+\varepsilon} + (A_{\max}/b)(h/b),
$$

with the last charge at most $1/x$ eventually. The guarded audit verified the signed row difference, thick-support count, normalized comparison and eventual price. All thin and ramified contributions remain in $S(v)$. The outstanding supplier above applies to this choice of $v$ as well.

Native declaration names: `alpogeNativeSignedWidthSource_sub_eq`, `alpogeNativeThickPositiveSites_card`, `alpogeNativeFreezeThick_logMean_le`, `alpogeNativePhysicalSubgroupTopExcess_freezeThick_upper_le`, `nativeConstructedDyadicFrozenDiscrepancyLedger`, `nativeFrozenWidthPrice_eventually`.

## Native signed compensation after the freeze of #1201

Foundation commit `52fbe6b` and merge commit `5eeebbd` have Git tree `1fd6e929252f786ff89ecd0abd749f0f6308288e`. The hosted build and guarded audits passed. After the first job deleted its restored full cache, rerunning the hosted build alone saved the exact key again. Cache ID `11157389789` was present after cleanup. [Hosted verification](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45821573180) · [Main push](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45835391297).

The frozen elaborated inventory has 42,159 project records, 36 declarations returning RH and no closed literal RH theorem. Its general graph exporter recorded zero body references for all 32,830 theorems because `ConstantInfo.value?` defaults to excluding theorem and opaque values. The dedicated axiom check and the strict principal dependency check are separate. The successor explicitly includes opaque bodies in the existing graph exporter. [Kernel graph exporter](../scripts/lean/DeclGraph.lean) · [Pinned Lean implementation](https://github.com/leanprover/lean4/blob/v4.34.1/src/Lean/Declaration.lean#L483-L488).

### Which first-prime cuts can still decide the sign

Keep the selected pair, host, actual rounded widths $v$, cutoff $N$, heights, signed MAIN and divisor $Q$ of the ledger. Write $K_{ng}$ for the nonnegative Fourier-inverted weight including $\Lambda(n)$, $k_n=\sum_{g\notin\Phi}K_{ng}$, and $\rho(t,g)$ for the positive partner. Brackets denote the full-host average of the sum over the original tops and rows. For $z=\lfloor\sqrt x\rfloor$, compute two finite quantities from this frame.

$$
\begin{aligned}
L&=\left\langle\sum_{n=1}^N k_n\frac{a_t}{n}
             -\operatorname{Re}\mathrm{MAIN}(\ell,a_t,v_{uj})\right\rangle,\\
P_{>z}&=\left\langle
  \sum_{\substack{z<p\le N\\p\ {\rm prime}}}\ \sum_{g\notin\Phi}K_{pg}
      \min\!\left(\frac{a_t}{p},v_{uj,\rho(t,g)}\right)
\right\rangle .
\end{aligned}
$$

Put $S_z=L-P_{>z}$. Every proper prime power and every small first prime keeps its linear term and exact inertia mass. The identity $y-(y-w)_+=\min(y,w)$ gives $S(v)\le S_z$. For every sufficiently large $x$, on every frame meeting the ledger's scalar conditions,

$$
0\le\frac{S_z-S(v)}Q
 \le 8(2K+\log 4+2)x^{1/2+\varepsilon}.
$$

Here $K$ is one absolute Chebyshev constant. Take $B=2b$ and $M=\lceil x+1\rceil$. The thick conditions give $v\le b+h\le 2b$ eventually. At a thin partner the original bound gives $w\le3a_t/\exp(x^{\varepsilon/3})\le b$ eventually. Rounding can only lower the width. Each replaced cut costs at most $B\min(M/n,1)$. At the proper powers the sum of $\Lambda(n)\min(M/n,1)$ is at most $K\sqrt M$ independently of $N$, by applying the finite Abel bound at $\max(M,N)$. At first primes through $z$ the sum is at most $\psi(z)\le(\log4+2)z$. The kernel satisfies $k_n\le2\Lambda(n)$, including at ramified primes. Dividing by the original $Q$ gives $4B(K\sqrt M+(\log4+2)z)/(b\Delta)$. Finally $\sqrt M\le2\sqrt x$ and $1/\Delta\le x^\varepsilon$.

The forward comparison therefore needs **one concrete lower estimate** on the jointly measured frame,

$$P_{>z}\ \ge\ L-K_\varepsilon Qx^{1/2+C\varepsilon}.$$

Both sides retain the same widths. The linear terms $a_t k_n/n$ in $L$ can be large. The estimate for $S_z-S(v)$ pays only the replaced cuts. [Physical comparison and normalization](../RHLean/Analysis/AlpogeThin/NativeExistingRecoveryPayment.lean) · [Scalar proper-power bound](../RHLean/Analysis/AlpogeNativeProperPowerCentering.lean).

The exact row decomposition is `alpogeNativeFirstPrimeWidthASK_eq_linear_sub_saving`.

`nativeLedger_firstPrimeWidth_on_dyadicFrame` specializes this price to the actual reciprocity map, canonical character term, original thick and thin masks, and full subgroup. Its constant precedes $\varepsilon$, the dyadic exponent, both primes and every frame parameter. The cutoff $N$ and the signed MAIN agree exactly in the two sources. Combining this one-sided estimate with the frozen ledger gives $G_{\rm native}(x)\le S_z/Q+(6+\log4)x^{1/2+\varepsilon}$ on those measured frames.

The measured thin width can be removed over a much longer first-prime interval. Set $X'=\exp(x^{\varepsilon/3})$ and $T=\lfloor X'/(x+1)^2\rfloor$. On every thin colour, rounding and the original thin-return inequality give $v\le w\le 3a_t/X'\le 3(x+1)b/X'$. Total kernel mass through $T$ is at most $2\psi(T)$. Consequently the contribution $P_{\mathrm{thin},(z,T]}$ of these sites to $P_{>z}$ satisfies

$$
0\le \frac{P_{\mathrm{thin},(z,T]}}{Q}
\le \frac{12(\log4+2)(x+1)T}{\Delta X'}
\le \frac{12(\log4+2)}{(x+1)\Delta}.
$$

The finite proof uses $p\le\min(T,N)$ on each row and the coefficient $2/(b\Delta)$ before averaging. For fixed $\varepsilon>0$, $T$ eventually exceeds every fixed power of $x$. Thus all thin-site savings through this threshold can be omitted from the lower-bound attack with the displayed error. The savings above $T$, the thick-site savings and the complete signed MAIN remain on their original frame. The Lean declaration is `alpogeNativeThinFirstPrime_saving_le`.

The selected pair also prices the ramified first prime $d$. At its original involution-shifted Frobenius site, $\log d\,\min(a_t/d,v)$ is bounded by $\log d\,a_t/d$. This last quantity is exactly the $d$-prime ASK at exponent cutoff one and zero width. Applying `nativeDyadicDPrimeASK_normalized_le_of_winPair` to this independent positive majorant yields $P_d/Q\le16x^{\varepsilon-1}$ on the same window, including when the actual rounded cut is inactive. The primes dividing $2^{e+2}q$ have zero source mass by `nativeDyadicHostPrimePowerWeight_typeI`. All unramified first primes with positive mass are inert. Hence the unresolved savings can be restricted to the thick sites of unramified inert primes above $z$ and their thin sites above $T$. The original linear terms and signed MAIN remain in $L$. [Discriminant price](../RHLean/Analysis/AlpogeThin/NativeExistingRecoveryPayment.lean) · [Actual prime weights](../RHLean/Analysis/AlpogeThin/NativeDyadicHostPrimePowerWeights.lean).

An Euler sign reversal at a mixed product $mp$ with $m>1$ and $p\nmid m$ has $\Lambda(mp)=0$. On every unramified inert prime tower the signed binomial ancestry has a single common sign across all surviving powers. Thus a pointwise cancellation between opposite signs in that tower cannot supply the needed payment. [Native mixed sites and signed ancestry](../RHLean/Analysis/AlpogeThin/NativeSignedPrimeExponentAncestor.lean).

Writing $P_*$ for the unramified inert savings at thick sites with $p>z$ and thin sites with $p>\max(z,T)$, these independent charges give

$$0\le (L-P_*-S(v))/Q \le Cx^{1/2+\varepsilon}+
\bigl(16+12(\log4+2)\bigr)x^{\varepsilon-1}.$$

To obtain the requested upper bound on $S(v)$ it suffices to prove $P_*\ge L-K_\varepsilon Qx^{1/2+C_0\varepsilon}$. The displayed two-sided price also quantifies exactly how much the restricted target can exceed the original signed source. The cutoff $N$ bounds all sums in $P_*$.

There is a further cancellation at every thick site with prime index $p\ge x$. Remove both its linear term from $L$ and its saving from $P_*$. Their difference is precisely its positive ASK cut. With $R=\sqrt{x}$ the ledger's own spacing satisfies $\eta=b\Delta R/(2A_{\max})\le1/(2R)$. Thus $v\ge b e^{-\eta}\ge b(1-1/(2R))$. For any integer $n\ge x$, the cut is at most $b(1/x+1/(2R))\le 3b/(2R)$. At $n\ge x+1+2R$ it vanishes. The support claim follows from $(x+1+2R)(1-1/(2R))-(x+1)=(3R+1)(R-1)/(2R)\ge0$. The interval has at most $2+2R\le4R$ integers. Its upper endpoint is at most $4x$, and the sum of all colour weights at each index is at most $2\Lambda(n)\le 2\log(4x)$. On one row this gives $12b\log(4x)$, even including proper powers. After the actual averaging and division the additional price is at most $24\log(4x)/\Delta$. The submitted declarations are `nativeLedger_thickTail_cut` and `nativeLedger_thickTail_mass`.

Write $L'$ and $P'$ for these simultaneous deletions, restricted to the affected unramified inert first primes already in $P_*$. Then

$$-24\log(4x)/\Delta\ \le (L'-P'-S(v))/Q\ \le C x^{1/2+\varepsilon}+(16+12(\log 4+2))x^{\varepsilon-1}.$$

The thick primes in $P'$ now lie strictly between $\sqrt{x}$ and $x$. Thin primes above $\max(z,T)$ and the exact signed MAIN still enter the same-family lower bound. The additional price fits the square-root budget uniformly by $1/\Delta\le x^\varepsilon$ and $\log(4x)\ll\sqrt{x}$ for $x\ge1$.

The remaining thick savings have a direct evaluation. Let $B_{q,d}(x)$ be the sum of $\log p$ over the actual unramified inert primes $\sqrt x<p<x$ whose Frobenius has the binary colour of $\operatorname{E1}$. Primes of the other binary colour have no thick translate. At each such prime $a_t/p\ge b$. Every thick translate therefore has
$$b e^{-\eta}\le\min(a_t/p,v)\le b+h.$$
For every top $t$ and host coordinate of the Frobenius there are exactly $|T_2|$ thick translates. Since $N\ge x$, none of these indices are lost. Sum the inequalities over the same tops, rows and translates. The native weight $2\log p$, the $1/|H|$ average and $Q=|TT|mb\Delta/2$ give
$$4 e^{-\eta} B_{q,d}(x)\le P'_{\rm thick}/Q\le4(1+h/b) B_{q,d}(x).$$
Set $C_\psi=\log4+2$. Since $B_{q,d}(x)\le\psi(\lfloor x\rfloor)\le C_\psi x$, $\eta\le1/(2\sqrt{x})$, and $(A_{\max}/b)(h/b)\le1/x$ eventually with $A_{\max}/b\ge x$, this becomes
$$-2C_\psi\sqrt x\le P'_{\rm thick}/Q-4 B_{q,d}(x)\le 4 C_\psi/x.$$
The error is independent of the thick density. The submitted row result is `nativeLedger_thickFirst_saving_census`. The aggregate follows by the displayed finite summation. This extracts the actual gain from the widths at the required scale. Its signed comparison with the linear and MAIN terms still requires an independent estimate of the arithmetic class sums on the selected pair.

The magnitude of this census has an independent quantitative estimate on the original pair. Write $F_\chi(y)=\sum_{n\le y}\Lambda(n)\chi(n)(y/n-1)+y\ell_\chi$ for any one of its three nonprincipal primitive two-bit twists. For $0<h\le x$, take $D_hF_\chi(x)=(x/h)(F_\chi(x+h)-F_\chi(x))-F_\chi(x)$. The $y\ell_\chi$ term cancels exactly. Every $n\le x$ has coefficient one. The coefficient for $x<n\le x+h$ is $x(x+h-n)/(hn)\in[0,1]$. Consequently
$$\Big|\sum_{n\le x}\Lambda(n)\chi(n)\Big|\le (x/h)(|F_\chi(x+h)|+|F_\chi(x)|)+|F_\chi(x)|+(h+1)\log(x+h).$$
This uses $|\chi(n)|\le1$ and at most $h+1$ integers in the boundary interval. The conductor and its logarithmic derivative introduce no constants. Set $h=x^{3/4+\varepsilon/4}$ with $0<\varepsilon<1/52$. For $Y\ge4$, $Y\le x\le Y^{3/2}$ gives $Y\le x\le x+h\le 2Y^{3/2}\le Y^2$. At both points `nativePairGood_dyadicTwist_bound` gives $|F_\chi(y)|\le y^{1/2+\varepsilon/2}$ for every one of the three twists on the same pair. The submitted Lean declarations `alpogeNativeTwistedSharp_le_forward` and `nativeLedger_pairGood_sharp_twist` give the finite, two-point estimate. The sharp twisted sums are therefore $O(x^{3/4+\varepsilon/4}\log(2x))$ uniformly over the whole real window.

At every first prime $p\nmid 2qd$ the two quadratic signs are $A(p),B(p)\in\{-1,1\}$. The value $1+B(p)-A(p)-A(p)B(p)$ is four on the actual thick binary class and zero on the others. Switching all three primitive sums to first primes costs $O(\sqrt x)$ by the native Chebyshev bound for proper powers. The exceptional first primes dividing $2qd$ cost $O(\log(2x))$, with three possible primes regardless of the modulus. Removing first primes $p\le\sqrt x$ costs $O(\sqrt x)$ and the possible first prime equal to $x$ costs $O(\log(2x))$. With $\vartheta(x)=\sum_{p\le x}\log p$, the resulting signed comparison is
$$\left|P'_{\rm thick}/Q-\vartheta(x)\right|\ll x^{3/4+\varepsilon/4}\log(2x).$$
In particular, the native thick savings have leading magnitude $x$ by the prime number theorem. The forward-difference argument costs both $x^{3/2+\varepsilon/2}/h$ and $h\log(2x)$. Balancing them leaves a power gap of one quarter before subpower losses. It preserves the sign and magnitude of the leading term but cannot alone give the required signed bound for the complete linear and MAIN combination. [Selected two-bit estimates and induction to primitive characters](../RHLean/Analysis/AlpogeThin/NativeDyadicThickCharacters.lean) · [Actual four-character kernel](../RHLean/Analysis/AlpogeNativeFourCharacterArithmetic.lean).

### Signed thin contribution on the actual rounded family

When the original MAIN is assigned to the colours by the complete Fourier identity, the entire centered thin contribution admits an independent upper price, including its large first primes. To apply that identity with rounded widths, keep the original $N$ on the left and use $N'=\max(N,\max_\rho\lceil a_t/v_\rho\rceil)$ only on the right. Each additional Fourier-inverted ASK weight and cut is nonnegative. MAIN is identical on both sides. At $N'$ the established exact identity gives the sum of the actual thick and thin responses evaluated at the same rounded widths.

For any pair already selected by the ledger, `principalPair_uniform_noExc` and `QH.thin` give the uniform bound $|F_\psi(y)|\le y\theta$, $\theta=\exp(-x^{\varepsilon/8})$, at all $y\ge\exp(x^{\varepsilon/3})/3$, with the native conductor bound. On a thin site $v\le w$, so $y=a_t/v$ meets that threshold. Each product $vF_\psi(a_t/v)$ costs at most $a_t\theta$. There are $4|H|$ characters, $2|H|-|T_2|$ thin colours and the divisor per colour is $2|H|$. Applying the original row and translate sums gives

$$S_N(v)/Q\le \frac{1}{Q|H|}\sum_{u,t,j}\operatorname{Re}\operatorname{ActualThick}(F,T_2,a_t,u,t,v_{uj})+\frac{(8|H|-4|T_2|)\theta\,\overline a}{b\Delta}.$$

The final term is at most $2/(x\Delta)\le2x^{\varepsilon-1}$ eventually because $\overline a/b\le x+1$ and the verified native host cost gives $4|H|(x+1)\theta\le 1/x$. The original conductor estimate follows from `nativeDyadicHost_windows` on this same pair. The branch submits `nativeLedger_anyCutoff_le_thick_add_thin` and `nativeLedger_pairGood_roundedASK_le_thick` for the row inequality. Summation uses the frozen normalization `nativeDyadicThinBill_div_projectionDivisor`. This directly reduces an upper bound on the comparison to the centered, signed thick response. That response includes its own share of MAIN and still requires the quantitative physical gain. The small error for the centered thin response cannot be used as a bound on the uncentered thin saving in $P'$ alone. [Complete source identity](../RHLean/Analysis/AlpogeNativeSubgroupProjection.lean) · [Independent thin estimate](../RHLean/Analysis/AlpogeThin/NativeCftThin.lean) · [Size and normalization](../RHLean/Analysis/AlpogeThin/NativeDyadicCostWindows.lean).

### Paying the reverse comparison to physically measured widths

The frozen ledger prices $S_N(w)-S_N(v)$ from above. The reverse direction allows a signed recovery proof at the actual geometric widths $w$ to feed the rounded comparison. On each lift and row use the mixed profile $w_1=w$ on the actual thick mask and $w_1=v$ elsewhere. For large anchors $h\le b$ and $0<\eta\le1/(2\sqrt x)\le1/2$. Every changed width obeys $v\ge e^{-\eta}w\ge b/2$ and $0\le w_1-v\le(1-e^{-\eta})(b+h)\le2b\eta$. The signed upward width movement bound at baseline $b/2$ therefore gives, for each top, a price of at most $4b\eta\,\psi(\lfloor2a_t/b\rfloor)\le8(\log4+2)a_t\eta$. After summation and division the charge is at most $16(\log4+2)A_{\max}\eta/(b\Delta)=8(\log4+2)\sqrt x$.

For $w_1$, enlarge the cutoff only on the majorizing side to cover every ratio $a_t/w_{1,\rho}$. For $w$ the **original** $N$ already covers every ratio. In their complete Fourier decompositions the signed thick responses agree term by term because their widths coincide on the same thick colours. Each signed thin average has absolute value at most $2Q/(x\Delta)$ by the preceding character estimate on the *same* pair. Subtract the two complete responses, using the upper cutoff comparison for $w_1$. Together these calculations yield the paper inequality

$$-\sqrt x\ \le \frac{S_N(v)-S_N(w)}{Q}\ \le 8(\log4+2)\sqrt x+\frac{4}{x\Delta}.$$

This addresses the rounded comparison on measured frames without requiring a separate geometric realization of $v$ or $w_1$. Only $w$ must come from a physically realized family with sufficient signed gain. The two-sided aggregate is a paper derivation. The submitted row estimate `nativeLedger_restoreMeasuredThick_le` proves the thick-width movement price using `alpogeNativeSignedWidthSource_lower_width_le`. Freezing the thick signal at a common width evaluates to `alpogeNativeProjectedSignal` by `alpogeNativeFrozenThick_average_eq_signal`. On this pair it still contains the original principal term, since `nativePairGood_dyadicGsig_sub_Gz_norm_le` pays just the three nonprincipal twists. An independent upper bound on the physical signed source thus remains essential. [Signed width movement](../RHLean/Analysis/AlpogeNativeThickFreezing.lean) · [Thick characters on the selected pair](../RHLean/Analysis/AlpogeThin/NativeDyadicThickCharacters.lean).

### Aggregate effect at one shared width

Fix an unramified inert prime $p$, one lift and translate, and a destination reached from $s$ with odd exponent $i$. For exponent $i+2j$ the partner equality forces the top to be $s-2j\,\mathrm{Frob}_p$ in its host coordinate. The two binary coordinates are unchanged. This is an exhaustive address at that exponent even after a return modulo the host order. For any top retained by the cutoff and the original top set, $a_t/a_s\le(x+1)/x\le2$. Write $A=(a_s/p^i-v)_+$. The later cut is at most $2p^{-2j}A$ for $j\ge1$, since $2p^{-2j}\le1$ and the width is common and nonnegative. Hence

$$\sum_{\mathrm{later\ reads\ at\ this\ site}}(a_t/p^{i+2j}-v)_+
 \le \frac{2}{p^2-1}A.$$

The source factor $2\log p$ multiplies both sides. On the historical 43 example, the reads $(1849,43)$ and $(1,43^3)$ are both positive at width 16. Their later-to-leading ratio is exactly $3571428568589/6603571428568523$. This falsifies a zero allowance for later reads and is below $1/924$. That example measures arithmetic cuts and fails the upstream physical top quota. [Native shared-width argument](../RHLean/Analysis/AlpogeThin/NativeDyadicShiftedWidthRows.lean) · [Original benchmark](../scripts/native_economical_recovery_widths.py).

### Simultaneous physical height readings for a single prime

Fix the actual dyadic Frobenius and write $\sigma_p(t)=t+2\mathrm{Frob}_{p,H}$. At an unramified inert prime the first and third powers have the same nonzero coefficient before the cut. Their partners agree for the respective tops $\sigma_p(t)$ and $t$. Whenever $2p^3\le x$, $a_t\ge xb$, and this common width is at most $2b$, both cuts are active. In the original cutoff both are present when both tops are selected and $p^3\le N$. In the ledger $N=\lceil A_{\max}/\beta\rceil\ge x$. Writing $U_{t,i}$ for the actual unweighted local ASK atom, one obtains the integral reading
$$p^3(U_{t,3}-U_{\sigma_p(t),1})=a_t-p^2a_{\sigma_p(t)}.$$

Every vector of residues $y_t\bmod p^k$ can be prescribed in these readings at once. On the whole native host put $Tz(t)=z(\sigma_p(t))$ and choose $r=\sum_{j=0}^{k-1}p^{2j}T^jy\pmod{p^k}$. Then $(I-p^2T)r=y$ since $p^{2k}=0\bmod p^k$. This includes every cyclic return. For an incomplete top set, extend the desired residues to all tops and use only edges whose two tops are retained. If the allowed height interval begins at $L$ and has length at least $p^k$, choose the least height $a_t\ge\lceil L\rceil$ of residue $r_t$. Thus $L\le a_t<L+p^k$ simultaneously for all tops. A primitive coordinate vector, or any other requested residue vector, needs the same interval. The submitted Lean declaration `nativeDyadic_activeShift_residues_in_window` includes the integer heights, the simultaneous residues, and the identity for the measured active cuts. [Native shift and atom](../RHLean/Analysis/AlpogeThin/NativeDyadicShiftedWidthRows.lean) · [Prime-power coefficients](../RHLean/Analysis/AlpogeThin/NativeDyadicHostPrimePowerWeights.lean).

For several distinct primes, the Chinese remainder theorem on each top realizes all the residue vectors on one height profile. The interval length required by this construction is $M=\prod_p p^{k_p}$ independent of the number of downstream tops. The original exponential collar gives length $b/(Rx^{13})\ge b/x^{14}$ for $1\le R\le x$. For $b=\exp(x^\varepsilon)$ it suffices that $\sum_p k_p\log p\le x^\varepsilon-14\log x$. For example, all $p\le x^{\varepsilon/2}$ with $k_p\le x^{\varepsilon/4}$ cost at most $(\log4+2)x^{3\varepsilon/4}$ by the native Chebyshev bound. That fits eventually, and $2p^3\le x$ also holds for $\varepsilon<1/52$. The formula realizes the selected height residues even for primes with zero source coefficient. Only unramified inert primes enter the physical gain, and the original pair forces odd primes up to $Y^{\varepsilon/5}$ to split. With distinct integral heights required on the whole host, assign the top of index $j$ its own consecutive interval of length $M$ and solve the same congruences there. The resulting room requirement is $|H|M$, adding just $\log |H|\le(2+8.01\varepsilon)\log x$ to the logarithmic budget. The submitted theorem `nativeDyadic_activeShift_joint_injective_heights` constructs this injective height profile for every residue vector at every selected prime on the same host.

This gives full residue rank on the **height-difference coordinates** available at those actual pairs of tops. It does not identify that coordinate lattice with Alpöge's section or dual lattice. Multiplying the difference by $p^3$ extracts an integer and contributes a scale which must be accounted for when comparing valuations. The same heights must still support the competing-edge divisibilities, global index, norm and archimedean signed payment. No lower bound for the signed prime gain follows by summing prescribed residues.

The cubic activity range and the unpaid interior prime range are disjoint on the thick sites. If $p>\sqrt{x}$, then $a_t/p^3\le b(x+1)/x^{3/2}<b e^{-\eta}$ for all sufficiently large $x$, whereas every rounded thick width is at least $b e^{-\eta}$. There is no third-power thick reading to deduct from the same high first prime. Alpöge's index and global norm comparison is precisely where a gain produced by small-prime recovery could influence a different range of primes.

Two first primes of the same thick binary colour admit a different local comparison. At $p\ne r$ choose $s=t+\mathrm{Frob}_{p,H}-\mathrm{Frob}_{r,H}$. The partners coincide. When both tops belong to the original set and both cuts are active, their actual widths cancel and $pr(U_{t,p}-U_{s,r})=r a_t-p a_s$. Since $r$ is a unit at $p$, on a complete orbit the operator $rI-pT$ is invertible modulo every $p^k$ by the same finite geometric sum after multiplication by $r^{-1}$. This observation does not price repeated use of the $r$ row or the omitted tops.

There is an exact counting limit on independently prescribing high-prime residues by choosing heights. For any nonempty finite set of $n$ tops in a common interval of length $W$, there are at most $(\lfloor W\rfloor+1)^n$ possible integral height profiles. There are $\prod_{p\in P}p^{k_p n}$ possible independent residue vectors. A surjection from profiles to all these vectors would force $\sum_{p\in P} k_p\log p\le\log(\lfloor W\rfloor+1)$. At the original collar this is at most $x^\varepsilon+O(1)$. Hence for $k_p\ge1$ an independently programmable subset of the upper thick primes accounts for at most $4(1+h/b)(x^\varepsilon+O(1))$ in the normalized positive savings, by the exact thick census. This rules out paying an order-$x$ budget by summing independently prescribed scalar residues on every high prime. A common constrained section or an independently quantified aggregate signed comparison could still supply the gain.

### Closure obligations and dependency status

There is a numerical obstruction to instantiating the compact global comparison on the native moving discriminant. In Sernau’s pinned compact source, `c_ge` gives $d\le P.c$ and `Data.scale` gives $10^{12}P.c\le\log\log b$ and $100\log\log b\le\log X$. Consequently

$$10^{14}d_{\mathrm{compact}}\le 100\log\log b_{\mathrm{compact}}\le\log X_{\mathrm{compact}}.$$

On the native pair, for every fixed $A\ge0$, every $Y\ge\exp(\max(1,4A))$ and every $0<x\le Y^2$, `nativeLedger_winPair_discriminant_growth` gives $A\log x<\log d_{\mathrm{native}}$. Indeed $2A\log Y\le(\log Y)^2/2<\log d_{\mathrm{native}}$ by `WinPair.d_lo`. Taking $d_{\mathrm{compact}}=d_{\mathrm{native}}$ and $X_{\mathrm{compact}}\le x^A$ would require $10^{14}d_{\mathrm{native}}<\log d_{\mathrm{native}}$. No choice of the width or fixed power of the anchor cures this incompatibility. Direct transport therefore has to use the local index and signed-norm inequalities before this global scale restriction. Choosing a different discriminant would require its own measured source discrepancy. [Compact admissibility](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Data/AdmissibleData.lean#L15-L30) · [Parameter bound](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Data/Magnitudes.lean#L21-L22) · [Native prime selection](../RHLean/Analysis/AlpogeThin/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean).

At a fixed prime, `exists_colengthDvd_gaugeLe_compositeLift` chooses **one** exponent $j$ and submodule $S$ before quantifying over every twist, chain datum and ramified form in $S$. For ordinary small nonsplit primes $j=0$ and the collision sum fits the loss on the entire integral module. For exceptional small nonsplit primes it chooses a full mark, forms its scaled Hecke product $U$, and takes $S=U^mM+p^{j_p}M$. The same full mark bounds the colength and the valuation on that very $S$. Then `indexLe_of_mem_image_normalizedPoincare` transports both bounds along the same restricted linear map. A native replacement has to bound the index of the actual image and prove the valuation gain on its elements for every required twist. The global signed comparison also uses archimedean norms and the lower covolume of that image. A collection of separately optimal recovery and gain witnesses does not imply these two conclusions. [Local four-case proof](https://github.com/leanprover-community/riemann-hypothesis/blob/61d870d08d5f6f5cc12f31fe40f5689024ea15ab/src/New/UpperBound/Divisibility/LocalDivisibility.lean#L417-L481) · [Use of the same submodule](https://github.com/leanprover-community/riemann-hypothesis/blob/61d870d08d5f6f5cc12f31fe40f5689024ea15ab/src/New/Reduction/ShortAndEnough.lean#L290-L319).

The community main advanced to `61d870d` during this audit. Its elementary-divisor edge file, geometric collision sum, signed prime-gain comparison, final covolume inequality and one-sided prime-remainder theorem are byte-identical to `3ad0b4b`. Its admissible-evaluation update removes a redundant rational-primality hypothesis in two lift lemmas. Their local uniformizer, unit, scaling and lifting conditions still require witnesses. At the subsequent revision `884e2d0`, the local colength statement and its four-case proof retain their mathematical content. The scalar-norm step in `ShortAndEnough` now invokes `normSqAt_smul`. Two further evaluation lemmas omit the ambient rational-primality instance. Their split level, uniformizer, integrality and matching assumptions persist. [Latest local colength proof](https://github.com/leanprover-community/riemann-hypothesis/blob/884e2d0174803658e0acfbf795410576892d140f/src/New/UpperBound/Divisibility/LocalDivisibility.lean) · [Latest admissible evaluation](https://github.com/leanprover-community/riemann-hypothesis/blob/884e2d0174803658e0acfbf795410576892d140f/src/New/UpperBound/Seesaw/AdmissibleEvaluation.lean).

| Obligation and required inequality | Alpöge mechanism | Native declaration and established estimate | Remaining gap |
|---|---|---|---|
| For each primitive $c$ find one integral $v$ with $C(v)\in K_{\rm comp}$ and $\langle c,E(v)\rangle\mid p^D$. | `SrcTests`, `goodRank_of_prim` and `s7` combine the selected test with the competing divisibilities. The compact edge restriction applies a translated matrix and a depth scaling. | `NativeTheta.adaptedEdge_pairing` evaluates an adapted basis pair. `NativeJointEvaluationRecovery.recovery_of_congruent_primitive_tests` consumes congruence modulo $p^D\varpi$ on the same lift. `nativeDyadic_activeShift_residues_in_window` realizes every integral height-difference residue vector in room $p^k$. `nativeDyadic_activeShift_joint_injective_heights` realizes all selected primes on one injective height profile in room $|H|\prod p^{k_p}$. | On the injective square-clock profile the paired first cuts have scalar duals at every prime-power depth outside an explicitly paid exceptional set. For the primitive-test route, produce the actual restricted sections and competing lattice memberships. Direct production of the short independent family in Sernau A/B could replace this input. |
| Retain the required rank with affordable finite-index and Gram costs on one frame. | `indexLe_normalizedPoincare` and `enough_forms` use the same translates. `integral_forms_long` compares their independent images with a lower covolume bound including twice the index cost. | `alpogeNativePartner_even_offset_iff` and `nativeDyadic_sharedWidth_laterReads_le` price later arithmetic reads by $2A/(p^2-1)$. `NativeServedPrimeLength.lengthFromAllBut_of_sandwich` consumes actual exceptional generators and inclusions. | In standard height coordinates the normalized prime chain has length distortion at most 2 and denominator price per column at most $2(\log4)Z$. Extend these bounds to the actual localized sections, with their measured metric, retained rank and signed term. |
| $P_{>z}\ge L-K_\varepsilon Qx^{1/2+C\varepsilon}$. | `log_invGainFactor_le` subtracts the sum of the measured prime gains in the norm estimate. `span_short_integralRamified_eq_top` and `star_inequality` cancel the gain and the main amount on the same independent family. | `alpogeNativeFirstPrimeWidthASK_error`, `alpogeNativeFirstPrimeWidth_normalized_error`, `nativeLedger_roundedWidth_cap_eventually` and `nativeLedger_firstPrimeWidth_price_le` give the priced comparison above. | The selected-pair sharp estimate `nativeLedger_pairGood_sharp_twist` gives a paper comparison of the normalized thick saving with $\vartheta(x)$ of order $x^{3/4+\varepsilon/4}\log(2x)$. The thick saving is determined by the explicit $4B_{q,d}(x)$ within $2(\log4+2)\sqrt x$ below and $4(\log4+2)/x$ above. Bound the remaining same-pair arithmetic combination against the linear and signed MAIN terms. The native Perron cosine kernel is $+1/(qr)$ at frequency zero. A negative cross contribution requires control of the actual weighted frequencies and their attachment to this frame. |
| On the original family, $(S(v)-S_{P,\mathrm{thick}})/Q\le -2V_w/c+K_\varepsilon x^{1/2+C\varepsilon}$. | In `star_inequality`, A and C price the same corrected covolume, and B prices completion. | `nativeLedger_high_wheel_normalized_price` prices the measured high thick discrepancy. The wheel block dual, Gram and short-completion declarations above give $J$ missing columns, a unimodular completion and $O(\sqrt{x}\log x)$ cost for the joint ordinary dual Gram. The sum of log squared projection distances equals $-V_w$. | Identify or bound the original signed MAIN and remaining ASK by this projected wheel volume on every real anchor. The native Perron kernel at one frequency is the sum of its cosine and sine outer products, so a single frequency can have rank at most two on a block. A proof using those alignments must control the actual combined metric. |
| Bound every error after division by $Q$. | Preserve the original thick density and signed height/width comparison. | `nativeConstructedDyadicDiscrepancyLedger` and `nativeDiscrepancyPrice_le` give $(6+\log4)x^{1/2+\varepsilon}$ on admissible frames. `nativeProperPower_clippedMass_le` supplies the separate proper-power price from Chebyshev and finite summation. | Realize the same measured frames at all required anchors. Their scalar conditions suffice for the prices. |
| Cover the full real window and deliver the bound with fixed exponent coefficient. | One selected pair precedes the anchor choice, followed by the one-sided analytic handoff. The compact `eventually_primeRemainder_natCast_le` bounds a congruence-restricted prime remainder. | `nativeLedger_realHeight_mem_pairWindow` puts every $[x,x+1]$, $x\in[Y,Y^{3/2}]$, inside one $[Y,Y^2]$ for $Y\ge4$. `AlpogeNativeBoundHandoff.SmallEpsilonWindowBound` requires fixed $C_0$ and $\varepsilon_1>0$, then $\forall\,0<\varepsilon<\varepsilon_1\ \exists K_\varepsilon\ \forall Y_0\ \exists Y\ge Y_0$, and a bound for every real anchor. | Supply the signed family with $K_\varepsilon$ independent of $Y_0,Y,x$. For a requested loss $\eta>0$, take $0<\varepsilon<\min(\varepsilon_1,\eta/(1+\lvert C_0\rvert))$. |
| `native_riemannHypothesis : RiemannHypothesis`. | One-sided zero exclusion. | `AlpogeNativeBoundHandoff.riemannHypothesis_of_smallEpsilonWindowBound` is the verified conditional consumer from #1205. | The unconditional declaration and its terminal semantic audit are open. |

```mermaid
flowchart TD
    R["Simultaneous native height residues"] --> A["Short columns carrying the signed source (open)"]
    K["Height rank and denominator prices"] --> B["Physical retained rank and denominator budget (open)"]
    T["Integral heights and unit scalar duals"] --> P["Disjoint high first-prime cuts and weighted margin"]
    P --> A
    J["Integral dual and Gram for the high thick ASK"] --> A
    J --> B
    J --> M["Signed MAIN versus projected wheel volume (open)"]
    M --> S
    B --> A
    B --> C["Lower determinant with the same main amount (open)"]
    A --> S["Upper and lower bounds on the same columns"]
    C --> S
    S --> E["Bound for the full comparison"]
    D["Priced transfer errors on admissible frames"] --> F["Native discrepancy ledger"]
    E --> F
    W["Measured frames on complete real windows (open)"] --> F
    F --> H["SmallEpsilonWindowBound"]
    H --> Z["Unconditional native RH (open)"]
```

[Original primitive tests and Smith step](https://github.com/leanprover-community/riemann-hypothesis/blob/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a/src/Formalism/SharpRestriction/GrowthBounds/ScaleEdges/GoodRankOfPrim.lean) · [Compact edge restrictions](https://github.com/leanprover-community/riemann-hypothesis/blob/61d870d08d5f6f5cc12f31fe40f5689024ea15ab/src/New/UpperBound/ElementaryDivisors/Edges.lean) · [Prime collision budget](https://github.com/leanprover-community/riemann-hypothesis/blob/61d870d08d5f6f5cc12f31fe40f5689024ea15ab/src/New/UpperBound/Divisibility/JetExponent.lean) · [Signed prime gains](https://github.com/leanprover-community/riemann-hypothesis/blob/61d870d08d5f6f5cc12f31fe40f5689024ea15ab/src/New/Reduction/ShortAndEnough.lean) · [Same-family covolume comparison](https://github.com/leanprover-community/riemann-hypothesis/blob/61d870d08d5f6f5cc12f31fe40f5689024ea15ab/src/New/Reduction/MainInequality.lean) · [Proof map](https://riemann.verifytask.cn/?lang=en) · [Guarded native roots](ALPOGE_EXISTING_RECOVERY_APPLICATION_AUDIT_20261124.lean) · [Native Perron alignment](STABLE_FAR_PERRON_REAL_GRAM_COSINE.lean).

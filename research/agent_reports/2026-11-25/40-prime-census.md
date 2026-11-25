# Prime Census Laboratory | November 25, 2026 (New York)

## Registered question | PC-20261125T081101Z-HEIGHTFIBRE-OPEN

PARTIAL / IN_PROGRESS. Can sparse base averaging preserve the original ASK minus MAIN at unequal top heights? Test the competing explanations that one translate count for the whole top set suffices, or that the distinct measured heights impose separate constraints. Do not infer scalar inequality from a failure to match distributions. The independently paid physical words, widths and bases have not been supplied in the handoffs; no geometric family will be simulated or claimed.

Scheduled 03:11:01 EST (08:11:01Z), America/New_York; RUN_ID_UNAVAILABLE. Main `7cb76d913acfd68fc036e01673a876a9a77be90f`, AGENTS `a60620dca883d98dbe391ddd1ab5afcab805b96e`, contract `6fa886e125321056739a48d09fd33c95edaebf6b`, final directive `395378d0e6525fab6c6ed9b7315c5de4c36329dd`. Draft #1201 `c94fc79fe452d568eb877fbe64f17ad638e7bc0d`, instructions `2bf7b75c5abb01962ecd9989320b600315e1a46f`. Reports intake `7b6c494fdb99a179835c93b7591b6b122a1be5b0`. Today TOPLAW1-4 and PARTNER1-4; yesterday WIDTHLAW1-4, LOCALGAIN1-4, WINDOW1-4, FIBER, CORE1-5, METRIC1/PERIOD1. Last Census FOURPOWER1-4 on November 22; no November 23 folder or November 24 Census file. The prior prime proxy is not a payment. The main merge of the frozen external replay (#1211) does not supply the native same-host inequality. The required #1201 Lean source-audits run 45548060914 failed. Native RH remains open.

Pre-computation design: keep one fixed native modular map, its actual Frobenius and all inertia cosets; the two quadratic bits, exact top translation, all prime powers through the physical cutoff, every lift, width, height, and the sign of minus MAIN. Compare the direct ledger with a height-weighted histogram of the ratios of width to height. Reject on a single unequal coefficient, including the logarithmic width term. Test exact zero on individual height classes against exact zero after folding; probe tied and nearly split heights at a ramified square, initially q=11,d=7,e=2. Check disjoint fixtures and row laws; label test inputs distinct from PairGood/PageN or geometric witnesses. Reuse the selected-pair EAtH construction as an analytic supplier only; do not re-select the pair. No local Lean, proof-source edit or new endpoint.

`final_1201_ack=FINAL_PR_1201_PROOF_CLOSURE_V1; FINAL_1201_ROLE=CENSUS; DIRECT_CORE_CUT_V1; STRICT_NO_GEOCL_ANYGEOMETRY_V1; continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1; publish_ack=REPORT_PUBLISH_RECOVERY_V1`.

## Verified calculation | PC-20261125T081101Z-HEIGHTFIBRE-M1

08:28 UTC / 03:28 EST. At the diagnostic modular host (q,d,e)=(11,7,2), moving only top 0 from 49 to 49+1/4 changes the original uniform-minus-comparator excess by exactly +log(7)/784 or -log(7)/784, according to which two bases are kept. After the original divisor Q this is +/-log(7)/400. The unique active site is the ramified square 49. The same construction at 50 gives exactly zero although the distributions fail to match. A separate (3,23,3) test at 529 gives -log(23)/8480 after normalization. Two different modular reconstructions and exact rational log coefficients agree. These are not measured geometric rows.

The height-weighted width/height distribution gives a one-pass comparison; whether it vanishes exactly is determined separately on each equal-height class. All 6,640 tested nonempty top/height assignments on groups of orders 4 and 8 agreed with the predicted minimum base support. Full proof, scope, costs, independent tests and replay follow. The complete signed payment on a genuine selected family remains OPEN.

## Final findings | PC-20261125T081101Z-HEIGHTFIBRE-FINAL

### A. Most important discovery

**Equal measured heights, not just membership in the top set, determine which base points may be omitted from an exact width-distribution comparison.** Under the odd thick-set and translation hypotheses in F, a binary-tree test gives the *exact* minimum number of bases and decides whether a prescribed set of independently payable bases is sufficient. One uniquely occurring height forces every base to be retained for this certificate. This is not a necessity theorem about the scalar bound itself.

The distinction is visible on the genuine modular coefficients: splitting one of two equal heights at 49 leaves exactly `+log(7)/400` or `-log(7)/400` **after the original normalization**, depending on which two bases are used. The omitted term in a prime-only calculation would be the ramified square, not an ordinary prime. Splitting at 50 changes the distributions but has **zero** effect on the signed sum. There is no independently paid physical family in these examples. The native critical estimate and RH on this route remain **OPEN**.

| Claim | Evidence and limit |
|---|---|
| PC-20261125-HEIGHTFIBRE1 | PAPER_PROOF: exact variable-height representation of a *difference* of complete signed excesses, with one measurable upper bound. No common-height replacement. |
| PC-20261125-HEIGHTFIBRE2 | PAPER_PROOF: exact separation by height; necessary support constraints on the original separated odd thick mask, also sufficient for measured translation-covariant width histograms. |
| PC-20261125-HEIGHTFIBRE3 | PAPER_PROOF and FINITE_COMPUTATION: sharp minimum support, prescribed-support feasibility and least independent linear price under those constraints. |
| PC-20261125-HEIGHTFIBRE4 | REFUTED on the specified modular finite-data class: aggregate top balance guarantees exact signed transfer at unequal heights; prime-only testing detects every such failure. The converse inference from histogram mismatch to scalar mismatch is also false. |

SELF_AUDIT; independent specialist review and Lean verification of these new statements are pending. No change of mathematical campaign.

### B. Authority and the actual source

[Main instructions][maininst] `7cb76d913acfd68fc036e01673a876a9a77be90f`; [contract][contract] and [controlling seven-role directive][directive]; [actual #1201 instructions][prinst] at `c94fc79fe452d568eb877fbe64f17ad638e7bc0d`. The [canonical objective][vf] is one $C\ge0$ such that $|\pi(R^2)-VF_{\rm can}(R^2)|\le C R\log R$ for every integer $R\ge2$. The active sufficient route concerns the one-sided bound for

$$Z(x)=\sum_{1\le l\le\lfloor x\rfloor}\Lambda(l)(x/l-1)-x\log x+(1+\gamma)x,\qquad x\ge1.$$

I compared the two literal definitions `Sz` and `Gz` in the [original pin][up], the [community cleanup][community], the [branch copy][copy], and the [native handoff][handoff]. Same closed integer cutoff, zero kernel at an integer upper endpoint, every prime power with weight $\log p$, and identical Euler centering. In [`nativePrincipalCyclicGm_eq`][pay], the kept set is the principal singleton; erasing it leaves an empty nonprincipal sum, then `statementOCGz_eq_native` identifies the source. This exact identity does not estimate $Z$ or identify arbitrary upstream witnesses.

**Same pair, not merely the same integers in two independent choices.** [`nativePrincipalEAtH_windows`][eath] chooses one `PairGood` pair on a complete window before $x$, takes the actual `PageN` exponent at $x$, and proves EAtH for **every** $TT$. Index one and $A_0=\top$ give exact shares; the bounded characters reduce on units to the three nontrivial quadratic twists, and both response and log-derivative bounds use that pair. For square anchors use the *payment's* pair for $Y=A^2-1$ with outer endpoint $Y^2$, its $e(R^2-1)$, and `nativePrincipalEAtH_squareClock_of_pair`; do not select a second pair. $A\le R\le A^{3/2}$ puts the whole interval $[R^2-1,R^2]$ inside the outer window. The [frame map][frame] swaps the physical additive bits $(d,q)$ to $(q,d)$ unit signs for the raw analytic host; [`nativeDyadicArt`][raw] explicitly composes that equivalence with the modular reciprocity map. For ASK below, the *first physical bit is at $d$*. No mask is applied to an unswapped raw pair of signs.

### C. Question and alternatives

[TOPLAW1–4][tii] already show that matching the distributions after averaging all top translates at a *common* height need not give equality at the measured heights; this was not rerun as a discovery. Our question was which information about the heights is necessary and whether one can compute the best exact support. Possibilities: one overall translate count; separate tests on height classes; or accidental agreement of the arithmetic even when those tests fail. The discriminators are the signed distributions at the ratios $w/a_t$, the full ASK coefficient at each $p^i$, the width term of minus MAIN, and the smallest feasible support. One unequal exact coefficient rejects a proposed reconstruction. Agreement on a single scalar does not certify distribution matching.

### D. Complete finite carrier

Fix the selected $q,d,e$, its actual group $H=(\mathbb Z/2^{e+2})^\times/\{\pm1\}$ of size $n=2^e$, nonempty $TT,T_2\subset H$, $T=|TT|$, $m\ge1$, $\Delta=|T_2|/n$, $b>0$, and the *same* divisor $Q=Tmb\Delta/2$. Write $g=((1,v),h)\notin\Phi$, $\rho(g)=(1+v,h)$ on the positive planes (first zero bit suppressed). The partner is $\rho_t(g)=(1+v,h+t)$, addition of the bit modulo 2. The widths $w_{uj}(c,h)>0$ are indexed by base $u$, lift $j$, and positive site. Keep $a_t>0$, $S=\sum_{TT}a_t$, $\bar a=S/T$, physical $N=\lceil A_{\max}/\beta\rceil$, $a_t\le A_{\max}$ and $w\ge\beta$. Thus all sites above $N$ have zero hinge. No cutoff changes when comparing laws.

For $l=p^i\le N$, $i\ge1$, use the [exact native coefficient][sharp]

$$k_l(g)=\frac{2}{|I_p|}\,1_{g-iF_p\in I_p}.$$

Here $F_p$ is the image of the CRT unit congruent to $p$ off the $p$-part and to 1 on the $p$-part, and $I_p$ is the image of the full local-unit kernel, not a single Frobenius at a ramified prime. ASK includes $\log p\, k_l(g)(a_t/l-w_{uj}(\rho_t(g)))_+$. MAIN is $a_t(\log a_t-1-\gamma+\Re\ell(\chi_C)-|\Phi|^{-1}\sum_{\rho\in\Phi}\log w_{uj}(\rho))$ after taking real parts. For a probability law $\lambda$ on this very base, denote the weighted sum of the complete real ASK **minus** MAIN over all $t,j$ by $X(\lambda)$. Only uniform $\mu$ is the [original subgroup excess][sub]; $\nu$ is a comparison, not a replacement population or a new choice of geometric data. The canonical derivative $\ell$ is unchanged. Its cancellation below is between laws of equal mass, not from setting it to zero.

### E. Exact comparison at the measured heights

For $v,r>0$ define

$$D_{c,h}(v)=\frac1m\sum_{u,j}(\mu(u)-\nu(u))1_{w_{uj}(c,h)\le v},\qquad
F_{c,h}(r)=\frac1S\sum_{t\in TT}a_tD_{c,h+t}(a_t r).$$

Write $\overline F=(2n)^{-1}\sum_{c,h}F_{c,h}$ and $J_a=\int_0^\infty\max_{c,h}|F_{c,h}(r)|\,dr/r$. These are finite step functions with zero tails; $J_a$ is exactly a sum of measured step heights times log ratios of consecutive, distinct $w/a_t$. Breakpoint equalities have no interval mass.

**HEIGHTFIBRE1.** On all the finite data above:

$$\frac{X(\mu)-X(\nu)}{mS}
=\int_0^\infty\left[\sum_{\substack{l=p^i\le N\\lr<1}}\log p
\sum_{g\notin\Phi}k_l(g) F_{\rho(g)}(r)-\frac{\overline F(r)}r\right]dr. \tag{1}$$

**Proof.** Each hinge is $a_t\int_0^{1/l}1_{w/a_t\le r}\,dr$. Interchange finite sums with these integrals. In minus MAIN the log-width has a **plus** sign; its difference of expectations is the *negative* integral of the signed CDF against $dr/r$. The constant $\log a_t$ from rescaling the width and all other width-independent MAIN terms cancel at each original top and lift because both base laws have mass one. Translation permutes the sites in each positive plane. These facts give (1), including its negative mean-CDF term.

As $\sum_{g\notin\Phi} k_l(g)\le2$ even at $2,q,d$ and [`nativePsi_le_const_mul`][cheb] gives $\psi(z)\le C_\psi z$, $C_\psi=\log4+2$, (1) implies

$$\frac{|X(\mu)-X(\nu)|}{Q}\le
\frac{2\bar a}{b\Delta}(2C_\psi+1)J_a. \tag{2}$$

Indeed the whole prime-power mass below $1/r$ is at most $C_\psi/r$. There is **no separate height-restoration term**: the actual heights are already inside $F$. This is a measurable alternative to TOPLAW1, not a claim of a smaller numerical price on every dataset. For a one-sided certificate one can keep minus $\overline F/r$ in (1) and use $2C_\psi\max(0,\max F)/r$ on the ASK part only. No norm or absolute summation was applied to $X(\mu)$ itself.

### F. The hidden variable: equal-height classes

Let $L_s=\{t\in TT:a_t=s\}$ for each distinct measured height. **HEIGHTFIBRE2:** $J_a=0$ **if and only if**, for every $s,c,h,v$,

$$\sum_{t\in L_s}D_{c,h+t}(v)=0. \tag{3}$$

**Proof.** In $y=\log r$ take the finite spatial Fourier transform on $H$, separately on each plane. For a mode $\chi$, the folded transform is a sum of translates of the *one* compactly supported step function $\widehat D_c(\chi,e^y)$; its coefficient at shift $\log s$ is $s\,\sum_{t\in L_s}\chi(t)/S$ (or its conjugate by convention). Distinct translates of a nonzero compactly supported finite step function are linearly independent: the largest shift with a nonzero coefficient is alone on a nonempty interval at the left edge of its support. Thus either the raw mode vanishes identically or every height-class multiplier vanishes. Fourier inversion gives (3); the converse follows by substitution. Right-continuity at the finitely many jumps turns a.e. zero into pointwise zero. This proof assumes **no** covariance of widths with the base.

**Physical separator.** Suppose $3A_{\max}\exp(-x^{\varepsilon/3})<b$ on an actual admissible row. On the second positive plane, [the thick sites][thick] are exactly $h-u\in T_2$. All other widths there satisfy the original thin-ratio bound by taking their inverse partner for each top. Between the thin and thick widths the raw CDF is $D_{1,h}=-[(\mu-\nu)*1_{T_2}](h)$, with $(f*g)(h)=\sum_u f(u)g(h-u)$. If $|T_2|$ is odd, convolution by $1_{T_2}$ is invertible over $\mathbb R$: in $\mathbb F_2[H]$ its $2^e$-th power is the identity, so its integral convolution determinant is odd. Consequently (3) **requires**

$$\sum_{t\in L_s}\nu(h+t)=|L_s|/n\qquad\text{for every }s,h. \tag{4}$$

If the **measured lift histograms**, not necessarily individual widths, satisfy $P_u(c,h,v)=P_0(c,h-u,v)$, where $P_u=m^{-1}\sum_j1_{w_{uj}\le v}$, (4) also **suffices**: $D=(\mu-\nu)*P_0$ at each $c,v$, so (4) annihilates every summand in (3) after translation. Without this extra hypothesis use (4) only to reject impossible exact supports; compute (1) or (2) on the real widths.

There is also a quick **quantitative necessary test for this certificate**, without histogram covariance. Put $G=x^{\varepsilon/3}-\log(3A_{\max}/b)>0$ and $K(h)=[(\mu-\nu)*1_{T_2}](h)$. Throughout the common normalized separator $3\exp(-x^{\varepsilon/3})\le r<b/A_{\max}$, all thin sites are counted, no thick sites are counted. Hence

$$J_a\ \ge\ G\,\max_h\left|S^{-1}\sum_t a_tK(h+t)\right|. \tag{5}$$

A large lower bound in (5) rules out the *proposed price from (2)* at that tolerance. It is not a lower bound on the arithmetic error, which retains signs.

### G. Sharp support and a test on prescribed paid rows

**HEIGHTFIBRE3.** Index the native $H$ by powers of $5$ modulo sign, hence by $\mathbb Z/2^e$. Indeed $v_2(5^{2^k}-1)=k+2$ by induction, its powers are $1\bmod4$, and they exhaust the quotient. Call depth $j\in\{1,\ldots,e\}$ **free** if for every $s$ and every $r<2^{j-1}$ the counts of $L_s$ in the two residues $r$ and $r+2^{j-1}$ modulo $2^j$ agree. Write $E$ for the set of free depths. Then the exact smallest support of any probability law satisfying (4) is

$$\boxed{\,2^{e-|E|}\,}. \tag{6}$$

Here “smallest” is over all possible positive weights, not just uniform subsets. To see this, the polynomial $\sum_{t\in L_s}X^t$ vanishes at a primitive root of order $2^j$ exactly when its residue counts match across those two halves: reduce modulo $X^{2^{j-1}}+1=\Phi_{2^j}(X)$. This integer polynomial vanishes either at every primitive root of this order or at none. Fourier-transform (4): at a nonfree depth the law must have zero coefficient at **all** primitive characters of that order. This is exactly equal total mass on each pair of sibling residues at depth $j$ (the odd Fourier frequencies of the pushforward). At a free depth no such restriction is imposed. Every positive path must therefore split in two at every nonfree depth; placing all mass on one child at each free depth attains the count. A singleton $L_s$, or any odd $|L_s|$, forces $E=\varnothing$. Even cardinality of every class is not sufficient: on order eight, $L_1=\{0,4\}$ vanishes at primitive order eight, $L_2=\{1,3\}$ at primitive order four, so **all eight bases** are required.

**Usable on a specified support $B$.** Mark leaves outside $B$ unavailable. Work from residues mod $2^e$ up to the root: at a nonfree split **both** children must be feasible; at a free split **at least one** must be feasible. This decides existence on the actual proposed $B$, not just its cardinality. For externally established scalar row costs $c_u$, start with $c_u$ on $B$ and $+\infty$ outside. Use the arithmetic mean of child costs at a nonfree depth, the minimum at a free one. The root is the exact minimum of $\sum_u\nu(u)c_u$ subject to (4) and support in $B$: condition on the parent mass and minimize the linear cost on each subtree. This does **not** turn a mean-only bound for one law into rowwise costs, justify reweighting two separate losses, or prove any row payable.

### H. Exceptional configurations and signed certificates

**HEIGHTFIBRE4.** Use $e=2,q=11,d=7$, $H=\mathbb Z/4$, $TT=H$, $T_2=\{0\}$, one lift, $\beta=1$, $b=50/49$. On plane $c=1$ set width $b$ only at $h=u$, otherwise 1; all plane-0 widths are 1. Thus $Q=b/2=25/49$. The original heights are $(49,48,49,48)$, then $a_0=49+\xi$ with $0<\xi<1$; $N=49$ before, $50$ after. Use $\nu_+$ uniform on $\{0,1\}$ or $\nu_-$ uniform on $\{2,3\}$. Local congruences $q=3\bmod8$, $d=7\bmod16$, $(-d/q)=1$ hold, but no finite test pair is asserted `PairGood`, `PageN`, or a measured cost witness.

Before the split, the two height classes $\{0,2\},\{1,3\}$ satisfy (4) for either law and the widths translate. After it, a singleton makes the only exact matching law uniform. On the moving top, for $l\le48$ both widths are strictly active throughout the movement ($48b<49$); their derivatives are the same, so their comparison does not move. For $l\ge50$ neither width turns on. Only the width 1 at $l=49$ is crossed. Here $I_7$ frees just the first physical bit. Since $7\equiv-5^2\bmod16$, its square has dyadic coordinate 0 and even $q$ bit, with unique negative colour $((1,0),0)$ and mass $2/2=1$. Its positive partner at $t=0$ is $(1,0)$ in the abbreviated site notation. The difference in low-width probabilities is $\nu_\pm(0)-1/4=\pm1/4$. The spatial log-width sum in MAIN is equal on every base. Therefore the **entire** differences are

$$X(\mu)-X(\nu_\pm)=\pm\frac{\xi\log7}{196},\qquad
\frac{X(\mu)-X(\nu_\pm)}{Q}=\pm\frac{\xi\log7}{100}.$$

At $\xi=1/4$ this is $\pm\log7/400$ normalized; at $\xi=2^{-20}$ it is $\pm\log7/104857600$. This is a sign reversal of the transfer error, not of $Z(x)$ or an assertion under first-bad hypotheses.

**Why exact rejection is not numerical instability.** For $\nu_+$ put $L=49$, $S=194+\xi$. Each site's only uncancelled CDF is the difference of two log-width intervals of length $\log b$, with relative shift $\log(1+\xi/L)$, weights $L+\xi,L$, and spatial magnitudes $1/4$. Integrating the two end pieces and their overlap gives exactly

$$J_a=\frac{2L\log(1+\xi/L)+\xi\log b}{4S}.$$

Thus the exact support jumps from two to four while the comparison price tends to zero. Do not equate rounded heights to infer a true tie; for near ties compute (2).

**Negative and held-out controls.** Replace $L$ by 50 and $b$ by $51/50$ in the same construction. Only $l=50$ can change the signed difference and $\Lambda(50)=0$: $J_a>0$ but the full scalar difference is exactly zero. On the distinct host $q=3,d=23,e=3$, take $L=529$, $b=530/529$, $TT=H=\mathbb Z/8$, $a_t=L-(t\bmod2)$ except $a_0=L+1/4$, $T_2=\{0\}$, same translate widths, and $\nu$ uniform on $\{0,1,2,3\}$. $[23^2]=[17]=[5^4]\bmod32$; the unique selected ramified-square partner is at $h=4$, outside that support. The only nonzero coefficient is $-\log23/16928$ raw, or **$-\log23/8480$** after $Q$. All coefficients at $2,q,d$ and their powers, including zero coefficients, were retained.

### I. Executed tests and uncertainty

CPython 3.12.14, standard library, deterministic; `time python -u height_fibre.py`, final run 1.971 seconds elapsed. SHA-256 of the exact appendix program including its final newline: `0687d373d11208c61316d643bb8d646292979333b4eb1bf153b59df8494d2825`. No Lean execution, randomized models, probable primes or numerical logarithms.

| Independent constructions | Exact outcome |
|---|---|
| Factor every integer by trial division; enumerate **all modular units**, derive the local-unit image and unique CRT Frobenius, then evaluate the original full row before subtracting base expectations. Independently sieve primes and generate their powers, then use local quadratic/odd-unit products, ratio breakpoints and integrals of the signed CDF. | On $(q,d,e)=(11,7,2),(3,23,2),(3,71,3)$, 270 comparisons, 6,120 prime-power entries, 56 active breakpoint ties; agreement separately on every $p^i$ coefficient and every independent log coefficient of minus MAIN. 138 nonzero ASK vectors and 72 nonzero MAIN differences. 114 cases exactly matched the folded histograms; **18 other** cases had equal complete scalars despite a histogram mismatch. |
| One or two lifts, three width tables (including non-covariant widths), three height/top profiles, five base laws including nonuniform weights. All use $\beta=1$, $N=\lceil\max_t a_t\rceil$; main sweep $N=48,49,50$. Controls use $N=49,50,51,530$ as applicable. | Referee can reproduce all coefficients without evaluating a single log: represent $\log r$ for positive rational $r$ by its vector of prime valuations. For the two-way sign certificates only one signed coefficient and a positive $\log p$ remain. The closed expression for $J_a$ was also checked as a vector of log coefficients at $L=49,50,529$. |
| Each top is absent, height 1, or height 2 (labels only); enumerate every nonempty assignment on groups of order 4 and 8. Check every nonempty allowed support by direct translate counts of uniform subsets versus the binary tree, and the predicted global minimum. | Order 4: 80 families, 1,200 allowed-support tests. Order 8: 6,560 families, 1,672,800 tests. **Zero disagreements.** The direct finite sweep over uniform subsets alone would not prove the unrestricted real-weight result; the proof in G does. |
| Independent rational linear program: enumerate all linearly independent column supports in the *original* translate equations, solve by exact elimination, keep positive feasible vertices, price a signed integer leaf cost. Compare against the tree for every allowed support. | All 80 order-4 families (1,200 tests) and four specified order-8 families (1,020 tests), **2,220 exact LP price/feasibility comparisons**. Includes all-forced, partial, and alternating splits. This is a separate algorithm, not a separate human review. |

The prime checks stop at the chosen finite cutoffs. The first reconstruction costs a scan of the conductor's units for each new prime plus finite hinge sums; the reference support sweep is exponential by design. The usable depth test uses $O(e|TT|+2^e\,d_a)$ or less with counts per height ($d_a=$ number of distinct heights); the support/pricing tree once its depths are known has $O(2^e)$ nodes. No asymptotic prime sampling, root-growth estimate, or uniform geometric gain is inferred from these tests.

### J. Effect on the binding estimate

The [actual analytic consumer][paybase] gives $\operatorname{avg}_{t\in TT}Z(a_t/b)\le X(\mu)/Q+x^{1/2+\varepsilon}$. An independently certified bound for $X(\nu)/Q$ on the **same** data can use (1)–(2) to return to the original uniform law; $J_a=0$ makes the transfer exact. This does not supply $X(\nu)/Q$. If the comparison in (2) is at most $x^{1/2+\varepsilon}$, it fits the **one** comparison allowance of [TOPLAW4][tii]; do not spend the old height-restoration allowance again. Use the actual displacement $|a_t/b-x|$ to move the resulting *mean* of $Z$ to the requested anchor, and keep the thresholds and both interval edges. Exact height factoring in ASK is not a substitute for this separate movement of $Z$.

The [original normalized price][cost], with $z=x^\varepsilon$, is

$$\mathcal P_x=\frac{2a_E(1+m^2/k)}{mb\Delta}
+\frac{4nmz}{T\Delta}+\frac{2kz^2}{nT}.$$

The open payment concerns $X(\mu)/Q$ against $x^{\mathrm{CErr}(C)\varepsilon}\mathcal P_x$, or an independently sufficient same-host comparison. The [physical mean-loss supplier][pay] still requires actual `HidaSetting, DIV, EComp5, HComp, Count5, Slopes, QuotientSlopeBoundsWith, Losses, SlopeIneq, HHBound, FParams`, the error/large-$x$ and $B_0,N_c$ inequalities and, for the rounded conclusion, `GeometricSizeWindows`. In particular both $\operatorname{umean}(\mathrm{ASK}-\mathrm{Ga})\le\mathrm{LoP}$ and $\operatorname{umean}(\mathrm{IO})\le\mathrm{LoP}$ need the actual signed gains, Frobenius/inertia recovery, integral rank and measured widths, periods/heights and costs. Inspection of [the current integration map][map] and handoffs did not yield an instantiated independently paid set of words with these data. No `TT,T2,a,b,w,B` tuple was manufactured to satisfy them. No source premise or exponent was thereby discharged.

Fix $e_D,e_L,\varepsilon_1$ before $\varepsilon$, with $\varepsilon_1>0$ and the physical range restricted to $0<\varepsilon<1/52$ as required. For each $0<\varepsilon<\varepsilon_1$, **one** $C_\varepsilon$ must work before the location: for every $Y_0$ some $Y\ge Y_0$ satisfies $Z(y)\le C_\varepsilon y^{1/2+(e_D+e_L+7)\varepsilon}$ for **all real** $y\in[Y,Y^{3/2}]$. The branch's cyclic inlet can use coefficient one after its threshold. Keep the actual host sizes, complete cofinal windows and independently uniform caps; the local examples give none of them. Merged [#1205][pr1205] supplies the *implication* from the quantified bound, not its hypothesis.

### K. Evidence, recent source changes and continuity

Authority retrieved from the GitHub connection starting at 08:11 UTC, November 25. Main and draft #1201 rechecked at 08:33 UTC unchanged. [#1210][pr1210] merged at `5fefebadf176092a7cd83a4e16aca1f0ec0ce60e`; [#1211][pr1211] merged at the current main commit. Its [separate frozen external replay][stage] logged its external quantitative root and external RH root; it does **not** meet the independent dependency-clean native payment contract. [#1207][pr1207] (`0991c2f181f6943d0e57671cffebb1129d5ff4b4`; citation) was the only other open PR at intake. No other proof branch, API write, workflow trigger or merge by Census beyond the authorized report writes.

On the actual #1201 head the [required changed-closure job][failed] **FAILED**. Its log shows successful individual builds of `NativePrincipalEAtH`, `NativeCore33HostDegree`, `NativeExistingRecoveryPayment`, but errors at `NativeSummandCovolume.lean:45:10` and `:46:10`. The [full native build][full] was skipped. The [hosted semantic census][scan] at tested merge `79313611be39f71636d5ad2c3edd2c6f8238b241` scanned 3,592/3,592 tracked Lean files, zero scan failures, 191 visible-premise RH-return candidates: lexical leads, **not** transitive semantic clearance. The [#1205 terminal audit][terminal] lists only `propext, Classical.choice, Quot.sound` for its **conditional** window implication. No `GeoCl`, `geoCl`, `anyGeometry`, inlined vacuous substitute, upstream terminal root or assumed estimate was used as evidence for (1)–(6). The new claims have no Lean/CI receipt.

Key blobs (source paths and revision links below):

| Source | Git blob SHA |
|---|---|
| Main AGENTS / CURRENT_PROOF_CONTRACT / final directive | `a60620dca883d98dbe391ddd1ab5afcab805b96e` / `6fa886e125321056739a48d09fd33c95edaebf6b` / `395378d0e6525fab6c6ed9b7315c5de4c36329dd` |
| Main canonical VF / bound handoff / full semantic audit | `79030d70e8d3e0d08eef9bac53fef95c36eca2fb` / `31dc576197075a0448ced1a1c58e24a35c6d80d6` / `1029b89123471c04da44b0d91f382d7291cf1f14` |
| #1201 AGENTS / principal EAtH / existing recovery / dyadic Gz payment | `2bf7b75c5abb01962ecd9989320b600315e1a46f` / `ed98fe285987a38bc635a3729024bc3f3b1ac4b2` / `1076fb12c5bb2b1a85ed97f20aadfb105c4e2747` / `89b83b14a060443aceab44fdb38478f07af5678b` |
| Frame equivalence / raw host / Frobenius | `273552d726256547123fc298ef0c9c860b448956` / `0870b63eaf25cdd9bcf4bc2c8fd8f90d6d60c6e1` / `3060f0f62eace9e371a7c7c00db1d2a63d690de2` |
| Sharp kernel/MAIN / subgroup excess / thick mask / elementary Chebyshev | `3b6c2035d23b235ff9c0e1cb287eec8fdc516acc` / `d4606eb7ad3ee83dad06f063cfe3f4502c47eb67` / `3cdd42173c809b28752f8f9b686425bd9aa0d5f6` / `f88e3ae9da124aa23ad160ab1cf5389376486948` |
| Native scalar / cost / signed slope / integration map | `5203ec0e45b1d1f9b88d87e8b93455526169fbc8` / `07ec36dabad5d06c97dde991fb8c7de99af442d7` / `d8250851cd4ddc640fdc89df8475dcc2c09a636a` / `f5fbe62572ec786e2057790c35427ecb64720a2b` |
| StatementOC: upstream / cleaned community / #1201 copy | `12ab19c0176bd4135c2b23a7ee3ac22888df0122` / `04fc51afb2067e67d157e70df7fe571b098f3b7b` / `d02057b5bf0986c5a9952adc588a534d6b6d5978` |

**Latest actual handoffs.** At [reports intake][intake] `7b6c494fdb99a179835c93b7591b6b122a1be5b0` I enumerated the dated directories with no lookback cutoff; the [change interval][backfill] since the last Census intake `f1964c3ca5aa8509d4532ed55f22df16bf5faca7` comprised 39 commits/20 changed paths, none removed. Verified complete UTF-8 blobs for all changed canonical reports and all three Nov 22 recovery siblings; Coordinator 00/90 have identical full-blob objects at each date, counted once. Late Nov 22 backfill included FIELDWINDOW, THIN, SELECT, METRIC, Referee POWER (accepts FOURPOWER in scope) and Lean's even-power square-cell result. The three recovery openings are the same invocations as their completed canonical continuations, not extra runs. No November 23 folder. The inherited Nov 13–15 historical gap is not retroactively certified.

| Role, last verified and consumed section (New York time) | Blob, change since last Census and remaining boundary |
|---|---|
| Coordinator, Nov 24 23:09, 00/90, DIRECT1–3 then WIDTHLAW1–4 | `960b5843affc6cf2765d90b92547e12d656b50e8`. Measured subset transfer conditional; no paid base. TODAY=PENDING; YESTERDAY=CARRY_FORWARD. |
| Owner, Nov 24 19:56:24, 10, LOCALGAIN1–4 | `74f9baaea9fa0e4043e79e01e99d732e61daab86`. Served orbit sum and rounded maximum are coupled; actual relative image/word missing. TODAY=PENDING; YESTERDAY=CARRY_FORWARD. |
| Analytic, Nov 25 01:04:01, 20, TOPLAW1–4 | `11e89f84ece71cbaa810860ad37c268abfe754d1`, following Nov 24 WINDOW1–4 `32cc8ba27f99490c5aac69987f5eec86f0230958`. Common-height comparison plus genuine restoration; keep anchor movement and both edges. |
| Wheel, Nov 25 02:05:01, 30, PARTNER1–4 | `93f18c6e1475ff9ca69c1ae49df2dae1f07d3232`, following Nov 24 FIBER1–4 `eca61b12421b8d15e717677b1a4a71321fc81650`. Full stopped prime-partner mask and collateral; no certified lattice row. |
| Census, Nov 22 03:11, 40, FOURPOWER1–4 (before this run) | `f8f96d3ce7b2e2f1305b0a1984d6f936c9f55448`. No Nov 24 file; no invented run. Proper-power restoration retained; new work tests a different transfer. |
| Referee, Nov 24 20:13, 50, CORE1–5 | `bfb4c06772fe4b5df481d27921abe0a49ce73802`. Singleton DIV circular; constant-zero Frobenius rejected as a literal model. TODAY=PENDING; YESTERDAY=CARRY_FORWARD. |
| Lean, Nov 24 21:08, 60, METRIC1/PERIOD1 | `ff6acf015a1c890bd339d27b6b16aee456ee5b14`. An ordered pair of genuinely measured periods can suffice; freely assigned periods do not. TODAY=PENDING; YESTERDAY=CARRY_FORWARD. |

`LAST_VERIFIED=LAST_CONSUMED` at the listed sections, `NEW_UNCONSUMED=NONE` through intake; rechecked after milestone: only the new own file had appeared. [External handoffs][inbox] `7d63d434690d00dffce9c90335d41c4f62d85798` unchanged: EXT-20261018-PNT-1 keeps the $c=1$ and $p=R$ endpoints; corrected EXT-20261017-XCOORD-1 keeps $q=R$; EXT-20261014-3/-5 do not give uniform contraction. None supplies measured words or widths here.

### L. Specialist handoffs

| Recipient | Action on the same selected pair and host |
|---|---|
| Proof Architect | Record (6) as an exact support test, **not** new gain. Demand independent payable bases and measured heights first; reject an impossible exact thinning before requesting more geometry. |
| Owner Payment | Provide the actual top-height multiset and candidate paid base set together with the original integral word/image certificates, both mean losses and measured prices. Do not use a fitted row price as a certificate. |
| Analytic Type II | (1)–(2) replace only the width comparison and its height restoration, not movement of $Z$. Compare measured prices with TOPLAW1, use the smaller valid one, and retain the full window argument. |
| Finite Wheel | Retain the first-return mask and exclusions in your local split. The $d^2$ example checks the complementary ramified term that must survive reassembly; no first-return saving is credited twice. |
| Adversarial Referee | Check the extreme-shift proof, the necessity/sufficiency distinction in (4), and the raw-to-analytic bit swap. The 50 control refutes necessity for the scalar and the $23^2$ check reverses the sign. |
| Lean Verification | No new PR or terminal theorem requested. If an actual physical attachment needs it, (1) or the finite translate/sibling lemma is a nonterminal formalization candidate **after review**. |

### M. Ranked portfolio

1. **Continue the actual payment.** Test a real retained orbit: for each primitive combination construct an integral evaluation dividing the independently budgeted $p^D$, with retained rank and competing-edge divisibility. Pay the separately measured quotient, signed loss and costs on that host. Neither the width theorem nor prior relative Smith data supplies this.
2. **Use exact thinning only when possible.** For separated odd $T_2$, reject an infeasible support using (4)–(6); with measured translation covariance, feasible means exact equality of full excesses. Otherwise test the actual folded histograms. The independent ingredient is the location and arithmetic of the paid bases, not their count.
3. **Retain approximate thinning near ties.** Use (5) for inexpensive rejection, then evaluate (2) at exact ratio breakpoints; a singleton height is not a lower bound on actual arithmetic error. Suspend any attempt to repair an impossible exact support by rounding heights or dropping ramified powers.

### N. Resume and publication

Next run: obtain the **first independently certified same-pair base set $B$** with $TT,T_2,e,q,d,a_t,b,\beta,m,w$ and both signed row budgets. First test the actual thick separator and height-class sibling counts. If exact support is impossible or widths are not translation-covariant, evaluate (1), (2), (5) with the true cutoff, both sign bits, all lifts and the original $Q$. Report comparison cost in units of $x^{1/2+\varepsilon}$, separately from geometric price and anchor movement. Without those data record the missing field/word; do not rerun the toy host or claim a bound on the selected family.

`EXECUTION_COMPLETED; MATH=PAPER_PROOF/FINITE_COMPUTATION at stated scopes; INDEPENDENT_REVIEW=PENDING; NEW_LEAN_DECLARATIONS=NONE; SAME_HOST_PAYMENT=OPEN; NATIVE_RH=OPEN`. Opening verified at `e3b1bfb0215e456513d5dd7d65ee21018c2b1ae6`, blob `276104ccd605e9cf5bd72acb92d54030d16b7db5` (2,553 bytes). Milestone verified at `6c2a70919c3a28304ebef1bb6fc1053d18b817ed`, blob `42a5b319507c1726ed2fdf2d331738132f8094ab` (3,655 bytes); this complete prefix is preserved. Final publication requires exact-commit readback and is reported outside this append. No other role's file, source, policy, schedule or workflow was changed.

[maininst]: https://github.com/OVVO-Financial/RH_Lean/blob/7cb76d913acfd68fc036e01673a876a9a77be90f/AGENTS.md
[contract]: https://github.com/OVVO-Financial/RH_Lean/blob/7cb76d913acfd68fc036e01673a876a9a77be90f/CURRENT_PROOF_CONTRACT.md
[directive]: https://github.com/OVVO-Financial/RH_Lean/blob/7cb76d913acfd68fc036e01673a876a9a77be90f/docs/RHLEAN_FINAL_PR_1201_PROOF_CLOSURE_20261124.md
[prinst]: https://github.com/OVVO-Financial/RH_Lean/blob/c94fc79fe452d568eb877fbe64f17ad638e7bc0d/AGENTS.md
[vf]: https://github.com/OVVO-Financial/RH_Lean/blob/7cb76d913acfd68fc036e01673a876a9a77be90f/research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean
[up]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/StatementOC.lean
[community]: https://github.com/leanprover-community/riemann-hypothesis/blob/27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59/src/Formalism/StatementOC.lean
[copy]: https://github.com/OVVO-Financial/RH_Lean/blob/c94fc79fe452d568eb877fbe64f17ad638e7bc0d/RHLean/Analysis/AlpogeThin/Formalism/StatementOC.lean
[handoff]: https://github.com/OVVO-Financial/RH_Lean/blob/7cb76d913acfd68fc036e01673a876a9a77be90f/RHLean/Analysis/AlpogeNativeBoundHandoff.lean
[pay]: https://github.com/OVVO-Financial/RH_Lean/blob/c94fc79fe452d568eb877fbe64f17ad638e7bc0d/RHLean/Analysis/AlpogeThin/NativeExistingRecoveryPayment.lean
[eath]: https://github.com/OVVO-Financial/RH_Lean/blob/c94fc79fe452d568eb877fbe64f17ad638e7bc0d/RHLean/Analysis/AlpogeThin/NativePrincipalEAtH.lean
[frame]: https://github.com/OVVO-Financial/RH_Lean/blob/c94fc79fe452d568eb877fbe64f17ad638e7bc0d/RHLean/Analysis/AlpogeThin/NativeDyadicFrame.lean
[raw]: https://github.com/OVVO-Financial/RH_Lean/blob/c94fc79fe452d568eb877fbe64f17ad638e7bc0d/RHLean/Analysis/AlpogeThin/NativeDyadicHostRaw.lean
[sharp]: https://github.com/OVVO-Financial/RH_Lean/blob/c94fc79fe452d568eb877fbe64f17ad638e7bc0d/RHLean/Analysis/AlpogeNativeSharpASKBalance.lean
[sub]: https://github.com/OVVO-Financial/RH_Lean/blob/c94fc79fe452d568eb877fbe64f17ad638e7bc0d/RHLean/Analysis/AlpogeNativeSubgroupProjection.lean
[cheb]: https://github.com/OVVO-Financial/RH_Lean/blob/c94fc79fe452d568eb877fbe64f17ad638e7bc0d/RHLean/Analysis/NativePNTChebyshev.lean
[thick]: https://github.com/OVVO-Financial/RH_Lean/blob/c94fc79fe452d568eb877fbe64f17ad638e7bc0d/RHLean/Analysis/AlpogeNativeThickFreezing.lean
[cost]: https://github.com/OVVO-Financial/RH_Lean/blob/c94fc79fe452d568eb877fbe64f17ad638e7bc0d/RHLean/Analysis/AlpogeNativeCostNormalization.lean
[paybase]: https://github.com/OVVO-Financial/RH_Lean/blob/c94fc79fe452d568eb877fbe64f17ad638e7bc0d/RHLean/Analysis/AlpogeThin/NativeConstructedDyadicGzPayment.lean
[map]: https://github.com/OVVO-Financial/RH_Lean/blob/c94fc79fe452d568eb877fbe64f17ad638e7bc0d/research/ALPOGE_VERIFYTASK_NATIVE_INTEGRATION_20261124.md
[tii]: https://github.com/OVVO-Financial/RH_Lean/blob/7b6c494fdb99a179835c93b7591b6b122a1be5b0/research/agent_reports/2026-11-25/20-analytic-type-ii.md
[intake]: https://github.com/OVVO-Financial/RH_Lean/tree/7b6c494fdb99a179835c93b7591b6b122a1be5b0/research/agent_reports
[backfill]: https://github.com/OVVO-Financial/RH_Lean/compare/f1964c3ca5aa8509d4532ed55f22df16bf5faca7...7b6c494fdb99a179835c93b7591b6b122a1be5b0
[inbox]: https://github.com/OVVO-Financial/RH_Lean/blob/7b6c494fdb99a179835c93b7591b6b122a1be5b0/research/agent_reports/EXTERNAL_HANDOFFS.md
[pr1205]: https://github.com/OVVO-Financial/RH_Lean/pull/1205
[pr1207]: https://github.com/OVVO-Financial/RH_Lean/pull/1207
[pr1210]: https://github.com/OVVO-Financial/RH_Lean/pull/1210
[pr1211]: https://github.com/OVVO-Financial/RH_Lean/pull/1211
[stage]: https://github.com/OVVO-Financial/RH_Lean/actions/runs/45531344512/job/138927151494
[failed]: https://github.com/OVVO-Financial/RH_Lean/actions/runs/45548060914/job/138985874764
[full]: https://github.com/OVVO-Financial/RH_Lean/actions/runs/45548060914/job/138991231922
[scan]: https://github.com/OVVO-Financial/RH_Lean/actions/runs/45548060686/job/138982316988
[terminal]: https://github.com/OVVO-Financial/RH_Lean/actions/runs/45309220195/job/138160666430

### Replay appendix

Run `python height_fibre.py` with the standard library. This is finite test code, not a replacement for a geometric witness.

```python
"""Exact finite replay for PC-20261125-HEIGHTFIBRE. Python standard library."""

from collections import defaultdict
from fractions import Fraction as F
from functools import cache
from itertools import product
from math import ceil, gcd, isqrt


def clean(d):
    return {k: v for k, v in d.items() if v}


@cache
def factors(k):
    out = []
    p = 2
    while p * p <= k:
        v = 0
        while k % p == 0:
            k //= p
            v += 1
        if v:
            out.append((p, v))
        p += 1
    if k > 1:
        out.append((k, 1))
    return tuple(out)


def add_log(out, x, mass):
    for k, s in ((x.numerator, 1), (x.denominator, -1)):
        for p, v in factors(k):
            out[p] += s * v * mass


@cache
def direct_kernel(e, q, d, N):
    n, b = 2**e, 2**(e + 2)
    M = b*q*d
    hd = {s * pow(5, h, b) % b: h for h in range(n) for s in (1, -1)}
    sq = [{u*u % v for u in range(1, v)} for v in (d, q)]
    units = {u: (int(u % d not in sq[0]), int(u % q not in sq[1]), hd[u % b])
             for u in range(1, M) if gcd(u, M) == 1}
    loc, out = {}, {}
    for z in range(2, N + 1):
        f = factors(z)
        if len(f) != 1:
            continue
        p, i = f[0]
        if p not in loc:
            v = 1
            while M % (v*p) == 0:
                v *= p
            a = M//v
            I = {g for u, g in units.items() if (u - 1) % a == 0}
            f0, = [g for u, g in units.items() if (u-p) % a == 0 and (u-1) % v == 0]
            loc[p] = (I, f0)
        I, f0 = loc[p]
        row = {}
        for x, y, h in I:
            if (i*f0[0] + x) % 2 == 1:
                row[((1 + i*f0[1] + y) % 2, (i*f0[2] + h) % n)] = F(2, len(I))
        out[z] = row
    return out


@cache
def product_kernel(e, q, d, N):
    n, b = 2**e, 2**(e + 2)
    prime = [False, False] + [True] * max(0, N-1)
    for p in range(2, isqrt(N) + 1):
        if prime[p]:
            for k in range(p*p, N+1, p):
                prime[k] = False
    out = {}
    for p in range(2, N+1):
        if not prime[p]:
            continue
        z = p
        while z <= N:
            D, B = [([0, 1] if p == v else [int(pow(z, (v-1)//2, v) != 1)])
                    for v in (d, q)]
            H = (list(range(n)) if p == 2 else
                 [h for h in range(n) if (z - pow(5,h,b)) % b == 0 or
                  (z + pow(5,h,b)) % b == 0])
            assert len(H) == (n if p == 2 else 1)
            out[z] = {(1-y,h): F(2, len(D)*len(B)*len(H))
                      for x,y,h in product(D,B,H) if x == 1}
            z *= p
    return out


def law(n, support):
    return [F(1, len(support)) if u in support else F(0) for u in range(n)]


def direct_rows(K, n, m, heights, W):
    rows = []
    for u in range(n):
        ask, main = defaultdict(F), defaultdict(F)
        const = F(0)
        for t, a in heights.items():
            for j in range(m):
                const += a
                add_log(main, a, -a)
                for c, h in product(range(2), range(n)):
                    add_log(main, W[u,j,c,h], a/(2*n))
                for z, sites in K.items():
                    for (c,h), coeff in sites.items():
                        ask[z] += coeff * max(F(0), a/z - W[u,j,c,(h+t)%n])
        rows.append((ask, main, const))
    return rows


def row_difference(rows, mu, nu):
    def expect(values, law):
        return sum((v*p for p, v in zip(law, values)), F(0))
    assert expect([r[2] for r in rows], mu) == expect([r[2] for r in rows], nu)
    out = []
    for j in (0,1):
        keys = set().union(*(r[j] for r in rows))
        out.append(clean({k: expect([r[j].get(k,0) for r in rows],mu)
                             - expect([r[j].get(k,0) for r in rows],nu) for k in keys}))
    return tuple(out)


def folded(K, n, m, heights, W, mu, nu):
    A, main = defaultdict(F), defaultdict(F)
    separated_zero, folded_zero = True, True
    ties = 0
    for c,h in product(range(2),range(n)):
        hist, levels = defaultdict(F), defaultdict(F)
        for t, a in heights.items():
            for u, (prob, other) in enumerate(zip(mu, nu)):
                for j in range(m):
                    w = W[u,j,c,(h+t)%n]
                    hist[w/a] += (prob-other)*a
                    levels[a,w] += prob-other
        hst = clean(hist)
        separated_zero &= not clean(levels)
        folded_zero &= not hst
        xs = sorted(hst)
        assert sum(hst.values()) == 0
        mass = F(0)
        for lo, hi in zip(xs, xs[1:]):
            mass += hst[lo]
            add_log(main, hi/lo, -mass/(2*n))
            for z, sites in K.items():
                if (c,h) in sites:
                    ties += int(F(1,z) == hi or F(1,z) == lo)
                    A[z] += sites[c,h]*mass*max(F(0),min(hi,F(1,z))-lo)
    assert folded_zero == separated_zero
    return (clean(A), clean(main)), folded_zero, ties


def integrated_norm(n, heights, W, mu, nu):
    jumps = defaultdict(lambda: defaultdict(F))
    S = sum(heights.values())
    for c,h,t,u in product(range(2),range(n),heights,range(n)):
        a = heights[t]
        jumps[W[u,0,c,(h+t)%n]/a][c,h] += a*(mu[u]-nu[u])/S
    points = sorted(jumps)
    sums, out = defaultdict(F), defaultdict(F)
    for lo,hi in zip(points,points[1:]):
        for k,v in jumps[lo].items():
            sums[k] += v
        add_log(out, hi/lo, max(map(abs,sums.values())))
    return clean(out)


def arithmetic():
    counts = defaultdict(int)
    for e,q,d in ((2,11,7),(2,3,23),(3,3,71)):
        n = 2**e
        for typ, m, prof in product(range(3), (1,2), range(3)):
            top = [t for t in range(n) if prof != 2 or t%3 != 1]
            heights = {t: (F(48) if prof == 0 else (F(49-t%2) if prof == 1
                            else F(49) + F((3*t+1)%7,8))) for t in top}
            N = ceil(max(heights.values()))
            kd, kf = direct_kernel(e,q,d,N), product_kernel(e,q,d,N)
            assert kd == kf
            W = {}
            for u,j,c,h in product(range(n),range(m),range(2),range(n)):
                k = (h - u) % n
                W[u,j,c,h] = (F(1) + F((k+2*c+j)%3,2) if typ == 0 else
                              F(1) + F((3*h + (u+1)*(h+1) + 2*j+c)%7,4) if typ == 1
                              else F(50,49) if c==1 and k==0 else F(1))
            rows = direct_rows(kd,n,m,heights,W)
            mu = law(n, range(n))
            for nu in [mu, law(n,[0]), law(n,[0,1]), law(n,range(0,n,2)),
                       [F(2*(u+1),n*(n+1)) for u in range(n)]]:
                lhs = row_difference(rows,mu,nu)
                rhs, zero, ties = folded(kf,n,m,heights,W,mu,nu)
                assert lhs == rhs
                counts["comparisons"] += 1
                counts["power_vectors_entries"] += len(kd)
                counts["nonzero_main"] += bool(lhs[1])
                counts["nonzero_ask"] += bool(lhs[0])
                total = defaultdict(F, lhs[1])
                for z, coeff in lhs[0].items():
                    total[factors(z)[0][0]] += coeff
                counts["unequal_histogram_equal_scalar"] += not zero and not clean(total)
                counts["exact_histogram"] += zero
                counts["active_breakpoint_ties"] += ties
    print("physical formula diagnostics", dict(sorted(counts.items())))


def ramified():
    e,q,d,n,m=2,11,7,4,1
    b = F(50,49)
    W = {(u,0,c,h): b if c==1 and h==u else F(1)
         for u,c,h in product(range(n), range(2), range(n))}
    mu = law(n,range(n))
    for delta in (F(0),F(1,2**20),F(1,4),F(99,100)):
        a = {0:49+delta,1:F(48),2:F(49),3:F(48)}
        N=ceil(max(a.values()))
        k1,k2=direct_kernel(e,q,d,N),product_kernel(e,q,d,N)
        assert k1==k2 and k1[49]=={(1,0):1}
        rows=direct_rows(k1,n,m,a,W)
        for sig, supp in ((1,[0,1]),(-1,[2,3])):
            nu=law(n,supp)
            x=row_difference(rows,mu,nu)
            y,zero,_=folded(k2,n,m,a,W,mu,nu)
            assert x==y==(clean({49:sig*delta/196}), {})
            assert zero==(delta==0)
            Q=F(4)*b*F(1,4)/2
            assert x[0].get(49,0)/Q==sig*delta/100
        print("ramified square",delta,N,"+/-",delta/196,"log(7); divided by Q:",delta/100)


def withheld():
    for e,q,d,L,want in ((2,11,7,49,F(1,4*196)),
                          (2,11,7,50,F(0)),
                          (3,3,23,529,-F(1,4*8*529))):
        n, delta, b = 2**e, F(1,4), F(L+1,L)
        nu,mu=law(n,range(n//2)),law(n,range(n))
        W={(u,0,c,h):b if c==1 and h==u else F(1)
           for u,c,h in product(range(n),range(2),range(n))}
        a={t:F(L-t%2)+(delta if t==0 else 0) for t in range(n)}
        N=ceil(max(a.values()))
        kd,kf=direct_kernel(e,q,d,N),product_kernel(e,q,d,N)
        assert kd==kf
        val=row_difference(direct_rows(kd,n,1,a,W),mu,nu)
        other,zero,_=folded(kf,n,1,a,W,mu,nu)
        assert not zero and val==other==(clean({L:want}),{})
        form=defaultdict(F)
        add_log(form,1+delta/L,F(2*L)/(n*sum(a.values())))
        add_log(form,b,delta/(n*sum(a.values())))
        assert integrated_norm(n,a,W,mu,nu)==clean(form)
        print("norm identity and isolated site",e,q,d,L,clean({L:want}),
              "normalized coefficient",want/(b/2))


def members(mask,n):
    return [u for u in range(n) if (mask>>u)&1]


def zero_levels(S,e):
    return sum(1<<(j-1) for j in range(1,e+1)
               if all(sum(t%(2**j)==r for t in S)==
                      sum(t%(2**j)==r+2**(j-1) for t in S)
                      for r in range(2**(j-1))))


def tree_price(n, E, B, prices):
    p=[F(prices[u]) if (B>>u)&1 else None for u in range(n)]
    while len(p)>1:
        k=len(p)//2
        nxt=[]
        for a,b in zip(p[:k],p[k:]):
            opts=[v for v in (a,b) if v is not None]
            nxt.append((min(opts) if opts else None) if E&k else
                       (None if len(opts)<2 else (a+b)/2))
        p=nxt
    return p[0]


def vertices(n,sets):
    # Independent rational LP vertex enumeration in the original translate equations.
    M=[[1]*n+[F(1)]]
    M += [[int((u-h)%n in S) for u in range(n)]+[F(len(S),n)]
          for S in sets for h in range(n)]
    out={}
    for mask in range(1,1<<n):
        cols=members(mask,n); k=len(cols)
        A=[[F(r[u]) for u in cols]+[r[-1]] for r in M]
        for i in range(k):
            j=next((j for j in range(i,len(A)) if A[j][i]),None)
            if j is None:
                break
            A[i],A[j]=A[j],A[i]
            div=A[i][i]
            A[i]=[x/div for x in A[i]]
            for j in range(len(A)):
                if j!=i and A[j][i]:
                    v=A[j][i]
                    A[j]=[x-v*y for x,y in zip(A[j],A[i])]
        else:
            if any(a[-1] for a in A[k:]) or any(A[i][-1]<=0 for i in range(k)):
                continue
            out[mask]=dict(zip(cols,[A[i][-1] for i in range(k)]))
    return out


def masks():
    for e in (2,3):
        n, caps=2**e,2**(2**e)
        sets=[members(b,n) for b in range(caps)]
        zlev=[zero_levels(s,e) for s in sets]
        cost=[(u*u+3*u+5)%11-4 for u in range(n)]
        ok=[0]*caps; contained=[0]*caps
        for b,S in enumerate(sets):
            for k,B in enumerate(sets[1:],1):
                if all(n*sum((h+t)%n in B for t in S)==len(B)*len(S) for h in range(n)):
                    ok[b] |= 1<<k
                if k&b==k:
                    contained[b] |= 1<<k
        trees={(E,B):tree_price(n,E,B,cost) for E in range(1<<e) for B in range(1,caps)}
        cases=tests=lp=lp_tests=0
        for states in product(range(3), repeat=n):
            parts=[sum(1<<j for j,v in enumerate(states) if v==k) for k in (1,2)]
            parts=[b for b in parts if b]
            if not parts:
                continue
            E,allowed=(1<<e)-1,ok[0]
            for b in parts:
                E &= zlev[b]
                allowed &= ok[b]
            assert min(k.bit_count() for k in range(1,caps) if allowed>>k&1)==2**(e-E.bit_count())
            for B in range(1,caps):
                assert (trees[E,B] is not None)==bool(allowed & contained[B])
                tests+=1
            cases+=1
            if e==2 or (e==3 and tuple(parts) in ((17,10),(85,170),(1,254),(51,204))):
                V=vertices(n,[sets[k] for k in parts])
                prices={b:sum(x*cost[u] for u,x in v.items()) for b,v in V.items()}
                for B in range(1,caps):
                    best=min((v for b,v in prices.items() if b&B==b),default=None)
                    assert trees[E,B]==best
                    lp_tests+=1
                lp+=1
        print("dyadic tree",n,"families",cases,"support tests",tests,"exact LP",lp,lp_tests)


if __name__ == "__main__":
    ramified()
    withheld()
    arithmetic()
    masks()
```

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


## Census continuation | PC-20261125T160001Z-HALFSTEP-OPEN

**IN_PROGRESS; physical recovery not established.** Can the local integers of the selected square host themselves be the integral coefficient ring of the edge test? If they cannot, how must the admissible-image Smith profile change when the actual coefficient uniformizer is used, especially at odd competing depths? This is a test of the first physical attachment, not another width census. A period lattice, an incidence matrix or a positive index on a freely chosen module will not be counted as a physical section or dual.

Scheduled invocation 2026-11-25 11:00:01 EST (16:00:01 UTC); `RUN_ID_UNAVAILABLE`. Main `cad8dba7bbab6c709264061a3269790230c0d9a5`, main `AGENTS.md` `c7715e559ab64a8b2ebbf4623ecc246cb43179af`, contract `6fa886e125321056739a48d09fd33c95edaebf6b`, economical directive `8c16f05a43e8794fa78f77ba2645b3913669b93f`; draft #1201 `5eb0d87573d087aed794ef065ceea034021fa280`; community policy pin `251c7b05dd869ceba1aa42c6001c00b4010f23f9`, live `d91ae2678eea19a0c3045ffca37f1da757c2e719`. `native_economical_recovery_ack=NATIVE_ECONOMICAL_RECOVERY_V1; ECONOMICAL_RECOVERY_ROLE=CENSUS; final_1201_ack=FINAL_PR_1201_PROOF_CLOSURE_V1; FINAL_1201_ROLE=CENSUS; DIRECT_CORE_CUT_V1; STRICT_NO_GEOCL_ANYGEOMETRY_V1; continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1; publish_ack=REPORT_PUBLISH_RECOVERY_V1`.

**Frozen discriminator.** Read `PageN`/`WinPair` separately from full `PairGood` and `EdgeStep`. At the documented place above 43 (and separately at the ramified places), check actual inertia and the literal edge scalar relation. If an unramified base DVR and a ramified edge DVR differ, derive what integral base change predicts for `E(C^{-1}(w^c O^s))` at adjacent depths on the *same* hypothetical descended maps; look for counterexamples when the maps do not descend. Use independent exact arithmetic. Distinguish a genuine host calculation, a theorem conditional on descent, and any synthetic algebra controls. Do not assign physical dimensions, matrices, rank or gain without the section-to-edge and incoming dual constructors.

**Continuity.** Latest own completed section `PC-20261125T081101Z-HEIGHTFIBRE-FINAL`, commit `f45d18cfbf9a1f211cf861535139ddefd7bdb2b5`, blob `96b465a19ec643b83c8c21f27c20a100807246fc`, 53,276 bytes. At report intake `cc60e5e93d6c2183441b69d57ca1f73bc7ab588d` all seven roles have actual Nov 25 reports. The 17-commit comparison from the prior intake touched only seven Nov 25 report paths. Full Nov 24/25 canonical blobs and equal Coordinator mirrors were verified; no Nov 24 Census file or Nov 23 directory. New since prior intake: HEIGHTFIBRE, ROW, LIFT, JETCUT, FRAME, PRICE; PARTNER and the external inbox are unchanged. Today’s new frontier supersedes the prior width-only experiment; `RH=OPEN`.


### Verified milestone | PC-20261125T160001Z-HALFSTEP-M1

**An actual edge has a layer that a raw integer frame cannot represent by a common unramified base change.** At the tested place over 43 the native host is unramified, with residue degree exactly $2^{99}$ (modular powering independently agrees with the 2-adic order formula). In the upstream `UnramifiedQuadraticSetting`, $w$ is irreducible, $w^2=p$, and the residue degree of $O$ over that of $W$ is two. These are two different rings. The actual `LeAt` of any `IsEdge` is the intermediate lattice $S_O+wT_O$ on each twisted factor. The source `Re` relative to `HL(src)` and dual `Re'` relative to `HL(tgt)`'s dual have the **same** orders $o_i$ separately, before competitors. For every noncentral dominant tensor weight and $0<r<k$, some $o_i=1$ (and some $o_i=0$): change the rightmost tableau column in one noncentral block to move one letter past $r$. The paired, equal-cutoff diagonal can nevertheless be a pure power of $p$. None of these orders is a Smith factor of the physically restricted evaluation image without the actual maps.

**Independent finite check.** Original interlacing counts versus a separate Jacobi-Trudi determinant: 150 discovery profiles, 145 held-out profiles and 18 boundary profiles; no disagreement. For $k=6,r=2$ and even-slot raw weight $(2,1,0,0,0,0)$ the order histogram is $(2,16,32,20)$; the odd slot with the same raw weight gives its reverse. Together the 4,900 basis indices include exactly 2,452 odd orders. These are exact weight-carrier diagnostics, not a selected host or rank quota. Actual source/dual restriction, signed payment and RH remain open. Opening commit `f606404d54c31a9da915c6f4679881fa40b74d6e`, 56,096 bytes, verified at that commit.


## The Odd Edge Layer | PC-20261125T160001Z-HALFSTEP-FINAL

### A. Finding

**A noncentral physical edge weight necessarily has a depth-one direction in its original, unrestricted local lattice.** Its depth is one in the edge uniformizer $w$, not one in the rational prime $p=w^2$. This holds for both the source relative to its source host lattice and the dual relative to the **target dual** lattice. The same pairing at equal cutoffs can show only integral powers of $p$, hiding this direction. This rules out identifying both lattices, in one frame, with plain scalar extensions of unramified lattices. It does **not** prove that a geometric section hits the direction, that it survives the competing edges, or that using native arithmetic coordinates is impossible.

At a genuine native host place above 43 I constructed, on paper, a coefficient tower meeting the upstream local-ring predicate for the host residue degree. I did not find a full `PairGood`/geometric instance with a pairing-preserving map from its integral sections and dual. **Physical $E,C$, their admissible Smith factors and the signed payment: `BLOCKED`; RH remains open.** Claims `PC-20261125-HALFSTEP1–4` below are paper mathematics or exact finite checks, not new Lean declarations. Independent specialist review pending.

### B. Authority and question

[Main policy][hs-main] `cad8dba7bbab6c709264061a3269790230c0d9a5`; [current contract][hs-contract]; [November 25 assignment][hs-policy]; [November 24 closure][hs-closure]; actual [#1201 instructions][hs-prinst] at `5eb0d87573d087aed794ef065ceea034021fa280`. The public [square endpoint][hs-vf] remains $\exists C\ge0\ \forall R\ge2:\ |\pi(R^2)-VF_{\rm can}(R^2)|\le CR\log R$. Today's assignment is its independent native proof campaign, specifically the same-host selected/competing evaluations, not another equivalent endpoint.

**Mystery.** Can a computation in ordinary integral prime-exponent coordinates correctly measure the original edge before we have a geometric restriction? Prediction 1: if both members of a lattice pair descend in a common unramified frame, every relative elementary exponent becomes even after quadratic ramification. Prediction 2: if the original weights read the intermediate lattice, odd orders are intrinsic and equal-cutoff pairing alone can miss them. A single order-one witness discriminates. A separate test asks what survives for *jointly descended* selected and competing maps. No incidence array was declared to be either map.

### C. Genuine arithmetic | HALFSTEP1

Used the [versioned exact diagnostic][hs-hostscript] only for its genuine `WinPair`, `PageN` and original site clauses; the following residue-degree and coefficient-tower test is new to this continuation. $R=m=10^7$, $N=x=Y=R^2-1$, $\epsilon=9/560$, $e=99$, $q=3$, $d=3814\cdot5^{400}+1$. $TT=\{[1],[17],[47],[43^2]\}$, $T_2=H$, $b=\beta=w_{\rm width}=16$, $h=1$, $a_t=A_{\max}=16N$. Here, and only because of these data, $\lceil A_{\max}/\beta\rceil=N$, $\Delta=1$ and $Q=320000000$. The height and width diagnostic is not a physical payment. The two originally excluded first returns are $([1],17,1),([1],47,1)$. At partner $43^3$ the two retained reads are $([1],43,3)$ and $([43^2],43,1)$; shared value is not shared section. The native coefficient is $2/|I_p|$ times the **whole** coset indicator of $i\,{\rm Frob}_p+I_p$ before the signed source's logarithm and positive part. At 2 and 3 the non-$\Phi$ read vanishes on this test; $d>N$. These are verified endpoints, not a rule to remove ramified contributions on other windows.

The prime certificate for $d$ uses $5^{400}\mid d-1$, $5^{800}>d$, $2^{d-1}=1\bmod d$ and $\gcd(2^{(d-1)/5}-1,d)=1$. Thus every prime divisor of $d$ is $1\bmod 5^{400}$ and there cannot be two counting multiplicity. The script's strict inequalities use exact rational Taylor enclosures or integer powers. The [actual `PairGood.bounds/boxes`][hs-pair] at $X=Y^2$ are not certified for this tuple, and the [geometric window][hs-size] fails both top density and $26\le x^{3\epsilon/8}$. An eventual existence theorem does not select this tuple.

**Local field at 43.** The native conductor is $2^{101}qd$. The [actual Artin/inertia clauses][hs-primes] show that away from the conductor inertia is trivial. In native **$d,q$** order the bits at 43 are $(1,0)$, and the dyadic class is $[43]$ modulo sign. Independently, $d\bmod43=23$ is a square, so quadratic reciprocity gives $(43/d)=-1$; $43\bmod3=1$. An odd power of 43 is $3\bmod8$, not $-1$. For $j\ge1$, $v_2(43^{2^j}-1)=j+2$, by factoring the first square and then doubling. Hence its order modulo sign at $2^{101}$ is $f=2^{99}$. Exact modular powering gives $43^{f/2}=1+2^{100}\bmod 2^{101}$ and $43^f=1+2^{101}\bmod 2^{102}$. The sign factors do not enlarge this even order. The [degree of the native field][hs-square] is $4\cdot2^{99}$. Using the original inertia factors and Frobenius **modulo inertia**, the checks give:

| Rational prime | Ramification index in the native field | Residue degree | Places above it |
|---|---:|---:|---:|
| $2$ | $2^{99}$ | $2$ | $2$ |
| $q=3$ | $2$ | $2^{99}$ | $2$ |
| $d$ | $2$ | $2^{98}$ | $4$ |
| $43$ | $1$ | $2^{99}$ | $4$ |

In the first three rows the inertia images are respectively the dyadic factor, the $q$ sign and the $d$ sign, by the CRT unit description in [the prime source][hs-primes]. This is CRT on the full conductor, **not** CRT independence of a truncated block. The order checks treat the coordinate belonging to inertia as a coset; $d\equiv7\bmod16$ in particular. No local unramified formula was applied uniformly across this table.

Fix any actual $P\mid43$ and put $W=\widehat{\mathcal O_{H.E,P}}$, $Q_q=\operatorname{Frac}W$. It cannot serve as the edge ring $O$: $v_W(43)=1$, whereas a square has even valuation. Nor does just adjoining $\sqrt{43}$ give the extra residue degree required by [`UnramifiedQuadraticSetting`][hs-setting]. Here is a coefficient construction, with no change to the physical host: take $A=W[\zeta_{2^{102}}]$ in a fixed unramified closure, $O=A[w]$, $w^2=43$, $K_f=\operatorname{Frac}O$. The order calculation above gives $2^{102}\nmid43^f-1$, $2^{102}\mid43^{2f}-1$. The primitive residue root therefore first appears over the **quadratic** residue extension of $W$; it lifts by Hensel since 43 is odd. Thus $A/W$ is unramified quadratic. $X^2-43$ is Eisenstein over $A$: $O$ is the complete quadratic ramified DVR, with uniformizer $w$, residue cardinal $43^{2f}$ and rank four over $W$. Use the actual unramified arithmetic Frobenius on $Q_q$ (order $f$, reduces to $x\mapsto x^{43}$) and the natural inclusions. For every nonzero integer $z=43^s u$, the residue of its unit part in $\mathbb F_{43}^{\times}$ is a square in the even-degree residue field of $O$; lift a root of $u$ by Hensel and multiply by $w^s$. Zero is immediate. This checks even the predicate's `∀ z : ℤ, ∃ y, y²=z` field; $f\ge2$ is even. See the [DVR ramification conventions](https://stacks.math.columbia.edu/tag/0EXQ).

**Scope:** this supplies a local coefficient setting with $n'=f$ at a native place, not an identification of that $n'$ with the selected geometric orbit length of an actual `PairGood`/`EdgeStep` instance. No $r,\lambda_0,c_\star,D,t_S,t_T$ are assigned to that place. Bare `HidaSetting` only imposes $w^2=p$, not irreducibility of $w$; the uniformizer statements below use the *stronger* predicate.

### D. The original edge | HALFSTEP2

Let $k=m_{\rm loc}+1$, $0<r<k$, and take **any actual `IsEdge`** $\eta=(S,T)$ in the strong coefficient setting: $pT\subset S\subset T$ and $|T/S|=p^{n'r}$. This quantification does not assert that the displayed numerical host supplies a selected such edge. For each prescribed Frobenius twist, extend **both endpoints by the same twist** and denote them $S_O,T_O$. The literal [`LeAt`][hs-setting] applies $w^{-1}$ to the image of $pT$, hence
\[
 M_\eta=S_O+wT_O,\qquad
 T_O/M_\eta \xrightarrow{\;\times w\;} M_\eta/S_O
 \quad\text{is an isomorphism of residue spaces of dimension }r .
\]
Indeed the $W$-elementary exponents of $S$ in $T$ are $r$ ones and $k-r$ zeros. In one adapted target basis, $S_O=(w^2O)^r\oplus O^{k-r}$ and $M_\eta=(wO)^r\oplus O^{k-r}$. This describes an actual first constituent; a colour of a prime power has no such automatic identification. The two successive quotients are not two independent gains.

Now take dominant weights, using [`lamAt`][hs-setting], including the **negative reversed weight on odd slots**. Write $\lambda_s=\operatorname{lamAt}(\lambda_0,s)$, $\mu_{s,i}=\lambda_{s,i}-\lambda_{s,k}$ in one-based notation. Put $A_r=\sum_s\sum_{i\le r}\lambda_{s,i}$. In the [actual adapted basis][hs-basis], $x_i$ spans `HL(src)`, $p^{\nu_i}x_i$ spans `HL(tgt)`, and $o_i=A_r-\nu_i\ge0$. Consequently the two **separate** quotients
\[
 Q_S=R_\eta/HL(S),\qquad Q_T=R'_\eta/HL(T)^\vee
\]
have the same multiset $O/(w^{o_i})$. For the dual, the denominator basis is $p^{-\nu_i}x_i^\vee$, **not** the unscaled source dual. This is a relative-lattice calculation before any off-edge test; it is not `admG1`'s quotient or $E(L_c)$.

**Exact order spectrum (paper proof).** For each slot the basis proof indexes [`ssIdx`][hs-ss] by arrays of nonnegative integers with shape row totals $\mu_{s,j}$ and [the original interlacing inequalities][hs-inter]. Ordering the letters in each tableau row gives exactly these arrays: the number of letters $\le a$ in row $j+1$ cannot exceed the number $<a$ in row $j$. Thus there is no multiplicity lost in using semistandard tableaux. For a tableau $T_s$, let $b_r(T_s)$ count its letters $\le r$. The `pos_basisO/ten_basisO` exponents give
\[
 o=\sum_s\left(\sum_{i\le r}\mu_{s,i}-b_r(T_s)\right).
\]
The $r\lambda_{s,k}$ determinant twists cancel in this **difference**, not in the original $p^{-\nu_i}$ dual basis.

All integer orders from $0$ to
\[
 d_*=\sum_s\left(\sum_{i\le r}\mu_{s,i}-\sum_{i>k-r}\mu_{s,i}\right)
\]
occur. In a column of height $h$, the smallest entries are $1,\ldots,h$ and the largest are $k-h+1,\ldots,k$; these simultaneous extrema are legal tableaux. Transform the first to the last from the rightmost column to the left, within each column from bottom to top, increasing entries one unit at a time. Strict columns remain strict, and the column already finalized on the right is no taller, so weak rows are preserved. The count $b_r$ decreases by zero or one each time. The extremes above follow by summing $\min(h,r)$ and $\max(0,h+r-k)$ by column. Concatenate this path across slots.

In particular **$o=1$ occurs iff at least one block is noncentral**, under $0<r<k$. A direct witness: start in the top tableau; in the rightmost column of any nonempty normalized shape, of height $1\le h<k$, replace $h$ by $r+1$ if $h\le r$. If $h>r$, replace the suffix $r,\ldots,h$ by $r+1,\ldots,h+1$. Other slots remain top. A central weight has empty normalized shape and no such witness. The endpoints $r=0,k$ have only order zero. The unequal-to-equal cutoff distinction matters: [`adaptedEdge_pairing`][hs-rows] has exponent $(o_i-t_S)_++(o_i-t_T)_+$ in $w$; at $t_S=t_T=t$ it is $p^{(o_i-t)_+}$. An even pairing diagonal cannot rule out an odd lattice step.

**What is refuted:** for noncentral weights, the claim that either of these whole lattice pairs is a simultaneous, unshifted scalar extension from an unramified DVR in one common frame. Such an extension doubles **all** elementary exponents, whereas the pair has exponent one. A common homothety or compatible integral basis change does not change relative exponents. A ramification-aware construction, a charged shift, or a smaller realized submodule is not refuted. There is no inference that the odd directions are exceptionally bad or paid.

### E. Exact counts and falsification

For repeated slots count **all** basis indices, not just distinct exponents. If $s_\mu$ is the Schur polynomial, $a_s=\sum_{i\le r}\mu_{s,i}$ and $d_s=s_{\mu_s}(1^k)$, the number of odd orders is
\[
 \frac{\prod_s d_s-
 (-1)^{\sum_s a_s}\prod_s s_{\mu_s}(\underbrace{-1,\ldots,-1}_{r},1,\ldots,1)}{2}.
\]
This follows by taking the signed trace of the preceding exact tableau count. The two sides of the edge are not additional tensor factors.

| Test range | Shapes | $(\mu,r)$ profiles | Basis tableaux enumerated | Independent determinant evaluations |
|---|---:|---:|---:|---:|
| Discovery: all last-zero partitions, $2\le k\le5$, $|\mu|\le5$, every $1\le r<k$ | 52 | 150 | 1,725 | 750 |
| Holdout: $k=6$, $|\mu|\le6$, same rules | 29 | 145 | 8,113 | 850 |
| Boundary: $k=7$, zero, $(2,2,2,2,2,2,0)$, $(4,1,1,0,0,0,0)$, all $r$ | 3 | 18 | 2,129 | 111 |

Method one enumerates the original interlaced integer arrays. Method two does **not** use them: it evaluates the Jacobi–Trudi determinant by fraction-free elimination, specializing $r$ variables to $u$ and the rest to one. For $h_j$, use $\sum_{a=0}^j {r+a-1\choose a}{k-r+j-a-1\choose j-a}u^a$; $h_j=0$ for $j<0$. Evaluations at $0,\ldots,\sum_{i\le r}\mu_i$ determine the whole polynomial, and $u=-1$ separately checks parity. [Jacobi–Trudi formulas](https://faabian.github.io/algebraic-combinatorics/docs/AlgebraicCombinatorics.SymmetricFunctions.PieriJacobiTrudi.html). All **313 profiles / 1,711 evaluations** agreed. The theorem rests on the proof, not extrapolation.

Hand controls: the single-box order histogram is $(r,k-r)$; a determinant twist alone has $(1)$. At $k=6,r=2$ the raw block $(2,1,0,0,0,0)$ has counts $(2,16,32,20)$. Using that same raw weight on an odd slot gives $(20,32,16,2)$. Together the counts are $(40,384,1184,1684,1184,384,40)$, hence 2,452 odd among 4,900 indices. The tall rightmost-column control at $k=7,r=2$ gives $(15,10,3)$. None of these example weights is asserted to satisfy the numerical `Hyps` for a selected host. Missing directions can cancel in parity under tensoring; do not sum the odd counts of individual slots.

### F. The missing variable | HALFSTEP3

For any actual finite torsion module $Q'$ over a DVR with uniformizer $w$, $w^2=p$, set $V_j=p^jQ'/p^{j+1}Q'$ and let $N_j$ be **multiplication by $w$** there. Then $N_j^2=0$. If $b_i$ are the actual $w$-elementary exponents, with residue field $\kappa$, then
\[
 \dim_\kappa N_j V_j=\#\{i:b_i\ge2j+2\},\qquad
 \dim_\kappa(\ker N_j/N_jV_j)=\#\{i:b_i=2j+1\}.
\]
Proof on one summand: the $p$-layer has length $0,1$ or $2$. Only the length-two summand has nonzero image under $w$; only the length-one summand contributes to kernel modulo image. Both displayed spaces are killed by $w$, so no unspecified coefficient-field embedding into $V_j$ is needed. These counts at all $j$ determine every positive exponent, not the number of zero factors unless the ambient rank is known.

**Smallest length ambiguity:** $O/(w^2)$ and $O/(w)\oplus O/(w)$ both have unramified Smith group $\kappa^2$ in the explicit coefficient tower, but the two $w$-image ranks at $j=0$ are one and zero. Pad the first presentation with a unit factor for identical target rank. No ambiguity occurs at lengths 0 or 1. Direct multiplication at residue characteristic 43 gives image sizes 43 and 1 on the separate $\mathbb F_{43}$ algebra control of size 1,849, not the residue field of the numerical host. For the $(2,1)$ single-slot test, the kernel/image defects at $j=0,1$ are 16 and 20. Thus a count of integral $p$-layers alone loses information on the original edge lattice. Apply this test to any **separately constructed** admissible-image quotient; never substitute the unfiltered $Q_S,Q_T$ as its answer.

### G. Joint lifts | HALFSTEP4

There is a constructive replacement for rounding a depth to an integer. On the actual tower $O=A\oplus wA$, any **already constructed** integral map $U=U_0+wU_1$ acts on $a+wb$ by
\[
 (a,b)\longmapsto(U_0a+pU_1b,\;U_1a+U_0b).
\]
Demanding divisibility by $w^c$ means divisibility of these two outputs by $p^{\lceil c/2\rceil}$ and $p^{\lfloor c/2\rfloor}$ respectively. For a selected column with threshold $w^{2D+1}$ subtract the actual $p^D e_i$ in the first output, and use depths $D+1,D$. The **same** $a,b$ must satisfy every competing row. These are algebraically equivalent integral tests, not a way to construct unknown coefficients. Use them on source and admissible dual separately. In a bare Hida setting use $v_\pi(w)$ rather than silently setting it to one.

A useful falsifier for a **claimed unramified descent** on a common frame: let $E,C$ and the source lattice all be defined over $A$, with $I_j=E\{v:Cv\in p^j A^s\}$ and base change both maps to $O$. Write $J_c$ for the actual image at competitor depth $w^c$. Then
\[
 J_{2k}=I_k+w I_k,\qquad J_{2k+1}=I_{k+1}+w I_k .
\]
The two coefficients of each lift are separately free here *because the same matrices are over $A$*. In a common saturated target span, sorted $A$-exponents $\alpha_i(k)$ of $I_k$ give $w$-exponents $2\alpha_i(k)$ at $2k$ and $\alpha_i(k+1)+\alpha_i(k)$ at $2k+1$. Indeed $pI_k\subseteq I_{k+1}\subseteq I_k$ gives $\alpha_i(k)\le\alpha_i(k+1)\le\alpha_i(k)+1$. Modulo $w^{2t}$ the two coefficient quotients of the odd image have respective caps $p^t,p^t$; modulo $w^{2t+1}$ they have caps $p^{t+1},p^t$. Successive differences of the resulting lengths count exactly the proposed exponents. This does not presume compatible Smith bases for different depths. Deficient image ranks are handled in their common saturation, not by calling an infinite factor zero.

Five deterministic two-input matrix controls include dependent selected rows, zero competitors and nonunit pivots. Complete finite-ring enumeration versus the split base images agreed on 245 readout/competitor precision pairs at $p=2$ modulo $w^6$, and 125 at $p=3$ modulo $w^4$. These are **synthetic algebra checks only**. With $E(x)=x,C(x)=wx$ the scalar image exponents at $c=0,1,2,3,4$ are $0,0,1,2,3$: the even-depth parity prediction already fails at $c=2$ when descent is removed. Neither this example nor a width matrix is a physical counterexample. A divisor-closed prime partition changes no physical Smith factors under a **common** domain change $(E,C)\mapsto(EU,CU)$, since the selected image is identical. The previously checked $z=16,32,64$ width comparisons remain width-only; physical partition and boundary comparisons are `BLOCKED`, not zero. No CRT approximation or independent sign model was used.

### H. What is still missing

[`nativeSquareHost_exists_lattice_theta`][hs-square] supplies the actual half-different $B$, prescribed period lattice of rank $R^3-1$ over $\mathcal O_{H.E}$ and a nonzero complex theta for $1\le j\le R$ on the same pair. [`halfDifferent_local_eq_top`][hs-rows] gives the unit half-different away from its relative support; it does not construct a local section. [Period evaluation][hs-period] gives only proportional values under period translates. [The evaluated family][hs-family] takes the actual charts, formal group, directions, gauges and germs; [section descent][hs-section] takes faithful flatness and phase transport. None of these inputs can be replaced by a power of 43.

**First typed attachment to build on a genuinely selected pair:** at $j=1$, one actual place and one selected $\eta$, construct the localization of the measured integral section module into $V_{\lambda_0}(K_f)$, matching the normalized geometric evaluation with $be(F,G)=G(p^{A_r}F)$ in the actual adapted bases. Construct separately the incoming-dual localization, with the same $W,O,\iota,\sigma,w$, half-different, shifts and pairing. Verify the actual local $n'$, weights, target lattice and `IsEdge`, not only the scalar-ring predicate. Source membership is in $w^{-t_S}HL(S)$ and $R_\eta$, and every other outgoing restriction must land in $w^{c_\star}R_{\eta'}$. The dual is in $w^{-t_T}HL(T)^\vee$ and $R'_\eta$ and meets all other incoming conditions for [`EdgeFam`][hs-edges]. For `SrcTests`, retain `Ntgt` and exactly the other **selected** incoming off-edge clauses; the dual test may depend on the primitive combination. An arbitrary transpose does not construct it. At least one actual nonzero direction with an honest competitor is the smallest meaningful test; there is no numerically certified least full host. If the image avoids the odd constituent, prove that and charge any lost dimension; the existence of an odd direction does not require selecting it.

| Quantity on the **physical** section and dual | Status |
|---|---|
| Dimensions of $E_S,C_S,E_T,C_T$; selected/competing lifts; image before/after prime partitions | `BLOCKED`; not the period rank, the example's 4,900 tableau indices, or the four width sites |
| $E(C^{-1}(w^{c_\star}O^s))$, leakage, relative quota $\sum n_\eta/\dim V$ and actual recovery at $p^D$ | `BLOCKED`; no numeric rank or exponent supplied |
| Grouped exceptional generators, decay and stopping $a^{VS}M\subset N_{\rm loc}$ | `BLOCKED`; the $N_j$ test is not the `AllButLE` theorem |
| Same-frame residue index, placewise Gram, heights, both signed mean losses, normalized complete excess | `BLOCKED`; no index gain, signed saving or improved exponent |

The coefficient Hasse matrix on divisor-closed fibres has inverse $(-1)^{\Omega(h)-\Omega(d)}\prod_p{v_p(h)\choose v_p(d)}$ and unweighted column norm $\max_h2^{\Omega(h)}\le N^{\log2/\log z}$. Incomplete windows owe every omitted ancestor; at $zR^2\ge(R+1)^2$ a proper high ancestor is earlier, otherwise keep the boundary explicitly. No such norm measures the [original same-frame Gram][hs-gram] or identifies the physical operator. [`admG1`][hs-linkg] pays discarded quotient length only after its genuine generators and stopping inclusion; `Conclusion1`/`ParametersFill` supply signed gain separately. Keep [both mean losses][hs-slope], $\langle{\rm ASK}-{\rm Ga}\rangle\le{\rm LoP}$ and $\langle{\rm IO}\rangle\le{\rm LoP}$, without assigning `D0.Ga`. Retain every prime power, both character signs, ramified, complementary, thin and principal returns, and $Q=|TT|mb\Delta/2$. The terminal [square arithmetic][hs-candidate] is $G_N=C_N-D_N$ with $\log(n)(N/n-1)$, complete proper powers and Euler centering. No bound on it was inferred from the lattice result.

The [existing native payment and principal identity][hs-pay] and [merged #1205 window handoff][hs-window] require the actual height transfer and constants $e_D,e_L,\epsilon_1$ fixed before $\epsilon$. For every $0<\epsilon<\epsilon_1$, one $C_\epsilon$ must serve every requested $Y_0$ and the whole real window $[Y,Y^{3/2}]$ for some $Y\ge Y_0$, at exponent $1/2+(e_D+e_L+7)\epsilon$. This experiment neither proves nor refutes that statement. No prohibited geometry, imported terminal RH, new conditional endpoint or local Lean execution.

### I. Source and continuity receipts

Authority retrieval began shortly after the 16:00:01 UTC trigger. [#1212](https://github.com/OVVO-Financial/RH_Lean/pull/1212) merged policy at 12:08:04 UTC; [#1211](https://github.com/OVVO-Financial/RH_Lean/pull/1211) merged the separate external stage, not a native supplier. [#1205](https://github.com/OVVO-Financial/RH_Lean/pull/1205) merged as `fde7ea71ed88f540a8829554a8ab4602bda96f4d`. Open PRs on refresh: [#1201](https://github.com/OVVO-Financial/RH_Lean/pull/1201) draft (sole proof PR); [#1207](https://github.com/OVVO-Financial/RH_Lean/pull/1207) open `0991c2f181f6943d0e57671cffebb1129d5ff4b4`; [#1213](https://github.com/OVVO-Financial/RH_Lean/pull/1213) Euler-lever draft, observed `6719752c` then `ee9ab44585af73a5eaef2801883827d3aa594279`, not merged policy. Main and #1201 unchanged on prepublication refresh. [#1201 changed-closure job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45625259670/job/139243948070) **failed** on merge checkout `b225c317e9f102e67d183898205f4b226405048c`: `NativePrimeExponentJet.lean:37` invalid `.symm`; independent build diagnostics reported `NativeDyadicPrimePowerIncidence.lean:323/333` timeouts. [Full build](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45625259670/job/139255968247) skipped. [Semantic census](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45625260573/job/139243639205) scanned 3,621/3,621 tracked Lean files; 191 visible-premise RH-return candidates are review leads, not proof defects or transitive clearance. `SOURCE_INSPECTED; NEW_LEAN_VERIFICATION=NONE`.

| Inspected source (same order as hashes) | Git blob SHA |
|---|---|
| Main AGENTS / contract / economical / final directives | `c7715e559ab64a8b2ebbf4623ecc246cb43179af` / `6fa886e125321056739a48d09fd33c95edaebf6b` / `8c16f05a43e8794fa78f77ba2645b3913669b93f` / `395378d0e6525fab6c6ed9b7315c5de4c36329dd` |
| PR AGENTS / square-host constructor / host prime clauses / local rows | `4496eb12b74c58185eefa5d01b463ebca82e0ee4` / `b1d4cf64de78d94582c586b9b1651727c63389a9` / `5aa87d548312f8f5bf06ae72e88d874ac6eb70d0` / `7a5190692f1a3292ff391f23823da06772a2a74d` |
| PairGood / arithmetic diagnostic / joint recovery / evaluated family | `65cf7392ca0826eb602b18e580826b2719185a2a` / `74985f528f1ae6fb87aba534eb8a6053b09ea23e` / `32ff6612607bf57c00167f025a2d59ac2d28ebdc` / `7e8c4a9f5b1cd5349f870a32842d61f935245a33` |
| Original square statistic / mean-loss consumer / #1205 | `395e595d9ada914edbe41b441a4767a044634ad9` / `1076fb12c5bb2b1a85ed97f20aadfb105c4e2747` / `31dc576197075a0448ced1a1c58e24a35c6d80d6` |
| Community setting / adapted basis / interlacing / basis index | `1c9ff6676bad3634a65d75f248b53bb82c03d1ee` / `a06905c304fb168551eff773fd926ccfcc09fcab` / `025e77dfa0c5e44742149b694838176a95c77a46` / `a048c410ff3f38091ca6969a6aec35839366ed8a` |

Community policy pin `251c7b05dd869ceba1aa42c6001c00b4010f23f9`; live `d91ae2678eea19a0c3045ffca37f1da757c2e719`. ManyEdges (`7f043efac738a5e73ec785f5fe4435031babde4f`) and the adapted basis have identical complete blobs at both. PlaneCount changed `9093d64224dc052521d7114b52f833fa727eeb7d` to `700619442da4ead8fdebfd8d54eedce03dcf755a`: only two unused local bindings outside `linkG_at_core` were removed. No terminal upstream theorem was used.

**Latest actual reports.** Enumerated all 42 dated folders at [intake][hs-intake], not a date-limited search. The [17-commit backfill][hs-history] since the last verified Census intake touched only seven Nov 25 files and no recoveries. Fully fetched and verified the Git blob hash and UTF-8 length of all 15 available Nov 24/25 canonical files; the 00/90 mirror bytes agree on both dates. No Nov 23 folder, no Nov 24 Census file; previous actual Census was Nov 22, not a silent Nov 24 run. The prior watermark's documented older gaps remain gaps. All roles had actual Nov 25 sections; no `TODAY=PENDING` at intake. In the table, the left claim is the previous consumed section and the right is the new verified/consumed watermark on Nov 25 (EST). `GAP` as above; `NEW_UNCONSUMED=NONE` through the stated snapshot. Later runs are not inferred.

| Role/file stem | Prior → latest claim, timestamp; resume | Latest blob |
|---|---|---|
| Coordinator 00/90 | WIDTHLAW → JETCUT1–3, 07:10; chart filtration on the real germs | `f00778c30a19c9500d0f82108c3296b5b33c3ba2` |
| Owner 10 | LOCALGAIN → FRAME1–4, 08:09; the shared 43-power widths lose directions; use original signed operator | `30355ef9ac83c1fc4e2d88f3edf6b72db08c766f` |
| Analytic 20 | TOPLAW1–4, 01:04 → PRICE1–4, 09:09; restore crossings, projected Gram and whole-window movement | `37747c5895f879309caeebede03358b9c66740cf` |
| Wheel 30 | PARTNER1–4, 02:05, unchanged after FIBER; first-return labels retain all collateral | `93f18c6e1475ff9ca69c1ae49df2dae1f07d3232` |
| Census 40 | FOURPOWER → HEIGHTFIBRE1–4, 03:11; genuine height-fibre support test retained, not a primitive section | `96b465a19ec643b83c8c21f27c20a100807246fc` |
| Referee 50 | CORE → ROW1–4, 04:13; occurrence count is not relative rank; keep competing dual and bare-Hida distinction | `e857d047300ea59650c4c6eda319d64353c3c2ef` |
| Lean 60 | METRIC/PERIOD → LIFT1–2, 05:10; pay joint kernel correction on actual words | `665f7b85a0b93964f408c4342f6c8b09916fdf3a` |

[External inbox][hs-inbox] unchanged `7d63d434690d00dffce9c90335d41c4f62d85798`: EXT-20261018-PNT-1, corrected XCOORD and the #915 limsup do not attach an integral section. No historical table or settled build was rerun as a substitute. `CONTINUITY_COMPLETE` for the stated interval, not a retrospective certificate for every archived run.

### J. Specialist handoffs and resume

| Recipient | Concrete next use |
|---|---|
| Proof Architect | Record the strong local coefficient predicate as constructible at the arithmetic place with the stated $n'$, and the full selected instance as unbuilt. Require the actual orbit-length identification and first section before booking any rank. |
| Wheel | On one measured edge compute the $w$-odd component of the actual section germ and incoming dual, or prove that their images miss it. Use the two-row integral formula at the prescribed $c_\star,D$; no new prime partition until the same maps exist. |
| Referee | Check `lamAt` on odd slots, the two different host denominators of $Q_S,Q_T$, the rightmost-column witness and the necessity versus sufficiency of the parity obstruction. |
| Owner | On a claimed unramified Smith calculation retain multiplication by $w$ and compare local length to the same measured global frame; do not count $Q_S,Q_T$ twice or convert them into `Ga`. |
| Analytic | Charge any removed ancestor and its actual Gram/width cost; an order-one direction is neither an archimedean norm nor the signed height cost. |
| Lean Verification | Review the order-one witness and the $w$-layer recovery lemma as nonterminal candidates on #1201 only if useful; first obtain a pairing-preserving section/dual detail and resolve current hosted failures. No implementation or workflow requested by this report. |

**Ranked portfolio.** (1) **Continue** the ramification-aware physical restriction: choose an actually supplied $j=1$ section and a primitive dual at the same admitted $\eta$; measure the normalized pair and the complete competitor stack in its given bases. (2) **Retain** the $w$-action test for any realized quotient, using the exact odd-profile prediction above to catch a hidden change of lattice. Even factors alone do not prove descent or recoverability. (3) **Reject** plain common unramified base change of the full noncentral adapted pair; **suspend** new width-only, determinant-only or unweighted $J$ scans unless a new physical comparison or boundary is supplied.

**Next run, one decisive test:** obtain one actual source-to-germ restriction *and* its compatible incoming-dual test on a `PairGood` window at a certified place; evaluate their projections to the order-one constituent on the original `be` normalization and test a nontrivial competing edge on the identical lift. Then and only then extend to all competitors and calculate the image, quota, leak and stopping layers. If no such data appear, report the first missing map rather than repeat the 313 profiles. No scheduling, proof PR, Lean source or other role's report was changed.

`EXECUTION_COMPLETED; MATH=PAPER_PROOF / FINITE_COMPUTATION at the stated scopes; INDEPENDENT_SPECIALIST_REVIEW=PENDING; PHYSICAL_E_C=BLOCKED; SAME_HOST_PAYMENT=OPEN; NATIVE_RH=OPEN`. Opening `f606404d54c31a9da915c6f4679881fa40b74d6e` (56,096 bytes) and milestone `468d23adb4a23f0cca89d5834e151dc6a37707d9` (57,853 bytes, blob `240591824d87e671191cf301a03932a4df5fbe51`) were re-fetched at the exact commits. Direct Git tunnel 403; the replacement endpoint was not credited after validation/service errors. Authenticated, non-forced Git-data publication was restricted to this path with a fresh head lease and complete-prefix checks. Final receipt follows commit readback outside this text.

### K. Reproduction

CPython 3.12.14, Linux, standard library only; integer/rational arithmetic, no random seed, floating sign, local Lean, or manual prime table. Final replay: 2.163 s shell wall time. Interlaced arrays are exhaustively enumerated in the stated small shapes; the independent determinants are polynomial in matrix size per evaluation. The joint control enumerates $p^{4t}$ input pairs for a two-input map over $O/(w^{2t})$; this was intentionally not scaled. On a checkout of #1201 at the pinned SHA, extract the single Python block below as `halfstep.py` and run `python halfstep.py scripts/native_economical_recovery_widths.py`. Script SHA-256 `aaa94d8a96822d4059984ced84912847d53b278c38035e57c5fcce6f1c186677`; input script Git blob as listed above.

<details><summary>Complete exact replay</summary>

```python
"""Census HALFSTEP: integer-only host, adapted-weight, and congruence tests."""
from collections import Counter
from functools import cache
from itertools import product
from math import comb, gcd
from pathlib import Path
import runpy
import sys


def valuation2(n):
    return (n & -n).bit_length() - 1


def host(script):
    src = runpy.run_path(str(script))
    src["certify_host"]()
    src["check_stronger_size_band"]()
    d, mod, p, e = src["D"], src["DYADIC"], 43, src["E"]
    assert gcd(p, mod * 3 * d) == 1
    f = 1
    while pow(p, f, mod) not in (1, mod-1):
        f *= 2
    assert p % 8 == 3 and f == 2**(e+2-valuation2(p-1)-valuation2(p+1)+1)
    assert pow(p, f//2, mod) == 1 + mod//2 and pow(p, f, mod) == 1
    assert pow(p,f,2*mod)==1+mod and pow(p,2*f,2*mod)==1
    # Independent reciprocity check: p,d are both 3 mod 4.
    sq43 = {t*t % p for t in range(1,p)}
    d_sign = -1 if d % p in sq43 else 1
    assert (d_sign, pow(p, (d-1)//2, d), p % 3) == (-1, d-1, 1)
    assert src["frobenius"](p) == (1,0,p)
    assert src["active_reads_at_site"](1, p**3) == [
        (1,p,3,"retained"), (p**2,p,1,"retained")]
    assert [(t,l,i) for h in (1,17,47,p*p)
            for t,l,i,label in src["active_reads_at_site"](0,h)
            if label=="first-excluded"] == [(1,17,1),(1,47,1)]
    print("HOST", "d mod 43", d%p, "f", f, "g", 4*2**e//f,
          "half-power", pow(p,f//2,mod), "bits", src["frobenius"](p))
    for l, inertia in ((2,2**e),(3,2),(d,2),(p,1)):
        db,qb,h = src["frobenius"](l)
        u=h if l!=2 else 1
        n=1
        while (pow(u,n,mod) not in (1,mod-1) or
               (l!=d and db*n%2) or (l!=3 and qb*n%2)):
            n*=2
        print("efg",str(l) if l!=d else "d",inertia,n,4*2**e//(inertia*n))


@cache
def parts(total, k):
    if k == 1:
        return ((total,),)
    return tuple((a,)+b for a in range(total+1) for b in parts(total-a,k-1))


def interlaced(mu):
    k = len(mu)
    def walk(j, prev, wt):
        if j == k:
            yield wt
            return
        for col in parts(mu[j], k):
            left = right = 0
            for a in range(k):
                right += col[a]
                if prev is not None and right > left:
                    break
                left += prev[a] if prev is not None else 0
            else:
                yield from walk(j+1, col, tuple(x+y for x,y in zip(wt,col)))
    return walk(0,None,(0,)*k)


def det(A):
    M = [r[:] for r in A]
    prev = sign = 1
    for i in range(len(M)-1):
        j = next((j for j in range(i,len(M)) if M[j][i]),None)
        if j is None:
            return 0
        if j != i:
            M[i], M[j] = M[j], M[i]
            sign *= -1
        for j in range(i+1,len(M)):
            for l in range(i+1,len(M)):
                num = M[i][i]*M[j][l]-M[j][i]*M[i][l]
                assert num % prev == 0
                M[j][l] = num//prev
        prev = M[i][i]
    return sign*M[-1][-1] if M else 1


def schur(mu,r,t):
    k = len(mu)
    @cache
    def h(j):
        return sum(comb(r+a-1,a)*comb(k-r+j-a-1,j-a)*t**a for a in range(j+1))
    n = sum(v>0 for v in mu)
    return det([[h(mu[i]-i+j) for j in range(n)] for i in range(n)])


def weights(shapes, label):
    cases = states = evaluations = 0
    pick = {}
    for mu in shapes:
        k = len(mu)
        hist = [Counter() for _ in range(k)]
        for occ in interlaced(mu):
            states += 1
            for r in range(1,k):
                hist[r][sum(mu[:r])-sum(occ[:r])] += 1
        for r in range(1,k):
            cases += 1
            H, top = hist[r], sum(mu[:r])
            assert set(H) == set(range(top-sum(mu[-r:])+1))
            if any(mu):
                assert H[0] and H[1]
            for t in range(-1,top+1):
                assert schur(mu,r,t) == sum(v*t**(top-j) for j,v in H.items())
                evaluations += 1
            assert sum(v for j,v in H.items() if j%2) == (
                schur(mu,r,1)-(-1)**top*schur(mu,r,-1))//2
            if r==2 and (mu in ((1,0,0,0,0,0),(2,1,0,0,0,0),(2,2,2,2,2,2,0))):
                pick[mu] = [H[i] for i in range(len(H))]
    print(label, "shapes",len(shapes),"profiles",cases,"tableaux",states,"det-checks",evaluations)
    if pick:
        print("FIXTURES",pick)


def shapes(k,size):
    return [x for n in range(size+1) for x in parts(n,k)
            if x[-1]==0 and all(a>=b for a,b in zip(x,x[1:]))]


def paired_and_layers():
    k,r=6,2
    lam=(2,1,0,0,0,0)
    factors=[]
    for a in (lam,tuple(-x for x in reversed(lam))):
        mu=tuple(x-a[-1] for x in a)
        H=Counter(sum(a[:r])-r*a[-1]-sum(v[:r]) for v in interlaced(mu))
        factors.append(H)
    joint=Counter()
    for i,x in factors[0].items():
        for j,y in factors[1].items():
            joint[i+j]+=x*y
    A=lambda H: [H[i] for i in range(max(H)+1)]
    # At -1 the signed order-trace reverses by the sum of the two top sizes.
    traces=[]
    for a in (lam,tuple(-x for x in reversed(lam))):
        mu=tuple(x-a[-1] for x in a)
        traces.append((-1)**sum(mu[:r])*schur(mu,r,-1))
    odd=sum(v for h,v in joint.items() if h%2)
    assert 2*odd==sum(joint.values())-traces[0]*traces[1]
    print("TENSOR",A(factors[0]),A(factors[1]),A(joint),odd)
    # Enumerate actual multiplication by w on every small two-step quotient.
    p=43
    for a in range(8):
        for j in range(4):
            d=max(0,min(2,a-2*j))
            X=list(product(range(p),repeat=d))
            image={tuple(([0]+list(x))[:d]) for x in X}
            kernel=[x for x in X if not any(([0]+list(x))[:d])]
            assert len(image)==p**int(a>=2*j+2)
            assert len(kernel)//len(image)==p**int(a==2*j+1)
    print("W-ACTION",p,32,"layer checks; twin groups of size",p*p,
          "w-image sizes",p,1)


def dot(row,x):
    return sum(a*b for a,b in zip(row,x))


def variants(E,C,p,t):
    # Explicit quotient images at each readout precision, over the two rings.
    mod = p**t
    domain = list(product(range(mod),repeat=2))
    proj = lambda rows,x: tuple(dot(row,x) for row in rows)
    L = [(proj(E,x),proj(C,x)) for x in domain]
    def depth(vals):
        j=0
        while j<t and all(v%p**(j+1)==0 for v in vals):
            j+=1
        return j
    # In the independent O path we enumerate actual a+w*b as base-p digit
    # strings; a competing output vanishes iff its first c w-digits vanish.
    def raw(a,b):
        z=0
        for j in range(t):
            z+=(a//p**j%p)*p**(2*j)+(b//p**j%p)*p**(2*j+1)
        return z
    R = [(tuple(raw(x,y) for x,y in zip(a,b)),
          tuple(raw(x,y) for x,y in zip(s,v))) for (a,s),(b,v) in product(L,repeat=2)]
    integ = []
    for k in range(t+1):
        I = {tuple(y%mod for y in v) for v,c in L if depth(c)>=k}
        integ.append([len({tuple(y%p**j for y in v) for v in I}) for j in range(t+1)])
    checks = 0
    for c in range(2*t+1):
        Im = {v for v,a in R if not any(y%p**c for y in a)}
        for j in range(2*t+1):
            got = len({tuple(y%p**j for y in v) for v in Im})
            expect = integ[(c+1)//2][(j+1)//2] * integ[c//2][j//2]
            assert got == expect
            checks+=1
    return checks


def main():
    host(Path(sys.argv[1]))
    weights([mu for k in range(2,6) for mu in shapes(k,5)],"DISCOVERY")
    weights(shapes(6,6),"HOLDOUT")
    weights([(2,2,2,2,2,2,0),(4,1,1,0,0,0,0),(0,)*7],"ADVERSARIAL")
    paired_and_layers()
    examples = [([[1,0],[0,1]],[[1,1]]), ([[1,1],[0,3]],[[1,-1],[0,3]]),
                ([[2,1],[4,2]],[[2,-1]]), ([[3,0],[0,9]],[[0,0]]),
                ([[2,3],[-1,1]],[[1,2],[2,4]])]
    for p,t in ((2,3),(3,2)):
        print("JOINT",p,t,len(examples),sum(variants(E,C,p,t) for E,C in examples))
    # Genuinely w-valued scalar competitor: C(x)=w*x and E(x)=x.
    p=3
    for c in range(5):
        # O/(w^4), represented as a+b*w, a,b mod 9. Multiply by w=(p*b)+a*w.
        def ord4(a,b):
            av = 2 if a%9==0 else int(a%3==0)
            bv = 2 if b%9==0 else int(b%3==0)
            return min(4,2*av,1+2*bv)
        got=min(ord4(a,b) for a,b in product(range(p*p),repeat=2) if ord4(p*b,a)>=c)
        assert got==max(0,c-1)
    print("NONDESCENDED", [max(0,c-1) for c in range(5)])


if __name__ == "__main__":
    main()
```

</details>

[hs-main]: https://github.com/OVVO-Financial/RH_Lean/blob/cad8dba7bbab6c709264061a3269790230c0d9a5/AGENTS.md
[hs-contract]: https://github.com/OVVO-Financial/RH_Lean/blob/cad8dba7bbab6c709264061a3269790230c0d9a5/CURRENT_PROOF_CONTRACT.md
[hs-policy]: https://github.com/OVVO-Financial/RH_Lean/blob/cad8dba7bbab6c709264061a3269790230c0d9a5/docs/RHLEAN_NATIVE_ECONOMICAL_RECOVERY_20261125.md
[hs-closure]: https://github.com/OVVO-Financial/RH_Lean/blob/cad8dba7bbab6c709264061a3269790230c0d9a5/docs/RHLEAN_FINAL_PR_1201_PROOF_CLOSURE_20261124.md
[hs-prinst]: https://github.com/OVVO-Financial/RH_Lean/blob/5eb0d87573d087aed794ef065ceea034021fa280/AGENTS.md
[hs-vf]: https://github.com/OVVO-Financial/RH_Lean/blob/cad8dba7bbab6c709264061a3269790230c0d9a5/research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean#L24
[hs-hostscript]: https://github.com/OVVO-Financial/RH_Lean/blob/5eb0d87573d087aed794ef065ceea034021fa280/scripts/native_economical_recovery_widths.py
[hs-pair]: https://github.com/OVVO-Financial/RH_Lean/blob/5eb0d87573d087aed794ef065ceea034021fa280/RHLean/Analysis/AlpogeThin/Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean#L37
[hs-size]: https://github.com/OVVO-Financial/RH_Lean/blob/5eb0d87573d087aed794ef065ceea034021fa280/RHLean/Analysis/AlpogeThin/NativeGeometricCostWindows.lean#L26
[hs-primes]: https://github.com/OVVO-Financial/RH_Lean/blob/5eb0d87573d087aed794ef065ceea034021fa280/RHLean/Analysis/AlpogeThin/NativeDyadicHostPrimes.lean#L36
[hs-square]: https://github.com/OVVO-Financial/RH_Lean/blob/5eb0d87573d087aed794ef065ceea034021fa280/RHLean/Geometry/NativeSquareHostRealization.lean#L71
[hs-setting]: https://github.com/leanprover-community/riemann-hypothesis/blob/251c7b05dd869ceba1aa42c6001c00b4010f23f9/src/Formalism/SharpRestriction/GrowthBounds/UnramifiedQuadraticSetting.lean
[hs-basis]: https://github.com/leanprover-community/riemann-hypothesis/blob/251c7b05dd869ceba1aa42c6001c00b4010f23f9/src/Formalism/SharpRestriction/GrowthBounds/ScaleEdges/EdgeLatticeAdaptedBasis.lean#L166
[hs-ss]: https://github.com/leanprover-community/riemann-hypothesis/blob/251c7b05dd869ceba1aa42c6001c00b4010f23f9/src/Formalism/GradedWeylDivisibility/StatementD.lean#L15
[hs-inter]: https://github.com/leanprover-community/riemann-hypothesis/blob/251c7b05dd869ceba1aa42c6001c00b4010f23f9/src/Formalism/GradedWeylDivisibility/StatementC.lean#L43
[hs-rows]: https://github.com/OVVO-Financial/RH_Lean/blob/5eb0d87573d087aed794ef065ceea034021fa280/RHLean/Geometry/NativeHostIntegralJetRows.lean
[hs-period]: https://github.com/OVVO-Financial/RH_Lean/blob/5eb0d87573d087aed794ef065ceea034021fa280/RHLean/Geometry/NativeThetaPeriodEvaluation.lean
[hs-section]: https://github.com/OVVO-Financial/RH_Lean/blob/5eb0d87573d087aed794ef065ceea034021fa280/RHLean/Geometry/NativeThetaSectionRealization.lean#L82
[hs-family]: https://github.com/OVVO-Financial/RH_Lean/blob/5eb0d87573d087aed794ef065ceea034021fa280/RHLean/Geometry/NativeThetaEvaluatedFamily.lean#L133
[hs-edges]: https://github.com/leanprover-community/riemann-hypothesis/blob/251c7b05dd869ceba1aa42c6001c00b4010f23f9/src/Formalism/SharpRestriction/GrowthBounds/ScaleEdges/ManyEdges.lean#L23
[hs-gram]: https://github.com/OVVO-Financial/RH_Lean/blob/5eb0d87573d087aed794ef065ceea034021fa280/RHLean/Geometry/NativeSummandCovolume.lean
[hs-linkg]: https://github.com/leanprover-community/riemann-hypothesis/blob/251c7b05dd869ceba1aa42c6001c00b4010f23f9/src/Formalism/SharpRestriction/GrowthBounds/PlaneCountTheoremWithConstants.lean#L598
[hs-slope]: https://github.com/OVVO-Financial/RH_Lean/blob/5eb0d87573d087aed794ef065ceea034021fa280/RHLean/Analysis/AlpogeNativeSignedSlopeComparison.lean
[hs-candidate]: https://github.com/OVVO-Financial/RH_Lean/blob/5eb0d87573d087aed794ef065ceea034021fa280/RHLean/Analysis/AlpogeNativeSquareCandidateCapacity.lean#L88
[hs-pay]: https://github.com/OVVO-Financial/RH_Lean/blob/5eb0d87573d087aed794ef065ceea034021fa280/RHLean/Analysis/AlpogeThin/NativeExistingRecoveryPayment.lean#L99
[hs-window]: https://github.com/OVVO-Financial/RH_Lean/blob/cad8dba7bbab6c709264061a3269790230c0d9a5/RHLean/Analysis/AlpogeNativeBoundHandoff.lean#L158
[hs-inbox]: https://github.com/OVVO-Financial/RH_Lean/blob/cc60e5e93d6c2183441b69d57ca1f73bc7ab588d/research/agent_reports/EXTERNAL_HANDOFFS.md
[hs-history]: https://github.com/OVVO-Financial/RH_Lean/compare/7b6c494fdb99a179835c93b7591b6b122a1be5b0...cc60e5e93d6c2183441b69d57ca1f73bc7ab588d
[hs-intake]: https://github.com/OVVO-Financial/RH_Lean/tree/cc60e5e93d6c2183441b69d57ca1f73bc7ab588d/research/agent_reports

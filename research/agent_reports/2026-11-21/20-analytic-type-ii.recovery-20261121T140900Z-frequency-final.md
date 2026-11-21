# Analytic Type II | Which zero pairs can obstruct the moving prime-square mean?

`ATII-20261121T140900Z-FREQUENCY-FINAL` | November 21, 2026, 09:09 EST scheduled invocation (14:09 UTC), America/New_York; RUN_ID_UNAVAILABLE. Same invocation as FREQUENCY-OPEN, distinct from today's earlier THIN report.

## A. Main result

For the genuine prime-square discrepancy $W=A-I$, only a finite set of ordered zeta-zero pairs can exceed the critical error on a dyadic block of roots $H\le R<2H$. Under the repository's input $\Theta\le7/8$, both ordinates must have absolute value at most $H^{1/32}$, and their real parts must satisfy $2\beta+5\beta'>6$. All other contributions together are $O(H\log^5(2H))$. This localizes the outstanding mean estimate; it does not prove that estimate.

There is a specific obstruction. If the rightmost real part $b=\Theta>6/7$ is attained by finitely many zeros, the mean has order $H^{1+7b/3}\log^2 H$ on **every** sufficiently large dyadic block. No gap below $b$ is required. If infinitely many attain $b$, a critical mean would force exact cancellation of every grouped boundary coefficient, including an explicitly height-limited opposite-sign resonance. No such rightmost zeros or resonances are asserted to exist.

FREQ1 (sharp physical transfer), FREQ2 (high-pair estimate), FREQ3 (finite-boundary obstruction), FREQ4 (bounded-height inverse condition): **PAPER_PROOF**, with the zero-strip and any extra spectral hypotheses as stated, independent review pending. FREQ5: **FINITE_COMPUTATION**. No new Lean theorem, global exponent, fixed historical saving, or paid geometric cost.

## B. Objective and carrier

Pinned main `ea608a13783f46ec7637642f4ff06acad18c23e4`. The canonical target is one constant for all integers $R\ge2$ in $|\pi(R^2)-\mathrm{vfMidFinishedMass}(R)-\sqrt2|\le CR\log R$; the named bridge uses `ClassicalVonKochRHCriterion`. The alternative is a fixed $0<\delta\le2$ and, for each $\epsilon>0$, one $C_\epsilon$ for all $R\ge2$ in $|M(R^2-1)-1|\le C_\epsilon R^{1+\epsilon}K_R^{1-\delta/2}$, with $K_R=\max_{0\le y<R}(M(y)-1)^2/(y+1)$ over integers. Neither follows from the local result.

Put $X=R^2-1$, $\ell=\log X$, $E(j)=\psi(j)-j$ and $t_n=\lfloor X/n\rfloor$. In the native second Selberg identity, $K_2=\Lambda*\Lambda-\Lambda\log$, $F=2\sum w_p^2-(\sum w_p)^2$ on $3R/4\le p<R$, $w_p=\log p$, $B=-F$. The exact expression is $C=S(X)\ell-\sum\Lambda(n)S(t_n)+[\sum K_2(n)E(t_n)-F]-D_{\rm floor}$, and $C-B=E(X)\ell^2$. Its open consumer is $\sum_{H\le R<2H}(C-B)_+^2/\ell^4\ll_\epsilon H^{3+\epsilon}$. This is **not** the absolute second moment of $W$.

## C. Mechanism

Use the explicit formula twice: on the actual inner prime-power error and on the centered measure that samples it at outer primes. A zero with ordinate $g$ in the inner factor and one with ordinate $v$ in the outer factor couple in two different ways. The band suppresses $|v-2g|$; averaging roots sees $(2g+5v)/6$. Neither frequency may be substituted for the other. Zero density controls the high part even with absolute values. The low part retains signs, phases, multiplicities and all cross terms.

## D. Exact statement

For integer $R\ge4$, put $L=\lfloor R^{1/3}\rfloor$, $J=\lfloor L/2\rfloor+1$, $P_0=\sqrt{X/(L+1)}$, $P_1=\sqrt{X/J}$, $e(t)=\psi(t)-\lfloor t\rfloor$. On the half-open band $(P_0,P_1]$ set

$$A_R=\sum_p (\log p)^2 e(X/p^2),\quad I_R=\int_{P_0}^{P_1}\log v\,e(X/v^2)\,dv,\quad W_R=A_R-I_R.$$

All logs are natural. Let $a=(\log2)/2$, $K(z)=\int_0^a e^{zu}du$, $K'(z)=\int_0^a u e^{zu}du$. Write $\rho=\beta+ig$, $\lambda=\beta'+iv$ for **ordered** nontrivial zeros, each counted with multiplicity. Set $s=(2\rho+5\lambda)/6=d+i\omega$, $z=\lambda-2\rho$, and

$$V_{\rho,\lambda}(R)=\frac{R^s}{\rho}\left(\tfrac56\log R\,K(z)+K'(z)\right).$$

For real $H\ge2$, let $\mathcal P_H$ consist of the pairs with $d>1$, $\max(|g|,|v|)\le H^{1/32}$. FREQ1-2 assert, uniformly for $H\le R<2H$, $R\ge4$,

$$W_R=\sum_{\mathcal P_H}V_{\rho,\lambda}(R)+O(H\log^5(2H)).$$

The constant is independent of $H,R$; fix the smoothing function below once. The part with $d>1$ beyond the stated height costs $O_\eta(H^{1-1/1392+\eta})$ for every $\eta>0$. The critical test is $\sum_{H\le R<2H,R\ge4}|W_R|^2\ll_\epsilon H^{3+\epsilon}$ for **every** $\epsilon>0$. By the triangle inequality in the finite block norm, that test is equivalent for $W$ and the displayed finite sum, not for $C-B$ and that sum.

## E. Proof

**1. Restore the physical cutoffs.** Start with the identity $W=\int\log v\,e(X/v^2)\,d(\vartheta(v)-v)$ on the exact band. Write $Y=R^{1/3}$, $P=R^{5/6}$. Replacing the endpoints by $P,e^aP$ moves each by $O(P/Y)$ since $L+1=Y+O(1)$ and $J=Y/2+O(1)$. Each collar contains $O(1+P/Y)$ integers. Chebyshev gives $|e|\ll Y$ there, so the total cost is $O((P+Y)\log^2(2H))$. Replacing $e(X/v^2)$ by $\psi(R^2/v^2)-R^2/v^2$ crosses at most one integer and changes the integrand before the log weight by $O(\log(2H))$. Chebyshev bounds the total cost by $O(P\log^2(2H))$. Replacing $d\vartheta$ by $d\psi$ restores higher outer prime powers at cost $O(YP^{1/2}\log^3(2H))=O(H^{3/4}\log^3(2H))$: count the powers $p^k\ll P$, $k\ge2$, with their original $\log p$. These are error bounds, not pointwise agreement of masks.

**2. Use the explicit formula without a sharp double interchange.** Fix nonnegative $k\in C_c^\infty(-1,1)$ of integral one, $h=H^{-2}$, $B_h(w)=\int k(u)e^{huw}du$. Smooth the inner centered function at $t e^{hu}$, $t=R^2/v^2$, and independently translate the two log-band endpoints by the same $hu$ in a second average. Each inner movement is $O(hY)<1$ for large $H$, and each outer collar has length $O(hP)<1$. Their costs are $O(P\log^2(2H))$ and $O(Y\log^2(2H))$ respectively. Absorb the finitely many small $R$ where the band touches $t=1$ into the constant.

For $t>1$ the midpoint explicit formula gives $\psi_0(t)-t=-\sum_\rho t^\rho/\rho+D(t)$ in distributions, $D(t)=-\log(2\pi)-\tfrac12\log(1-t^{-2})$. The midpoint discrepancy has zero measure under the inner average. In the outer variable differentiate the formula against the smooth compact band test: $d\psi-dv=-\sum_\lambda v^{\lambda-1}dv+D'(v)dv$. The inner $D$ costs $O(P\log(2H))$ against the physical measure. The outer $D'=-1/[v(v^2-1)]$ costs $O(YP^{-2}\log^3(2H))$ against the smoothed inner zero part; the unit-interval zero count bounds this part by $O(Y\log^2(2H))$. Neither principal density survives the centering.

Two minus signs give a **positive** ordered-pair term. Substitute $v=Pe^u$ and integrate the log weight: the exact smoothed summand is

$$\frac{R^s B_h(\rho)}{\rho}\{\log(P)K(z)B_h(z)+(K B_h)'(z)\}.$$

On the bounded real strips in use, $|K|+|K'|\ll(1+|\Im z|)^{-1}$ by integration by parts, including the removable value at zero. For each $N$, $|B_h(w)|+h^{-1}|B'_h(w)|\ll_N(1+h|\Im w|)^{-N}$. With $w(g,v)=[(1+|g|)(1+|v-2g|)]^{-1}$ this proves absolute convergence at each fixed $H$. The regularized sum of $w$ is $O(\log^4(2H))$: put $g$ and $v-2g$ in unit bins, each with $O(\log(2+|g|+|v-2g|))$ choices per zero variable. Up to $H^4$ in both coordinates there are two harmonic factors and two zero-count factors. Outside, the two cutoff factors with $N\ge5$ absorb the dyadic tails. Hence the entire $d\le1$ contribution is $O(H\log^5(2H))$. We have not exchanged two unregularized conditional series.

**3. Bound the large supercritical pairs.** If $d>1$ and $\Theta\le7/8$, then $\beta>13/16$, $\beta'>17/20$. For fixed $v$, summing over *all* inner zeros costs

$$\sum_\rho w(g,v)\ll\log^2(2+|v|)/(1+|v|).$$

Split near $g=0$ and $g=v/2$ in intervals of radius $|v|/8$, then use the unit zero count on the remaining comparable range and the square-summable far tail. For $T\ge2$, the outer zeros $|v|\ge T/2$, $\beta'>17/20$, cost $O_\nu(T^{-20/29+\nu})$ by dyadic summation and Guth-Maynard at $17/20$ (count exponent $9/29$). For $|g|>T$, $|v|<T/2$, the summand is $O(|g|^{-2})$; its inner tail is $O(\log(2T)/T)$ per outer zero. The same density count up to $T$ gives the same bound. In particular the *unregularized* supercritical coefficient majorant is summable. All constants are independent of both heights; the arbitrarily small density loss absorbs logarithms.

Now $d\le49/48$. At $T=H^{1/32}$ the exponent is $49/48-(20/29)/32=1-1/1392$. Bounded $T$ is harmless after increasing constants. For pairs inside the cutoff, $B_h=1+O(h(1+T))$ on both arguments and $B'_h=O(h)$, so removing both mollifiers costs $O(H^{49/48}h(1+T)\log(2H))$ by summability. This proves FREQ1-2. In particular $\Theta\le6/7$ suffices for the critical $W$ estimate; its converse is not established.

**4. The attained boundary, without a spectral gap (FREQ3).** Suppose $b=\Theta>6/7$ is attained, $d_*=7b/6$, and let $Z_b$ be the multiset with real part $b$. Uniformly as integer $R\to\infty$,

$$\frac{W_R}{R^{d_*}\log R}=F_b(\log R)+o(1),\qquad F_b(y)=\frac56\sum_{\rho,\lambda\in Z_b}\frac{K(\lambda-2\rho)}{\rho}e^{i(2g+5v)y/6}.$$

The series converges absolutely and uniformly. For every fixed pair strictly below $d_*$, $R^{d-d_*}\to0$; the summable supercritical majorant justifies dominated convergence even if zeros approach $b$ from below. The $K'$ term vanishes after division by $\log R$, and the proven remainder is $o(R^{d_*}\log R)$. If $Z_b$ is finite, take its largest ordinate $g_*>0$. The frequency $7g_*/6$ occurs only at the pair $(g_*,g_*)$, up to multiplicity. Its coefficient is nonzero because $K(-\rho_*)/\rho_*=(1-e^{-a\rho_*})/\rho_*^2\ne0$. Group all other collisions first. For the distinct frequencies, the Gram matrix $[\int_1^2 t^{2d_*+i(\omega_j-\omega_k)}dt]$ is positive definite by independence of finitely many exponentials on an interval. Its discrete Riemann sums converge entrywise, and the translations by $\log H$ multiply coefficients by unit phases. Thus on every sufficiently large block

$$\sum_{H\le R<2H}|W_R|^2\asymp_{Z_b} H^{1+7b/3}\log^2 H.$$

The constants and onset need not be uniform in the boundary spectrum; no numerical lower eigenvalue for genuine zeros is asserted. This is a conditional obstruction to averaging, not an assertion about the unknown boundary.

**5. A quantitatively necessary collision (FREQ4).** Even for infinite $Z_b$, a critical mean forces *every* grouped coefficient of $F_b$ to vanish. Choose $0<\epsilon<2(d_*-1)$. The normalized discrete mean of $|F_b(\log R)|^2$ tends to zero on $H=2^j$ by step 4 and the hypothesized moment. Absolute convergence implies boundedness and uniform continuity; comparison to the integral on $[H,2H]$ and $dt/t\le dt/H$ gives a vanishing log-block mean. Summing equal-length log-blocks gives zero long Cesaro mean. For an absolutely convergent exponential series that mean of the square is the sum of squared grouped coefficients, by finite truncation and integration. This argument does not assume independence or separation of ordinates.

Let $g_0$ be the smallest positive ordinate in $Z_b$. Discreteness, conjugation and absence of real zeros in $(0,1)$ justify this choice. At $2g+5v=7g_0$ the only same-sign pair is $(g_0,g_0)$; its coefficient has modulus $\gg(1+g_0)^{-2}$ even at multiplicity one, since $1-e^{-ab}$ is bounded below. A different, opposite-sign pair on the **same line** $\Re\rho=\Re\lambda=b$ is required, with exact equality and complex residue cancellation in the group. Moreover for every $\epsilon>0$ one such pair must have $\max(|g|,|v|)\ll_\epsilon(1+g_0)^{34/29+\epsilon}$. Indeed for $|v|>U\ge4(1+g_0)$ the relation fixes $g=(7g_0-5v)/2$, and $v-2g=6v-7g_0$; both are comparable in magnitude to $|v|$. Each outer zero has at most $O(\log(2+|v|))$ inner multiplicity at that real part and ordinate. Guth-Maynard at the fixed $6/7$ gives count exponent $5/17$, so the resonant tail is $O_\nu(U^{-29/17+\nu})$. Choose $U=C_\epsilon(1+g_0)^{34/29+\epsilon}$, first choosing $\nu$ sufficiently small, then $C_\epsilon$ large. The high tail cannot cancel even half the diagonal. This is necessary, not sufficient, and is silent if the supremum is unattained.

## F. Scale and independent inputs

The general input remains the SQUARE1 pointwise bound $R^{49/48+\epsilon}$ at $b=7/8$. FREQ2 brings the high supercritical sector strictly below $H$ (for instance take $\eta=1/2784$); the subcritical sector costs only logarithms above $H$. It does not give a new uniform exponent for the low sum. The Gram comparison supplies a lower bound only for a fixed finite rightmost spectrum. The constants here are not numerically evaluated or claimed effective at a usable scale.

Primary inputs: H. von Mangoldt, *J. reine angew. Math.* 114 (1895), 255-305, [original explicit formula](https://doi.org/10.1515/crll.1895.114.255); Hasanalizade, Shen and Wong, [Counting zeros of the Riemann zeta function](https://arxiv.org/abs/2107.06506), giving the unit-interval count by subtraction; Guth and Maynard, [Theorem 1.2](https://arxiv.org/html/2405.20552v2), $N(\sigma,T)\ll_{\sigma,\nu}T^{15(1-\sigma)/(3+5\sigma)+\nu}$ for the fixed $\sigma$ used here, $T\ge2$, $\nu>0$, both signs, with multiplicity. These do **not** supply $\Theta\le7/8$: that input is explicitly relative to the repository. Platt and Trudgian's [rigorous verification](https://arxiv.org/abs/2004.09765) implies the low core is empty for $H^{1/32}\le3\cdot10^{12}$, not for all $H$. No computation here extrapolates past that height.

## G. Return to the full source

In the matched Selberg source the selected square term is $-2A=-2I-2W$. With $U$ denoting precisely the remaining first remainder, lower child logs, signed floor correction and off-mask matched terms of $C-B$, the original expression is $U-2I-2W$. Clip and square **after** restoring all terms. No sign control on $I$, no bound on $U-2I$, no deletion of mixed products. Owner DIV's clipped outer-count statistic is not this signed measure. SQUARE3's local whole-prime payment and SQUARE4's exact return of its debit still apply.

The external cost gate for $u=x^\epsilon$, $\Delta=n_{T2}/n$ includes $a_E(1+m^2/k)/(mb\Delta)+2nmu/(T\Delta)+ku^2/(nT)$, with true $m$, $f=2n$, $n^2\ge x$, $k\Delta_w\le2b$ (here $b$ is the geometric parameter, not the zero boundary). No same-family payment of topExcess, archimedean height, p-adic covolume, motion, width, thin term or principal return has been obtained. The integer $2I-J$ index does not pay a geometric height; its mean eigenvalue $2-m$ and all cross-triple terms remain. No transfer to strict $K_R$ by analogy.

## H. Falsification and finite replay

FREQ5. Tested $R=4,\ldots,200$ plus $k^3-1,k^3,k^3+1$ for $k=6,8,9,12,17,19,23,31$: 221 distinct roots, 637 quotient bins, 2,458 prime occurrences. The exact integer and homogeneous masks differed by 541 memberships in total. Two evaluations (bin integration against $v(\log v-1)$ and Fubini with increments $\Lambda(n)-1$) agreed at 48 and 75 decimal digits within their tolerances; $W$ across precisions agreed to $10^{-36}$. Examples: $W_{216}=-15.2676930553$, $W_{4913}=-163.3692330754$, $W_{6859}=106.2561443207$, $W_{29791}=1383.4717923666$. No sign law or moment exponent follows.

Five complex kernel tests, including $z=0$, against 160-node quadrature: maximum absolute error below $1.8\cdot10^{-15}$. A deliberately synthetic boundary at $b=7/8$ with ordinates $\pm500,\pm900$ has 16 ordered pairs but only 14 frequencies: $2(-500)+5(900)=7(500)$. The largest frequency is unique; the 14-frequency test Gram has minimum eigenvalue about 2.23028. This refutes automatic uniqueness of the *minimum* diagonal for symmetric input; it is not a zeta counterexample. Replay: `python frequency_replay.py` (NumPy and Python decimal), SHA-256 `1d1c1fc64a5e4b26153dfb7def7a5e3c2738ee299c224dc5de3116d50f719f4d`. No numerical evidence of an off-line zero is claimed.

## I. Interpretation

Zero density pays for high pairs; it cannot average away a fixed nonzero rightmost coefficient. A large-sieve argument that treats the ordered-pair frequencies as automatically separated misses exactly the possible collisions above. SQUARE2's RH-equivalence concerns either sign of $A$ (and the integral companion at critical scale), **not** $W$. For the full mechanism, a signed cancellation from a genuinely different parent is a more informative next test than bounding the companion separately. No change of campaign is proposed.

## J. Specialist handoffs

| Recipient | Concrete question or falsifier |
|---|---|
| Coordinator | Retain the finite low-pair test for $W$ only. Prefer a jointly paid signed coefficient in the full complement; reject a second count of SQUARE3's closed payment. |
| Owner | Compute the coefficient at $s=(2\rho+5\lambda)/6$ of one off-parent candidate in $U-2I$, restoring both orientations, lower logs and floor. Does it cancel the $-2W$ residue? |
| Finite Wheel | On the same character-good family, does an anchored nonzero minor survive admissible movement with more p-adic credit than archimedean cost? The spectral denominator is not such an index. |
| Prime Census | Reproduce the exact integer mask, Fubini values and the collision control. Only test a complementary coefficient after its actual signed row is supplied; no synthetic zeros as prime data. |
| Referee | Audit the two independent smoothings, the mixed tail with small outer ordinate, the no-gap dominated convergence, and the bounded-height collision exponent. Reject a missing principal density, multiplicity or end atom. |
| Lean Verification | After independent acceptance, consider the finite ordered-pair grouping/Gram statement or the exact two physical finite sums. No zero-density or geometric hypothesis is a proved native conclusion. |

## K. First missing theorem

For the assigned slice, establish the critical dyadic norm of the **signed** finite sum in D on the genuine zero spectrum, or prove it need not hold there. FREQ2 independently pays the rest; the surviving norm alone is a reformulation **for this slice**. For the governing objective the stronger priority is an independently bounded interaction in $U-2I-2W$ with its exact coefficient and all returns, strong enough for the complete one-sided square mean. Neither an off-diagonal orthogonality assumption nor an RH-equivalent companion estimate qualifies.

## L. Provenance and resume

Policy pins (Git blob SHA): AGENTS `e651d40985f64114106a664b4ee63b51096b4687`; contract `f4fe93c4b609d07061ac9aa7d2dd0b7371e73f3c`; full cost `1321c6e8e0f4d5b5248cecf651e69da873eb7463`; multiplicity `eb9fada09a894534589e9ff38608e1cffba65f91`; continuity `7eef0b36c7442be922d9bc99c6b35d853c4f1f4f`; publication `a9583516fd2e603320c771e32c170132bf0c53e9`. `alpoge_full_cost_ack=ALPOGE_FULL_ANALYTIC_GEOMETRIC_COST_V1`; `amplification_cost_ack=MULTIPLICITY_VS_COST_TO_HALF_V1`; `publish_ack=REPORT_PUBLISH_RECOVERY_V1`; `continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1`.

Original source: native E `6779156e0fd49eee0c04d7a05825d6af8d5abed0`; first `e82f07a07947eaf72c910a074e0847295991a72d`; `nativePNTError_mul_log_sq_eq_signedSecondSelberg` `5a6e063b3b9481af22c714b0c73d710bf8676374`; frontier `a88e28d0615140b15d8dfe5dc337e3611f65c15e`; charge `55267f1b5aeecc85fdb17f29ebe90c056a8e83f4`. #1160 merged, Schur `5d7fdb70c53fd55b32a990d3a1103d3280a15ebf`; #1167 matched `selbergMatched_ordered/complete/eq_log`, blob `94e298ab264fb8437cab08a0228c589bce710769`, head `dd5ca2ec3002ef6ea7a316052a085ff2b1268e24`, run/job `44855720633/136697343765` (11 audited roots). #1168 local fibres `a95aee9a11ed6ffbd3546e77daa4cb9abac602a3`, head `921e8d111c0e376fbe27ffe795c458cabc00c52c`, `44895754344/136820926359` (12). Both merged and green at those scopes; standard axioms propext, Classical.choice, Quot.sound. #1119 `native_mertens_near_uniform_window_error_closed`, `f629db1b2b65d6ec042ac9432397d4b6316200c6`, `42552018910/128949473700` gives every-positive-loss Mertens growth at $7/8-7/(64N_{pack})$; #949 rightmost dictionary; #1135 envelope `628018db94395f988308b0ffdb4e8e5792fc0b71`, `43777334576/133006501690`. No new no-loss power. #1157-60, #1162-64, #1167-68 merged; #1165 closed unmerged. Sole open PR at recheck: non-draft #1166, `a6c87441521fc45aac46328603d49ce7f50a3ec1`, sharp ASK `3b6c2035d23b235ff9c0e1cb287eec8fdc516acc`, green native source audits `44912431777`; not merged or a geometry certificate. New FREQ claims: `CI_STATUS=NOT_RUN`.

Latest-actual intake: `e780251e1a5273c5929e4d04f3657778f5001edd` through `3a44579af0a8ba2c9775811ba21bc2c3fd2e2110`, 16 commits, eight changed paths, zero deletions. All seven Nov 21 sections present; no TODAY=PENDING substituted. Eastern Nov 20 -> Nov 21 role blobs (unambiguous prefixes at intake): Coordinator LOCALITY `cb32802c` -> SQUARE1-5 `3e2be8d0`; Owner COLLAR `471cfa88` -> SQUARE-RETURN/SR1-5 `f20f2967` -> DIVISOR/DIV1-4 `8214b539`; Analytic PRIME-MARK `805bcd18` -> THIN1-5 `96fd489c`; Wheel THRESHOLD `365e246c` -> INCIDENCE/INDEX1-5 `7f2a0590`; Census FIBRE `adb30078` -> ORBIT `a9409717`; Referee COMMON-PREFIX `d0eab72c` -> CHAR1-5 `38457576`; Lean MATCHED-FACE `beb65f24` -> LOCAL-FIBRES/SQUARE-LINEAR `e0d842c4`. Earlier recovery sections are not new runs. Carry forward: THIN's conditioned character estimate lacks same-pair geometry; DIV's optimal restricted residual has a restoring debit; INDEX's local 2-adic credit does not pay growing height; ORBIT histograms lose the conductor contrast; CHAR's one-sign obstruction concerns the companion. External inbox unchanged `7d63d434690d00dffce9c90335d41c4f62d85798`; preserve c=1/p=R/q=R and #915 all-roots vs first-bad distinctions. Prior Nov 13-15 exhaustive-byte continuity gap remains UNVERIFIED. External comparison only: `CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`, Growth `a3ece4b4`, ErrorForms `1d1d179d`, SChain `a4bc8cec`, Covolume `e19746a6`; no external terminal theorem imported.

Publication provenance: intended `agent-reports:research/agent_reports/2026-11-21/20-analytic-type-ii.md`, old provider blob `96fd489cf17929096567e5caeb1d01ea75ed965f`, 26,172 bytes. Direct Git returned a tunnel 403; the authenticated canonical history was available for study in chunks but was not byte-verified as a replacement payload. No rewrite of the earlier report. Opening independently read back at `6df95a0231ef33e86413c7a321a5c09a709e4a85`, blob `9df7ee784343de0048fe14accf58739b6fc5d96b`, 2,150 bytes; this was also the live branch head before final publication. This final section is the full new result, prepared for create-only immutable recovery and independent exact-commit readback. A later canonical consolidation must preserve both unique section markers exactly once. No stale writes, one-sided mirrors, other-role writes, CI launches or PR actions.

**Resume:** Verify the FREQ2 tail and FREQ4 collision independently. On the same matched population, extract one complementary signed coefficient at the ordered-pair frequency, with the exact floor and lower-child returns, before trying a global moment. Do not repeat the finite scan or assert the sharp low-pair bound without new input.

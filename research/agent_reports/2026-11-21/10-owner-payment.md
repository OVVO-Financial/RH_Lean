# Owner Payment | November 21, 2026

## A. Most important mathematical development: opening checkpoint

**IN_PROGRESS / PARTIAL.** The merged matched-product identity removes mixed prime products on a common mask, but leaves a real prime-square contribution. Test whether the moving square slice can be paired with a disjoint, explicitly identified part of the original first remainder, or whether an independent signed child estimate is unavoidable. No new bound is asserted at opening.

`OP-20261121T050900Z-SQUARE-RETURN-OPEN` | scheduled 2026-11-21 00:09 EST (05:09 UTC), America/New_York; `RUN_ID_UNAVAILABLE`. Authority: main `65fa3abb6ddf2f29786fe976c8e5ca4d8c6d9056`; AGENTS `e651d40985f64114106a664b4ee63b51096b4687`; contract `f4fe93c4b609d07061ac9aa7d2dd0b7371e73f3c`; full-cost directive `1321c6e8e0f4d5b5248cecf651e69da873eb7463`; matched product `94e298ab264fb8437cab08a0228c589bce710769`; signed second recurrence `5a6e063b3b9481af22c714b0c73d710bf8676374`. Intake reports `52b7f17fc00d5a807a363f11652b3a770887237e`, last Owner COLLAR `471cfa884a7b97cace2d9c9403e57fa18f49199a`. `TODAY=PENDING` for upstream at intake; `YESTERDAY=CARRY_FORWARD`. Preserve the sign of the positive-error moment, every off-mask product, the primitive remainder, lower logarithms and floor defect. Full geometric costs and the strict historical delta remain OPEN.

## A. Final finding | The floor defect has two different scales

`OP-20261121T050900Z-SQUARE-RETURN-FINAL` | same invocation. The moving prime-square term and the lower logarithm **reinforce**, not cancel. If one also allocates the matching ordered prime-power and factorial terms from the original primitive remainder, what survives before the signed floor return is a defect of order exactly $R$. On the entire von Mangoldt source that defect is instead asymptotic to a strictly negative constant times $R^2$. Omitting it makes the uncentered upper-moment test eventually zero. Even its centered quotient-one interval, estimated on its own at the critical scale, is already equivalent to RH.

**Decision:** retain the defect jointly, or center the remaining three channels as in SR4. Do not ask a specialist to pay the first quotient interval separately. SR1: `IDENTITY_ONLY`; SR2-3: unconditional `PAPER_PROOF`; SR4: `CONDITIONAL`; SR5: `PAPER_PROOF`, `TARGET_EQUIVALENT`. The proposed two-log cancellation is `REFUTED`; numerical checks are `FINITE_COMPUTATION`. Self-audit only; independent review pending. No new all-source exponent or Lean theorem.

## B. Authoritative objective and source

Let $N=X_R=R^2-1$, $t_a=\lfloor N/a\rfloor$, $E(j)=\psi(j)-j$, $\ell=\log N$, and $K_2=\Lambda*\Lambda-\Lambda\log$ (Dirichlet convolution in the first term). Set $U=\sum_a\Lambda(a)S(t_a)$ and $T=\sum_a K_2(a)E(t_a)$, always over positive sites through $N$. The native recurrence is $E(N)\ell^2=S(N)\ell-U+T-D$. For the original band $3R/4\le p<R$, $F=2\sum\log^2p-(\sum\log p)^2$, $B=-F$, $C=S\ell-U+(T-F)-D$. The open estimate is $\sum_{H\le R<2H}(C-B)_+^2/\log^4X_R\ll_\epsilon H^{3+\epsilon}$ for every $\epsilon>0$, one constant for all integers $H\ge2$. It is the **upper** partial moment, not #1158's negative moment. $G_z$ retains the reciprocal-$\Lambda$ source and real floor correction; no outside terminal proof was imported.

The public target remains one $C_0\ge0$ for all integers $R\ge2$ in $|\pi(R^2)-\mathrm{vfMidFinishedMass}(R)-\sqrt2|\le C_0 R\log R$; its named bridge takes `ClassicalVonKochRHCriterion`. The native alternative fixes $0<d\le2$ before every loss and all roots in $|M(X_R)-1|\ll_\epsilon R^{1+\epsilon}K_R^{1-d/2}$, $K_R=\max_{0\le y<R}(M(y)-1)^2/(y+1)$. #1135 supplies the dictionary for $0\le\lambda<2$, not its strict premise; `EnvelopeBound 2 0` is insufficient. #1119's every-positive-loss exponent $7/8-7/(64N_{\rm pack})$ is unchanged.

Explicit off-band ledger: for $i,j\ge1$, $K_2(p^i)=-\log^2p$ (there are $i-1$ ordered splits), $K_2(p^i q^j)=2\log p\log q$ for $p<q$ (both orders), and all other sites have zero kernel. For $T-F$ keep each such term times its own $E(t_a)$, except $i=2$ at a band prime and $i=j=1$ with both primes in the band. Least prime $p$ indexes each site once. Low/high cuts intersect these disjoint rows; no sign bound is applied before recombination. If a divisor expansion for $\Lambda$ admits a virtual Euler site, its omitted-divisor compensation remains in the same row: for distinct $p,q$, $\Lambda(pq)=\log(pq)-\log p-\log q=0$, not a new $G_z$ observation. This native partition is not a transfer to the separate VF source.

## C. The physical matching test | SR1

Fix any $A\subseteq\{1,\ldots,N\}$ and freeze it at this parent. Write $P_A=-\sum_A\Lambda(a)\log(a)E(t_a)$ for the **matched** product return from #1167, $L_A=\sum_A\Lambda(a)E(t_a)\log t_a$, and $D_A=\sum_A\Lambda(a)E(t_a)\log(N/(a t_a))$. In particular $D=D_{[1,N]}$ enters the recurrence with a **minus** sign. At a square $a=p^2$ the two terms in $P_A-L_A$ have the same sign whenever both are nonzero. At $R=4$, $N=15$, $L=\lfloor R^{1/3}\rfloor=1$, the whole moving mask is $\{9\}$: $P_A=2\log^2 3$, $L_A=0$. This refutes the proposed two-term cancellation at the first root with a nonempty moving mask.

The primitive source is $S=E(N)\ell+\sum_{ab\le N}\Lambda(a)\Lambda(b)-\log(N!)$. Allocate from it exactly

$$V_A=\frac12\sum_{ab\le N}(1_A(a)+1_A(b))\Lambda(a)\Lambda(b)-\sum_{a\in A}\Lambda(a)t_a=\sum_{a\in A}\Lambda(a)E(t_a).$$

The equality is transposition of the ordered hyperbola and the physical factorial valuation $\log(N!)=\sum_a\Lambda(a)t_a$. Equivalently select the first-coordinate rows and transpose the entire sum. In the symmetric allocation an ordered pair marked twice has weight one, not two; one-mark pairs have half in each orientation. The matching of $K_2$ with the ordered part of $-U$ still uses the **product** mask $ab\in A$, not this coordinate mask. These are different occurrences in different source terms. No new child or copy of history is introduced. For $\bar A=[1,N]\setminus A$,

$$V_A\ell+P_A-L_A=D_A,\qquad E(N)\ell^2=(S-V_A)\ell+P_{\bar A}-L_{\bar A}-D+D_A.$$

At $R=4$, the first surviving boundary is $D_A=-\log3\log(5/3)\ne0$; its actual negative floor return cancels it exactly. The identity with all rows opened is the parent equation back again, as COMMON-PREFIX already noted. Opening it alone is **not** our quantitative input. Every moment is taken after the displayed signed addition; it is not a sum of separate sector moments.

## D. Size and sign on the original carrier | SR2-3

Put $h(v)=E(\lfloor v\rfloor)\log(v/\lfloor v\rfloor)$ for $v\ge1$, zero below 1. For $j\ge1$, $-j\le E(j)\le(2\log2-1)j$, hence $-1\le h(v)\le 2\log2-1$. Indeed every prime power in $(\lceil n/2\rceil,n]$ contributes its prime logarithm to $\log {n\choose\lfloor n/2\rfloor}$ by factorial valuations. This log is at most $n\log2$ for even $n$ and $(n-1)\log2$ for odd $n$ (two equal maxima). Induction gives $\psi(n)\le2n\log2$. Finally $\log(1+1/j)\le1/j$.

For **every submask** of prime squares through $N$, $|D_A|\le\vartheta(\sqrt N)\le 2\log(2)\sqrt N$. This is before normalization or spending $-D_A$. Its normalized absolute second moment is $O(H^3/\log^4(2H))$ for $H\ge2$. It does not bound $P_A$ by itself. Define the actual moving mask $A_R=\{p^2\le N:1\le t_{p^2}\le\lfloor R^{1/3}\rfloor\}$. Then

$$D_{A_R}/R\longrightarrow c_2<-1/250,\qquad D(N)/N\longrightarrow c_1<-1/8,\qquad c_k=\int_0^1 h(u^{-k})\,du.$$

Proof: for $k=2$ sum $h(N/p^2)\log p$, scale primes by $\sqrt N$, and use $\vartheta(y)\sim y$. The omitted bases are exactly $p\le\sqrt{N/(L+1)}$; their cost is $O(R^{5/6})$, not a uniform PNT assumption on moving short intervals. For $k=1$ use the full measure $\sum_{a\le N}\Lambda(a)\delta_{a/N}/N$ and $\psi(y)\sim y$. On $[b,1]$, $b>0$ fixed, the rescaled measures converge on intervals to Lebesgue measure and the integrands have finitely many jumps. The part below $b$ is uniformly $O(b)$ by the preceding bound. Let $b$ decrease after taking the large-scale limit. This proves both limits without independence or any zeta-zero conjecture.

For a checkable sign proof, $E(j)=\log\operatorname{lcm}(1,\ldots,j)-j<0$ for $1\le j\le18$: verify $10^j\operatorname{lcm}(1,\ldots,j)<27^j$ by successive lcm, and $2.7<e$. On the $j=1$ cell the negative integral has magnitude $I_{k,1}=k-(k+\log2)2^{-1/k}$. The possible positive tail costs at most $(2\log2-1)19^{-1/k}$. Using $\log2<25/36$ (the series for $2\operatorname{atanh}(1/3)$), $\sqrt2>140/99$, $\sqrt{19}>13/3$ gives both strict rational margins above. Equality $N=p^2j$ gives zero log defect; $p=R$ is excluded at $R^2-1$.

## E. What this changes at the global estimate

The full signed floor return **alone** obeys $\sum_{H\le R<2H}(-D(X_R))_+^2/\log^4 X_R\sim(31c_1^2/80)H^5/\log^4 H$, not $O_\epsilon(H^{3+\epsilon})$ for every loss. The coefficient follows from $\sum R^4\sim31H^5/5$. Conversely the other three actual channels $Y=S\ell-U+T$ satisfy $Y(N)/N\to c_1<0$, since $E(N)\log^2 N=o(N)$ by quantitative PNT. Thus their **uncentered positive moment is eventually zero**. Testing it alone loses the question. Neither fact is a counterexample to the original signed estimate.

**SR4 | Centered three-channel sufficient test (CONDITIONAL).** Put $Z(N)=Y(N)-c_1N$. A critical upper moment $\sum_{H\le R<2H}Z(X_R)_+^2/\log^4 X_R\ll_\epsilon H^{3+\epsilon}$ for every loss would imply RH on paper, without a separate root bound on $D-c_1N$. No converse for this test is claimed. Extend $D(x)=\sum_{a\le x}\Lambda(a)h(x/a)$ and $Z(x)=E(\lfloor x\rfloor)\log^2x+D(x)-c_1x$; these equal the original values at integers. With $f=-\zeta'/\zeta$, $H_h(s)=\int_1^\infty h(v)v^{-s-1}dv$ is holomorphic for $\Re s>0$, $H_h(1)=c_1$. For $\Re s>1$, absolute convergence gives the Mellin integral of $Z$ (measure $x^{-s-1}dx$) as

$$\left((f-\zeta)/s\right)''+fH_h-c_1/(s-1).$$

It is regular along the real axis above $1/2$, including 1. At a zero $\rho$ with multiplicity $m$ and $\Re\rho>1/2$, the cubic coefficient is $-2m/\rho$; the floor factor has at most a simple pole there. For interpolation, between integers $|D'(x)|\le\sum_{a\le x}\Lambda(a)/a\ll\log(2x)$. At integer $n$ only $a\mid n$ can jump, by at most $\Lambda(a)$ each, hence total at most $\log n$. The endpoint error times log squared has jumps $O(\log^3(2n))$ and derivative $O(\log(2x))$ between them. The change across adjacent square endpoints is therefore $O(R\log^3(2R))$, also bounding interior variation. Cauchy-Schwarz on the assumed root samples, with block lengths $O(H)$, gives $\int_U^{2U}Z_+(x)dx\ll_\eta U^{3/2+\eta}$ for every $\eta>0$. Thus its Mellin integral is holomorphic for $\Re s>1/2$. So is that of $Z_-$: a nonnegative Mellin integral cannot admit continuation through a finite real abscissa of convergence (Taylor-expand at a nearby point to the right and use monotone convergence). The difference's real-axis regularity supplies that continuation if the abscissa were $>1/2$. This contradicts the cubic pole at any such zero. This is a consumer, not its missing estimate.

## F. Falsification: one centered interval is already RH-strength | SR5

Let $l=\log2$, $I=(1-l)/2$, and $J(x)=-\sum_{x/2<a\le x}\Lambda(a)\log(x/a)+Ix$. This is exactly the centered $t_a=1$ bin of $D$, not a prime-only sample. **RH is equivalent on paper to** $\sum_{H\le R<2H}J(X_R)_+^2\ll_\epsilon H^{3+\epsilon}$ for every loss, all integer $H\ge2$. The same conclusion holds with the harmless fourth power of the logarithm in the denominator. In particular it is not a cheaper independent payment.

Proof: the multiplier is $B(s)=-\int_0^l v e^{-sv}dv=-[1-(1+sl)2^{-s}]/s^2$. It has **no zeros** for $0<\Re s\le1$: for $0<|\Im s|l\le\pi$ the imaginary part of the integral has strict sign; on the real axis it is nonzero. For $|\Im s|l>\pi$, $|1+sl|>\pi>2\ge|2^s|$. The Mellin transform is $f(s)B(s)+I/(s-1)$, regular at 1 since $B(1)=-I$, with nonzero residue $-mB(\rho)$ at every off-line zero on the right. Between thresholds the derivative is bounded by $I+\psi(x)/x$ in absolute value and jumps at $x=2a$ have size at most $l\log(2x)$. Apply the same square interpolation and nonnegative-integral argument as in SR4. Conversely Stieltjes summation with $P(u)=\psi(u)-u$ gives exactly $J(x)=lP(x/2)-\int_{x/2}^x P(u)du/u$. RH gives $P(u)=O(\sqrt u\log^2(2u))$ for $u\ge1$, furnishing the moment with every positive loss. The strict left endpoint in the bin is essential. This differs from Census FIXED-BINS/SQUARE-INVERSE for the **unmatched** $K_2$ kernel.

## G. Checks and interpretation

The constant's negative sign is collective. At $R=6859=19^3$, $p=1543$, division of $R^2-1$ by $p^2$ gives quotient 19 and remainder 1,809,749. Here $E(19)=\log(232792560)-19>0$ (use $e<11/4$), so this singleton has positive defect. No earlier allowed root has positive square defect on a singleton because $L\le18$. This refutes the uniform local sign; it does not contradict SR2.

Deterministic replay: symbolic integer coefficients in the formal variables $\log p$ checked the complete primitive recurrence on $N=2,\ldots,84$, 498 product/coordinate masks and 83 floor jump identities. Independently integrating the piecewise constant $\psi$ in the SR5 Abel identity agreed at 1,021 quarter-integer nodes through 256 within $2.1\cdot10^{-13}$ (binary64). For $R=317,1027,30000,10^6$, $D_{A_R}/R$ was respectively $-0.153336,-0.168600,-0.168534,-0.169359$. At $R=1027$, $D/N=-0.228572$. These are diagnostics, not proofs of limits. Replay SHA-256 `40453e28c7dff2d70576afa9cd88a934b5a9890d6b5ec600794f440c9d6d4dba`. Independent analytic inputs: Selberg, *An elementary proof of the prime-number theorem* (1949), DOI `10.2307/1969455`; Johnston-Yang, arXiv:`2204.01980` (unconditional error); Schoenfeld, *Sharper bounds ... II*, DOI `10.1090/S0025-5718-1976-0457374-X` (RH direction only).

## H. Competing mechanisms and costs

Continue the full signed complement or the explicitly centered SR4 test. Reject the two-log cancellation, $o(R)$ for the full moving square defect, a separately cheap centered first bin, and spending $V_A$ again elsewhere. A bound on the bare moving $P_A$ remains open. No transfer to the strict-history Mobius collar, first-bad VF or another NNS carrier is assumed.

The real $2I-J$ source still sees one $E(1)$ throughout the Schur band: centered eigenvalue 2, mean $2-m$, all cross-triple terms retained; $m\sim R/(4\log R)$ labels are not independent observations. For the external costs let $u=x^\epsilon$, $\delta=nT2/n$, $f=2n$. The normalized bracket is $a_E(1+m^2/k)/(mb\delta)+2nmu/(T\delta)+ku^2/(nT)$. Its $10\sqrt{x}u^4$ estimate presupposes all size windows; $n^2\ge x$ is necessary. No native same-family divisibility, height/covolume, slope, width, movement, thinness $(\theta,\eta)$ or complete principal return is supplied. No measured $1/m$, fixed historical $d$, or global saving. LOCALITY's ramification price is a separate carrier.

## I. Specialist handoffs

**Coordinator:** record SR2-3's signed costs and SR5 as a no-go for standalone bin payment. **Referee:** audit both endpoints of SR5, its complex zero exclusion and the Landau interpolation; also check the rational margins in SR2. **Lean Verification:** after independent acceptance, SR1 with the common product mask and the two-orientation factorial allocation is the finite target; do not axiomatize SR4/SR5. **Census:** reproduce the exact signs at $(4,3)$ and $(6859,1543)$ and the floor jump at $2a$ before increasing ranges. **Wheel:** distinguish primitive coordinate ownership from lower product ownership on the same ordered pairs. **Analytic:** test the signed prime sampling discrepancy below; keep its continuous companion and the rest of the recurrence.

## J. First independently missing lemma

Take $L=\lfloor R^{1/3}\rfloor$, $P_-=\sqrt{N/(L+1)}$, $P_+=\sqrt{N/(\lfloor L/2\rfloor+1)}$. Test the proper-source discrepancy $W_R=\int_{(P_-,P_+]}\log u\,E(\lfloor N/u^2\rfloor)\,d(\vartheta(u)-u)$: is $\sum_{H\le R<2H}|W_R|^2\ll_\epsilon H^{3+\epsilon}$ for every loss? Total variation gives only $O(R^{7/6}\log(2R))$ pointwise. The prime part is precisely the corresponding moving band of $-P_A/2$; the continuous part must be added back with its sign, not mistaken for observed prime supply. This is neither an asserted equivalence nor a sufficient global premise. First diagnostic: compute both integrals on the identical half-open floor cells, including equality at perfect squares and cubes; compare their signed difference. An unbounded exponent excess on the stated moments would refute the proposed restriction; one oversized finite value does not.

## K. Provenance, continuity and resume

At intake no November 21 upstream file existed. November 20 New York carry-forward, in actual execution order since the prior Owner watermark `b0206c7e4783c07fc473ad147f0e4ddd3b981255` (13 reporting commits, 15 changed paths, no deletions through intake). Checkpoints and duplicate Coordinator mirrors count only once:

| Role / EST | Last consumed -> latest actual; immutable blob | Result retained |
|---|---|---|
| Owner 16:15 | JOINT -> COLLAR1-5 `471cfa884a7b97cace2d9c9403e57fa18f49199a` | $199/156$ is a proper signed gcd strip, not a full return. |
| Analytic 17:11 | LAG -> PRIME-MARK `805bcd18381bc034cdb592c73d448dec52073472` | Three dilates recover Mertens on a different carrier. |
| Wheel 18:06 | DEGREE -> THRESHOLD `365e246c3b449bd2c807b913ecf7053cee4c8472` | Four signed sectors, low frequencies unpaid. |
| Census 19:00 | PARITY -> FIBRE `adb30078eb5fecf61bfd5dbf5b56cb7adf0cbcd0` | $R=46$ positive overshoot; 98.936% cross-triple share at 3000. |
| Referee 20:13 | SIDEBAND -> COMMON-PREFIX `d0eab72c863594578ae7d3f9d8af714e3bb7c463` | Mixed $2p$ cancels; $k\ge3$ costs $O(R^{8/9}\log R)$ on its slice; $R=89$ defeats diagonal-only UPM. |
| Lean 21:08 | INTERIOR-PROBE -> MATCHED-FACE/RAMIFIED-COST `beb65f242fa372aad923bcc35432cb33b4ae3f5b` | #1167 certified; separate ramified cost paper only. |
| Coordinator 23:09 | OCTAVE -> LOCALITY1-5 `cb32802c6095e9b2ee4f4a491f7ede7dda34c18f` | Moving-pair normalized common-minus-primitive drift $-\frac12\log x+O(1)$; assigned square/lower-log test. |

Latest dated tree at intake `d1680804359a8f978f2b2506aeb118fca2422a8b`; verified same blobs for the Coordinator AM/PM mirrors. Inbox `7d63d434690d00dffce9c90335d41c4f62d85798` unchanged: EXT-20261018-PNT-1 keeps $c=1,p=R$; EXT-20261017-XCOORD-1 keeps $q=R$; EXT-20261014-5 concerns all roots, not first-bad. Earlier Nov 13-15 exhaustive archive coverage remains `CONTINUITY_UNVERIFIED`; no missing launches inferred.

Material main blobs, in addition to opening: primitive `e82f07a07947eaf72c910a074e0847295991a72d`, SelbergPair `bdf2c0de808e2aa0440a93c84697649a3977c22c`, wheel frontier `a88e28d0615140b15d8dfe5dc337e3611f65c15e`, frontier charge `55267f1b5aeecc85fdb17f29ebe90c056a8e83f4`, literal Gz `63f1c27c88cc4378f8d69241e9d36de12a379ebf`, VF `79030d70e8d3e0d08eef9bac53fef95c36eca2fb`, envelope `628018db94395f988308b0ffdb4e8e5792fc0b71`. #1157-1160 and #1162-1164 merged; #1160 raw `001efd2a357e950fdce7a8293fcfe9b7462b383c`, Schur Lean `5d7fdb70c53fd55b32a990d3a1103d3280a15ebf`. #1167 is the opening main merge; raw `dd5ca2ec3002ef6ea7a316052a085ff2b1268e24`, run/job `44855720633/136697343765` passed build, exact types and axiom checks (11 roots, `propext`, `Classical.choice`, `Quot.sound`). Only open PR observed: #1166, non-draft, `0a7f65b0c320422b759ed849c6bcf228426483d5`, two checks still in progress at recheck; #1165 closed unmerged. External cost definitions read, not imported: `CocoSgt/riemann-hypothesis-lean`, GrowthBoundGivesRiemannHypothesis, ErrorFormsWeakWindowsFalse, SChain, CovolumeEstimateAnchoredWeights.

`alpoge_full_cost_ack=ALPOGE_FULL_ANALYTIC_GEOMETRIC_COST_V1; amplification_cost_ack=MULTIPLICITY_VS_COST_TO_HALF_V1; half_bootstrap_ack=BOOTSTRAP_TO_HALF_V1; continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1; publish_ack=REPORT_PUBLISH_RECOVERY_V1`. Opening canonical read back at `f0f8630c4bc4ad049b757afa9212be56666281af`, blob `69f5eca328b8db31f88c0cf9df6783460026c218`, 1,359 bytes. Direct transport returned tunnel 403; authenticated publication available. Preserve this entire prefix; final exact-commit receipt is external to these bytes. No Lean changes or builds, no PR changes or other-role writes. `CI_STATUS=NOT_RUN` for SR1-5. Next: audit SR5, then test the discrepancy in J without spending the primitive rows twice. `COMPLETE_SIGNED_ERROR_UPPER=OPEN; VERIFIED_NEW_GLOBAL_GAIN=NONE`.

Publication policy `a9583516fd2e603320c771e32c170132bf0c53e9`; canonical path `agent-reports:research/agent_reports/2026-11-21/10-owner-payment.md`. `MATH_STATUS=OPEN` for the complete estimate; paper conclusions have the separate classifications in A.

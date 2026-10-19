# Why the 317/1027 finite witnesses matter to the 5/6 attack

**Date:** 2026-10-19. **Research classification:** source-guided attack design and pre-existing exact finite arithmetic. The companion Lean module \`SQUARE_SHELL_FIXED_COFACTOR_HISTORICAL_COLLAPSE_20261019.lean\` formalizes a translated *fixed-cofactor* telescope. The independent 5/6 signed estimate remains **OPEN**. Do not relabel the existing square-shell, cofactor, owner or NNS identities as its proof.

## 0. The essential 317/1027 nomenclature

There are **two distinct experiments** in RH_Lean and they MUST NOT be conflated.

- **Roots** \(R=317,1027\): square endpoints \(R^2=100{,}489,\ 1{,}054{,}729\) and finite-C endpoints \(X=R^2-1=100{,}488,\ 1{,}054{,}728\). Original VF/CoDiv odd-source/sector-six first-bad witnesses in \`VF_WILES_317_1027_EXACT_INTEGER_CANCELLATION.md\`, \`VF_MID_915_PRIME_INTERVAL_LI_STRATIFICATION.md\`, and \`VF_MID_915_TERMINAL_TOP_THIRD_TRANSPORT.md\`.
- **Fixed cutoffs** \(x=317,1027\): \(r=\lfloor\sqrt{x}\rfloor=17,32\) respectively (last processed zero-killing prime \(17,31\)), \(M(317)=-4,\ M(1027)=-3\). These are prime-comb-insertion witnesses in \`SEQUENTIAL_PRIME_POPULATION_CUTOFF_AND_ANCESTRY_2026_10_11.md\`. Their post-root stages are not the root 317/1027 experiments.

The numerical data are already exact or independently checked; the missing work is to turn their *specific cancellation mechanisms* into an all-scale signed theorem.

## 1. Attack A: odd-wheel survivor minus **genuine** late semiprime

For the original VF half-run \(A=\lfloor R/2\rfloor+1\), \(B=R+1\), with \(B\le2A\), the existing occurrencewise equality for odd physical sites is
\[
\mathbf1_{\rm prime}(n)=S_A(n)-T_A(n)
\]
where \(S_A(n)\) survives all odd prime owners up to \(A\), and the only surviving composites are **two distinct primes** \(p,q>A\), both counted once by \(T_A\). With actual native VF weight \(w_r\), \(\rho_A=\prod_{3\le p\le A}(1-1/p)\) (odd conditional wheel), the exact full signed source is
\[
\sum_n(\mathbf1_{\rm prime}(n)-w_r)
=\underbrace{\sum_n(\rho_A-w_r)}_{\rm deterministic}
+\underbrace{\sum_n(S_A(n)-\rho_A)}_{\rm actual\ wheel\ fluctuation}
-\underbrace{\sum_nT_A(n)}_{\rm actual\ two\!-\!prime\ incidence}.
\]

| R | deterministic bias | survivor-minus-density | late semiprimes | **actual P-V run** |
|--:|--:|--:|--:|--:|
| 317 | +1351.612201 | -424.591317 | -942 | -14.979115 |
| 1027 | +11201.433805 | -4323.266391 | -6936 | -57.832586 |

**The important object is a single compensated sieve/semiprime fluctuation.** Bounding the survivor variance and the semiprime variance separately throws away the cancellation exhibited here. A real new analytic estimate would control the *joint* error after retaining each \(\mu\)- or VF-native charge exactly once. The late semiprimes are a naturally **balanced prime-prime Type II family** \(p,q\asymp R\), rather than an arbitrary squareful composite population.

**Carrier warning:** This identity has **VF original odd-seat weights**, not the Möbius signed cofactor \(\mu(c)\). It can attack the original #915 Sector Six (or suggest a prime Type II mechanism), but does **NOT** directly imply the Mertens 5/6 long-lag estimate without an exact sign-/mask-preserving source bridge.

## 2. Attack B: fixed-c chronology and an actual early/late source telescope

The native #915 cofactor prime intervals at completed root R show actual-minus-floor-Li errors:

| R | positive cofactor errors | negative magnitude | signed net | high-prime odd composites / Li events |
|--:|--:|--:|--:|--:|
| 317 | +50 | -62 | **-12** | 192 / 204 |
| 1027 | +144 | -133 | **+11** | 659 / 648 |

This is cofactor **and** time correlation. Earlier historical native weighted VF transport (all original physical charges) has:

| R | raw local absolute cofactor charge | abs after telescoping each c in time | signed native composite error | signed complementary smooth error |
|--:|--:|--:|--:|--:|
| 317 | 2205.880216 | 81.263616 | -80.533792 | **+83.280459** |
| 1027 | 17884.620225 | 309.192317 | -284.788121 | **+293.363482** |

The native prime-seat errors are +12.253334 and +49.424639, giving exact reassembled +15 and +58. The composite error alone cannot be bounded as the full VF response. Replacing it with Li without the smooth complement is a **known false proof route**.

The new Lean module proves, with \(\pi\) genuine or any model \(F:\mathbb N\to\mathbb R\), for fixed c and literal translated half-open walls \(L_{r,T,k}=r^2-T+k\),
\[
\boxed{\sum_{r=a}^{b-1}
\left[F(\lfloor L_{r+1,T,k}/c\rfloor)-F(\lfloor L_{r,T,k}/c\rfloor)\right]
=F(\lfloor L_{b,T,k}/c\rfloor)-F(\lfloor L_{a,T,k}/c\rfloor).}\tag{FC}
\]
After summing \(\mu(c)\) over a **fixed** cofactor range, and averaging all \(2T+1\) shifts, it remains exactly true. Apply this to \(E_\pi=\pi-\pi_{\mathrm{model}}\): **all intermediate prime-error interval endpoints disappear**, but the two remaining cofactor-weighted endpoint discrepancies are generally nonzero.

This directly links the previous #915 historical fixed-c Abel transport to PR #982's \(O(T)\) sharp/smoothed endpoint telescope, now on the **genuine Möbius cofactor carrier**. The unsigned local short-prime-window estimates are no longer the right norm to request.

**Next exact bridge (NOT YET LEAN):** combine the already compiled admissible-product orientation \(p>r,\ c\le r\iff p>c\) with the translated shell partition to obtain for \(0\le K\le H,\ T\le H-2\)
\[
\sum_{r=H}^{H+K-1}\sum_{c=1}^{r}\mu(c)
\sum_{\substack{p>r\\p\ {\rm prime}}}
\mathbf1_{\{r^2+t<pc\le(r+1)^2+t\}}
=
\sum_{c=1}^{H+K-1}\mu(c)
\left[
\pi\!\left(\left\lfloor\frac{(H+K)^2+t}{c}\right\rfloor\right)
-\pi\!\left(\max\left(c,\left\lfloor\frac{H^2+t}{c}\right\rfloor\right)\right)
\right].\tag{MOVING}
\]
The factor ordering ensures every \(\mu(c)\) appears with the true high-prime sign \(-\mu(c)\) in the Möbius source. The right-hand high-c range \(c\asymp H\), \(p>c\), \(p=O(H)\) is an actual balanced Type II coefficient problem for \(T\asymp H\); a **new signed estimate** must also retain the complementary root-smooth source \(A\) and all cross terms. (MOVING) is a proposed exact finite bridge requiring its own Lean proof and adversarial integer tests; it does not claim a 5/6 bound.

## 3. Attack C: owner-2/3 compensation and the actual original quadratic

At the true current odd VF block the original Co/Div excess is **positive**:
- R=317: +13,423.784662.
- R=1027: +105,561.281363.

But after just owner 2 the same original ledger is **negative**:
- R=317: -10,120.580460.
- R=1027: -173,464.141270.

Owner 3 reclassifies exactly 106 and 343 *physical composite sites*, respectively, and brings the total to **+25,572.580287** and **+211,608.388513**. Later owners may reduce the slack again. The 3-owner event is not a small optional correction: it creates the positive slack in these witnesses.

The three original physical sectors at completed blocks also have sharply different signed roles. Next-right is **-1,338.94382** and **-10,057.17454**, while first-left and returned-left are positive. The exact next-right source is
\[
Z_{\rm NR}=w_R^2 N_R-w_R(1-w_R)P_RC_R
\]
with the **true** prime/composite pair incidence; the second term is exactly the large negative prime-vs-composite payment.

**Proof candidate:** derive an *all-scale, history-conditioned, clipped* bound for the coupled 2/3(/5)-owner packet's contribution to the full six-sector \(B\), not independent sign-definiteness for each prime owner. Preserve one historical anchor, all actual cross-owner/mixed pairs and physical squareful/even masks.

**Required falsifiers:** At \(R=25\), next-right is positive before the first prime enters; at \(R=166\) it is temporarily positive. Hence “next-right always negative at each K/cutoff” is FALSE. At \(R=317\) actual completed next-right is negative, but cannot be spent at earlier hypothetical first-bad clocks without a new clipped-history argument.

## 4. Attack D: shared-gcd cannot be an independent sign theorem

For \(X=R^2-1\), the Möbius root-smooth/high split satisfies
\[
M(X)=S_R+H_R,\qquad
H_R=-\sum_{c<R}\mu(c)N_R(c),\quad
N_R(c)=\pi(\lfloor X/c\rfloor)-\pi(R-1).
\]
At R=317, \(S_R=-918,\ H_R=+890,\ M(X)=-28\). The cancellation is across physical smooth/high terms, not evidence of independent cofactor signs.

The exact **same-large-prime** overlap has shared-gcd signed term -8,362 and coprime term -1,950 at R=317. By R=1000 the signs are -207,442 (shared) and +47,138 (coprime). The physical **smooth/high** cross terms reverse which sector restores: at R=317 coprime -1,014,741 and shared +197,721; at R=1000 coprime +9,563,364 and shared -51,296,649. A fixed “shared always cancels” rule is therefore FALSE.

The root-6000 same-prime Gram is only 6,127,885, whereas distinct-prime-owner coherent cross products in the *same high-prime field* reach 5,517,949,907,204 before smooth compensation. That explains why measuring only shared-owner collision structure cannot establish the large signed saving. A 5/6 attack must control **different-owner mixed terms before taking absolute values**.

Empirical same-prime shared-gcd negativity through R=20,000 remains an interesting *subtheorem*; a naive pointwise shared-cumulative sign is **disproved** at t=191,931. Use actual reciprocal-band prime weights \(h_R(t)\), not arbitrary nonnegative surrogates. A proof of the same-prime sign alone is nowhere near the needed cross-owner bound.

## 5. Attack E: smaller x=317/1027 distinguishes restorative suffix from large-root sign changes

For **x=317** and **x=1027** (not root R=317/1027), the prime-candidate field after processing \(\sqrt x\) has signed values -120 and -343 versus completed \(M(x)=-4,-3\). For each new post-root prime \(p\) the exact change is
\[
\Delta_p J_x=2(1-M(\lfloor x/p\rfloor)).
\]
Because every admitted \(k=\lfloor x/p\rfloor\le32<95\), all these post-root changes are nonnegative. In the final \(x/3<p\le x/2\) strip each \(\Delta_p J_x=+2\):
\[
J_{103}(317)=-24,\quad +20\to M(317)=-4,\qquad
J_{337}(1027)=-61,\quad +58\to M(1027)=-3.
\]
But the full real source ceases to be monotone already at \(x=9215\), and at \(X=317^2-1=100488\), \(p=439\) gives \(k=228,\ M(228)=3\), hence \(\Delta_{439}J_X=-4\). Thus “more prime owners always restore” is a finite-small-x illusion.

**Useful new test:** group the post-root prime feedback by the actual **reciprocal quotient** \(k=\lfloor x/p\rfloor\), with exact prime availability
\[
N_x(k)=
\pi(\lfloor x/k\rfloor)
-\pi(\max(\lfloor\sqrt x\rfloor,\lfloor x/(k+1)\rfloor)).
\]
For the fixed completed field
\[
J_{\rm complete}(x)-J_{\lfloor\sqrt x\rfloor}(x)
=2\sum_{k=2}^{\lfloor\sqrt x\rfloor}(1-M(k))N_x(k).\tag{Q}
\]
(Q) is a *source reindexing*, not a \(5/6\) estimate. Its analytic value is that it puts **the actual lower-scale Möbius oscillation** into the same prime-availability buckets as (FC)/(MOVING), permitting a genuine signed mixed-quotient test. Need compare native \(\mu(c)\)-cofactor and candidate-stage J signs before identifying them; \(J_y\ne S_y\).

## 6. Concrete one-week-independent-test proof priorities (no background tasks)

1. **Lean Verification / Owner:** prove (MOVING) for real genuine prime \(p\), literal \(p>c\), all \(0\le K\le H\), and squareful zeros; reconcile the low-c signed source and original historical anchor. The generic fixed-c chronology (FC) is in PR #982.
2. **Analytic Type II:** isolate the *balanced* \(\mu(c)\times\mathbf1_p\) range \(c,p\asymp H\) after cofactor chronology, but **couple it to the smooth compensation and distinct-prime-owner covariance**. Quantify the saving over the elementary \(O(H^2/\log H)\) counting baseline needed for an \(H^{5/3+\varepsilon}\) amplitude target. Avoid a hidden use of the very same Mertens \(5/6\) bound.
3. **Prime Census:** regress (FC)/(MOVING) on both R=317,1027 root squares, separate x=317,1027 prime-comb clocks, and adversarial roots 25,166,1000,5561,6000 and x=9215,100488. Record *all partial K*, the positive next-right clips and prime-439 negative update.
4. **Adversarial Referee:** reject pointwise restoration by owner, an odd-wheel c=1 prime count substituted for the full even Möbius carrier, an unconditioned shared-gcd sign, a cofactor-telescoped VF weight used as \(\mu(c)\), independent same-owner norms used in place of distinct-owner cross cancellation, or complete-block statistics used for a required supremum over K.

**Conclusion:** The 317/1027 data expose *at least four substantive, complementary quantitative attack sites*: (i) wheel–semiprime matched cancellation, (ii) time-telescoped **actual** cofactor prime-error walls, (iii) history-conditioned 2/3-owner and prime/composite pair compensation, and (iv) scale-changing shared/coprime cross-owner covariance. The smaller fixed-x 317/1027 feedback supplies additional exact quotient-bucket structure plus counterexamples. None is an independent uniform \(5/6\) or RH proof yet.
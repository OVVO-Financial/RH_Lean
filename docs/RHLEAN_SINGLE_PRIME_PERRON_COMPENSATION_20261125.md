# V4: single-prime signed compensation through the native Perron alignments

**Directive SINGLE_PRIME_PERRON_COMPENSATION_V4, 2026-11-25, PR #1213.** Use the native weighted cofactor cap and paid deep tail of V3, then recover the signed cross-prime comparison using the existing Perron/Mellin operators. This update proves an exact physical alignment and an unconditional initial-owner centered estimate on paper. The new finite Lean suppliers are submitted for hosted verification; the infinite-series/variation specialization is not yet kernel-verified. No RH or improved zero-free exponent is claimed.

## 1. The actual upstream compensation to transfer

At upstream pin 8e5cefeeaffe7e4c12153385b7bb33fb7223c41a, [PartnerCountOfCentral.lean, kink](https://github.com/leanprover-community/riemann-hypothesis/blob/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/PartnerCountOfCentral.lean#L133-L193) assigns a distinct (even source, odd displacement) pair to each selected odd top destination. [ask_add_Mn, gU_lower, kinkHH](https://github.com/leanprover-community/riemann-hypothesis/blob/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/PartnerCountOfCentral.lean#L243-L432) turn matched capped capacity into a credit, and [starAt_E](https://github.com/leanprover-community/riemann-hypothesis/blob/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/PartnerCountOfCentral.lean#L689-L833) charges the remaining explicit expenses. This is not independence of prime insertions; a source may supply many targets. The separate quotient-length/valuation supplier admG1 remains upstream geometric machinery.

In the native arithmetic a prime flips/removes all its surviving multiples at once. For example 875=5^3*7=5*175. Counting both ancestry addresses as separate payments of the same liability is not justified. Even-to-odd pairing within one prime does not pay all first-depth sites, including positive even depths, and does not control repeated use across primes. We instead retain the *complete signed difference* on the actual physical carrier. The relevant already-existing RH_Lean mechanisms are:

- [weightedFreshPrimeDifference and its commutation](../research/GLOBAL_RETURNED_CORE_WEIGHTED_ALIGNMENT_INTERTWINING.lean);
- [physical Boolean-face floor expansion](../RHLean/Proof/LowWheelSurvivorFloorExpansion.lean) and [fresh-prime finite difference](../RHLean/Arithmetic/PrimeCombFiniteDifferenceFreshPrime.lean);
- [Mellin interpolation and LOG_MATCH](../RHLean/Proof/PostRootPartnerMellinInterpolation.lean);
- [weighted returned-fibre multiplicity](../research/STABLE_FAR_PERRON_RETURNED_FIBER_INTERFACE.lean);
- [signed real Perron Gram](../research/STABLE_FAR_PERRON_REAL_GRAM_COSINE.lean) and [phase-aligned physical owner compensation](../research/VF_MID_919_OAI_PHASE_ALIGNED_OWNER_COMPENSATION.lean).

The last two physical interfaces have different original weights. Do not identify their populations or import their norm bounds without the exact carrier/weight comparison below. In particular the reciprocal-square quarter frame is for q^2 descent (critical amplitude 1/q), not first-power p descent (critical amplitude 1/sqrt(p)).

## 2. Actual physical centered prefix: exact Perron supplier

For prime p define P_p=product of primes q<p, old indicator r_p(n)=1_{gcd(n,P_p)=1}, and signed centered removal

    f_p(n)=r_p(n)*(1_{p|n}-1/p).

These are the RAW V1/V3 removal coefficients, not the squarefree Möbius field and not a stripped ancestor carrier. Keep n=1 in prefixes; the physical owner starts at n=p^2.

For a complex multiplicative test weight chi, put F_p^chi(x)=sum_{1<=n<=x} r_p(n) chi(n). If chi(p*m)=z chi(m), physical removal has exactly the cofactor expansion

    sum_{n<=x,p|n} r_p(n) chi(n) = z F_p^chi(floor(x/p)).

It follows that the actual centered twisted prefix is

    Phi_p^chi(x)=z F_p^chi(floor(x/p))-F_p^chi(x)/p
               = -(1/p) weightedFreshPrimeDifference(p*z,p,F_p^chi)(x).

This is the precise reuse of the repository's arbitrary-ratio weighted Euler difference. It is not the special q^2 multiplier on a first-power shift. For chi(n)=n^(-s), z=p^(-s); in Re(s)>1 the full Dirichlet series is

    sum_{n>=1} f_p(n) n^(-s)
        = (p^(-s)-1/p) zeta(s) product_{q<p}(1-q^(-s)).

The factor p^(-s)-1/p vanishes at s=1, exactly canceling the local density pole. This by itself says nothing about uniform large-p control or the terminal RH bound. Multiplying by log n corresponds to the negative Mellin derivative. The finite phase identity is valid before any real-part or norm operation.

**Exact crossing splice to V3.** For d=p^k, M=floor(N/d), use the actual stripped ancestor prefix F(x)=sum_{m∈Q_p,m<=x} w_N(m) (or the same prefix tested against a complex observable). The cross-prime inner band in J_{p,k} is

    F(min(M,q^2-1)) - F(min(M,floor((q^2-1)/d)))
      = weightedFreshPrimeDifference(1,d,F∘min(M,-))(q^2-1).

Both the strict square endpoint and the clipped cofactor cutoff are retained. Before clipping, the continuous Perron description has the difference-of-dilated-endpoints factor (1-d^(-s)); using q^2 in place of the strict integer endpoint requires its own endpoint convention/correction. No such approximation enters the finite identity. The cofactor phase z is not the weight ratio 1/p in the density centering. Retain both.

## 3. Signed compensation of ALL later Euler attenuation crossings

Let V(r)=product_{q prime<=r}(1-1/q), a_p(n)=V(max(p,floor(sqrt(n))))/V(p). It is a nonnegative nonincreasing attenuation, equal to 1 at n=p^2, independent of the terminal N. For x>=p^2, define the physical prefix

    S_p(x) = Phi_p^1(x)-Phi_p^1(p^2-1)
           = sum_{p^2<=n<=x} f_p(n).
    H_p(x) = sum_{p^2<=n<=x} a_p(n) f_p(n).

Use the same definitions for twisted prefixes with f_p(n) chi(n) in place of f_p(n). At every q^2 where the attenuation changes, put lambda_{p,q}=V(q-1)/(q V(p)). Finite summation by parts gives exactly

    H_p(x) = a_p(x) S_p(x)
               + sum_{p<q<=floor(sqrt(x)), q prime} lambda_{p,q} S_p(q^2-1).

The coefficients are nonnegative and their sum is exactly 1: they telescope the attenuation drops from a_p(p^2)=1 to a_p(x). Consequently a bound on the full signed physical interval prefix is preserved under ALL subsequent attenuation crossings at once. This is the arithmetic compensation replacing independent matching of subsequent flips. It does not bound J in isolation: J is only one component of the V3 split, and the gains and other expenses must be kept with it. The actual V3 J crossing splice above is independently verified.

The native old-wheel prefix has the exact Möbius face expansion

    F_p^1(x) = sum_{d|P_p} mu(d) floor(x/d),
    Phi_p^1(x) = sum_{d|P_p} mu(d)
                   [floor(x/(pd))-floor(x/d)/p]
               = -(1/p) sum_{d|P_p} mu(d) (floor(x/d) mod p).

Each individual centered face floor remainder belongs to [-(p-1)/p,0]. Therefore the difference of two such remainders has magnitude at most 1 (not 2). Let B_p=2^{pi(p-1)}, the number of old squarefree faces. Then uniformly in x,y,

    |Phi_p^1(x)-Phi_p^1(y)| <= B_p.

The same bound holds for any physical interval of f_p. The attenuated interval prefix has magnitude at most B_p times its initial attenuation, by the nonnegative Abel coefficients above. In particular |H_p(x)|<=B_p. This is genuine quantitative control on the complete signed raw source, not a cap chosen by the desired terminal inequality.

For a twisted unit phase chi(n)=exp(-it log n), a further Abel step on the phase gives, for x>=L>=1,

    |sum_{L<=n<=x} f_p(n) chi(n)| <= B_p [1+|t| log(x/L)].

The bound follows from the interval bound and |d chi(u)/du|=|t|/u. The attenuated version follows by the same monotone attenuation principle. This is an exact-carrier finite-height budget; it is NOT a uniform high-height power saving and is not the q^2 quarter frame.

## 4. Independent main term and unconditional initial-prime sector estimate

Return to the original V1 D_N with N=R^2-1 and w_N(n)=log(n)(N/n-1). Each raw owner contribution is

    D_p(N)=sum_{p^2<=n<=N} a_p(n) f_p(n) w_N(n),   p<R.
    D_N = sum_{p<R} D_p(N).

The physical coefficient here includes pure p powers. It equals the V3 stripped ledger plus its exact pure-power correction U_p, not a different target.

Define, independently of N, the ordinary convergent signed series

    c_p = sum_{n>=p^2} a_p(n) f_p(n) log(n)/n.

Convergence: on n>=p^2>=4 the kernel log(n)/n decreases to 0, and the attenuated interval prefixes are bounded by B_p. This is the Dirichlet/Abel convergence argument, not a definition through the desired RH-scale comparison. For an independent truncation T>=p^2, the tail is at most B_p*a_p(T+1)*log(T+1)/(T+1) in magnitude. Thus c_p can be computed with an explicit deterministic tail enclosure.

The centering constant itself has an elementary Euler description. The full unattenuated Dirichlet series in section 2 is regular at s=1 by the bounded prefix and elementary pole cancellation. Its negative derivative at 1 is

    c_p^full = V(p-1) * ( (log p)/p * (gamma + sum_{q<p} log(q)/(q-1))
                          - (log p)^2/(2p) ),

where gamma is Euler's constant. Bounded prefixes justify the derivative at s=1 by locally uniform Abel convergence. With later Euler attenuation restored,

    c_p = c_p^full
          - sum_{n<p^2} f_p(n)*log(n)/n
          - sum_{q>p, q prime} lambda_{p,q} *
                  sum_{n>=q^2} f_p(n)*log(n)/n.

The low prefix is explicit: below p^2 the old survivors are 1 and primes q>=p; its sum is log(p)/p - (1/p)*sum_{p<=q<p^2, q prime}log(q)/q. Each inner signed tail in the later-prime sum is bounded by B_p log(q^2)/q^2, and the lambda coefficients sum to at most one. This exchange of the finite hazard expansion and the infinite tail is justified by uniformly bounded signed tails and absolute summability of the hazard coefficients (finite partial sums followed by dominated convergence for the q series). This is the exact signed Euler square-crossing centering, not a free fitted intercept.

Now subtract this independently specified linear term. The residual has a single common finite-variation kernel:

    D_p(N)-N*c_p
      = -sum_{n>=p^2} a_p(n) f_p(n) ell_N(n),
    ell_N(n)=log(n)*min(1,N/n).

The kernel increases up to n=N and decreases thereafter to 0, since N>=p^2>=4. Its discrete total variation on n>=p^2 is at most 2 log N. Apply signed Abel summation with H_p(x), bounded by B_p, and pass to the limit (the boundary term tends to zero). This proves

    |D_p(N)-N*c_p| <= 2 B_p log N.

For the first j primes p_i<R, B_{p_i}=2^(i-1), hence the actual complete initial-owner signed residual satisfies

    |sum_{i<=j} (D_{p_i}(N)-N*c_{p_i})|
      <= 2(2^j-1) log N.

Choosing j=min(pi(R-1),floor(log_2 R)) gives an unconditional O(R log R) budget, uniformly at every square clock. All their subsequent Euler attenuation crossings have already been included. More generally any j with 2^j<=R^(1+eta/2) gives O_eta(R^(1+eta)) after absorbing the logarithm. This is a genuine paid sector of the V1 centered target, independent of the deep-tail budget in V3. It does not allow us to drop the linear term N*sum c_p or imply an improved zero-free exponent.

## 5. Exact remaining high-owner comparison

Keep the original V1 B_N, M_N, K_N=D_N-(B_N-M_N). Set j by the previous cutoff and write

    K_N = E_low(N) + K_high(N),
    E_low(N)=sum_{i<=j} (D_{p_i}(N)-N*c_{p_i}),
    K_high(N)=sum_{p_j<p<R} D_p(N) -
                 [B_N-M_N-N*sum_{i<=j} c_{p_i}].

We have paid E_low unconditionally at RH scale. The remaining one-sided problem is K_high(N)>=-C_eta R^(1+eta) for every eta>0. The centering bracket is fixed from the existing terminal target and explicit constants; it cannot be chosen by optimization on N or from the desired answer.

Use the native signed Perron alignments of section 2, the exact V3 shallow carrier/cap and paid deep-power residual, and the common clipped endpoints in section 3. The deep-tail payment is for an actual odd/even expansion if used, not a deduction from D_N (which uses first depth only). Improve the exponential old-face budget for the remaining primes by reassembling the old finite Euler differences and their signed cross-owner returned multiplicities; neither commuting operators nor a pointwise frame bound proves this high-owner compensation. Do not replace the actual rough coefficients by toy unit prime waves or assume the same q^2 norm for first-power transport. Preserve the signed real Gram (NNS Co-Div where its physical weight agrees), rather than first paying each prime separately in absolute value. A full proof would supply the native counterpart of the quantitative signed comparison; no identification with admG1 is asserted.

## 6. Reproduction and exact-head status

[Lean finite physical alignment and Abel suppliers](../research/SINGLE_PRIME_PERRON_COMPENSATION_20261125.lean) use the existing weighted operator and physical Boolean-face floor results. Theorems are submitted for hosted warning-fatal compilation, not certified here. The infinite c_p convergence, explicit Euler derivative, log-kernel variation and final prime-count aggregation remain paper proofs. The previous V3 exact-head job 139307949573 had only a remaining unreachable-tactic warning at line 102; its six printed weighted declarations had the three standard axioms. This patch removes that redundant tactic without changing a statement or linter.

[Executable actual carrier test](../scripts/single_prime_perron_compensation_20261125.js) and [recorded outputs](single_prime_perron_compensation_20261125.json). The integer floor remainders are checked exactly in the tested range. Other weights, attenuation and the complex phase t=7/3 are binary64 diagnostics, not certified numerical enclosures. Tail constants are independently approximated by T=(2R)^2-1. The last column is the paper error bound for the true centered residual; the separate truncation bound must be added when comparing the displayed finite approximation.

| R | initial primes | last initial prime | low raw D | approximate low centered residual | true residual bound | finite truncation bound |
|---:|---:|---:|---:|---:|---:|---:|
|64|6|13|1820.83|-20.94|1048.01|152.80|
|317|8|19|52860.75|-56.00|5874.07|822.63|
|1027|10|29|619772.24|-108.84|28375.55|3901.49|

All 255 incoming-prime tests for each of: raw Perron twisted cofactor reindexing, V3 cross-prime square-band decomposition, and signed weighted Abel reassembly passed. 108505 signed hazard-prefix checks (with corresponding complex phase checks) and 12943 exact integer inclusion-exclusion interval checks passed. Maximum scaled real/complex identity error 2.24e-12. No initial-owner centered bound violation after accounting for the truncation allowance.

## 7. Revised seven-role attack directive

- COORDINATOR: use V4 K_high as the exact remaining signed target; do not restart the rank-independence construction. Preserve V3 deep budget and V4 initial-owner budget as separate proved paper suppliers; integrate into #1201 only after actual Lean verification and the high-owner comparison.
- WHEEL: formalize a_p and its exact hazard drops on the physical count prefix, and the clipped square-band J identity on the V3 carrier. Prove the actual complex-phase specialization chi(n)=n^(-s), retaining the exact p*z factor in the centered operator.
- OWNER: reconstruct the remaining starAt_E signed comparison as actual high-owner returned boundary compensation, retaining every old-owner coordinate until common-carrier Fubini. Explicitly identify the source of savings; don't duplicate a liability across valid ancestry addresses.
- ANALYTIC: formalize c_p convergence and its explicit Euler derivative/centering formula, log-kernel variation and initial-owner aggregate bound. Use the existing Mellin/Perron interfaces at the correct contour and retain cutoffs. Attack K_high without recentering the terminal target.
- CENSUS: test the actual high-owner signed centered residual and mixed q,p square crossings with native phase/returned-fibre weights. Compare cancellation before/after attenuation; preserve signs. Extend the initial-owner tail computations with explicit tail bounds.
- REFEREE: audit pure-power restoration, exact p^2 lower boundary, all cross-prime multiplicities, first-power vs square-power Mellin scaling, independence of c_p from N, and every remaining signed comparison. Reject a proof that only asserts a cap, commutation, or tautological terminal inequality.
- LEAN: compile new finite suppliers and the V3 linter repair, then formalize the actual scalar specialization/initial-prime theorem. Prove quantitative high-owner closure before calling the existing square-clock RH consumer. No new assumed terminal estimate.

This is a repository-scoped directive. It does not launch or reconfigure any external agent runtime. The final integration PR #1201 is unchanged.

## 8. V5 complete-cell attack

See [the new native mod-four two-clock discrepancy reduction and seven-role directive](RHLEAN_CROSS_CELL_PERRON_COMPENSATION_20261125.md). This supersedes the immediate V4 high-owner attack by an exactly centered finite-window sufficient target; V4 suppliers remain intact. All new V5 bounds are paper derivations pending formalization.

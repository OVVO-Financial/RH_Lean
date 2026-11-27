# V5: mod-four complete-cell Perron compensation

**Directive CROSS_CELL_PERRON_V5, 2026-11-25, PR #1213.** Preserve the original V1 physical signed Euler source and #1201 final integration. Use the existing mod-four geometry and Perron alignments to recover the quantitative consequence of Alpöge's economical recovery, not his entire host geometry. The following are paper derivations and numerical diagnostics; no new Lean theorem or RH claim is made.

## 1. Finite two-clock centering

Retain V1's K(N)=D_N-(B_N-M_N)=M_N-T_N, where T_N=sum_{prime l<=N} log(l)(N/l-1) and M_N=N log N-(1+gamma+c_pp)N. For R>=2 take X=R^2-1, Y=4R^2-1 and t=X/Y. Define

    g(n) = 1-t             (1<=n<=X)
         = X/n-t           (X<n<=Y)
         = 0               (n>Y)
    h(n) = log(n)*g(n)
    I_R = K(X)-t*K(Y)
        = sum_{prime l<=Y} h(l) - X log(Y/X).

This subtracts the original weights and deterministic main terms; all N-linear constants cancel exactly. The proper-power payment remains in the final V1 handoff, once only. The classical quantitative PNT (or the classical Mertens constant for sum Lambda(n)/n) gives sum_{n<=N} Lambda(n)/n=log N-gamma+o(1) and psi(N)=N+o(N). With V1's proper-power error this implies K(N)/N->0. Hence for X_j=(2^j R)^2-1,

    K(X) = lim_{m->infty} sum_{j=0}^{m-1} (X/X_j)*I_(2^j R).

If I_R >= -C_eta R^(1+eta) uniformly for every 0<eta<1, the negative majorants sum since X/X_j<=4^(-j). This supplies the original one-sided K bound (larger eta follows by weakening the exponent) and the existing square-clock RH consumer. No assertion that a one-sided K bound alone implies a one-sided I bound is required. Finite telescoping and the vanishing endpoint suffice, without assuming absolute convergence.

Let r(n)=floor sqrt(n), V(r)=product_{q<=r,prime}(1-1/q), f_p(n)=1_{old survivor}(1_{p|n}-1/p), a_p(n)=V(max(p,r(n)))/V(p). The physical owner restriction is n>=p^2. The weight h is nonnegative and unimodal, increasing to X, decreasing after X by differentiation, with H=max h=(1-t)log X.

    B_h = sum_{2<=n<=Y} V(r(n))*h(n)
    D_p[h] = sum_{p^2<=n<=Y} a_p(n)*f_p(n)*h(n)
    I_R = B_h - sum_{p<2R}D_p[h] - X log(Y/X).

This is the V1 sitewise Euler telescope. n=1 has zero weight. Let j=floor(log_2 R), b the j-th prime (truncate to the primes <R if necessary). Keep b fixed at BOTH clocks. V4's initial-owner estimate implies sum_{p<=b}D_p[h]=O(R log R), because c_p cancels for each p and the two residual bounds sum to at most 2*(2^j-1)*(log X+t log Y). Equivalently apply V4 finite Abel directly to h. Define

    I_high = B_h - sum_{b<p<2R}D_p[h] - X log(Y/X)
    I_R = I_high - sum_{p<=b}D_p[h].

## 2. Native complete-cell operator

The existing [FourSlotCell.lean](../RHLean/Arithmetic/FourSlotCell.lean) compresses the three active Möbius slots 1,2,3. The raw survivor carrier here is DISTINCT: for odd p, 2 is already inserted, leaving only slots 1 and 3. The p=2 contribution is included in the paid initial sector for sufficiently large R. The full physical address n=4k+r transforms under p into (pk+floor(pr/4), pr mod 4). Odd p preserves the odd slots if p=1 mod 4 and exchanges them if p=3 mod 4. Keep the cell index and exponent depth. The residue alone cannot identify the physical site. Prime powers can survive in the raw carrier even if their Möbius value is zero.

Let F_p(k)=number of old survivors n<=4k, including n=1. Let k0=(p^2-1)/4. Every odd prime square starts a complete cell C_k=[4k+1,4k+4], so the lower cutoff and all later attenuation changes agree with cell boundaries. The terminal Y omits the last even slot; extend with zero h there.

    A_p(k)=number of old survivors <=floor(4k/p)
    A_p(k)=F_p(floor(k/p))+b_p(k),  0<=b_p(k)<=2.

Indeed floor(4k/p)=4 floor(k/p)+floor(4*(k mod p)/p) and the latter floor is in {0,1,2,3}; the incomplete cell has at most two odd sites. Exact V4 cofactor transport gives the centered raw prefix at 4k:

    Phi_p(4k)=F_p(floor(k/p))-F_p(k)/p+b_p(k).

The two full-cell terms are -(1/p)*weightedFreshPrimeDifference(p,p,F_p)(k) on the real/complex embedding. Use [existing arbitrary-ratio operator](../research/GLOBAL_RETURNED_CORE_WEIGHTED_ALIGNMENT_INTERTWINING.lean); the twisted site version still uses z=p^(-s) and ratio p*z. Do NOT silently substitute the q^2 critical multiplier or infer a norm from operator commutation.

## 3. New unconditional O(R) aggregate payment

Freeze h on each cell at h(4k+1), keeping attenuation exact. After summing high owners, the actual coefficient at n>=2 is

    d_b(n)=1_{r(n)>b, minFac(n)>b}*(V(r(n))/V(b)-1_{n prime}).

This is the V1 telescope restricted to high owners, and abs(d_b(n))<=1. Thus the combined high-owner freezing error is <=3*TV(h)<=6H; sum over owners with signs BEFORE freezing. The excluded unit has zero original weight.

Set W_p(k)=a_p(4k+1)*h(4k+1) for k0<=k<R^2 and zero outside. Its total upward variation (including initial jump) is <=H, because attenuation is nonincreasing in [0,1], h increases until its peak and then decreases. The downward variation equals the upward variation. For a real prefix e(k) ranging over an interval of width L, summation by parts therefore gives

    abs(sum_{k=k0}^{R^2-1} W_p(k)*(e(k+1)-e(k))) <= L*H.

The coefficients of e sum to zero and their positive/negative masses are each <=H; shift e by its lower endpoint. This includes both boundary terms, even if e(k0) is nonzero. For b_p, L=2: incomplete cofactor returns cost <=2H per owner, hence <=2*pi(2R)*H=O(R) by Chebyshev.

Let E_p(k)=F_p(k)-4kV(p-1). The genuine symmetric cross-cell discrepancy is

    Gamma_p(k)=E_p(floor(k/p))-E_p(k)/p
    Phi_p(4k)=Gamma_p(k)+b_p(k)-4V(p-1)*{k/p}.

The deterministic density sawtooth has width 4V(p-1)<=4, so costs <=4H per prime by the same Abel inequality. No bound on E_p is assumed. Define

    Q_R = sum_{b<p<2R} sum_{k=k0}^{R^2-1} W_p(k)*
                          (Gamma_p(k+1)-Gamma_p(k))
    J_R = B_h - X log(Y/X) - Q_R.

Then abs(I_high-J_R)<=6H+6*pi(2R)*H=O(R). The initial-owner payment and dyadic reconstruction show that the remaining sufficient quantitative target is

    For every eta>0, J_R >= -C_eta R^(1+eta) uniformly for all large R.

This is a signed comparison on the exact physical population, not a bound on the uncentered Q_R. Preserve the deterministic B_h-X log(Y/X); do not refit it. No new assumed terminal estimate.

## 4. Exact obstruction to literal same-root recovery

For p>Y^(1/3), every surviving composite removed by p is p*q with q prime >=p (including p^2): three factors >=p exceed Y. Its recovery root q<=Y/p<p^2. The negative prime-debit sites l>=p^2 have disjoint roots. Across ALL p>Y^(1/3), recovery roots q<Y^(2/3), prime-debit roots l>Y^(2/3). No same-root overlap.

Primes l>Y/2 have no nontrivial parent and no child within the finite physical multiplication graph. For c=floor(Y^(1/3)), their high-owner negative coefficient is 1-V(r(l))/V(c) when r(l)>c. The mass on Y/2<l<=3Y/4 is asymptotic to

    (Y/12)*(log(3/2)-1/4).

By classical PNT and Mertens' product theorem, V(r(l))/V(c)->2/3 uniformly there; t->1/4 and h(l)=log(l)*t*(Y/l-1). Integrate against theta by partial summation. This is order Y before deterministic centering. Literal multiplication matches cannot pay the whole raw debt by themselves: retain the baseline and cross-root interactions. This does not refute Alpöge's actual geometric normalized rank/degree or signed comparison.

## 5. Signed Gram: retain the actual centered source

On each physical cell let

    e_k = sum_{n in C_k,2<=n<=Y} [(V(r(n))-d_b(n))*h(n)-g(n)].

The sum equals I_high plus the deterministic quadrature X log(Y/X)-sum_{2<=n<=Y}g(n)=O(1) by monotonicity and the integral of g over [0,Y]. This is the actual centered cell population. Expanding a block's square gives its diagonal plus twice the actual cross-cell products. For complex tests use the existing Perron operator at the correct first-power phase, not the q^2 Gram normalization. The reduced version uses Q_R against the SAME baseline; the corrections are paid at O(R). Negative observed cross terms do not prove a contraction or uniform lower bound. Require a genuine quantitative signed comparison on this complete population, retaining every sign and multiplicity. V3 deep-tail payment is distinct and may only be consumed if a real odd/even expansion is introduced.

## 6. Reproduction

Compile [C++ diagnostic](../scripts/cross_cell_perron_attack_20261125.cpp):

    g++ -O3 -std=c++17 scripts/cross_cell_perron_attack_20261125.cpp -o /tmp/cross_cell_perron_attack
    /tmp/cross_cell_perron_attack

Default R=64,317,1027,2048,4096, largest Y=67108863; alternatively pass 64 317. See [full JSONL](cross_cell_perron_results_20261125.jsonl). All recorded assertions passed. The independent full per-prime prefix loop is restricted to R<=317 (10,854,723 exact integer checks). Across all five scales, 7,914,125 physical child relocations, maximum virtual occupancy 2. At larger scales use sitewise enumeration and relocated children, not the full direct prefix loop. Local audit reran 64 and 317 with identical JSON rows; higher-scale rows are preserved from the preceding run. Weights, attenuation and energy are long-double diagnostics, not certified real enclosures.

| R | I_high/R | sum abs incomplete correction | bound | isolated top mass | shared roots |
|---:|---:|---:|---:|---:|---:|
|64|-0.99570|33.99|311.93|169.61|0|
|317|-1.00272|160.91|1848.61|4466.50|0|
|1027|-1.00893|476.62|6240.96|49951.87|0|
|2048|-1.04492|895.58|12649.24|200378.23|0|
|4096|-1.04915|1684.95|25352.55|808983.37|0|

At R=4096 freezing error 0.02624, sum abs density correction 592.96 (bound 3669.99); Q_R=2806229.90308. I_high=-4297.33808, J_R=I_high+(high_pos-high_neg)-Q_R, about -2599.15. Finite observations are consistent with RH-scale behavior, not a uniform estimate. No improved zero-free exponent is claimed.

## 7. Seven-role directive (V5 supersedes V4's immediate attack target)

- COORDINATOR: track J_R as finite two-clock target with fixed b and original baseline. Charge V5 O(R) and V4 initial-owner O(R log R) once each. Keep #1201 final.
- WHEEL: formalize F_p, exact floor split, odd-slot partial count <=2, p^2 alignment and signed whole-carrier freezing. Reuse FourSlotCell without identifying the raw survivor field with Moebius.
- OWNER: attack the actual cross-root/cross-cell signed discrepancy using the existing first-owner returned fibres. Same-root-only matching is excluded in the cube-root sector. Keep baseline and signs across primes; earn the quantitative comparison rather than a raw recovery count.
- ANALYTIC: formalize two-clock kernel, K(N)/N->0 from classical quantitative PNT, dyadic one-sided telescope and original quantifiers. Prove range-width Abel and Chebyshev aggregation. Preserve exact first-power p*z alignment and proper-power handoff.
- CENSUS: extend reproducible actual-population tests. Stratify cross-cell and cross-owner covariance by distance, depth and cube-root sector. Compare J_R against original baseline and separated paid corrections; no fitted centering or toy phase waves.
- REFEREE: audit signs, clipping, same b at both clocks, nonzero starting prefix, last even slot, raw-vs-Moebius mismatch, p^(-s) vs q^(-2s) and claimed uniform gains. Reject tautological Gram bounds or unsupported claims about upstream geometry.
- LEAN: reuse research/SINGLE_PRIME_PERRON_COMPENSATION_20261125.lean (oldSites_image_eq_removedSites, actual_centered_phase_eq_perron_difference, finiteAbel) and GLOBAL_RETURNED_CORE_WEIGHTED_ALIGNMENT_INTERTWINING.lean. Formalize V5 finite suppliers, then the quantitative comparison and terminal specialization. No new assumed endpoint, sorry, vacuous predicates or custom axioms.

Repository-scoped instructions only. No external agent runtime change or merge. New paper suppliers await Lean formalization and semantic review; no new Lean declarations in this update.

## 8. V6 — integral multiplicity rather than a restated energy gap

See [the native multiplicity-and-index construction, exact factorial recovery and revised role directive](RHLEAN_NATIVE_MULTIPLICITY_INDEX_20261125.md). V6 is the priority experiment: independent arithmetic divisibility and size, not a renamed cumulative negative-balance bound. V5's physical reduction remains available; V6 introduces no new Lean declarations or assumed terminal inequality.

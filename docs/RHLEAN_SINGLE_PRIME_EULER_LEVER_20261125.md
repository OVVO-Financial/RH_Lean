# One prime per Euler: native economical recovery attack

**Directive SINGLE_PRIME_EULER_LEVER_V1 (2026-11-25).** The only generating geometric operation is the extension of the existing Euler wheel by one new prime. This is a separate reusable arithmetic-supplier research PR explicitly requested by the user. It does not replace #1201 as the final completion PR, weaken its audits, or import a terminal RH theorem. The target is an independently earned inequality, not another conditional RH endpoint.

## 1. Exact physical operation

Fix an integer set I, actual weight w(n), and the set S of all primes preceding the newly inserted prime p. Write s_S(n) for the indicator that no q in S divides n. Define

    A_S(I) = sum_{n in I} w(n) s_S(n)
    C_p(I) = sum_{n in I, p | n} w(n) s_S(n)
    delta_p(I) = C_p(I) - A_S(I)/p.

Then s_(S+p) = s_S(1 - 1_{p|n}), and A_(S+p) = (1-1/p) A_S - delta_p. Each removed integer is owned by its least prime, so distinct owner sectors are disjoint, with no probabilistic premise. The fresh prime is coprime to all preceding primes; hence s_S(pm)=s_S(m), and

    C_p(I) = sum_{m : pm in I} w(pm) s_S(m).

The cofactor reindexing preserves the actual weights and all endpoint restrictions. On an interval [L,U], the exact cofactor interval is [ceil(L/p),floor(U/p)]. On a complete old wheel fibre, CRT supplies exactly p lifts, one removed; truncated physical intervals do NOT have those multiplicities automatically.

For the unweighted prefix H_S(t) = #{1<=n<=floor(t): s_S(n)=1}, write F_S(t)=H_S(t)-t V_S, where V_S=prod_{q in S}(1-1/q). For every real t>=0,

    H_(S+p)(t)=H_S(t)-H_S(t/p),
    F_(S+p)(t)=F_S(t)-F_S(t/p),
    delta_p([1,t])=F_S(t/p)-F_S(t)/p.

For a general interval use the difference of endpoint prefixes, not an independent residue distribution. For nonnegative weights use Abel summation or actual pulled-back weights, retaining the boundary terms. This recurrence is an explicit native transport along the sole Euler lever.

Submitted Lean: [one-prime formalization](../research/SINGLE_PRIME_EULER_DEFECT_20261125.lean), including actual finite owner/cofactor transport, weighted step, attenuated telescoping and scalar centering equivalence. The proof uses the original finite sets, not abstract assumed removal amounts. Existing main has [signed Buchstab recursion](../RHLean/Arithmetic/SignedBuchstabRecursion.lean), [prime-wheel recovery](../RHLean/Arithmetic/PrimeWheelMobiusRecovery.lean) and [fixed square-wheel and ancestry](../research/SQUARE_BLOCK_EULER_ANCESTRY_COVARIANCE_20261017.lean). The signed Möbius recursion complements the unsigned survival recurrence; do not conflate them.

## 2. Physical square-block decomposition and exact target

Let N=R^2-1, R>=2, and I_r=[r^2,(r+1)^2-1] intersect [2,N] for 1<=r<R. Let w_N(n)=log(n)(N/n-1). In block r the wheel through r removes exactly the composite sites; I_1={2,3} uses the empty wheel. Every other composite has least prime <=r. Put

    V(r)=prod_{p<=r}(1-1/p)
    B_N=sum_{r<R} V(r) A_empty(I_r)
    D_N=sum_{r<R} sum_{p<=r} (V(r)/V(p)) delta_{p,r,N}
    T_N=sum_{p<=N} w_N(p).

The exact identity is T_N=B_N-D_N. In addition, total composite removal is sum_{r,p} C_p(I_r). No overlap of owners is double charged. All products and sums are finite. For the high-owner tail, if p^3>(r+1)^2-1, every surviving cofactor in I_r is a prime q>=p: m>=p, and m<p^2 excludes a composite whose prime factors are >=p. In particular the complete sector p>N^(1/3) is exactly

    sum_{N^(1/3)<p<=sqrt(N)} sum_{p<=q<=N/p, q prime} w_N(pq).

This does not bound that sector, but gives an exact first-prime-pair bill, including squares, from the single Euler extension.

Use the proper-prime-power centering submitted on [#1201 at 5eb0d87](https://github.com/OVVO-Financial/RH_Lean/blob/5eb0d87573d087aed794ef065ceea034021fa280/RHLean/Analysis/AlpogeNativeProperPowerCentering.lean#L164-L218). It is not yet on main at the base of this PR. With c_pp=sum_p log(p)/(p(p-1)), P_N=sum_{p^a<=N,a>=2}log(p)(N/p^a-1),

    E_N = N c_pp - P_N,       0<=E_N<=C sqrt(N)
    M_N = N log N - (1+gamma+c_pp)N
    K_N = D_N - (B_N-M_N).

For the literal principal source in RHLean,

    G(N) = T_N + P_N - N log N + (1+gamma) N
         = -K_N - E_N.

The exact target (sufficient and necessary up to the unconditional O(R) proper-power error) is therefore

    For each eta>0, there exist C_eta>=0,R0 such that
    for every R>=max(2,R0):
    K_(R^2-1) >= -C_eta R^(1+eta).

No absolute bound on K is required. This supplies the existing
[SquareClockBound / riemannHypothesis_of_squareClockBound](../RHLean/Analysis/AlpogeNativeBoundHandoff.lean) at the existing quantifier order. Alternatively supply the existing complete-real-window bound with uniform constants, including every real point by the proved interpolation. Do not replace the all-scale target with isolated good endpoints, nor assume that sparse square windows automatically imply complete real windows.

## 3. Mandatory correction: the uncentered Euler debt is large

The raw sum D_N is NOT the small residual to bound. By the classical Mertens product theorem, log(n) V(floor(sqrt(n))) tends to 2 exp(-gamma). Since sum_{2<=n<=N}(N/n-1)=N log N+O(N), a finite initial segment costs O(N), and an arbitrarily small uniform tail error costs o(N log N),

    B_N = (2 exp(-gamma)+o(1)) N log N.

By partial summation of PNT, sum_{p<=N}log(p)/p=(1+o(1))log N and theta(N)=O(N), hence T_N=(1+o(1))N log N. Therefore, unconditionally as a classical paper argument,

    D_N = (2 exp(-gamma)-1+o(1)) N log N.

The coefficient is positive (about 0.1229). The raw debt is order N log N, not order sqrt(N), even assuming RH. Do not try to prove a subpower absolute envelope on the raw defects or use the uncentered net sum as an RH-scale residual. This paper asymptotic has not been formalized here. It identifies the mandatory deterministic centering and the actual signed lower-bound direction.

## 4. Initial reproducible attack and limitations

Run node scripts/single_prime_euler_defect_20261125.js. Each block is independently enumerated with a least-prime sieve; each removed sector is checked against its cofactor interval, every count telescope is verified by BigInt with no division or floating point, and every weighted telescope and source recombination is checked in binary64. The exact integer recurrence uses old P=prod primes, phi=prod(p-1), A=initial survivors at the step, c=removed count and D an accumulated numerator:

    D_new=(p-1)D+(pc-A)P,
    P_new=pP, phi_new=(p-1)phi,
    A_new P_new = |I| phi_new - D_new.

Default run results (weighted entries rounded; c_pp is truncated at p<=N; this is diagnostic, not certified log/constant evaluation):

| R | exact steps | positive / negative / zero count defects | raw D_N | attenuated sum of abs(weighted defects) | K_N with truncated c_pp | G(N) |
|---:|---:|---:|---:|---:|---:|---:|
|16|55|29 / 18 / 8|90.43|241.82|-40.18|1.73|
|32|192|99 / 74 / 19|480.69|1507.04|-77.84|1.43|
|64|651|340 / 270 / 41|2441.32|8387.06|-153.10|1.85|
|317|11399|5606 / 5511 / 282|93405.92|362796.50|-710.57|3.79|
|1027|96455|45174 / 50318 / 963|1264074.42|5114310.17|-2225.27|7.14|

Total exact step checks: 108752. These are finite consistency tests only. At R=1027 the raw debt is over a million and the absolute attenuated sum exceeds five million; the centered defect is about -2225 and the proper-power error about +2218 in the truncated model. The terminal G is about 7.14. The original G recombination is independent of the truncation algebraically; weighted numerics have rounding error. The omitted prime tail of c_pp is positive and bounded by the corresponding all-integer tail O(log N/N); multiplying by N costs O(log N). No asymptotic RH-scale estimate follows from these five cases.

## 5. Attack the actual inequality using Alpöge's quantitative map

Every proposed auxiliary object must come with the diagram of ONE fresh prime insertion, its exact physical action, and the original signed cost it controls. The next attack is not another definition of the bound.

Use [ManyEdges/EdgeFam/EdgeStep/SrcTests](https://github.com/leanprover-community/riemann-hypothesis/blob/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a/src/Formalism/SharpRestriction/GrowthBounds/ScaleEdges/ManyEdges.lean) and [the numerical consumer](https://github.com/leanprover-community/riemann-hypothesis/blob/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a/src/Formalism/SharpRestriction/GrowthBounds/PlaneCountTheoremWithConstants.lean#L598-L646) as the quantitative blueprint; see [DAG](https://riemann.verifytask.cn/?lang=en). Distinguish the local quotient-length supplier admG1 and signed gain Conclusion1. A CRT rank count by itself is not either theorem.

1. For each surviving old residue fibre, construct the integral parent-to-child incidence for adding p, retaining the actual integer interval. Derive the kernel and image of the restricted selected/competing readouts, rather than count all CRT lifts in a full period. Prove exact ownership and use the cofactor recurrence to compare old and new physical populations.
2. Determine which label differences are killed by the **complete signed functional**; allow quotient recovery only after proving that vanishing (or a quantitatively paid error). Test shared-site obstructions against #1201, including 43^3=[43^2]*43 and distinct first primes with shared colours. One-prime ancestry is not automatically physical recovery.
3. Transport the actual local rank/depth/exceptional-layer budget on the restricted fibre from Alpöge's supplying proofs or prove the native replacement. Establish a signed gain/cost comparison for the same measured family. Preserve p-adic valuation depth, exact weights, multiplicities, boundaries, and all terms if using upstream ASK/MAIN and Q. No synthetic witnesses or replacement of the upstream Q by V(r).
4. Recombine signed marginal defects BEFORE taking absolute values. Work against the exact deterministic main B_N-M_N, not 0. Use prefix recurrence F_(S+p)(t)=F_S(t)-F_S(t/p), the interval pullback, and the semiprime tail split above. The decisive inequality is a lower bound for K_N with the proper-power cost paid once, not a claimed norm of an unsigned inverse.
5. Verify the eventual R quantifiers and apply the existing #1205 native square-clock consumer. If only a window argument is earned, prove its full real-window hypotheses before using the other consumer. No new conditional endpoint, RH claim, or mathematical completion PR is opened by this research supplier.

### Existing seven roles — one frontier

- COORDINATOR: ledger each prime-extension input/output, one signed target K_N, exact missing supplying theorem, and status. Reuse main and #1201 declarations; do not count identities as bounds.
- WHEEL: prove physical CRT restriction and cofactor transport, prefix/interval recurrence, ownership, truncated rank/depth, semiprime tail; test actual rank loss.
- CENSUS: reproduce exact diagnostics, stratify by p/r, wheel stage and cofactor length, extend R, retain raw signs and deterministic drift; supply reproducible counterexamples to proposed local bounds.
- OWNER: derive the actual centered marginal gain/payment from the upstream local quantitative supplier or native substitute, with same-frame costs and all signed terms.
- ANALYTIC: prove uniform aggregate lower bound after centering; use summation by parts, complete windows and the already paid terminal proper powers, never assert unearned equidistribution or independence.
- REFEREE: challenge partial-window CRT inference, parity barrier, weighted inverse growth, quotient-vs-signed confusion, hidden assumption of the target, missing small primes, double payments and exceptional losses.
- LEAN: verify the submitted arithmetic module under hosted warning-fatal Lean; formalize square-clock and prefix joins, exact centered target and proven suppliers only. Coordinate any final bound with #1201 rather than adding a competing RH endpoint.

Acceptance: independently prove the centered aggregate lower bound for the actual arithmetic source, or report the first explicit local rank/payment inequality that remains unproved. A green build of the submitted identities alone is not closure. Preserve existing role access, report continuity, model/cadence, hosted-only verification, semantic dependency audit and human-only merge. The directive is scoped to this PR until reviewed; repository edits do not themselves launch or reconfigure agents.

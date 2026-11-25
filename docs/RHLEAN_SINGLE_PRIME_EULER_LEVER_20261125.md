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


## 6. V2 — trace Alpöge's own single-prime operation first

**Directive SINGLE_PRIME_FROBENIUS_GAIN_V2 (2026-11-25).** Refines the attack order in section 5; the centered source and acceptance gates remain unchanged. Before attempting a native inequality, reconstruct the actual upstream prime action, its two channels and its two distinct quantitative payments. Do not assume an Euler-wheel insertion is literally Alpöge's construction.

### 6.1 Pinned source ledger

All links below are to community commit 8e5cefeeaffe7e4c12153385b7bb33fb7223c41a.

- [Host group and Frobenius](https://github.com/leanprover-community/riemann-hypothesis/blob/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a/src/Formalism/FrobeniusOrbits/Statement.lean#L26-L46), [HostFrob](https://github.com/leanprover-community/riemann-hypothesis/blob/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a/src/Formalism/FrobeniusOrbits/Statement.lean#L172-L183): the host is two sign characters times the unit group modulo 2^(e+2), quotiented by ±1. For unramified p the signs are the Jacobi symbols (-q/p),(-d/p), and the remaining coordinate is the class of p modulo 2^(e+2). The fixed host action is arithmetically computable without constructing a CM variety. It is not a succession of enlarging squarefree Euler wheels. The ordinary old wheel does not in general encode the 2-power coordinate; use an auxiliary modular coordinate and explicit characters if reproducing the host action. Treat p=2,q,d separately. Do not replace the host's geometric suppliers by this finite-group observation.
- [partner, stepP, nP, fillG](https://github.com/leanprover-community/riemann-hypothesis/blob/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L99-L165): partner(p,s,k) = (IsSg(p) and Odd(k), s+k*hP(p)). Signal primes use stepP=2*hP; the Boolean sheet is meaningful. Plain orbit parity is not well-defined modulo an odd orbit order. Prime 3 acting on the previous wheel 2 already has order 1. Retain the exponent and sheet separately.
- [gamma, rho, gainG, excessGain](https://github.com/leanprover-community/riemann-hypothesis/blob/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a/src/Formalism/GrowthSums/StatementA.lean#L34-L50) and [CappedGainSubLE](https://github.com/leanprover-community/riemann-hypothesis/blob/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a/src/Formalism/GrowthSums/StatementG.lean#L14-L22): distinguish a capped-gain formula from the hypotheses that actual intermediate quantities are bounded by each cap. In particular CappedGainSubLE is a stated proposition, not by itself a supplying proof.
- [capU, Excl, dl, g0, gU, Pr](https://github.com/leanprover-community/riemann-hypothesis/blob/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L218-L261) and [tauP, ioP, gainP, askG, askP](https://github.com/leanprover-community/riemann-hypothesis/blob/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L330-L365): the operative gainP is a sum of maxima of zero, g0, and (on VV) gU-Pr, not simply gainG. g0 excludes selected first-hit displacements, gU has a restricted set of capped terms, dl charges orbit length and top multiplicity, and tauP and ioP are additional expenditure. Record all exclusions, offsets, normalizations, small-prime and exceptional sectors.
- [isEdge_of_basis](https://github.com/leanprover-community/riemann-hypothesis/blob/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a/src/Formalism/SharpRestriction/GrowthBounds/ScaleEdges/EdgePlane.lean#L137-L200): the prime-local lattice extension has quotient size p^(f*r) under its residue-ring and basis hypotheses. CRT lift counts do not establish the selected evaluation rank or actual divisibility.
- [GainBoundAt](https://github.com/leanprover-community/riemann-hypothesis/blob/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/Conclusion1OfGainBoundAll.lean#L89-L107), [admG1](https://github.com/leanprover-community/riemann-hypothesis/blob/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a/src/Formalism/SharpRestriction/GrowthBounds/SmallOrderPrimes.lean#L177-L187) and [linkG_at_core](https://github.com/leanprover-community/riemann-hypothesis/blob/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a/src/Formalism/SharpRestriction/GrowthBounds/PlaneCountTheoremWithConstants.lean#L592-L646): separate the signed ask/gain inequality from the local quotient-length and valuation supplier. Both are required by the downstream comparison. Inspect proofs of the suppliers, not merely the consumers.

### 6.2 Exact operator and physical prime-power transport

For a fresh prime p and old wheel P coprime to p, let T_p push a vector on reduced residues forward by a -> p*a mod P. It is a permutation. In any finite-dimensional norm in which it is isometric, the convergent operators are

    O_p = sum_{k>=1, k odd} p^(-k) T_p^k
        = (T_p/p) (Id-T_p^2/p^2)^(-1)
    E_p = sum_{k>=2, k even} p^(-k) T_p^k
        = (T_p^2/p^2) (Id-T_p^2/p^2)^(-1).

Summing coordinates gives gamma_p=p/(p^2-1) and rho_p=1/(p^2-1). This is an exact finite-wheel realization of the scalar geometric series, not a bound on the physical source.

For a physical positive integer interval I=[L,U], define A_t as its old-wheel population at residue t. For d=p^k, let B_k(t) count n in I with n=t mod P and d|n. The actual weighted layer for arbitrary original w is exactly

    B_k(t;w) = sum_{m in [ceil(L/d),floor(U/d)], m=d^(-1)*t mod P} w(d*m).

The inverse is taken modulo P; no division by a residue that is not a unit. For k=1, summing over t gives the actual one-prime removal from section 1. The higher layers are nested; sum over odd k of 1_{p^k|n} is ceil(v_p(n)/2) and sum over positive even k is floor(v_p(n)/2). Their difference detects odd valuation, not squarefreeness and not total first-prime removal. Keep this separate from the signed Möbius recursion and the terminal proper-power payment.

**Exact boundary theorem (paper proof):** the A_t sites in I form one consecutive arithmetic progression of difference P. Divisibility by d selects exactly one residue class of its index modulo d. If A_t=d*q+r, 0<=r<d, then B_k(t)=q+epsilon, where epsilon is 0 or 1 determined by the position of that residue class in the remaining r indices. Consequently

    d*B_k(t)-A_t = d*epsilon-r,  |d*B_k(t)-A_t| < d.

If s=d^(-1)*t mod P, then |A_s-A_t|<=1 for an unweighted contiguous interval, since all residue classes modulo P have floor or ceil(|I|/P) representatives. Thus

    B_k(t)-A_s/d = (d*epsilon-r)/d + (A_t-A_s)/d,
    |d*B_k(t)-A_s| <= d.

The latter follows by integer rounding from the strict first bound. This decomposition isolates the physical endpoint phase and source/destination mismatch. For weights use the exact pulled-back weight or Abel summation of the interval counts; do not replace weights by a uniform density. A per-fibre O(1) bound is not a useful global estimate when the number of active fibres grows with the physical block length.

### 6.3 Decisive exact obstruction to a bare wheel gain

Set P=30, p=7 and use two half-open-in-spirit, closed integer subintervals of the *same* square block [900,960]:

    I=[900,929], J=[930,959].

Each contains precisely one member of every old reduced residue 1,7,11,13,17,19,23,29. Hence the old vector A and every output of the theoretical operators O_p,E_p on it are identical. But actual p-removal in I is {917}, and in J is {931,959}. The second interval has one p^2-divisible site, 931=49*19. Thus delta_p(I)=1-8/7=-1/7, while delta_p(J)=2-8/7=6/7. There can be no function of the old count vector and fixed p alone computing the exact removal for all physical subintervals.

Furthermore for I, n=917=7*131 has source residue 11 and target residue 17. Its actual count 1 exceeds the proposed cap A_11/7=1/7. Therefore the literal assignment i(s,k)=actual raw occupancy and al(s)=old raw count does not satisfy the cap premise in CappedGainSubLE, even for full old-wheel periods. This does not refute Alpöge's theorem: his capacities are auxiliary quantities in an appropriately normalized selected family. It refutes this naive transfer of the theorem.

The obstruction is not a claim that all endpoint-enriched wheel constructions fail, nor a lower bound on the aggregate error. It identifies exactly what an economical native supplier has to recover: the prime-indexed endpoint phase (or a signed aggregate that controls its effect). A new lattice with a chosen diagonal and a p^r quotient is not evidence of that recovery.

Reproduce with node scripts/single_prime_frobenius_orbit_20261125.js. This exact-integer diagnostic compares direct physical enumeration, inverse cofactor enumeration, the fibre rounding identity, the source/destination bound, and the odd/even depth identity. Over primes 2,3,5,7,11,13,17 with old wheels containing all preceding primes, and full square blocks r=p..128: 845 block/prime cases, 4136 prime-power layers, 56342 fibre comparisons, all passed; 2458 strict violations of the naive raw-count cap. The two subintervals above are additional tests. All numbers are safe exact integers in this bounded diagnostic; no assertion of asymptotic uniformity. A finite Lean counterexample is submitted in the existing research module; hosted verification pending.

### 6.4 Revised single-prime quantitative assignment

The next supplier is a same-frame recovery/payment for the signed endpoint phase, not another wheel identity or a copy of the upstream geometric definitions.

1. WHEEL/LEAN: formalize exact T_p, the two geometric resolvents, the independent sheet/exponent label, the restricted p^k transport and the quotient/remainder boundary identity. Produce the explicit correspondence of the unramified upstream host action in an enriched native residue coordinate, with ramified exceptions separated. Verify the finite old-count collision. Do not import the terminal RH proof.
2. OWNER: trace the actual supplier of g0/gU and the min-cap hypotheses to the original selected orbit, its degree budget dl and tauP/ioP. Construct a physical readout whose recovered quantities satisfy a proved cap (or a new inequality with an explicit paid rounding term). The same physical interval, weights, lift and competing sites must appear in the signed ask and the rank/depth proof. Retain all exclusions and the partner-sheet normalization.
3. CENSUS: compute phase errors d*epsilon-r and source/destination mismatch, grouped by p, k, t, and square block. Keep the signed sum, not only the counts of cap failures. Check near-empty fibres, odd order orbits, p^2 layers and shared targets. Do not infer uniform bounds from the diagnostic.
4. ANALYTIC: connect the paid phase residual to the exact attenuated defects of section 2, and to K_N (not raw D_N), including p=2, other exceptional primes, semiprime high owners, and the proper-power payment exactly once. Keep the original square-clock quantifiers.
5. REFEREE/COORDINATOR: require separate proofs of the physical analogue of GainBoundAt (signed ask minus allowances bounded by recoverable gain minus expenditure) and admG1 (actual recovery rank/depth/quotient length at a paid cost), or a demonstrably sufficient native replacement for those two inequalities. Neither a CRT full-fibre rank nor the resolvent identity discharges either. Follow upstream supplying proof dependencies if a native inequality fails. Report the first precise missing inequality and a counterexample if available.

Finish only by proving the centered aggregate lower bound in section 2 and feeding the existing native square-clock consumer. The V2 directive does not retask or launch external agent runtimes; it specifies the work in this PR. All actual new mathematical proofs need hosted verification and semantic review.

## 7. V3 — physical weighted recovery replaces naive independent rank

See [the V3 physical recovery proof, exact signed ledger, paid deep tail and seven-role directive](RHLEAN_SINGLE_PRIME_PHYSICAL_RECOVERY_20261125.md). The direct product-rank transplant is refuted on actual physical sites. The new weighted ancestor cap and unconditional all-prime deep-power tail are paper proofs with submitted Lean sublemmas and reproduced all-prime diagnostics; the centered shallow signed comparison is explicitly still open. V3 supersedes V2's instruction to seek the naive independent-rank analogue, while preserving the source correspondence and V1 terminal target.

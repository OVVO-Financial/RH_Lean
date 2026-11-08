# Adversarial Referee - 2026-11-08

## Early Checkpoint - 20261108-referee-1

Invocation: scheduled 2026-11-08 04:13:01 EST (America/New_York).
Execution=IN_PROGRESS; mathematical result=PENDING; publication requires commit/readback.
Platform run identifier: RUN_ID_UNAVAILABLE.

### A. Current Finding
No new mathematical conclusion is claimed at this checkpoint. Selected work is independent review of 20261108-wheel-1/SP1-SP4 and 20261108-census-1/TC1-TC4 on the original CORR4 moving daughter samples, plus an attempt to strengthen the geometric consumer without assuming signed cancellation.

### B. Authority And Baseline
Actual main: bf4af1cd18aff7c3944a75991aa66371c8afc18a.
AGENTS blob: 0a99faf8458809ac772d470d704c5433f373bda8.
CURRENT_PROOF_CONTRACT blob: d1d6fd558ee23927bd9f70ffdc375bafd1dbb67a.
HIGH policy blob: be8168b67584d9d8ebbaa732a30c51509137543e.
high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1;
chain_ack=CANCELLATION_CHAIN_REUSE_V1;
baseline_ack=PAID_BASELINE_EXACT_CONSUMER_V1;
deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1.

Canonical actual-prime VF/von Koch remains OPEN. The common complete object is M(R^2-1)=L_R+H_R with fixed-Lambda LOW bounded by (floor Lambda+1)R. Human-merged #1107 supplies the same-source boundary b_base=7/8-m/4, m=actualSlotMinimum(D)>0. The original terminal source was retrieved; relevant exact-head CI/dependency verification is in progress, not yet claimed as newly checked. No numerical value of m, optimum boundary, fixed no-loss endpoint without epsilon spending, or new gain is asserted.

### C. Continuity And Source
Reports snapshot: 17d0f4b9454ec6e772a3a7cc12c5a9ca7ddc4abd.
November 7 reports for all seven roles were retrieved, including the latest Coordinator WS, Owner JT, Analytic BC, Wheel OC, Census RC, Referee TF and Lean #1107 handoffs.
November 8 Owner PD, Analytic MP, Wheel SP and Census TC are available.
November 8 Coordinator and Lean: TODAY=PENDING; YESTERDAY=CARRY_FORWARD. Their scheduled completion is not assumed.
Own November 8 report was absent from the retrieved complete tree.
External inbox blob 038018145c0fddb2f6306c0712373adf9cd1ea52 has no entry newer than October 18. Its source/boundary/denominator safeguards remain; historical routing is superseded.

Exact selected carrier:
Y(R,q)=floor((R^2-1)/q^2), q odd prime, q^2<R, R>=56.
Events are pairs (R,q); equal Y does not erase physical multiplicity.
Complete bill B_R=G_R^2+2G_R U_R-2E_R-Hdiag_R, retaining the full ray/tail complement and negative squares once only.
Prospective consumer: Corr4PowerMixedTailBill -> mertensPowerBound_of_corr4MixedTailBill.
No sampled-energy or full-bill gain has been assumed.

Open PR discovery: #1108, non-draft, head a0c986c0343a56e98b7344268fdc0b74aa885cdb; not merged authority. #1097 and #1107 are verified human-merged metadata; CI review follows.
Review method: upstream statements and proofs have been read; subsequent reconstruction is independent checking, not a blind/claim-first review.

### D-O. Work Pending
Independent derivation, exact finite reproduction, obstruction scope, strongest repair, specialist handoffs and the final resume capsule will be appended in this same invocation.
No Lean execution, proof-source edit, other-report write, branch/PR mutation, main write, schedule change or agent launch is authorized or performed.

---

## Dyadic Ray Repair And Transition Review - 20261108-referee-1

This synthesis completes the scheduled invocation begun 2026-11-08 04:13:01 EST. It is not an additional run. The early checkpoint is preserved above. Research status at assembly: RESEARCH_FINISHED / PUBLICATION_PENDING. No new endpoint gain or Lean theorem is claimed.

### A. Most Important Mathematical Finding

**Repeated divisible-root samples are controllable on the actual dyadic root window without declaring them independent or removing them. A corresponding uniform claim over arbitrary finite root sets is false.** This distinction supplies a useful replacement for mask erasure and avoids turning a genuine exceptional population into a universal obstruction.

For the original daughter cutoff Y(R,q)=floor((R^2-1)/q^2), with q an odd prime and q^2<R, call an event a ray event when q divides R. On every finite I contained in [H,2H), the reciprocal ray sampling matrix satisfies

```text
||A_ray||_(2->2)^2 <= C_dyad < 12/5,
C_dyad = sum_(p,r odd primes, 1/2<p/r<2) 1/(p*r).
```

The constant is independent of H, the selected prime cutoff Q, the number of events, and the input vector. Its convergence follows from a binomial-coefficient prime count, not PNT or a hypothesis about Mobius cancellation. The explicit rational certificate below proves the displayed nonoptimal 12/5 bound. On the doubled-cube range Q^3<=4H, combining this with the independently accepted Census off-ray result gives a uniform image-energy estimate for ALL small-prime samples, including rays. The actual mixed output is retained; disjoint input columns do not imply orthogonal arithmetic outputs.

In contrast, for unrestricted finite I in the half-line R>=H, the supremal ray operator norm is exactly sum_(3<=p<=Q, p prime)1/p. This grows without bound with Q. A finite full-matrix counterexample uses 49 genuine roots, 62 nonzero input coordinates, H=512096 and Q=127. Its squared norm ratio is 1568/6975, strictly larger than the proposed mask-erased coefficient, which is less than 1779/8128. These are genuine integer events with a deliberately specified arbitrary test vector, NOT measured Mertens values. They refute the arbitrary-vector strengthening, not a genuine-Mobius estimate or the original masked theorem.

New claim IDs: **20261108-referee-1/DR1-DR4**. Evidence: PAPER_PROOF / SELF_AUDIT, with FINITE_COMPUTATION for the certificates and regressions; independent acceptance and Lean formalization of these new claims remain PENDING. Upstream SP/TC claims receive independent scoped verdicts in D. NEW_VERIFIED_ENDPOINT_GAIN=NONE; net_endpoint_gain=UNKNOWN. The inherited #1107 improvement is not recounted as today's discovery, and its programme-level independent-review gate is not changed by this CORR4 review.

### B. Current Authoritative Objective

Actual main at intake and prepublication refresh: **bf4af1cd18aff7c3944a75991aa66371c8afc18a**, tree aa6a5053535dff7f9fcd4abbaac790791e191fe9. AGENTS blob 0a99faf8458809ac772d470d704c5433f373bda8; CURRENT_PROOF_CONTRACT blob d1d6fd558ee23927bd9f70ffdc375bafd1dbb67a. The full immutable source ledger follows the report.

The canonical actual-prime objective remains

```text
exists C>=0, forall integer R>=2,
  |pi(R^2)-vfCanonical(R^2)| <= C*R*log R,
vfCanonical = vfMid + sqrt(2).
```

It is OPEN. The formal classical von Koch criterion is not silently discharged. For fixed Lambda>=0, the current common object is M(R^2-1)=L_R+H_R with the original absolute birth-height definition, both orientations, and |L_R|<=(floor Lambda+1)R. These definitions were inspected in CanonicalHighSectorCore, CanonicalLowOccupancy and CanonicalHighSectorBridge. CORR4 daughter labels are a different coordinate, not a replacement definition of HIGH.

The strongest consumed same-source main envelope is `native_mertens_true_physical_slot_minimum_total_mass`: there exists one fixed original fine source D with m=actualSlotMinimum(D)>0 and every-positive-loss boundary **b_base=7/8-m/4**. The source-general theorem retains its fineness hypothesis; the terminal existential theorem constructs a source and has no assumed Mertens bound. The fixed-power companion spends m/8 and yields 7/8-m/8. The older same-source 7/8-m/24 is weaker. No numerical m, equality with the optimal boundary, attained infimum over sources, or scale-dependent choice of D is asserted.

Exact #1107 head cd8f98fd6ed2dee3fa08f526eb8ac86c94549da5 passed run 42437401175. Job 128599096276 was actually fetched: four terminal live audits report only propext, Classical.choice, Quot.sound, with closure counts 35352, 35731, 35732 and 35746. The tested-head-to-main comparison changes only the separately merged prime-admission/amplification files, root export, audit/workflow and notes, not the consumed OAI module closure. Human merge occurred at 2026-11-08T03:26:45Z. This is reused exact-head evidence for an established supplier, not a new local build or a fresh independent reproof of the entire OAI chain.

Compact HIGH record:

```text
high_attack_ack: COMPLETE_SIGNED_HIGH_ATTACK_V1
chain_ack: CANCELLATION_CHAIN_REUSE_V1
baseline_ack: PAID_BASELINE_EXACT_CONSUMER_V1
deployment_ack: NO_PIGEONHOLING_ROUTE_SELECTOR_V1
route: CORR4 / literal moving daughter prefixes
exact object: full signed mixed-tail bill B_R, defined in E1
input: original strict q^2 mask; SP/TC determinant geometry; native b_base
changed inference: window-local reciprocal ray norm, with rays restored
consumer: sampled image energy inside the full signed CORR4 return
complete endpoint consumer: Corr4PowerMixedTailBill -> MertensPowerBound
first unpaid step: a stronger actual signed bill, not a geometric norm
new endpoint / new Lean evidence: NONE / NONE
```

### C. Highest-Risk Proof Mechanisms

The selected risks are extending off-ray injectivity or its norm coefficient to ray events, extending a window-local estimate to an arbitrary finite collection of roots, dropping a repeated physical occurrence because its cutoff agrees with another, and spending daughter-square credit both in a norm bound and again in the final signed completion.

A different risk is overreaction: failure on unrestricted roots does not disprove a dyadic-window bound. DR2 proves that such a bound is available. Likewise a general arbitrary-vector failure does not refute estimates restricted to the actual Mertens vector. No new arbitrary-vector norm is imposed as a compulsory entrance condition for the programme.

The Coordinator's WS split-HIGH source audit and Analytic's BC generalized-count return remain independent ready work. They have not been rejected, silently assumed, or substituted by today's CORR4 argument.

### D. Claims Reviewed

Review method: the upstream statements and proofs were read during intake; I then reconstructed the determinant, ray classification, matrix bounds and square completion, inspected original definitions and the actual consumer, and executed a separately written exact verifier. This was NOT blind review or an independent rerun of the upstream scripts. Separate execution is not a claim of statistical independence.

| Stable claim | Verdict | Accepted evidence and exact scope |
| --- | --- | --- |
| 20261108-wheel-1/SP1 | ACCEPT | PAPER_PROOF: exact placement, ray iff square-minus-one, and the three forbidden near-square levels, with q>=1 and R>q^2. |
| 20261108-wheel-1/SP2 | ACCEPT | PAPER_PROOF: determinant restriction; injectivity off rays at Q^3<=2H; arbitrary-Q multiplicity ceiling; all original prime and strict masks retained. |
| 20261108-wheel-1/SP3 | ACCEPT_WITH_SCOPE | PAPER_PROOF: stated sampling Gram, exact prime-ratio ray entries and weighted estimates. No orthogonality of actual output values follows. |
| 20261108-wheel-1/SP4 | ACCEPT_WITH_SCOPE | IDENTITY_ONLY for the completed square; PAPER_PROOF for its necessary two-branch alternative. Neither branch is excluded. |
| 20261108-census-1/TC1 | ACCEPT | PAPER_PROOF: Q^3<=4H gives determinant-one double columns, coprime opposite-parity roots, high labels, ray separation and the stated short-window corollary. |
| 20261108-census-1/TC2 | ACCEPT_WITH_SCOPE | PAPER_PROOF: off-ray operator and weighted estimate with min(2*sigma_*,sigma_*+2/Q). This is a norm of the sampling map, not a new bound on its arithmetic input. |
| 20261108-census-1/TC3 | ACCEPT_WITH_SCOPE | IDENTITY_ONLY plus a valid necessary alternative; complete F, A/2, disagreement and daughter defect all retained. |
| 20261108-census-1/TC4 | ACCEPT_WITH_SCOPE | FINITE_COMPUTATION / REFUTED strengthening: doubled-range injectivity fails at (556,11),(657,13). The minimality ordering by largest root was independently reproduced on the declared R>=56 domain. The author's other large-count totals were not rerun. |
| 20261108-referee-1/DR1 | SELF_AUDIT | PAPER_PROOF: exact half-line ray norm; finite full-matrix mask-erasure counterexample; no actual-Mertens refutation. |
| 20261108-referee-1/DR2 | SELF_AUDIT | PAPER_PROOF plus exact finite certificate: uniform dyadic reciprocal ray bound, with no cube restriction on the ray part. |
| 20261108-referee-1/DR3 | SELF_AUDIT | PAPER_PROOF: complete small-prime image-energy transfer, including nonnegative root weights, under Q^3<=4H. |
| 20261108-referee-1/DR4 | SELF_AUDIT | IDENTITY_ONLY for all-column signed completion; explicit baseline-scale and target-equivalence audit. No new exponent. |

The new DR claims are not labelled PROVED_IN_LEAN. The unchanged previously reviewed claims retain their earlier status, not a new review stamp. Owner PD, Analytic MP and the latest WS/BC proofs were consumed as handoffs, not independently accepted in this invocation.

### E. Independent Mathematical Reconstruction

#### E1. Original Arithmetic And Complete Return

For every integer R>=56, write

```text
X_R=R^2-1; S_R={q odd prime: q^2<R}; Y(R,q)=floor(X_R/q^2);
d_(R,q)=M(Y(R,q)); G_R=M(X_R)-M(R-1);
U_R=sum_(q in S_R) d_(R,q)/q; E_R=sum_(q in S_R) d_(R,q)^2;
V0_R=sum_(R<=n<=X_R) mu(n)^2;
Vq_R=sum_(R<=n<=Y(R,q)) mu(n)^2;
Hdiag_R=V0_R+2*sum_(q in S_R) Vq_R/q;
B_R=G_R^2+2*G_R*U_R-2*E_R-Hdiag_R.
```

The original `rawQ2ChildCutoff` is literal natural division, not rounding to a square endpoint. The original `canonicalRoughLowQ2Owners` is exactly the odd-prime strict mask. Set p_R(n)=mu(n)*sum_q 1_(n<=Y(R,q))/q and f_R(n)=mu(n)*1_(R<=n), on 1<=n<=X_R. Their sums are U_R and G_R. The inspected signed cell includes p(n)f(m)+f(n)p(m)+f(n)f(m). Full first-owner reassembly gives

```text
2*lowOwnerPrefixTailMixedRawCellMass(R)
  = G_R^2+2*G_R*U_R-Hdiag_R,
B_R=2*lowOwnerPrefixTailMixedRawCellMass(R)-2*E_R.
```

This follows either by subtracting the diagonal in the all-distinct-site sum, or from the compiled post789 remainder plus prefix-diagonal identity. It retains squareful zeros, mu(1), the historical prefix, both mixed orientations and the physical diagonal. The older reciprocal-prefix quarter-energy is not an additional available credit.

#### E2. Exact Geometry And The Doubled Threshold

Euclidean division gives n*q^2<R^2<=(n+1)*q^2. If n+1=s^2, then R<=qs and R>q^2 implies s>q. If R<=qs-1, then R^2<q^2(s^2-1), a contradiction. Thus n+1 is a square iff q divides R, and then n=(R/q)^2-1. The same placement argument excludes s^2-2, s^2 and s^2+1. The strict active mask is essential.

Two equal cutoffs satisfy

```text
|R*r-S*q|*(R*r+S*q) < q^2*r^2.
```

For q,r<=Q and R,S>=H, q^2*r^2/(q+r)<=Q^3/2. Off-ray reduced fractions are distinct unless the events coincide. Hence Q^3<=2H forces no off-ray collision, including equality. More generally k fractions in one off-ray column have consecutive gaps at least 1/Q^2 and total span less than Q/(2H), so k<=ceil(Q^3/(2H)). This argument is valid on the whole root half-line and is not an arithmetic cancellation statement.

At Q^3<=4H, a nonzero determinant is strictly below two, hence equals one in absolute value. It forces gcd(R,S)=1 and opposite root parity because q,r are odd. Three events would contain two roots of the same parity, so each off-ray column has at most two events. If q<=5Q/8, monotonicity gives

```text
q^2*r^2/(q+r) <= 25*Q^3/104 < Q^3/4 <= H,
```

contradicting the determinant inequality. Thus both colliding labels exceed 5Q/8. Ray and off-ray columns are disjoint by the exact square characterization, without any cube assumption. Different odd prime labels differ by at least two; the determinant equation then yields Q*|S-R|>=2H-1. This proves the stated short-window exclusion Q*(h-1)<2H-1.

For A_o(R,n)=1/q at each off-ray event, its row Gram is diag(sigma_R)+K. Each event has at most one partner, each partner product is less than 4/Q^2, and each row has at most Q/2 odd-prime labels. Thus every row sum of nonnegative symmetric K is at most 2/Q. The inequality 2|xy|<=x^2+y^2 proves its norm bound directly. Row Cauchy-Schwarz and column multiplicity two give the alternative 2*sigma_* coefficient. These reconstruct TC2, including its weighted form by scaling entries by sqrt(alpha_R/beta_n)<=1.

#### E3. DR1: Exact Half-Line Ray Norm And Its Scope

Fix integers H>=1 and Q>=3. Consider all finite row sets I contained in R>=H, all genuine ray events with q<=Q and q^2<R, and arbitrary finitely supported real input z indexed by n. Let W_Q=sum_(3<=p<=Q, p prime)1/p. Then

```text
sup_I ||A_ray(I,Q)||_(2->2) = W_Q.
```

For the upper bound identify a ray column with s via n=s^2-1. For each prime p, the map sending u_s to u_(R/p) on multiples R=ps, with the original s>p mask, is an isometry followed by restrictions and therefore a contraction. The triangle inequality gives norm at most W_Q. This argument establishes an upper bound, not orthogonality between different primes.

For the reverse inequality list the k odd primes <=Q and choose a power of two K>max(H,Q^2). Put z_(s^2-1)=1 for s=K*product_j p_j^(e_j), 0<=e_j<L. Take rows R=K*product_j p_j^(e_j), 1<=e_j<L. Every selected prime is an admitted divisor of each row, every daughter belongs to the chosen input, and each output is exactly W_Q. Unique factorization gives L^k input sites and (L-1)^k rows. Therefore the squared norm ratio is at least (1-1/L)^k*W_Q^2. Let L grow with Q fixed. This proves the asserted supremum, without claiming it is attained by a finite packet.

There is no Q-independent half-line constant: W_Q is unbounded. An elementary proof is that bounded sum_p 1/p would bound product_(p<=Q)(1-1/p)^(-1), since its logarithm is bounded by a constant plus twice that sum. But this Euler product contains every term 1/n for n<=Q and hence dominates the divergent harmonic partial sums. No prime asymptotic or unproved distribution statement is used.

The cube hypothesis does not repair unrestricted roots: for each Q choose H>=Q^3/4 and then K large enough. What changes in the dyadic repair is the ROOT WINDOW, not the source coefficients or a conjectured sign pattern. The test inputs here are arbitrary geometric vectors. This is not an infinite family of failures of a bound asserted only for M(n).

#### E4. DR2: A Uniform Dyadic Ray Bound

Now let I be ANY finite subset of [H,2H), with all original ray masks and any Q. Two ray events sharing a column have R=ps and S=rs. Consequently 1/2<p/r<2. The row sum of the nonnegative symmetric ray Gram is bounded by

```text
C_dyad=sum_(p,r odd primes, 1/2<p/r<2)1/(p*r).
```

This includes the diagonal p=r. At a fixed R and p, the partner row is uniquely S=R*r/p; multiple physical events on the diagonal are summed, not removed. Extending the permitted partners to all comparable odd prime pairs gives the displayed bound. Symmetric row-sum control implies ||A_ray||^2<=C_dyad, by the same elementary quadratic-form argument used for K.

Here is a self-contained convergence and constant proof. Set b_k=sum_(2^k<=p<2^(k+1), p odd prime)1/p, k>=1, and b_0=0. Comparable primes belong to equal or neighboring bins, so

```text
C_dyad <= sum_(k>=1)b_k*(b_(k-1)+b_k+b_(k+1))
        <= 3*sum_(k>=1)b_k^2.
```

For k>=1 put n=2^k. Every prime in (n,2n) divides the integer binomial(2n,n), whose value is less than 4^n. Since each such prime is greater than n, there are fewer than 2n/k of them. Hence b_k<=2/k. The prime endpoints cause no exception: 2^k is not an odd prime. In particular the wholly analytic bound C_dyad<=24 already follows from sum_(k>=1)1/k^2<=2.

The exact rational calculation in the appendix enumerates primes by trial division only through 2047 and proves sum_(k=1..10)b_k^2<2/5. For the remaining bins, sum_(k>=11)b_k^2<=4*sum_(k>=11)1/k^2<=4/10 by integral comparison. Thus

```text
C_dyad < 3*(2/5+4/10)=12/5.
```

The printed decimal 2.391485830852926 is only a display of the sharper finite-plus-tail rational upper bound. The proof and pass condition use Fractions, not that decimal. The finite part does not extrapolate to larger primes: the binomial tail proves the missing uniformity. The constant is deliberately nonoptimal; no literature-priority claim is made for Schur bounds or Chebyshev's binomial argument.

#### E5. DR3: Restore Both Sampling Populations

For H>=56, integers Q>=3 with Q^3<=4H, and finite I contained in [H,2H), let A_Q contain EVERY admitted q<=Q. Let N_Q be its image, A_o its off-ray part, and sigma_*=max_R sum_(off-ray q<=Q)1/q^2, using zero for the empty population. Ray and off-ray COLUMN sets are disjoint, so

```text
A_Q*A_Q^t=A_o*A_o^t+A_ray*A_ray^t;
c_Q=12/5+min(2*sigma_*,sigma_*+2/Q);
sum_(R in I)|sum_(q in S_R,q<=Q)z_(Y(R,q))/q|^2
  <= c_Q*sum_(n in N_Q)|z_n|^2.                         (DR3a)
```

This matrix argument controls the cross term between the actual outputs; it DOES NOT say that U_o(R)U_ray(R)=0. Since sum_(q odd prime)1/q^2<sum_(j>=1)1/((2j+1)^2-1)=1/4, c_Q<=29/10. This last uniform simplification is optional and coarser.

For arbitrary nonnegative root weights alpha_R, set beta_n=max_(events at n)alpha_R. Omit zero-beta columns. Entrywise scaling by sqrt(alpha_R/beta_n)<=1 preserves the preceding nonnegative-matrix norm upper bound. Therefore

```text
sum_R alpha_R*|U_Q(R)|^2
 <= c_Q*sum_(n in N_Q)beta_n*M(n)^2.                    (DR3b)
```

All constants are uniform in H,Q,I,alpha and z in the stated domain. In particular I=[H,H+h), 1<=h<=H, is allowed, including h=1. This is a theorem about daughter sampling, not the canonical HIGH prefix-window criterion.

The improvement is over the growth-bearing generic ray triangle bound W_Q^2 on deduplicated IMAGE energy. It is NOT a stronger replacement for the already available pointwise row frame U_Q(R)^2<=(1/4)*sum_q M(Y)^2 on PHYSICAL occurrence energy. Those right-hand sides differ. The two estimates should be chosen according to the actual consumer, not ranked solely by their constants.

### F. Counterexamples And No-Go Results

The original Census falsifier is reproduced exactly:

```text
(R,q)=(556,11), (S,r)=(657,13), n=2554;
556*13-657*11=1; 13^3<=4*556;
2554*121<556^2<=2555*121;
2554*169<657^2<=2555*169.
```

Both labels are odd primes, both satisfy q^2<R, neither divides its root, and both roots lie in [556,658), h=102. The independent all-event search for 56<=R<=2000 contains every candidate with largest root <=657; under the doubled-cube condition such a candidate has prime labels at most 13. It finds this as the first by largest root. It does not claim an unrestricted minimum outside that stated domain/order.

Two independent Mobius methods give M(2554)=-5. At the parent roots,

```text
M(556^2-1)=165; M(555)=5; G_556=160;
M(657^2-1)=45;  M(656)=-8; G_657=53;
B_556=-42754054126/230945;
B_657=-14830731658/51051.
```

Deleting the second repeated occurrence from U and E, while holding the other source terms fixed, changes B_657 by +1180/13. The local squared reciprocal cross term is 50/143. These are rigorous failures of occurrence deletion, not a universal positive sign assertion about the complete bill.

The new **full-matrix** mask-erasure counterexample is as follows. Set H=512096, Q=127, K=524288=2^19, and

```text
I={K*3^a*5^b: 1<=a,b<=7}.
```

All 49 roots exceed H and Q^2; Q^3=2048383<=4H=2048384. Let z_n=1 on the 62 distinct ray cutoffs reached by q=3 or q=5 in these rows, and zero on all other image columns of the COMPLETE q<=127 matrix. No other odd prime divides these roots; an off-ray column cannot equal one of these square-minus-one columns. Thus every output equals 1/3+1/5=8/15 and

```text
sum_R |(A_Q z)_R|^2 / sum_n |z_n|^2 = 1568/6975.
```

For this complete matrix every row diagonal is sigma_full=sum_(3<=p<=127,p prime)1/p^2. Exact trial division verifies sigma_full<13/64. A putative extension of TC2 obtained by simply removing its off-ray mask would give coefficient at most

```text
sigma_full+2/127 < 1779/8128 < 1568/6975.
```

The certified excess over even the larger rational upper bound is 336179/56692800>0. This refutes that EXACT strengthening on arbitrary finite I in the half-line. It does not refute TC2, which excludes rays, or DR3, which assumes a dyadic window. This packet is deliberately not confined to one dyadic window. It is not asserted to be a vector of actual Mertens values.

Disclosed scope correction during development: an initial Q=31 packet used the RAY-ONLY diagonal and refutes the analogous ray-only coefficient. That diagonal is not the complete matrix diagonal. The verifier retains that diagnostic and separately verifies the Q=127 full-matrix counterexample with every admitted label restored. The smaller test is not misreported as a full-carrier refutation.

DR1's norm theorem supplies an infinite-family obstruction to any Q-uniform arbitrary-vector half-line sampling constant. Its scope does not extend to signed/renormalized methods, fixed-aspect windows, or actual-Mertens-only estimates.

### G. Original-Carrier And Signed Interaction Audit

An event is (R,q); its cutoff n is not its identity. All source coefficients remain mu, 1/q and the literal floor. The ray/off-ray split and q<=Q versus q>Q split partition actual occurrences without duplicated or missing descendants. Squareful zeros remain in the site sum, while a sampled cutoff itself is not required to be squarefree. The historical M(R-1) and every diagonal term remain in G_R and Hdiag_R.

DR3 combines matrix bounds before applying the actual vector, so it does not discard arithmetic ray/off-ray cross terms. It is not a claim of stochastic independence, independent primes, orthogonal Mertens prefixes, or cancellation of Hecke phases. Nothing here is a bridge to the clipped #915 physical source or an identification with Analytic MP's additive short windows.

For a source-exact signed return including rays, let U_Q,E_Q contain all small-prime events and U_tail,E_tail the remaining original labels. Define

```text
F_R^Q=G_R^2+2*G_R*U_tail(R)-2*E_tail(R)-Hdiag_R;
B_R=F_R^Q+2*G_R*U_Q(R)-2*E_Q(R).
```

For each complete small-prime column n, let w_n=sum_(events at n)alpha_R, t_(R,q)=G_R/q, and tbar_n=sum alpha_R*t_(R,q)/w_n. Omit zero-weight columns. Put

```text
A=sum_(small events)alpha_R*t_(R,q)^2;
P=(1/2)*sum_n sum_(events at n)alpha_R*(t_(R,q)-tbar_n)^2;
D=sum_n w_n*(M(n)-tbar_n/2)^2.
```

Then the exact DR4 restoration is

```text
sum_R alpha_R*B_R=sum_R alpha_R*F_R^Q+A/2-P-2D.
```

This algebra works for arbitrary column multiplicity, not only double columns and not only the cube range. On a ray n=s^2-1 its parent targets are exactly G_(qs)/q for the admitted primes q with qs in I and q<s. Nonnegative disagreement among those actual targets is retained. No negative square was spent before this identity. This is an extension of the already accepted column completion to the full selected source, not a new claim to have bounded the defect or complement.

### H. Quantifier And Circularity Audit

DR1 fixes Q and then takes a supremum over finite sets whose largest root may grow arbitrarily; its constant depends on Q. DR2 requires a fixed-aspect root window but allows Q to grow. DR3 additionally requires Q^3<=4H, uniformly in shorter windows and root weights. None of these changes of quantifier is implicit. Growing Lambda or dropping h=1 in the canonical HIGH criterion is not licensed.

Under the inherited Mertens bound at every positive loss, |G_R| is at most a constant times R^(2*b_base+epsilon). Merely substituting this envelope into the completed bill or the new sampling bound does not lower that exponent. The full consumer asks for B_R<=A*R^(4*b_new) for every R>=56, b_new>=1/2. A fixed b_new<b_base would give a genuine improvement through the inspected Lean gate; no such estimate is proved here.

The whole-bill assumption is target-equivalent at a fixed power, rather than an independently supplied sampling lemma. The forward implication is the actual `mertensPowerBound_of_corr4MixedTailBill`. For the reverse implication suppose |M(n)|<=C*n^b, b>=1/2, C>=0. Then |G_R|<=2C*R^(2b). With sigma=sum_q1/q^2<1/4, row Cauchy gives U_R^2<=sigma*E_R and

```text
2*G_R*U_R-2*E_R <= (sigma/2)*G_R^2 <= G_R^2/8;
B_R <= (9/8)*G_R^2 <= (9/2)*C^2*R^(4b).
```

The first inequality is the maximum of 2*|G|*sqrt(sigma*E)-2E, or follows by completing a square. If sigma=0, U=0 and the same conclusion is immediate. Thus existence of the fixed-power complete bill is equivalent to the fixed-power Mertens bound within this domain. This scope is carried forward and independently checked, not advertised as a newly solved input. No necessity is claimed for a smaller separate component estimate.

For comparison with an every-positive-loss baseline, a new statement B_R=O_epsilon(R^(4*(b_base-eta)+epsilon)) would, at epsilon=2*eta, supply fixed power b_base-eta/2. The required positive eta is absent from today's geometric theorem. The final partial-square cost O(R) and fixed-Lambda canonical LOW are also retained in any eventual HIGH transfer.

### I. Strongest Surviving Repair

Keep SP and TC at their original hypotheses. Do not erase the ray mask while preserving the off-ray coefficient. Use DR2 on rays within the actual dyadic window, TC2 on off-rays where Q^3<=4H, and DR3 only when an image-energy estimate is the intended consumer. This removes a possible growing W_Q^2 loss without claiming to improve the stronger physical-occurrence row frame.

Apply the actual arithmetic vector only after proving its needed image-energy or joint signed estimate. If that estimate is not available, retain the exact DR4 identity with F_R^Q, all column means, and all negative credit. A hypothetical failure then has the same two alternatives as TC3: either the restored complement exceeds half the target, or A exceeds the target and P+2D is smaller than half the excess. Neither alternative is ruled out by geometry alone.

### J. Competing Proof-Strategy Assessment

CORR4 now has accepted transition geometry and a proposed dyadic all-small-prime sampling interface. This is a justified continuation of WS-CORR4-MOVING, not a competing proof of the endpoint. The half-line obstruction does not retire the route, and the dyadic repair does not make it the unique route.

Owner PD concerns primitive cofactor ratios with actual prime-error weights, not squared daughter cutoffs. Analytic MP concerns genuine additive short windows, not prefix values along these images. Their required transfers have not been established here. Their inverse/component findings remain pending their own independent review. MU-LIFT OC's physical donor capacity restrictions and the released-bank repair also retain their separate carrier and scope.

Keep OAI WS/BC work, NYMAN full-basis work, FINITE-AC and the other protected routes active. The new baseline #1107 is paid input; neither it nor an unmerged #1108 can be counted again as a newly discovered DR gain. No schedule, portfolio coverage clock or human-merge policy is altered.

### K. Original Research And Executed Tests

The new work went beyond reviewing SP/TC: it derived the exact half-line ray norm, constructed a valid full-matrix falsifier with the true diagonal, proved a different dyadic bound from comparable prime pairs, and restored rays through a weighted image-energy estimate and the complete signed column identity.

The independent verifier uses Python arbitrary-precision integers and Fraction throughout. Its only floating conversion prints the nonbinding decimal bound. Exact coverage:

- All 17,665 admitted events with 56<=R<=2000; 1,047 repeated cube-range pairs and 13 doubled-range off-ray collision pairs.
- Forward and inverse placement populations agree in six declared windows, including Q^3=2H and Q^3=4H boundaries and the minimal witness window.
- Forty-eight deterministic rational-vector off-ray checks and forty-eight complete weighted checks, with exact Gram row sums and masks.
- Mobius sieve through 431648, trial-factor agreement at every n<=10000, and separate trial-factor summation of M(2554).
- Exact B values, deletion change and disagreement penalty for the two original witness roots.
- Two all-column signed completion tests, retaining rays, tails, physical diagonal and nonconstant rational weights; both residuals are exactly zero.
- The Q=31 ray-only diagnostic, the corrected Q=127 full-matrix falsifier, and an exact small-prime-plus-proved-tail certificate for C_dyad<12/5.

The code was written separately from the upstream appendices. The six window tests and new packet were selected for this review; they are not described as preregistered blind experiments or a rerun of Census's 800,309-event census. The proofs, not the finite tests, supply the all-scale statements. No numerical exponent fit or asymptotic inference from measured signs is made.

Verifier SHA-256: **83a0cc8927938e491070f7604c2ee92e07374a96501228a08b75b5dd366a6db7**. The complete 268-line source and captured final output are embedded below for reproduction. The hash is of the code bytes alone, including its terminal newline.

### L. Formalization Guidance

One implementation-sized accepted task, if an active consumer needs it: formalize TC1's doubled-cube determinant/parity/high-label theorem and TC2's weighted off-ray norm, reusing #1097's literal cutoff and strict mask. Preserve the half-line versus window quantifiers and treat the weighted matrix scaling explicitly. This is accepted supporting mathematics, not a target-assuming endpoint wrapper.

A second, conditional task is review-first: independently check DR2's dyadic ray Schur proof and its prime-bin certificate, then integrate DR3 only if a named image-energy consumer needs it. DR claims are this author's new paper proofs and do not yet have independent acceptance. No new proof branch, Lean source edit, CI dispatch, or agent launch was performed or requested through a tool. Do not formalize the refuted mask-erased coefficient.

### M. Specialist Handoffs

- Proof Architect: record SP1-SP2 and TC1 as accepted paper geometry, SP3-SP4/TC2-TC4 with the scopes above; DR1-DR4 are new self-audited paper work. The exact root-window hypothesis resolves the apparent ray obstruction. Keep the complete bill as the unpaid endpoint, not the norm interface.
- Finite Wheel: use the all-column DR4 completion to retain the ray targets G_(qs)/q and their actual disagreements. Determine whether a source-specific joint inequality can exploit them together with the full complement. Do not repeat the endpoint-injectivity census or reset protected rotation.
- Prime Census: the minimal collision and signed values were independently reproduced. A useful next discriminator is an ACTUAL-Mertens test of a precisely proposed ray-target alignment estimate, including the complement branch; the arbitrary-vector packet above is not such a test.
- Analytic Type II: no MP-to-daughter transfer is claimed. If an existing estimate controls the weighted image sum in DR3b, specify its exact endpoint set and weights; otherwise retain this as a missing source transfer, not a reason to reject MP or invent a Hecke identification. Continue the due protected route and the pending BC/WS work separately.
- Owner Payment: the prime-ratio relation in ray columns is an exact sampling incidence, not your primitive-cofactor prime-error graph. Shared vocabulary gives no signed covariance transfer. PD claims remain at their original pending-review scope.
- Lean Verification: consume the accepted SP/TC scope if it has an active consumer. DR2/DR3 require a genuinely independent mathematical check before implementation. #1107's exact-head proof evidence is confirmed and remains inherited; #1108 is still unmerged at the observed head.

These are asynchronous report handoffs, not claims that another agent has executed or will execute outside its configured schedule.

### N. First Independently Missing Mathematical Ingredient

The missing content is a new inequality for the ACTUAL signed parent/daughter source, including its complement, at a power beating b_base. Neither a reciprocal sampling norm nor injectivity supplies the sizes/signs of M(n), G_R or the restored F_R^Q. The full bill is target-equivalent, as H verifies, so renaming it is not a smaller independent theorem.

The concrete next research question is whether the dyadic ray restriction 1/2<p/r<2 imposes a useful quantitative condition on the actual joint values G_(ps)/p and M(s^2-1), AFTER retaining all off-ray and q>Q pieces. A proposed bound should be tested at h=1 as well as full windows and against the exact DR4 identity. At present no independent estimate excludes its two failure alternatives. This limitation does not invalidate the accepted sampling theorem, and it is not a no-go for a joint signed method.

### O. Continuity, Evidence And Resume Capsule

The intake report snapshot was agent-reports@17d0f4b9454ec6e772a3a7cc12c5a9ca7ddc4abd. November 7 reports from all seven roles and available November 8 Owner/Analytic/Wheel/Census reports were retrieved. The Coordinator AM/PM files have identical November 7 blob SHAs. At the prepublication directory refresh, November 8 Coordinator and Lean were still absent: **TODAY=PENDING; YESTERDAY=CARRY_FORWARD**. Their completion was not inferred from the clock. Upstream November 8 report blobs were unchanged.

Continuity preserved: Coordinator 20261107-coordinator-2309/WS and OPEN-WS-BULK; Owner 20261107-owner-3/JT and 20261108-owner-1/PD; Analytic 20261107-analytic-3/BC and 20261108-analytic-1/MP; Wheel 20261107-wheel-3/OC and 20261108-wheel-1/SP; Census 20261107-census-2/RC and 20261108-census-1/TC; own 20261107-referee-3/TF and prior scoped RG acceptance; Lean 20261107-lean-3/#1107. Only the selected SP/TC claims received new independent mathematical review here. Historical draft/unmerged wording is superseded by the checked current PR metadata, not by rewriting earlier reports.

External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 has no post-October-18 entry. EXT-20261018-PNT-1..3, EXT-20261017-XCOORD-1 and EXT-20261014-5 retain their actual-prime, boundary, anchor and original-denominator qualifications. They are not imported as suppliers for DR. No unchanged historical no-go or large scan was rerun as new progress.

Formal metadata actually checked: #1097 is merged, head bc727dc9f7dd655fdd2addc943b246ad70ef576d, run 42203731194 successful; job 127845057234 contains the exact nine sampling declarations and standard-axiom/no-shortcut audit. #1107 is merged at current main with the terminal evidence in B. #1108 is open/non-draft at a0c986c0343a56e98b7344268fdc0b74aa885cdb; run 42451075330 is completed/success at that head. Its terminal logs and source chain were NOT independently reviewed in this run, so no new formal endorsement of that PR is asserted.

No local Lean/Lake was executed. No proof source, shared instruction, other report, branch, issue, PR, workflow, permission or schedule was changed. Only the own dated report is published remotely. GitHub source/log retrieval and local exact computations succeeded. New DR mathematics remains unformalized and pending independent review; the canonical VF objective, a new complete HIGH gain, and RH remain OPEN.

Resume from DR3b/DR4 and the actual ray-column targets, not from another scan of the same cutoffs. Preserve the two counterexample domains, the complete-matrix diagonal correction, source/report blob ledgers and verifier hash. A next reviewer should first check DR2's prime-bin proof and then ask which actual arithmetic consumer would benefit from its image-energy bound. Until such a consumer improves the complete budget, report no new endpoint gain.

Publication evidence: the early checkpoint was committed as f18fd877ed64d270cfef6590f9eb14c2b2c15ad8 and read back byte-for-byte at blob 2c5b49b6940d9e34d68bdb6a9277632dc4cf3ad2. A fresh prewrite fetch matched it. The final commit/readback receipt is appended only after those operations succeed; this text does not presume their success.


### Immutable Source Ledger

All main paths below were actually retrieved at bf4af1cd18aff7c3944a75991aa66371c8afc18a. Source bytes and proof evidence are distinct. Sampling source e823a1a124dc1bfe4c38d4af4ee10c1e481cad2a was also retrieved at its tested PR head and matches current main byte-for-byte.

| Main source | Blob SHA |
| --- | --- |
| [AGENTS.md](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/AGENTS.md) | 0a99faf8458809ac772d470d704c5433f373bda8 |
| [CURRENT_PROOF_CONTRACT.md](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/CURRENT_PROOF_CONTRACT.md) | d1d6fd558ee23927bd9f70ffdc375bafd1dbb67a |
| [docs/RHLEAN_COMPLETE_SIGNED_HIGH_ATTACK_20261107.md](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/docs/RHLEAN_COMPLETE_SIGNED_HIGH_ATTACK_20261107.md) | be8168b67584d9d8ebbaa732a30c51509137543e |
| [docs/RHLEAN_REUSE_CANCELLATION_CHAIN_20261107.md](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/docs/RHLEAN_REUSE_CANCELLATION_CHAIN_20261107.md) | 28e2ab47c68bc83b91ae02b6112b94867b021b32 |
| [docs/RHLEAN_PAID_BASELINE_EXACT_CONSUMER_20261106.md](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/docs/RHLEAN_PAID_BASELINE_EXACT_CONSUMER_20261106.md) | 13d58dd12d90fbf1160812c7c93442dc5d0576ac |
| [docs/RHLEAN_INDEPENDENT_MULTIFRONT_NO_PIGEONHOLING_20261104.md](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/docs/RHLEAN_INDEPENDENT_MULTIFRONT_NO_PIGEONHOLING_20261104.md) | 6ff6eb30b91705af5478d3705849234260f8a7a3 |
| [docs/RHLEAN_NATIVE_SQUARE_CLOCK_AGENT_DIRECTIVE_20261029.md](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/docs/RHLEAN_NATIVE_SQUARE_CLOCK_AGENT_DIRECTIVE_20261029.md) | a0198ff1877de2a0ce164ff5a21768583c7a144a |
| [docs/RHLEAN_ALL_VECTOR_AGENT_PROMPTS_20261030.md](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/docs/RHLEAN_ALL_VECTOR_AGENT_PROMPTS_20261030.md) | 151283a82eb699f734b80e67dcee7b24a90d1e1d |
| [docs/RHLEAN_SOURCE_FAITHFUL_COMPLETE_RETURN_AGENT_CONTRACT_20261031.md](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/docs/RHLEAN_SOURCE_FAITHFUL_COMPLETE_RETURN_AGENT_CONTRACT_20261031.md) | 4775ee5fd95f279beab08a75d1e17127078b19a6 |
| [docs/RHLEAN_SEVEN_AGENT_RESEARCH_ENGINE_20261101.md](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/docs/RHLEAN_SEVEN_AGENT_RESEARCH_ENGINE_20261101.md) | 3f4e594c6af26e57ba0800b2a1ec81effb71db13 |
| [docs/RHLEAN_BROAD_SEARCH_UNTIL_ETA_20261031.md](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/docs/RHLEAN_BROAD_SEARCH_UNTIL_ETA_20261031.md) | 469caefcd2d82f8d59044f67c78c89ebbe613ac7 |
| [docs/DYNAMIC_RESEARCH_AGENTS.md](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/docs/DYNAMIC_RESEARCH_AGENTS.md) | dd99f8d6fff199c9cad363a4ea8d9e721079c4bb |
| [RHLean/Analysis/CanonicalHighSectorCore.lean](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/RHLean/Analysis/CanonicalHighSectorCore.lean) | dd02fc8fabfe4004c6b0d50374b3b8752607b168 |
| [RHLean/Analysis/CanonicalLowOccupancy.lean](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/RHLean/Analysis/CanonicalLowOccupancy.lean) | b958da340d107cdd00015d2827b9a728357b4d8e |
| [RHLean/Analysis/CanonicalHighSectorBridge.lean](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/RHLean/Analysis/CanonicalHighSectorBridge.lean) | c8e59235a138413257552bbe9b9207fc8ff243ff |
| [RHLean/Proof/SignedTransportAmplificationAudit.lean](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/RHLean/Proof/SignedTransportAmplificationAudit.lean) | 746f35f126f36e024d39e38c92dde30aabca266b |
| [research/CANONICAL_ROUGH_Q2_TAIL_REDUCTION.lean](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/research/CANONICAL_ROUGH_Q2_TAIL_REDUCTION.lean) | ebca096e83009a7df514d00b6a2696be86a94c55 |
| [research/CORR4_SQUARE_CLOCK_SAMPLING_20261106.lean](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/research/CORR4_SQUARE_CLOCK_SAMPLING_20261106.lean) | e823a1a124dc1bfe4c38d4af4ee10c1e481cad2a |
| [research/CORR4_OAI_POWER_MIXED_TAIL_GATE_20261025.lean](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/research/CORR4_OAI_POWER_MIXED_TAIL_GATE_20261025.lean) | bb0ee1252e7ba10c44ae5b8d827573d6c581b73a |
| [research/GLOBAL_RETURNED_CORE_WEIGHTED_MOBIUS_COORDINATE.lean](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/research/GLOBAL_RETURNED_CORE_WEIGHTED_MOBIUS_COORDINATE.lean) | f0e2e672a1ed369d1dc6dacbe9024c65e986a3c8 |
| [research/GLOBAL_RETURNED_CORE_RECIPROCAL_PREFIX_SIGNED_CELL_SPLIT.lean](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/research/GLOBAL_RETURNED_CORE_RECIPROCAL_PREFIX_SIGNED_CELL_SPLIT.lean) | 29bb263ddd07b12a2dd5ccf6a12aecaf627134d8 |
| [research/GLOBAL_RETURNED_CORE_RECIPROCAL_PREFIX_FIRST_OWNER_ENERGY.lean](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/research/GLOBAL_RETURNED_CORE_RECIPROCAL_PREFIX_FIRST_OWNER_ENERGY.lean) | ac8015a1dd87aea23d35d57f5102efd38f4a105b |
| [research/GLOBAL_RETURNED_CORE_PREFIX_TAIL_MIXED_REMAINDER_IDENTITY.lean](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/research/GLOBAL_RETURNED_CORE_PREFIX_TAIL_MIXED_REMAINDER_IDENTITY.lean) | d17aeb639bb47d79333cf0d00760c2604feddfdf |
| [research/GLOBAL_RETURNED_CORE_POST789_DIAGONAL_SUBTRACTED_CONTROL.lean](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/research/GLOBAL_RETURNED_CORE_POST789_DIAGONAL_SUBTRACTED_CONTROL.lean) | ba95beda901719afaabca9011b8dbae6fc69662d |
| [research/oai_434/VF919TotalMassEndpoint.lean](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/research/oai_434/VF919TotalMassEndpoint.lean) | 827bb952c4d4311d75fd03a2470799dc10b0f7e7 |

### Research Continuity Ledger

Snapshot: 17d0f4b9454ec6e772a3a7cc12c5a9ca7ddc4abd. Only relevant sections were mathematically reviewed; retrieval is not blanket endorsement. November 7 Coordinator AM and PM share the same blob; the AM text was read once.

| Report path | Blob SHA |
| --- | --- |
| [research/agent_reports/2026-11-07/00-coordinator-am.md](https://github.com/OVVO-Financial/RH_Lean/blob/17d0f4b9454ec6e772a3a7cc12c5a9ca7ddc4abd/research/agent_reports/2026-11-07/00-coordinator-am.md) | 00a649b70f851ca193e74e5004d0d3390cf9ca18 |
| [research/agent_reports/2026-11-07/10-owner-payment.md](https://github.com/OVVO-Financial/RH_Lean/blob/17d0f4b9454ec6e772a3a7cc12c5a9ca7ddc4abd/research/agent_reports/2026-11-07/10-owner-payment.md) | 933e8eb23e669594cc687059d75147e6267eec8d |
| [research/agent_reports/2026-11-07/20-analytic-type-ii.md](https://github.com/OVVO-Financial/RH_Lean/blob/17d0f4b9454ec6e772a3a7cc12c5a9ca7ddc4abd/research/agent_reports/2026-11-07/20-analytic-type-ii.md) | 77f3e5795533041e4356ceb94cb66328da7af27c |
| [research/agent_reports/2026-11-07/30-finite-wheel.md](https://github.com/OVVO-Financial/RH_Lean/blob/17d0f4b9454ec6e772a3a7cc12c5a9ca7ddc4abd/research/agent_reports/2026-11-07/30-finite-wheel.md) | 7739fa5d4cc77f35773b0d4149b2ddd21732a70d |
| [research/agent_reports/2026-11-07/40-prime-census.md](https://github.com/OVVO-Financial/RH_Lean/blob/17d0f4b9454ec6e772a3a7cc12c5a9ca7ddc4abd/research/agent_reports/2026-11-07/40-prime-census.md) | 3fae830e34c590d32c31ad77cad3ace833eb3ff5 |
| [research/agent_reports/2026-11-07/50-adversarial-referee.md](https://github.com/OVVO-Financial/RH_Lean/blob/17d0f4b9454ec6e772a3a7cc12c5a9ca7ddc4abd/research/agent_reports/2026-11-07/50-adversarial-referee.md) | 426c2abfa5b8926b512e07f05be37692a2416d0b |
| [research/agent_reports/2026-11-07/60-lean-verification.md](https://github.com/OVVO-Financial/RH_Lean/blob/17d0f4b9454ec6e772a3a7cc12c5a9ca7ddc4abd/research/agent_reports/2026-11-07/60-lean-verification.md) | ec14e2803af8c1e56123682ee61ed927ed4f9450 |
| [research/agent_reports/2026-11-07/90-coordinator-pm.md](https://github.com/OVVO-Financial/RH_Lean/blob/17d0f4b9454ec6e772a3a7cc12c5a9ca7ddc4abd/research/agent_reports/2026-11-07/90-coordinator-pm.md) | 00a649b70f851ca193e74e5004d0d3390cf9ca18 |
| [research/agent_reports/2026-11-08/10-owner-payment.md](https://github.com/OVVO-Financial/RH_Lean/blob/17d0f4b9454ec6e772a3a7cc12c5a9ca7ddc4abd/research/agent_reports/2026-11-08/10-owner-payment.md) | 79dd00b2c26491ab302ea17d6dbe4e0146d57a97 |
| [research/agent_reports/2026-11-08/20-analytic-type-ii.md](https://github.com/OVVO-Financial/RH_Lean/blob/17d0f4b9454ec6e772a3a7cc12c5a9ca7ddc4abd/research/agent_reports/2026-11-08/20-analytic-type-ii.md) | b32aa501bff08a8da7ecf387f4e9a168f71ea3e5 |
| [research/agent_reports/2026-11-08/30-finite-wheel.md](https://github.com/OVVO-Financial/RH_Lean/blob/17d0f4b9454ec6e772a3a7cc12c5a9ca7ddc4abd/research/agent_reports/2026-11-08/30-finite-wheel.md) | 5b56caa1e7b3463510a7257b10a784ccc8798621 |
| [research/agent_reports/2026-11-08/40-prime-census.md](https://github.com/OVVO-Financial/RH_Lean/blob/17d0f4b9454ec6e772a3a7cc12c5a9ca7ddc4abd/research/agent_reports/2026-11-08/40-prime-census.md) | 3cc1bbe7e0d9a80bdcaa630a2fb3c31d4b8f90c8 |
| [research/agent_reports/EXTERNAL_HANDOFFS.md](https://github.com/OVVO-Financial/RH_Lean/blob/17d0f4b9454ec6e772a3a7cc12c5a9ca7ddc4abd/research/agent_reports/EXTERNAL_HANDOFFS.md) | 038018145c0fddb2f6306c0712373adf9cd1ea52 |

### Reproducibility Appendix

The following independently written verifier was executed to successful completion. It requires only Python's standard library. It does not execute Lean or fetch any external data.

```python
"""Exact independent CORR4 checks for the 2026-11-08 referee report."""

from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations
from math import gcd, isqrt


def primes_to(n):
    return [p for p in range(3, n + 1, 2)
            if all(p % d for d in range(2, isqrt(p) + 1))]


def mobius_trial(n):
    count = 0
    for p in range(2, isqrt(n) + 1):
        if n % p == 0:
            n //= p
            count += 1
            if n % p == 0:
                return 0
            while n % p == 0:
                n //= p
    return -1 if (count + (n > 1)) % 2 else 1


def mobius_sieve(n):
    mu = [1] * (n + 1)
    mu[0] = 0
    prime = [True] * (n + 1)
    for p in range(2, n + 1):
        if not prime[p]:
            continue
        for j in range(p, n + 1, p):
            mu[j] = -mu[j]
            if j > p:
                prime[j] = False
        for j in range(p * p, n + 1, p * p):
            mu[j] = 0
    prefix = [0] * (n + 1)
    sq = [0] * (n + 1)
    for j in range(1, n + 1):
        prefix[j] = prefix[j - 1] + mu[j]
        sq[j] = sq[j - 1] + mu[j] ** 2
    return mu, prefix, sq


P = primes_to(2047)
cols = defaultdict(list)
event_count = 0
for R in range(56, 2001):
    for q in P:
        if q * q >= R:
            break
        n = (R * R - 1) // (q * q)
        assert n * q * q < R * R <= (n + 1) * q * q
        assert (isqrt(n + 1) ** 2 == n + 1) == (R % q == 0)
        s = isqrt(n)
        assert n not in (s * s, s * s + 1, (s + 1) ** 2 - 2)
        cols[n].append((R, q))
        event_count += 1

double_pairs = []
cube_pairs = 0
for n, events in cols.items():
    for (R, q), (S, r) in combinations(events, 2):
        H, Q = min(R, S), max(q, r)
        det = abs(R * r - S * q)
        assert det * (R * r + S * q) < q * q * r * r
        if Q ** 3 <= 2 * H:
            cube_pairs += 1
            assert R % q == 0 and S % r == 0 and det == 0
        if Q ** 3 <= 4 * H and R % q and S % r:
            assert det == 1 and gcd(R, S) == 1 and (R - S) % 2
            assert 8 * q > 5 * Q and 8 * r > 5 * Q
            assert Q * abs(R - S) >= 2 * H - 1
            double_pairs.append((max(R, S), min(R, S), q, r, n))
first = min(double_pairs)
assert first == (657, 556, 11, 13, 2554)
print("geometry", event_count, "events; cube pairs", cube_pairs,
      "transition pairs", len(double_pairs), "first", first)

# Independent inverse-placement population, no floating square roots.
for H, Q, h in [(128, 8, 128), (256, 8, 256), (550, 13, 550),
                (556, 13, 102), (1024, 16, 1024), (2048, 16, 17)]:
    forward = set()
    inverse = set()
    for R in range(H, H + h):
        for q in P:
            if q > Q:
                break
            if q * q < R:
                forward.add((R, q, (R * R - 1) // (q * q)))
    for q in P:
        if q > Q:
            break
        for n in range((H * H - 1) // (q * q),
                       ((H + h - 1) ** 2 - 1) // (q * q) + 1):
            lo = max(H, q * q + 1, isqrt(n * q * q) + 1)
            hi = min(H + h - 1, isqrt((n + 1) * q * q))
            for R in range(lo, hi + 1):
                inverse.add((R, q, n))
    assert forward == inverse
    off = defaultdict(list)
    ray = defaultdict(list)
    for R, q, n in forward:
        (off if R % q else ray)[n].append((R, q))
    assert not (off.keys() & ray.keys())
    assert max(map(len, off.values()), default=0) <= 2
    K = defaultdict(F)
    sigma = defaultdict(F)
    for ev in off.values():
        for R, q in ev:
            sigma[R] += F(1, q * q)
        for (R, q), (S, r) in combinations(ev, 2):
            K[R] += F(1, q * r)
            K[S] += F(1, q * r)
    assert max(K.values(), default=F(0)) <= F(2, Q)
    sigma_star = max(sigma.values(), default=F(0))
    coeff = min(2 * sigma_star, sigma_star + F(2, Q))
    ray_gram_rows = defaultdict(F)
    for ev in ray.values():
        for R, q in ev:
            ray_gram_rows[R] += sum(F(1, q * r) for S, r in ev)
    assert max(ray_gram_rows.values(), default=F(0)) < F(12, 5)
    for seed in range(8):
        z = {n: F((n * 17 + seed * 31) % 23 - 11, 7)
             for n in off}
        rows = defaultdict(F)
        for n, ev in off.items():
            for R, q in ev:
                rows[R] += z[n] / q
        assert sum(x * x for x in rows.values()) <= coeff * sum(
            x * x for x in z.values())
        alpha = {R: F(1 + (R + seed) % 5, 3) for R in range(H, H + h)}
        full = dict(off) | dict(ray)
        beta = {n: max(alpha[R] for R, q in ev) for n, ev in full.items()}
        zall = {n: F((n * 11 + seed * 19) % 17 - 8, 5) for n in full}
        allrows = defaultdict(F)
        for n, ev in full.items():
            for R, q in ev:
                allrows[R] += zall[n] / q
        assert sum(alpha[R] * v * v for R, v in allrows.items()) <= (
            F(12, 5) + coeff) * sum(beta[n] * v * v for n, v in zall.items())
    print("window", H, Q, h, "events", len(forward),
          "off columns", len(off), "ray columns", len(ray),
          "Kmax", str(max(K.values(), default=F(0))))

mu, M, Sq = mobius_sieve(657 ** 2 - 1)
assert all(mu[n] == mobius_trial(n) for n in range(1, 10001))
assert M[2554] == sum(mobius_trial(n) for n in range(1, 2555)) == -5


def bill(R):
    X = R * R - 1
    G = M[X] - M[R - 1]
    labels = [q for q in P if q * q < R]
    daughters = [(q, (X // (q * q)), M[X // (q * q)]) for q in labels]
    U = sum((F(d, q) for q, n, d in daughters), F(0))
    E = sum(d * d for q, n, d in daughters)
    diag = Sq[X] - Sq[R - 1] + 2 * sum(
        (F(Sq[n] - Sq[R - 1], q) for q, n, d in daughters), F(0))
    B = G * G + 2 * G * U - 2 * E - diag
    return G, U, E, diag, B


for R in [556, 657]:
    print("arithmetic", R, "Mend", M[R * R - 1],
          "Mhistorical", M[R - 1], "bill", str(bill(R)[-1]))
assert bill(556)[-1] == F(-42754054126, 230945)
assert bill(657)[-1] == F(-14830731658, 51051)
assert -2 * bill(657)[0] * F(M[2554], 13) + 2 * M[2554] ** 2 == F(1180, 13)
assert (F(bill(556)[0], 11) - F(bill(657)[0], 13)) ** 2 / 4 == F(2241009, 81796)

# Column completion retains ALL daughter squares, including ray columns.
for H, Q, h in [(56, 7, 31), (556, 13, 102)]:
    columns = defaultdict(list)
    left = F(0)
    complement = F(0)
    A = F(0)
    for R in range(H, H + h):
        alpha = F(1 + R % 5, 3)
        G, U, E, diag, B = bill(R)
        UQ = F(0)
        EQ = 0
        for q in P:
            if q > Q or q * q >= R:
                break
            n = (R * R - 1) // (q * q)
            d = M[n]
            t = F(G, q)
            columns[n].append((alpha, t, d))
            UQ += F(d, q)
            EQ += d * d
            A += alpha * t * t
        left += alpha * B
        complement += alpha * (B - 2 * G * UQ + 2 * EQ)
    penalty = F(0)
    defect = F(0)
    for ev in columns.values():
        w = sum(a for a, t, d in ev)
        mean = sum(a * t for a, t, d in ev) / w
        penalty += sum(a * (t - mean) ** 2 for a, t, d in ev) / 2
        defect += w * (ev[0][2] - mean / 2) ** 2
    assert left == complement + A / 2 - penalty - 2 * defect
    print("all-column-completion", H, Q, h, "columns", len(columns), "residual 0")

# A finite genuine-event, arbitrary-vector counterexample to erasing the ray mask.
H, Q, K = 7448, 31, 8192
I = [K * 3 ** a * 5 ** b for a in range(1, 8) for b in range(1, 8)]
ray_columns = defaultdict(list)
outputs = defaultdict(F)
for R in I:
    assert R >= H and Q ** 3 <= 4 * H
    for q in [p for p in P if p <= Q]:
        if R % q == 0 and q * q < R:
            n = (R * R - 1) // (q * q)
            assert n == (R // q) ** 2 - 1
            ray_columns[n].append((R, q))
            outputs[R] += F(1, q)
assert len(I) == 49 and len(ray_columns) == 62
sigma = F(1, 9) + F(1, 25)
claimed = min(2 * sigma, sigma + F(2, Q))
actual_ratio = sum(v * v for v in outputs.values()) / len(ray_columns)
assert actual_ratio == F(1568, 6975)
assert claimed == F(1504, 6975)
assert actual_ratio - claimed == F(64, 6975)
print("ray-mask-counterexample", len(I), "rows", len(ray_columns), "columns",
      "ratio", str(actual_ratio), "claimed", str(claimed),
      "excess", str(actual_ratio - claimed))

# For the FULL matrix the diagonal must include nondividing labels too.
# Use a larger legal cutoff; do not reuse the ray-only diagonal above.
H, Q, K = 512096, 127, 524288
I = [K * 3 ** a * 5 ** b for a in range(1, 8) for b in range(1, 8)]
ray_image = {(R // q) ** 2 - 1 for R in I for q in (3, 5)}
full_output = F(0)
sigma_full = sum((F(1, q * q) for q in P if q <= Q), F(0))
for R in I:
    assert Q ** 3 <= 4 * H and H <= R and Q * Q < R
    value = F(0)
    for q in P:
        if q > Q:
            break
        n = (R * R - 1) // (q * q)
        if n in ray_image:
            assert q in (3, 5)
            value += F(1, q)
    full_output += value * value
full_ratio = full_output / len(ray_image)
assert full_ratio == F(1568, 6975)
assert sigma_full < F(13, 64)
full_claimed = min(2 * sigma_full, sigma_full + F(2, Q))
assert full_ratio > F(13, 64) + F(2, Q) > full_claimed
print("full-mask-counterexample", "H", H, "Q", Q, "K", K,
      "ratio", str(full_ratio), "claimed_lt", str(F(13, 64) + F(2, Q)),
      "certified_excess_gt", str(full_ratio - F(13, 64) - F(2, Q)))

# Exact finite part plus a proved binomial tail certifies the dyadic ray bound.
bands = [sum((F(1, p) for p in P if 2 ** k <= p < 2 ** (k + 1)), F(0))
         for k in range(1, 11)]
sum_sq = sum(b * b for b in bands)
upper = 3 * sum_sq + F(12, 10)
assert sum_sq < F(2, 5)
assert upper < F(12, 5)
print("dyadic-ray-certificate", "sum_first_10_band_squares_lt_2/5",
      "upper_rounded", float(upper), "strictly_lt_12/5")
print("ALL EXACT ASSERTIONS PASSED")
```

Captured final output:

```text
geometry 17665 events; cube pairs 1047 transition pairs 13 first (657, 556, 11, 13, 2554)
window 128 8 128 events 384 off columns 297 ray columns 67 Kmax 0
window 256 8 256 events 768 off columns 595 ray columns 134 Kmax 0
window 550 13 550 events 2750 off columns 2279 ray columns 324 Kmax 1/143
window 556 13 102 events 510 off columns 424 ray columns 85 Kmax 1/143
window 1024 16 1024 events 5120 off columns 4256 ray columns 604 Kmax 0
window 2048 16 17 events 85 off columns 72 ray columns 13 Kmax 0
arithmetic 556 Mend 165 Mhistorical 5 bill -42754054126/230945
arithmetic 657 Mend 45 Mhistorical -8 bill -14830731658/51051
all-column-completion 56 7 31 columns 92 residual 0
all-column-completion 556 13 102 columns 509 residual 0
ray-mask-counterexample 49 rows 62 columns ratio 1568/6975 claimed 1504/6975 excess 64/6975
full-mask-counterexample H 512096 Q 127 K 524288 ratio 1568/6975 claimed_lt 1779/8128 certified_excess_gt 336179/56692800
dyadic-ray-certificate sum_first_10_band_squares_lt_2/5 upper_rounded 2.391485830852926 strictly_lt_12/5
ALL EXACT ASSERTIONS PASSED
```

### Independent Prime-Certificate Cross-Check

A separate JavaScript sieve and BigInt rational calculation independently confirmed the prime-band inequalities. Unlike the Python trial-division implementation, this uses Eratosthenes marking. The code below is a function body; execute it in a function. It was run in this invocation, not merely proposed.

```javascript
const gcd=(a,b)=>b?gcd(b,a%b):a;
const rat=(a,b=1n)=>{const g=gcd(a,b);return [a/g,b/g];};
const add=([a,b],[c,d])=>rat(a*d+b*c,b*d);
const mul=([a,b],[c,d])=>rat(a*c,b*d);
const sieve=Array(2048).fill(true);sieve[0]=sieve[1]=false;
for(let p=2;p*p<2048;p++) if(sieve[p])
  for(let n=p*p;n<2048;n+=p) sieve[n]=false;
const bands=[];
for(let k=1;k<=10;k++){
  let s=[0n,1n];
  for(let p=2**k;p<2**(k+1);p++)
    if(p%2&&sieve[p])s=add(s,rat(1n,BigInt(p)));
  bands.push(s);
}
const sum=bands.map(b=>mul(b,b)).reduce(add,[0n,1n]);
const upper=add(mul([3n,1n],sum),[6n,5n]);
if(!(5n*sum[0]<2n*sum[1]&&5n*upper[0]<12n*upper[1]))
  throw Error("exact prime-band certificate failed");
return {odd_primes:sieve.filter((v,n)=>v&&n>2).length,
        sum_first_10_band_squares_lt_two_fifths:true,
        certified_ray_bound_lt_twelve_fifths:true};
```

Result:

```json
{
  "odd_primes": 308,
  "sum_first_10_band_squares_lt_two_fifths": true,
  "certified_ray_bound_lt_twelve_fifths": true
}
```

The full operator proof is not reduced to testing vectors or a numerical matrix eigensolver. Exact finite code supplies only the declared certificates and regressions; E3-E5 provide the all-scale arguments.

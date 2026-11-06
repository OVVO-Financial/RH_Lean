# Coordinator research synthesis | 2026-11-05

## A. What changed mathematically?

**eta_gate: SEARCH_BROAD.** No new complete-endpoint gain has been established by this invocation. Live main includes merged Nyman flat-taper return PR #1093; its precise mathematical scope is being checked, not promoted to an RH proof. The independent nine-route selector is active.

Execution status: **PARTIAL / IN_PROGRESS**, checkpoint 2026-11-05 12:13:31 UTC. This is one actual scheduled Coordinator invocation, not a launch of other agents.

## B. Current proof objective

Pinned main: `ff620da3c0d2c29585805960c6be183c07f16556`, committed 2026-11-05T03:23:34Z.
Authority: main:AGENTS.md blob `547dda0d9456e7a4e1165dc72d59da6f70d5c023`; CURRENT_PROOF_CONTRACT.md blob `7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c`.
Canonical objective remains VFCanonicalSquareVonKochStatement:
there exists C >= 0 such that for every natural R >= 2,
|pi(R^2)-VF_can(R^2)| <= C R log R. The independent arithmetic estimate is OPEN.
The nearer new uniform below-7/8 endpoint and complete-return gate are separate from structural lemmas.

## C. Competing mechanism portfolio

PENDING source/report review. Preserve all nine protected routes; no automatic OAI or NYMAN concentration.

## D. Conceptual research performed

PENDING substantive investigation. No original mathematical result claimed in this checkpoint.

## E. Specialist findings

Reports snapshot `d64e2a707a60e4445a2c948157fe12a45e0a6fbb` (2026-11-05T10:35:48Z) contains November 4 reports for all six specialists and the Coordinator, and November 5 Owner, Wheel, Census, Referee and Lean reports. November 5 Analytic is absent at that snapshot: current stage PENDING; November 4 evidence is dated carry-forward. Report bytes and external handoffs have been retrieved; detailed acceptance review is in progress.

## F. Mathematical bottlenecks

PENDING exact-source diagnosis; no green conditional theorem pays its missing hypothesis.

## G. Strategy decisions

Follow NO_PIGEONHOLING_ROUTE_SELECTOR_V1. No schedule, policy, Lean source, proof branch, other role report or main modification.

## H. Next specialist assignments

PENDING. Assignments will be asynchronous written handoffs only; no other agent has been launched.

## I. Lean and PR status

Verified collection: sole open PR #1094 is draft at `1ea4a8a4308976721a3841998d6c3a4554f7a9c9`; PR #1093 merged at 2026-11-05T03:23:34Z. Nine workflows attached to current main are successful. Dedicated exact-head theorem/axiom checks are still under review; no further formal status is asserted.

## J. Next-run resume capsule

Complete the original-source and today/yesterday handoff audit; choose a substantive independent question; prove or falsify it with full quantifiers; record portfolio, six nonduplicate handoffs and exact CI evidence; append the synthesis and verify both mirrors. This checkpoint is not a completed research report.


## Final Research Synthesis - 20261105-coordinator-1

Actual invocation: SCHEDULED, 2026-11-05T07:10:01-05:00, America/New_York; RUN_ID_UNAVAILABLE. This continues the early checkpoint above, not a second execution. Synthesis prepared after the 12:28:07 UTC source/test check. Publication completion is recorded only in the subsequent verified receipt.

### A. What Changed Mathematically?

**eta_gate: SEARCH_BROAD. A sub-square-root collection of prime-multiplication rules still cannot force a positive defect in finitely many fixed CORR4 daughter caps, even after preserving a uniform sublinear bound at EVERY intermediate prefix.** This extends today's fixed-wheel and logarithmic-wheel obstructions by a different mechanism: perturb a sparse collection of genuine positive semiprime cores, instead of freely reassigning the whole rough population and estimating a growing inclusion-exclusion error.

Precisely, assume an already available genuine envelope |M(n)| <= C0 n^b, with fixed 0<b<1. Fix finitely many distinct odd prime daughter labels. For ANY rule cutoff y_R tending to infinity with y_R/sqrt(R^2-1) tending to zero, every sufficiently large R admits the cap-saturating auxiliary function constructed in D. It preserves squarefree support, every prime's actual sign, all coefficients below R, the actual endpoint M(R^2-1), every prime rule p<=y_R, and a uniform O(n^b) bound for all its prefixes. The constant may increase; the exponent does not. In particular, the obstruction covers all primes up to X^delta for every fixed delta<1/2, and up to sqrt(X)/log X.

**This is a theorem about a specified auxiliary relaxation, NOT a counterexample to genuine Mobius cancellation, the full CORR4 bill, or RH.** The functions differ with R, the daughter labels are fixed, and the complete complementary-label contribution remains. Requiring one globally coherent function or using further actual factor relations is a different problem. At the full cutoff p<=sqrt X the rules force f=mu, providing a rigorous limiting control rather than an extrapolated impossibility claim.

New claims C53-C56: **PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED**, with explicit existing-input dependence below. C57: **FINITE_COMPUTATION**. No literature-originality claim is made. No new complete-endpoint gain, canonical VF bound or RH proof is established.

Formal change, separately verified: the finite C49 high-correction obstruction is now **PROVED_IN_LEAN at PR #1094's exact head**, CI_GREEN but DRAFT/UNMERGED. Its component scope is unchanged. C50-C51's analytic implications and today's new claims are not thereby formalized or Referee-accepted.

### B. Current Proof Objective And Authority

Pinned main: **ff620da3c0d2c29585805960c6be183c07f16556**, tree **958770679fb0146df80f44de258f694cd232434e**, committed 2026-11-05T03:23:34Z. Live AGENTS blob **547dda0d9456e7a4e1165dc72d59da6f70d5c023**; CURRENT_PROOF_CONTRACT blob **7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c**. Deployment acknowledgement: **NO_PIGEONHOLING_ROUTE_SELECTOR_V1**, policy blob **ffd8f1c65cc4da656174956d4e03b48bea46768b**, consumed through the stable selector and the breadth, complete-return, engine, role and multi-run policies.

The actual declaration in `research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean` remains

```text
VFCanonicalSquareVonKochStatement:
exists C:Real, 0<=C and forall R:Nat, 2<=R ->
  |vfCanonicalSquareDefect R| <= C*R*log R.
vfCanonicalSquareDefect R = pi(R^2)-VF_can(R^2).
```

The arithmetic conclusion is OPEN. The fixed sqrt(2) phase, square/all-real transports, and the explicit `ClassicalVonKochRHCriterion` parameter of the canonical RH consumer are unchanged. CORR4 instead has its own internally proved Mertens-power consumer, with an unpaid signed arithmetic premise.

**Do not erase the inherited strict result.** The inspected live `native_mertens_fixed_strict_power` states an existential fixed positive gap below 7/8. Today's argument may weaken that inherited envelope to b=7/8. It neither optimizes the tiny slot constant nor re-credits it as this invocation's gain. SEARCH_BROAD here concerns additional independent arithmetic and the live broad-research gate. I inspected the declaration, not a fresh compilation of its entire analytic dependency chain.

Original sources read at this main:

| Source | Git blob | Scope used |
| --- | --- | --- |
| `research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean` | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb | Literal canonical statement and explicit classical interface |
| `RHLean/Proof/SignedTransportAmplificationAudit.lean` | 746f35f126f36e024d39e38c92dde30aabca266b | `rawQ2ChildCutoff`, unshifted daughter square |
| `research/CANONICAL_ROUGH_Q2_TAIL_REDUCTION.lean` | ebca096e83009a7df514d00b6a2696be86a94c55 | Strict q^2<R low labels |
| `research/GLOBAL_RETURNED_CORE_WEIGHTED_MOBIUS_COORDINATE.lean` | f0e2e672a1ed369d1dc6dacbe9024c65e986a3c8 | Original reciprocal 1/q weights and physical-site Fubini |
| `research/GLOBAL_RETURNED_CORE_RECIPROCAL_PREFIX_SIGNED_CELL_SPLIT.lean` | 29bb263ddd07b12a2dd5ccf6a12aecaf627134d8 | Both mixed orientations and tail/tail |
| `research/GLOBAL_RETURNED_CORE_PREFIX_TAIL_MIXED_REMAINDER_IDENTITY.lean` | d17aeb639bb47d79333cf0d00760c2604feddfdf | Original full remainder and diagonal restoration |
| `research/CORR4_OAI_POWER_MIXED_TAIL_GATE_20261025.lean` | bb0ee1252e7ba10c44ae5b8d827573d6c581b73a | Explicit conditional power consumer |
| `research/oai_434/VF919NativeStrictMertens.lean` | b33a4883e1ddb0551b0f11f062bce46680d87450 | Inherited sublinear input, not a new supplier |
| `research/NYMAN_FLAT_TAPER_RETURN_20261104.lean` | 2d23721027ecc44e85b7add02fc632b482f03352 | Merged exact return, not a norm upper bound |

### C. Competing Mechanism Portfolio

Three highlighted mechanisms remain mathematically distinct; this is not a reduction of the protected nine-route programme.

**1. Genuine factor relations in the complete CORR4 mixed bill: REVISE.** Concept: exploit relations among actual residual core signs, or the full growing daughter family, before taking norms. Independent input: a new signed restriction not implied by support, prime signs, sub-root prime rules and the inherited prefix exponent. Target implication: `mertensPowerBound_of_corr4MixedTailBill` converts B_R <= A R^(4 beta), beta>=1/2, to the matching genuine Mertens bound. First missing step: an independently justified full B_R upper estimate improving the inherited exponent. Support: exact source identities, finite shared-core facets at R=57/58, and today's precise description of what the weaker relaxation permits. Obstruction: C54-C55 invalidate fixed-label defect suppliers even with much larger rule sets and a whole-prefix envelope. Decisive experiment: test a proposed additional relation against the explicit sparse semiprime orbit flips in D8, not another larger wheel scan. Specialists: Wheel and Referee; Census only for a changed hypothesis. Retire the failed relaxation-based supplier, not CORR4.

**2. Prime-location discrepancy with joint source return: CONTINUE.** Concept: retain original prime-minus-Li increments with genuine cofactor signs, or the sampled JOH backlog after its O(N) placement payment. Independent input: an actual signed estimate for those increments/backlogs beyond the inherited scalar prime-error envelope. Target implication: first return to the complete SAT M(Y)=L_R+E_R+C_R or the exact JOH consumer; only then use its endpoint implication. First missing step: OPEN-SAT-I plus its anchor/complement, or JOH's weighted sampled backlog. Support: Owner LC4's paid placement sector and RC1-RC4's genuine arithmetic partition. Obstructions: bounded ancestry capacity fails even at squarefree depth three; separate RC5 packet payment is equivalent to a specified ordinary prime-error bound, and the current separate SAT endpoint certificate is nonbinding for a bootstrap. Decisive experiment: independently certify the already specified JOH arrival-cell reconstruction; for SAT, challenge a proposed joint bound rather than assuming a small centered rectangle. Specialist: Owner, with Census and a separate Referee review. VF-LOW is Owner's next protected turn; this portfolio does not override it.

**3. NYMAN exact-head, joint middle-norm mechanism: CONTINUE, WITHOUT COMPONENTWISE PAYMENT.** Concept: changed low coefficients create a polynomial exact head, while signed base/correction cancellation is retained through the whole middle. Independent input: a new uniform or suitable unbounded-sequence upper bound for the ENTIRE original residual norm. Target implication: accepted C45-C46 turn a head H>=c N^theta and E<=N^(kappa+epsilon) into zero boundary 1/2+kappa/(2theta); the norm supplier remains unproved. First missing step: the corrected full middle, not the already paid head, transition or remote tail. Support: Analytic P1-P10, Referee-9 scope acceptance, merged #1093, and #1094's newly verified finite component obstruction. Obstructions: prefix-only majorants lose 1-theta; divergent floor pieces cannot be normed separately; a separate high-correction rate has the stronger C50-C51 analytic demand. Decisive experiment: an explicitly paired arithmetic numerator must improve the complete signed middle after both bands and after-N terms are restored. Specialist: Analytic, whose current report is PENDING. Referee review of C50-C51 remains separate.

**Protected coverage, not fictional completed work.** The rows below use the actual dated reports at the pinned report snapshot. Carry-forward source references are evidence from those reports, not newly rerun proofs.

| Route | Last substantive investigator attempt | Exact surviving gap / next action | Review and formal state |
| --- | --- | --- | --- |
| VF-LOW | Nov 4 Owner-2 SF1-SF5 | Actual-weight response after the squarefree depth-three capacity obstruction; next Owner turn | Paper/self-audit; no new formal bound |
| SAT | Nov 5 Owner-1 RC1-RC6 | Joint I_R, original anchor and full complement | Paper/self-audit, RC5 target-strength at its stated scope |
| JOH | Nov 4 Owner-3 LC1-LC5 | Weighted sampled backlog after O(N) placement | Paper/self-audit; independent arrival fixtures pending |
| CODIV | Nov 4 Analytic-3 M1-M6 | OPEN-CD5 fixed-power triangular lag input; all-log result alone insufficient | External-theorem application review pending; not formalized |
| OAI-NNS | Nov 4 Analytic-2 CF1-CF3 | Original coefficient-sensitive all-selected inverse energy and full return | CF scopes accepted by Nov 4 Referee; no new all-selected saving |
| NYMAN | Nov 4 Analytic-1 P1-P10 | Joint whole middle; next Analytic route due | P1-P10 accepted with scope; #1093 structural return merged |
| FINITE-AC | Nov 4 Wheel-2 L1-L4 | Signed estimate beyond coherent full-prime completion; next Wheel turn | Paper/self-audit; averaging completions is not a new direction |
| CORR4 | Nov 5 Wheel-1 F1-F4 | Residual-core information or genuinely growing labels; new C54 extends method obstruction | Fixed-P scope accepted; new growing/sub-root work paper only |
| MU-LIFT | Nov 4 Wheel-3 QC1-QC4 | Class-changing signed interaction and full subcritical recurrence | Paper/self-audit; square-class absolute method obstruction awaiting separate review |

The latest three actual Owner attempts are VF-LOW, JOH, SAT; Wheel's are FINITE-AC, MU-LIFT, CORR4; Analytic's are NYMAN, OAI-NNS, CODIV. No current-day Analytic execution is invented. Next protected routes: **VF-LOW / NYMAN / FINITE-AC** respectively. Support work must not erase those assignments.

### D. Conceptual Research Performed

#### D0. Original CORR4 carrier and the exact claim being challenged

For integer R>=56 let

```text
X=R^2-1; S_R={odd primes q:q^2<R}; Y_q=floor(X/q^2);
m=M(R-1); G=M(X)-m; d_q=M(Y_q);
V_q=sum_(R<=n<=Y_q) mu(n)^2; V_0=sum_(R<=n<=X)mu(n)^2;
H_R=V_0+2 sum_(q in S_R)V_q/q;
J_q(d)=2Gd/q-2d^2;
B_R=2 Mixed_R-2 sum_q d_q^2=G^2-H_R+sum_(q in S_R)J_q(d_q).
```

This uses the literal unshifted Mertens daughters, original reciprocal column, both mixed orientations and actual diagonal H_R. On sites t(n)=1_[R,X](n) and a(n)=sum_q 1_(n<=Y_q)/q, the ordered off-diagonal expression is G^2+2G sum_q d_q/q-H_R. This is not Pearson correlation or the masked original VF #915 statistic.

The anchored one-coordinate cap is C_q^anc=max J_q(d) on the parity interval {m-V_q,m-V_q+2,...,m+V_q}. The candidate disproved below is that the stated prime-rule relaxation forces a strictly positive sum of cap defects on a FIXED finite label set at all sufficiently large R. Genuine mu is a member of the relaxation, but its other members are not mu.

#### D1. C53: saturated Mobius kernel vectors generate every integer direction

Assume |M(n)|<=C0 n^b for n>=1, C0>=1 and 0<b<1. Fix q_0=1 and distinct odd primes q_1,...,q_s. For n>=1 define the integer vector

```text
v_n=( M(floor(n/q_i^2)) )_(i=0..s).
```

**Claim C53.** There is a finite collection of n-values such that every z in Z^(s+1) is a nonnegative INTEGER combination of the corresponding v_n. Moreover, a fixed L exists such that at most L ||z||_1 columns suffice, counting multiplicity.

Proof of the crucial zero mean, without assuming a new cancellation rate: for real sigma>1, absolute Dirichlet convolution gives sum mu(k)/k^sigma=1/zeta(sigma), and partial summation gives

```text
1/zeta(sigma)=sigma integral_1^infinity M(t)t^(-sigma-1)dt.
```

The inherited bound dominates the integrand, for 1<sigma<=2, by 2C0 t^(b-2), which is integrable. Since zeta(sigma) tends to infinity as sigma decreases to 1 (already implied by its finite harmonic partial sums), dominated convergence yields

```text
sum_(n>=1) M(n)/[n(n+1)] = integral_1^infinity M(t)t^(-2)dt = 0.
```

Grouping the positive weights over n=q_i^2 k,...,q_i^2(k+1)-1 therefore gives the ABSOLUTELY convergent vector identity

```text
sum_(n>=1) v_n/[n(n+1)] = 0.                         (C53a)
```

Also v_1=e_0, and v_(q_i^2)-v_(q_i^2-1)=e_i for i>0: the endpoint coordinate's jump is mu(q_i^2)=0; distinct other prime squares do not divide q_i^2. Thus the columns generate the full integer lattice.

If a real h has h dot v_n>=0 for EVERY n, C53a and its strictly positive weights force h dot v_n=0 for every n; the unit jumps force h=0. For each unit h there is consequently an n with h dot v_n<0. Compactness of the unit sphere selects finitely many such columns with no nonzero nonnegative separating functional. The elementary finite-dimensional separating-hyperplane theorem implies their conic hull is the whole space. Adjoin the finitely many unit-jump columns if necessary.

Because these columns have integer coordinates, any feasible nonnegative linear representation can be chosen rational. For a column v, write -v as a nonnegative rational combination, multiply by an integer k, then add (k-1) copies of v. This expresses -v as a nonnegative INTEGER combination. The monoid consequently contains the whole lattice generated by the columns, namely Z^(s+1). Choose once and for all representations of each +e_i and -e_i; their maximal total length is L and gives the asserted linear bound. This proves C53. No quantitative bound for the minimal finite cutoff or L is claimed.

This is more than a new notation for the desired CORR4 estimate: it establishes flexibility of an explicitly different sign family, using only the existing input. It supplies no improved Mertens exponent.

#### D2. Independent input: many genuine rough semiprime cores in fixed intervals

For every fixed 0<alpha<beta<=1 there are constants c,c'>0 such that, for all sufficiently large X, at least c X/log(X)^2 distinct integers a in (alpha X,beta X) are products of two DISTINCT primes both exceeding c' sqrt X.

Proof: choose two disjoint fixed positive intervals (u1,u2) and (w1,w2) with every product in (alpha,beta). The prime number theorem supplies at least c1 sqrt X/log X and c2 sqrt X/log X primes in their sqrt-X dilates. Products are injective by unique factorization and disjointness of the two prime intervals. Both factors exceed a fixed positive multiple of sqrt X. This proves the count. Only finitely many fixed intervals will be used, so all their thresholds and positive constants can be chosen together.

The imported theorem is only the ordinary **pi(x)~x/log x**, verified against [NIST DLMF 27.2.3](https://dlmf.nist.gov/27.2.E3), which records its original Hadamard/de la Vallee Poussin provenance. Its application is to fixed-ratio intervals tending to infinity, NOT short intervals with shrinking relative length. All later use of these cores and their signs is derived here; no prime independence or probabilistic sign model is imported.

#### D3. C54: interpolation with every sub-root prime rule

Fix the labels, C0,b as in C53 and C>0. For each integer R let X=R^2-1 and let y_R be real with y_R -> infinity and y_R/sqrt X -> 0. There are constants R0 and C_star, independent of the target vector, such that for EVERY R>=R0 and EVERY integer vector (t_0,...,t_s) satisfying

```text
|t_i| <= C X^b,
t_i == sum_(n<=floor(X/q_i^2)) mu(n)^2 (mod 2),       (C54a)
```

there exists f_R:{1,...,X}->{-1,0,1} with

```text
|f_R(n)|=mu(n)^2;                 f_R(n)=mu(n) for n<R;
f_R(p)=-1 for every prime p<=X;
f_R(p*n)=-f_R(n) whenever p<=y_R is prime, p does not divide n, p*n<=X;
sum_(n<=floor(X/q_i^2)) f_R(n)=t_i for every i;
|sum_(n<=z)f_R(n)| <= C_star z^b for EVERY integer 1<=z<=X.       (C54b)
```

The number of changed physical coefficients is O_(labels,C0,C,b)(X^b), and every change is above c X for a fixed c>0 depending only on the finite column certificates. The threshold may depend on the convergence of y_R; C_star need not. There is no asserted common function for different R, no growing-label uniformity and no preservation of the original numerical constant C0.

**Construction and exact source map.** Let W_R be the product of primes <=y_R. Every squarefree physical n has a unique representation n=a d with gcd(a,W_R)=1 and d|W_R. Its true sign is mu(a)mu(d). Let D be the largest column index in the finite C53 certificates. Eventually y_R>=D. For a semiprime core in

```text
X/(n+1) < a <= X/n,  n<=D,
```

both prime factors exceed y_R by D2 and y_R=o(sqrt X). The true core sign is +1. Every admitted multiplier is a squarefree d<=floor(X/a)=n<=D, hence all its primes lie in W_R. Its full prefix vector is exactly

```text
sum_(d squarefree, a*d<=floor(X/q_i^2)) mu(d)
   = M(floor(X/(a*q_i^2)))
   = M(floor(n/q_i^2)) = (v_n)_i.                  (C54c)
```

The last equality is an exact floor identity for integer q_i^2, not a limiting approximation. Flipping the ENTIRE admitted orbit of this positive semiprime core changes the vector by -2v_n. No individual multiplier is omitted and no occurrence belongs to two different rough cores.

Let delta_i=(t_i-M(floor(X/q_i^2)))/2. Parity makes delta integral and the inherited bound gives ||delta||_1 <= (s+1)(C+C0)X^b/2. Apply C53 to -delta. At most L||delta||_1 cores are required, with prescribed counts in finitely many disjoint intervals. Each interval supplies at least c_n X/log(X)^2 cores, which dominates any fixed multiple of X^b. Reserve that many distinct cores, flip their complete orbits, and leave every other core at its genuine sign. This gives every target exactly.

All changed sites are composite and exceed X/(D+1)>R eventually; the entire history and all prime signs remain untouched. Adding an allowed prime changes only d, not a, so it toggles the same sign on the entire orbit. Squareful sites stay zero on both sides. This proves all arithmetic constraints in C54b.

**The intermediate-prefix envelope is not silently assumed.** Each changed core has at most D admitted sites. Thus the total absolute change of ANY prefix is at most

```text
D L (s+1)(C+C0) X^b.
```

Before X/(D+1), no site changes. Afterwards X^b <= (D+1)^b z^b. One valid uniform constant is therefore

```text
C_star = C0 + D L (s+1)(C+C0)(D+1)^b.                (C54d)
```

This completes the paper proof. The construction uses the inherited genuine exponent to size sparse perturbations, not a new desired exponent. In particular, adding merely the existence of a uniform prefix bound at that SAME exponent does not repair the failed relaxation.

#### D4. C55: the exact CORR4 fixed-label no-go

Take t_0=M(X), and for each fixed q_i choose any anchored parity-cap maximizer. Completing the square gives

```text
J_q(d)=G^2/(2q^2)-2(d-G/(2q))^2.
```

The fixed-q squarefree count V_q is asymptotic to a positive constant times X/q^2, whereas m and G are O(X^b). Consequently the nearest parity-lattice point to G/(2q), at distance <=1, lies in the anchored interval for all sufficiently large R. Its size is O(X^b). It has the required squarefree-prefix parity, since every nonzero Mobius sign is 1 modulo 2. The elementary squarefree asymptotic used here follows from mu(n)^2=sum_(d^2|n)mu(d), with O(sqrt X) error; it is not an RH assumption.

C54 therefore supplies an f_R obeying all its restrictions, preserving the actual endpoint and history, for which

```text
sum_(q in fixed L) [C_q^anc-J_q(sum_(n<=Y_q)f_R(n))] = 0.       (C55)
```

Hence any eventually strictly positive universal lower bound for this selected defect over the stated relaxation is **REFUTED**, including a claim that only imposes some uniform whole-prefix O(z^b) envelope with an unspecified constant. A fixed preassigned smaller constant is not covered automatically.

The original full expression remains

```text
B(f_R)=G^2-H_R+sum_(q in L)J_q(d_q(f_R))
                    +sum_(q in S_R minus L)J_q(d_q(f_R)).       (RETURN)
```

The final sum is NOT discarded or paid. There is no claim that B(f_R) is large, that all growing labels can be simultaneously optimized, or that true mu has zero defect. The finite source polynomial can be evaluated on this auxiliary family; the Lean declarations on actual mu have NOT been redefined.

#### D5. C56: the full square-root cutoff forces the true signs

For ANY integer X>=2, suppose f has squarefree support, f(1)=1, f(p)=-1 for all primes <=X, and the prime-multiplication rule for EVERY prime p<=sqrt X. Then f=mu on 1..X. For a squarefree composite n, choose its least prime p<=sqrt n<=sqrt X. The cofactor is smaller and coprime to p, so induction gives f(n)=-f(n/p)=-mu(n/p)=mu(n). Primes, 1 and squareful sites are already fixed.

This elementary forcing argument is a boundary control, not a newly discovered factorization theorem. Together with C54 it locates a genuine scale obstruction: every diverging o(sqrt X) cutoff leaves the stated fixed-coordinate freedom, whereas the full sqrt X cutoff does not. No sharp transition for each fixed constant multiple of sqrt X is asserted.

#### D6. Novelty and no-circularity review

Today's Wheel F2 is fixed-P interpolation. Referee-2 extends it under 2^|P| A/sqrt X ->0 and A^2/log X ->0, including p<=log X. Their proofs reassign the whole unanchored core population, and their stated conclusions do not control every intermediate prefix. C54 instead starts with genuine mu, obtains all signed correction directions from the saturated kernel's zero weighted mean, and changes only O(X^b) balanced semiprime orbits. It does not estimate 2^|P| or ask for arbitrary rough-sign balancing. This is a genuinely different argument, not numerical range extension.

C53's zero-mean identity alone is structural. Its conic/lattice consequence plus D2 and the sparse perturbation bound give the new quantified flexibility theorem. C54 is not equivalent to the canonical target and does not improve its input exponent. C55 refutes ONLY a universal assertion on an explicitly enlarged family. A valid new genuine-Mobius theorem, even one whose conclusion is target-equivalent, remains welcome if independently proved.

The general proof uses the explicit existing power envelope. It should not be described as an elementary unconditional proof of such an envelope. For the repository's actual arithmetic instance, that input is inherited, not invented. Independent Referee review of C53-C55 is still required. The self-checks in this invocation are not independent acceptance.

#### D7. Checked cross-route connection and non-transfer

Owner's SAT RC1 supplies a useful contrasting idea: genuine semiprimes can be rigid within a small-prime core class. Here the exact map is (p,r)->a=pr->the FULL set {a d<=X: d squarefree, all prime factors <=y_R}; coefficients are mu(a d)=mu(d) and a flip contributes -2mu(d). D2 proves availability in the new balanced-factor intervals. This is not the SAT rectangle, whose owner and cofactor have different scales, and no SAT norm bound or inverse prime-error estimate is transferred.

There is also an exact scalar connection to the Nyman weight: sum M(n)/[n(n+1)]=0 supplies the positive-weight annihilator in C53. It is linear in the genuine Mertens prefix, whereas Nyman's residual energy is a square of different coefficient functions. Squaring or importing its tail estimate would be an invalid transfer. The new useful implication is specifically zero weighted mean plus isolated unit jumps -> two-sided finite integer correction directions. Neither Nyman norm convergence nor a Hecke coefficient identification is assumed.

#### D8. C57: exact decisive experiments and falsifiers

Before the physical test, the discriminator was fixed: construct both signs of every coordinate direction, verify whole-orbit admission, history/prime preservation and EVERY affected allowed-rule edge, and require a failure when an omitted large-prime rule or an incomplete orbit is introduced. This is not an exponent fit or a search for evidence of RH.

For labels (1,3,5,7), seven small kernel columns suffice:

| n | v_n |
| ---: | --- |
| 1 | (1,0,0,0) |
| 3 | (-1,0,0,0) |
| 10 | (-1,1,0,0) |
| 26 | (-1,0,1,0) |
| 95 | (2,-1,-1,1) |
| 98 | (1,-1,-1,0) |
| 219 | (4,-2,-2,-1) |

Exact nonnegative integer certificates:

```text
 e0=v1;                       -e0=v3;
 e1=v1+v10;                   -e1=v26+v98;
 e2=v1+v26;                   -e2=v10+v98;
 e3=v10+v26+v95;              -e3=2v10+2v26+v219.
```

A numerical integer optimizer was used only to discover this list. The deliverable verifier uses standard-library integer arithmetic, independently computes mu by trial factorization, and verifies every displayed equality exactly; no optimizer or floating tolerance is part of the certificate.

Physical fixtures use R=10^6, X=999999999999 and the EXACT cutoff y=floor(sqrt(X)/bit_length(X))=24999, containing 2,762 prime rules. All eight certificates were realized by distinct balanced semiprime cores and complete admitted orbits. There were 444 changed-site occurrences across the eight separate fixtures, 1,400 affected rule-edge checks, and six endpoint-preserving daughter moves. Unchanged edges retain the genuine rule by definition; squareful sites stay zero. This is a sparse exact construction, NOT a numerical census of all integers up to X and NOT a computation of M(X).

One genuine full-complement warning appears in the witness increasing d_7 by 2: it also changes d_11 and d_13 by -2 each. This is why the final sum in RETURN cannot be suppressed. Adding the omitted prime-factor rule at one of each witness's balanced core factors detects f(pr)=-1 rather than +1. Deleting the 2a companion of a changed a in the n=10 cell violates the p=2 rule. Both negative controls passed.

Executed standard-library verifier SHA-256: **17c918e37daa65f7c01b18025e4ffaa72bd9e8633c98c9b0c080bb53da73fb67**. Its complete source and exact output are appended for durable reproduction. These checks do not certify the infinite PNT/convexity argument in Lean. The small integer cone certificates can, however, be checked without that general argument.

### E. Specialist Findings And Continuity

Reports were retrieved at **agent-reports@d64e2a707a60e4445a2c948157fe12a45e0a6fbb**, whose commit time is 2026-11-05T10:35:48Z. I read the relevant dated result, derivation, review and resume sections; executable appendices were not all rerun. Retrieval is not blanket mathematical acceptance.

| Role | Nov 4 blob | Nov 5 blob / stage | Disposition |
| --- | --- | --- | --- |
| Coordinator | 68495a5e913eee0e788940a683cf16ec4d0984cc, both mirrors | This actual invocation | C41-C43 scope obstructions; C45-C47 accepted; C49 finite core now PR-head verified; C50-C51 review pending |
| Owner | 560b0b7617703b64e728e12e60a390646c9379ea | 51d0ca5e2e16ab13a341143b56aefdbf4ab7993a | RC1-RC6 and LC/SF carry-forward retained with self-audit status; not independently endorsed wholesale |
| Analytic | 04ffb1b41d8b6afe5a5d89754f5ccbc8d9682d58 | ABSENT: PENDING | Explicit Nov 4 carry-forward P1-P10, CF1-CF3, M1-M6; no fabricated today execution |
| Wheel | 37ad6a1230fbb46369311790ed5686baf1775598 | 2fe34fb6712c34db043e14b1046bb20b9da2f769 | F1-F3 accepted with scope by Referee; full CORR4 still open; L/QC separate pending claims |
| Census | 4bd5319fa3d13219cdad006dce4a854b606c2f7c | 44f070eed4302f3d8d560346c6fb9b66c35be18a | R=57/58 joint gaps independently reproduced by Referee; no asymptotic positive-gap inference |
| Referee | 0e4fdfbf90d52a74074e04ef6cb6988339dc8d84 | edabebb46222d0cb5b85bd4263921a6ba000ce0e | Fixed-P acceptance and exact joint gaps; growing-rule extension is its own paper/self-audit result |
| Lean | 5fce0138779d67eda4e69c13230274e6419de894 | 2b9aabf0dec05ec75d9c20ffaa2e971080f930dc | #1093 merged; #1094 finite original-carrier theorem verified at unmerged head |

Important retained corrections: Y_7(59)=71, not 70; the earlier program used 71, so its numerical certificate is unchanged. The R=57 and R=58 marginal-majorant gaps are respectively 28/3 and 12; their existence does not imply a positive gap eventually. The prior Nyman factor-four and monotonicity falsifiers remain accepted only at their exact stated scopes, and were not rerun here.

External inbox blob **038018145c0fddb2f6306c0712373adf9cd1ea52**, read at the same snapshot, has no entry later than October 18. EXT-20261018-PNT-1..3, EXT-20261017-XCOORD-1 and EXT-20261014-5 retain source, boundary and unconditional-versus-first-bad safeguards. They supply no new C54 estimate and their historical task order/cadence is superseded by current main. No missing external handoff is invented.

### F. Mathematical Bottlenecks

**CORR4:** for some fixed exponent beta improving the inherited envelope, prove B_R<=A R^(4 beta) on EVERY required R, with beta>=1/2, using genuinely new arithmetic. Relative to the rounded 7/8 benchmark, B_R<=C_epsilon R^(7/2-eta+epsilon) has x-exponent gain eta/4, but a NEW claim must also compare with the inherited strict gap. C54 gives no such inequality. The complete bill is target-strength: its forward consumer is inspected, and the converse follows at paper scope from |G|=O(X^beta), sum_q |d_q|/q=O(X^beta), and the nonpositive subtracted squares/diagonal.

**NYMAN:** the entire corrected middle norm remains unpaid. Exact head, finite correction obstruction and paid remote tail do not control the base/correction mixed term or the remaining middle ranges. C50-C51 remain separate review obligations, not assumed suppliers.

**SAT/JOH:** jointly control actual prime-error increments/backlogs with exact boundaries; do not infer a bound for one centered packet from a bound for the sum. **CODIV:** the every-log result is not a fixed-power source estimate. **FINITE-AC/MU-LIFT:** source completion or class-preserving absolute cancellation has no remaining independent gain; a real coefficient-sensitive signed estimate or subcritical full-prefix recurrence is still needed. These are independent gaps, not nine names for one assumed covariance.

### G. Strategy Decisions

1. **Retire the specific CORR4 repair** that expands only small-prime rules, keeps finitely many labels, and adds an inherited-exponent prefix envelope with a free constant. Subject to independent review, C54-C55 eliminate that repair throughout the diverging sub-root range. Keep the exact finite facets as valid finite mathematics.
2. **Do not retire CORR4 or infer a full-source no-go.** Test genuinely additional residual-core relations, growing-label coupling, or stronger quantified information that the constructed family violates. Merely enforcing all prime rules at sqrt X recovers mu; that observation is not by itself a usable bound.
3. **Restore distinct primary work at the next actual invocations:** Owner VF-LOW, Analytic NYMAN, Wheel FINITE-AC. A support audit of this report must not consume all investigators or reset their rotation.
4. **No new upper estimate survived this investigation.** The substantial output is the new precise obstruction, its sparse constructive proof, a stricter test for future hypotheses, and exact finite certificates. New complete endpoint gain remains UNKNOWN.
5. **Formalization is selective.** Keep #1094's review distinct from its compilation. Do not manufacture a proof PR for an unproved improved bound or recompile already merged identities for activity.

### H. Next Specialist Assignments

These are asynchronous requests in the Coordinator's own report, not launches, schedule changes or claims of future work already running.

**Owner Payment, next protected VF-LOW:** resume SF1-SF5 on actual VF-weighted squarefree depth-three seats. Exact question: can a chronological, signed cross-core response evade the once-only ancestor-capacity obstruction without reusing a historical prime charge? Reuse the 435-seat/31-ancestor witness and the infinite fixed-depth construction. Missing input is original-weight return and full complementary-source admission, not prime-count density. Expected output: one occurrence-preserving signed relation with a new quantitative restriction, or a legal counterexample to a proposed response. Falsifier: the same historical capacity charged twice, or a physical seat outside the mask. A surviving result would distinguish genuine VF leverage from the now-dead bounded-capacity repair. Do not transplant C54's artificial signs into VF.

**Analytic Type II, next protected NYMAN:** resume P10 and accepted C45-C47, with #1093 and #1094 available at their stated scopes. Exact question: can a signed decomposition pair the forced reciprocal-moment response with the base BEFORE squaring, yielding an independently proved improvement over the known middle majorant on the original residual? Keep both correction bands, both omitted-modulus sums and the after-N range. Expected output: an actual full-middle upper estimate, or a precise failure of a proposed pairing. Falsifier: a surviving unpaid component at the same exponent, or a hidden assumed decay of u(N,H). This decides whether the mechanism merits further quantitative investment; today remains PENDING until a report exists.

**Finite Wheel & Incidence, next protected FINITE-AC:** resume L1-L4, where normalized complete-prime averaging preserves the signed scalar. Exact question: does a genuine factor-conditioned PARTIAL completion create a new restriction on the original finite-C source after its complete missing-corner and historical return are restored? Keep X=R^2-1 and the original strict historical K. Expected output: an explicit arithmetic inequality not already implied by the coherent completion identity, or a source-exact no-go. Falsifier: recombination again equals the same M(X), or the removed corner carries the entire apparent saving. On the following CORR4 turn, use C54 as a falsification test, not as an invitation to repeat the log-wheel scan.

**Prime Census Laboratory, distinct source support:** independently test Owner LC4's exact JOH compression at development N=512,1024 and held-out N=2048,4096 with a=5, as previously requested but not completed by today's CORR4 work. Use certified Li_2 floor-arrival intervals, actual primes, initial/final partial cells and the exact displacement error. Expected output: exact G=U+E_place certificates and 0<=E_place<=pi(N)log N, or the first violated identity with its endpoint. Falsifier: uncertain rounding at an arrival treated as exact. Do not enlarge the range or fit an RH exponent. This qualifies a distinct paid sector for review and balances support work away from repeated CORR4/NYMAN tests.

**Adversarial Referee, new high-consequence audit:** reconstruct C53-C55 from the statement and original source. Audit absolute convergence and zero mean, finite conic extraction, rational-to-integer monoid saturation, fixed-interval semiprime counts, exact floor grouping, every p<=y_R rule, whole-prefix C_star, target parity and complementary labels. Attempt to break the proof with y_R=sqrt X/log X, arbitrary fixed labels, or a prescribed too-small envelope constant. The latter is outside the claim, not a refutation. Expected output: ACCEPT_WITH_SCOPE, a specific repair, or a counterexample. A failure of C53's integer step or C54's uniform capacity would restore the corresponding prime-rule avenue; acceptance retires it at the displayed scope. C50-C51, Owner RC5 and Wheel QC1-QC3 remain separate queued reviews, not implicitly complete.

**Lean Verification, at most two existing qualified tasks:** first retain #1094's exact-head green evidence and obtain separate scope review without claiming draft means merged; repair only an actual changed-head failure. No new proof is needed merely to restate C49. The second possible implementation remains previously Referee-accepted C45's original Mellin/localized exact-head lower bound, ONLY if its actual analytic source prerequisites are available and the theorem is still absent. Expected output: the source-faithful declaration and full CI/axiom evidence, or an exact missing analytic bridge. Stop on a missing integrability/zero hypothesis or substituted abstract source. New C53-C55 are NOT yet qualified implementation assignments; do not formalize them ahead of independent review solely because the finite certificates are easy.

### I. Lean And PR Status

The fresh open/draft collection contains **only #1094**, draft and unmerged, branch `agent/lean-verification/20261105-nyman-correction-energy`, head **1ea4a8a4308976721a3841998d6c3a4554f7a9c9**. Its theorem source blob is **e5453cd32c3c4ebf9ebf41927bcb92e534b2ece7**. All 12 returned exact-head workflows succeeded. The actual tested synthetic merge **45a4bc4b5995d908328e5aec4c12a6a4eec946ec** has parents main and that proof head, and tree **e98a257a8258c42baae89222c999f4dfd544546a**, exactly equal to the proof-head tree.

I read the actual dedicated [run 42011040577 / job 127189858614](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42011040577/job/127189858614) log and the source theorem statements. Warning-fatal Lean 4.34.1 compilation passed. All eight printed terminal declarations depend only on **propext, Classical.choice, Quot.sound**. The audit explicitly reports PASS. Unchanged prerequisites were cached; no full cold rebuild is claimed. The general result is

```text
K>=1, d_k=0 for 2<=k<=3K:
sum_(K<=m<=3K) [z-sum_(2<=k<=N)d_k*(m mod k)/k]^2/[m(m+1)]
  >= (6K/81) [sum_(2<=k<=N)d_k/k]^2.
```

The implementation also retains the exact signed base-plus-correction split. This is **PROVED_IN_LEAN / CI_GREEN / DRAFT_PR**, NOT MERGED and not separate Referee acceptance. Neither full-norm upper control nor C50-C51 is a theorem of this PR.

**#1093 is MERGED on main.** Final proof head **a54f0cf9535c548920dae3412e3fbe6d6584e029**, all 12 returned head-associated workflows successful. Dedicated [run 41955044802 / job 127007831273](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41955044802/job/127007831273) was read directly: warning-fatal compilation, eight original-return declarations and standard terminal axioms passed. Tested merge **779336cefaf99d04bf48b837340a076d40aebdd3** has the SAME complete tree as current main. Thus the source-exact flat return and exact-head moment criterion are established, not the missing middle norm.

The nine workflows attached directly to current main are all successful. Recent merge metadata also confirms #1092 routing, #1091 fixed-slot construction, #1090 Nyman invariant and #1085/#1087 moving-mass work are merged; stale draft language in older prose is superseded. I do not claim to have freshly re-audited every historical OAI dependency on this unrelated route. No active failed check needing repair was found. Human merge remains the gate. No Lean execution occurred locally and this Coordinator created no proof branch, PR or source edit.

### J. Next-Run Resume Capsule

```text
RUN: 20261105-coordinator-1; scheduled 07:10:01 EST; RUN_ID_UNAVAILABLE.
MAIN: ff620da3c0d2c29585805960c6be183c07f16556.
POLICY: NO_PIGEONHOLING_ROUTE_SELECTOR_V1;
        ffd8f1c65cc4da656174956d4e03b48bea46768b.
REPORT_SNAPSHOT: d64e2a707a60e4445a2c948157fe12a45e0a6fbb.
GATE: SEARCH_BROAD; inherited strict-slot result retained; NEW_GAIN=NONE.
SELECTED: CORR4 fixed-label prime-rule relaxation, not mandatory OAI.
C53: saturated columns v_n=(M(floor(n/q_i^2))) positively generate Z^(s+1).
C54: for y_R->infinity, y_R=o(sqrt X), sparse semiprime orbit flips realize
     every O(X^b) parity target, preserving all prime signs/history/rules and
     an EVERY-prefix O(z^b) envelope with a possibly enlarged constant.
C55: exact fixed-label cap saturation with genuine endpoint; scoped no-go.
C56: all prime rules through sqrt X force f=mu; boundary control only.
C57: 8 exact certificates, 8 sparse fixtures at R=10^6, y=24999;
     444 changed-site occurrences, 1400 affected rule-edge checks;
     complement q=11,13 can move, so do not drop it.
REVIEW: C53-C56 PAPER_PROOF / SELF_AUDIT; independent Referee PENDING.
FORMAL: #1094 CI_GREEN/DRAFT at 1ea4a8a4308976721a3841998d6c3a4554f7a9c9;
     finite Nyman component only. #1093 MERGED; source return not norm bound.
FIRST_OPEN: full genuine CORR4 mixed bill, original NYMAN joint middle,
     SAT/JOH signed source supplier; no new upper estimate established.
NEXT_PRIMARY: Owner VF-LOW; Analytic NYMAN; Wheel FINITE-AC.
NEXT_SUPPORT: Census JOH LC4 fixtures; Referee C53-C55;
     Lean preserve #1094 review gate, optionally accepted C45 if ready.
ANALYTIC_TODAY: PENDING at snapshot; Nov4 exact carry-forward, no launch inferred.
EXTERNAL: 038018145c0fddb2f6306c0712373adf9cd1ea52, latest entry Oct18.
RESUME_TASK: audit finite integer monoid and same-exponent envelope, then
     demand a proposed genuine restriction that the explicit flips violate.
NO_REPEAT: unchanged large wheel scans, tiny slot denominator optimization,
     already merged Nyman identities, or isolated component estimates.
```

The early checkpoint was committed atomically to both mirrors in **c96c464f9c4aabeca6b4c6d675bc0506bd2154cb**, common blob **94376539b133b982af4f992cc3547e297615d29f**; pinned PM readback matched exactly. All of that checkpoint is preserved above. This synthesis is not declared published until its own commit and both readbacks succeed. No other agent was launched and no future work is represented as running.

### Appendix. Exact Executed Verifier

The following standard-library source is the final executed verifier, with the SHA-256 stated in D8. The discovery optimizer is not required.

```python
"""Exact finite checks for a scoped CORR4 relaxation, not an RH experiment."""

from math import isqrt


LABELS = (1, 3, 5, 7)
CERTIFICATES = {
    (0, -1): {3: 1},
    (0, 1): {1: 1},
    (1, -1): {26: 1, 98: 1},
    (1, 1): {1: 1, 10: 1},
    (2, -1): {10: 1, 98: 1},
    (2, 1): {1: 1, 26: 1},
    (3, -1): {10: 2, 26: 2, 219: 1},
    (3, 1): {10: 1, 26: 1, 95: 1},
}


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def next_prime(n):
    while not prime(n):
        n += 1
    return n


def mobius(n):
    sign, d = 1, 2
    while d * d <= n:
        if n % d == 0:
            n //= d
            sign = -sign
            if n % d == 0:
                return 0
        d += 1
    return -sign if n > 1 else sign


MU = [0] + [mobius(n) for n in range(1, 1001)]
M = [0]
for value in MU[1:]:
    M.append(M[-1] + value)


def column(n, labels=LABELS):
    return tuple(M[n // (q*q)] for q in labels)


def pick_core(x, n, used, rule_limit):
    lo, hi = x // (n + 1) + 1, x // n
    mid = (lo + hi) // 2
    p = next_prime(9 * isqrt(mid) // 10)
    while True:
        q = next_prime(mid // p + 1)
        a = p * q
        if lo <= a <= hi and a not in used and p != q:
            assert min(p, q) > rule_limit
            used.add(a)
            return a, p, q
        p = next_prime(p + 1)


def main():
    for (i, sign), terms in CERTIFICATES.items():
        total = tuple(sum(c * column(n)[j] for n, c in terms.items())
                      for j in range(4))
        assert total == tuple(sign * int(i == j) for j in range(4))
    for i, q in enumerate(LABELS):
        jump = tuple(column(q*q)[j] - column(q*q-1)[j] for j in range(4))
        assert jump == tuple(int(i == j) for j in range(4))
    print("PASS: eight exact nonnegative integer certificates and four unit jumps")
    for n in (1, 3, 10, 26, 95, 98, 219):
        print("column", n, column(n))

    r = 10**6
    x = r*r - 1
    y = isqrt(x) // x.bit_length()
    rules = [p for p in range(2, y+1) if prime(p)]
    assert y == 24999 and max(n for t in CERTIFICATES.values() for n in t) < y
    print("Rule cutoff", y, "number of enforced prime rules", len(rules))
    total_edges = 0
    total_sites = 0
    for (i, sign), terms in CERTIFICATES.items():
        used, cores, delta = set(), [], {}
        for n, count in terms.items():
            for _ in range(count):
                a, p, q = pick_core(x, n, used, y)
                assert a > r and x // a == n
                assert prime(p) and prime(q) and p != q
                cores.append((n, a, p, q))
                for d in range(1, n+1):
                    if MU[d]:
                        site = a*d
                        assert site not in delta and site <= x
                        # All factors of d are <=219<y<p,q; hence mu(a*d)=mu(d).
                        delta[site] = -2*MU[d]
        actual = tuple(sum(change for site, change in delta.items()
                           if site <= x // (q*q)) for q in LABELS)
        expected = tuple(-2*sign*int(i == j) for j in range(4))
        assert actual == expected
        assert all(site >= r for site in delta)
        edges = 0
        for site, change in delta.items():
            for p in rules:
                if site % p != 0 and site*p <= x:
                    assert delta.get(site*p, 0) == -change
                    edges += 1
                if site % p == 0:
                    parent = site // p
                    assert parent % p != 0
                    assert delta.get(parent, 0) == -change
                    edges += 1
        # Every edge with a changed endpoint was inspected. Unchanged edges
        # retain the genuine Mobius rule; squareful sites remain zero.
        first_core = cores[0]
        _, a, p, q = first_core
        assert p <= isqrt(x) and p > y and delta[a] == -2
        # Adding this omitted large-prime rule forces f(p*q)=+1, but f(a)=-1.
        assert q not in delta
        assert 1 + delta[a] != -(-1 + delta.get(q, 0))
        if i != 0:
            assert sum(delta.values()) == 0
        complement = tuple(sum(change for site, change in delta.items()
                               if site <= x // (q*q)) for q in (11, 13, 17))
        print("fixture", (i, sign), "cores", cores, "changed_sites", len(delta),
              "checked_edges", edges, "prefix_change", actual,
              "other_daughter_changes_11_13_17", complement)
        total_edges += edges
        total_sites += len(delta)

    # A proper incomplete orbit can violate a rule that the full orbit preserves.
    a, p, q = pick_core(x, 10, set(), y)
    assert 2*a <= x
    incomplete = {a: -2}
    assert incomplete.get(2*a, 0) != -incomplete[a]
    print("PASS: eight sparse physical fixtures,", total_sites,
          "changed sites and", total_edges, "affected rule-edge checks")
    print("PASS: six endpoint-preserving daughter moves; large-prime and partial-orbit controls")
    print("Scope: no full-prefix numerical Mertens scan, no all-label cap or endpoint gain")


if __name__ == "__main__":
    main()
```

Exact executed output:

```text
PASS: eight exact nonnegative integer certificates and four unit jumps
column 1 (1, 0, 0, 0)
column 3 (-1, 0, 0, 0)
column 10 (-1, 1, 0, 0)
column 26 (-1, 0, 1, 0)
column 95 (2, -1, -1, 1)
column 98 (1, -1, -1, 0)
column 219 (4, -2, -2, -1)
Rule cutoff 24999 number of enforced prime rules 2762
fixture (0, -1) cores [(3, 291671110331, 486061, 600071)] changed_sites 3 checked_edges 4 prefix_change (2, 0, 0, 0) other_daughter_changes_11_13_17 (0, 0, 0)
fixture (0, 1) cores [(1, 750010430969, 779477, 962197)] changed_sites 1 checked_edges 0 prefix_change (-2, 0, 0, 0) other_daughter_changes_11_13_17 (0, 0, 0)
fixture (1, -1) cores [(26, 37749473851, 174877, 215863), (98, 10153438453, 90697, 111949)] changed_sites 78 checked_edges 246 prefix_change (0, 2, 0, 0) other_daughter_changes_11_13_17 (0, 0, 0)
fixture (1, 1) cores [(1, 750010430969, 779477, 962197), (10, 95455969207, 278063, 343289)] changed_sites 8 checked_edges 16 prefix_change (0, -2, 0, 0) other_daughter_changes_11_13_17 (0, 0, 0)
fixture (2, -1) cores [(10, 95455969207, 278063, 343289), (98, 10153438453, 90697, 111949)] changed_sites 68 checked_edges 216 prefix_change (0, 0, 2, 0) other_daughter_changes_11_13_17 (0, 0, 0)
fixture (2, 1) cores [(1, 750010430969, 779477, 962197), (26, 37749473851, 174877, 215863)] changed_sites 18 checked_edges 46 prefix_change (0, 0, -2, 0) other_daughter_changes_11_13_17 (0, 0, 0)
fixture (3, -1) cores [(10, 95455969207, 278063, 343289), (10, 95458715519, 278071, 343289), (26, 37749473851, 174877, 215863), (26, 37749429799, 174893, 215843), (219, 4557443327, 60757, 75011)] changed_sites 184 checked_edges 612 prefix_change (0, 0, 0, 2) other_daughter_changes_11_13_17 (-2, -2, 0)
fixture (3, 1) cores [(10, 95455969207, 278063, 343289), (26, 37749473851, 174877, 215863), (95, 10474131719, 92107, 113717)] changed_sites 84 checked_edges 260 prefix_change (0, 0, 0, -2) other_daughter_changes_11_13_17 (0, 0, 0)
PASS: eight sparse physical fixtures, 444 changed sites and 1400 affected rule-edge checks
PASS: six endpoint-preserving daughter moves; large-prime and partial-orbit controls
Scope: no full-prefix numerical Mertens scan, no all-label cap or endpoint gain
```

### Closeout Freshness Check

At 2026-11-05 12:39:16 UTC, main remains `ff620da3c0d2c29585805960c6be183c07f16556`. The report branch before this synthesis is exactly our early-checkpoint commit `c96c464f9c4aabeca6b4c6d675bc0506bd2154cb`; no newer upstream report or Analytic execution is present. Both current Coordinator blobs were fetched and match the checkpoint byte-for-byte. The sole open PR remains #1094, draft at the unchanged verified head. No source-dependent conclusion needs revision. Research is finished; publication is certified only in the subsequent receipt.

### Verified Publication Receipt - 20261105-coordinator-1

**Execution COMPLETE; substantive synthesis PUBLISHED_AND_READBACK_VERIFIED. Mathematical objective OPEN; C53-C56 independent review PENDING.**

The substantive report was committed atomically to both authorized mirrors in **7773273e5aafe248a35b0827553ce22215b9823d** at **2026-11-05T12:39:48Z**. Immutable readback of BOTH files matched all **54,078 ASCII characters** exactly, with common blob **77e86a036fc291f47699641ab116100162e32383**. Commit inspection confirms only the two Coordinator reports changed, each with **558 additions and zero deletions**. The early checkpoint remains an exact prefix. A-J sections, Markdown fences, embedded executed-script bytes and finite test output were validated. Final script syntax checks passed; no research computation remains running.

This receipt records that already successful substantive publication; its own commit will be checked separately. The final outcome is the scoped C53-C55 paper argument, C56 limiting control and C57 exact finite evidence, not an independently reviewed new arithmetic upper bound. The same complete-source complement and all stated quantifier limitations remain. #1094 remains a verified draft component theorem, not a merged or full-residual result. No source, main, policy, other role report, proof branch, PR, workflow, permission or schedule was modified, and no other agent was launched.

Receipt prepared 2026-11-05 12:40:50 UTC.


---

## Scheduled Continuation Checkpoint - 20261105-coordinator-2

**PARTIAL / IN_PROGRESS.** Trigger: SCHEDULED, 2026-11-05 15:13:00 EST (-0500), America/New_York. Platform run ID: RUN_ID_UNAVAILABLE. Checkpoint UTC: 2026-11-05 20:18:07 UTC.

The complete residual, rather than an isolated favorable or unfavorable component, remains the mathematical frontier. Main is now `884de7a1fa7687d483a7b5272bff6c9d53790367` (2026-11-05T13:35:24Z), merging #1094's high-supported Nyman correction-energy theorem. This supersedes the earlier synthesis's DRAFT/UNMERGED status only; no full-norm estimate or endpoint improvement follows. Exact-head CI and today's later claims are under review.

Authority consumed: AGENTS blob `547dda0d9456e7a4e1165dc72d59da6f70d5c023`; contract `7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c`; independent multi-front policy `ffd8f1c65cc4da656174956d4e03b48bea46768b`. Protected nine-route coverage and SEARCH_BROAD remain. This invocation will independently test an exact cross-route mechanism after the latest handoffs are assessed; no new result is asserted yet.

Reports snapshot `d4ae547b8783aefdb0e7cf16f8d95746863b7464` contains November 4 and 5 reports for all six specialists and both Coordinator mirrors. All have been retrieved, including today's Analytic report, which was PENDING at the earlier Coordinator snapshot. Relevant sections and the external inbox are being read; retrieval alone is not acceptance. External inbox blob `038018145c0fddb2f6306c0712373adf9cd1ea52` has no newer entry than October 18. Only open PR at intake: #1095, Euler axiom-audit repair, head `46e68178192c6e429a02abee9d5b8ebca5de46c8`; no review/merge conclusion yet.

Independent derivation, portfolio decisions, source verification, assignments and final readback remain PENDING. Canonical VF bound and new complete-endpoint gain remain OPEN. No Lean source, policy, other report, proof branch, PR, schedule or permission will be changed by this role; no other agent is launched. Earlier sections and evidence are preserved verbatim.


---

## Research Synthesis - 20261105-coordinator-2

Actual invocation: **SCHEDULED, 2026-11-05 15:13:00 EST (-0500), America/New_York; RUN_ID_UNAVAILABLE**. This appends one continuation to the existing complete mirrors, not a new launch. Research is finished; publication is PENDING until the verified receipt below. Earlier reports and their time-specific statuses are preserved.

### A. What Changed Mathematically?

**A fixed finite signed combination of polynomial-head flat tapers cannot repair their all-scale norm obstruction.** The shortest head whose combined coefficient is nonzero controls the exact logarithmic-limsup exponent of the complete pre-correction residual. This remains true when the weights cancel the explicit prime-power term altogether, and when the mixed terms are negative. The proof is not a triangle lower bound: a hypothetical cancellation would force a sequence of actual zeta zeros toward 1 through one of finitely many strict contractions.

For the precise original-residue families in D, with fixed shortest exponent theta_1 in (0,1),

```text
limsup_(N->infinity, 6|N) log(1+E_pre(N))/log N
    = 1-2*theta_1*(1-beta_*),
beta_* = sup Re(actual nontrivial zeta zeros).                 (C60)
```

In particular this exponent is at least 1-theta_1>0. For every 0<delta<1-theta_1 and every C,N0, some multiple of six N>=N0 has E_full(N)>C*N^(1-theta_1-delta). This is not divergence at every N. Fixed ordinary affine combinations of the individually normalized tapers satisfy the same restriction (C61).

**New C58-C61: PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED.** C59's source formulas are IDENTITY_ONLY until used in the inverse estimate. C62 is exact FINITE_COMPUTATION for the source algebra, with separate non-certified decimal diagnostics. The finding is new relative to the retrieved two-day reports; no literature-originality claim is made. No additional complete-endpoint exponent improvement, canonical VF estimate or RH proof is established.

Today's later Analytic SP1-SP5 are now independently accepted on paper by Referee-5; the morning Coordinator's pending Analytic stage is superseded. PR #1094 is now human-merged and verified at its finite component scope. PR #1095, initially green but unmerged during intake, was human-merged during this execution; its repaired Euler axiom audit has the exact merged tree. Those formal developments do not certify today's analytic argument.

### B. Current Proof Objective And Authority

Final pinned main: **1667c3cf9b4e898bb9afd62ec48e24610b2156ab**, committed 2026-11-05T20:32:22Z; tree **6351bbacd22d7abb34eefed1e2cbf5f674642010**. Intake main was **884de7a1fa7687d483a7b5272bff6c9d53790367**, committed 2026-11-05T13:35:24Z; tree e98a257a8258c42baae89222c999f4dfd544546a. The intervening #1095 merge changes only `.github/workflows/euler-fractional-coupled.yml` and two audit/test scripts; no mathematical source or policy changes. Both authority files were fetched again at the final main: AGENTS blob **547dda0d9456e7a4e1165dc72d59da6f70d5c023** and CURRENT_PROOF_CONTRACT blob **7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c** are unchanged. Independent multi-front policy blob **ffd8f1c65cc4da656174956d4e03b48bea46768b** controls route choice. Task selector, breadth, complete-return, research-engine, role and operating/cadence documents were retrieved at intake and are unchanged by this merge.

Canonical arithmetic target, inspected in `research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean`:

```text
VFCanonicalSquareVonKochStatement:
exists C >= 0, forall natural R >= 2,
  |pi(R^2)-VF_can(R^2)| <= C*R*log R.
```

It remains OPEN. The actual declaration `riemannHypothesis_of_vfCanonicalSquare` still takes `ClassicalVonKochRHCriterion` explicitly; the coordinate equivalence is not a newly proved prime bound. Existing fixed-count slot results keep their own certified scope. This invocation claims no new gain beyond the inherited result and does not optimize its denominator.

Deployment acknowledgement: **NO_PIGEONHOLING_ROUTE_SELECTOR_V1**, sources above; selected task **NYMAN-FINITE-SIGNED-PROFILE-ESCAPE**, resuming Analytic SP1-SP5 and Referee-6 rather than a compulsory OAI ticket. Independent new step: finite-branch pole propagation, including exact prime-term elimination. Protected route rotation is unchanged; no other agent was launched.

Original sources read at this main:

| Source | Blob | Actual role |
| --- | --- | --- |
| research/NYMAN_HIGH_COEFFICIENT_INVARIANT_20261104.lean | 2da630c1d5fb9302e2097ec1e170cf41c2b40609 | Original residues, residual, logarithmic kernel and finite divisor identities |
| research/NYMAN_FLAT_TAPER_RETURN_20261104.lean | 2d23721027ecc44e85b7add02fc632b482f03352 | Complete return with moment defect, exact-head criterion |
| research/NYMAN_CORRECTION_ENERGY_20261105.lean | e5453cd32c3c4ebf9ebf41927bcb92e534b2ece7 | Component lower bound, not the full norm |
| research/MERTENS_CONVERSE_IDENTIFICATION.lean | 768c8255850bf4074aff265c3fe17a1f5c43979b | Existing actual-zero/Mertens exponent translator; no numerical boundary supplied |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb | Canonical statement and conditional classical interface |
| research/EULER_RANK_ONE_FRACTIONAL_ROWS_20261027.lean | e482711a3f55c1f59fc771f108671477f51732f2 | Nonsymmetric original kernel and complete rank-one residual |
| research/EULER_SELF_DUAL_FINITE_C_BRIDGE_20261027.lean | e97561ef330a9996fd807d8910369f0698147b01 | Exact ordered convolution-to-floor map, not a bound |
| research/CORR4_OAI_POWER_MIXED_TAIL_GATE_20261025.lean | bb0ee1252e7ba10c44ae5b8d827573d6c581b73a | Explicit conditional mixed-tail consumer |

### C. Competing Mechanism Portfolio

**1. Chronological non-divisor prime response: CONTINUE at proper-sector scope.** Concept: spend actual earlier prime coefficients fractionally and once, keeping unfinished chronological packets. Independent input: ordinary effective PNT supplies the donor interval counts in Owner CR1-CR2. Exact return: -D_T=C_F(T)+Q(T), with Q(T)=o(T/log T) for the stated sparse selections; the canonical phase and full square remain. First missing step: new control of the dense original complement or a genuine simultaneous allocation with sufficiently small chronological return. Support: paper CR1-CR3 and the exact finite donor checks. Obstruction: a sparse per-label result cannot be summed over the dense three-prime rectangle without congestion and return costs. Decisive test: a proposed dense allocation must pay every donor once and bound every unfinished prefix. Owner leads, with Referee review pending. This is real prime/chronology information, not a Mobius norm reformulation.

**2. Joint historical bilinear control: REVISE, retaining signed masks.** Concept: exploit genuine factor geometry in the complete floor source before taking block norms. Independent input needed: a new arithmetic restriction on the recombined form, beyond exact Mobius inversion and inherited prefix bounds. Consumer: the original finite-C/Euler chain with strict historical K_R, or the separately inspected CORR4 full mixed-tail consumer; those are different source contracts, not interchangeable norms. First missing step: an independently paid uniform signed remainder. Support: Wheel's exact P1 four-block return and paper P2 asymptotic. Obstruction: all four actual blocks have size R^2/log^2 R and cancel in the leading matrix [[-1,1],[1,-1]]; bounding them separately at R sqrt(K_R) is false. CORR4 fixed-label relaxations also leave freedom (C53-C55 still review pending). Decisive experiment: require a new proposed packet to mix the obstructing classes, then restore its entire complement before assessing its gain. Wheel leads; no extra team-wide route is imposed.

**3. Nyman approximation with changed constraints: REVISE; fixed finite-mixture repair RETIRED at its stated all-scale scope, subject to independent review.** Concept: allow genuine scale-dependent profiles, reciprocal-moment leakage or a sufficiently sparse sequence, with the original full Hilbert norm. Independent input needed: an upper bound for the entire new residual, plus the exact leakage/tail/consumer calculation. Support: the unrestricted basis, C45-C46's localized consumer, and Referee-8's source-realizable moment-defect tradeoff. Obstructions: SP1-SP5 and C58-C61 eliminate high-correction rearrangement and fixed finite taper superposition as all-scale bounded-norm repairs. Optimizing one lower certificate is not an upper estimate. Decisive experiment: choose one explicitly different coefficient rule and test its head, orthogonal pre-residual, corrections and after-N return together. Analytic leads on its next NYMAN turn, not at the expense of the due OAI/CODIV rotation. This remains exploratory: there is no surviving proved norm supplier.

These are three distinct proposed sources of information, not three claimed closing theorems. No new independent mechanism is promoted to a program-wide priority. All nine protected routes remain active as investigations.

### D. Conceptual Research Performed

#### D1. C58-C59: Exact finite-profile carrier and full return

Fix an integer d>=1, distinct real exponents

```text
0<theta_1<...<theta_d<1,
alpha_i in R\{0}, fixed independently of N,
A=sum_i alpha_i,
c_star=sum_i alpha_i*(1-theta_i) != 0.
```

Combine equal exponents first and delete any resulting zero coefficient. For every sufficiently large multiple of six N=6K put H_i=floor(N^theta_i), so 2<=H_i<N/2. Define

```text
ell_i=log(N/H_i),                  ell=sum_i alpha_i*ell_i,
F(k)=mu(k)*sum_i alpha_i*log(N/max(H_i,k)),  1<=k<=N,
u=sum_(k=1..N) F(k)/k,
h(k)=0 for 2<=k<=N/2,             sum_(k=2..N)h(k)/k=u,
c(k)=(h(k)-F(k))/ell,             2<=k<=N,
r_N(m)=1-sum_(k=2..N)c(k)*(m mod k)/k,
E_pre(N)=sum_(K<=m<3K)r_N(m)^2/[m(m+1)],
E_full(N)=sum_(m>=1)r_N(m)^2/[m(m+1)].
```

Here h is ANY finite real correction satisfying the displayed conditions; it may vary with N. The sign of ell is immaterial. It is nonzero eventually because ell=c_star*log N+O(N^(-theta_1)). Each full norm is finite since the actual finite residue sum is bounded and periodic at fixed N. Uniform boundedness is NOT inferred. Optional mean centering is allowed but not needed for the obstruction.

Use the already inspected definition

```text
U_B(m)=sum_(B<k<=m)mu(k)*log(B/k)*floor(m/k).
```

Linearity of `nyman_flat_complete_return`, including F(1)=ell, gives the complete identity, for EVERY m>=1:

```text
ell*r_N(m)=m*(u-sum h(k)/k)
           +A*U_N(m)-sum_i alpha_i*U_(H_i)(m)
           +sum_(k=2..N)h(k)*floor(m/k).                    (C59a)
```

Nothing after N is dropped from this equality. Under the stated moment and support conditions,

```text
ell*r_N(m)=-sum_i alpha_i*U_(H_i)(m),  1<=m<N/2;
r_N(m)=0,                              1<=m<=H_1.           (C59b)
```

Thus the whole pre-block, not a correction component, is independent of h. All cross-profile and base/correction interactions remain inside r_N before squaring. For A=0 the U_N and explicit prime-power terms cancel exactly; this important hostile case is INCLUDED.

#### D2. Full-residual smooth probe

Set T(x)=sum_(k<=x)mu(k)log(x/k)/k and V(x)=1-T(x). Choose a fixed nonnegative normalized smooth probe g supported on [1/6,1/2], w=-g', and

```text
w_N(t)=N^(-2)*w(t/N),
P_g(N)=N^(-1)*sum_n Lambda(n)*g(n/N)-1,
L_N(r)=integral w_N(t)*r_N(floor t) dt,
Q_N(H)=sum_(k<=H)mu(k)log(H/k)
       *integral w_N(t)*({t/k}-1/2) dt,
B_g=integral v^2*w(v)^2 dv > 0.
```

For a prescribed number J of integrations by parts one may explicitly use the polynomial probe from Referee-6: g(v)=C_l(3v-1/2)^l(3/2-3v)^l on that interval, zero elsewhere, l>=J+3, C_l=3(2l+1)!/(l!)^2. Every parameter is fixed before N; no uniformity as theta_d tends to 1 is claimed.

The same finite divisor identity used in SP1, now summed with the ORIGINAL alpha_i, gives

```text
sum_i alpha_i*V(H_i)+A*P_g(N)
    =-ell*L_N(r)-sum_i alpha_i*Q_N(H_i).                    (C59c)
```

This can be checked directly from U_H(floor t)=log H+psi(t)-t*T(H)+sum_(k<=H)mu(k)log(H/k){t/k}. The prime-power coefficient is A, not automatically 1. The k=1 term of Q is retained even though the discrete k=1 residue vanishes.

The exact norm correspondence and Fourier estimate give

```text
|L_N(r)| <= sqrt(B_g*E_pre(N)/N),
|Q_N(H)| <= C_(g,J)*(H/N)^(J+1),
|sum_i alpha_i V(H_i)+A P_g(N)|
 <= |ell| sqrt(B_g E_pre(N)/N)
      +C_(g,J)*sum_i |alpha_i|*(H_i/N)^(J+1).              (C59d)
```

For completeness, the periodic Fourier coefficient after J integrations is bounded by a constant times k^J/N^(J+1). Summing k^J log(H/k) over k<=H costs at most H^(J+1) for J>=1, using log(H/k)<=H/k. Absolute convergence after smoothing justifies the exchange. The continuous norm is exactly integral_(N/6..N/2)r_N(floor t)^2*t^(-2)dt. This is a lower/inverse bound on the complete residual; it never asserts E_component<=E_full.

#### D3. C58: Finite-branch pole-contraction lemma

Let 0<=kappa<1 with kappa>1-2theta_1 and put a=(1-kappa)/2, so 0<a<theta_1. Suppose, explicitly as an OPEN UPPER PREMISE, that for every epsilon>0 there are C_epsilon,N_epsilon such that

```text
E_pre(N)<=C_epsilon*N^(kappa+epsilon)
for EVERY multiple of six N>=N_epsilon.                   (UPPER)
```

Choose J with (J+1)(1-theta_d)>a. Equation C59d implies decay of the sampled expression. To remove both floor heads and the six-step mesh, use the elementary bounds

```text
|V'(x)| <= (1+log x)/x,
|P_g'(y)| <= C_g*log(2y)/y.
```

The first follows from differentiating T; T is continuous across integer changes because its new term has log 1=0. The second follows by differentiating the finite smooth sum and using Lambda(n)<=log n. Replacing H_i by N^theta_i costs O(log N/N^theta_i); moving to a real scale within six costs O(log N/N). They are smaller than N^(-a+epsilon). Consequently

```text
W(x):=sum_i alpha_i V(x^theta_i)+A P_g(x)
       =O_epsilon(x^(-a+epsilon)),  x>=1.                  (C58a)
```

Its Mellin transform is holomorphic on Re(s)>-a, by dominated convergence on compact subsets. On Re(s)>0 direct absolutely convergent integration gives, with ghat(z)=integral g(v)v^(z-1)dv,

```text
integral_1^infinity W(x)*x^(-s-1) dx
 = -sum_i alpha_i*theta_i/[s^2*zeta(1+s/theta_i)]
   -A*ghat(1+s)*zeta'(1+s)/zeta(1+s).                     (C58b)
```

Indeed the V term has transform 1/s-theta_i/[s^2 zeta(1+s/theta_i)]. The prime term is -ghat(1+s)zeta'/zeta(1+s)-1/s, with no lower-limit correction because the probe support lies below 1. The scalar poles cancel since A=sum alpha_i. The apparent singularity at s=0 is removable, also directly from the residue-one pole of zeta and ghat(1)=1.

Now suppose an actual nontrivial zero rho satisfies Re(rho)>1-a/theta_1. At s_0=theta_1*(rho-1), the i=1 reciprocal term has a nonremovable pole, since alpha_1!=0 and s_0!=0. Holomorphy forces another summand to have a pole there. Hence AT LEAST ONE of

```text
1+(theta_1/theta_i)*(rho-1),  i>1;
1+theta_1*(rho-1),           if A!=0
```

must also be a zeta zero. A vanishing ghat can remove an available cancelling pole, never create another escape. Multiple zeros cause no difficulty: the nonzero distinguished reciprocal term still has a pole that requires another singular summand. We do not assert that their residues actually cancel, only the necessary zero condition.

Every possible multiplier belongs to a FINITE set of positive numbers strictly below 1. The new zero has larger real part, remains within the same offending half-plane, and has strictly smaller distance to 1. Repeat the argument with the new zero in the distinguished i=1 term. If q is the maximum allowed multiplier, the distances are at most q^j|rho-1| and tend to zero. If the set is empty the first pole is already impossible. But (z-1)zeta(z) is holomorphic and nonzero near z=1. This contradiction proves

```text
UPPER ==> beta_* <= 1-(1-kappa)/(2theta_1).                (C58c)
```

This is the genuinely new extension of the single-head argument: pole cancellation may branch among several reciprocal-zeta factors, and may have NO logarithmic-derivative term when A=0, but cannot cycle or terminate outside a zero-free neighborhood of 1. Signs and positivity of the mixture weights play no role.

External analytic facts used, independently checked against [NIST DLMF 25.2](https://dlmf.nist.gov/25.2) and [25.10](https://dlmf.nist.gov/25.10): meromorphic continuation of actual zeta, its sole simple residue-one pole at 1, and existence of critical-line zeros. The Dirichlet-series/Mellin identities above are derived in their absolutely convergent half-plane before continuation. No RH, zero-density estimate, rightmost attained zero, independence model or new prime-error bound is assumed.

#### D4. C60: Sharp exponent and scoped no-go

Let p=1-2theta_1(1-beta_*), with 1/2<=beta_*<=1. Then p>=1-theta_1>0. If the logarithmic limsup of E_pre were less than p, choose kappa strictly between max(that limsup,0,1-2theta_1) and p. It is <1. The eventual power bound implied by the limsup and C58c would give a strict upper boundary smaller than beta_*, contradicting its definition as a supremum. No maximum zero is required.

For the reverse inequality, if beta_*<1 choose beta_*<b<1. The EXISTING `growthAtMost_of_strip` supplies |M(x)|<=C_b x^b (choose its positive exponent loss within b-beta_*). Abel summation of sum_(H<k<=y)mu(k)log(k/H), followed by the floor-quotient sum, gives the already used estimate

```text
|U_H(m)| <= C_b*K_b*m*H^(b-1),
K_b=(2-b)/(1-b)^2.
```

All alpha_i are fixed and H_i>=H_1. Thus C59b and |ell| asymptotic to |c_star|log N yield

```text
E_pre(N) <= C_(b,alpha,theta)*N*H_1^(2b-2)/(log N)^2.
```

Let b decrease to beta_*. If beta_*=1, the elementary bound |U_H(m)|=O(N log^2 N) on the pre-block gives limsup<=1. This proves C60 in A. It determines the exponent in terms of the existing UNKNOWN beta_*, not a new value of that boundary. The upper result is for E_pre only; it is NOT an upper result for E_full.

Critical-line zeros make the all-scale bounded-norm supplier false for EVERY such fixed finite mixture. For kappa in [1-theta_1,1), both directions give the precise equivalence

```text
E_pre(N)=O_epsilon(N^(kappa+epsilon)) for every epsilon>0
iff beta_*<=1-(1-kappa)/(2theta_1).                        (C60b)
```

At kappa=1-theta_1 this PRE-block rate is TARGET_EQUIVALENT to RH. It is not a smaller assumed supplier. No conclusion is made about arbitrary sparse sequences, coefficients depending freely on N, theta_i moving with N, infinitely/growingly many profiles, low-supported corrections, a moment defect, or the unrestricted optimized basis. The c_star=0 normalization case is excluded, not disposed of by division by zero.

#### D5. C61: Ordinary fixed weighted combinations are also covered

Let r_i,N be the individually normalized original flat residual at H_i, each with any high-supported exact-moment correction. For fixed real a_i with sum a_i=1, set r_N=sum_i a_i*r_i,N. Group equal-exponent BASE profiles and delete any zero combined base weight first. Retain every weighted high correction in the full residual, even when its base profiles cancel: different corrections need not cancel each other, but all vanish on the pre-block after the exact-moment reduction. The remaining base weights still sum to 1. Then r_N is again a residual with constant term 1 on the ORIGINAL full basis, and has exact head through the shortest remaining H_i.

Multiplying its probe by log N gives effective coefficients

```text
a_i*log N/ell_i = a_i/(1-theta_i)
                 +O_(a,theta)(N^(-theta_i)/log N).
```

The elementary bounds V(H_i)=O(log^2 N), P_g(N)=O(log N), and the periodic bound show that replacing them by the fixed alpha_i=a_i/(1-theta_i) costs only O(N^(-theta_1)log N). That is below the required N^(-a) because a<theta_1. Repeat C58 with these alpha_i, including possible sum alpha_i=0. The same upper Abel bound proves C60 for this mixture too. This is an asymptotic controlled transfer, not an exact equality of the two parameterizations. It covers fixed convex averaging and fixed signed extrapolation of normalized residuals; freely adaptive weights remain outside its hypotheses.

#### D6. Checked cross-route connection, no circularity and novelty

The source-to-classical Hilbert map is exact. For t=m+v with 0<=v<1,

```text
{t/k}-(1/k){t}=(m mod k)/k.
```

With x=1/t, dx=t^(-2)dt in absolute value, this identifies the whole discrete energy with the integer-dilation Nyman residual norm on (0,1). It preserves every modulus and all mixed terms. The classical integer-dilation density criterion is an existence statement, not a claim that these particular coefficients converge; see [Baez-Duarte's primary paper](https://arxiv.org/abs/math/0202141). No unproved density is imported into the argument.

The further NYMAN-to-genuine-Mertens connection uses the inspected actual-zero translator, not a map to Hecke phases or VF seats. An inherited envelope b gives the pre-block certificate exponent

```text
kappa_in=1-2theta_1*(1-b).
```

The new family-specific inverse returns exactly b. The general localized exact-head consumer C46 would return b+(1-theta_1)/(2theta_1), a weaker statement under its broader hypotheses. An independently proved improvement kappa_in-eta in the REQUIRED all-scale pre upper bound would return b-eta/(2theta_1), with its needed parameter range. No such improvement is supplied. This is not the shell eta/4 exchange and cannot borrow CODIV's local logarithmic savings without a new source-preserving comparison.

The preceding reports treat one fixed theta, sampled scales, moment leakage and separately centered correction costs. The search of retrieved relevant reports found no finite signed multi-profile/prime-term-annihilating result. Our new input is a finite contracting graph of possible zeta-pole cancellations. C59 alone is linear algebra; C58 and the critical-line contradiction provide the quantified obstruction. It does not assert a false lower bound obtained by dropping a negative mixed term. The theorem is a scoped method no-go and a target-equivalence diagnosis, not a new upper bound or a universal impossibility claim for Nyman.

#### D7. C62: Preregistered exact checks and limits

Test question fixed before execution: do the combined original residues retain the full return and exact head for signed mixtures, including A=0, and do the conclusions cease to apply when the moment or support is changed? Rival explanation: an omitted k=1, after-N floor or cross term could create a spurious obstruction. Reject the source formula on ANY rational prime-log-vector mismatch. Finite energies do not test a limiting exponent.

Executed N=96,192,384, heads (floor sqrt N,floor N^(3/4)), weights (1,1), (1,-1), (2,-1), (-3/2,5/3), with both a single high correction and a distinct high correction also satisfying mean centering. All 12 fixtures passed. Exact coefficients are rational vectors of prime logarithms; no floating logarithm decides a source equality.

```text
24 reciprocal-moment checks; 12 mean-centering checks;
360 direct original-residue/full-return coordinates;
192 pre-coordinate identities; 48 exact-head coordinates;
12 distinct-high-correction invariant pre-block comparisons;
333 exact A=0 prime-power-cancellation checks;
12 moment-breaking and 12 low-support negative controls;
1 duplicate-profile cancellation control.
```

The direct coordinates include both sides of head/correction boundaries, N, N+1 and 2N+1. Full pre energy is evaluated for every m in [N/6,N/2). Twelve 60-digit Decimal decompositions check E_1+E_2+2Cross=E_mix numerically to 1e-50; these decimal values are diagnostics, NOT certified bounds. At N=96, alpha=(1,-1), the energy is approximately 0.014722827321 and its mixed contribution approximately -0.0039038643260. The prime-power coefficient is exactly zero; the actual residual is not. A negative mixed term is compatible with the theorem.

The verifier is included below, SHA256 **4c65321f0c381519ac0947cf1a1b426b7cc94472fdebbe7bdfe18252ece4c444**. Initial tooling adjustments replaced an unavailable optional numerical package with standard Decimal and stopped a redundant exhaustive run to use the decisive boundary fixtures; no failed mathematical check was hidden. No local Lean ran. No finite result is extrapolated to all scales.

### E. Specialist Findings And Continuity

Both dates' reports and the external inbox were fetched from immutable reporting snapshot **d4ae547b8783aefdb0e7cf16f8d95746863b7464** (2026-11-05T18:36:20Z). Applicable substantive sections, claims, proofs and resume capsules were read. All six current-day stages are available; no missing execution is invented. For exact paths below use `research/agent_reports/YYYY-MM-DD/<role-file>` at that snapshot.

| Role | November 4 blob | November 5 blob | Accepted/current reading |
| --- | --- | --- | --- |
| Owner | 560b0b7617703b64e728e12e60a390646c9379ea | b4a4f636ece46d696360b5ca9312c2d1d81498c9 | S2/S3, SF1-SF5, LC1-LC5 carried forward; RC1-RC5 and CR1-CR5 are paper/self-audit, not blanket Referee acceptance. CR3 corrects the scale at which ancestry-only payment truly fails. |
| Analytic | 04ffb1b41d8b6afe5a5d89754f5ccbc8d9682d58 | 0774002d5244d373b0230429802cd1cfd8a3a8e8 | P1-P10, CF1-CF3, M1-M6 read. Today's SP1-SP5 have independent Referee-5 acceptance; the full all-scale flat-profile obstruction supersedes the earlier merely open bounded-norm proposal. CODIV every-log savings are not fixed power gains. |
| Wheel | 37ad6a1230fbb46369311790ed5686baf1775598 | 000bd6a7e0900373f8fca05a607676f6170f1032 | Complete-prime L1-L4 coherence, QC1-QC3 method obstruction and today's F/P bundles read. Fixed-prime F2-F3 have scoped Referee acceptance. New nonsymmetric P1-P4 block obstruction and QC1-QC3 still need independent review. |
| Census | 4bd5319fa3d13219cdad006dce4a854b606c2f7c | 44f070eed4302f3d8d560346c6fb9b66c35be18a | Cube/incidence source factors and Nyman N=42/120 failures retained. Today's genuine joint-feasibility gaps 28/3 at R=57 and 12 at R=58 are independently reproduced by Referee; no uniform gap follows. |
| Referee | 0e4fdfbf90d52a74074e04ef6cb6988339dc8d84 | df74121b0a07297776a106ccd1b9d80a36b12fc5 | Earlier cube-source, Nyman divergent-piece and C45-C47 reviews retained. Today's fixed/growing prime-rule and SP reviews distinguished from new Referee-6/-7/-8 self-audit extensions. C53-C57 remain REVIEW_PENDING. |
| Lean | 5fce0138779d67eda4e69c13230274e6419de894 | c9e8255d2c00a2b317f39531589ac2a16f8e3518 | #1090/#1093 structural implementation history retained; #1094 merged and independently scope-reviewed; #1095 exact-head green and now human-merged, superseding the report's earlier unmerged state. |
| Coordinator | 68495a5e913eee0e788940a683cf16ec4d0984cc | 8598794f544c0abb9e3437faaad109e3d4f24485 | C41-C57 and preceding synthesis preserved; new continuation is C58-C62. Today's initial mirror blobs matched. |

External inbox blob **038018145c0fddb2f6306c0712373adf9cd1ea52** has no entry later than October 18. EXT-20261018-PNT-1..3, EXT-20261017-XCOORD-1 and EXT-20261014-5 remain dated safeguards about original carriers, endpoints and unconditional versus first-bad claims. They supply no new finite-mixture theorem. Historical routing/cadence there does not override current main.

### F. Mathematical Bottlenecks And Protected Coverage

| Route | Latest substantive continuation | First independently missing input / next disposition |
| --- | --- | --- |
| VF-LOW | Nov 5 Owner-2 CR1-CR5 | Dense original-weight chronological return with once-only donors and the true complement; CR2 is proper-sector only. |
| SAT | Nov 5 Owner-1 RC1-RC5 | Joint original smooth/prime-error source beyond inherited bounds; separate packet RC5 retains its stated prime-error-equivalent burden. |
| JOH | Nov 4 Owner-3 LC1-LC5 | Independent control of weighted sampled backlogs U, not within-cell position. Next Owner route due. |
| CODIV | Nov 4 Analytic-3 M1-M6 | A fixed power improvement on complete source energy; every fixed log saving at H^3 does not reach H^(5/2-eta). |
| OAI-NNS | Nov 4 Analytic-2 CF1-CF3 plus Referee-5..8 | Coefficient-sensitive all-selected source control, including upper numerator rows and full return. Next Analytic route due. |
| NYMAN | Nov 5 Analytic-1 SP1-SP5; this synthesis | A truly changed profile/moment or sparse-sequence supplier; fixed finite profile mixing is not an all-scale escape. |
| FINITE-AC | Nov 5 Wheel-2 P1-P5 | Complete signed non-divisor/corner estimate at the original historical budget; four component bounds are not available. |
| CORR4 | Nov 5 Wheel-1 F1-F4; Census/Referee | Genuine all-label arithmetic restriction for the full mixed bill, beyond finite marginal caps and the artificial-sign relaxations. |
| MU-LIFT | Nov 4 Wheel-3 QC1-QC4 | Cross-square-class signed information and a paid whole-prefix recurrence r<k. Next Wheel route due. |

The most recent three substantive investigator turns cover each protected triple: Owner JOH/SAT/VF-LOW, Analytic OAI-NNS/CODIV/NYMAN, Wheel MU-LIFT/CORR4/FINITE-AC. No overdue route is inferred from calendar time alone. S1 packet admission, S2 divisor/source alignment, S3 owner chronology/recurrence and S4 cross-scale analytic transfer remain distinct; this run advances S4 only through a scoped inverse theorem. No fabricated OAI audit is added to the Nyman task.

### G. Strategy Decisions

1. Stop treating fixed finite signed profile averaging as a prospective all-scale bounded-norm repair without a changed hypothesis. C58-C61 include negative weights and exact prime-term removal; acceptance remains subject to Referee review.
2. Preserve unrestricted NYMAN and sparse/adaptive/leaky variants. The next Nyman experiment must specify its genuinely changed source and complete norm/consumer, not only optimize one probe or correction component.
3. Keep Owner's proper-sector chronological construction separate from the target-equivalent complete residual. Do not turn its success into permission to reuse prime charges across dense owner families.
4. Retain Wheel's full nonsymmetric four-block expression. Neither its negative prime block nor a sum of absolute block bounds supplies finite C. Preserve all-label CORR4 and cross-class MU-LIFT alternatives with their distinct original carriers.
5. No new Lean proof assignment for C58-C61 before independent review. #1095 is now human-merged; no duplicate repair or re-run of unchanged green checks is needed. SEARCH_BROAD remains the additional-gain gate.

### H. Next Specialist Assignments

**Owner, due JOH:** resume LC4 with B(n)=pi(n)-floor(Li_2(n)), arrival b_j and U_a(N)=G(a)+sum_(b_j<N)(min(b_(j+1),N)-b_j)B(b_j). Exact question: does a new chronological cofactor restriction control a proper class of MULTI-cell backlog excursions after unequal counts, anchor and final partial cell are restored? Reuse the paid E_place=O(N); do not repeat midpoint signs or assume eventual U(R^2)<0, which LC5 identifies as target-equivalent. Output one weighted inequality with an independent arithmetic input, or a legal counterexample. Falsifier: excursions with the same local owner data but uncontrolled accumulated backlog. This decides whether chronological progress reaches the actual retained variable; CR1-CR3 review is a separate queue.

**Analytic, due OAI-NNS:** resume the previously accepted CF1/source cube extraction and Referee-7 restricted-row theorem. Exact question: can one coefficient-sensitive argument bound the original extracted-sector UPPER numerator rows not covered by N(m)<=C Z^(5/6-(5/3)h), with the original Hecke/Gauss coefficients, masks and Gaussian return? Expected output is a genuinely paid integrated estimate or a lawful obstruction to a specific source-level move, not another positive counting envelope or a repeat of the scale-mismatch proof. Falsifier: same-norm/cube-sharing channels or upper-row mass survives every purported gain. Preserve CODIV/NYMAN rotation. On the following NYMAN turn, choose a profile or moment change outside C58-C61 and quantify head leakage, orthogonal pre residual and all later return before proposing an exponent.

**Wheel, due MU-LIFT:** resume QC1-QC3 at the exact ordered k-lift occurrences. Exact question: can a deterministic pairing or bilinear estimate move between distinct square classes while preserving original signs, binomial multiplicities, once-only occurrences and X<B^k, and leave a quantitatively smaller complete signed remainder? Reuse the exact K_s=mu(s)W_s and the 121-versus-1 fixture at B=4,k=2,X=15. Missing input is cross-class arithmetic, not another class-preserving matching. Output a real mixed-class identity plus an independently proved restriction, or a counterexample to a proposed rule. Check the final amplitude r<k and all-prefix coverage. A mere re-expression of M(X)^2 is IDENTITY_ONLY and does not promote the route.

**Census:** independently test C59 on one three-profile signed fixture with A=0 and nonzero c_star, retaining exact prime-log coefficients and both sides of the correction boundary; include a fixed-weight normalized-mixture fixture for C61. Falsification criterion: any mismatch of the original residues, complete return, or predicted rounding-coefficient expansion. Do not fit a limiting exponent or re-run the old N=42/120 scans. A failure changes the proposed finite-mixture theorem immediately; success supports only the finite source bridge. The uncompleted JOH LC4 independent certificate remains a distinct useful follow-on, not a fabricated completed handoff.

**Referee:** independently audit C58-C61, especially A=0, repeated exponents, normalization c_star, the floor error versus a<theta_1, smoothing order based on theta_d, multiple zeros, and finite branching with q<1. Reconstruct the Mellin formula before relying on the author's cancellation argument. Expected result: ACCEPT_WITH_SCOPE, precise repair, or a counterexample. Test whether fixed normalized weights are transported with the actual O(N^(-theta_1)log N) error. Growing/adaptive weights and vanishing normalizers are excluded, not silent conclusions. C53-C57, Owner CR1-CR5 and Wheel P1-P4/QC1-QC3 remain separately pending; this ticket does not accept them by association.

**Lean Verification:** preserve #1095's exact-head green audit evidence and record its human merge; do not rerun or create another repair unless source/head changes. One possible implementation task remains the independently accepted C45 localized original-Nyman Mellin functional, only if the necessary integrability and actual-zero interfaces are available and the declaration is still absent. Required output is the exact source-faithful theorem and pinned CI/axiom evidence, or the specific missing analytic bridge. Do not replace it by a generic Hilbert axiom or formalize unreviewed C58-C61 for theorem count. At most this one new implementation-sized task is proposed; the human merge gate remains unchanged for any future PR.

These are asynchronous report handoffs for the roles' next actual executions, not launches, schedule changes or claims of future delivery.

### I. Lean And PR Status

Live open/draft collection at intake contained only **#1095**. The final refreshed open collection is empty: #1095 was human-merged at 2026-11-05T20:32:22Z. Recent merged #1090, #1091, #1092, #1093, #1094 and #1095 were individually checked; stale descriptions in PR bodies were not used as current state.

**#1094 MERGED / PROVED_IN_LEAN at the component scope.** Latest proof head **1ea4a8a4308976721a3841998d6c3a4554f7a9c9**; human merge **884de7a1fa7687d483a7b5272bff6c9d53790367** at 13:35:24Z. All 12 returned head-associated workflows succeeded. [Dedicated run 42011040577, job 127189858614](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42011040577/job/127189858614) was read directly: eight intended theorem types and actual axiom lists contain only propext, Classical.choice, Quot.sound. Its checked synthetic merge **45a4bc4b5995d908328e5aec4c12a6a4eec946ec** has tree **e98a257a8258c42baae89222c999f4dfd544546a**, exactly the intake main tree; the relevant sources are unchanged at final main. This is stronger evidence than a PR headline and still proves only the finite correction bound and exact split.

**#1093 MERGED, exact source return retained.** Proof head **a54f0cf9535c548920dae3412e3fbe6d6584e029**; merge **ff620da3c0d2c29585805960c6be183c07f16556**. All 12 returned head-associated workflows succeeded. [Run 41955044802, job 127007831273](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41955044802/job/127007831273) directly verifies eight terminal declarations with the standard axiom sets, including `nyman_flat_complete_return`, `nyman_flat_return_of_moment`, `nyman_flat_exact_head` and `nyman_flat_head_iff_moment`. Synthetic checkout **779336cefaf99d04bf48b837340a076d40aebdd3**, tree **958770679fb0146df80f44de258f694cd232434e**. Current source blob matches the verified source ledger. Mellin and infinite-norm arguments are not in this PR.

**#1095 MERGED / exact-head CI_GREEN, superseding its intake REVIEW_READY state.** Branch `agent/lean-verification/20261105-euler-axiom-audit`, head **46e68178192c6e429a02abee9d5b8ebca5de46c8**; human merge **1667c3cf9b4e898bb9afd62ec48e24610b2156ab** at 2026-11-05T20:32:22Z. All three triggered head workflows passed. [Run 42084042187, job 127444267657](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42084042187/job/127444267657) was inspected directly: eight actual terminal declarations, including the formerly absent cast bridge, are covered with standard axioms; the final audit reports exact coverage, not an empty match. Checked synthetic merge **55968fd690fea8b12f4602ab9dc9adf58bf00c60** has tree **6351bbacd22d7abb34eefed1e2cbf5f674642010**, exactly the human-merged final main tree. Mathematical source declarations are unchanged. No claim that unrelated workflows ran at this repair head or that a separate post-merge CI run was inspected is made. Human merge occurred outside this agent's actions; permissions remain unchanged.

Today's C58-C61 are not compiled, and the existing green algebra does not prove their analytic steps. The current invocation did not execute Lean, write source, create a proof branch/PR, weaken audits or merge anything.

### J. Next-Run Resume Capsule

```text
RUN: 20261105-coordinator-2; scheduled 15:13:00 EST; RUN_ID_UNAVAILABLE.
FINAL_MAIN: 1667c3cf9b4e898bb9afd62ec48e24610b2156ab.
INTAKE_MAIN: 884de7a1fa7687d483a7b5272bff6c9d53790367.
POLICY: NO_PIGEONHOLING_ROUTE_SELECTOR_V1; SEARCH_BROAD.
INTAKE_REPORTS: d4ae547b8783aefdb0e7cf16f8d95746863b7464.
EARLY_CHECKPOINT: 35061e892f440c80db59cab39f159d41eb0c06f6;
  identical mirrors df0e381cd34ad144c6a38a1b78f301c13559f59e.
C58: finite contracting-pole argument for signed scale superpositions.
C59: exact original-residue multi-profile return/probe, including A=0.
C60: pre-energy exponent 1-2theta_min(1-beta_*), all-scale scoped no-go.
C61: same result for fixed affine combinations of normalized residuals.
C62: exact finite source tests; decimal energies are diagnostics only.
REVIEW: C58-C61 SELF_AUDIT / PAPER_PROOF, independent review PENDING.
INHERITED: Analytic SP1-SP5 accepted by today's Referee-5.
RETIRED_SUPPLIER: all-scale bounded norms from fixed finite polynomial-head
  mixtures with exact moment and high-supported corrections.
NOT_RETIRED: adaptive/moving/infinite profiles, relaxed moment, sparse
  sequences, unrestricted full-basis NYMAN, or any other protected route.
FORMAL: #1094 merged; #1095 human-merged, exact tested tree equals main.
NEXT: Referee finite-branch audit; investigators JOH / OAI-NNS / MU-LIFT.
HIGHEST_VALUE_NYMAN_TASK: explicitly change a hypothesis and bound the
  whole resulting residual, not another corrected component or one probe.
ENDPOINT: canonical VF OPEN; no additional exponent gain established.
```

### Appendix. Complete C62 Verifier

The following standard-library Python program reproduces the exact finite checks and the separately labeled Decimal diagnostics. It has no network dependency or Lean invocation.

```python
"""Finite source checks only; no Lean execution or asymptotic inference."""

from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from math import isqrt
import json
from decimal import Decimal as D, getcontext


def add(*vectors):
    out = {}
    for v in vectors:
        for p, a in v.items():
            out[p] = out.get(p, Q(0)) + a
    return {p: a for p, a in out.items() if a}


def scale(v, a):
    return {p: b * a for p, b in v.items() if b * a}


def logvec(n):
    out = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, Q(0)) + 1
            n //= p
        p += 1
    if n > 1:
        out[n] = out.get(n, Q(0)) + 1
    return out


def mobius(n):
    factors = logvec(n)
    return 0 if any(e > 1 for e in factors.values()) else (-1) ** len(factors)


def value(v):
    return sum((D(a.numerator) / D(a.denominator) * D(p).ln()
                for p, a in v.items()), D(0))


def main():
    getcontext().prec = 60
    counts = Counter()
    records = []
    for n in (96, 192, 384):
        heads = (isqrt(n), isqrt(isqrt(n ** 3)))
        assert 2 <= heads[0] < heads[1] <= n // 2
        mu = [0] + [mobius(k) for k in range(1, 2 * n + 2)]
        logs = [dict()] + [logvec(k) for k in range(1, 2 * n + 2)]

        @lru_cache(maxsize=None)
        def tail(b, m):
            return add(*(scale(add(logs[b], scale(logs[k], -1)), mu[k] * (m // k))
                         for k in range(b + 1, m + 1)))

        for weights in ((Q(1), Q(1)), (Q(1), Q(-1)), (Q(2), Q(-1)),
                        (Q(-3, 2), Q(5, 3))):
            total_weight = sum(weights, Q(0))
            lam = add(*(scale(add(logs[n], scale(logs[h], -1)), a)
                        for h, a in zip(heads, weights)))
            assert lam
            f = [dict()] + [scale(add(*(scale(add(logs[n], scale(logs[max(h, k)], -1)), a)
                                         for h, a in zip(heads, weights))), mu[k])
                                  for k in range(1, n + 1)]
            assert f[1] == lam
            moment = add(*(scale(f[k], Q(1, k)) for k in range(1, n + 1)))
            mass = add(scale(lam, 2), *f[1:])
            b = scale(add(scale(moment, n), scale(mass, -1)), n - 1)
            centered = {n - 1: b, n: add(mass, scale(b, -1))}
            corrections = ({n: scale(moment, n)}, centered)
            observations = []
            for correction in corrections:
                assert add(*(scale(v, Q(1, k)) for k, v in correction.items())) == moment
                counts['moment_checks'] += 1

                def residual_scaled(m, corr=None):
                    if corr is None:
                        corr = correction
                    return add(lam, *(scale(add(corr.get(k, {}), scale(f[k], -1)),
                                             -Q(m % k, k)) for k in range(2, n + 1)))

                if correction is centered:
                    center = add(*(scale(add(correction.get(k, {}), scale(f[k], -1)),
                                        Q(k - 1, 2 * k)) for k in range(2, n + 1)))
                    assert center == lam
                    counts['mean_center_checks'] += 1

                coordinates = sorted(set([1, *heads, *(h + 1 for h in heads),
                                          n // 6, n // 6 + 1, n // 2 - 1, n // 2,
                                          n // 2 + 1, n - 1, n, n + 1, 2 * n, 2 * n + 1]))
                for m in coordinates:
                    direct = residual_scaled(m)
                    restored = add(scale(tail(n, m), total_weight),
                                   *(scale(tail(h, m), -a) for h, a in zip(heads, weights)),
                                   *(scale(v, m // k) for k, v in correction.items()))
                    assert direct == restored
                    counts['complete_return_coordinates'] += 1
                    if m < n // 2:
                        pre = add(*(scale(tail(h, m), -a) for h, a in zip(heads, weights)))
                        assert direct == pre
                        counts['pre_coordinates'] += 1
                    if m <= heads[0]:
                        assert not direct
                        counts['exact_head_coordinates'] += 1
                pre_values = [add(scale(tail(n, m), total_weight),
                                  *(scale(tail(h, m), -a) for h, a in zip(heads, weights)),
                                  *(scale(v, m // k) for k, v in correction.items()))
                              for m in range(n // 6, n // 2)]
                observations.append(pre_values)
            assert observations[0] == observations[1]
            counts['high_correction_invariance'] += 1

            # All three quadratic terms are retained; finite cancellation is allowed.
            e1 = e2 = cross = full = D(0)
            ell = value(lam)
            for m, v in zip(range(n // 6, n // 2), observations[0]):
                parts = [-value(scale(tail(h, m), a)) / ell for h, a in zip(heads, weights)]
                w = D(1) / (m * (m + 1))
                e1 += parts[0] ** 2 * w
                e2 += parts[1] ** 2 * w
                cross += 2 * parts[0] * parts[1] * w
                full += (value(v) / ell) ** 2 * w
            assert abs(full - e1 - e2 - cross) < D('1e-50')
            records.append({'N': n, 'H': heads, 'alpha': [str(a) for a in weights],
                            'A': str(total_weight), 'energy': f'{full:.11g}',
                            'mixed': f'{cross:.11g}'})
            counts['numeric_energy_decompositions'] += 1

            # A moment-preserving correction below N/2 changes the actual pre-block.
            k0 = n // 4
            altered = dict(centered)
            altered[k0] = lam
            altered[n] = add(altered[n], scale(lam, -Q(n, k0)))
            assert add(*(scale(v, Q(1, k)) for k, v in altered.items())) == moment
            assert add(residual_scaled(k0, altered), scale(residual_scaled(k0), -1)) == lam
            counts['support_negative_controls'] += 1
            # Breaking the reciprocal moment destroys the exact head at m=1.
            broken = dict(centered)
            broken[n] = add(broken[n], scale(lam, n))
            assert residual_scaled(1, broken) == scale(lam, -1)
            counts['moment_negative_controls'] += 1

            # If A=0, the prime-power contribution cancels exactly, not the residual.
            if total_weight == 0:
                for m in range(1, n // 2):
                    # Lambda(p^j)=log p, not log(p^j).
                    psi = add(*({next(iter(logvec(k))): Q(1)} for k in range(2, m + 1)
                                if len(logvec(k)) == 1))
                    expansions = []
                    for h, a in zip(heads, weights):
                        low = add(*(scale(add(logs[h], scale(logs[k], -1)),
                                          -mu[k] * (m // k)) for k in range(1, h + 1)))
                        expansions.append(scale(add(logs[h], psi, low), a))
                    assert add(*expansions) == add(*(scale(tail(h, m), a)
                                                    for h, a in zip(heads, weights)))
                    counts['prime_term_cancellation_checks'] += 1
                assert full > 0

    # Duplicate exponents must first be combined; cancelling their coefficients
    # removes that profile and is outside the shortest-nonzero-head conclusion.
    assert add(scale(logvec(9), 3), scale(logvec(9), -3)) == {}
    counts['duplicate_profile_control'] += 1
    print(json.dumps({'checks': dict(counts), 'finite_diagnostics_not_bounds': records}, indent=2))


if __name__ == '__main__':
    main()
```

### Publication Freshness

Final authority refresh: main **1667c3cf9b4e898bb9afd62ec48e24610b2156ab**, unchanged instruction/contract blobs, #1095 human-merged and no open/draft PRs at the final collection read. Reporting parent **35061e892f440c80db59cab39f159d41eb0c06f6** and both current own blobs were read back before writing. All earlier report bytes and the early checkpoint are retained as an exact prefix.

Synthesis publication prepared at **2026-11-05 20:41:02 UTC** (America/New_York calendar date 2026-11-05). Execution publication status remains **PENDING_READBACK** until the verified receipt. Mathematical C58-C61 remain **PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING**; canonical target **OPEN**.

### Verified Publication Receipt - 20261105-coordinator-2

**Execution COMPLETE; mathematical endpoint OPEN.** At **2026-11-05 20:41:45 UTC**, both complete Coordinator mirrors were fetched from substantive commit **76258df2da8fe14e8d8dcfe21c32c2d9bb9927eb** and matched the intended **106388-character** content exactly, with identical blob **0e740e9cbf6e3ad09e6c06090729d7e50b97ff01**. The branch update succeeded with an expected-parent lease; the exact prior report and checkpoint were preserved. Only the two authorized Coordinator report paths were changed.

C58-C61 remain **PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED**; C62 is finite source evidence, not an asymptotic proof. Independent review and the source-changing Nyman follow-up are published handoffs only. The final main snapshot is **1667c3cf9b4e898bb9afd62ec48e24610b2156ab**; #1094 and #1095 are human-merged. No Lean source, proof branch, PR, policy, other agent report, schedule or merge action was changed by this execution.


---

## Scheduled Continuation Checkpoint - 20261105-coordinator-3

**SEARCH_BROAD. PARTIAL / IN_PROGRESS.** No new endpoint estimate is established at intake. Current main is `1667c3cf9b4e898bb9afd62ec48e24610b2156ab`; canonical actual-prime VF and the new complete-return exponent gain remain OPEN. This actual invocation began 2026-11-05 23:09:00 EST (2026-11-06T04:09:00Z), SCHEDULED, RUN_ID_UNAVAILABLE.

Deployment acknowledgement: current main AGENTS blob `547dda0d9456e7a4e1165dc72d59da6f70d5c023`, proof-contract blob `7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c`, NO_PIGEONHOLING_ROUTE_SELECTOR_V1. Preserve nine-route research and own-report-only authority. Initial reporting snapshot `8c525379f7fe53fa07b131965f0ca785592002b9`; prior complete mirror blob `88c4b9f83cc3dcea885d0c9ddb1fc26cedef4632` is retained byte-for-byte above. Today's and yesterday's full report sources are being retrieved, with relevant continuation and proof sections to be inspected before selecting the new mathematical attempt. The latest open collection contains #1096 at `ecf701ff2fea1de52e505ee34048a2b3c220f0fc`; compilation/axiom status is PENDING review. Earlier #1095 is merged in current main. No new claim is accepted merely from its report or PR title.

Next: finish source and report continuity, develop one nonduplicate mathematical argument, record its complete scope and first open inequality, then append the verified synthesis to both mirrors. This checkpoint is not a completed research result. No other agent is launched, no schedule is changed, and no Lean source or proof branch is written.


---

## Research Synthesis - 20261105-coordinator-3

### A. What Changed Mathematically?

**SEARCH_BROAD. The new 13c/15c cancellation is already optimal, to leading order, among ALL replacements using only the prime factors 3, 5 and 13. Repeating those templates cannot produce a geometric contraction.** An exact outside-prime-core invariant gives the sharp finite residual and its positive density. This applies to arbitrarily deep cofactors, so it is different from the Referee's low-depth-endpoint obstruction.

There is a constructive escape, with a precise limitation. A cohort of positive semiprimes that is isolated under every replacement using primes at most four fifths of sqrt(X) can be matched, once each, to genuinely unused negative triples 15q. Ordinary PNT proves enough actual prime q for every sufficiently large cutoff. These five-prime edits preserve the earlier factor-two, prime/semiprime and qualified 13c/15c matchings. They remove the identified obstruction cohort, but only O(X/log(X)^2) sites; the complete unsigned remainder is still linear. This is a source-qualified intermediate theorem, not the missing MU-LIFT estimate.

New claims **C63-C67 are PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED**. C63 includes an exact identity and a sharp finite minimization; C68 is FINITE_COMPUTATION. The scoped absolute-certificate suppliers excluded below are REFUTED, not MU-LIFT, genuine signed cancellation, or RH. No literature-priority claim is made. The new contribution is the exact application, sharp saturation constant, growing-bank restriction and lawful unused-partner repair, beyond the retrieved handoffs.

Actual invocation: SCHEDULED, began **2026-11-05 23:09:00 EST**, equivalent to 2026-11-06T04:09:00Z; RUN_ID_UNAVAILABLE. The Eastern reporting date is November 5. This synthesis and the earlier checkpoint belong to one invocation. Publication remains PENDING_READBACK until the receipt below; mathematical review remains separate.

### B. Current Proof Objective And Authority

Main inspected: **1667c3cf9b4e898bb9afd62ec48e24610b2156ab**, tree **6351bbacd22d7abb34eefed1e2cbf5f674642010**. AGENTS blob **547dda0d9456e7a4e1165dc72d59da6f70d5c023**; CURRENT_PROOF_CONTRACT blob **7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c**. The live NO_PIGEONHOLING_ROUTE_SELECTOR_V1 policy blob is **ffd8f1c65cc4da656174956d4e03b48bea46768b**. The selector, breadth, complete-return, persistent-engine, role, dynamic and multirun policies were retrieved at that main. Their current routing supersedes historical compulsory OAI tasks and old cadence prose; no schedule was changed or inferred.

The actual canonical goal is unchanged:

```text
VFCanonicalSquareVonKochStatement:
 exists C >= 0, forall integer R >= 2,
 |pi(R^2) - vfMidFinishedMass(R) - sqrt(2)| <= C R log R.
```

The original definitions and terminal consumer were read. `riemannHypothesis_of_vfCanonicalSquare` still requires BOTH `ClassicalVonKochRHCriterion` and the actual-prime bound. The O(1) VF/Li transport is not that bound. No new canonical estimate, complete zero-target payment, finite A/C bound, CORR4 estimate, subcritical lift recurrence, or full-basis Nyman density proof is established here. Inherited imported 7/8 and source-qualified slot results are not relabeled as new, withdrawn, or assumed to improve themselves.

Deployment acknowledgement: independently selected MU-LIFT after the current common-cofactor handoff, not a compulsory OAI task. Resumed sources are Wheel PE1-PE4 and Referee-14, not the already defeated square-class-only matching. The actual new steps are C63-C66 below.

Material source ledger:

| Source | Blob / scope |
| --- | --- |
| research/MERTENS_HEATH_BROWN_SIGNED.lean at main | af69b4811cf9f523eb7c96fb0ca836b2cdbd1180; exact lift, not a norm estimate |
| research/MERTENS_FINITE_PREFIX_EXTENSION.lean at main | 131e9af86207a42d4bf6488e3f64c9ce4f97e5df; genuine prefix and strict precision |
| RHLean/Proof/AdaptivePrimeMatching.lean at main | c2caaace0f4e99ea06107d939119c12fa005bcbc; single-toggle obstruction, not today's multi-edit theorem |
| research/VF_CANONICAL_SQRT_TWO.lean at main | 3ced39671cff51579a8009a6ea059890368ca05a |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean at main | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |
| research/VF_MID_SQUARE_BAND_COMPOSITE_BRIDGE.lean at main | e73fab365f477c61725f843082817cbad3413a5f; original prime/composite carrier |
| research/MERTENS_ODD_BOUNDARY_PRIME_ESCAPE_20261105.lean at #1096 head | 3cbc5159536d6b9e5000f74c5bd018bd2d62daf1; finite endpoint subsets, coefficient-level lift bridge |

### C. Competing Mechanism Portfolio

These are three distinct working mechanisms, not three established routes to a new exponent. Other protected investigations remain in the coverage ledger.

| Mechanism | Independent input and exact target route | First missing input / support / decisive test | Assignment and disposition |
| --- | --- | --- | --- |
| JOH actual arrival-clock count innovations | Owner MC2 imports a classical prime-interval mean square through an explicit integer-clock sampling bridge; a stronger complete clock energy would feed MC4's prime-error consumer | MC2 remains paper/self-audited. Its X h^2 (log log X)^2/log(X)^3 bound, h=floor(X^(1/4)), does not pay X^(5/4-kappa+epsilon). Keep upper halo, initial backlog and signed coarse return. Test the external theorem's hypotheses and exact sampling loss, not more local sign rules | Owner on next JOH rotation; Referee review priority. CONTINUE at logarithmic scope |
| CODIV genuine phase-uniform short-interval cancellation | Analytic M1-M4 use a stated external short-interval theorem on actual Mobius AP/polynomial sums and return to full daughter/root-step sources | Every fixed logarithmic saving at H^3 is still polynomially above the sharp shell H^(5/2-eta). OPEN-CD5's signed triangular lag estimate is unpaid. Fixed degree and owner-only masks cannot become arbitrary site masks. Test one genuine common-window correlation retaining all shifts and boundaries | Analytic next primary CODIV. CONTINUE; no log-to-power upgrade |
| MU-LIFT cross-core arithmetic cancellation | Unique factorization, squarefree counts and PNT provide actual disjoint packets; exact lift reconstruction transfers them to original ordered occurrences | Fixed-bank absolute finish is refuted by C64; even growing small-prime banks fail by C65. C66 pays one large-prime cohort, not typical-depth signed residuals or whole-prefix r<k. Test a proposed large-prime rule for once-only coverage and the complete remaining source | Wheel on next MU-LIFT rotation; Census can test C66 now. REVISE toward changing genuinely large prime coordinates or a signed estimate |

The fixed polynomial-head flat-taper NYMAN bounded-norm program remains retired at its proved scope: Analytic SP1-SP5 have separate Referee acceptance. Earlier Coordinator C58-C61 extend to fixed finite mixtures but still await their own independent review. Moving/adaptive profiles, relaxed moments, sparse scales and the unrestricted full basis are not refuted. Do not manufacture a replacement independent upper-bound supplier merely to keep a fourth attractive entry.

### D. Conceptual Research Performed

#### C63. Sharp Outside-Core Conservation Law

Fix any finite set P of odd primes, including the empty set; put W=product(P), D=2W. For positive n define core_D(n) by removing ALL powers of primes dividing D. Let

```text
U_X = {n: X/2 < n <= X, n odd, mu(n) != 0},    X >= 1 integer,
sigma_W(t) = sum_(d|W) mu(d) 1_(d <= t < 2d),
S_c(X) = sum_(n<=X, core_D(n)=c) mu(n),
Lambda_W(X) = sum_(c<=X, gcd(c,D)=1) |S_c(X)|.
```

For EVERY c coprime to D, including nonsquarefree c,

```text
S_c(X) = mu(c) sigma_W(X/c),
Lambda_W(X) = sum_(c<=X, gcd(c,D)=1) mu(c)^2 |sigma_W(X/c)|. (C63a)
```

Proof: write the nonzero physical terms uniquely as n=c e with e squarefree and e|D. Their signed sum is mu(c) sum_(e|2W,e<=X/c)mu(e). Pair the divisors e=d and e=2d to obtain sigma_W. Equivalently the original factor-two matching removes all terms outside U_X, separately within EACH core. No prime-density model or independence is used.

Any rational replacement whose prime factors belong to D preserves core_D, including an arbitrary composition of such replacements. Any zero-sum packet inside a core preserves S_c. Therefore Lambda_W is the SHARP minimum number of unmatched unit-sign physical sites under unrestricted sign-reversing pairing within these cores: if a core has a positive and b negative sites, exactly |a-b| remain after pairing min(a,b). This best-case relaxation includes every bank-restricted template scheme, even when an actual restricted graph cannot attain the optimum. A bounded dual certificate is the sign of S_c on each core; it takes values in {-1,0,1} and evaluates the signed population to Lambda_W.

The same statement holds for the ORIGINAL ordered Heath-Brown atoms. For B>=2, k>=2 and 1<=X<B^k, retain occurrence identifiers

```text
o=(j,v,a_1,...,a_j,b_1,...,b_(j-1)),
1<=j<=k, 1<=v<=binom(k,j), 1<=a_i<B, mu(a_i)!=0, b_l>=1,
n(o)=product a_i product b_l<=X,
epsilon(o)=(-1)^(j-1) product mu(a_i).
```

The inspected `heathBrownLift_prefix_exact`, with N=B-1, gives total epsilon in each physical n-fiber equal to mu(n). Grouping atoms by core_D(n(o)) therefore gives EXACTLY S_c, even when individual physical n or b_l are squareful. Pairing within fibers and then within cores attains Lambda_W without duplicating any atom. The coefficient reconstruction and generic finite matching principle are reused prior mathematics, not new discoveries.

If cancellation on the full ordered square is required to preserve the ORDERED PAIR of core labels, its sharp absolute remainder is Lambda_W(X)^2, since each block has signed mass S_c S_e. Tensoring the first-order matching attains that count. This does NOT cover arbitrary cross-core pair cancellations. The actual signed complete square is still M(X)^2, often much smaller.

#### C64. Exact Positive Density And Saturation Of The 13/15 Template

For FIXED W define

```text
delta_D = (1/zeta(2)) product_(p|D) p/(p+1),
I_W = integral_(1..2W) |sigma_W(t)| dt/t^2,
c_W = delta_D I_W.
```

Then, unconditionally as integer X tends to infinity,

```text
Lambda_W(X) = c_W X + O_W(sqrt(X)),
delta_D/2 <= c_W <= 2/pi^2.                         (C64a)
```

Here is a proof of the only counting input, rather than an assumed distribution law. Expanding squarefreeness and coprimality gives

```text
Q_D(y) = #{n<=y: mu(n)^2=1, gcd(n,D)=1}
 = sum_(d<=sqrt(y),(d,D)=1) mu(d)
     sum_(e|D) mu(e) floor(y/(d^2 e))
 = delta_D y + O_D(sqrt(y)).
```

The finitely many e and all d-floor errors cost O_D(sqrt(y)); the absolutely convergent d-tail has the same cost. Multiplying the local factors gives delta_D. Split the integral at the finite breakpoints d and 2d, d|W. On each [a,b), C63 counts c in (X/b,X/a], so Q_D(X/a)-Q_D(X/b) proves C64a with the correct strict endpoint. On [1,2), sigma_W=1, giving the lower bound. The triangle inequality gives I_W <= sum_(d|W)1/(2d), yielding the upper bound. The standard evaluation zeta(2)=pi^2/6 is independently documented in [DLMF 25.6.1](https://dlmf.nist.gov/25.6.E1). No uniform error for W growing with X is inferred.

If the earlier PE1 stage has frozen t prime/semiprime pairs, remove its 2t endpoints before further core cancellation. Write Lambda'_W for the new sharp minimum. For EVERY such choice,

```text
|Lambda'_W-Lambda_W| <= 2t <= 2[pi(X)-pi(X/2)].       (C64b)
```

This is the l1 triangle inequality on the vector of core sums, not a sign assumption. The standard [prime number theorem](https://dlmf.nist.gov/27.2.E3) makes the last quantity O(X/log X), uniformly in the PE1 partner pool. Thus a fixed W still has residual c_W X+O_W(X/log X), after preserving those earlier pairs. This statement does not allow PE1 endpoints to be reused as flow vertices for new cross-core moves.

For W=195=3*5*13 the signed odd divisors are

```text
d:       1,  3,  5, 13, 15, 39, 65,195
mu(d):  +1, -1, -1, -1, +1, +1, +1, -1.
```

The ONLY opposite-sign divisor pair with larger/smaller ratio less than two is (13,15). Both can appear in one U_X core exactly when X/26<c<=X/15. Consequently, for EVERY X,

```text
K_all(X)={c: mu(c)^2=1, gcd(c,390)=1, X<26c, 15c<=X},
Lambda_195(X)=|U_X|-2|K_all(X)|.                    (C64c)
```

The 13c/15c pairs are disjoint: 13c=15e would force 3|c, violating coprimality. Exact integration gives

```text
I_195 = 56/65 - 2(1/15-1/26) = 157/195,
delta_390 = 65/(28 pi^2),
c_195 = 157/(84 pi^2).                             (C64d)
```

This independently reproduces Referee-14's leading residual constant and strengthens its interpretation: it is the best possible constant for the entire {2,3,5,13}-core-preserving class, not merely a defect of that one construction. After PE1 is frozen, the exact optimum pairs every still-available (13c,15c). Referee-14 uses all c with at least two distinct prime factors; these endpoints are automatically untouched by PE1. Its omitted c=1 or prime contribute only O(X/log X). Hence its construction already attains the sharp leading coefficient, for any PE1 pool.

This independent Coordinator reconstruction is a paper audit of R14, not R14's author accepting their own result. The new optimality claim still awaits separate Referee review. Fixed-bank saturation is different from Referee-13: arbitrarily large factor depth is allowed here. Adding more stages or changing their order inside this fixed bank cannot reduce c_195 to zero.

#### C65. A Uniform Growing-Bank Obstruction And Inverse Requirement

For EVERY integer X sufficiently large, allow ANY finite prime-edit bank whose odd primes are at most (4/5)sqrt(X). Allow a preceding PE1 matching with any partner pool under the same bound. Define

```text
J_X={p prime: (4/5)sqrt(X)<p<=(9/10)sqrt(X)},
V_X={p q: p,q in J_X, p<q},   v_X=binom(|J_X|,2).
```

Every element n of V_X is a distinct positive-Mobius odd squarefree integer in (X/2,X], since 16X/25<n<=81X/100. It has no prime factor in the edit bank. Its outside core is n itself, and the only squarefree physical site in that core below X is n: every nontrivial bank multiplier is at least two. It cannot be a PE1 partner because those have a factor in the allowed small-prime pool, and it is not prime. Each such core therefore retains signed mass +1 after any bank-preserving zero-sum cancellation.

PNT applied only to the two fixed macroscopic endpoints of J_X gives

```text
|J_X| ~ sqrt(X)/(5 log X),
v_X ~ X/(50 log(X)^2).                              (C65a)
```

Thus the terminal unsigned remainder T satisfies T>=v_X, uniformly over the allowed moving banks, all their template choices and the earlier partner pools. This proof does not sum fixed-W error terms over a growing bank. It supplies a uniform positive lower constant, for example T>=X/(100 log(X)^2) eventually.

At X=B^k-1, fixed k>=2, fixed 1<=r<k, C>0 and any G(B)>=1 with log G(B)/log B tending to zero, the elementary E(B)<=sqrt(B-1) gives

```text
T/[C G(B) E(B)^r sqrt(X)]
 >= const * B^((k-r)/2)/[G(B) log(B)^2] -> infinity.  (C65b)
```

This refutes the stated absolute-certificate finish even on an unbounded scale chain. It is NOT a lower bound on |M(X)|. The corresponding inverse requirement is concrete: any sign-reversing matching leaving o(v_X) of this cohort must match (1-o(1))v_X distinct positive sites through a change of an outside-core prime coordinate. No two of these +1 sites can be paired to each other. That necessary large-prime coverage is not yet sufficient for a recurrence.

This reuses the general rough-semiprime idea seen in Owner RC1 and Coordinator C53, but does NOT transfer their bounds between carriers. The present interval, constants, arbitrary moving bank and exact original lift are derived here. The result is not claimed as a new sieve principle.

#### C66. A Lawful Large-Prime Escape Using Unspent Negative Triples

The C65 obstruction is avoidable when genuinely large primes may change. For all sufficiently large X define

```text
Z_X={15q: q prime>13, X/30<q<=X/15}.
```

Every z in Z_X is an odd squarefree upper-half triple with mu(z)=-1. It is unused by factor-two matching and PE1, because its factor depth is three. It is also unused by the qualified R14 extension: it is not divisible by 13, and in the 15c representation its cofactor c=q is prime, whereas R14 requires at least two prime factors. Every n in V_X is likewise unused by R14 and PE1; its two prime factors exceed every small pool prime and eventually exceed 13.

The prime-count input is exactly

```text
|Z_X|=pi(X/15)-pi(X/30) ~ X/(30 log X),
|Z_X|/v_X ~ (5/3) log X -> infinity.                 (C66a)
```

Hence there exists an absolute X0 such that for EVERY integer X>=X0 and every allowed PE1 pool, the increasing lists give an injection V_X into Z_X. Pair each n with its assigned triple. No intermediate vertex is consumed. All endpoints are disjoint and unused, so this genuinely extends the old matching. For large X, q>X/30>(9/10)sqrt(X), and the five prime coordinates p_1,p_2,3,5,q are distinct. It changes large coordinates and is not a composition of the old small-bank replacements.

This supplies an unconditional all-large-cutoff packet theorem, not just a favorable census. No effective numerical X0 is claimed. The same PNT statement used in C64-C65 supplies these fixed-interval counts; there is no short-interval PNT, random-sign assumption, growing-modulus input or RH premise.

Let R_old be the COMPLETE remainder after PE1 and R14. For the new remainder R_new,

```text
|R_new|=|R_old|-2v_X,
sum_(n in R_new)mu(n)=M(X),
|R_new|=157X/(84 pi^2)+O(X/log X).                   (C66b)
```

The last line follows from the previously proved R14 density and v_X=O(X/log(X)^2), not from a numerical fit. It remains linear. The complete signed return, with Z=sum_(R_new)mu, is

```text
M(X)=v_X-v_X+Z,
M(X)^2=v_X^2+v_X^2+Z^2-2v_X^2+2v_X Z-2v_X Z=Z^2.
```

C63's physical-fiber representatives lift these disjoint matches to the original ordered atoms; the tensor involution cancels their entire ordered square. All cross-family, diagonal and complement interactions are present. The negative credit is used once. This establishes new partner availability, not a smaller unsigned exponent or a signed remainder upper bound.

#### C67. Checked Cross-Route Nontransfer To Native VF

The actual R14 pair is 1001=7*11*13 and 1155=3*5*7*11. Their Mobius signs are -1 and +1. In the original raw odd-seat VF carrier, however, both are strict-interior COMPOSITES, in blocks r=31 and r=33. Their original coefficients are respectively

```text
w_31 and +w_33,
w_r=(2r+1)/(r log(r^2+r+1/2))>0.
```

Their VF charge is strictly positive, not zero. The same obstruction applies to the semiprime/triple partners of C66: both physical sites are composites. Thus the identity map on integer occurrences does NOT preserve signs or weights from MU-LIFT to VF-LOW, and this cancellation gives no original #915 payment. A different weighted map with real prime donors, chronology, masks and complements would need its own proof. This is a precise failed transfer, not an impossibility result for all cross-route methods. The original square-band composite and canonical declarations were inspected; the raw-seat weighting is the current contract's stated paper carrier.

#### C68. Exact Experiments And Scope

The first test plan fixed the core-sum identity, exact {3,5,13} optimum, PE1 deletion stability, moving boundary X=2001/2002 and complete raw ordered-square return in the verifier before execution. This was not a separately published preregistration. The large-prime repair was a separately disclosed proof-driven addition before its test; it is not retroactively called part of the initial plan. No exponent fit or large range extension was performed.

The verifier checked 660 core-formula cases and 660 exceptional-deletion inequalities on four banks and 165 cutoffs (4..160 plus eight displayed larger cases); 165 exact 195-optimality cases; 2,048 independent trial-factorization Mobius checks; 2,694 literal original lift atoms and ALL 3,791,564 ordered pairs in four declared small carriers. Twelve rough semiprime witnesses and their twelve new large-prime partner pairs were checked at X=16383 and 65535; X=4095 has no such pair in this narrow prime band. These are finite tests, not the PNT proof.

| X | R14 remainder | Further V_X pairs | Complete final cardinality | Actual M(X) |
| --- | ---: | ---: | ---: | ---: |
| 4095 | 307 | 0 | 307 | -19 |
| 16383 | 1496 | 6 | 1484 | -32 |
| 65535 | 6808 | 6 | 6796 | 14 |

At X=16383 one new pair is 11021=103*107 with 8205=3*5*547. Both are in (X/2,X], have opposite signs, and are unused by the old packets. The old-bank negative control 17<->21 at X=31 has opposite signs but distinct {2,3,5,13}-cores, so it is correctly excluded rather than disproving C63. The 1001/1155 pair exits at X=2002 exactly, and the VF sign mismatch is tested on strict nonsquare seats.

Exact rational integration produced c_W*pi^2 equal to 2 for the empty odd bank, 157/84 for {3,5,13}, 157/84 for {3,5,7,13}, and 129961/72576 for {3,5,7,11,13,17}. These are evaluations of the proved finite formula, not evidence for a limiting growing-bank exponent. The full executed script appears below; SHA-256 **87f83b065aff67f6a179c27e974b6666e4754e0ead781c0c4b18b57de8b2f061**. Runtime assertions and Python syntax compilation passed. No Lean ran locally.

### E. Specialist Findings And Continuity

Both November 4 and November 5 report sets were retrieved at immutable reporting snapshot **8c525379f7fe53fa07b131965f0ca785592002b9**. Relevant result, proof, correction, source and resume sections were read; unrelated executable appendices were not all rerun. Every role has an available November 5 report. Earlier same-day PENDING labels remain valid historical snapshots and were not rewritten. The Coordinator mirrors had identical complete blobs on both dates.

| Role | November 4 blob | November 5 intake blob |
| --- | --- | --- |
| Coordinator | 68495a5e913eee0e788940a683cf16ec4d0984cc | 88c4b9f83cc3dcea885d0c9ddb1fc26cedef4632 |
| Owner | 560b0b7617703b64e728e12e60a390646c9379ea | 39665b5b28fc48378519ab9d56cee8df4d3e2681 |
| Analytic | 04ffb1b41d8b6afe5a5d89754f5ccbc8d9682d58 | 9490aa2eecafcd19d8007043cc5f978fe421a7c9 |
| Wheel | 37ad6a1230fbb46369311790ed5686baf1775598 | afc85d800c47f82f2db634591a7798005cb668de |
| Census | 4bd5319fa3d13219cdad006dce4a854b606c2f7c | 24fcd6a631eca9ae44238d927215f49e1d8a174f |
| Referee | 0e4fdfbf90d52a74074e04ef6cb6988339dc8d84 | 789ed87021fe98963c244a8d0c9075638e76be43 |
| Lean | 5fce0138779d67eda4e69c13230274e6419de894 | 5e0ecdd8f08c2e19b4614f00c1a5657f58722344 |

**Owner:** RC1-RC6 preserve the SAT small-prime-certificate obstruction and prime-error equivalence at its stated exponent, not a paid joint SAT source. CR1-CR5 distinguish sparse chronological prime allocation from the many-family ancestor-capacity failure, even allowing an RH-sized remainder. MC2 is a new paper logarithmic prime-clock estimate; MC3 keeps the signed coarse positional return. Their analytical proofs remain separately review-pending. Census has now independently reproduced the cited finite LC4/MC1/MC3/MC5 carrier checks, superseding the earlier finite-reproduction pending stage without certifying MC2.

**Analytic:** SP1-SP5's all-scale fixed-polynomial-head Nyman obstruction has Referee acceptance; retain its limsup and family scope, not every-scale divergence or rejection of the full basis. Current CR1-CR3 optimize a restricted OAI row rebase and show the physical all-selected annulus eventually misses that paid domain. They remain paper/self-audited; no nu or physical gain follows. M1-M6's November 4 CODIV logarithmic estimate is carry-forward evidence, not a fresh November 5 CODIV execution.

**Wheel:** F1-F4 refute the specified fixed-prime relaxation as a uniform CORR4 supplier, with auxiliary signs explicitly not genuine Mobius. P1-P4 require the finite-C prime block and both cross terms to cancel before any norm; the separate block scale is too large. PE1-PE4 are independently accepted by Referee-11. Their finite coefficient consequences are now verified at the unmerged #1096 head; the raw occurrence involution and PNT asymptotic are not silently included in that Lean result.

**Census:** the R=57/58 joint CORR4 gaps are exact finite evidence, not a uniform cap saving; Wheel's R=59 Y_7=71 correction is retained. Latest JOH JL1-JL4 show that deleting upper-halo windows changes the source and can reverse a lag sign: X=209 has full C_2=+1 but truncated C_2=-1. All-lags-negative is refuted, while full aggregate negativity through 128..8192 is only finite evidence. JL5's power accounting is conditional, not a new upper estimate.

**Referee:** PE1-PE4 acceptance and SP1-SP5 acceptance are retained at their scopes. R12-R13's low-depth sharp optimum and growing-depth argument remain that author's new paper work. R14's source admission and density have now been reconstructed here, with the stronger C64 optimality interpretation. C53-C61, MC2 and OAI CR1-CR3 have NOT acquired independent acceptance merely from this synthesis.

**Lean:** #1094's finite correction bound and #1095's audit repair are human-merged. #1096 is source-verified, exact-head CI_GREEN and REVIEW_READY, but UNMERGED. No unfinished CI repair is invented. Mathematical arithmetic suppliers remain open.

The external inbox blob **038018145c0fddb2f6306c0712373adf9cd1ea52** was read. There is no entry later than October 18. EXT-20261018-PNT-1..3, EXT-20261017-XCOORD-1 and EXT-20261014-5 retain exact-carrier, cutoff and unconditional-versus-first-bad safeguards; their old routing, PR-state and once-daily prose is historical. They supply no missing MU-LIFT recurrence.

### F. Mathematical Bottlenecks And Coverage

The selected exact quantitative gap is still, for a fixed k>=2 and an unbounded power chain B_(j+1)=B_j^k,

```text
exists fixed 1<=r<k, G_j>=1, log G_j/log B_j -> 0,
forall sufficiently large j, forall integer B_j<=X<B_j^k,
 |sum_(n<=X) heathBrownLift(mobiusPrefix(B_j-1),k)(n)|
       <= G_j E(B_j)^r sqrt(X).
```

At k=2 the left side is exactly |2M(B_j-1)-Q_(B_j-1)(X)|, with the entire ordered bilinear Q and both linear copies retained. A signed residual identity is target-equivalent at the same cutoff; it is not an independent upper-bound supplier. C63-C66 do not assume this inequality and do not prove it. PNT supplies the displayed macroscopic capacities only. The near-perfect typical-depth coverage, or a genuine signed norm estimate bypassing cardinality, is the first missing arithmetic for this matching mechanism.

| Protected route | Last substantive available attempt | Exact unpaid point / next action |
| --- | --- | --- |
| VF-LOW | Nov 5 Owner-2, CR1-CR5 | complete chronological donor/complement return beyond sparse populations |
| SAT | Nov 5 Owner-1, RC1-RC6 | joint OPEN-SAT-I, not the separately prime-error-equivalent packet; Owner next due |
| JOH | Nov 5 Owner-3, MC1-MC5 | independent MC2 audit, then stronger clock/weighted-level input |
| CODIV | Nov 4 Analytic-3, M1-M6 | OPEN-CD5 genuine signed lag power; Analytic next due |
| OAI-NNS | Nov 5 Analytic-2, CR1-CR4 | actual physical all-selected rows, not the disjoint smaller row cap |
| NYMAN | Nov 5 Analytic-1, SP1-SP6 | changed source or moment outside the retired fixed profile, full returned norm |
| FINITE-AC | Nov 5 Wheel-2, P1-P5 | complete four-block cancellation and original historical K budget |
| CORR4 | Nov 5 Wheel-1, F1-F4; Census finite support | actual cross-core arithmetic and all daughter labels; Wheel next due |
| MU-LIFT | Nov 5 Wheel-3, PE1-PE5; current Coordinator C63-C68 | new large-prime/typical-depth coverage or whole-prefix signed estimate |

These are actual report observations, not a fabricated synchronized round. Owner and Wheel completed their three owned turns on November 5; Analytic's rolling three substantive attempts are November 4 CODIV, November 5 NYMAN and OAI-NNS. The next distinct primary routes are SAT / CODIV / CORR4. Support work must not erase that rotation.

### G. Strategy Decisions

1. Retire a repeated fixed-bank 13/15 contraction as an unsigned MU-LIFT proof strategy. C64 computes its exact saturation; reusing the same negative credit or simply multiplying its one-step retained fraction is invalid.
2. Reject the broader small-prime-only absolute finish within C65's precise moving-bank scope. This is not a statement that all large-prime or signed methods fail.
3. Retain C66 as a new, genuinely admitted large-prime packet and a falsifiable repair of C65, but deprioritize adding more low-depth cohorts without a reason they control the typical-depth remainder. Its full cardinality remains linear, consistent with Referee-13.
4. Keep the three independent primary portfolios and SEARCH_BROAD. The prime-clock and CODIV logarithmic results deserve source/theorem audits; neither is a power gain. Do not move all support roles to this new matching argument.
5. Preserve #1096 for human review. Do not reopen green source, duplicate its endpoint-subset theorem, or ask Lean to encode an assumed recurrence. C63-C67 are paper work pending independent review.

No-circularity result: the sharp partition identities and finite matching principles are prior/generic infrastructure; the independent new restrictions are the explicit density/optimality, uniform isolated cohort and actual unused capacity. Their proofs use no desired Mertens bound. The full residual's sum still equals M(X), so renaming it is not a smaller final theorem. No source equality is promoted to an upper bound, and no finite test is promoted to an asymptotic result.

### H. Next Specialist Assignments

**Owner, primary SAT:** resume RC1-RC6's actual joint OPEN-SAT-I with E_R=-A_R-I_R and M(Y)=L_R+E_R+C_R. Resolve whether a proposed nonlocal signed cofactor relation preserves the true weights, endpoint and model complement and removes a binding loss, rather than paying the prime-error-equivalent Z_R alone. Output one independently proved proper-term bound or a precise counterexample. A recombination that still leaves the R^(85/48) certificate above the inherited 7/4 root power is not a bootstrap. C67 is a ready nontransfer warning, not an additional compulsory MU-LIFT job.

**Analytic, primary CODIV:** resume M1-M6 and OPEN-CD5, with the true Mobius coefficients, fixed-degree polynomial/AP source, owner-only masks and complete triangular lag kernel. Test one arithmetic restriction that supplies a fixed power beyond every-log savings after the full daughter and root-step return. Output an actual quantified correlation estimate or an exact failed transfer. Falsifiers must include site-dependent masks and changing frequencies, which are not covered by the old theorem. Do not repeat the paid maximal-window packing proof.

**Wheel, primary CORR4:** resume F2-F3 and Census's R=57/58 joint-core constraints. Ask whether an actual cross-core multiplicative relation, with all physical daughter cutoffs and complete mixed bill, imposes a scale-uniform deficit not already defeated by the per-root auxiliary construction. Reuse C53-C56's sub-square-root relaxation restriction rather than re-proving it. Expected output is a genuine arithmetic joint restriction or a legal countermodel at the stated relaxation. A non-Cartesian feasible set without an objective gap is not sufficient. C63-C66 are queued for the next MU-LIFT rotation, not a reason to skip CORR4.

**Census:** independently test C66's finite admission and nonreuse at X=16383: V consists of the six products of 103,107,109,113; the first donor is 15*547=8205. Retain all PE1 and R14 endpoints, both complete signed cross orientations and the strict upper-half cutoff. Test donor c prime versus R14's c-depth restriction, and a wrong small-bank classification as negative controls. Output exact pairs and a source-preserving full-sum certificate or the smallest failure; no trend fit or extended asymptotic scan. This strengthens or falsifies a proper packet only.

**Referee:** primary independent audit of the genuinely quantitative pending JOH MC2 transfer: check the exact external short-interval theorem range, integer sampling, arrival overshoot, upper halo and endpoint-shift prime bound. Output ACCEPT_WITH_SCOPE or the first missing hypothesis; finite JL4 does not certify the analytic theorem. Queue C63-C66 as a separate subsequent review: test the sharp core optimum, fixed-W versus moving-W distinction, PNT constants 1/50 and 1/30, prior-endpoint exclusion and inability of the repaired packet alone to change the linear residual. Earlier C58-C61 remain separately pending, not implicitly accepted.

**Lean Verification:** retain the exact green #1096 head and human-review gate; no CI rerun or repair is requested without a new failure or changed source. Its raw-occurrence PE3 and PNT asymptotic omissions are deliberate scope, not completed formalizations. No new implementation-sized task is activated for self-audited C63-C67. A previously qualified general Nyman localized Mellin interface may still be considered only if an active consumer needs it and its analytic prerequisites are available; otherwise an honest no-new-qualified-task report is preferable to a conditional recurrence wrapper.

These are published asynchronous assignments for future actual role executions. No other agent was launched, rescheduled or represented as working in the background.

### I. Lean And PR Status

The current open/draft collection contained only **#1096**, open and not draft, branch **agent/lean-verification/20261105-mobius-prime-escape**, head **ecf701ff2fea1de52e505ee34048a2b3c220f0fc**. All **14** head-associated workflows and **15** check jobs are completed/success. The exact source and dedicated workflow were read, not merely the PR body.

The actual [run 42150511056, job 127672350630](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42150511056/job/127672350630) contains successful warning-fatal import/type and ten-name axiom audit. Nine declarations use only propext, Classical.choice and Quot.sound; `upper_half_static_partner_eq` uses propext and Quot.sound. The final job reused three compiled source modules (compiled=0, cached=3) and freshly checked its audit harness; it is not described as three fresh source compilations. Tested synthetic merge **7783734bdc9960d3c2483af380759db85e87bc8f** has exactly current main and the final PR head as parents. Its tree **48b193cd105e21183b1cfd68b059894c8056f35c** equals the head tree. The source/axiom audit also traverses the unchanged genuine prefix/lift dependencies.

Qualified status: **PROVED_IN_LEAN at PR HEAD / CI_GREEN / REVIEW_READY / UNMERGED**. Principal theorem `RHLean.Proof.exists_prime_semiprime_residual` constructs equal-cardinality endpoint subsets and the exact signed remainder. The complete-square theorem and `heathBrownLift_sum_eq_prime_semiprime_residual` are exact consumers, not recurrence bounds. The sorted-list involution, raw binomial-occurrence PE3, exact capacity formula, PNT asymptotic and today's new claims are NOT asserted to be compiled there.

Recent main history was freshly inspected: #1093 flat-taper return, #1094 finite correction-energy obstruction and #1095 fail-closed Euler audit are human-merged. Prior report evidence for #1093/#1094 is preserved; no claim of rerunning those workflows is made. For #1095 this run directly reread [job 127444267657](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42084042187/job/127444267657), including the actual eight terminal declarations and multiline standard-axiom lists. Synthetic merge **55968fd690fea8b12f4602ab9dc9adf58bf00c60** has tree **6351bbacd22d7abb34eefed1e2cbf5f674642010**, identical to current main. Its repaired audit is valid evidence, not a new arithmetic result. No blanket fresh build of all main was performed.

Direct shell cloning was unavailable (CONNECT 403); authenticated GitHub reads and own-report publication worked. No local Lean execution, source change, proof branch, PR, merge, auto-merge, policy edit, other role report edit or schedule change occurred.

### J. Next-Run Resume Capsule

```text
RUN: 20261105-coordinator-3; scheduled 23:09:00 EST; RUN_ID_UNAVAILABLE.
MAIN: 1667c3cf9b4e898bb9afd62ec48e24610b2156ab.
POLICY: NO_PIGEONHOLING_ROUTE_SELECTOR_V1 / SEARCH_BROAD.
INTAKE_REPORTS: 8c525379f7fe53fa07b131965f0ca785592002b9.
EARLY_CHECKPOINT: 8ab16757f1c247718d868d7034e662121a81515d.
EARLY_BOTH_BLOBS: d3656c16594ff2f1e88f70ed1ce19e11f1a9ccdb; exact readback.
C63: exact outside-prime-core sums, sharp finite unsigned minimum;
     original ordered lift and ordered-pair-of-cores scope retained.
C64: Lambda_W=c_W X+O_W(sqrt X); c_195=157/(84 pi^2);
     R14 already saturates the entire fixed-bank leading capacity.
C65: all banks <=(4/5)sqrt X leave a rough-semiprime cohort
     ~X/(50 log^2 X), too large for the subcritical absolute certificate.
C66: unused 15q triples pay that cohort with genuine five-prime edits;
     preserves PE1/R14, still leaves a linear total remainder.
C67: mu sign cancellation does not transfer to two positive VF composites.
C68: exact finite checks; 2694 raw atoms, 3791564 ordered pairs; no fit.
REVIEW: C63-C67 SELF_AUDIT/PAPER_PROOF; independent review PENDING.
FORMAL: #1096 exact green head ecf701ff2fea1de52e505ee34048a2b3c220f0fc,
        REVIEW_READY and UNMERGED; #1095 repaired audit verified on main tree.
PRIMARY_NEXT: Owner SAT; Analytic CODIV; Wheel CORR4.
SUPPORT: Census C66 unused donor test; Referee MC2 external-source transfer.
FIRST_OPEN: genuine whole-prefix signed r<k recurrence or independently
           quantified typical-depth/large-prime coverage with full return.
NEXT_COORDINATOR: consume MC2/CODIV reviews or investigate a genuinely
                 quantitative joint source; do not optimize fixed-bank constants.
NET_NEW_ENDPOINT_GAIN: UNKNOWN / NONE_ESTABLISHED. Canonical VF and RH OPEN.
PUBLICATION: pending verified commit/readback receipt below.
```

### Appendix. Complete C68 Verifier

The following is the complete executed standard-library program. It requires no repository checkout, network or Lean installation. Its checks are exact finite arithmetic; all asymptotic conclusions above use the displayed separate proofs.

```python
"""Exact finite tests of fixed-prime core cancellation; no Lean or asymptotic fit."""

from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from math import comb, gcd, isqrt, prod
import json


def factor(n):
    out = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def trial_mu(n):
    f = factor(n)
    return 0 if any(e > 1 for e in f.values()) else (-1) ** len(f)


def sieve(n):
    mu = [1] * (n + 1)
    mu[0] = 0
    prime = [True] * (n + 1)
    prime[0:2] = [False, False]
    for p in range(2, n + 1):
        if prime[p]:
            for j in range(p, n + 1, p):
                mu[j] *= -1
                if j != p:
                    prime[j] = False
            for j in range(p * p, n + 1, p * p):
                mu[j] = 0
    return mu, [p for p in range(2, n + 1) if prime[p]]


def strip(n, primes):
    for p in primes:
        while n % p == 0:
            n //= p
    return n


def divisors(primes):
    ds = [(1, 1)]
    for p in primes:
        ds += [(p * d, -s) for d, s in list(ds)]
    return sorted(ds)


def core_sums(sites, bank, mu):
    out = defaultdict(int)
    for n in sites:
        out[strip(n, (2, *bank))] += mu[n]
    return {c: s for c, s in out.items() if s}


def integral(bank):
    ds = divisors(bank)
    breaks = sorted({x for d, _ in ds for x in (d, 2 * d)})
    total = F(0)
    for a, b in zip(breaks, breaks[1:]):
        sigma = sum(s for d, s in ds if d <= a < 2 * d)
        total += abs(sigma) * (F(1, a) - F(1, b))
    density_pi2 = F(4) * prod((F(p, p + 1) for p in bank), start=F(1))
    return total, density_pi2 * total


def prime_escape(x, pool, mu, primes):
    upper = {n for n in range(x // 2 + 1, x + 1) if n % 2 and mu[n]}
    top = [p for p in primes if x < 2 * p <= 2 * x]
    partners = sorted({s * q for s in pool for q in primes
                       if q > max(pool) and x < 2 * s * q <= 2 * x})
    t = min(len(top), len(partners))
    removed = set(top[:t]) | set(partners[:t])
    assert len(removed) == 2 * t
    assert removed <= upper
    assert sum(mu[n] for n in removed) == 0
    return upper, upper - removed, t


def raw_lift(b, k, x, mu):
    atoms = []
    seed = [n for n in range(1, b) if mu[n]]
    for j in range(1, k + 1):
        for aa in product(seed, repeat=j):
            v = prod(aa)
            if v > x:
                continue
            sign = (-1) ** (j - 1) * prod(mu[n] for n in aa)

            def visit(prefix, value, remaining):
                if not remaining:
                    for copy in range(comb(k, j)):
                        atoms.append(((j, copy, aa, prefix), value, sign))
                    return
                for q in range(1, x // value + 1):
                    visit(prefix + (q,), value * q, remaining - 1)

            visit((), v, j - 1)
    return atoms


def main():
    mu, primes = sieve(65535)
    assert all(mu[n] == trial_mu(n) for n in range(1, 2049))
    counts = Counter(independent_mu_checks=2048)
    banks = [(), (3, 5, 13), (3, 5, 7, 13), (3, 5, 7, 11, 13, 17)]
    constants = []
    for bank in banks:
        ii, cc = integral(bank)
        assert ii >= F(1, 2)
        assert 0 < cc <= 2
        constants.append({'bank': bank, 'integral': str(ii),
                          'residual_coefficient_times_pi_squared': str(cc)})
    assert integral((3, 5, 13)) == (F(157, 195), F(157, 84))
    ds = divisors((3, 5, 13))
    possible = [(a, b) for (a, sa), (b, sb) in combinations(ds, 2)
                if sa != sb and b < 2 * a]
    assert possible == [(13, 15)]

    cutoffs = list(range(4, 161)) + [255, 511, 1001, 1155, 2001, 2002, 4095, 65535]
    records = []
    p9 = (3, 5, 7, 11, 13, 17, 19, 23, 29)
    for x in cutoffs:
        upper, residual, t = prime_escape(x, p9, mu, primes)
        assert sum(mu[n] for n in upper) == sum(mu[1:x + 1])
        for bank in banks:
            sums = core_sums(upper, bank, mu)
            assert sums == core_sums(range(1, x + 1), bank, mu)
            form = {}
            modulus = 2 * prod(bank)
            for c in range(1, x + 1):
                if mu[c] and gcd(c, modulus) == 1:
                    signed = mu[c] * sum(s for d, s in divisors(bank)
                                         if d * c <= x < 2 * d * c)
                    if signed:
                        form[c] = signed
            assert sums == form
            best = sum(abs(v) for v in sums.values())
            after = sum(abs(v) for v in core_sums(residual, bank, mu).values())
            assert abs(after - best) <= 2 * t
            counts['core_formula_cases'] += 1
            counts['exception_lipschitz_cases'] += 1

        pairs = [(13 * c, 15 * c) for c in range(1, x // 15 + 1)
                 if mu[c] and gcd(c, 390) == 1 and x < 26 * c]
        flat = [n for pair in pairs for n in pair]
        assert len(flat) == len(set(flat))
        assert set(flat) <= upper
        assert all(mu[a] == -mu[b] for a, b in pairs)
        l195 = sum(abs(v) for v in core_sums(upper, (3, 5, 13), mu).values())
        assert l195 == len(upper) - 2 * len(pairs)
        usable = [(a, b) for a, b in pairs if a in residual and b in residual]
        after_best = sum(abs(v) for v in core_sums(residual, (3, 5, 13), mu).values())
        assert after_best == len(residual) - 2 * len(usable)
        high = [(a, b) for a, b in pairs if len(factor(a // 13)) >= 2]
        assert all(a in residual and b in residual for a, b in high)
        r14 = len(residual) - 2 * len(high)
        assert 0 <= r14 - after_best <= 2 * (len(pairs) - len(high))
        counts['sharp_195_cases'] += 1
        if x in (1155, 2001, 2002, 4095, 65535):
            records.append({'X': x, 'upper': len(upper), 'prime_pairs': t,
                            'L195': l195, 'all_13_15_pairs': len(pairs),
                            'after_PE_optimum': after_best, 'R14_left': r14,
                            'M': sum(mu[1:x + 1])})

    rough_records = []
    for x in (4095, 16383, 65535):
        y = isqrt(16 * x // 25)
        bank = tuple(p for p in primes if 2 < p <= y)
        ps = [p for p in primes if 16 * x < 25 * p * p and 100 * p * p <= 81 * x]
        witnesses = [p * q for p, q in combinations(ps, 2)]
        assert len(witnesses) == len(set(witnesses)) == comb(len(ps), 2)
        _, residual, _ = prime_escape(x, p9, mu, primes)
        for n in witnesses:
            assert x < 2 * n <= 2 * x and mu[n] == 1
            assert strip(n, (2, *bank)) == n and n in residual
        r14_pairs = [(13 * c, 15 * c) for c in range(1, x // 15 + 1)
                     if mu[c] and gcd(c, 390) == 1 and x < 26 * c
                     and len(factor(c)) >= 2]
        r14_used = {n for pair in r14_pairs for n in pair}
        remaining = residual - r14_used
        donors = [15 * q for q in primes if q > 13 and x < 30 * q <= 2 * x]
        assert len(donors) >= len(witnesses)
        new_pairs = list(zip(sorted(witnesses), donors[:len(witnesses)]))
        new_used = {n for pair in new_pairs for n in pair}
        assert len(new_used) == 2 * len(witnesses)
        assert new_used <= remaining
        for a, b in new_pairs:
            assert mu[a] == 1 and mu[b] == -1
            assert len(set(factor(a)) ^ set(factor(b))) == 5
        final = remaining - new_used
        assert sum(mu[n] for n in final) == sum(mu[1:x + 1])
        signed = sum(mu[n] for n in final)
        v = len(witnesses)
        assert v*v + v*v + signed*signed - 2*v*v + 2*v*signed - 2*v*signed == signed*signed
        counts['large_prime_escape_pairs'] += len(new_pairs)
        counts['growing_bank_isolated_witnesses'] += len(witnesses)
        rough_records.append({'X': x, 'y': y, 'band_primes': ps,
                              'isolated_positive_semiprimes': len(witnesses),
                              'unused_negative_15q_donors': len(donors),
                              'new_pairs': new_pairs,
                              'complete_final_remainder': len(final)})

    raw_records = []
    for b, k, x in ((4, 2, 15), (8, 2, 63), (3, 3, 26), (4, 3, 63)):
        atoms = raw_lift(b, k, x, mu)
        assert len({a[0] for a in atoms}) == len(atoms)
        coefficients = Counter()
        by_core = Counter()
        for _, n, s in atoms:
            coefficients[n] += s
            by_core[strip(n, (2, 3, 5, 13))] += s
        assert all(coefficients[n] == mu[n] for n in range(1, x + 1))
        expected = core_sums(range(1, x + 1), (3, 5, 13), mu)
        assert {c: s for c, s in by_core.items() if s} == expected
        pair_cores = Counter()
        for _, n, s in atoms:
            for _, m, t in atoms:
                pair_cores[(strip(n, (2, 3, 5, 13)),
                            strip(m, (2, 3, 5, 13)))] += s * t
        best = sum(abs(v) for v in expected.values())
        assert sum(abs(v) for v in pair_cores.values()) == best * best
        assert sum(pair_cores.values()) == sum(mu[1:x + 1]) ** 2
        counts['raw_atoms'] += len(atoms)
        counts['ordered_raw_pairs'] += len(atoms) ** 2
        raw_records.append({'B': b, 'k': k, 'X': x, 'atoms': len(atoms),
                            'core_absolute_square': best * best,
                            'actual_square': sum(mu[1:x + 1]) ** 2})

    # A new large-prime edit escapes the invariant, but is not old-bank closure.
    assert 17 * 2 > 31 and 3 * 7 * 2 > 31
    assert mu[17] == -mu[21]
    assert strip(17, (2, 3, 5, 13)) != strip(21, (2, 3, 5, 13))
    assert 13 * 77 <= 2001 < 26 * 77
    assert not (2002 < 26 * 77)
    # Genuine VF carrier mismatch: both are nonsquare composite odd seats.
    for n in (1001, 1155):
        r = isqrt(n)
        assert r * r < n < (r + 1) ** 2 and len(factor(n)) >= 3
    counts['negative_controls'] = 3
    print(json.dumps({'counts': dict(counts), 'constants': constants,
                      'fixed_bank_records': records, 'rough_records': rough_records,
                      'raw_records': raw_records,
                      'scope': 'Exact finite identities; no asymptotic extrapolation.'}, indent=2))


if __name__ == '__main__':
    main()
```


### Publication Freshness

At 2026-11-06 04:34:04 UTC, the main refresh remained **1667c3cf9b4e898bb9afd62ec48e24610b2156ab** and the sole open PR remained #1096 at **ecf701ff2fea1de52e505ee34048a2b3c220f0fc**, non-draft and unmerged. The reporting branch was still the verified early checkpoint **8ab16757f1c247718d868d7034e662121a81515d**. Both own report blobs and all unchanged specialist blobs were checked before writing. The full previous report and checkpoint remain an exact prefix. All ten A-J sections, balanced code fences and the complete executed verifier were checked. Execution publication remains PENDING_READBACK until the receipt; independent mathematical review remains PENDING.

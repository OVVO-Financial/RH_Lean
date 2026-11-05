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

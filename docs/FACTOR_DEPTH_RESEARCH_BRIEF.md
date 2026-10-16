# Live research brief: factor-depth coupling and independent amplification

**Revision: 2026-10-16, after #961 merged on `main@df47c8ae0e751ce12bd0e493156a957d86e02ee4` and the unified manual cycle.** Read this file from current main every invocation, after [AGENTS.md](../AGENTS.md) and [CURRENT_PROOF_CONTRACT.md](../CURRENT_PROOF_CONTRACT.md). The target and permissions are unchanged. The candidates below are research hypotheses, not asserted new bounds. MU-LIFT work also reads the [subpower amplification budget](MERTENS_AMPLIFICATION_BUDGET.md).

## 1. What the overnight cycle actually changed

The raw odd-seat census gave an exact complete partition into historical-prime/distinct-semiprime tag charges and the remaining squareful/higher-factor composite mass. At R=3162, the reported tag sum is about -368057.434014, the residual about +368388.745488 and the total about 331.311475. The large components, not only bounded local owner packets, must be explained. Integer populations were independently checked; weighted decimals are numerical diagnostics, not certified intervals or an all-scale theorem.

Evidence: [Census, 2026-10-15](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-10-15/40-prime-census.md), claims census-1 through census-4, blob `2e3c1cf95cd11669d57d2ce1f7216916736ff095`; [Referee](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-10-15/50-adversarial-referee.md), blob `cf0db85f6b04c56527bc9a26a1b6741ae196435a`.

**Updated leading question:** after the exact reported A/B cut identity, what independently provable NEW signed arithmetic input (not just regrouping) can control the original source? Examine a complete genuine-Mobius Type II/hyperbola source estimate, or a genuinely distinct Nyman/nonlocal mechanism; pure raw-sector reassembly is provisionally suspended. Merely asserting that their mismatch is O(R log R) restates the endpoint target. Prefer a new restriction, exact transport with a separately controlled defect, or a weaker uniform estimate that reveals the missing mechanism.

## 2. Fixed source dictionary

For natural R>=3:

```text
C_R = {(r,n): 2<=r<R, r^2<n<(r+1)^2, n odd}.
w_r = (2*r+1)/(r*log(r^2+r+1/2)).
c(r,n) = w_r - 1_Prime(n).
L_R = sum_(C_R) c(r,n).
```

For odd prime tags q with 5<=q<R^2, let `X_R(q)` sum `w_floor(sqrt(p*q))` over odd primes p<q, p*q<R^2; put `Y(q)=1-w_floor(sqrt(q))`, `G_R(q)=X_R(q)-Y(q)` and `T_R=sum_q G_R(q)`. Define `H_R` as the positive native weight of **every other composite seat**. Unique factorization gives the paper-level exact identity

```text
L_R = T_R + H_R.
```

H_R includes squarefree factor depth at least three and squareful seats that actually lie in C_R; strict square boundaries exclude perfect squares. Distinguish total prime-factor multiplicity Omega(n), number of distinct prime factors omega(n), and squarefree status. For the displayed convention, telescoping gives `L_R=F_R-pi(R^2)+2`; the canonical defect is `2-sqrt(2)-L_R`. A native Lean bridge still requires checking the actual definitions; this doc does not certify one.

Three carriers must remain separate: **eligible ancestry**, **raw C_R**, and **literal masked/clipped first-bad returned cells**. An exact result for the first or second is not automatically source admission to the third. This separation applies to both positive claims and counterexamples.

The square `L_R^2=T_R^2+H_R^2+2*T_R*H_R` retains the cross-depth interaction. T_R itself has within-tag and cross-tag interactions. The global zero-target NNS statistic uses its original coefficients and normalization; neither a diagonal sum nor a mean-centered correlation replaces it. The raw square is not automatically the compressed #915 norm.

### October 16 accepted support geometry and corrected compensation target

**Merged and Lean verified:** [PR #958](https://github.com/OVVO-Financial/RH_Lean/pull/958) introduced `RHLean/Proof/OddResidualCofactorSupport.lean` and proved that `1<m<R^2`, an odd `canonicalCofactor m` and the explicit exclusions in `IsOddFactorDepthResidual m` imply `9*canonicalLargestPrimeFactor m<R^2`. The strict prime-square exclusion matters. The module does **not** formalize the full raw `H_R` bijection or prove returned-cell admission, signed cancellation or a quantitative endpoint bound.

**Raw carrier, PAPER_PROOF:** by the Wheel report every positive `H_R` seat has unique `n=a*q`, odd composite cofactor `a>=9` and greatest prime `q<R^2/9`. But the negative upper tag tail is

```text
A_R = sum_(prime q: R^2/3 < q < R^2) G_R(q),
B_R = L_R - A_R  =  (lower prime-tag charges) + H_R.
```

Thus **direct greatest-tag-preserving `A_R -> H_R` incidence is empty**. A direct `A_R -> B_R` transport could still involve lower-tag terms; it must be fully specified rather than inferred from the support gap. Coordinator's PNT theorem gives `A_R=-(1/3+o(1))*R^2/log R` and `B_R=(1/3+o(1))*R^2/log R`, **not** an `A_R+H_R` compensation theorem. Its unbounded relative `o` remainder falls far short of the `O(R log R)` canonical target. Preserve `L_R^2=A_R^2+B_R^2+2*A_R*B_R` and, inside `B_R`, all existing `T_R/H_R` and complete zero-target NNS terms.

**Growing cofactor requirement (PAPER_PROOF, not in #958):** for each fixed finite odd composite set `S`, `H_R(S)/H_R -> 0`. The Referee sharpens fixed layers to `H_R(a)~2*R^2/(a*log^2(R^2))`, versus `H_R >> R^2/log R`. Census proved `a^k < (R^2)^(k-1)` when `k=Omega(n)`, hence `a^(j+1)>=(R^2)^j => Omega(n)>=j+2`. Numerically, the top 15 cofactors account for only 14.27% of residual mass at `R=5000`; this is a **finite diagnostic**, not an asymptotic mass-band theorem.

**Mechanism status:** REJECT same-greatest-tag `A_R -> H_R` matching and any fixed finite `H_R` cofactor backbone as complete explanations; CONTINUE/REVISE growing-cofactor, cross-tag transport for the **complete** signed complement. Next smallest real input: specify a signed transition kernel/bijection or weighted defect on dyadic cofactor bands `A<=a<2A`, including lower-tag charges, moving boundaries and the actual quadratic cross terms. Prove a uniform restriction **independently**, even weaker than the target, and recombine before taking norms. The Owner `q -> 3q` boundary packets are distinct semiprimes in `T_R`, not `H_R` mass.

Paper sources: [Wheel (Oct 16)](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-10-16/30-finite-wheel.md), [Census (Oct 16)](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-10-16/40-prime-census.md), [Referee (Oct 16)](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-10-16/50-adversarial-referee.md). Prior exact local crossings: [Owner (Oct 15)](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-10-15/10-owner-payment.md). Always re-fetch for later corrections.

### Post-#961 unified-cycle evidence and scoped directions

**Merged, kernel-proved:** [PR #961](https://github.com/OVVO-Financial/RH_Lean/pull/961) adds `RHLean/Proof/RootWallCompleteFibre.lean`: for prime `q>=R` the canonical greatest-prime fibre below `R^2` consists of its positive multiples with multiplier `a<q`, with non-square and explicit odd residual classification. Together with merged #958, this is **incidence/support**, not a weighted source or signed sum bound. Do not duplicate these declarations.

**PAPER_PROOF / INDEPENDENT_REVIEW_REQUIRED (one self-audited manual AI cycle):**
```text
x=R^2
A_R = sum_(prime x/3<q<x) (w(q)-1)
B_R = F_R+2-pi(x/3)-sum_(prime x/3<q<x) w(q).
```
The exact `A_R+B_R=L_R` cancellation is `IDENTITY_ONLY`, not an independent payment. The claim `|B_R-B*_R|=O(R log R) iff RH` uses a **specific** `B*_R` smooth model from Owner `20261016-owner-5` and has not yet had an independent human/agent referee proof check. Do not generalize the equivalence to every cutoff/model.

**Root-scale prime-reciprocal band:** distinguish `E_prime(y)=sum_(p<=y)1/p-log(log y)-M_Meissel` from `E_mu(B)=max_(1<=n<B)|M(n)|/sqrt(n)`. Owner `20261016-owner-3` states the paper identity `T_R-M_R^band=F_R*(E_prime(2R-1)-E_prime(R-1))+rho_R`, `rho_R=O(R/log^2 R)`. Owner `-4` argues from the known zeta zero near `1/2+14.13i` that `T_R-M_R^band` is **not** `O(R^(3/2-delta))` for any fixed positive delta. Analytic `-4` states a restricted `1/2<=theta<2/3` family. These **paper** no-gos apply to the named band **against the named prime-free main term**, and do NOT refute full cross-band cancellation or an explicit oscillatory main term. Independently audit the Mellin continuation, branch passage, arithmetic sampling and claimed exponent before declaring the method excluded.

**Type II potential, not a unique proven closure:** Analytic `20261016-analytic-1` gives `M(X)=2M(N)+K1-K2+K3`, `N=B-1`, `B<=X<B^2`, with genuine `mu(i)mu(j)` and hyperbola cutoff `ij<=X`; see [amplification budget](MERTENS_AMPLIFICATION_BUDGET.md). A proposed `X/H<ij<=X` slice of `K3` requires explicit `H`, all remaining `K3` ranges, exact `K1/K2` cancellation, original signed coefficients and full-prefix coverage. A suggested `ij -> X/(ij)` reflection is **not** automatically an integral bijection; prove a signed lattice transformation or exact weighted identity with every boundary term. Do not infer new exponent improvement from a shorter but otherwise identical sum.

**Disposition:** PROVISIONALLY SUSPEND pure raw A/B regrouping and stand-alone sector estimates about the specified main terms; MERGE inverse root-band prime-reciprocal configurations into their cut-mode audit; CONTINUE genuine signed MU-LIFT research and truly independent Hilbert/nonlocal inputs. These are research priorities, not a claim that every possible sector partition is RH-equivalent or supertarget. No quantitative progress toward the canonical bound, finite A/C or RH was made. Dated evidence: [Owner](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-10-16/10-owner-payment.md), [Analytic](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-10-16/20-analytic-type-ii.md), [Referee self-audit](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-10-16/50-adversarial-referee.md), [Census](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-10-16/40-prime-census.md).

## 3. Active and suspended mechanisms after #961

### FD-TRANSPORT: signed depth-transition law

**PROVISIONALLY SUSPENDED as a pure raw-seat route.** The proposed complete cross-tag A/B reassembly is now the exact cut identity and has no independently paid remainder. **Only consider revival** via a genuinely new sieve/Buchstab/Vaughan/Mobius or native-source identity with a separately proved quantitative input that preserves each original signed term. This paper disposition is scoped, not a proof excluding every cross-band mechanism.

Owner should write the actual occurrence map or operator, not just label the desired remainder small. Preserve fresh-prime/coprimality conditions, multiplicities, weight changes `w_floor(sqrt(n*q))-w_floor(sqrt(n))`, new squareful contacts, physical boundaries, cutoff changes and all unmatched terms. A weighted conservation law must include its exact weighting defect; equal unweighted counts do not imply weighted cancellation.

A first successful result may be an exact transition identity plus a new sign, support restriction or weaker explicit remainder bound. Quantify accumulated loss before claiming endpoint relevance. Nonlocal response-weighted analysis is a possible version only if it supplies a genuinely new property of the response, not the old Duhamel equality under a new name.

**Decisive test:** declare a native-weight **signed** observable for both the upper `A_R` and the complete `B_R`, stratify B by lower-tag versus residual and growing cofactor/`Omega`, then derive a measurable prediction about its constrained ancestry pairs before scanning. Compare genuine data with a declared control that preserves specified layer populations but breaks the proposed ancestry relation. Failure may expose a missing squareful or boundary term. Controls are synthetic and never proof of arithmetic independence.

### INV-CONFIGURATION: inverse structural obstruction

**MERGE, when it is only the root-band prime statistic.** Wheel `20261016-wheel-5` identifies a band imbalance with a prime-reciprocal Mertens error increment and independently bounds it at classical PNT strength. A distinct inverse route needs a newly specified configuration and an independently *stronger* arithmetic restriction, not the same cut mode in different notation.

Wheel and Referee should separate the two theorems: (i) imbalance implies a named configuration, with constants and all hypotheses; (ii) genuine arithmetic restricts that configuration independently of the endpoint bound. A configuration defined simply as 'the mismatch is too large' is circular. A capacity bound on unrelated support is insufficient. Search for a minimal actual counterexample or sharp boundary before widening a wheel.

**Decisive test:** determine a cross-tag/cofactor-band observable on which this inverse proposal and FD-TRANSPORT make different predictions; same-tag `A_R -> H_R` incidence is already proved empty, not an open experimental candidate. If they use the identical unpaid inequality, merge them into one lane and develop a truly different alternative. No arbitrary map between tags is allowed without preserving the physical coefficient and compensations.

### MU-LIFT: genuine finite-prefix signed amplification and the complete Type II anatomy

**New research emphasis:** seek a truly signed shortening identity or independent Type II estimate in the exact `K1/K2/K3` hyperbola decomposition. The `K3` corner is a candidate, **not** sufficient by itself. The fixed `(r,g)` implication is conditional: chain coverage gives a zero-free boundary at `1/2+2g/(2-r)`, all-`B` coverage can improve it to `1/2+g/(2-r)`; a proven nontrivial gain would therefore already be a substantial zeta-zero result. A finite observed ratio is not this theorem. Distinguish the prime-reciprocal `E_prime` from the `E_mu` budget.

**Distinct current baseline:** [MERTENS_FINITE_PREFIX_EXTENSION.lean](../research/MERTENS_FINITE_PREFIX_EXTENSION.lean) proves the genuine Newton support extension B -> B^2. Merged #954 adds [higher-order signed lifts](../research/MERTENS_HEATH_BROWN_SIGNED.lean), exact B -> B^k coefficient reconstruction, and the [complete signed hyperbola bridge](../research/MERTENS_SIGNED_HYPERBOLA.lean). Neither support extension nor reindexing bounds the remaining signed summatory gain.

**Relaxed acceptance rule:** use `E(B)=max_(1<=n<B)|M(n)|/sqrt(n)`. An independently proved rule `E(B_j^2)<=G_j*E(B_j)^r` with fixed `1<=r<2` and `log G_j/log B_j -> 0` suffices on one eventually valid square-growing chain. Constants and the old budget may be large. Polylogarithmic gain is sufficient but **not necessary**; `exp(sqrt(log B))` and `exp(log B/log log B)` are also subpower. The normalized recurrence is `u_(j+1)<=(r/2)*u_j+g_j/2`, and the full-prefix definition supplies the all-cutoff passage. The [amplification note](MERTENS_AMPLIFICATION_BUDGET.md) contains the paper proof, exact accumulation and qualifications.

**Independent arithmetic target:** for N=B-1 and every integer B<=X<B^2, seek `|2*M(N)-Q_N(X)|<=G_j*E(B)^r*sqrt(X)` with the original signed floor form `Q_N(X)=sum_(i,j<=N)mu(i)*mu(j)*floor(X/(i*j))`. The old prefix is automatically dominated when G_j>=1,r>=1,E(B)>=1. An endpoint-only estimate needs an independent interval argument. The actual minimal-gain subpower condition is target-equivalent; naming or assuming it is not the new input.

Analytic should report **scale power k, final amplitude-budget power r, gain G, normalized loss g, full interval/chain and independent arithmetic ingredient**. Normalize squared-energy bounds consistently before comparing r to k. For a separately proved fixed-k whole-prefix inequality, r<k suffices; exact higher-order support alone does not prove that bound, and constants depending on a varying k need new control. Fixed r<2 or a uniform gap is essential to the stated square-scale argument; merely r_j<2 with r_j approaching two is insufficient.

**Decisive test:** use the committed [finite-extension experiment](../experiments/mertens_finite_extension/) and [signed-lift diagnostics](../experiments/mertens_signed_lift/), retaining all cross-row and alternating-component terms. For fixed candidate r, record complete-prefix maxima and `log(max(1,E(B^k)/E(B)^r))/log B`, not just a last-endpoint value or a large finite loss ratio. Distinguish prefix-derived prediction, independent future-data validation and certified full-interval coverage. Finite decreasing costs do not prove subpower asymptotics. The #954 sparse arbitrary-prefix control must be excluded by actual Mobius restrictions, not by scalar prefix size alone.

The completed [Mertens converse](../research/MERTENS_CONVERSE_IDENTIFICATION.lean) gives the bidirectional coordinate identification. Do not assign re-proving it. A generic contraction/full-prefix consumer is a legitimate conditional formalization candidate after duplicate search, but cannot be reported as proof of the arithmetic gain. Keep genuine finite A/C and the independent factor-depth/inverse lanes distinct.

## 4. Mandatory regression set, with carrier qualifiers

Reuse these results at unchanged dependencies; do not rerun a large scan merely to reconfirm them. Apply each to a proposed theorem only when its actual hypotheses match.

| Regression | Exact lesson and scope |
| --- | --- |
| Raw cap four: R=15, q=17; products 51,85,119,187,221 | Five distinct semiprime descendants with one historical prime refute unrestricted raw global cap-four allocation. They do NOT refute the compiled local theorem with its specific window/eligibility assumptions or prove later returned-cell admission. Referee-3 is the small exact witness. |
| Same-tag NNS sign reversal: q=11534351, owners 3 and 5 | Two negative isolated slacks become a positive once-history grouped slack, with paper lower bound 737/15360. Do not add isolated slacks or infer quadratic payment from linear packet negativity. This is genuine ancestry, not yet a masked-source admission theorem. |
| Repeated history: q=1000000007, 111 descendants in the reported half-run | One physical historical charge cannot be reused 111 times. Finite native-weight overload is not a complete-source first-bad counterexample. |
| Full depth ledger: R=500,1000,2000,3000,3162 | Direct reconstruction includes all squareful/higher-factor mass; identity and observed compensation are not a new mismatch bound. R=3162 was the original held-out endpoint, not permanently fresh validation data. |
| Merged #958 canonical cofactor support | PROVED_IN_LEAN_ON_MAIN: `IsOddFactorDepthResidual m`, odd cofactor and `m<R^2` imply `9*P+(m)<R^2`. This is support only; do not pretend the paper raw `H_R` set equivalence, PNT cancellation or returned-cell admission is compiled. |
| October 16 raw tag support | `H_R` cofactor `a>=9` forces `q<R^2/9`, while `A_R` has `q>R^2/3`. Reject greatest-tag-preserving `A_R -> H_R` only. The complementary signed sector is full `B_R=L_R-A_R`, not `H_R` alone. |
| Fixed-cofactor no-go / staircase | PAPER_PROOF: `H_R(S)/H_R -> 0` for fixed finite S; `a^(j+1)>=(R^2)^j` forces `Omega(n)>=j+2`. No inferred bound on signed `A_R+B_R`; do not rerun the 7,160,321-occurrence R=5000 census unchanged. |
| Raw tag monotonicity | The paper theorem is only on prime tags q>=R: G_R(q) is nonincreasing, hence at most one positive-to-nonpositive transition. It does not imply transition existence, strict margins or monotonicity on q<R. |
| Centered sitewise Li correction | Analytic-6 has `C(X)=-(1/2)*log(log X)+O(1)`. This defeats a uniformly summable scalar correction, not every nonlocal/response-weighted method. Its raw-prime finite check is not a direct numerical verification of every centered Li-increment term. |
| Finite-extension negative control | PR #951 reports the first unit 0.45 failure at n=30770121 with M(n)=-2343, despite successful smaller interval certificates. This is executable finite evidence, not a Lean numerical theorem. It rejects automatic perpetual guard preservation, not every weaker signed amplification law. |
| Amplification boundary controls | The synthetic E(B)=B^delta shows r=k is insufficient at scale B -> B^k. A vanishing gap r_j->2 can also fail despite subpower gain; the exact countermodel is in the amplification note. Neither model is a counterexample about actual mu. |
| Arbitrary scalar prefix | #954's sparse a(1)=1,a(2)=-1 control defeats arguments for all bounded scalar-prefix inputs. Proposals must use genuine Mobius constraints and preserve all signed families. |

Owner sources: [2026-10-14 report](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-10-14/10-owner-payment.md), owner-5 through owner-8, blob `4f39c1690ee4cee0a00d4ebd0d08323f06d6c75d`. The exact same-tag polarization in that report is `H(U+V,y)=H(U,y)+2*V*(3*y-U)-V^2`, with `H(W,y)=(W+y)^2-2*(W-y)^2`. This H is a local slack, **not** the residual H_R defined above.

Analytic source: [2026-10-14 report](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-10-14/20-analytic-type-ii.md), analytic-6, blob `3a6932d9c5e1474adf1f34374310c7b73eb71fc2`. Wheel source: [2026-10-15 report](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-10-15/30-finite-wheel.md), wheel-1..3, blob `6d451c35eef4021fcff78253bed609d193c249c1`.

### Post-cycle scoped regressions

- **#961 merged:** root-wall complete fibre and explicit odd-residual characterization are kernel-proved; full weighted raw charge, band identity and signed estimate are *not*.
- **Owner cut and equivalence:** the exact A/B cut is raw-paper bookkeeping. The claimed `B_R-B*_R` iff RH for a specific B* has only one-session self-audit; next independent Referee must examine the bootstrap before treating it as settled.
- **Band and prime reciprocal:** paper `[R,2R)` formula plus stated oscillation; no all-sector no-go. Finite `R=1000..5000` and segmented `R~1.1e8` diagnostics are source-referenced, not certified asymptotics. Reuse published data.
- **K3 decomposition:** full signed pair support `ij<=X`; require all `K1,K2,K3`, every subregion and exact `H` when testing a corner. Reject a purported involution unless defined on actual integer lattice with exact signs, multiplicities and cutoffs.
- **Single manual seven-role cycle:** one actual invocation, one AI self-audit; do not count it as seven scheduled runs or independent mathematical confirmation.

## 5. Census acceptance: discover a restriction, not a fitted residual

A new experiment specifies in advance its two competing explanations, precise observable, rejection criterion, endpoint convention, scale range and held-out cases. Always label a root R separately from a cutoff x; `R=317` and `x=317` are different experiments.

Use directly classified native seats to report **the signed A/B partition**, positive `H_R`, *all lower-tag contributions inside B*, cofactor bands, `Omega`, boundaries and the actual constrained cross terms needed by the candidate. A positive `H_R` histogram alone is not the missing signed compensator. Exact population conservation and independently recomputed endpoint totals are required checks. A complement computed from the already-known endpoint is a checksum, not independent evidence of compensation.

Do not call the matrix of products of aggregate layer totals a newly discovered pairwise law: it is algebraically rank one. For covariance claims identify the actual occurrence-level kernel, restrictions and normalization. Keep zero target and original coefficients; mean-centering or deleting cross terms changes the question.

Distinguish exact integer/rational comparisons, floating logs, arbitrary precision and certified error intervals. Near-zero signs need a certified inequality before supporting a proof claim. Preserve source code or an executable reproducer, input/seed hashes and actual commands. Report failed candidates and untested tails. Use finite evidence to propose a theorem; never promote the fit to one.

## 6. Next-role handoffs and stopping rules

**Coordinator:** register #961 as MERGED, the manual cycle as one self-audited invocation, and its paper no-gos as independent-review-pending. Suspend pure-sector routes provisionally, without asserting all sector methods impossible. Rank distinct Type II, Nyman-Hilbert and new nonlocal input hypotheses.

**Owner:** independently test the cut identity and the specific `B_R-B*_R` RH bootstrap. If renewing owner payment, supply a NEW native signed source/sieve theorem with a separately paid estimate and complete covariance; do not rederive A+B.

**Analytic:** independently scrutinize owner-4 Mellin/zeta-zero argument and analytic-3 fixed-(r,g) calibration. Test the exact K1-K2+K3 signed hyperbola structure; work toward an actual, quantified full-prefix bound only with independent arithmetic input. Keep Nyman-Hilbert distinct.

**Wheel:** find an exact **integer-lattice** involution or other arithmetic support restriction on K3 and the actual floor/divisor carrier, including repeated-prime and boundary cases. Check whether any claimed reduction actually shortens complexity and transports back with losses accounted for.

**Census:** reuse `research/agent_reports/2026-10-16/manual-cycle/` reproducer; preregister one decisive K3/integer-pair symmetry or alternative test and retain K1/K2, other K3 regions, full signed μ and held-out endpoints. Do not rerun the 2e9 sieve or R<=5000 ledger just for size.

**Referee:** **independently** audit owner-4 band oscillation, owner-5 B* ⇔ RH equivalence, analytic-3 chain/all-B exponent differences, analytic-4 theta range and whether the K3 corner is genuinely distinct. A same-session self-audit is not independent validation. Keep any no-go within its exact carrier and quantifiers.

**Lean:** treat #958 and #961 as merged infrastructure; search source for existing identity first. If a genuinely new, independently reviewed theorem exists, formalize it on the authorized branch with exact-head CI and axiom checks. Conditional gain consumers are not numerical gain proofs; no filler PR.

Every report specifies its independent fact, claim strength/status, exact carrier, missing source arrows, newly falsified hypothesis and smallest next arithmetic test. The canonical endpoint and global payment remain open. No scheduled role edits shared instructions or merges a PR.
# Live research brief: factor-depth coupling and independent amplification

**Revision: 2026-10-15. Baseline inspected: `main@df353c9d40c660cc247bd2fdb96c536c74b04fe3`.** Read this file from current main every invocation, after [AGENTS.md](../AGENTS.md) and [CURRENT_PROOF_CONTRACT.md](../CURRENT_PROOF_CONTRACT.md). The target and permissions are unchanged. The candidates below are research hypotheses, not asserted new bounds.

## 1. What the overnight cycle actually changed

The raw odd-seat census gave an exact complete partition into historical-prime/distinct-semiprime tag charges and the remaining squareful/higher-factor composite mass. At R=3162, the reported tag sum is about -368057.434014, the residual about +368388.745488 and the total about 331.311475. The large components, not only bounded local owner packets, must be explained. Integer populations were independently checked; weighted decimals are numerical diagnostics, not certified intervals or an all-scale theorem.

Evidence: [Census, 2026-10-15](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-10-15/40-prime-census.md), claims census-1 through census-4, blob `2e3c1cf95cd11669d57d2ce1f7216916736ff095`; [Referee](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-10-15/50-adversarial-referee.md), blob `cf0db85f6b04c56527bc9a26a1b6741ae196435a`.

**Leading question:** find an independently provable arithmetic relation coupling the negative tag mass to the positive higher-depth mass, with the full physical signed statistic retained. Merely asserting that their mismatch is O(R log R) restates the endpoint target. Prefer a new restriction, exact transport with a separately controlled defect, or a weaker uniform estimate that reveals the missing mechanism.

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

## 3. Initial competing mechanisms

### FD-TRANSPORT: signed depth-transition law

**Hypothesis to develop:** a genuine prime-adjoining, divisor, involution or telescoping relation transfers native signed mass between factor-depth layers with an independently controlled residual.

Owner should write the actual occurrence map or operator, not just label the desired remainder small. Preserve fresh-prime/coprimality conditions, multiplicities, weight changes `w_floor(sqrt(n*q))-w_floor(sqrt(n))`, new squareful contacts, physical boundaries, cutoff changes and all unmatched terms. A weighted conservation law must include its exact weighting defect; equal unweighted counts do not imply weighted cancellation.

A first successful result may be an exact transition identity plus a new sign, support restriction or weaker explicit remainder bound. Quantify accumulated loss before claiming endpoint relevance. Nonlocal response-weighted analysis is a possible version only if it supplies a genuinely new property of the response, not the old Duhamel equality under a new name.

**Decisive test:** derive a measurable prediction about layer increments or constrained ancestry pairs before scanning. Compare genuine data with a declared control that preserves specified layer populations but breaks the proposed ancestry relation. Failure may expose a missing squareful or boundary term. Controls are synthetic and never proof of arithmetic independence.

### INV-CONFIGURATION: inverse structural obstruction

**Hypothesis to develop:** an excessive signed mismatch forces a precisely quantified surplus, incidence pattern, factor-depth transition defect or quotient-interval configuration that can be independently excluded or bounded.

Wheel and Referee should separate the two theorems: (i) imbalance implies a named configuration, with constants and all hypotheses; (ii) genuine arithmetic restricts that configuration independently of the endpoint bound. A configuration defined simply as 'the mismatch is too large' is circular. A capacity bound on unrelated support is insufficient. Search for a minimal actual counterexample or sharp boundary before widening a wheel.

**Decisive test:** determine an observable on which this inverse proposal and FD-TRANSPORT make different predictions. If they use the identical unpaid inequality, merge them into one lane and develop a truly different alternative. No arbitrary map between tags is allowed without preserving the physical coefficient and compensations.

### MU-LIFT: genuine finite-prefix signed amplification

**Distinct current baseline:** [MERTENS_FINITE_PREFIX_EXTENSION.lean](../research/MERTENS_FINITE_PREFIX_EXTENSION.lean) already proves exact support extension using `T(a)=2a-a*a*zetaInt` and `D(T(a))=D(a)*D(a)`. The extension agrees with genuine mu below B^2 when the input agrees below B. It does not prove norm contraction.

Analytic should investigate an independently defined **signed summatory gain or certificate class**, its exact transition under T, all boundary errors and uniform dependence on the scale. Do not define the class by the desired future Mertens bound, assume its invariance, or infer cancellation from support squaring. Compare any candidate with the existing finite-A/C consumers and perform the same bidirectional strength audit.

A bounded gain at square-growing scales would permit a logarithmic loss in a correctly formulated all-prefix recursion; that gain and the required interpolation are obligations, not established inputs. A global absolute weighted l1 defect estimate is not a default repair: the compiled prime-tail coefficient obstruction must be respected.

**Decisive test:** use the committed [finite-extension experiment](../experiments/mertens_finite_extension/) and exact guards, not only an independently sieved future sequence. Report what is computed from the prefix and what is separately checked with future data. Test the gain/class on valid prefixes and an explicit negative control. A finite checked interval is not perpetual preservation.

The completed [Mertens converse](../research/MERTENS_CONVERSE_IDENTIFICATION.lean) already gives the bidirectional coordinate identification. Do not assign re-proving it. The common exponent's numerical value remains uncontrolled by that identification alone. The finite amplitude strip map does not turn sample coordinates into actual zeta zeros.

## 4. Mandatory regression set, with carrier qualifiers

Reuse these results at unchanged dependencies; do not rerun a large scan merely to reconfirm them. Apply each to a proposed theorem only when its actual hypotheses match.

| Regression | Exact lesson and scope |
| --- | --- |
| Raw cap four: R=15, q=17; products 51,85,119,187,221 | Five distinct semiprime descendants with one historical prime refute unrestricted raw global cap-four allocation. They do NOT refute the compiled local theorem with its specific window/eligibility assumptions or prove later returned-cell admission. Referee-3 is the small exact witness. |
| Same-tag NNS sign reversal: q=11534351, owners 3 and 5 | Two negative isolated slacks become a positive once-history grouped slack, with paper lower bound 737/15360. Do not add isolated slacks or infer quadratic payment from linear packet negativity. This is genuine ancestry, not yet a masked-source admission theorem. |
| Repeated history: q=1000000007, 111 descendants in the reported half-run | One physical historical charge cannot be reused 111 times. Finite native-weight overload is not a complete-source first-bad counterexample. |
| Full depth ledger: R=500,1000,2000,3000,3162 | Direct reconstruction includes all squareful/higher-factor mass; identity and observed compensation are not a new mismatch bound. R=3162 was the original held-out endpoint, not permanently fresh validation data. |
| Raw tag monotonicity | The paper theorem is only on prime tags q>=R: G_R(q) is nonincreasing, hence at most one positive-to-nonpositive transition. It does not imply transition existence, strict margins or monotonicity on q<R. |
| Centered sitewise Li correction | Analytic-6 has `C(X)=-(1/2)*log(log X)+O(1)`. This defeats a uniformly summable scalar correction, not every nonlocal/response-weighted method. Its raw-prime finite check is not a direct numerical verification of every centered Li-increment term. |
| Finite-extension negative control | PR #951 reports the first unit 0.45 failure at n=30770121 with M(n)=-2343, despite successful smaller interval certificates. This is executable finite evidence, not a Lean numerical theorem. It rejects automatic perpetual guard preservation, not every weaker signed amplification law. |

Owner sources: [2026-10-14 report](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-10-14/10-owner-payment.md), owner-5 through owner-8, blob `4f39c1690ee4cee0a00d4ebd0d08323f06d6c75d`. The exact same-tag polarization in that report is `H(U+V,y)=H(U,y)+2*V*(3*y-U)-V^2`, with `H(W,y)=(W+y)^2-2*(W-y)^2`. This H is a local slack, **not** the residual H_R defined above.

Analytic source: [2026-10-14 report](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-10-14/20-analytic-type-ii.md), analytic-6, blob `3a6932d9c5e1474adf1f34374310c7b73eb71fc2`. Wheel source: [2026-10-15 report](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-10-15/30-finite-wheel.md), wheel-1..3, blob `6d451c35eef4021fcff78253bed609d193c249c1`.

## 5. Census acceptance: discover a restriction, not a fitted residual

A new experiment specifies in advance its two competing explanations, precise observable, rejection criterion, endpoint convention, scale range and held-out cases. Always label a root R separately from a cutoff x; `R=317` and `x=317` are different experiments.

Use directly classified native seats to report signed depth totals, squareful mass, greatest-prime tags, relevant coprimality/shared-ancestry classes, quotient-boundary events and the actual constrained cross terms needed by the candidate. Exact population conservation and independently recomputed endpoint totals are required checks. A complement computed from the already-known endpoint is a checksum, not independent evidence of compensation.

Do not call the matrix of products of aggregate layer totals a newly discovered pairwise law: it is algebraically rank one. For covariance claims identify the actual occurrence-level kernel, restrictions and normalization. Keep zero target and original coefficients; mean-centering or deleting cross terms changes the question.

Distinguish exact integer/rational comparisons, floating logs, arbitrary precision and certified error intervals. Near-zero signs need a certified inequality before supporting a proof claim. Preserve source code or an executable reproducer, input/seed hashes and actual commands. Report failed candidates and untested tails. Use finite evidence to propose a theorem; never promote the fit to one.

## 6. Next-role handoffs and stopping rules

**Coordinator:** publish a compact portfolio of the genuinely distinct live candidates, their independent missing inputs, one decisive next question per assigned specialty and explicit evidence-based decisions. Separate signed-law progress from formal coordinate infrastructure. Correct stale converse/PR status from live main; do not rewrite historical reports to pretend they knew later merges.

**Owner:** obtain one useful exact depth/ancestry relation and identify what new restriction it might imply. Restore squareful, boundary and mixed terms explicitly. Seek an independently proved partial estimate, not another local pair catalogue.

**Analytic:** compare the best nonlocal estimate with the distinct MU-LIFT gain question. Establish a quantitative bound at its honest strength or expose the exact obstruction. Do not import the desired amplification as a hypothesis under a new name.

**Wheel:** work on the independent inverse-configuration restriction or a signed transition constraint. Retire unmodified fixed-capacity covering and unsigned-wheel enlargement as complete mechanisms.

**Census:** execute the smallest test that separates the current contenders and compute residual layers directly. Expand ranges only when a stated prediction or regime change justifies it.

**Referee:** check every original carrier and source arrow; explicitly test cloning, nonadditivity, omitted depth mass, growing-cutoff uniformity, finite preservation and target-equivalence. Supply the strongest surviving corrected theorem.

**Lean:** refresh live code/PRs; repair a legitimate current PR first, or formalize a newly justified useful lemma after scope review. The raw partition/endpoint constant and tail monotonicity are possible small candidates, not mandatory work or closure claims. Do not duplicate merged Mertens maps/lift or create an assumed-invariant abstraction.

At the end of a run, answer: **What independent fact was learned? Which competing hypothesis changed status? What bound was actually improved, with what losses? What is the smallest next decisive step?** An honest unchanged frontier with a precise obstruction is better than manufactured novelty. No scheduled agent changes shared instructions, permissions, schedules or merge policy; proposals go to human review.

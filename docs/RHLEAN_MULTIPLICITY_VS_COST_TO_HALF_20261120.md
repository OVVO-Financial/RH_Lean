# MULTIPLICITY_VS_COST_TO_HALF_V1 — all-seven-agent source-faithful amplification attack (2026-11-20)

**Status:** User-directed research-task priority, proposed by this PR for **every one of the seven existing roles**. Effective for repository-directed work only after review and human merge. **This is NOT a theorem, a result that RH is proved, a grant of tool access, an agent launch, a new schedule, or a change to saved Studio prompts.** No scheduled role may merge this PR.

**Single common goal:** Discover, disprove, or rigorously delimit an **unconditional multiplicity-versus-cost advantage on the complete, actual arithmetic source** that, via a proved RH_Lean consumer, forces the zero excess to vanish and hence reaches the line Re(s)=1/2. Seek arithmetic constraints retained under Mobius/prime ancestry, determinant/rank and positivity, Euler-von-Mangoldt convolution, actual-prime theta and exact VF; do not keep deriving equivalent representations with no strict consequence. All seven roles attack **this same goal** through distinct technical tests, not seven unrelated agendas.

## Precedence, continuity and restrictions

Read, in this order on each actual invocation: live main `AGENTS.md`; this directive; `CURRENT_PROOF_CONTRACT.md`; [the Nov 16 bootstrap-to-half contract](RHLEAN_BOOTSTRAP_TO_HALF_20261116.md); [universal-envelope proof evidence](UNIVERSAL_ENVELOPE_FORMALIZATION_20261115.md); the live [proof DAG](PROOF_DEPENDENCY_DAG.md), [coordinate atlas](COORDINATE_ATLAS.md), source declarations; and the newest **actually verified** own/upstream reports with no calendar cutoff. Source hashes, theorem types and actual merge/CI status override a dated note.

This directive supersedes **conflicting research-selection priorities only** (generic HIGH, old finite-wheel monopoly, frozen root/prime two, isolated slot improvements, dated `NEXT-*` tasks). Preserve the proved cancellation chain, all nine route toolkits (VF-LOW, SAT, CODIV, OAI-NNS, JOH, FINITE-AC, CORR4, MU-LIFT, NYMAN), the prior source-faithfulness conditions, counterexamples, exact finite results, incomplete-return requirements and half-continuation constraint. Distinct routes need not identify rational Mobius with ideal characters or model theta lifts with ancestry unless an explicit bridge is proved.

**Do not spend a run merely reducing 7/8 by another finite amount**, rediscovering already-paid cancellation, or renaming a source, unless it is a necessary, demonstrated step in an unconditional continuation to 1/2. A negative result that rules out a specified multiplier is useful; submit a precise falsifier rather than a substitute target.

## Exact existing consumer — distinguish supplier from equivalence

The original strict history, not an enlarged self-inclusive maximum, is

```text
X_R = R^2 - 1
K_R = max_{0 <= y < R} (M(y)-1)^2/(y+1)    (K_R >= 1)
A(X) = max_{R >= 2, X_R <= X} (M(X_R)-1)^2/(R^2 K_R)
Theta = sup {Re(rho) : rho is a nontrivial zero of zeta}
h = max(Theta, 1/2) - 1/2
```

The verified universal-envelope infrastructure (merged #1135; verify the exact current declaration and import closure) gives `q(X)=log(1+A(X))/log X -> h` and, for `0 <= lambda < 2`, `eta >= 0`, the exact dictionary

```text
EnvelopeBound lambda eta <-> Theta <= 1/2 + eta/(2-lambda)
EnvelopeBound lambda eta :=
  forall epsilon > 0, exists C_epsilon >= 0, forall R >= 2,
    |M(R^2 - 1)-1| <= C_epsilon * R^(1+eta+epsilon) * K_R^(lambda/2)
```

**Primary new arithmetic supplier to attempt** (not currently proved):

```text
exists delta, 0 < delta <= 2 AND EnvelopeBound (2 - delta) 0.
Equivalently:
forall epsilon > 0, exists C_epsilon >= 0, forall R >= 2,
  |M(R^2 - 1)-1| <= C_epsilon * R^(1+epsilon) * K_R^(1-delta/2).
```

This, with a **fixed** delta independent of R, epsilon, zero, or cutoff, forces `Theta <= 1/2` through the already-proved dictionary; it is **RH-strength and currently OPEN**. For a source-faithful improvement mechanism, an alternative acceptable target is a proved fixed-point contradiction at every possible exponent `b>1/2` or a renewable `P(b) -> P(Phi(b))` with `Phi(b)<b`, all costs and hypotheses valid at the next step. Require a true terminal implication and no hidden RH input. `EnvelopeBound 2 0` is already true and **does not** yield RH: `lambda=2` is the degenerate boundary. Do not mistake a pointwise `epsilon` or `delta(R)` for fixed uniform saving. This target does NOT require uniform finite `A`, which is separately stronger.

The established amplified-exponent meter is also available: a uniform squared bound `(M(R^2-1)-1)^2 <= C_epsilon R^(p+epsilon) K_R` corresponds to `Theta <= (p-1)/2`, with the critical RH value `p=2`. The native `Q_R=2M(R-1)-M(R^2-1)` identity and the canonical VF-to-von-Koch source provide other exact consumers. Preserve all terms and the source's ordinary integer coefficients.

## The concrete outside stimulus (hypothesis generator, NOT imported proof)

The [2026-11-20 RH/GRH announcement](https://alpo.ge/remark.pdf) and [14-part Lean source archive](https://alpo.ge/lean.tar.gz.part01) suggest exploring **Stepanov-style multiplicity, iterated theta lifts, determinant/nonvanishing, arithmetic divisibility, trace-formula positivity and cost balancing**. The public [archive mirror](https://github.com/CocoSgt/riemann-hypothesis-lean) and [independent verification effort](https://github.com/Deicyde/riemann-hypothesis) allow source inspection. **Neither announcement nor static no-`sorry` scan is a mathematically accepted RH/GRH proof; do not import its conclusions, accept its unverified lemmas as axioms, or label RH solved.** Independent kernel checking and independent mathematical validation of its deep mathematical steps must be recorded separately.

The *exact classical arithmetic crosswalk*, initially on `Re(s)>1`, is

```text
(1/zeta)(s) = Sum_n mu(n)/n^s
-(zeta'/zeta)(s) = Sum_n Lambda(n)/n^s
Lambda = mu DirichletConvolution log
```

A consequence for the actual `mu` or `Lambda` source requires a typed and quantified bridge. In particular, "R generations of prime ancestry" is NOT the same as "multiplicity R of a zero", Gram nonnegativity is NOT strict coercivity, and automorphic trace positivity is NOT automatically positivity of a signed Mobius Gram. Explicitly retain the full mixed terms, negative credit, complete LOW/HIGH, principal and far/error corrections, prime powers, floor/virtual Euler compensation and normalization.

## Required attack protocol (each role)

1. **Baseline & live evidence.** Pin main/source/policy SHAs and the strongest **unconditional** current output, including every positive loss and slot/cutoff uniformity; verify accepted theorem dependencies. Use #1119, #1135 and later merged changes only at their exact actual scope.
2. **Source-faithful construction.** On a *named* complete source define the candidate incidence/lift matrix, determinant, rank, divisor multiplicity, Gram, or energy. Record rows, columns, signs, weights, cofactor masks, truncations and inherited ancestor/prime-power effects. Supply a literal finite identity or prove why no such identity exists.
3. **Multiplicity vs. cost ledger.** For scale `R` (or `X`), establish a **lower bound** for genuinely independent constraints/multiplicity and an **upper bound** for every introduced geometric, analytic and arithmetic cost. Identify exactly where existing norm/triangle/Cauchy-Schwarz estimates lose sign or correlation, and whether an already-proved RH_Lean interaction recovers it. No generic rank or determinant argument may silently assume nonzero minors.
4. **Uniform quantitative bridge.** Convert the retained information to a candidate strict historical-power bound, closed exponent improvement, or directly to the **real original prime/VF** consumer. Distinguish a conditional lemma from its supplier. Write the exact `epsilon`, `delta`, `R`, cutoff, prime and zero quantifier order, and full complementary return.
5. **Adversarial and computational tests.** Construct the cheapest falsifier: zero Gram eigenvalue; aligned signs; rank collapse; a disappearing determinant; ill-conditioned lifts; a counterexample to an assumed monotone multiplicity; a mask mismatch; an off-critical toy mode; and boundary cases including R=549 (refuted block capture), R=317 and R=1027 where appropriate. Finite observations and numerical positivity are not infinite proofs.
6. **Close or park.** Claim progress **only** for a new, transitive-axiom-audited theorem on the actual source or a concrete obstruction to a proposed argument. Attach its direct path to `EnvelopeBound (2-delta) 0`, an equivalent fixed-point contradiction, or the prime-error consumer; if no bridge, label OPEN and state the exact first unpaid lemma. Do not rename a conditional implication an unconditional supplier.

## Seven distinct assignments, one shared terminal target

| Role | First technical deliverable |
| --- | --- |
| **Coordinator / Proof Architect** | Construct a seven-branch multiplicity/cost dependency matrix, mapping *every* proposal to the exact original source, the first unpaid supplier and the already-proved `EnvelopeBound`/zero-boundary consumer. Maintain independent branches and consolidate duplicate input inequalities; prohibit paper-to-theorem status promotion. |
| **Owner Payment / Signed Arithmetic** | Derive a complete integer Mobius ancestry incidence operator at square endpoints with signed weights, first-owner masks, chronological shifts and both mixed orientations. Seek a constrained rank/determinant or full Gram contraction whose gain survives all transport and HIGH returns. No splitting cost into independently bounded pieces. |
| **Analytic Type II** | Examine whether the von Mangoldt/`mu*log` bridge and actual Euler source support a multiplicity/divisibility or analytic determinant estimate with a provable `delta>0` after all LOW/HIGH/principal/tail costs. Compare the alleged theta-lift/trace mechanism to *actual* coefficients; do not assume automorphic transfers or unverified published claims. |
| **Finite Wheel & Incidence** | Construct explicit finite-wheel / cofactor / CORR4 / MU-LIFT matrices; calculate exact row independence, singular values/minors, arithmetic divisor constraints and strict-history `K_R` feedback. Propose and falsify the smallest scale-independent coercivity inequality on the entire complete source, including every product, power and historical term. |
| **Prime Census Laboratory** | Implement preregistered small/full-dimension exact-integer tests for the *same* candidate determinants, rank or sign-cost laws on real Mobius/von Mangoldt and square blocks; compare to adversarial sign surrogates but never substitute them. Search first failing R, prime-square boundary, theta/floor mismatch, and loss of uniformity with increasing R. Publish code, ranges and seeds. |
| **Adversarial Referee** | Independently reconstruct both `EnvelopeBound` dictionary and each claimed multiplier-to-cost estimate. Hunt hidden RH/GRH assumptions, invalid theta-lift analogies, determinant vanishing, positive-definiteness gaps, incorrect convolution, epsilon leaks, false monotonicity and omitted mixed returns. Treat the external 14-part claim as UNVERIFIED until independent checking actually concludes. |
| **Lean Verification** | Pin exact types/imports of the merged #1135 `EnvelopeBound` dictionary, `Q_R` and zero-limit consumers, then formalize the smallest independently checked finite source/incidence/convolution or rank lemma. Provide explicit conditional supplier/consumer signatures with all parameters, never a disguised hypothesis in an "unconditional" theorem. Preserve full repo read/write on non-main PR branches, pinned GitHub Actions build and axiom audits. |

No role is assigned to discover *another generic cancellation mechanism*. The required discovery, if any, is a **source-faithful structural constraint that makes already available cancellation quantitatively stronger**.

## Reporting contract and acceptance

After first *actual* consumption, each role records `amplification_cost_ack=MULTIPLICITY_VS_COST_TO_HALF_V1` in its own authorized report (Coordinator mirrors as required). Every report contains:

```text
MAIN_SHA / POLICY_SHA / ORIGINAL_SOURCE_SHA / REPORT_WATERMARK
CURRENT_UNCONDITIONAL_THEOREM + EXACT TYPE / AXIOM & CI STATUS
ROLE / PROPOSAL_ID / ORIGINAL_SIGNED_SOURCE / COEFFICIENT BRIDGE
MULTIPLICITY_LOWER / ALL_COSTS_UPPER / MISSING_INDEPENDENCE
CANDIDATE STRICT_DELTA / QUANTIFIERS / CONSUMER / HALF_CONTINUATION
FIRST_UNPAID_LEMMA / FINITE_FALSIFIER / COUNTEREXAMPLE
NEXT_SMALLEST_RIGOROUS_STEP
MATH_STATUS=PROVED | CONDITIONAL | OPEN | REFUTED
PUBLICATION_STATUS=CANONICAL_VERIFIED | RECOVERY_VERIFIED | NOT_PUBLISHED
```

Reports must follow [latest-actual continuity](RHLEAN_REPORT_CONTINUITY_LAST_ACTUAL_20261111.md) and [lossless publication/recovery](RHLEAN_AGENT_REPORT_PUBLISH_RECOVERY_20261118.md), including append preservation, GitHub API transport fallback and immutable recovery siblings. Six non-Lean roles remain **own-report-only**; only Lean Verification may make task-relevant reviewable code PRs within its existing GitHub authorization. No agent may push main, merge, auto-merge, launch another agent, or alter schedules/grants. Human-only merge and multiple-daily cadence remain as configured externally. This PR changes **repository instruction text only**. An actual post-merge run acknowledgement is the evidence that an agent has taken it up.

**Completion criterion:** A transitive-axiom-audited, externally reviewable theorem on the true integer source that *unconditionally* establishes a fixed strict `delta` in `EnvelopeBound (2-delta) 0`, or another explicitly verified RH-strength terminal supplier. Until then the goal is OPEN and the outside 14-part proof remains unverified.

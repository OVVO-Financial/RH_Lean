# ALPOGE_FULL_ANALYTIC_GEOMETRIC_COST_V1 — seven-agent full-source cost campaign (2026-11-20)

**User instruction / highest research-selection priority, once human-reviewed and merged.** All SEVEN existing RH_Lean roles must pursue the SINGLE specific task: **prove that the native signed-Selberg 2I-J lattice's multiplication/divisibility/coercivity advantage reduces Alpöge's COMPLETE analytic/geometric error, with every complementary term and quantified cost paid**, OR prove a source-faithful obstruction and repair the candidate. Neither a determinant nor a new conditional equivalent of RH counts as completion.

**Activation boundary:** On the next REAL configured agent invocation after human merge, consume this directive and report the acknowledgement below. The PR does not launch/reconfigure Agent Studio, change schedules/model/permissions, write outside assigned role paths, or certify RH. Respect multiple daily runs, exact-head CI and HUMAN-ONLY merges. External saved prompts require separate human synchronization unless they reload live main. The source PR #1160 is OPEN at creation of this policy: always check its LIVE head, CI and merge state; do not label its novel Lean declarations verified until exact-head CI succeeds.

## 0. Required reading order (every actual run)

1. Live main AGENTS.md and this directive (record policy blob and main commit).
2. Actual live [PR #1160](https://github.com/OVVO-Financial/RH_Lean/pull/1160): research/ALPOGE_SIGNED_SELBERG_INTEGRAL_SCHUR_20261120.md, research/ALPOGE_SIGNED_SELBERG_INTEGRAL_SCHUR_20261120.lean, scripts/alpoge_selberg_schur_lattice_regression.py and scripts/alpoge_selberg_complete_return_audit.py, using PR head while unmerged.
3. Actual merged #1157 arithmetic source and currently OPEN #1159 cost-replication research (verify status), plus the one-sided semivariance note and #1158 (verify status). Prefer current live file SHAs/theorem signatures over any dated notes.
4. RHLean/Analysis/NativePNTSignedSecondSelberg.lean, RHLean/Analysis/NativePNTSignedSecondSelbergWheelFrontier.lean and RHLean/Analysis/NativePNTSignedSecondSelbergFrontierCharge.lean.
5. [Alpöge's original formal cost ledger](https://github.com/CocoSgt/riemann-hypothesis-lean): src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean, src/Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean, src/Formalism/SizeWindowBrackets/SChain.lean, and src/Formalism/MeanHeightDescent/CovolumeEstimateAnchoredWeights.lean. Check actual declarations and assumptions; announcements and mirror summaries do not license axioms.
6. Live CURRENT_PROOF_CONTRACT.md, #1135 exact exponent dictionary, docs/PROOF_DEPENDENCY_DAG.md, and latest REAL published role/upstream reports with NO date cap (docs/RHLEAN_REPORT_CONTINUITY_LAST_ACTUAL_20261111.md). Apply docs/RHLEAN_AGENT_REPORT_PUBLISH_RECOVERY_20261118.md on reporting.

Previous MULTIPLICITY_VS_COST_TO_HALF_V1 and BOOTSTRAP_TO_HALF_V1 remain mathematical safeguards, but this full analytic/geometric cost supplier supersedes conflicting task-selection queues. Preserve all nine original source-based route toolkits as instruments; every selected route must pay THIS named seam rather than become unrelated exploration.

## 1. Exact native object and what is actually proved

For R>=4, X_R=R^2-1, E(x)=psi(x)-x and K2(n)=(Lambda*Lambda)(n)-Lambda(n) log n, the already-proved signed recurrence is

    E(X_R) * log(X_R)^2
      = S(X_R)*log(X_R) - (Lambda*S)(X_R)
        + sum_{1<=n<=X_R} K2(n)*E(floor(X_R/n))
        - floorDefect(X_R).

S is the EXACT signed first-Selberg remainder from the native module. Do not substitute an asymptotic or independently bound the parts without retaining the signed interaction.

Let P_R={prime p : 3*R<=4*p and p<R}, m=|P_R|, w_p=log p.
Each genuine p*q (including p=q) in this band satisfies floor(X_R/(p*q))=1; native E(1)=-1. Thus the actual selected signed square PLUS DISTINCT semiprime contribution is

    F_R = sum_{p in P_R} w_p^2 - 2 sum_{p<q in P_R} w_p*w_q
        = 2 sum_p w_p^2 - (sum_p w_p)^2
        = w^T (2 I_m - J_m) w.

The normalized INTEGRAL COEFFICIENT matrix A_m=2I_m-J_m acts as 2I on the centered sum-zero space, has mean eigenvalue 2-m and det=(2-m)2^(m-1). For three primes det=-4 and normalized singular values are 1,2,2. Prime number theorem implies m ~ R/(4 log R), near X_R^(1/2-o(1)). On the narrow prime band F_R ~ -R^2/16. These are important finite/source consequences, **not yet an analytic/automorphic cost theorem**.

**Three non-negotiable limitations**:
- The ACTUAL source entries contain real log(p)log(q) weights, so an integer coefficient determinant does NOT directly give the nonunit p-adic lattice index, Hecke divisibility or covolume hypothesis in Alpöge's theorem. A valid valuation/integral structure must be exhibited, or an alternative signed-correlation inequality with fully priced replacement must be proved.
- Taking disjoint 3x3 PRINCIPAL SUBMATRICES and multiplying their determinants as though the original operator were block-diagonal silently drops all cross-triple terms. A true block-diagonalization must explicitly account for them and the rank-one mean return. The FULL A_m has growing mean norm |m-2|; only centered directions have norm exactly 2.
- The selected band is evaluated at reciprocal quotient 1. Its m directions do not give independent E(x) observations, and rank/index alone may not be inserted as a free 1/m in any analytic or geometric error budget.

## 2. Precise missing supplier: quantify the full signed complementary return

Define B_R=-F_R (for R with m>=3 this is positive). Define C_R **by enumerating the actual complementary source**:

    C_R = S(X_R)*log(X_R)
          - (Lambda*S)(X_R)
          + [sum_{1<=n<=X_R} K2(n)*E(floor(X_R/n)) - F_R]
          - floorDefect(X_R).

Thus EXACTLY E(X_R)*log(X_R)^2=C_R-B_R. Square diagonal, distinct ordered pairs counted ONCE, prime powers, products outside P_R, lower/higher reciprocal quotients, principal and centered pieces, owner/FV channels and floor defect must all be returned. Merely defining C_R in terms of E without deriving this literal source partition is NOT a supplier.

The sign-compatible NNS/Alpöge terminal inequality is (still OPEN)

    FOR EVERY epsilon>0, EXISTS C_epsilon >= 0
    FOR EVERY integer H>=2:
       sum_{H<=R<2H} (max(C_R-B_R,0))^2 / log(X_R)^4
             <= C_epsilon H^(3+epsilon).

This is exactly the degree-two UPPER partial moment of the COMPLETE Chebyshev error at square endpoints; through the (not yet cross-repo-certified) one-sided smoothing/Landau bridge it implies RH. The B_R negative credit is favorable for this *upper* E error, not for negative-E semivariance. A sign-reversed attack is allowed only after redoing ALL sign and endpoint interpolation algebra. Do not infer this uniform bound from finite numerical ratios.

The full K2*E example at R=1027 from the independent finite census: selected band F_R about -56,617, total K2*E about +1,356,127, other K2 sources about +1,412,744. This directly prevents treating B_R as a dominant estimate unless a separately PROVED interaction constrains the entire complement.

The alternative directly native historical-consumer target remains a fixed delta>0 in EnvelopeBound (2-delta) 0, or another genuinely paid terminal bootstrap to 1/2, with a COMPLETE typed bridge and exact strict-history K_R. Do not use a conditional equivalence as a theorem supplying its hypothesis.

## 3. Alpöge's analytic/geometric cost acceptance (no analogy allowed)

The actual SIZE-WINDOW shape, with r=sqrt(x), u=x^epsilon, delta=nT2/n, T=nT, is

    Err0 = T*aE*(1+m^2/k)
           + m*(2*n*m*b*u + delta*k*b*u^2/n),

    Err0/(T*m*b*delta)
       = aE/(m*b*delta)*(1+m^2/k)
         + 2*n*m*u/(T*delta)
         + k*u^2/(n*T).

With ALL Alpöge SizeWindows parameter inequalities and a genuine family, the abstract algebra pays <=10*r*u^4, before the extra x^(C*epsilon) and movement/thin/width costs. This computation is NOT the hard existence proof.

**The one missing bridge all roles must attack:** for a source-preserving family of admissible *native* arithmetic lifts, PROVE lower multiplicity AND upper complete paid errors in the SAME family so that the final bound on -Gz or the actual UPM2 has root scale. Specifically account for T, n, nT2, m, k, b, delta, aE, Err, f, theta, eta, covolume/height, divisibility/congruences, floor/prime-power returns and all signed complements. An honest alternative signed-covariance route must identify what takes the place of every external geometric parameter and prove its quantitative cost.

Test a genuine lower bound m>=x^(1/2-epsilon), not simply a count of prime labels; prove admitted noncollapsing response modes, not merely source matrix rank. Supply a fixed epsilon-uniform estimate or a precise counterexample. No free division by m. Propose a gain only if the complete source-to-consumer inequality changes.

## 4. SEVEN role-specific attacks (one shared theorem)

| Role | Immediate mathematical assignment / falsifier |
| --- | --- |
| Coordinator / Proof Architect | Build one JOINT source-and-cost ledger with separate exact theorem, hypotheses, quantitative supplier, and terminal consumer columns. Assign names to every C_R sector and map them to the external T,n,nT2,m,k,b,delta,aE,Err,f,theta,eta and covolume gates. Maintain the synchronized first-unpaid-lemma map and test two valid consumers (positive square UPM2 and historical EnvelopeBound). Report a true new net power only if all returns are paid. |
| Owner Payment / Signed Arithmetic | Establish the FULL exact C_R Fubini partition from the native signed second-Selberg recurrence, with actual first-owner masks, square faces, all p*q outside the selected band, prime powers, low/high, floor/virtual Euler compensation. Look for a one-sided complete-source inequality on (C_R-B_R)_+; preserve every mixed cancellation. No separate abs bounds disguised as progress. |
| Adversarial Referee | Independently try to KILL any claim that det A_3=-4 or 2I centered action yields Alpöge's covolume saving. Probe real log-weight integrality, cross-triple principal-mode interactions, quotient=1 data collapse, size-window parameter witnesses, signs, epsilon-uniformity and double counting. Give explicit counterexamples or a verified non-circular route, not a blanket objection. |
| Prime Census Laboratory | Run BOTH scripts in PR #1160 and independent prime-power Lambda/K2*E full recurrence at R=100,317,549,1027 and feasible larger scales. Numerically reconstruct S*log, Lambda*S, floorDefect and hence C_R, not just K2. Report signed cancellation/UPM2/Gram eigenvalues, counterexample probes and correct finite/infinite status. Use deterministic exact integer masks; record precision for logarithmic comparisons. |
| Analytic Type II / NNS | Derive and test a true complete-source upper partial-moment inequality for positive error overshoot, using the Schur mean/centered channel together with existing signed Selberg identities and NNS LPM/UPM. Alternatively reconstruct Alpöge's anchored-weight/covolume bound with a typed actual-source arithmetic analogue. Quantify every error/movement/width term and state the first unproved quantitative estimate; do not assume theta-lift identity or spectral positivity. |
| Finite Wheel & Incidence | Find whether the 2-adic integer coefficient doubling survives **all** cross-triple interactions and the actual logarithm-weighted source; test exact block diagonalization, Smith normal form, full A_m determinant, zero-sum lattice and the bad mean direction. If it does not supply an actual integral Hecke-type index, propose and falsify an honest substitute involving wheel congruences, cofactor ancestry, or CORR4 source covariance. |
| Lean Verification | Read main+live #1160/#1159 and recompile their relevant real source lemmas on an authorized reviewable non-main branch. Formalize the FULL F_R source partition, centered and principal algebra, exact C_R, sign-correct UPM2 definitions and smallest independently accepted bound or adversarial counterexample. Audit transitive axioms/theorem parameters; any unproved cost premise stays an explicit parameter/OPEN proposition and cannot be hidden in a proof. |

Every agent should use different instruments but target THIS single amplification/cost payment. The coordinator may reconcile duplicate proposals; no role should simply repeat the already-proved determinant, the F_R asymptotic, or another equivalent RH criterion without new control over C_R.

## 5. Required output, progress meter, ownership

On each actual invocation append only to the OWN allowed report path (Coordinator mirrors as already authorized; Lean Verification only has additional reviewable non-main PR writing authority). Read the newest VERIFIED published report per role across any historical gap before choosing the next attack. First actual uptake must contain

    alpoge_full_cost_ack=ALPOGE_FULL_ANALYTIC_GEOMETRIC_COST_V1
    MAIN_SHA / POLICY_SHA / LIVE_1160_HEAD / SOURCE_DECLARATION_SHA
    PREVIOUS_REAL_REPORT_WATERMARK / NEW_SECTIONS_CONSUMED
    ROLE / EXACT_SOURCE / F_R / C_R / SIGNS_AND_COUNTS
    m_LOWER_AND_INDEPENDENCE / FULL_A_m_MEAN_CENTERED_AND_INTEGRALITY
    T,n,nT2,m,k,b,delta,aE,Err,f,theta,eta,HEIGHT_AND_COVOLUME_COSTS
    COMPLETE_SIGNED_ERROR_UPPER / EPSILON_UNIFORMITY
    FIRST_UNPAID_LEMMA / SMALLEST_FINITE_FALSIFIER / QUANTITATIVE_CONSUMER
    MATH_STATUS=PROVED|CONDITIONAL|OPEN|REFUTED
    CI_STATUS=GREEN_EXACT_HEAD|FAILED|PENDING|NOT_RUN
    PUBLICATION_STATUS=CANONICAL_VERIFIED|RECOVERY_VERIFIED|NOT_PUBLISHED

Do not report a mere new basis, no-sorry file, numerical test or operator determinant as the missing RH-strength proof. A mathematical progress claim MUST say whether the full normalized analytic/geometric error is reduced, by how much, with what independent arithmetical input and how the one-sided square-block/zero consumer follows.

**Proof acceptance:** either a new unconditional quantified full-source result with a genuine saving that pays EVERY analytic/geometric cost and a verified 1/2 continuation, OR a checked no-go delimiting an explicit attempted inequality and a strictly sharper surviving replacement. Partial exact identities are welcome as identified supporting lemmas but are not terminal success.

Follow the lossless report-publish recovery contract, six own-report-only roles, Lean Verification's existing GitHub PR rights, multiple-daily cadence, preserved agent configurations, no automatic merges, and human-only review. A new PR is a request for adoption, not evidence that any agent ran.

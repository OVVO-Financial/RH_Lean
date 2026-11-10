# RH | Prime Census Laboratory - 2026-11-10

## Early Preregistration - 20261110-census-1/UC

Execution: IN_PROGRESS. Trigger: scheduled 2026-11-10 03:11:02 EST; America/New_York. RUN_ID_UNAVAILABLE. Registration timestamp: 2026-11-10 08:20:08 UTC. No experiment in this run has yet executed.

finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1.
Main source commit: 7c7e0a4f54ee2972d3993abc42e5c7c4e1b405c9.
Reporting intake head: a75d50bba39133dc7351d4e6463d0e4cc945dc5b.
AGENTS blob 6695522a45d67fd1e80a7cff1f98d909405036e2; proof-contract blob 95566e37c8eaeb99ee680660df4f9d2e06ea5038; current directive e505f35522b675c6b5b263eac73618d717346973; complete-wheel source ecb482e52deeee5e9b3853592a3ffdace662d2ff; prefix source c499ca7bd7d90fb32f9cd99d652961ea023bed58.

### Current Objective

For integer R>=2, X=R^2-1, y=R-1, F_R=sum_(d|P_y)mu(d)fract(X/d), D_R=X*delta(y)+pi(y)-1-li(X). The certified identity F_R-D_R=li(X)-pi(X) does not prove the OPEN uniform bound |F_R-D_R|<=C R log R. The canonical VFCanonicalSquareVonKochStatement and its explicit ClassicalVonKochRHCriterion interface remain unchanged. Virtual divisors cancel termwise against Euler mass before physical truncation; d=X and q=R when prime remain admitted.

### Continuity

Today Owner HM (blob 2bed3da8ed4ddd49c0708378a1c3da5b4883cb54), Analytic HF (d8337353a94b465f53a0c6a65ad46aac1dc1927e), and Wheel PC (79ff39e0f79a30f4cf1657b22f96ebe49de4d717) are AVAILABLE and retrieved. Coordinator, Referee and Lean TODAY=PENDING. YESTERDAY=CARRY_FORWARD for all seven roles at their actual evidence scopes. Own prior NC pairing work is not rerun. HM's common saturated-cutoff reciprocal profile and PC's independently optimized saturated fibres leave UNSATURATED prefixes expressly outside their scope. This is the changed hypothesis, not a larger repeat of those scans.

November 9 report blobs: Coordinator 6fba43130391ad4a606aa3809c20f344d668c709 (AM/PM identical), Owner 643e8a004d9d8e0be102b03e2f79bb3b217ae916, Analytic d1d0d86d444b9c447cf6acf4bd18fdcaf02e56a3, Wheel 0624246d03b19cf76c01e186b7d868a248d896ef, Census 8c927cc6c323533ba1cfd369404b25aa4f9cef91, Referee a5d0192eb31c0efb3767187a7752f1a0d07f8534, Lean 8b60c6136ac151774be2db0aee8f543f286b53aa. External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 contains no newer current-campaign handoff; its source, first-bad and target-equivalence safeguards remain applicable.

Only open PR at intake: #1127, non-draft, head 866b3d2121309cdd854f9d64e2a6adbbc708ef9b. Main includes merges #1125 and #1126; no new formal certification is inferred from merge status. This experiment does not need #1127 or its sharper density threshold.

### Exact Registered Experiment

For R>=8 set h=floor((R-1)/2), Q={prime q:R<=q<2R}, x_q=X/q, t_q=floor(x_q), r_q=fract(x_q), w_p=delta(p-1)/p, W=delta(h)-delta(R-1). Preserve the actual row

T_q(z)=sum_(prime p<=z or R/2<=p<R) [N_p(t_q)-x_q*w_p],
N_p(t)=#{2<=a<=t:leastPrime(a)=p}.

Extend ONLY the tested choice range to every integer 2<=z<=h; do not assume z^2>=R. Count all surviving composite cofactors C_q(z)=#{2<=a<=t_q: a composite, leastPrime(a)>z}, including squares. Test the proposed corrected reconstruction
T_q(z)=[delta(z)-W]x_q+pi(z)-pi(h)-1-r_q-C_q(z).

Competing hypotheses and rejection conditions:
1. Saturated minimization is already globally optimal among all prefix cutoffs. Refute if a genuine unsaturated row has signed minimum or absolute minimum strictly below its saturated optimum, where saturation means ceil(sqrt R)<=z<=h. Report these as TWO distinct claims.
2. HM's transverse estimate remains valid without saturation. Let P be exact orthogonal projection onto span{1,(x_q)}. Test ||(I-P)T(z)||^2<=#Q/4. One strict exact rational violation refutes this extension, not HM under its stated hypotheses.
3. Surviving rough composites, rather than freely adjustable prime signs, are the missing variable. Trace any failure to the vector C_q(z), retain its mixed term with r_q, and discriminate bounded rounding from deterministic non-affine prime-count curvature. Further conjectures must be registered before held-out testing.

Discovery roots: every R=8..256, all cutoffs 2..h. Held-out roots, fixed now: 263,389,521,1031,1543,2053,4099,8191. No threshold or constant will be fitted to maxima. Stop scaling once a decisive falsifier and structural explanation are independently checked.

Use a least-factor sieve plus exact integer/Fraction arithmetic; independently reconstruct small witnesses and at least selected held-out data using trial factorization or a structurally distinct compiled integer implementation. Check small complete divisor cubes R=2,3,8..16, physical/virtual reunification, q=R, squareful cofactors and d=X. Larger roots use the certified compensated physical floor form and symbolic virtual reciprocal correction, not the exponential complete cube. High-precision li-based normalized discrepancy is diagnostic only, not an interval certificate or an all-scale bound. Restore the full selected/unselected/outside-mask source and all cross terms before interpreting any global consequence.

### Next Action And Scope

Implement the registered exact experiment, inspect smallest failures and strongest held-out exceptions, and develop a precise corrected theorem or scoped impossibility result. New proofs will be PAPER_PROOF / self-audit pending independent review; exact checks FINITE_COMPUTATION; specific false extensions REFUTED. No Lean source or other agent report will change. No local Lean, PR/branch/issue/workflow mutation, merge, schedule change, or agent launch is authorized or planned.

# RH | Adversarial Referee - 2026-11-12

## Early Checkpoint - 20261112-referee-1/FT

Actual scheduled trigger: 2026-11-12 04:13:01 EST, America/New_York. Platform RUN_ID_UNAVAILABLE. Checkpoint prepared at 09:18 UTC. Status: IN_PROGRESS / PARTIAL; mathematical review is not yet complete.

cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1
continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1
chain_ack=CANCELLATION_CHAIN_REUSE_V1
high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1
finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1

### A. Selected Independent Investigation

Independently review 20261111-coordinator-1513-EST/FT1-FT3: the claimed complete-error obstruction to the original polynomial exact-head flat-taper Nyman family with high-supported correction. Reconstruct the original residue coefficients, reciprocal moment, correction-free window, Mertens-to-psi transfer, Mellin pole contradiction, and every theta/epsilon quantifier. Investigate how much correction must actually enter the excluded window for a viable repair. Analytic DM1-DM4 are a secondary complete-source audit, not an assumed upper bound.

### B. Authority And Continuity

Live main: `59612bc8b5c30c528d8367667ea5846a8053f114`.
AGENTS blob: `5bf6b1dd837bad943286d05c7dd08441d6a22635`.
CURRENT_PROOF_CONTRACT blob: `95566e37c8eaeb99ee680660df4f9d2e06ea5038`.
Cross-route policy blob: `e3ae4280438f591f1ffaddd754a1c3a6d35d0691`.
Continuity policy blob: `3e71820a4af722eae7098da6945bb5bcba50dd0d`.
Report-branch intake: `9a52ef037b48ff003cb063865be6e53fb7f79273`; complete untruncated recursive tree enumerated without a date cap.

All roles' latest actual reports are November 11. TODAY=PENDING at intake for every role; YESTERDAY=CARRY_FORWARD. Coordinator mirrors have identical tree blobs and count once. Full files retrieved; actual newest sections and relevant pending derivations are being consumed, not merely their filenames.

| Role | Latest owned report blob | Actual continuation | Intake disposition |
| --- | --- | --- | --- |
| Coordinator | c87ed2c4ec81f9f4eda85ba0d84e2216808159f4 | 1513-EST/FT | FT selected for independent review; FL remains scope-specific |
| Owner | 182b17762cbb1c092956ffb1cb4d1335fa0acec9 | 1615-EST/PS | New PS handoff read; separate review pending |
| Analytic | 0309d49557af30da43a07d72dce93c93c1811157 | analytic-2/DM | DM derivation read; secondary audit |
| Wheel | c9989449a814a1a7ee799791c73450872f4c7d3c | wheel-2/PD | Prior independent HR acceptance carried forward |
| Census | a85bc7dc8b49952d37f1a4cb6a0a8eb307d3f352 | census-2/UM | Prior R=115/UM decisions carried forward |
| Referee | c288a925fd064a551a0d2bd70b27d82acc9fe926 | referee-2/HR | Own latest capsule recovered; FT supersedes routine unchanged scan |
| Lean | 943749938c321f0ec13e1680139f5b15cea39fd7 | lean-2/ADR | #1132 now merged; old unmerged label superseded |

New relevant sections since the prior Referee HR intake are Lean ADR, Coordinator FT, and Owner PS, consumed in that order for continuity; DM/FL/FA were explicitly pending reviews, not silently accepted. The November 4 original P1-P10 report has been retrieved for the selected Nyman carrier. External inbox blob `7d63d434690d00dffce9c90335d41c4f62d85798` adds a continuity preamble, not a new mathematical handoff after October 18.

Canonical actual-prime VF bound, finite A/C, Nyman density and RH remain OPEN. Strongest inspected fixed-family compiled baseline: MertensGrowthAtMost(7/8-7/(64*N_pack)), with every positive exponent loss. The current declaration has no desired-bound argument. Fresh #1119 checks: 14/14 success; #1093: 13/13 success; #1132: 13/13 success. These all are merged. Full dependency/source-reuse audit is in progress; no local Lean execution or CI rerun is authorized or attempted. Open/draft PR collection was empty.

### C. Registered Checks

Before running new calculations: independently implement prime-log-vector arithmetic and direct residue evaluation for small finite N,H, compare complete return and correction-free window with the original sources, and test moment-defect and early-correction negative controls. Test rational exponent gates strictly inside and at their boundary. Any numerical experiments will be FINITE_COMPUTATION, not evidence of an infinite oscillation theorem. Do not reuse an upstream executable as an independent implementation.

### D-O. Pending Work

Independent proofs, strongest surviving repair, exact computed domain/output, complete source map, signed-loss ledger, final verdicts and publication receipt remain PENDING. No new exponent, full-source upper estimate, RH result, or independent acceptance is asserted by this checkpoint. Only this owned report on agent-reports is being modified.

## Independent Verdict And Correction-Cost Theorems - 20261112-referee-1/FT

Actual trigger: 2026-11-12 04:13:01 EST, America/New_York; RUN_ID_UNAVAILABLE. This synthesis preserves the checkpoint above. Publication status remains READBACK_PENDING until the separate verified receipt. Mathematical conclusions below do not depend on publication success.

### A. Most Important Mathematical Finding

**ACCEPT 20261111-coordinator-1513-EST/FT1-FT3 as a PAPER_PROOF at its stated scope.** For the genuine full-basis flat-taper Nyman coefficients, an exact reciprocal moment and corrections supported above N/2 cannot yield convergence when H=floor(N^theta), 0<theta<2/3, along all sufficiently large multiples of six. More precisely, for every epsilon>0 the complete squared error E_N is not O(N^(1-theta-epsilon)). Thus limsup E_N=infinity. This is a refutation of that construction class, including its original two-band member, not of RH, the Nyman criterion, every exact-head construction, or all theta>=2/3. No eventual pointwise divergence or explicit first large numerical failure is claimed.

**ACCEPT Analytic 20261111-analytic-2/DM1-DM4 on paper:** E(1+V)>=1/768000 for arbitrary finite real residue coefficients, and the stated localized lower bound. These are complete-source necessary conditions, not a density construction or a missing upper estimate.

**New original supporting results, 20261112-referee-1/SH1-SH3:** a quantitative correction-cost extension of FT; the exact head/window least-squares problem when the reciprocal moment is relaxed; and an explicit two-band retuning that removes the identified drift while preserving periodic mean one. The retuning changes BOTH moment targets. Its reciprocal correction becomes S(N)-1, independent of the head, and its coefficient-size bound improves accordingly. Its head and remaining middle error are not proved small. These new results are PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING, not a self-issued independent acceptance or a new admitted RH route.

Executed independent exact checks: 76,762 primary assertions plus 3,846 separately registered retuning checks, for 80,608 in the final two programs. Full programs and exact outputs are appended. Repeated executions are not counted again. No computation is used to infer the infinite pole obstruction.

### B. Current Authoritative Objective And Baseline Receipt

Main is `59612bc8b5c30c528d8367667ea5846a8053f114`, tree `1d0f1bca9ba763add9212ea6dc1cb6f2a50f192a`. AGENTS blob `5bf6b1dd837bad943286d05c7dd08441d6a22635`; proof-contract blob `95566e37c8eaeb99ee680660df4f9d2e06ea5038`; cross-route directive blob `e3ae4280438f591f1ffaddd754a1c3a6d35d0691`; continuity directive blob `3e71820a4af722eae7098da6945bb5bcba50dd0d`. The older e922d4... cross-route hash in part of yesterday's Coordinator report predates the continuity preamble; the live hash above is authoritative. No mathematical source change follows from that metadata correction.

The canonical OPEN statement is: one C>=0 before every integer R>=2, |pi(R^2)-vfCanonical(R^2)|<=C R log R, with vfCanonical=vfMid+sqrt(2). The [actual VF consumer](https://github.com/OVVO-Financial/RH_Lean/blob/59612bc8b5c30c528d8367667ea5846a8053f114/research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean) retains its explicit ClassicalVonKochRHCriterion. The O(1) VF/Li_2 comparison is not the missing prime bound.

The separate frozen-history source remains X_R=R^2-1, K_R=max_(0<=y<R)(M(y)-1)^2/(y+1), and Q_R=sum_(1<=a,b<R)mu(a)mu(b)floor(X_R/(ab))=2M(R-1)-M(X_R). Its [finite-C consumer](https://github.com/OVVO-Financial/RH_Lean/blob/59612bc8b5c30c528d8367667ea5846a8053f114/research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean) does not prove the uniform finite-C premise.

Strongest inspected fixed-family compiled comparator:

```text
RHLean.Analysis.native_mertens_near_uniform_window_error_closed
  : MertensGrowthAtMost(b_base),
b_base = 7/8 - 7/(64*N_pack).
forall eps>0, exists C_eps>=0, forall integers n>=1,
  |M(n)| <= C_eps n^(b_base+eps).
```

The [current declaration](https://github.com/OVVO-Financial/RH_Lean/blob/59612bc8b5c30c528d8367667ea5846a8053f114/research/oai_434/VF919WindowErrorClosure.lean#L128) has no desired-growth argument. At the SAME positive explicitFineLength L0, the actual definitions give N_pack=ceil(max(1,1/(6L0)))+2 <= N_old=ceil(max(1,1/(3L0)))+2. Hence 7/(64N_pack)>1/(48N_old); the counts are compared, not identified. A fixed b>b_base is obtained by spending a positive loss, not by deleting it.

Source/dependency audit: fixed native arithmetic and weighted moments -> total-mass LOW plus anchored HIGH/principal/tail on the same probe -> actual Hecke zero boundary -> modulus-one Dirichlet product -> native Mertens converse. The inspected fixed-source moment theorem keeps 51/100<=beta_Hecke<=7/8+Delta, actual geometry and masks, J before the character, then C and Z0 before Z,tau,height. A conditional source record is constructed by its suppliers rather than assumed to contain the desired conclusion. Zeta beta below is NOT the Hecke supremum.

Fresh exact-head metadata and actual completed logs were retrieved in this invocation:

| PR | Tested head / check result | Inspected proof evidence |
| --- | --- | --- |
| #1119, merged | 77ee815846d6d534c866f0752aa33b84c385610a, 14/14 success | [job 128949473700](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42552018910/job/128949473700): five root audits, closures 35358,35375,35736,35737,35753; only propext, Classical.choice, Quot.sound |
| #1093, merged | a54f0cf9535c548920dae3412e3fbe6d6584e029, 13/13 success | [job 127007831273](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41955044802/job/127007831273): eight original-carrier terminal declarations and standard-axiom checks; actual checkout 779336cefaf99d04bf48b837340a076d40aebdd3 |
| #1132, merged 2026-11-11T19:46:26Z | cecb5c2fffbd86026665300bc0d6cc3a35b92cdb, 13/13 success | [job 130731834313](https://github.com/OVVO-Financial/RH_Lean/actions/runs/43080602001/job/130731834313): six relevant closures 3884,179,2332,4058,4109,4278, permitted axioms and original-source dependencies |

Untruncated tree comparisons with current main found zero changes in 911 selected preexisting #1119 source/audit blobs, all four selected #1093 source/workflow/audit blobs, and all four #1132 implementation/check blobs. This is unchanged-source reuse, not a new whole-repository kernel build or a claim that every imported file is placeholder-free. The live root audit uses actual proof values and a global terminal-axiom check. No local Lean or new CI was run.

Pins verified in the logs: Lean 4.34.1/compiler 5045d0056413266e57c625dcd7c365b10e377c52; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612; PNT c39a751132c88b6e8080b74c74023fd95b3d8be0; original math source 1581d4cbdd69a0faf34b2089614fe2a814316a6a; anchored source 9cbfce5295343bcb411e6d2cb159b59995cd985b. The accepted PAPER IR/FFR endpoint 7/8-1/2400000000 remains separate; #1132 proves FFR2, not FFR3 inversion or FFR4 global assembly.

### C. Highest-Risk Mechanisms And Continuity

CONTINUITY_COMPLETE means complete latest-actual discovery and the relevant backfill described here, not rereading the entire historical corpus. The untruncated agent-reports tree was enumerated without a date cap at intake `9a52ef037b48ff003cb063865be6e53fb7f79273`. All roles' latest actual sections were November 11; TODAY=PENDING, YESTERDAY=CARRY_FORWARD. Missing November 12 files are not evidence of executions. Coordinator mirrors have the same blob and count once.

The checkpoint table gives each latest report SHA. Last consumed Referee HR watermark was its November 11 intake at 1855dcff615963978e73bddf4779e9630420a549: Coordinator 106f6d... (FL), Owner accf293... (FA), Analytic 0309d495... (DM), Wheel c998944... (PD), Census a85bc7d... (UM), Lean c86b058... (FFR). Latest own report c288a925... contains HR and its actual 17:26:32 UTC publication receipt. New relevant continuations since that watermark are ADR, FT and PS; their history was reconciled in chronological order. DM/FL/FA were explicitly pending reviews, not missing publications. No unverified intervening report date was discovered. Relevant November 4 P1-P10 original derivation was recovered in full, blob 04ffb1b41d8b6afe5a5d89754f5ccbc8d9682d58.

Latest publication sections consumed: Coordinator FT, 15:55:44 EST; Analytic DM, 09:37:30 EST; Wheel PD, 10:39:35 EST; Census UM, 11:24:34 EST; Referee HR, 12:26:32 EST; Lean ADR, 13:52:07 EST; Owner PS, actual 16:15:01 EST trigger and final verified publication receipt. RUN_ID_UNAVAILABLE remains explicit. GAP=NONE observed after the verified watermarks; no claim is made that silence proves no execution.

External inbox 7d63d434690d00dffce9c90335d41c4f62d85798 contains no new mathematical handoff after October 18. EXT-20261018-PNT-1's cofactor/cutoff conditions and EXT-20261014-5's unconditional-all-root versus conditional-first-bad distinction survive. Its new continuity preamble is not a new arithmetic theorem.

Highest selected risk: continuing to seek OPEN-P10 for coefficients FT actually excludes. Other live risks remain separate: H_ROB is not a magnitude estimate; PS's selected prime-pair payment is not the complete marked/restored source; FFR2 is not its inversion; DM variance growth is necessary but not sufficient. No unchanged large sign census was repeated.

### D. Claims Reviewed And Verdicts

| Stable claim | Referee verdict | Mathematical scope |
| --- | --- | --- |
| 20261111-coordinator-1513-EST/FT1 | ACCEPT | Exact source/window identity, with reciprocal moment and support conditions indispensable; a consequence of compiled #1093 |
| FT2 | ACCEPT | Fixed-b Mertens-to-psi bound and complete-error/window estimate; constants depend on fixed b, not N |
| FT3b-FT3c | ACCEPT | PAPER_PROOF of the stated all-scale non-O conclusion; theta strictly below the gate, no attained supremum or simple-zero assumption |
| FT4 | AUTHOR COMPUTATION READ | Its 225157 count was not rerun; independent smaller exact implementation below supplies separate evidence |
| 20261104-analytic-1/OPEN-P10 for fixed 0<theta<2/3 and its exact original P4 family | REJECT / REFUTED | The full middle convergence assertion fails in that range. P1-P9 identities and correctly qualified upper bounds are not thereby false |
| 20261111-analytic-2/DM1-DM4 | ACCEPT | PAPER_PROOF, arbitrary finite real vectors including H>N; necessary complete-source variance/error restrictions only |
| DM5 | AUTHOR COMPUTATION READ | Different independent finite tests executed here; no claim to rerun its complete 49359-case program |
| 20261112-referee-1/SH1-SH3 | SELF_AUDIT | New supporting correction-cost theorem, exact optimization and retuning bound; independent review pending |
| Owner FA/PS; Coordinator FL2-FL5 | PENDING SEPARATE REVIEW | Latest derivations and scopes retained, not rejected or promoted by this NYMAN investigation |

Prior PD/UM/HR verdicts remain at their unchanged scopes. Coordinator's new independent acceptance of HR1-HR2 is acknowledged. In particular the genuine R=115 gap -195 concerns the nonunit response; the complete restored gap 18331 is not refuted. No further review of that unchanged computation was needed.

### E. Independent Mathematical Reconstruction Of FT

Fix 0<theta<1, N=6K, H=floor(N^theta), L=log(N/H). Eventually 2<=H<N/4. For arbitrary real h(k), 2<=k<=N, require h(k)=0 for k<=floor(N/2) and

```text
q(k)=log(N/max(H,k));
u=sum_(1<=k<=N) mu(k)q(k)/k;
sum_(2<=k<=N) h(k)/k=u;
c(k)=(h(k)-mu(k)q(k))/L;
r(m)=1-sum_(2<=k<=N)c(k)*(m mod k)/k;
E_N=sum_(m>=1) r(m)^2/[m(m+1)].
```

Each finite vector gives a bounded periodic residual and finite E_N. No sign, coefficient-size, variance or periodic-mean hypothesis on h is required by FT. In particular the original two-band solver is included, but not needed.

The [compiled complete return](https://github.com/OVVO-Financial/RH_Lean/blob/59612bc8b5c30c528d8367667ea5846a8053f114/research/NYMAN_FLAT_TAPER_RETURN_20261104.lean#L177) is

```text
L r(m)=m d + U_N(m)-U_H(m)+C_h(m),
d=u-sum h(k)/k,
U_B(m)=sum_(B<k<=m) mu(k)log(B/k)floor(m/k),
C_h(m)=sum_(2<=k<=N)h(k)floor(m/k).
```

For FT, d=0. On I_N={ceil(N/4),...,floor(N/2)}, U_N=C_h=0, so Lr=-U_H. High residue terms themselves do not vanish there; their reciprocal linear contribution has been canceled using the exact moment. This is the first important source check.

Put S(x)=sum_(k<=x)mu(k)log(x/k)/k, delta(x)=1-S(x), and T_H(m)=sum_(k<=H)mu(k)log(H/k){m/k}. The convolution identity sum_(k<=m)mu(k)log(H/k)floor(m/k)=log H+psi(m) gives exactly

```text
U_H(m)=m delta(H)+e_H(m),
e_H(m)=psi(m)-m+log H+T_H(m),
|T_H(m)|<=H log H-log(H!)<=H-1.
```

The last inequality follows from log(H!)>=integral_1^H log t dt, including H=1. No signed interaction or endpoint was removed before this identity.

For a FIXED 0<b<1 and |M(x)|<=C_b x^b, summation by parts gives A(x)=sum_(n<=x)mu(n)log n=O_b(x^b log x). The series sum mu(n)log n/n converges and equals -1 by differentiating the reciprocal-zeta identity on Re(s)>1 and continuing to s=1, justified by b<1. Split psi(x)=-sum_(d<=x)mu(d)log d floor(x/d) at Y. The lower part is x+O_b(xY^(b-1)log x+Y log x); grouping the upper part by its quotient bounds it by O_b(xY^(b-1)log x). With Y=x^(1/(2-b)),

```text
psi(x)-x=O_b(x^alpha log x), alpha=1/(2-b).
```

This deliberately weaker transfer suffices; ordinary PNT alone would not give this fixed power. On I_N let B_N=max |e_H(m)|. Then B_N=O_b(N^alpha log N)+H+log H. The original weighted norm satisfies sum_I m/(m+1)>=N/16 and sum_I1/[m(m+1)]<=4/N. Taking a norm only after the exact reconstruction yields

```text
|delta(H)| <= 4L sqrt(E_N/N)+8B_N/N.                 (E.1)
```

For Re(s)>0, absolute convergence justifies

```text
integral_1^infinity delta(x)x^(-s-1)dx
  =1/s-1/[s^2 zeta(1+s)].                           (E.2)
```

If delta(x)=O(x^-a), the left side is holomorphic for Re(s)>-a. At any nontrivial zero rho with Re(rho)>1-a, the right side has an uncanceled pole at rho-1, which is not zero. Multiplicity only increases the pole order. The apparent singularity at s=0 is removable since 1/zeta(1+s)=s+O(s^2). Meromorphic continuation and the identity theorem therefore forbid that decay whenever 1-a is below the actual rightmost zeta boundary beta.

The inspected [converse declaration](https://github.com/OVVO-Financial/RH_Lean/blob/59612bc8b5c30c528d8367667ea5846a8053f114/research/MERTENS_CONVERSE_IDENTIFICATION.lean#L169) gives every fixed Mertens power b>beta. The certified baseline gives beta<1. Hardy's theorem supplies beta>=1/2; only existence of a critical-line zero is needed, not RH or zero simplicity. The authoritative external statement is [Sangale, Hardy's Theorem, page 3](https://arxiv.org/pdf/1606.00680).

Suppose 0<theta<1/(2-beta) and E_N=O(N^p), where p=1-2theta(1-beta)-epsilon for some epsilon>0. Choose ONE b>beta sufficiently close to beta, with b<1, before N varies. In H units the three terms of (E.1) have decay powers

```text
a1=(1-p)/(2theta)=1-beta+epsilon/(2theta),
a2=(1-b)/[(2-b)theta],
a3=1/theta-1.
```

All exceed 1-beta. Select 1-beta<a<min(a1,a2,a3,1); the strict margin pays every logarithm. As K grows, consecutive (6K)^theta eventually differ by less than one, so their floors visit EVERY sufficiently large integer H. For H<=x<H+1, S(x)-S(H)=log(x/H)sum_(n<=H)mu(n)/n=O(log H/H). Thus the integer conclusion extends to delta(x)=O(x^-a). An actual zero with Re(rho)>1-a exists by the definition of supremum, whether or not beta is attained. Equation (E.2) contradicts it.

This proves FT3b exactly. Since beta>=1/2, theta<2/3 satisfies its strict gate and 1-2theta(1-beta)>=1-theta. Hence FT3c follows. Bounded E_N would satisfy the forbidden bound with, for example, epsilon=(1-theta)/2; consequently limsup E_N=infinity. This last step does not show eventual monotonic growth.

The complete Nyman source and its density consumer use the unchanged weight 1/[m(m+1)] and residues {m/k}; vanishing E would meet [Bagchi's Theorem 1](https://arxiv.org/html/math/0607733v1). FT excludes a specified coefficient family, not that full-span criterion. No external theorem asserting convergence of this family was assumed.

### F. New Correction-Cost Theorem And Exact Negative Controls

**SH1, robust complete-source bill.** Allow ARBITRARY h(k), including early corrections and a nonzero moment defect d. Keep the same N,H,L and original c,r,E. On I_N define

```text
g_N(m)=m d+C_h(m),
J_N=sum_(m in I_N)g_N(m)^2/[m(m+1)],
W_N=E_N+J_N/L^2.
```

The exact return is Lr=g_N-m delta(H)-e_H. Therefore

```text
|delta(H)|<=4/sqrt(N)*(L sqrt(E_N)+sqrt(J_N))+8B_N/N
           <=4L sqrt(2W_N/N)+8B_N/N.               (SH1.1)
```

Repeat the fixed-b, floor-coverage and Mellin argument above. For 0<theta<1/(2-beta) and every epsilon>0,

```text
W_N is not O(N^(1-2theta(1-beta)-epsilon)).          (SH1.2)
```

This is an unconditional necessary tradeoff using the same certified beta<1 input. It does not forbid large signed repair terms that cancel in r. If E_N->0, then for each 0<epsilon<p0, p0=1-2theta(1-beta)>0, J_N/L^2 cannot be O(N^(p0-epsilon)). An exact-moment, high-only correction has J_N=0 and recovers FT. Thus merely renaming the correction or claiming its norm is negligible cannot repair the excluded source. This is a bound on a defined additional bill, not an RH-equivalent premise assumed true.

Two exact finite negative controls, also covered by the independent implementation:

- N=12,H=2, h supported at N, d=L/7: r(1)=1/7. Dropping m d wrongly predicts an exact head.
- N=12,H=2, add h(3)=log 2 and compensate its reciprocal moment at 12: d remains zero, but Lr(3) changes by log 2. Dropping the early floor correction wrongly preserves the old window identity.

These are counterexamples to the stated omissions, not counterexamples to FT, whose hypotheses they respectively violate.

### G. Original-Carrier And Covariance Audit

The selected source uses genuine mu(k), every modulus 2<=k<=N including squareful correction directions, the original constant target, and every m>=1. Head, transition, correction-band, m>N and infinite-tail terms are never deleted from E_N. Restricting the nonnegative full energy to a window is a one-way LOWER bound, not an equality or an upper estimate. The exact returned numerator keeps U_N, -U_H, C_h and the moment defect together; squaring includes all mixed terms.

| Euler / finite AC | VF / actual primes | NNS / OAI | Square blocks / native Mertens |
| --- | --- | --- | --- |
| Q_R=sum mu(a)mu(b)floor((R^2-1)/(ab)), a,b<R, strict K_R. EXACT_IDENTITY to 2M(R-1)-M(X_R); conditional finite-C consumer. No equality with Nyman error. | Canonical pi-VF_can and full wheel li(X_R)-pi(X_R), with virtual divisors and Euler compensation. NOT_EQUIVALENT to E_N or delta(H); genuine prime coupling is needed. The canonical classical interface remains explicit. | Original ideal-labelled compensated tuple atoms, characters, height/conductor weights, signed Gram and principal return. Native endpoint -> Mertens is ONE_WAY_IMPLICATION. Rational residue coefficients are not Hecke atoms; no isometry supplies cancellation. | Same all-prefix Mertens function feeds FT's fixed-b supplier through the inspected converse. This is a valid ONE_WAY_IMPLICATION, not equality of square-shell energy, K_R and Nyman covariance. Canonical LOW/HIGH and all mixed terms remain separate. |

The prime-side quantity psi in E is connected by the explicit finite convolution -sum mu(d)log d floor(m/d), not by equating prime discrepancy with Mertens or substituting Li density. No owner admission, clipping, ancestral multiplicity or #915 denominator is imported into the Nyman statistic. Atlas blob cd0419d00a37739fe5a292f5cb738e33213949d5 was used as navigation; original declarations govern the arrows.

### H. Quantifiers And No-Circularity Audit

FT uses a fixed theta, then a hypothetical epsilon and bound constant, then a fixed b>beta and constants, before N. The actual zero supremum is not replaced by 1/2. The strict theta gate is essential: the present proof at equality loses the required exponent gap. It proves neither theta=2/3 nor all theta<1. Attempting that extension with the same bounds fails at a2 or a3; this is a limitation of the argument, not a theorem that larger-head approximants work.

SH1 likewise fixes all parameters before scale and measures the complete correction action, not the largest individual coefficient. It places no unsupported sign assumption on g_N. SH2-SH3 below change the reciprocal-moment/exact-head hypothesis visibly; they do not repair FT within its original hypotheses.

The old OPEN-P10, for its complete fixed coefficient family and paid complement, would have implied Nyman density. FT now disproves it for theta<2/3. A renamed complete middle bound for a new family is not an independently easier theorem. No reverse implication from RH to that particular new family has been proved; it must not be labeled TARGET_EQUIVALENT without both directions. DM and SH are necessary restrictions, not sufficient density or RH claims.

### I. Constructive Repairs: Exact Soft-Head Optimization And Retuning

**SH2.** Assume again h(k)=0 for k<=floor(N/2), but do NOT impose d=0. For N>=16, 1<=H<ceil(N/4), put

```text
A=sum_(1<=m<=H)m/(m+1),  B=sum_(m in I_N)m/(m+1),
Z=sum_(m in I_N)U_H(m)/(m+1),
Y=sum_(m in I_N)U_H(m)^2/[m(m+1)].
```

The exact head has become Lr(m)=m d. The disjoint head-plus-window energy is EXACTLY

```text
L^2 E_(head union window)
 = (A+B)d^2-2dZ+Y
 = (A+B)(d-Z/(A+B))^2+Y-Z^2/(A+B).                (SH2.1)
```

Every real d is realizable by the high coefficient h(N)=N(u-d). Thus d*=Z/(A+B) is the actual finite-subproblem minimizer, not just a formal optimization over an inadmissible scalar. It is not the minimizer of the entire infinite error. A second high-band moment can preserve mean one without restricting d, as below.

Writing U_H(m)=m delta(H)+e_H(m) and e_I^2=sum_I e_H(m)^2/[m(m+1)], the weighted triangle inequality on the TWO regions gives the useful unconditional lower bound

```text
L sqrt(E_N) >= (sqrt(A*B/(A+B))*|delta(H)|-e_I)_+.
```

Indeed the unperturbed squared norm is A d^2+B(d-delta)^2, whose minimum is AB delta^2/(A+B). If H=o(N), A is asymptotic to H and B is comparable to N, so allowing d changes this drift penalty from order N delta^2 to order H delta^2. This explains quantitatively why the exact-head condition matters. It does not make the complete middle small.

**SH3. Explicit source-faithful retuning.** Set d=delta(H). Then the identified linear drift cancels on the entire uncorrected window:

```text
Lr(m)=-e_H(m) for m in I_N;
E_head=A delta(H)^2/L^2.                           (SH3.1)
```

For the actual two-band supports I1={3K+1,...,4K}, I2={5K+1,...,6K}, write s_i=sum_(k in Ii)1/k and v=2L+sum_(k<=N)mu(k)q(k). Replace BOTH original scalar targets by

```text
u_new=u-d,   v_new=v-d,
A_new=(u_new-s2*v_new/K)/(s1-s2),
Z_new=(s1*v_new/K-u_new)/(s1-s2).
```

Use h=A_new on I1, h=Z_new on I2, zero elsewhere, and unchanged c=(h-mu*q)/L. Since s1-s2>1/20, this is always well-defined. Direct calculation gives sum c(k)/k=1-d/L and sum c(k)(k-1)/(2k)=1. If v were left unchanged, the periodic mean would instead be 1+d/(2L). That error is independently tested, not silently repaired in a claimed old statement.

There is a further arithmetic simplification: u=S(N)-S(H), so with d=1-S(H),

```text
u_new=S(N)-1=-delta(N),                            (SH3.2)
```

which is independent of H. This is a natural removal of the truncation bias, not an arbitrary desired-error hypothesis. It uses only the genuine mu values already present in the coefficient construction.

Here is an independent quantitative bound. Under any fixed |M(x)|<=C x^b with 0<b<1, partial summation and sum mu(n)/n=0 give

```text
|sum_(n<=t)mu(n)/n| <= C*(2-b)/(1-b)*t^(b-1),
|delta(t)| <= C*K_b*t^(b-1), K_b=(2-b)/(1-b)^2.
```

For the second inequality use S'(t)=(sum_(n<=t)mu(n)/n)/t between integers, continuity of S, S(infinity)=1, and integrate the first bound from t to infinity. The endpoint value follows from the same convergent log-reciprocal identity used in FT. No RH input is used.

Consequently |u_new|<=C K_b N^(b-1), whereas the old u bound depended on H^(b-1). Also sum mu(k)q(k)=integral_H^N M(t)dt/t, so |v_new|<=2L+C N^b/b+C K_b. The same explicit two-by-two solver gives

```text
max(|A_new|,|Z_new|)/L
 <= C*(60*K_b+40/b)*N^(b-1)/L+80/N.                (SH3.3)
```

This is uniform for 1<=H<=N/2 and improves the correction-size supplier; it does not control the full error. In particular E_head<=C^2 K_b^2 H^(2b-1)/L^2. With the available b>1/2 this UPPER bound is not a decaying certificate. Nor does a growing upper bound prove divergence. The interior residual, both correction activations, U_N beyond N, periodic covariance and infinite tail all remain in the new consumer. Existing tail estimates cannot be imported under the old coefficients without explicitly checking their hypotheses.

### J. Competing Proof-Strategy Assessment And Loss Ledger

| Source -> first loss | Paid recovery / exact check | Net consumer and verdict |
| --- | --- | --- |
| Flat taper -> set reciprocal defect to zero to force exact head | Compiled nyman_flat_complete_return restores the omitted m d; FT proves the high-only exact-head subclass cannot converge for theta<2/3 | Retire only this subclass. More high-supported coefficients with the SAME moment do not change the window |
| Complete U_H -> bound psi and T_H separately | Fixed-b source and exact convolution pay alpha=1/(2-b); abs(T_H)<=H-1 | These costs explain the strict theta gate. They are sufficient for a lower obstruction, not an upper approximation estimate |
| New correction -> declare small coefficients negligible | SH1 keeps its full floor action and moment term; SH3 gives genuine coefficient-size improvement | A large weighted correction action is compatible with small individual coefficients. No new global exponent or density is paid |
| DM coefficient recovery -> triangle at each divisor error | Full squarefree Gram and aggregate residual differences recover one forced direction BEFORE Cauchy-Schwarz | Valid E-V lower restriction, not orthogonality or a sufficient middle bound |
| OAI original principal -> discard delay interactions | Merged #1131 mass and #1132 all-delay return preserve the SAME signal | FFR3 and FFR4 remain open formal work; no transfer from the Nyman retuning to Hecke atoms |

No new proof route is admitted. FT is a substantial complete-source exclusion at the campaign's second admission criterion; SH consists of supporting repairs and an unpaid alternative, not a tenth route. Keep VF-LOW, SAT, CODIV, OAI-NNS, JOH, FINITE-AC, CORR4, MU-LIFT and NYMAN distinct. A change outside authorized priorities still requires the Proof Architect/human process.

### K. Original Research And Independent Verification

SH1 extends the no-go to explicitly measured early/moment repairs; SH2 solves the exact admissible finite head/window optimization; SH3 derives an explicit dual-moment correction, head-independent reciprocal target and improved correction-size bound. These are original derivations in this execution. Elementary Hilbert projection, partial summation and the inherited compiled return are credited as tools, not claimed as newly discovered theories. A scoped search of the retrieved November 4 and November 11 reports found the suggestion to try approximate heads, but not these specific formulas. No exhaustive literature-priority claim is made.

Independent primary checker: N=6,12,...,90; 99 integer head choices; 495 finite coefficient configurations; every 1<=m<=2N; original endpoint and two-band corrections, a relaxed moment, a retuned moment, and an early correction. Exact rational vectors in 1 and log(prime) certify all source equalities. Quadratic polynomials certify the weighted complete-square identities without floating-point signs. No independence of logarithms is assumed. Separate DM tests use 115 deterministic rational vectors, N=2..24 and H=2,3,4,8,16,32,48, including H>N. Four rational beta values and 80 strict exponent-gate cases test the algebra, not actual measured zero locations.

Primary result: 76,762 assertions PASS, including 54,720 complete returns, 7,205 delta decompositions, 396 exact soft-head quadratics, 99 attained finite projections, 115 full covariance/Jordan identities, and 805 checks each for DM's combined identity, dual norm, directional bound, residual Cauchy bound and master inequality. Script SHA256 76db3ee759e1b8932f792821b6d883e1d7ab1f1cab93cb79275ce9d5b35441d0; registration SHA256 170d81449d5b19e6736039b87325153eb137242f1a317113336a722370437446.

The separately registered two-target retuning follow-up first passed 3,747 checks. A proof-led added check then verified u-d=S(N)-1 for the same 99 heads; its final output and updated hashes are appended. Python syntax compilation passed. No local Lean, upstream-executable reuse, empirical asymptotic fitting, floating-point near-zero sign claim or untested infinite-tail certification occurred.

For DM, the independent proof reconstruction is as follows. The full covariance has Jordan form 12V=sum_(d>=2)J2(d)q_d^2, q_d=sum_(d|k)c_k/k. Multiples inversion gives c_k=<x,v_k>. For squarefree k,l, the complete functional Gram is zeta(2)mu(k)mu(l)/(kl)*sum_(d|gcd(k,l))d^2; the squareful multiple in a common-prime local factor is essential. For u_H=sum_(squarefree 2<=k<=H)mu(k)v_k, its norm squared is at most zeta(2)sum_(d<=H)Harmonic(floor(H/d))^2<=3zeta(2)zeta(3)H<=25H/4. The last harmonic identity follows by grouping the absolutely convergent positive double sum; no prime-independence assumption enters.

Aggregate the exact coefficient recovery before any norm: s_H+sum mu(k)c_k=sum_(m<=H)b_m r(m), with a_1=s_H, a_d=sum_(squarefree k<=H,d|k)mu(k)mu(k/d), a_(H+1)=0, b_m=a_m-a_(m+1). The bounds |a_d|<=H/d give sum m(m+1)b_m^2<=5H^3. Hence s_H<=sqrt(75HV)+sqrt(5H^3 E_H). The elementary squarefree bound s_H>=H/2-1 yields V>=H/1200 if H>=8 and E_H<=1/(320H). For 0<E<=1/2560 take H=floor(1/(320E))>=1/(640E), giving EV>=1/768000; larger E is immediate. E=0 is impossible for any finite vector at a common multiple of its moduli. Finally T>=max(8,4800V) yields E_T>=1/(80T). This verifies the constants, the endpoint and H>N scope independently. It does not upper-bound any approximation error.

### L. Formalization Guidance

FT1's complete return is already compiled; do not create a duplicate algebra PR. FT2-FT3 and DM1-DM4 now have this independent ACCEPT_ON_PAPER, not Lean certification. A formal FT3 proof would need the exact Mellin transform, analytic continuation/pole obstruction, all-scale floor interpolation and actual zeta-boundary supplier. An assumption asserting delta's desired decay or the target norm would invalidate its purpose.

SH1-SH3 need independent review before acceptance. SH2 is elementary algebra but is not, alone, a reason for a filler PR. If a revised Nyman family becomes strategically justified, reuse nyman_flat_complete_return with its defect rather than changing that theorem. Preserve both retuned moments and all tails. Continue the already accepted FFR3/FFR4 queue with #1132's actual hypotheses; its merge does not certify those later stages.

### M. Specialist Handoffs

- Proof Architect: FT1-FT3 accepted at the strict stated gate. Mark original OPEN-P10 false for theta<2/3 only. Record SH as self-audited supporting repair, not a new RH route. The live policy hash is e3ae428..., not the pre-continuity value.
- Analytic Type II: DM1-DM4 accepted on paper. For NYMAN, test the explicit SH3 family with targets u-d and v-d, d=delta(H). Its improved correction-size supplier is paid, but head error and complete middle remain unpaid. Reusing the old exact-head tail split without modification is invalid. Preserve CODIV/OAI portfolio coverage.
- Owner Payment: FA/PS remain pending separate independent review. Preserve the genuine r=71, q=299, n=5083, singleton {13} certificate and the complete restoration/mark distinction. This run does not turn raw donor availability into a global payment.
- Finite Wheel: PD/HR scope remains unchanged; the Nyman repair has no coefficient map to the powerful-response ledger. Keep the genuine H-E mixed interaction and strict K_R.
- Prime Census: no larger unchanged sign scan is requested. A new Nyman test should separate head, pre-correction window, both correction activations and remote tail, include the two moment checks and compare the same full error. Finite checks cannot establish the pole-based non-O theorem.
- Lean Verification: #1132 is merged and verified, not merely green/unmerged. FT and DM have scoped paper acceptance; SH does not yet have independent acceptance. No source edits or new PRs are requested by this report.

### N. First Independently Missing Mathematical Ingredient

For the rejected exact-head subclass with theta<2/3 there is no true OPEN-P10 estimate left to prove. For the new SH3 coefficients, the concrete unresolved consumer is the original weighted squared norm of

```text
m delta(H)+U_N(m)-U_H(m)+C_(h_new)(m),
```

divided by L^2, over ALL m>=1. A useful next theorem must independently pay the head cost and the signed middle, then verify the tail hypotheses for these new coefficients. Merely asserting that this full quantity tends to zero renames the desired sufficient density condition. Neither b_base nor DM supplies that upper bound. No reverse implication identifying this particular family with RH has been proved.

The separate best formal progress still needs FFR3 finite-interval response inversion and FFR4 complete physical assembly. No claim about one carrier discharges the other.

### O. Next-Run Resume Capsule

```text
RUN=2026-11-12T04:13:01-05:00; LABEL=20261112-referee-1/FT;
RUN_ID_UNAVAILABLE; cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1;
continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1.
MAIN=59612bc8b5c30c528d8367667ea5846a8053f114.
ACCEPT=FT1-FT3, exact scope incl theta<1/(2-beta);
  unconditional corollary theta<2/3; DM1-DM4 necessary bounds.
REFUTED=original P4/OPEN-P10 for fixed 0<theta<2/3 only.
NEW_SELF_AUDIT=SH1 repair-energy bill; SH2 soft-head projection;
  SH3 dual-moment retuning, u_new=-delta(N), improved coefficient bound.
SOURCE_GUARDS=actual mu; full basis; weights 1/[m(m+1)];
  both moments distinct; all U/correction/cross/tail terms retained.
CI=#1119/#1093/#1132 green and merged; actual logs read;
  selected source trees unchanged; no new Lean execution.
PENDING=independent SH review; PS/FA and residual FL scope reviews;
  FFR3/FFR4 formal return; complete new Nyman upper estimate.
NO_NEW_GLOBAL_GAIN; NO_NEW_ACCEPTED_ROUTE; VERIFIED_ETA=NONE; RH=OPEN.
NEXT=independent PS source/restoration review, or a genuinely new
  SH3 head-and-middle bound; do not rerun FT or old R=115 scans.
```

Early checkpoint commit 2b3ad783f50ceabab11dc8633e2a95d830be87a2, blob a810b337e7f6c17b48e6de4d5cb469c269ac55bf, was fetched at its immutable commit and matched exactly. Final publication evidence follows only after actual write/readback. Tool limitation: a direct git read failed CONNECT tunnel 403; authenticated GitHub reads/writes and completed log retrieval succeeded. No Lean source, main, other agent report, shared policy, proof branch, PR, workflow, schedule, permission, merge or agent launch was modified. Only this owned report is authorized remotely.

## Material Source And Handoff Receipt

All source links below are immutable at inspected main `59612bc8b5c30c528d8367667ea5846a8053f114`. Blob hashes identify the exact inspected content, not merely a branch name.

| Material source | Blob SHA |
| --- | --- |
| [AGENTS.md](https://github.com/OVVO-Financial/RH_Lean/blob/59612bc8b5c30c528d8367667ea5846a8053f114/AGENTS.md) | `5bf6b1dd837bad943286d05c7dd08441d6a22635` |
| [CURRENT_PROOF_CONTRACT.md](https://github.com/OVVO-Financial/RH_Lean/blob/59612bc8b5c30c528d8367667ea5846a8053f114/CURRENT_PROOF_CONTRACT.md) | `95566e37c8eaeb99ee680660df4f9d2e06ea5038` |
| [docs/RHLEAN_CROSS_ROUTE_SIGNED_RECOVERY_20261110.md](https://github.com/OVVO-Financial/RH_Lean/blob/59612bc8b5c30c528d8367667ea5846a8053f114/docs/RHLEAN_CROSS_ROUTE_SIGNED_RECOVERY_20261110.md) | `e3ae4280438f591f1ffaddd754a1c3a6d35d0691` |
| [docs/RHLEAN_REPORT_CONTINUITY_LAST_ACTUAL_20261111.md](https://github.com/OVVO-Financial/RH_Lean/blob/59612bc8b5c30c528d8367667ea5846a8053f114/docs/RHLEAN_REPORT_CONTINUITY_LAST_ACTUAL_20261111.md) | `3e71820a4af722eae7098da6945bb5bcba50dd0d` |
| [docs/COORDINATE_ATLAS.md](https://github.com/OVVO-Financial/RH_Lean/blob/59612bc8b5c30c528d8367667ea5846a8053f114/docs/COORDINATE_ATLAS.md) | `cd0419d00a37739fe5a292f5cb738e33213949d5` |
| [research/NYMAN_FLAT_TAPER_RETURN_20261104.lean](https://github.com/OVVO-Financial/RH_Lean/blob/59612bc8b5c30c528d8367667ea5846a8053f114/research/NYMAN_FLAT_TAPER_RETURN_20261104.lean) | `2d23721027ecc44e85b7add02fc632b482f03352` |
| [research/NYMAN_HIGH_COEFFICIENT_INVARIANT_20261104.lean](https://github.com/OVVO-Financial/RH_Lean/blob/59612bc8b5c30c528d8367667ea5846a8053f114/research/NYMAN_HIGH_COEFFICIENT_INVARIANT_20261104.lean) | `2da630c1d5fb9302e2097ec1e170cf41c2b40609` |
| [research/MERTENS_CONVERSE_IDENTIFICATION.lean](https://github.com/OVVO-Financial/RH_Lean/blob/59612bc8b5c30c528d8367667ea5846a8053f114/research/MERTENS_CONVERSE_IDENTIFICATION.lean) | `768c8255850bf4074aff265c3fe17a1f5c43979b` |
| [research/oai_434/VF919WindowErrorClosure.lean](https://github.com/OVVO-Financial/RH_Lean/blob/59612bc8b5c30c528d8367667ea5846a8053f114/research/oai_434/VF919WindowErrorClosure.lean) | `f629db1b2b65d6ec042ac9432397d4b6316200c6` |
| [research/oai_434/VF919NativeSevenEighthsReplay.lean](https://github.com/OVVO-Financial/RH_Lean/blob/59612bc8b5c30c528d8367667ea5846a8053f114/research/oai_434/VF919NativeSevenEighthsReplay.lean) | `111c933a7ca15647105ce6a4d0f3cbfc3cde81f4` |
| [research/oai_434/VF919NativeStrictMertens.lean](https://github.com/OVVO-Financial/RH_Lean/blob/59612bc8b5c30c528d8367667ea5846a8053f114/research/oai_434/VF919NativeStrictMertens.lean) | `b33a4883e1ddb0551b0f11f062bce46680d87450` |
| [research/oai_434/VF919ExplicitSquareBlockPacking.lean](https://github.com/OVVO-Financial/RH_Lean/blob/59612bc8b5c30c528d8367667ea5846a8053f114/research/oai_434/VF919ExplicitSquareBlockPacking.lean) | `32999039fdeea99c58a070c1c4ee9c140720dd44` |
| [research/oai_434/VF919ExplicitFixedSourceSlotCount.lean](https://github.com/OVVO-Financial/RH_Lean/blob/59612bc8b5c30c528d8367667ea5846a8053f114/research/oai_434/VF919ExplicitFixedSourceSlotCount.lean) | `bad5aab0a60e96d19e7c9550cd7c0a072288bc0f` |
| [scripts/lean/window_error_closure/WindowErrorClosureAudit.lean](https://github.com/OVVO-Financial/RH_Lean/blob/59612bc8b5c30c528d8367667ea5846a8053f114/scripts/lean/window_error_closure/WindowErrorClosureAudit.lean) | `1f17f9401a63d16227db2e2aad020b9f74bc5f4e` |
| [research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean](https://github.com/OVVO-Financial/RH_Lean/blob/59612bc8b5c30c528d8367667ea5846a8053f114/research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean) | `79030d70e8d3e0d08eef9bac53fef95c36eca2fb` |
| [research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/59612bc8b5c30c528d8367667ea5846a8053f114/research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean) | `e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73` |
| [research/oai_434/VF919PrincipalAllDelayReturn.lean](https://github.com/OVVO-Financial/RH_Lean/blob/59612bc8b5c30c528d8367667ea5846a8053f114/research/oai_434/VF919PrincipalAllDelayReturn.lean) | `9fc9e047f143b09284857766d669054bae45bd19` |

Latest-actual handoffs were read at the intake branch state `9a52ef037b48ff003cb063865be6e53fb7f79273`. The November 11 Coordinator evening mirror has the same content hash as its morning path.

| Handoff | Blob SHA |
| --- | --- |
| [agent_reports/2026-11-11/00-coordinator-am.md](https://github.com/OVVO-Financial/RH_Lean/blob/9a52ef037b48ff003cb063865be6e53fb7f79273/research/agent_reports/2026-11-11/00-coordinator-am.md) | `c87ed2c4ec81f9f4eda85ba0d84e2216808159f4` |
| [agent_reports/2026-11-11/10-owner-payment.md](https://github.com/OVVO-Financial/RH_Lean/blob/9a52ef037b48ff003cb063865be6e53fb7f79273/research/agent_reports/2026-11-11/10-owner-payment.md) | `182b17762cbb1c092956ffb1cb4d1335fa0acec9` |
| [agent_reports/2026-11-11/20-analytic-type-ii.md](https://github.com/OVVO-Financial/RH_Lean/blob/9a52ef037b48ff003cb063865be6e53fb7f79273/research/agent_reports/2026-11-11/20-analytic-type-ii.md) | `0309d49557af30da43a07d72dce93c93c1811157` |
| [agent_reports/2026-11-11/30-finite-wheel.md](https://github.com/OVVO-Financial/RH_Lean/blob/9a52ef037b48ff003cb063865be6e53fb7f79273/research/agent_reports/2026-11-11/30-finite-wheel.md) | `c9989449a814a1a7ee799791c73450872f4c7d3c` |
| [agent_reports/2026-11-11/40-prime-census.md](https://github.com/OVVO-Financial/RH_Lean/blob/9a52ef037b48ff003cb063865be6e53fb7f79273/research/agent_reports/2026-11-11/40-prime-census.md) | `a85bc7dc8b49952d37f1a4cb6a0a8eb307d3f352` |
| [agent_reports/2026-11-11/50-adversarial-referee.md](https://github.com/OVVO-Financial/RH_Lean/blob/9a52ef037b48ff003cb063865be6e53fb7f79273/research/agent_reports/2026-11-11/50-adversarial-referee.md) | `c288a925fd064a551a0d2bd70b27d82acc9fe926` |
| [agent_reports/2026-11-11/60-lean-verification.md](https://github.com/OVVO-Financial/RH_Lean/blob/9a52ef037b48ff003cb063865be6e53fb7f79273/research/agent_reports/2026-11-11/60-lean-verification.md) | `943749938c321f0ec13e1680139f5b15cea39fd7` |
| [agent_reports/EXTERNAL_HANDOFFS.md](https://github.com/OVVO-Financial/RH_Lean/blob/9a52ef037b48ff003cb063865be6e53fb7f79273/research/agent_reports/EXTERNAL_HANDOFFS.md) | `7d63d434690d00dffce9c90335d41c4f62d85798` |
| [agent_reports/2026-11-04/20-analytic-type-ii.md](https://github.com/OVVO-Financial/RH_Lean/blob/9a52ef037b48ff003cb063865be6e53fb7f79273/research/agent_reports/2026-11-04/20-analytic-type-ii.md) | `04ffb1b41d8b6afe5a5d89754f5ccbc8d9682d58` |

Fresh publication-time checks (2026-11-12, approximately 04:40 EST): main remains `59612bc8b5c30c528d8367667ea5846a8053f114`; open/draft PR collection is empty. The untruncated agent-reports tree at `2b3ad783f50ceabab11dc8633e2a95d830be87a2` has 3,266 entries and differs from intake only in this run's owned checkpoint. No new other-role report appeared. The current owned blob was fetched again and exactly matches the checkpoint. PR #1131's actual metadata separately confirms merge at 2026-11-11T12:46:15Z, merge `dda92f9ce59627b4c1f1317082f728648d330a0a`; stale "not merged" prose in its description is not current status.

## Reproduction Appendix

The programs below were written independently in this run and executed with Python 3.12 and its standard library. The exact registration files are included because the programs hash them. Each program runs with its named registration file beside it. The primary program was rerun unchanged before publication and returned the identical 76,762-check result. The final follow-up adds 3,846 checks; the earlier 3,747-check version and repeated executions are not added again. Total final-program assertions: **80,608**, all passed. These are finite exact algebra checks, not Lean certificates or proofs of the infinite no-go theorem.

<details>
<summary>Primary preregistration: registration.md</summary>

```text
# Independent FT / Soft-Head Review Registration

Registered before executing the independent checker, 2026-11-12.

- FT domain: N=6,12,...,90; 1<=H<=min(8,ceil(N/4)-1).
- Five genuine finite residue coefficient families: exact endpoint moment,
  original two-band/two-moment correction, high-supported defect delta(H),
  high-supported defect L/7, and an early correction at H+1 with the
  reciprocal moment restored at N.
- Complete return tested at every 1<=m<=2N. Head and correction-free window
  identities tested at their literal integer endpoints.
- New soft-head test: exact original weighted head-plus-window quadratic,
  its least-squares minimizer and complete square, and delta(H) retuning.
- Arithmetic uses exact rational vectors in 1 and log(prime), and exact
  quadratic polynomials. Equality is certified algebraically; no assumed
  linear independence of logarithms and no floating-point sign test.
- Independent DM tests: N=2,...,24; five deterministic rational coefficient
  patterns; H=2,3,4,8,16,32,48, including H>N. Check full covariance/Jordan
  identity, combined residual inversion, dual norm, master inequality and
  its stated finite implications with exact rationals.
- Exponent checks: beta=1/2,9/16,3/4,7/8; ten strict rational theta values
  below 1/(2-beta), epsilon=1/10,1/100. Choose a single fixed b>beta and
  verify every strict decay gate. Check equality fails the strict gate.
- Fixed negative controls N=12,H=2: omitting the moment defect gives wrong
  r(1); an early correction changes the window despite exact moment.
- Finite execution does not prove the infinite pole obstruction or RH.

No upstream executable is reused. No local Lean execution is performed.
```

</details>

<details>
<summary>Independent primary program: verify_ft.py</summary>

```python
"""Independent source, soft-head, and directional-variance checks."""

from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from math import gcd
import hashlib
import json
from pathlib import Path


def add(*vectors):
    out = {}
    for vector in vectors:
        for key, value in vector.items():
            out[key] = out.get(key, Q(0)) + value
    return {k: v for k, v in out.items() if v}


def scale(vector, scalar):
    return {k: v * scalar for k, v in vector.items() if v * scalar}


def sub(a, b):
    return add(a, scale(b, -1))


def mul(a, b):
    out = {}
    for i, x in a.items():
        for j, y in b.items():
            key = tuple(sorted((i, j)))
            out[key] = out.get(key, Q(0)) + x * y
    return {k: v for k, v in out.items() if v}


def square(a):
    return mul(a, a)


@lru_cache(None)
def factors(n):
    out = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            e = 0
            while n % p == 0:
                n //= p
                e += 1
            out.append((p, e))
        p += 1
    if n > 1:
        out.append((n, 1))
    return tuple(out)


def mu(n):
    fs = factors(n)
    return 0 if any(e > 1 for _, e in fs) else (-1) ** len(fs)


@lru_cache(None)
def logv(n):
    return {p: Q(e) for p, e in factors(n)}


ONE = {0: Q(1)}


@lru_cache(None)
def tail(B, m):
    return add(*(scale(sub(logv(B), logv(k)), mu(k) * (m // k))
                 for k in range(B + 1, m + 1)))


@lru_cache(None)
def psi(m):
    return add(*({fs[0][0]: Q(1)} for n in range(2, m + 1)
                 if len(fs := factors(n)) == 1))


def floor_correction(h, m):
    return add(*(scale(v, m // k) for k, v in h.items()))


def energy(vectors):
    return add(*(scale(square(v), Q(1, m * (m + 1)))
                 for m, v in vectors.items()))


counts = Counter()


def check(label, condition):
    assert condition, (label, dict(counts))
    counts[label] += 1


cases = 0
for N in range(6, 91, 6):
    K = N // 6
    left = (N + 3) // 4
    interval = range(left, N // 2 + 1)
    B = sum(Q(m, m + 1) for m in interval)
    check("window_signal", B >= Q(N, 16))
    check("window_weight", sum(Q(1, m * (m + 1)) for m in interval) <= Q(4, N))
    for H in range(1, min(8, left - 1) + 1):
        cases += 1
        L = sub(logv(N), logv(H))
        base = {k: scale(sub(logv(N), logv(max(H, k))), mu(k))
                for k in range(1, N + 1)}
        u = add(*(scale(v, Q(1, k)) for k, v in base.items()))
        v = add(scale(L, 2), *base.values())
        delta = sub(ONE, add(*(scale(sub(logv(H), logv(k)), Q(mu(k), k))
                              for k in range(1, H + 1))))
        s1 = sum(Q(1, k) for k in range(3 * K + 1, 4 * K + 1))
        s2 = sum(Q(1, k) for k in range(5 * K + 1, 6 * K + 1))
        first = scale(sub(u, scale(v, s2 / K)), 1 / (s1 - s2))
        second = scale(sub(scale(v, s1 / K), u), 1 / (s1 - s2))
        bands = {**{k: first for k in range(3 * K + 1, 4 * K + 1)},
                 **{k: second for k in range(5 * K + 1, 6 * K + 1)}}
        early = {H + 1: logv(2), N: scale(sub(u, scale(logv(2), Q(1, H + 1))), N)}
        families = {
            "exact": ({N: scale(u, N)}, {}),
            "bands": (bands, {}),
            "retuned": ({N: scale(sub(u, delta), N)}, delta),
            "defect": ({N: scale(sub(u, scale(L, Q(1, 7))), N)}, scale(L, Q(1, 7))),
            "early": (early, {}),
        }
        A = sum(Q(m, m + 1) for m in range(1, H + 1))
        W = add(*(scale(tail(H, m), Q(1, m + 1)) for m in interval))
        J0 = energy({m: tail(H, m) for m in interval})
        optimum = scale(W, 1 / (A + B))
        minimum = sub(J0, scale(square(W), 1 / (A + B)))
        for name, (h, defect) in families.items():
            actual_defect = sub(u, add(*(scale(a, Q(1, k)) for k, a in h.items())))
            check("reciprocal_moment_or_defect", actual_defect == defect)
            if name == "bands":
                total = add(*(sub(h.get(k, {}), base[k]) for k in range(2, N + 1)))
                reciprocal = add(*(scale(sub(h.get(k, {}), base[k]), Q(1, k))
                                   for k in range(2, N + 1)))
                check("two_band_mean", scale(sub(total, reciprocal), Q(1, 2)) == L)
            residues = {}
            for m in range(1, 2 * N + 1):
                R = sub(L, add(*(scale(sub(h.get(k, {}), base[k]), Q(m % k, k))
                                 for k in range(2, N + 1))))
                C = floor_correction(h, m)
                returned = add(scale(defect, m), tail(N, m), scale(tail(H, m), -1), C)
                check("complete_return", R == returned)
                if m <= H:
                    check("head_with_defect", R == scale(defect, m))
                if m in interval:
                    frac = add(*(scale(sub(logv(H), logv(k)), Q(mu(k) * (m % k), k))
                                 for k in range(1, H + 1)))
                    e = add(psi(m), scale(ONE, -m), logv(H), frac)
                    check("delta_decomposition", tail(H, m) == add(scale(delta, m), e))
                    if name != "early":
                        check("uncorrected_window", R == sub(scale(defect, m), tail(H, m)))
                    if name == "retuned":
                        check("retuned_window", R == scale(e, -1))
                if m <= H or m in interval:
                    residues[m] = R
            if name != "early":
                actual = energy(residues)
                quadratic = add(scale(square(defect), A + B), scale(mul(defect, W), -2), J0)
                completed = add(scale(square(sub(defect, optimum)), A + B), minimum)
                check("soft_head_exact_quadratic", actual == quadratic == completed)
            if name == "retuned":
                check("retuned_head_cost", energy({m: residues[m] for m in range(1, H + 1)})
                      == scale(square(delta), A))
        optimal_h = {N: scale(sub(u, optimum), N)}
        optimized = {m: sub(L, add(*(scale(sub(optimal_h.get(k, {}), base[k]), Q(m % k, k))
                                     for k in range(2, N + 1))))
                     for m in list(range(1, H + 1)) + list(interval)}
        check("attained_finite_projection", energy(optimized) == minimum)


def scalar_residual(c, m):
    return 1 - sum(value * Q(m % k, k) for k, value in c.items())


def sqrt_sum_ge(s, a, b):
    assert a >= 0 and b >= 0
    d = s * s - a - b
    return d <= 0 or d * d <= 4 * a * b


for N in range(2, 25):
    patterns = [
        {k: Q(0) for k in range(2, N + 1)},
        {k: Q((-1) ** k, k) for k in range(2, N + 1)},
        {k: Q(3 if k == 2 else 0) for k in range(2, N + 1)},
        {k: Q(1) for k in range(2, N + 1)},
        {k: Q(-mu(k)) for k in range(2, N + 1)},
    ]
    for c in patterns:
        V = sum(c[k] * c[l] * Q(gcd(k, l) ** 2 - 1, 12 * k * l)
                for k in c for l in c)
        jordan = Q(0)
        for d in range(2, N + 1):
            J2 = Q(d * d)
            for p, _ in factors(d):
                J2 *= 1 - Q(1, p * p)
            qd = sum(c[k] / k for k in c if k % d == 0)
            jordan += J2 * qd * qd
        check("full_covariance_Jordan", 12 * V == jordan and V >= 0)
        for H in (2, 3, 4, 8, 16, 32, 48):
            S = [k for k in range(2, H + 1) if mu(k)]
            sh = len(S)
            direction = sum(mu(k) * c.get(k, 0) for k in S)
            a = {1: sh, H + 1: 0}
            for d in range(2, H + 1):
                a[d] = sum(mu(k) * mu(k // d) for k in S if k % d == 0)
            b = {m: a[m] - a[m + 1] for m in range(1, H + 1)}
            residual = {m: scalar_residual(c, m) for m in range(1, H + 1)}
            EH = sum(r * r / (m * (m + 1)) for m, r in residual.items())
            BH = sum(m * (m + 1) * b[m] ** 2 for m in b)
            combined = sum(b[m] * residual[m] for m in b)
            check("DM_combined_identity", sh + direction == combined)
            check("DM_dual_norm", BH <= 5 * H ** 3)
            check("DM_directional_bound", direction ** 2 <= 75 * H * V)
            check("DM_residual_Cauchy", combined ** 2 <= BH * EH)
            check("DM_master", sqrt_sum_ge(sh, 75 * H * V, 5 * H ** 3 * EH))
            if H >= 8 and EH <= Q(1, 320 * H):
                check("DM_small_error", V >= Q(H, 1200))
            if H >= 8 and H >= 4800 * V:
                check("DM_location", EH >= Q(1, 80 * H))

for beta in (Q(1, 2), Q(9, 16), Q(3, 4), Q(7, 8)):
    gate = 1 / (2 - beta)
    for j in range(1, 11):
        theta = gate * Q(j, 11)
        for epsilon in (Q(1, 10), Q(1, 100)):
            step = (1 - beta) / 2
            while (1 - beta - step) / ((2 - beta - step) * theta) <= 1 - beta:
                step /= 2
            b = beta + step
            p = 1 - 2 * theta * (1 - beta) - epsilon
            exponents = ((1 - p) / (2 * theta), (1 - b) / ((2 - b) * theta),
                         1 / theta - 1)
            check("strict_exponent_gate", beta < b < 1 and min(*exponents, Q(1)) > 1 - beta)
    check("boundary_not_strict", (1 - beta) / ((2 - beta) * gate) == 1 - beta)

result = {
    "status": "PASS_EXACT",
    "N_values": 15,
    "head_configurations": cases,
    "FT_coefficient_vectors": 5 * cases,
    "DM_vectors": 23 * 5,
    "counts": dict(counts),
    "total_checks": sum(counts.values()),
    "negative_controls": {
        "N12_H2_moment_defect": "d=L/7 gives r(1)=1/7, not zero",
        "N12_H2_early_correction": "h(3)=log(2), compensated at 12, changes L*r(3) by log(2)",
    },
    "scope": "finite exact identities and rational inequalities; no infinite theorem certified",
    "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    "registration_sha256": hashlib.sha256(Path(__file__).with_name("registration.md").read_bytes()).hexdigest(),
}
print(json.dumps(result, indent=2))
```

</details>

<details>
<summary>Proof-led retuning preregistration: retuning-registration.md</summary>

```text
# Proof-Led Retuning Follow-Up

Registered after the primary 76,762-check run, before this follow-up.

For N=6,12,...,90 and the same 99 head choices, independently test the
two-band correction with moment defect d=delta(H). Preserve periodic mean
one by changing BOTH scalar targets to u-d and v-d, not u alone.
Check the reciprocal moment, total coefficient sum, periodic mean, head
slope and pre-correction-window identity using exact log vectors.

Negative control: changing u alone while keeping v gives periodic mean
1+d/(2L), not one. No infinite approximation claim follows from retuning.

Proof-led follow-up registered before its added check: verify for every
same-domain head that u-d=S(N)-1=-delta(N), independent of H. The first
3,747-check execution already passed; the new 99 checks extend, not replace,
its registered domain.
```

</details>

<details>
<summary>Independent retuning program: verify_retuning.py</summary>

```python
"""Exact finite audit of the two-target soft-head correction."""

from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import hashlib
import json


def plus(*items):
    out = {}
    for item in items:
        for k, v in item.items():
            out[k] = out.get(k, Q(0)) + v
    return {k: v for k, v in out.items() if v}


def times(a, q):
    return {k: v * q for k, v in a.items() if v * q}


@lru_cache(None)
def factor(n):
    out = {}
    p = 2
    while p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p += 1
    return out


def mu(n):
    f = factor(n)
    return 0 if any(e > 1 for e in f.values()) else (-1) ** len(f)


def logratio(a, b):
    return plus(factor(a), times(factor(b), -1))


counts = Counter()
for N in range(6, 91, 6):
    K = N // 6
    for H in range(1, min(8, (N + 3) // 4 - 1) + 1):
        L = logratio(N, H)
        base = {k: times(logratio(N, max(H, k)), mu(k)) for k in range(1, N + 1)}
        u = plus(*(times(v, Q(1, k)) for k, v in base.items()))
        v = plus(times(L, 2), *base.values())
        d = plus({0: Q(1)}, *(times(logratio(H, k), Q(-mu(k), k)) for k in range(1, H + 1)))
        endpoint_moment = plus({0: Q(-1)}, *(times(logratio(N, k), Q(mu(k), k))
                                             for k in range(1, N + 1)))
        assert plus(u, times(d, -1)) == endpoint_moment
        counts['head_independent_moment'] += 1
        s1 = sum(Q(1, k) for k in range(3 * K + 1, 4 * K + 1))
        s2 = sum(Q(1, k) for k in range(5 * K + 1, 6 * K + 1))
        for correct_v in (True, False):
            up = plus(u, times(d, -1))
            vp = plus(v, times(d, -1)) if correct_v else v
            a = times(plus(up, times(vp, -s2 / K)), 1 / (s1 - s2))
            z = times(plus(times(vp, s1 / K), times(up, -1)), 1 / (s1 - s2))
            h = {**{k: a for k in range(3 * K + 1, 4 * K + 1)},
                 **{k: z for k in range(5 * K + 1, 6 * K + 1)}}
            assert plus(*(times(value, Q(1, k)) for k, value in h.items())) == up
            assert plus(*h.values()) == vp
            counts['two_targets'] += 2
            numerator = {k: plus(h.get(k, {}), times(base[k], -1)) for k in range(2, N + 1)}
            mean = plus(*(times(value, Q(k - 1, 2 * k)) for k, value in numerator.items()))
            expected = L if correct_v else plus(L, times(d, Q(1, 2)))
            assert mean == expected
            counts['mean_or_negative_control'] += 1
            if not correct_v:
                continue
            for m in range(1, N // 2 + 1):
                R = plus(L, *(times(value, Q(-(m % k), k)) for k, value in numerator.items()))
                U = plus(*(times(logratio(H, k), mu(k) * (m // k)) for k in range(H + 1, m + 1)))
                assert R == plus(times(d, m), times(U, -1))
                counts['retuned_actual_residue'] += 1
                if m <= H:
                    assert R == times(d, m)
                    counts['head_slope'] += 1

print(json.dumps({
    'status': 'PASS_EXACT', 'counts': dict(counts), 'total_checks': sum(counts.values()),
    'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'registration_sha256': hashlib.sha256(Path(__file__).with_name('retuning-registration.md').read_bytes()).hexdigest(),
}, indent=2))
```

</details>

### Exact Execution Results

Primary final stdout:

```json
{
  "status": "PASS_EXACT",
  "N_values": 15,
  "head_configurations": 99,
  "FT_coefficient_vectors": 495,
  "DM_vectors": 115,
  "counts": {
    "window_signal": 15,
    "window_weight": 15,
    "reciprocal_moment_or_defect": 495,
    "complete_return": 54720,
    "head_with_defect": 2085,
    "delta_decomposition": 7205,
    "uncorrected_window": 5764,
    "soft_head_exact_quadratic": 396,
    "two_band_mean": 99,
    "retuned_window": 1441,
    "retuned_head_cost": 99,
    "attained_finite_projection": 99,
    "full_covariance_Jordan": 115,
    "DM_combined_identity": 805,
    "DM_dual_norm": 805,
    "DM_directional_bound": 805,
    "DM_residual_Cauchy": 805,
    "DM_master": 805,
    "DM_location": 92,
    "DM_small_error": 13,
    "strict_exponent_gate": 80,
    "boundary_not_strict": 4
  },
  "total_checks": 76762,
  "negative_controls": {
    "N12_H2_moment_defect": "d=L/7 gives r(1)=1/7, not zero",
    "N12_H2_early_correction": "h(3)=log(2), compensated at 12, changes L*r(3) by log(2)"
  },
  "scope": "finite exact identities and rational inequalities; no infinite theorem certified",
  "script_sha256": "76db3ee759e1b8932f792821b6d883e1d7ab1f1cab93cb79275ce9d5b35441d0",
  "registration_sha256": "170d81449d5b19e6736039b87325153eb137242f1a317113336a722370437446"
}
```

Retuning final stdout:

```json
{
  "status": "PASS_EXACT",
  "counts": {
    "head_independent_moment": 99,
    "two_targets": 396,
    "mean_or_negative_control": 198,
    "retuned_actual_residue": 2736,
    "head_slope": 417
  },
  "total_checks": 3846,
  "script_sha256": "05da309a6d028f934eb7fd253aa1604cf06b9ae7e6c0901d46859ecd7bb6d5dd",
  "registration_sha256": "208829f800b2878c52ef3258e71dc12e00ed9dddc2471b68bd6fb009d31b078a"
}
```

## Verified Publication Receipt - 20261112-referee-1/FT

**EXECUTION_COMPLETED / PUBLISHED / IMMUTABLE_READBACK_VERIFIED.** Verified at 2026-11-12 09:41:26 UTC (04:41:26 EST, America/New_York). This final receipt supersedes the checkpoint's historical IN_PROGRESS and the synthesis's prepublication READBACK_PENDING, without rewriting either record.

Substantive publication: [commit `d03afb0c4cb8502b5c5e410642bf706199c06ba0`](https://github.com/OVVO-Financial/RH_Lean/commit/d03afb0c4cb8502b5c5e410642bf706199c06ba0), report blob `4126b3c91e02bf3bc7fd72f9393692f83f39cf96`. The entire 66,240-character report was fetched using that immutable commit and matched the intended content exactly. Commit inspection confirmed exactly one changed file, `research/agent_reports/2026-11-12/50-adversarial-referee.md`, 883 added lines and zero deleted lines. The prior checkpoint and its evidence are preserved.

The verified substantive report contains all A-O sections, full source/claim provenance, exact independent programs and registrations, 76,762 primary plus 3,846 retuning assertions (80,608 total; all PASS), scoped FT/DM paper acceptance, SH1-SH3 self-audit with independent review pending, and precise unpaid consumers. Python syntax checks passed; no local Lean execution occurred. Completed research/publication does not mean the canonical objective is solved: NO_NEW_GLOBAL_GAIN; NO_NEW_ACCEPTED_ROUTE; VERIFIED_ETA=NONE; RH=OPEN.

Only the owned daily report on agent-reports was written remotely. No source, policy, other report, PR, workflow, merge, schedule or agent launch was changed. The next-run consumed handoff watermark is intake `9a52ef037b48ff003cb063865be6e53fb7f79273`, with a final untruncated tree reconciliation at `2b3ad783f50ceabab11dc8633e2a95d830be87a2` showing only this checkpoint as a difference. This receipt records the already verified substantive commit, not an unverified future commit of the receipt itself.

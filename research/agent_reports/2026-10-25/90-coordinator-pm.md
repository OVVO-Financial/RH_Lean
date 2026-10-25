# RH_Lean Coordinator report - 2026-10-25 PM

**Status:** COMPLETED
**Run:** 2026-10-25T19:09:01-04:00 scheduled invocation
**Revision history:** an early `IN_PROGRESS` checkpoint was published by commits `fb16b6db8344b1e3a483d3f0d0c13d4d68608ada` and `8a1f366ceaeaba4f31505e602b1377867d2bc0a4`; immediate readback showed byte-identical blob `58a84e2b753f49f575826cdd3c4e83aaf026b7d7` at both authorized paths. This synthesis replaces that checkpoint byte-for-byte.
**Result classes:** `PAPER_PROOF_NEEDS_REVIEW`, `PROVED_IN_LEAN_PR_GREEN_UNMERGED`, `FINITE_COMPUTATION`, `REFUTED`, `CONDITIONAL`, `NO_NEW_GLOBAL_QUANTITATIVE_BOUND`

## A. What changed mathematically?

### Claim `20261025-coordinator-1`: every excess CORR4 remainder bill forces a quantitative finite-A endpoint excursion

On the literal PR #1021 carrier, for R >= 56, put

```text
X_R = R^2 - 1
C_R = M(R-1) - M(X_R)
E_R = sum_(q odd prime, q^2<R) M(floor(X_R/q^2))^2
U_R = sum_(q odd prime, q^2<R) M(floor(X_R/q^2))/q
B_R = C_R - U_R.
```

Today's green unmerged PR #1023 proves the unconditional frame

```text
|U_R|^2 <= b_7 E_R,
b_7 = 1565172113 / 7214407200.
```

Let `a=9/4`. Then, for every R,

```text
|B_R|^2 - a E_R
  <= lambda_7 |C_R|^2,

lambda_7 = a/(a-b_7)
         = 16232416200 / 14667244087
         = 1.106712079223339...
```

Equivalently,

```text
|C_R|^2 >= kappa_7 (|B_R|^2-aE_R),
kappa_7 = (a-b_7)/a
        = 14667244087 / 16232416200
        = 0.903577379133489...
```

whenever the right side is positive.

This is not a new all-root upper bound. It is a sharp inverse theorem using only the unsigned daughter frame. It proves that a large complete physical-remainder bill cannot be created by the daughter synthesis alone: it must contain a comparably large square-endpoint Mertens excursion.

For an actual `LowerMertensCriticalEnvelope R K`, the y=R-1 instance gives

```text
|M(R-1)-1| <= sqrt(KR).
```

If K>0 and

```text
H_R = (|B_R|^2-aE_R)/(R^2 K) > 0,
A_R = (M(X_R)-1)^2/(R^2 K),
```

then

```text
sqrt(A_R) >= max(0, sqrt(kappa_7 H_R) - 1/sqrt(R)).
```

Thus every counterexample to a proposed uniform relaxed-remainder constant supplies an explicit finite-A endpoint excursion. At the Census fixture R=5561, `H_R=0.14418310472084428...`, and the inverse theorem alone forces `A_R>=0.1207800132...`.

**Classification:** `PAPER_PROOF_NEEDS_REVIEW / INVERSE STRUCTURAL RESTRICTION`. It neither proves finite A nor the relaxed remainder. Its strategic content is negative and decisive: additional refinements of the unsigned reciprocal-prime frame cannot by themselves pay the open CORR4 theorem.

## B. Current proof objective

Final authority refresh:

- `main@8d3a06d3748282e7e7e5cd273efdd00560cdee15`;
- `AGENTS.md` blob `fe049350c3d6a20096322a2c09c3993c2037022b`;
- `CURRENT_PROOF_CONTRACT.md` blob `93314aebfcc326b27aa5835bd33a23a76923016b`;
- portfolio blob `278cf50c25e30227021f34371932b1edd5e164bd`;
- overlap/imported-7/8 audit blob `c0002af0c26e0e2dff25758a4bc14c38a76f0822`;
- dynamic protocol blob `ff674b509cbdb67aebf635e0d9d5388c08967f12`;
- external handoff index blob `038018145c0fddb2f6306c0712373adf9cd1ea52`.

The exact public theorem remains `VFCanonicalSquareVonKochStatement`:

```text
exists C >= 0, forall R >= 2,
  |pi(R^2)-vfMidFinishedMass(R)-sqrt(2)| <= C R log R.
```

It remains OPEN. Merged #987 supplies the unconditional imported 7/8 Mertens baseline, not RH and not a native exponent improvement. Literal universal one-block capture remains `REFUTED` at R=549.

The canonical endpoint bound, complete original-source signed payment, finite A/C, CORR4, a subcritical MU-LIFT input, the full Nyman norm criterion and RH all remain unproved.

## C. Competing mechanism portfolio

### 1. CORR4 endpoint/daughter coherence - REVISE AND CONTINUE

**Concept:** use the exact complete physical remainder and low-q^2 daughters, but seek signed first-owner information beyond the unsigned frame.

**Independent input needed:** an all-root sign-preserving restriction on the complete first-owner Gram, or a genuine arithmetic theorem showing that endpoint/daughter anti-alignment cannot approach the sharp abstract extremizer on large endpoint excursions.

**Target implication:** `LowOwnerPhysicalRelaxedRemainderBound C` on PR #1021 implies actual CORR4 and RH through its green conditional consumer.

**First missing step:** pay `|B_R|^2-(9/4)E_R` by `O(R^2K)` without first assuming a finite-A endpoint bound.

**Support:** #1021 exact carrier and green conditional wiring; #1023's stronger frame; Census exact decomposition through R=6000.

**Obstruction:** claim `20261025-coordinator-1` proves that frame-only arguments rehouse the finite-A excursion. Census also refutes the local sign necessity at R=57 and shows endpoint dominance on every observed H_R>1/10 fixture.

**Decisive experiment:** compute the ratio
```text
(|B_R|^2-aE_R)/|C_R|^2
```
on held-out endpoint-excursion runs and compare it with the sharp frame ceiling `lambda_7`. A family approaching the ceiling rejects every proof using only the frame and scalar Young inequalities.

### 2. VF-LOW/SAT through JOH chronological displacement - CONTINUE

**Concept:** use the actual prime/floor-Li event stream, retaining the first chronological moment that yesterday's Owner proved is lost by the #915 zeroth-moment boundary.

**Independent input needed:** a genuine least-prime ancestry restriction on nonlocal prime/model barycentre separation that survives opposite-sign blocks and combines with the anchor and weighted block defects.

**Target implication:** an eventual JOH weighted composite-removal sign or a source-native first-lower-wall exclusion yields the prime-side RH criterion.

**First missing step:** bound the boundary-padded displacement without replacing genuine primes by count/parity/density candidates.

**Support:** `20261024-owner-1` exact crosswalk and `20261024-analytic-1` exact extremal countermodel.

**Obstruction:** zero count defect permits both signs at full natural block scale; actual blocks r=4 and r=7 already have opposite displacement signs. A count-only bridge is refuted.

**Decisive experiment:** certified dyadic scans restricted to zero-defect blocks, recording signed displacement, least-prime owner classes and cumulative barycentre compensation. The test must falsify a stated nonlocal ancestry law, not merely extend a range.

### 3. OAI-NNS nonresonant radical-period attack - CONTINUE CAUTIOUSLY

**Concept:** PR #1022 isolates exact nonprincipal zero modes on the original low-Gaussian numerator and proposes a high-J source-local Poisson factor `Z^(-1/64)` after radical conductor shortening.

**Independent input needed:** a complete exponent ledger covering the genuine radical-period lift, all outer source counts, low-J and unit-trivial/resonant rows, Gaussian tails, principal corrections, compensation subsets, and full signed NNS cross energy.

**Target implication:** a strict complete-source power improvement beyond imported 7/8 would improve the Mertens boundary; a local high-J saving alone does not.

**First missing step:** prove source admission and a positive net power after every complementary sector is restored.

**Support:** exact local zero-mode/radical-period declarations on prior green #1022 heads and the source-local paper calculation.

**Obstruction:** the inverse-row resonance no-go remains live; nonresonant cancellation covers neither resonant rows nor the complete detector. The latest head is still under CI.

**Decisive experiment:** tabulate every Z exponent and multiplicity on the smallest complete admitted source family. If the claimed 1/64 gain is consumed by outer costs or an uncovered sector remains at the 7/8 baseline, reject this implementation of the mechanism.

NYMAN remains the independent reserve. MU-LIFT remains eligible, but no new source-level recurrence with r<k was established today. Literal BLOCK stays retired.

## D. Conceptual research performed

The proof of claim `20261025-coordinator-1` is a one-line Hilbert-space optimization, but its route consequence is substantive.

From the triangle inequality,

```text
|C_R-U_R|^2 <= |C_R|^2 + 2|C_R||U_R| + |U_R|^2.
```

Since 0<b_7<a, weighted Young gives

```text
2|C_R||U_R|
 <= [b_7/(a-b_7)] |C_R|^2
  + [(a-b_7)/b_7] |U_R|^2.
```

Therefore

```text
|B_R|^2-aE_R
 <= [a/(a-b_7)]|C_R|^2
  + [a/b_7]|U_R|^2-aE_R
 <= [a/(a-b_7)]|C_R|^2.
```

The constant is sharp if the only available information is `|U|^2<=bE`: equality occurs in the abstract scalar model when U is antiparallel to C, the frame saturates, and `|U|/|C|=b/(a-b)`. This does not assert that genuine Mertens daughters realize equality; it proves that the unsigned frame contains no further information with which to rule it out.

For the finite-A consequence, use
```text
M(X_R)-1 = M(R-1)-1-C_R
```
and the reverse triangle inequality together with the historical envelope. Division by `R sqrt(K)` gives the displayed lower bound.

### No-circularity review

- The frame is unconditional and independent of RH.
- The new theorem is a necessary-condition/inverse result, not an upper estimate.
- It does not rename `M(X_R)`, `C_R` or the complete remainder as a solved quantity.
- A uniform bound on `C_R^2/(R^2K)` would essentially return to finite A/C and must not be advertised as a new CORR4 payment.
- PR #1021 already contains the analogous forward Young comparison with the older `211/900` frame. The new content is the stronger #1023 constant, the sharp inverse direction, and the explicit finite-A excursion forced by failure.
- No favorable sign, independence, density transfer or omitted cross term is assumed.

## E. Specialist findings

Today's committed reports:

- **Wheel**, blob `414415d53bfedd14ae9b72ed3cc55f65c1477a21`, claim `20261025-wheel-1`: unconditional paper bound `9769/44100` from excluding composite owner 9; conditional CORR coefficient improvement only.
- **Census**, blob `25dbde73e5b15bc8e028c69bb05809d2439da8af`, claim `20261025-census-1`: exact finite decomposition on 56<=R<=6000; large observed bills are endpoint excursions with daughter echo; `c_R>0 => C_RU_R<0` is refuted at R=57.
- **Referee**, blob `1cbc2e20d211523c926b9bb6a114e959ebbfded5`, claim `20261025-referee-1`: strengthens Wheel to the parametric finite-tail family and K=7 constant `b_7); accepts #1021/#1022 only at their exact conditional/local scope.
- **Lean**, blob `a0eb1172c932fdfea9633b7e431a72a53b19e721`: formalizes the K=7 frame on review-ready PR #1023, exact head `44fbcf3f2dcab39c849f8a52cec4202929a734ad`.

Today's Owner and Analytic reports are unavailable and remain `TODAY=PENDING`. Their 2026-10-24 blobs `3d5a94fdfc2da9b4918c9f9643582060f2105c92` and `c90beb4c1b5e2ad64e31ec8bc1dda6d36aede6d7` are explicitly dated carry-forward evidence. All other October 24 reports were read. No external handoff is newer than October 18.

Newly established today: the stronger prime frame, its exact Lean implementation on a green unmerged head, and finite endpoint/daughter diagnostics. Reproduced/accepted: the literal carrier identities and conditional CORR wiring. Refuted: a local sign necessity and any claim that the unsigned frame alone pays the remainder. Unresolved: every global quantitative input.

## F. Mathematical bottlenecks

- **CORR4:** a signed all-root theorem on the complete first-owner Gram that uses information not contained in the scalar frame or finite-A endpoint amplitude.
- **VF-LOW/Joh:** a nonlocal genuine-prime ancestry restriction on chronological barycentres, with anchor and weighted defect terms restored.
- **OAI-NNS:** a complete source-admission and exponent ledger with resonant, principal, low-J, tail, multiplicity and cross-energy costs.
- **FINITE-AC/MU-LIFT:** an independently proved uniform subcritical rate, not an envelope ratio defined from the target.
- **NYMAN:** full-basis density/decay, not finite rational certificates.

## G. Strategy decisions

1. Keep CORR4 as the recursive lead, but stop allocating work to successively smaller reciprocal-prime constants unless they alter a proved terminal threshold. The frame is now adequate; the signed remainder is not.
2. Promote claim `20261025-coordinator-1` as the falsification lens for CORR4: every proposed proof must identify what forbids the forced finite-A excursion or what signed information beats the sharp frame abstraction.
3. Continue VF-LOW/SAT/JOH as the prime-side mechanism. Its first-moment carrier is genuinely different from CORR4 and from #915's quadratic source.
4. Continue OAI-NNS as the analytic alternative only while PR #1022 can exhibit a positive complete exponent after all complementary costs. Local zero-mode cancellation is structural progress, not yet an exponent gain.
5. Do not revive universal BLOCK. Keep NYMAN as reserve and MU-LIFT open without manufacturing a recurrence hypothesis.

## H. Next specialist assignments

- **Owner Payment:** on the exact Owner crosswalk, state and test one dyadic least-prime ancestry law for the boundary-padded JOH displacement. It must include unequal-count correction, anchor and weighted block defects. Falsifier: the first zero-defect dyadic window whose genuine signed barycentre violates the proposed constant.
- **Analytic Type II:** produce a complete #1022 exponent table from the literal source. State every high-J, low-J, resonant, principal, Gaussian, outer-count and NNS-cross exponent. Valid result: a proved positive delta beyond 7/8 after the maximum sector cost; falsifier: one unavoidable sector with nonpositive net gain.
- **Finite Wheel:** seek a signed incidence restriction on the complete CORR4 first-owner Gram specifically on endpoint-excursion roots. Do not refine the reciprocal frame again. Valid result: an all-root inequality strictly stronger than claim `20261025-coordinator-1`; falsifier: an explicit legal incidence family saturating the abstract antiparallel configuration.
- **Prime Census:** preregister held-out roots above 6000 and measure `H_R`, finite-A `A_R`, and `H_R/A_R`, retaining exact rationals. Test proximity to `lambda_7` and report the first violation of any proposed signed-incidence restriction.
- **Adversarial Referee:** independently verify the sharpness, K>0 handling and finite-A corollary of `20261025-coordinator-1`; decide whether any current CORR theorem already proves the reverse implication. Separately audit #1022 only at its latest head and complete-source exponent.
- **Lean Verification:** after referee acceptance and human disposition of #1021/#1023, formalize the abstract frame-to-endpoint inverse inequality and its actual carrier specialization on an authorized branch. Keep the open remainder premise explicit. Do not stack a new claim on stale PR heads merely to obtain green CI.

These are asynchronous report handoffs, not claims that another execution was launched.

## I. Lean and PR status

Final live audit:

- **#1021:** OPEN, non-draft, unmerged, head `58be641ddb0c6cd003e4b61f760113ab254fbf11`. All 13 observed exact-head workflows are successful, including dedicated run `40162570279` and imported 7/8 run `40162570315`. Exact identities and conditional consumers are green; `LowOwnerPhysicalRelaxedRemainderBound` remains an unproved premise.
- **#1022:** OPEN, DRAFT, unmerged, latest head `03f756a4e4954d4df388f26105785cc30e438a16`. Proof inventory, policy, documentation and export checks had succeeded; the dedicated OAI certificate and several regressions were still in progress at final refresh. Earlier green heads do not certify this latest head.
- **#1023:** OPEN, review-ready, unmerged, head `44fbcf3f2dcab39c849f8a52cec4202929a734ad`. All 11 observed workflows are successful; dedicated run `40181443709` passed warning-fatal Lean and the standard `[propext, Classical.choice, Quot.sound]` axiom audit.
- **#1019:** merged at `2f4fc830150242b4cc0f9973f1c1b6c8be809fc3`; exact birth/transport structure only.
- Main remains `8d3a06d3748282e7e7e5cd273efdd00560cdee15`.

No PR was modified, reviewed, merged or auto-merged by this Coordinator execution.

## J. Next-run resume capsule

Resume from main `8d3a06d3748282e7e7e5cd273efdd00560cdee15`, claim `20261025-coordinator-1`, today's four specialist blobs, and the three live PR heads above.

Surviving ideas:

- CORR4 needs signed first-owner information beyond the sharp unsigned frame.
- VF-LOW/Joh needs genuine nonlocal chronological ancestry, not block counts.
- OAI-NNS needs a complete positive exponent ledger, not only a local high-J Poisson factor.

Decisive blocker: no independently proved all-scale source theorem yet controls any complete carrier at RH strength.

Highest-value next reasoning task: determine whether genuine CORR4 incidence forbids near-saturation of the antiparallel frame extremizer on finite-A endpoint excursions. A negative answer would collapse the present CORR4 attack into the stronger finite-A route and justify reallocating effort to VF-LOW/Joh or a complete OAI exponent gain.

Canonical VF and RH remain OPEN.

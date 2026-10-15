# RH_Lean Coordinator synthesis — 2026-10-15

**Status:** COMPLETED  
**Agent:** RH | Research Coordinator / Proof Architect  
**Run ID:** 2026-10-15T19:30:00-04:00, user-directed execution  
**Completed:** 2026-10-15T19:33:29-04:00  
**Reporting rule:** one execution and one synthesis, mirrored byte-for-byte at `00-coordinator-am.md` and `90-coordinator-pm.md`  
**Early checkpoint:** published and read back byte-identical before the final synthesis  
**Live main at final refresh:** `3d8687872160260710b0b0819132e02864844543`

## A. What changed mathematically?

The raw greatest-prime-tag ledger has a forced macroscopic cancellation that can be proved unconditionally, but only at Prime Number Theorem scale.

Let
[
A_R=sum_{substack{q {m prime}\R^2/3<q<R^2}}G_R(q),
qquad
B_R=L_R-A_R,
]
with the exact raw-seat definitions from the current contract. Then:

- **Claim `20261015-coordinator-1` / `PAPER_PROOF`:**
  [
  A_R=-left(rac13+o(1)ight)rac{R^2}{log R}.
  ]
- **Claim `20261015-coordinator-2` / `PAPER_PROOF`:**
  [
  B_R=+left(rac13+o(1)ight)rac{R^2}{log R}.
  ]

Thus the large negative prime-tag tail and the complete complementary factor-depth ledger cancel at leading order for arithmetic reasons, not because of a fitted finite coincidence. This is the first independently justified coupling isolated in this run.

It does **not** prove the canonical bound. The remainder allowed by the two (o(1)) terms is vastly larger than (Rlog R). The result instead proves a sharp strategic no-go: any argument that takes absolute values of the upper tag sector before reassembling it with the complement necessarily incurs a loss of order (R^2/log R), so it cannot reach the target scale.

This result is carrier-specific to the raw greatest-prime-tag partition. The repository already contains analogous PNT-scale compensation on a different Mertens prime-update ledger; that is precedent for the mechanism, not a bridge between the carriers.

## B. Current proof objective and authority

The authoritative theorem remains
[
	exttt{VFCanonicalSquareVonKochStatement}:
quad exists Cge0 orall Rge2,quad
|D_{m can}(R)|le C Rlog R.
]

Final authority:

- `main` SHA: `3d8687872160260710b0b0819132e02864844543`.
- `AGENTS.md` blob: `cbc234051834f971929d82972ba6a157b2129d32`.
- `CURRENT_PROOF_CONTRACT.md` blob: `dc73babe5eb7b8f9fb83272a27cd2468dbdcb7f2`.
- Factor-depth brief blob: `1a5f94bb81aa7d50b7c118f823a14c9ec644f947`.
- Dynamic protocol blob: `61f7e4dd90200c2f3426fce1e96f9779f40238dc`.
- Amplification budget blob: `3beff1f789646d59237744379ff8e578bb1042a0`.
- Canonical theorem source blob: `43e160ac7ad51f7646771297f43a9b95395ce709`.
- All-real VF–Li (O(1)) source blob: `f7c1cf3890e99acc6629084574c0e38bc2f60959`.
- Compiled native PNT source blob: `f9383cee102d8f6cb72d82803890ec29118b4794`.

The exact coordinate relation is still (L_R=F_R-pi(R^2)+2), hence (D_{m can}(R)=2-sqrt2-L_R), at paper level for the displayed raw endpoint conventions. The raw partition and its square are identities, not estimates, and they are not silently transferred to the masked/clipped returned-cell carrier or the compressed #915 norm.

## C. Competing mechanism portfolio

### 1. FD-TRANSPORT / macroscopic tail renormalization — CONTINUE, REVISE

- **Concept:** split off the forced upper-tag sector (A_R), whose main term is now proved, and seek a coefficient-preserving factor-depth transition for the renormalized pair ((A_R,B_R)).
- **Independent input:** a genuine arithmetic recurrence or sign restriction on the complete complement, beyond PNT and beyond the exact identity (L_R=A_R+B_R).
- **Target implication:** an independently proved (|A_R+B_R|=O(Rlog R)) gives the canonical endpoint bound through the exact coordinate bridge.
- **First unproved step:** a source-native second-order coupling theorem with all low tags, squareful/depth-at-least-three mass, boundaries and weight defects present.
- **Support:** Claims `coordinator-1/-2`; accepted raw partition `20261015-census-1`; tail monotonicity `20261015-referee-2`; finite full-depth ledger.
- **Obstruction:** the leading compensation alone follows from PNT and allows an error much larger than the target. A theorem merely naming the remaining mismatch is target-equivalent.
- **Decisive experiment:** decompose (B_R) by exact factor-depth transitions and test a predeclared second-order residual on held-out endpoints; compare against the deterministic PNT macro mode.
- **Disposition:** continue as the leading VF mechanism, but reject separate absolute estimates of (A_R) and (B_R).

### 2. INV-CONFIGURATION / renormalized bad-mode obstruction — CONTINUE, LOWER PRIORITY

- **Concept:** assume the renormalized mismatch (A_R+B_R) is large and derive concentration in a named quotient band, depth transition, or boundary incidence pattern.
- **Independent input:** an arithmetic theorem that independently bounds that named configuration.
- **Target implication:** the configuration theorem plus its independent exclusion must bound the full mismatch, not an unrelated support count.
- **First unproved step:** formulate an observable that differs genuinely from the endpoint sum and survives all coefficients and boundary terms.
- **Support:** raw cap-four failure at (R=15,q=17), all-scale fixed-capacity deficiency, and upper-tail monotonicity delimit impossible simplistic configurations.
- **Obstruction:** defining the bad configuration as “large mismatch” is circular; fixed-capacity incidence has already failed.
- **Decisive experiment:** search for two endpoints with similar (A_R+B_R) but different proposed configuration counts, or vice versa. Failure to distinguish them rejects the observable.
- **Disposition:** continue only with a non-tautological configuration; do not enlarge wheels or revive fixed-capacity covering.

### 3. MU-LIFT / genuine signed finite-prefix amplification — CONTINUE

- **Concept:** use the merged genuine (Bmapsto B^k) signed lift and complete hyperbola identity to prove a whole-prefix amplitude estimate.
- **Independent input:** a genuine Möbius restriction controlling the complete signed rows or alternating families, not scalar prefix size.
- **Target implication:** on one eventually valid chain, (E(B^k)le G(B)E(B)^r) with fixed (r<k) and (log G(B)/log B	o0), plus full interval coverage, implies (MertensGrowthAtMost(1/2)).
- **First unproved step:** the uniform signed floor-kernel/amplitude inequality itself.
- **Support:** merged #951 and #954 exact identities; merged #949 bidirectional exponent/zero-boundary map.
- **Obstruction:** #954’s sparse artificial prefix refutes scalar-prefix-only proofs; separated absolute budgets destroy the needed cancellation.
- **Decisive experiment:** for fixed (k,r), certify complete-prefix maxima and the normalized loss on disjoint future ranges while preserving all signed components. Trends remain finite evidence.
- **Disposition:** continue as the genuinely independent analytic mechanism.

The portfolio has three distinct inputs: cross-depth arithmetic transport, an inverse forbidden configuration, and genuine Möbius signed amplification. None is counted as established quantitative progress.

## D. Conceptual research performed

For Claim `20261015-coordinator-1`, take a prime tag (q) with (R^2/3<q<R^2). Every odd prime owner satisfies (pge3), hence (pq>R^2). Therefore the semiprime descendant sum is exactly (X_R(q)=0), and
[
G_R(q)=-(1-w_{lfloorsqrt qfloor}).
]
Uniformly on this sector,
[
w_{lfloorsqrt qfloor}=O(1/log R),
]
so
[
A_R=-#{q {m prime}:R^2/3<q<R^2}
 +O!left(rac1{log R}#{q:R^2/3<q<R^2}ight).
]
The PNT at the two fixed-ratio endpoints gives
[
pi(R^2)-pi(R^2/3)
=left(rac13+o(1)ight)rac{R^2}{log R},
]
which proves Claim 1.

For Claim `20261015-coordinator-2`, compiled VF–Li (O(1)), the PNT, and (L_R=F_R-pi(R^2)+2) give
[
L_R=o(R^2/log R).
]
Since (B_R=L_R-A_R), Claim 2 follows.

**No-circularity review:** both claims are unconditional consequences of the raw definitions, PNT and the VF quadrature bridge. They neither imply nor assume an (O(Rlog R)) endpoint estimate. They establish only the leading macroscopic mode. Conversely, the canonical target would sharpen the final cancellation enormously, so calling that sharpened remainder “small” without new input would be `TARGET_EQUIVALENT`.

**Exact-carrier review:** (B_R) is the entire complement: lower prime tags plus squareful and squarefree depth-at-least-three mass. Claim 2 does not assert that (H_R) alone has the positive main term. No mask, clip, returned-cell admission, #915 normalization, NNS cross term or historical restoration is inferred from this raw theorem.

**Failure-mode consequence:** the upper sector alone has magnitude asymptotic to (R^2/(3log R)), while the target scale is (Rlog R). Their ratio is (R/(3log^2R)	oinfty). Triangle inequality at that partition therefore cannot close the target; cancellation must be preserved across the split.

## E. Specialist findings

Today’s published evidence at final refresh:

- **Owner Payment:** `TODAY=PENDING`; 2026-10-14 blob `4f39c1690ee4cee0a00d4ebd0d08323f06d6c75d` is dated carry-forward only.
- **Analytic Type II:** `TODAY=PENDING`; 2026-10-14 blob `3a6932d9c5e1474adf1f34374310c7b73eb71fc2` is dated carry-forward only.
- **Finite Wheel:** blob `6d451c35eef4021fcff78253bed609d193c249c1`. Claims `20261015-wheel-1/-2` prove finite-capacity deficiency on the qualified carriers; Claim 3 is a necessary conditional source alternative.
- **Prime Census:** blob `2e3c1cf95cd11669d57d2ce1f7216916736ff095`. Claim `census-1` is the accepted raw partition; cap four is refuted on that carrier; factor-depth compensation is finite evidence; full-range one-sign-change remains unproved.
- **Adversarial Referee:** blob `cf0db85f6b04c56527bc9a26a1b6741ae196435a`. It accepts the qualified deficiency claims, proves raw-tag monotonicity only for (qge R), and supplies the smallest raw cap-four counterexample (R=15,q=17).
- **Lean Verification:** blob `a11eddb6f78c927b8ec838426f94d72e63cda123`. Its then-current #948 `READY_FOR_HUMAN_REVIEW / NOT_MERGED` line is superseded by live GitHub state: #948 is merged.

All seven 2026-10-14 role reports were read, including byte-identical Coordinator blob `bf05965ed6adcac8ee9ae7d6066e047485baf945`. External inbox blob `c1d1aad9872d1760d2e4e34b30bbc0ed4fa3d33c` was consumed. `EXT-20261014-5` remains `PAPER_PROOF` at its exact original-denominator scope; it is not a general no-go for renormalized signed mechanisms.

## F. Mathematical bottlenecks

1. **Factor depth:** improve the proved leading compensation to a genuinely independent second-order bound while retaining the complete complement. The statement (|A_R+B_R|=O(Rlog R)) itself is the endpoint target in these coordinates.
2. **Inverse route:** identify a bad configuration that is neither the mismatch by definition nor an unrelated support count, then prove a separate restriction on it.
3. **MU-LIFT:** bound the genuine signed floor kernel over every (Ble X<B^k) with fixed subcritical amplitude exponent and subpower normalized loss.
4. **Source bridge:** raw seats, eligible ancestry and masked/clipped returned cells remain distinct. No raw asymptotic transfers to the original NNS carrier without an exact bridge.
5. **Quadratic integrity:** local negative pairs, tag sums and depth aggregates do not add after discarding cross terms, anchor/restoration or historical decompression.

## G. Strategy decisions

- **REJECT** pure once-only fixed-capacity Hall allocation as a complete route. Preserve its deficiency theorem as a reusable no-go.
- **REJECT** any proof that separately norms the upper prime-tag sector. Claim 1 proves the resulting loss is supertarget.
- **CONTINUE** factor-depth transport with the PNT macro mode explicitly removed and every residual term retained.
- **CONTINUE** MU-LIFT as the strongest independent analytic alternative. Judge (r<k) and normalized loss, not constant gain.
- **CONTINUE CAUTIOUSLY** the inverse route only after it names an independently bounded observable.
- **SUSPEND** formalization of the raw tag asymptotic until the exact raw tag definitions and referee-qualified theorem statement exist in source. The paper theorem is useful now; a speculative abstraction is not.

## H. Next specialist assignments

- **Owner Payment — `RAW-TAIL-COMPLEMENT-TRANSPORT-1`:** derive an exact coefficient-preserving recurrence for (B_R) under (Rmapsto R+1) or a factor-depth transition. Include lower tags, squareful/depth-at-least-three seats, weight changes and boundaries. Falsification: one missing seat, changed greatest-prime tag, or a remainder equal by definition to (L_R).

- **Analytic Type II — `MU-LIFT-SIGNED-ROW-1`:** attack the genuine whole-prefix inequality for a declared fixed (k,r), reporting (G,g), interval coverage and the arithmetic feature excluding the sparse control. Falsification: a coherent row/component of larger order, loss (rge k), or endpoint-only coverage.

- **Finite Wheel — `RENORMALIZED-INVERSE-OBSERVABLE-1`:** formulate one exact configuration forced by a large (A_R+B_R) after the macro tail is removed, and prove it differs from the endpoint sum. Falsification: two exact finite ledgers breaking either direction, or dependence only on the already-refuted fixed cap.

- **Prime Census — `MACRO-TAIL-HELDOUT-1`:** independently reconstruct (A_R), (B_R), and the ratios (A_Rlog R/R^2), (B_Rlog R/R^2) on new held-out roots. Compare the proved (-1/3,+1/3) macro prediction against candidate second-order observables. This is a discriminating experiment, not evidence for an (O(Rlog R)) theorem.

- **Adversarial Referee — `COORDINATOR-TAIL-AUDIT-1`:** audit Claims `coordinator-1/-2`, endpoint conventions, uniform weight estimate, PNT transfer and the assertion that absolute sectorization is impossible. Try to find prior identical raw-carrier work and issue ACCEPT/REVISE/REJECT. Reject any transfer to (H_R) alone or to returned cells.

- **Lean Verification — `TAIL-THEOREM-TRIAGE-1`:** first refresh merged #948–#954 and avoid duplicate work. If the Referee accepts an exact source statement and the raw tag carrier is introduced cleanly, assess a small exact “upper tags have no descendants” lemma plus a fixed-ratio PNT corollary. Otherwise report `NO_NEW_THEOREM_TO_FORMALIZE`; do not open a filler PR.

## I. Lean and PR status

At final refresh there were no open pull requests. PRs #948–#954 are merged:

- #948 merge `f493cc6ede5bb42f1559ab2cb85ea2ea7a5d0da0`.
- #949 merge `1434da1159fb33e16567dc5d07cb381d7868898a`.
- #950 merge `5a0cb83307f6f43ef6fa08d441362e384b8d4f1b`.
- #951 merge `df353c9d40c660cc247bd2fdb96c536c74b04fe3`.
- #952 merge `470c19702553079b6b64a7f8e1f87ef544b76efe`.
- #953 merge `4a857fdd2d1c5b298aaad3dcfe622f892fae3d92`.
- #954 merge `c0bf6261b5e78aa0ec03967a86691987842b80eb`.

For #954, verified proof head `a4b5578f12729b4caa36e9305aa30ccc098f4923` had all eleven attached workflows successful. Dedicated run `38769272005` passed the signed-lift compilation and 22 exact axiom lists, each contained in `[propext, Classical.choice, Quot.sound]`. Current main `3d868787...` is a later policy/contract update; the combined-status and PR-workflow queries returned no attached runs for that exact documentation head. This does not upgrade or weaken the exact proof-head evidence.

Formal baseline on main: the bidirectional Mertens exponent/rightmost-zero identification, finite amplitude coordinate, finite-prefix extension, higher-order signed lift and complete signed hyperbola identity are `PROVED_IN_LEAN`. None supplies the missing quantitative amplification estimate.

## J. Next-run resume capsule

Resume from:

- main `3d8687872160260710b0b0819132e02864844543`;
- authority blobs `cbc23405...` and `dc73babe...`;
- current-day Wheel/Census/Referee/Lean blobs `6d451c35...`, `2e3c1cf...`, `cf0db85f...`, `a11eddb6...`;
- Owner and Analytic still `TODAY=PENDING / YESTERDAY=CARRY_FORWARD`;
- new Claims `20261015-coordinator-1/-2`: upper raw tag tail (-rac13R^2/log R), complete complement (+rac13R^2/log R), both `PAPER_PROOF`;
- decisive no-go: never take absolute values before cross-sector reassembly;
- first VF task: derive a non-tautological second-order factor-depth transport for (B_R);
- first independent analytic task: genuine MU-LIFT signed-row control with fixed (r<k) and subpower normalized loss;
- formal state: no open PRs; #948–#954 merged; no new Lean theorem requested before Referee qualification.

Do not rerun the existing full-depth endpoints, enlarge fixed wheels, clone one historical tag, infer a theorem about (H_R) alone, or present the remaining (O(Rlog R)) mismatch as an independently paid lemma.

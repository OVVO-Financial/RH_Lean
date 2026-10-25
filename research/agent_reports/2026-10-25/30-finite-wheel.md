# RH_Lean agent daily report - 2026-10-25 / RH | Finite Wheel & Incidence

**Status:** COMPLETED  
**Invocation:** one scheduled run, 2026-10-25 00:09--00:14 America/New_York  
**Pinned main:** `8d3a06d3748282e7e7e5cd273efdd00560cdee15`  
**Primary route:** CORR4 / CORR-A low-q^2 recursive owner incidence  
**Result classes:** `PAPER_PROOF_NEEDS_REVIEW / NEW UNIFORM PRIME-INCIDENCE CONSTANT`, `FINITE_COMPUTATION`, `CONDITIONAL COEFFICIENT IMPROVEMENT`, `NO_NEW_GLOBAL_QUANTITATIVE_BOUND`

## A. Main result

### Claim `20261025-wheel-1`: excluding the impossible composite owner 9 sharpens the low-q^2 prime frame

Put
[
 b_*=rac1{3^2}+rac1{5^2}+rac1{7^2}+rac1{20}
     =rac{9769}{44100}=0.221519274376ldots .
]

For every natural cutoff (N),
[
 sum_{substack{qle N\q {m prime}, q
e2}}rac1{q^2}le b_*.
]

This is a genuinely arithmetic incidence restriction: after the possible prime owners (3,5,7), the next odd prime is at least (11), because the odd location (9) is composite and cannot be an owner. It improves the compiled two-term rational Basel budget
[
 rac{211}{900}=0.234444ldots
]
by
[
 rac{211}{900}-b_*=rac{19}{1470}=0.01292517ldots .
]

**Proof.** Split the odd-prime set into (qin{3,5,7}) and (qge11). Every odd (qge11) is uniquely (q=2k+3) with (kge4). For every such (k),
[
 rac1{(2k+3)^2}le
 rac1{4(k+1)(k+2)}
 =rac1{4(k+1)}-rac1{4(k+2)}.
]
The finite tail is bounded by its infinite telescope (1/20). Adding the exact (3,5,7) terms gives (b_*). The argument is finite for each (N); the infinite notation only denotes the uniform telescoping upper envelope.

This was checked against the existing theorem
`oddPrimeOwnerReciprocalSquareBudgetReal_le_twoTermBasel` in
`research/STABLE_FAR_PERRON_BASEL_FRAME_SHARPENING.lean`, main blob
`e86617a02d18071ee9e73edc004937484e1a0447` as referenced by the live tree/PR closure. The existing proof retains (3,5) exactly and telescopes from (7); it does not use the composite gap at (9). Repository searches for `9769/44100`, `77/324`, and an exclude-9 reciprocal-prime-square theorem found no equivalent declaration.

## B. Exact consequence for the genuine LOW daughter carrier

On main, the genuine recursive owner set is
[
 {cal Q}_{m low}(R)=
 {q: qle R-1, q {m odd prime}, q^2<R}
]
and its literal daughter cutoff is
[
 Y_q=leftlfloorrac{R^2-1}{q^2}ightfloor.
]
These are exactly
`canonicalRoughLowQ2Owners R` and `rawQ2ChildCutoff R q` in
`research/CANONICAL_ROUGH_Q2_TAIL_REDUCTION.lean`, blob
`ebca096e83009a7df514d00b6a2696be86a94c55`.

Applying the already-compiled generic reciprocal-square frame theorem to this subset gives the paper corollary
[
 |mathrm{CriticalSynthesis}_R(	au)|^2
 le b_* E_{m low}(R),
]
where
[
 E_{m low}(R)=sum_{qin{cal Q}_{m low}(R)}M(Y_q)^2
]
is the literal `canonicalRoughLowQ2DaughterEnergy R`. No daughter is cloned; every (q) occurs once, all owner amplitudes remain inside the synthesis, and all cross-owner terms remain inside its norm before Cauchy--Schwarz.

The parent carrier remains the exact
[
 C_{m rough}(R)=M(R-1)-M(R^2-1),
]
compiled as
`squareRootCanonicalRoughCorrelation_eq_mertens_pred_sub_endpoint`
in `RHLean/Analysis/SquareRootCanonicalRoughCovariance.lean`, blob
`8c125b69cc0fbee577d063bcfa606843152868f3`.

## C. Conditional coefficient gain on the live PR #1021 mechanism

Open draft PR #1021, head
`1193a4eedb242e32b226999a0a20caaf580c0a78`, retains the complete physical remainder (B_R) and proposes the still-open source estimate
[
 |B_R|^2lerac94 E_{m low}(R)+C R^2K_R.
]
Its exact Young ledger sends a frame coefficient (b) to parent coefficient
[
 A_{m corr}=4b+rac43cdotrac94=4b+3.
]
Substituting the new arithmetic budget gives
[
 A_{m corr,*}=4b_*+3
 =rac{42844}{11025}
 =3.8860770975ldots<4<rac{2592}{629}.
]
Thus claim `20261025-wheel-1` improves the PR's current
(886/225=3.937777ldots) deterministic coefficient without changing its physical carrier or omitting mixed terms.

For the PR's nearest-square factor (37/36) and one-percent historical-root Young factor (101/100), the complete rational recurrence coefficient becomes
[
 lambda_*=
 rac{101}{100}rac{42844}{11025}rac{37}{36}
 rac{9769}{44100}
 =
 rac{391023831383}{437582250000}
 =0.8936007605ldots<1.
]
This replaces the PR's current (0.9583226365ldots) coefficient based on (211/900), increasing the deterministic induction margin from about (4.17%) to about (10.64%).

Equivalently, under the elementary two-square AMP estimate, the CORR-4 physical-remainder corridor increases from (Ble7/4) to
[
 Ble 2-b_*=rac{78431}{44100}=1.7784807256ldots.
]
For the Coordinator's paper threshold (A_{m corr}<2592/629), the corresponding remainder coefficient may be any
[
 B<rac12rac{2592}{629}-b_*
 =rac{51008899}{27738900}
 =1.8388940802ldots.
]

**Logical status.** The reciprocal-prime bound and rational arithmetic are unconditional paper proofs. The parent coefficient improvement is conditional on PR #1021's named full physical-remainder inequality, which remains OPEN. This report does not prove that inequality, a new Mertens exponent, canonical VF, or RH. Inserting imported 7/8 without the missing source estimate is still only `BASELINE_REEXPRESSED`.

## D. Finite checks and falsifiers

An exact rational sieve gave the actual low-owner reciprocal-square masses:

| R | low owners | largest q | actual mass |
|---:|---:|---:|---:|
| 56 | 3 | 7 | 0.171519274376 |
| 317 | 6 | 17 | 0.189161104562 |
| 1027 | 10 | 31 | 0.196051190201 |
| 5561 | 20 | 73 | 0.199890870676 |
| 1,000,000 | 167 | 997 | 0.202120430249 |

All are below (b_*). These checks validate arithmetic and endpoint interpretation only; they do not establish the all-scale theorem, whose proof is above.

Decisive scope controls:

1. The low set is (q^2<R), not every (q<R). At (R=5561) it stops at (q=73).
2. Excluding (9) is legal only because the owner carrier consists of genuine primes. The same improvement is false for an arbitrary odd-index frame.
3. The result improves a forward frame. It supplies no inverse frame and no sign for the complete physical remainder.
4. The (9/4) remainder coefficient is an unproved source inequality, not a consequence of the new owner budget.
5. No term of the full parent/remainder decomposition is deleted; only the uniform norm of the prime-owner coefficient vector is sharpened.

## E. Authority, continuity, and novelty audit

Current authority at intake:

- `main@8d3a06d3748282e7e7e5cd273efdd00560cdee15`;
- `AGENTS.md` blob `fe049350c3d6a20096322a2c09c3993c2037022b`;
- `CURRENT_PROOF_CONTRACT.md` blob `93314aebfcc326b27aa5835bd33a23a76923016b`;
- portfolio blob `278cf50c25e30227021f34371932b1edd5e164bd`;
- overlap/7/8 audit blob `c0002af0c26e0e2dff25758a4bc14c38a76f0822`;
- dynamic protocol blob `ff674b509cbdb67aebf635e0d9d5388c08967f12`.

At intake all 2026-10-25 specialist reports were absent: `TODAY=PENDING`. The complete 2026-10-24 set was consumed as `YESTERDAY=CARRY_FORWARD`:

- Coordinator `30942030c85ea079c0faacf97f2360cb77aca179`, claim `20261024-coordinator-1`;
- Owner `3d5a94fdfc2da9b4918c9f9643582060f2105c92`, claim `20261024-owner-1`;
- Analytic `c90beb4c1b5e2ad64e31ec8bc1dda6d36aede6d7`, claim `20261024-analytic-1`;
- Wheel `d7b956ad3e9f6e27e86644b371f275818a7516fd`, claim `20261024-wheel-1`;
- Census `04e90ce7bc531cf06be8fe0418477f4627bd625e`, claim `20261024-census-1`;
- Referee `8400b8ee3b8e6b68d2fb16ff6ffef395bf5dcca7`, claim `20261024-referee-1`;
- Lean `844b0cc6e49471469e60d9aa362744743c613740`, then still `IN_PROGRESS / CI_PENDING`.

External handoffs blob `038018145c0fddb2f6306c0712373adf9cd1ea52` has no entry newer than 2026-10-18. Consumed `EXT-20261018-PNT-1/2` and retained them as secondary; they do not supply the CORR4 remainder estimate. Literal universal BLOCK remains `REFUTED` at (R=549).

The current canonical theorem `VFCanonicalSquareVonKochStatement`, complete-source signed payment, CORR4, finite A/C, MU-LIFT gain and RH remain OPEN.

## F. Live GitHub/CI audit

- PR #1020 is merged; merge commit is current main.
- PR #1019 is merged at merge SHA `2f4fc830150242b4cc0f9973f1c1b6c8be809fc3`.
- PR #1021 is the only open PR observed, draft and unmerged, base main, head
  `1193a4eedb242e32b226999a0a20caaf580c0a78`, 13 changed files.
- At 2026-10-25T04:13:35Z, #1021 checks observed:
  `Prevent new cold-only Lean and OpenAI CI` SUCCESS;
  `Documentation checks` SUCCESS;
  CORR4 specialized, OpenAI 7/8, source audit, proof inventory, export and several regression workflows IN_PROGRESS/PENDING.
  Therefore no new PR declaration is promoted to `PROVED_IN_LEAN_PR_GREEN_UNMERGED` in this report.

## G. Handoffs and next action

**Lean Verification:** prove the finite rational prime-owner budget as a small standalone lemma, then specialize the generic frame theorem. If PR #1021 remains the live branch, update its (211/900), (886/225), and rounded-renewal constants only after independent review and exact-head CI. Do not hide the physical-remainder premise.

**Adversarial Referee:** check the set split at (9), the finite-to-uniform telescope, the coefficient map (bmapsto4b+3), and whether any current source already proves an equal or stronger composite-gap bound. Verify that the claimed margin concerns only the deterministic recursive coefficient.

**Coordinator:** replace the current CORR-A deterministic coefficient node by (42844/11025) if independently accepted. The first missing arithmetic theorem remains the complete (9/4)-remainder/first-owner Gram estimate (or a weaker power-saving version), not the reciprocal owner budget.

**Next Wheel run:** investigate whether further forbidden composite odd locations can be incorporated without losing a simple uniform finite proof, but only if the resulting gain changes the accepted CORR-A threshold or bootstrap margin. The higher-value mathematical task is still a sign-preserving restriction on the complete first-owner Gram/remainder, not another isolated reciprocal-density constant.

## H. Resume capsule

Resume from `main@8d3a06d3748282e7e7e5cd273efdd00560cdee15`, claim
`20261025-wheel-1`, and live PR #1021 head
`1193a4eedb242e32b226999a0a20caaf580c0a78`.

New independently checkable statement:
[
 sum_{qle N, q {m odd prime}}q^{-2}
 le 9769/44100.
]
Conditional CORR coefficient:
[
 4(9769/44100)+3=42844/11025<4.
]
Rounded one-percent renewal coefficient:
[
 391023831383/437582250000<1.
]
No global signed remainder estimate was proved. Canonical VF and RH remain open.

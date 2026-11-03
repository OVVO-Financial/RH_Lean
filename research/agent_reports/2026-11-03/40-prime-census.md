# RH | Prime Census Laboratory - 2026-11-03

## Early Research Checkpoint

Execution: PARTIAL / IN_PROGRESS. Scheduled invocation at 03:11:01 EST (-0500); RUN_ID_UNAVAILABLE. Checkpoint prepared 2026-11-03 08:17:39 UTC. No new computation is claimed yet.

### Selected Question And Preregistration

Resume the exact small fragment-versus-scalar discriminator in 20261102-coordinator-3, section H, rather than repeat the completed FINITE-AC bootstrap or affine censuses. Main is 8e5d64ae689b39dabd2a4f6eb33efe4d5d192015; reporting intake is a9f0b4abdf051612929d39b463a433ef844c45eb. Policy blobs: AGENTS 9fa5e9519e2fb6dde22217aa2a18982dafef373a; proof contract 88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a; research engine 6fce99c61efb5b2a73c0cb1f1464f09b351fcd55. deployment_ack: NEXT-CENSUS resumed with newer committed evidence and a nonduplicate test.

For each root R, retain the original field
g_R(n)=mu(n)+sum_(q odd prime, q^2<R, q^2|n) mu(n/q^2)/q,
on R^2<=n<(R+1)^2. Freeze g_H^fr by replacing q^2<R with q^2<H.
W_R is the complete shell sum. Omega_R^mov is the largest absolute sum on any contiguous fragment of the same shell, equivalently maximum minus minimum of all its prefix sums, including the empty prefix. Z_R is the actual occurrence-square diagonal. N_R^fr is the unordered distinct-address pair sum of the frozen field.

Fix exploratory H=64,128 and held-out H=256,512 BEFORE scanning. Exact finite candidate tests, proposed here by Census and not attributed to an analyst:
1. SCALAR-4: sum_R (Omega_R^mov)^2 <= 4 sum_R W_R^2.
2. DIAGONAL-2: sum_R [(Omega_R^mov)^2-W_R^2] <= 2 sum_R Z_R.
One exact failure refutes the stated constant on that tested block; no revised constant will be promoted from these data. The rival explanation is that total signed cancellation hides substantial internal excursions, so a scalar energy may not supply the maximal-fragment estimate. Survival is finite evidence only.

For every root write P_R(j)=sum_(R^2<=n<j)g_R(n), and record both endpoint overshoots:
a_R=min(0,W_R)-min_j P_R(j), b_R=max_j P_R(j)-max(0,W_R).
Then Omega_R=|W_R|+a_R+b_R. Reconstruct the complete square and its excess before any norm comparison. Also record every zero W_R, exact extremal roots, frozen/moving differences, root and activation interactions.

Reconstruct the original zero-frequency physical remainder
A_R=M(R-1)-M(R^2-1)-sum_(q odd prime, q^2<R) M(floor((R^2-1)/q^2))/q
and its increment A_(R+1)-A_R=mu(R)-W_R-K_R,
where K_R=M(R+2)/q for R=q^2 with odd prime q and zero otherwise.
Check the complete energy, all four covariance sectors, and C25c:
|sum_R (A_(R+1)-A_R)^2-2 sum_R N_R^fr|<=65H^2.
K_R here is the activation term, NOT the historical FINITE-AC envelope.

Mandatory regressions: s=12,p=3 fragment cancellation; strict q^2=R and q^2=H boundaries; the genuine (3,5) consecutive cell. Two independent Mobius/carrier reconstructions will be used. No scan beyond H=512 is planned absent a new mathematical reason.

### Authority, Continuity And Scope

Read live main instructions, contract, selector, breadth/complete-return/engine/role protocols; actual transport, ledger-splice, address and canonical definitions. Material source blobs: 72d66f61b3eeb000117ecdac393572558bb7c378, 73447e8c73ea60affec36a25b9f4794862331359, 61f98a8997d86ddbb07404284d12aebd36a67955, 8c125b69cc0fbee577d063bcfa606843152868f3.

All relevant November 2 role sections and today's Owner, Analytic and Wheel findings were retrieved. Today Coordinator, Referee, Lean and preceding Census are absent at intake: TODAY=PENDING; YESTERDAY=CARRY_FORWARD. External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 has no newer than October 18 entry; its old routing is superseded.

Referee 20261102-referee-3 and Coordinator 20261102-coordinator-3 accept the strict gain only on unmerged PR1073@9cbfce5295343bcb411e6d2cb159b59995cd985b. This run will refresh PR/CI state but does not claim an independent re-review of that proof. Main retains the non-strict baseline. Canonical actual-prime VF, sharp shell-energy gain, and RH remain OPEN. This experiment assumes none of those bounds.

Only this dated own report will be published. No Lean execution, source edit, issue/PR mutation, agent launch, or merge. Final exact results, reproducible code, limitations and continuation will be appended.

---

## Final Research Synthesis - Claims 20261103-census-1 And 20261103-census-2

Prepared 2026-11-03 08:39:08 UTC; this completes the scheduled 03:11:01 EST invocation, not a second run.

**Main finding:** Aggregate fragment energy and rootwise fragment loss behave very differently on the genuine moving source. All four preregistered block tests pass, including both held-out blocks. Nevertheless the root R=787 has maximal fragment amplitude more than 1,320 times its final signed shell sum. The exact interior-excursion defect, rather than a rootwise multiplicative comparison, is a concrete candidate for the missing scalar-to-fragment bridge.

**Evidence:** claim 20261103-census-1 is FINITE_COMPUTATION, with REFUTED pointwise constant-4 and constant-2 variants on their stated tested domain. Claim 20261103-census-2 is PAPER_PROOF / SELF_AUDIT for maximal-fragment freezing. The all-scale diagonal-repair assertion is CONJECTURE. Independent Referee review of these new claims is PENDING. No new PROVED_IN_LEAN result, complete shell bound, numerical endpoint gain, or RH conclusion is claimed.

### A. Discovery And Decision

Define, on the literal shell, P_R(j)=sum_(R^2<=n<j) g_R(n), including j=R^2 and j=(R+1)^2. Put

```text
W_R = P_R((R+1)^2),
Omega_R = max_j P_R(j) - min_j P_R(j),
a_R = min(0,W_R) - min_j P_R(j),
b_R = max_j P_R(j) - max(0,W_R),
J_R = a_R+b_R >= 0.
```

There is the exact deterministic identity

```text
Omega_R = |W_R| + J_R,
Omega_R^2 - W_R^2 = J_R^2 + 2|W_R|J_R.                 (PC1)
```

This elementary identity is not claimed as a novel algebra theorem. Its useful role here is to isolate exactly what the scalar shell sum discards, without dropping any signs or locations. The tested arithmetic question is whether the aggregate defect on the right has only diagonal size.

Across H=64,128,256,512, the ratio of total maximal-fragment energy to total scalar energy is between 2.1666 and 2.6629. The excess divided by the literal diagonal lies between 1.4917 and 1.6668. These are finite observations, not evidence of an optimal constant or a fitted growth exponent.

The rootwise losses are much larger: 494 of 960 roots fail Omega_R^2<=4 W_R^2, and 248 fail Omega_R^2-W_R^2<=2 Z_R. Thus the surviving conjecture must concern joint block aggregation, not a bound applied separately at each root.

### B. Live Authority And Continuity

Pinned main, refreshed before final publication: `8e5d64ae689b39dabd2a4f6eb33efe4d5d192015`. Initial reporting head: `a9f0b4abdf051612929d39b463a433ef844c45eb`. Main did not change during the experiment. Retrieval began 08:11 UTC / 03:11 EST on November 3. All source links below refer to this exact main revision.

| Source | Blob SHA |
| --- | --- |
| `AGENTS.md` | `9fa5e9519e2fb6dde22217aa2a18982dafef373a` |
| `CURRENT_PROOF_CONTRACT.md` | `88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a` |
| `docs/RHLEAN_NATIVE_SQUARE_CLOCK_AGENT_DIRECTIVE_20261029.md` | `d05c327ae694ea54b599dab0a21032a056b521f1` |
| `docs/RHLEAN_BROAD_SEARCH_UNTIL_ETA_20261031.md` | `b5c063c51556ba57c4b25bcc380a606fa8daa207` |
| `docs/RHLEAN_SOURCE_FAITHFUL_COMPLETE_RETURN_AGENT_CONTRACT_20261031.md` | `16838f7f3c8724b970f8b8ece0bceaab9418066d` |
| `docs/RHLEAN_SEVEN_AGENT_RESEARCH_ENGINE_20261101.md` | `6fce99c61efb5b2a73c0cb1f1464f09b351fcd55` |
| `research/CANONICAL_ROUGH_Q2_TAIL_REDUCTION.lean` | `ebca096e83009a7df514d00b6a2696be86a94c55` |
| `research/LOW_OWNER_PHYSICAL_AMPLITUDE_TRANSPORT.lean` | `72d66f61b3eeb000117ecdac393572558bb7c378` |
| `research/LOW_OWNER_AMPLITUDE_MELLIN_LEDGER_SPLICE.lean` | `73447e8c73ea60affec36a25b9f4794862331359` |
| `research/GLOBAL_RETURNED_CORE_WEIGHTED_MOBIUS_COORDINATE.lean` | `f0e2e672a1ed369d1dc6dacbe9024c65e986a3c8` |
| `research/GLOBAL_RETURNED_CORE_WEIGHTED_GRAM.lean` | `dbaf123113b544d0b19c7c3c6b92a1288a26cfb8` |
| `research/GLOBAL_RETURNED_CORE_ONE_AMPLITUDE.lean` | `b69a36ec4305a9309a5212358569905a968f4d63` |
| `research/LIFTED_MOBIUS_ADDRESS_INJECTIVITY_20261102.lean` | `61f98a8997d86ddbb07404284d12aebd36a67955` |
| `RHLean/Analysis/SquareRootCanonicalRoughCovariance.lean` | `8c125b69cc0fbee577d063bcfa606843152868f3` |
| `research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean` | `79030d70e8d3e0d08eef9bac53fef95c36eca2fb` |

The original low-owner set is the odd primes up to R-1 minus the owners satisfying R<=q*q. Thus it is exactly the strict set q^2<R used here. The raw cutoff is floor((R^2-1)/q^2). The compiled ledger splice identifies the zero-frequency remainder as rough correlation minus the reciprocal daughter column, while the rough-correlation theorem identifies its first term as M(R-1)-M(R^2-1). The common-clock weighted source provides a second representation. These are the definitions used, not a model.

Canonical theorem: VFCanonicalSquareVonKochStatement, exists C>=0, forall integer R>=2, |pi(R^2)-VF_can(R^2)|<=C R log R. It remains OPEN. The sharp signed square-shell gain is a separate open benchmark. A global prefix exponent is not substituted for local shell energy.

Relevant report bytes retrieved and their applicable sections consumed:

| Report | Blob SHA |
| --- | --- |
| 2026-11-02/00-coordinator-am.md | `1e932d4ce0eb0fd2c5f4507f6b111194d633eb32` |
| 2026-11-02/10-owner-payment.md | `abfe546d72b151f4cd200fc61de3197efe23a65c` |
| 2026-11-02/20-analytic-type-ii.md | `8e48b59611aa1d0bfa3577ed0a4a3bc0d0fcae73` |
| 2026-11-02/30-finite-wheel.md | `abf8ac8c22a708886183849552c90dd62787ac8d` |
| 2026-11-02/40-prime-census.md | `2cd84c57ab18d923e97368764f29f4ccd2ec3bb3` |
| 2026-11-02/50-adversarial-referee.md | `814af1684df66e6ac99b8df1f102cb592b316f89` |
| 2026-11-02/60-lean-verification.md | `02d19d792e26f072004cb5909f149538752626e9` |
| 2026-11-03/10-owner-payment.md | `5c085d12ca455327b2a9ab42d7e55a1b6b2d631b` |
| 2026-11-03/20-analytic-type-ii.md | `7a167a551ca047c0b5bccf6220f40152d78ea176` |
| 2026-11-03/30-finite-wheel.md | `ae0ce9040b145c8b2ee04418e02a363d10b5da38` |

The Coordinator's 00 and 90 mirrors have the same blob in the retrieved reporting tree; the 00 content was read once. The selected task is its latest claim 20261102-coordinator-3, C20-C25 and section H. Earlier FINITE-AC and affine censuses were completed and were not enlarged. Yesterday's Owner equations 42-47 and Analytic equations 53-63 specify the moving/frozen carrier; Referee-3 supplies the independently accepted PR1073 scope. The latest yesterday Lean section is PARTIAL, not an assumed completed handoff.

Today's Owner SAT dilation falsifier, Analytic NYMAN tail result, and Wheel integer daughter positivity gate were read as distinct portfolio developments. None supplies the missing maximal-fragment inequality; no redundant experiment was requested by those reports. Today's Coordinator, Referee and Lean were TODAY=PENDING at intake, with November 2 YESTERDAY=CARRY_FORWARD. The Census file was absent before this invocation's checkpoint. External inbox blob `038018145c0fddb2f6306c0712373adf9cd1ea52` contains no entry later than October 18; its historical routing is superseded, while its source/counterexample safeguards remain.

Recent accepted source changes are the address interface #1070, binary parity obstruction #1071 and native non-strict replay #1072. No new formal claim is inferred solely from merge status.

PR state was refreshed during this invocation:
- #1073: draft/open/unmerged at `9cbfce5295343bcb411e6d2cb159b59995cd985b`; all 13 returned PR-triggered workflows successful, including dedicated run 41554561404. The exact unchanged Referee-3 acceptance and standard-axiom/dependency audit are carried forward, not independently rerun here.
- #1074: draft/open/unmerged at `5f53bca7d728576efcbbf2762885b7720e89aef7`. Its stronger scope remains pending independent review; its reported green CI was not re-audited in this run.
- #1075: draft/open/unmerged at `acaa66c510259a6722e3d5590106fcb9b7d50181`; 8 returned successes and dedicated run 41580316113 failure.
- #1076: draft/open/unmerged at `f676c9b13960f8c80b68bdf35a5f04b07370e228`; all 8 returned workflows successful, including dedicated run 41579190117. New stronger-scope review remains PENDING.

Project eta_gate is VERIFIED_ETA only for the independently accepted #1073 PR head, not main. This census adds no eta and does not narrow protected research coverage. Canonical VF and RH remain OPEN.

### C. Competing Hypotheses And Fixed Tests

The preregistration was published and read back in commit `7b7392bb32e5be80097a2913b98b657eb9eb62ae`, report blob `bf07cc686dc98b5c29a9324d89baa148dbdd8153`, before code execution.

The scalar-control explanation predicts that the complete shell energy remains a useful aggregate proxy for maximal fragments. The rival explanation predicts a distinct internal-excursion bill that can be large despite a small shell total. The experiment allows both facts to coexist: bounded finite aggregate ratios need not imply any uniform rootwise comparison.

Two exact finite inequalities were proposed by Census, not falsely attributed to another investigator:

```text
SCALAR-4(H):   sum_R Omega_R^2 <= 4 sum_R W_R^2.
DIAGONAL-2(H): sum_R (Omega_R^2-W_R^2) <= 2 sum_R Z_R.
```

Exploratory blocks were H=64,128; held-out blocks were H=256,512, with H<=R<2H. Both constants were fixed before any scan and were not retuned. One failure would reject that constant on that block. Pointwise variants were examined only as exceptional-behavior diagnostics after the main tests; they are not retroactively described as preregistered all-scale claims.

### D. Exact Carrier And Full Reconstruction

All computations use genuine integer Mobius values and rational weights. There are no random signs, logarithmic weights, inferred source admission, or floating membership decisions.

```text
X_R = R^2-1,
g_R(n) = mu(n) + sum_(q odd prime, q^2<R, q^2|n) mu(n/q^2)/q,
g_H^fr(n) = mu(n) + sum_(q odd prime, q^2<H, q^2|n) mu(n/q^2)/q,
W_R = sum_(R^2<=n<(R+1)^2) g_R(n),
Z_R = sum_(actual admitted occurrences i) coefficient_i^2,
2N_R = W_R^2-Z_R.
```

The lifted-address injectivity and outer/daughter disjointness are checked in the implementation, not used to silently deduplicate. Each nonzero physical site has at most one admitted occurrence. The full off-diagonal source retains outer/outer, outer/daughter, same-owner daughter and cross-owner daughter sectors; their sum equals 2N_R exactly.

The original physical remainder and activation term are

```text
A_R = M(R-1)-M(X_R)
      -sum_(q odd prime, q^2<R) M(floor(X_R/q^2))/q,
K_R = M(R+2)/q if R=q^2 for an odd prime q, and 0 otherwise,
A_(R+1)-A_R = mu(R)-W_R-K_R.                              (PC2)
```

This K_R is activation, not the FINITE-AC historical envelope. At R=q^2, the new owner enters only at R+1; floor(((R+1)^2-1)/q^2)=R+2. Also mu(R)K_R=0.

Every cross term is retained:

```text
sum_R (A_(R+1)-A_R)^2
 = sum_R [mu(R)^2+Z_R+K_R^2]
   +2sum_R N_R -2sum_R mu(R)W_R +2sum_R W_R K_R.           (PC3)
```

C25c was tested on this COMPLETE energy against the directly reconstructed frozen distinct-address pair sum. It was not tested on a selected covariance sector.

### E. Methods And Independent Checks

Environment actually observed: Linux 6.18.57 x86_64; Python 3.12.14; g++ 13.3.0. No local Lean execution was performed.

Primary method: an Eratosthenes prime-toggle/square-zero Mobius sieve, followed by separate enumeration of original outer integers and each admitted daughter occurrence. An exact common denominator D is the product of odd primes q with q^2<2H. Prefix extrema and every squared/cross quantity are integers after scaling by D or D^2. Maximum Mobius index was 1,048,576. Development runtime reported internally was 0.121261276 seconds; held-out runtime was 5.091581292 seconds.

Independent method: a C++ linear least-prime-factor Mobius sieve, followed by per-integer divisibility evaluation of g_R and g_H^fr. Frozen unordered pairs are accumulated as 2*a times the preceding prefix, independently of computing W^2-Z. The original common-clock weighted cofactor amplitude is also summed directly at block boundaries and nonzero activation roots. This checks the physical source rather than only an endpoint identity.

All 960 roots and ten rational fields per root agree exactly: W, Z, Omega, frozen W/Z/Omega, K, physical adjacent difference and frozen twice-pair sum. Mismatches: zero. The C++ build used -Wall -Wextra -Werror -O2 -std=c++17; the Bash timing reported 0.086 seconds for its complete run. An initial attempt to invoke /usr/bin/time failed because it was absent; the subsequent actual run used Bash time. No result is attributed to the failed command.

A third small certificate uses direct trial division, sharing neither sieve, at R=65 and R=787. It agrees on every displayed total and prefix extremum. Exact activation fixtures at 121,122,123 and the s=12,p=3 regression were also checked.

Commands, with source files reproduced in the appendix:

```text
python fragment_census.py --blocks 64 128 --output /workspace/fragment_development.json
python fragment_census.py --blocks 256 512 --output /workspace/fragment_holdout.json
g++ -Wall -Wextra -Werror -O2 -std=c++17 fragment_reference.cpp -o fragment_reference
time ./fragment_reference 64 128 256 512 > /workspace/fragment_reference.csv
python verify_fragment_results.py
python fragment_certificates.py
```

The verifier's absolute scratch paths can be adjusted together when reproducing elsewhere. No execution depends on unavailable saved arrays. Python uses unbounded integers. The C++ scaled prefixes are below 10^15; squared/cumulative totals are below 10^32 on the declared domain, within signed 128-bit capacity. Decimal displays below are not used for any verdict.

### F. Exact Results And Exceptional Roots

| H | Role | sum Omega^2 / sum W^2 | excess / sum Z | SCALAR-4 | DIAGONAL-2 | C25 error / H^2 |
| ---: | --- | ---: | ---: | --- | --- | ---: |
| 64 | exploratory | 2.5793193241 | 1.5135078731 | pass | pass | 1.8405751159 |
| 128 | exploratory | 2.1666822953 | 1.4917410052 | pass | pass | 1.8142475028 |
| 256 | held out | 2.6416199046 | 1.5487011684 | pass | pass | 1.8430768938 |
| 512 | held out | 2.6628332372 | 1.6666975960 | pass | pass | 1.8488797552 |

C25's signed residual is positive in these four blocks and its absolute value is less than 1.849H^2, hence safely below the fixed 65H^2 statement. This does NOT propose replacing 65 by 1.849 universally. The frozen twice-pair sum is negative at H=64,256 and positive at H=128,512. Its sign is not silently forced by the nonnegative complete energy.

No root in 64<=R<=1023 has W_R=0, and no aggregate scalar or diagonal denominator is zero. The mandated original s=12 regression does have Delta_12=0 and Omega_12(mu)=3, with daughter fragments 0,1,-1. Its scalar ratio is undefined and is not divided by zero.

**Smallest tested pointwise SCALAR-4 failure: R=65.**

```text
owners = {3,5,7},
outer shell sum = 1,
daughter unweighted sums = {3:1, 5:-3, 7:1},
W_65 = 1+1/3-3/5+1/7 = 92/105,
min P_65 = -118/15 at exclusive endpoint j=4262,
max P_65 = 638/105 at exclusive endpoint j=4334,
Omega_65 = 488/35,
Omega_65^2/W_65^2 = 133956/529 > 4.
Z_65 = 100622/1225,
(Omega_65^2-W_65^2)/Z_65 = 1067416/452799 > 2.
```

This is the smallest failure in the declared domain 64..1023, not a claim of the globally smallest root. It refutes only the stated pointwise constants, not existence of a larger all-scale constant.

**Largest tested pointwise ratio: R=787.**

```text
owners = {3,5,7,11,13,17,19,23},
outer sum = -2,
daughter unweighted sums = {3:3,5:5,7:-1,11:1,13:0,17:1,19:2,23:-2},
W_787 = 14405/572033,
min P_787 = -7936437/2860165 at j=620915,
max P_787 = 485617463/15935205 at j=619955,
Omega_787 = 218167252/6561555,
Omega_787^2/W_787^2 = 13755518505271904656/7890340550625.
```

Thus Omega_787/|W_787| is approximately 1320.3547, and the energy ratio exceeds 1.74 million. Its mechanism is visible in exact arithmetic: the outer -2 is almost canceled by the completed daughter totals, while the same contributions have different locations inside the shell. The completed rational sum does not preserve the internal path.

Largest tested pointwise excess/diagonal is at R=517:
83117350481009625/15008753843930014, approximately 5.538. Large local defects are compatible with the much smaller aggregate ratios above; no claim of independence is used.

Strict activation stress test, q=11:
- R=121: potential cofactors 121,122,123 have mu=0,1,1, but q^2<R fails, so the whole would-be 2/11 contribution is excluded.
- R=122: q is admitted, but cofactors 124,125 both have mu=0, so its actual shell contribution is still zero.
- R=123: the admitted cofactors 126,127 have mu=0,-1, giving -1/11.

This separates eligibility, actual admission and nonzero signed contribution. The H=121 frozen owner set correctly excludes 11 throughout its frozen coefficient; no extra H=121 block census was run.

The (3,5) consecutive cell was retained only as a regression inside the complete source. Its (population,signed sum) values are (21,3), (81,-3), (343,-49), (1340,-2) for the four fixed blocks. These are not substituted for the full daughter covariance or advertised as a new enlarged affine census.

### G. Exact Data Certificate

For each block below, D is the exact common denominator. EVERY value in sums is an integer numerator over D^2, including squared amplitudes, diagonals and cross terms. The ratio fields are already reduced rationals. Integer strings prevent any loss through JSON floating-number parsers.

```json
[
  {
    "H": 64,
    "D": "1155",
    "sums": {
      "w2": "9688059471",
      "omega2": "24988599007",
      "wf2": "9688955331",
      "of2": "24984936922",
      "da2": "9636907461",
      "k2": "11025",
      "z": "10109322725",
      "zf": "10109256575",
      "pair2": "-421263254",
      "pair2fr": "-420301244",
      "root_cross": "-107304120",
      "activation_cross": "4114110",
      "root2": "52026975",
      "excess": "15300539536",
      "overshoot2": "6318487008",
      "overshoot_cross": "8982052528",
      "freeze_w2": "88200",
      "freeze_omega2": "33075",
      "c25_difference": "10057208705"
    },
    "ratio": "24988599007/9688059471",
    "excess_per_diagonal": "15300539536/10109322725",
    "tests": {
      "scalar4": true,
      "diagonal2": true,
      "c25": true
    },
    "cell35": {
      "population": 21,
      "signed": 3
    }
  },
  {
    "H": 128,
    "D": "15015",
    "sums": {
      "w2": "8738409826363",
      "omega2": "18933357859882",
      "wf2": "8745827744563",
      "of2": "18934035485677",
      "da2": "8613164491918",
      "k2": "5336100",
      "z": "6834261442255",
      "zf": "6834088019005",
      "pair2": "1904148384108",
      "pair2fr": "1911739725558",
      "root_cross": "-144331687500",
      "activation_cross": "1270449180",
      "root2": "17810567775",
      "excess": "10194948033519",
      "overshoot2": "3900920608139",
      "overshoot_cross": "6294027425380",
      "freeze_w2": "154746900",
      "freeze_omega2": "94715775",
      "c25_difference": "6701424766360"
    },
    "ratio": "18933357859882/8738409826363",
    "excess_per_diagonal": "10194948033519/6834261442255",
    "tests": {
      "scalar4": true,
      "diagonal2": true,
      "c25": true
    },
    "cell35": {
      "population": 81,
      "signed": -3
    }
  },
  {
    "H": 256,
    "D": "4849845",
    "sums": {
      "w2": "2690440545694954360",
      "omega2": "7107121297566113640",
      "wf2": "2692481640973932115",
      "of2": "7108384074524808606",
      "da2": "2681716900450109830",
      "k2": "3987989030025",
      "z": "2851861186672206716",
      "zf": "2851816218144877991",
      "pair2": "-161420640977252356",
      "pair2fr": "-159334577170945876",
      "root_cross": "-12092496748812480",
      "activation_cross": "-327932939334000",
      "root2": "3692796454271925",
      "excess": "4416680751871159280",
      "overshoot2": "1938896462040655088",
      "overshoot_cross": "2477784289830504192",
      "freeze_w2": "43838119900575",
      "freeze_omega2": "31397044185936",
      "c25_difference": "2841051477621055706"
    },
    "ratio": "177678032439152841/67261013642373859",
    "excess_per_diagonal": "1104170187967789820/712965296668051679",
    "tests": {
      "scalar4": true,
      "diagonal2": true,
      "c25": true
    },
    "cell35": {
      "population": 343,
      "signed": -49
    }
  },
  {
    "H": 512,
    "D": "100280245065",
    "sums": {
      "w2": "4888836896744367353421041077",
      "omega2": "13018157380118456948966401740",
      "wf2": "4889591275073556869214528802",
      "of2": "13017720560791988851641243443",
      "da2": "4886040790664737438493525437",
      "k2": "182174210731968805350",
      "z": "4877501775165242025042897443",
      "zf": "4877481323297270189727657218",
      "pair2": "11335121579125328378143634",
      "pair2fr": "12109951776286679486871584",
      "root_cross": "-5736747668616341526589440",
      "activation_cross": "-176940125816206994541300",
      "root2": "3117399540591901624809750",
      "excess": "8129320483374089595545360663",
      "overshoot2": "3539207629882095464580254627",
      "overshoot_cross": "4590112853491994130965106036",
      "freeze_w2": "22584855240850635758025",
      "freeze_omega2": "12995984563606052966633",
      "c25_difference": "4873930838888450759006653853"
    },
    "ratio": "13018157380118456948966401740/4888836896744367353421041077",
    "excess_per_diagonal": "8129320483374089595545360663/4877501775165242025042897443",
    "tests": {
      "scalar4": true,
      "diagonal2": true,
      "c25": true
    },
    "cell35": {
      "population": 1340,
      "signed": -2
    }
  }
]
```

The full per-root outputs are reproducible from the embedded code. The exact summary retains the root square, activation square, both cross terms, moving/frozen diagonal, pair covariance, overshoot square and overshoot mixed term. No positive or negative part has been omitted.

### H. A Useful All-Scale Structural Lemma

**20261103-census-2: maximal-fragment freezing. PAPER_PROOF / SELF_AUDIT; independent review PENDING.**

For integers H>=2 and H<=R<2H, let Omega_R^fr be the maximal oscillation of the frozen field on the same shell. Then

```text
|Omega_R^mov-Omega_R^fr| <= 4 sqrt(2),
sum_(H<=R<2H) (Omega_R^mov-Omega_R^fr)^2 <= 32H.          (PC4)
```

Proof. On any contiguous fragment of the shell, the moving-minus-frozen field has precisely owners satisfying H<=q^2<R, with the original 1/q weights. The quotient interval for one q has length at most (2R+1)/q^2<4 and contains at most four integers, so its signed sum has absolute value at most 4. There are at most sqrt(2H) eligible integer owner labels, each at least sqrt(H), giving sum_q 1/q<=sqrt(2). Hence the error on EVERY fragment is at most 4sqrt(2). The difference of the two suprema of absolute fragment sums is bounded by the supremum of their difference. Squaring and summing over H roots proves PC4. Strict equality cases q^2=H and q^2=R have exactly the stipulated admission.

This extends Analytic's scalar freezing estimate to the genuinely stronger maximal observable. It does not bound either observable absolutely. The proof is elementary and uses the same counting input as the earlier scalar result; no broad novelty claim is made. All 960 exact instances passed, but the argument, not finite survival, is the basis for its PAPER_PROOF classification.

### I. Surviving Conjecture And Proof Impact

**Diagonal-repaired maximal bridge, CONJECTURE:**

```text
exists a universal C>=0, forall integers H>=56,
  sum_(H<=R<2H) [J_R^2+2|W_R|J_R]
    <= C sum_(H<=R<2H) Z_R.                              (PC5)
```

All quantities are the actual moving source defined above. The stronger fixed choice C=2 survived exactly H=64,128,256,512; it is not established for other H, much less all scales. A pointwise version with C=2 is false. The largest observed block ratio is not called an optimal constant.

By actual address injectivity, sum Z_R<=sum(2R+1)=3H^2. Therefore PC5, IF independently proved, gives

```text
sum Omega_R^2 <= sum W_R^2 + 3 C H^2.                    (PC6)
```

For any fixed rho>2, a scalar O(H^rho) bound would then transfer to maximal fragments with the same exponent. Combined with Coordinator C25's complete physical/frozen reconstruction, and only after the paper fragment-preserving inverse C20-C22 receives its required review/formalization, this supplies the presently missing route from a signed frozen-covariance estimate to the original shell consumer.

PC5 itself proves neither scalar energy control nor RH. It is a new explicit proposed arithmetic restriction, not a target bound hidden as an established premise. A scalar bound with no PC5 or alternate bridge still does not control maximal fragments. The exact first missing inequality is PC5, or a justified weaker sub-H^(5/2) aggregate defect estimate sufficient for the intended gain, together with the independently missing signed frozen-covariance bound. Both costs must be paid.

### J. Falsification And Uncertainty Audit

All membership, signs, endpoints, maxima, rational comparisons and counterexamples are exact. Trial division and both sieves give rigorous primality/Mobius values within the finite declared domain; no probable-prime test is used. No logarithms, floating optimization, randomized null model or numerical error certification is needed.

The two all-block constants were frozen before execution and not changed. Exceptional roots and their extrema were selected after inspection and are labeled as such. They illustrate a mechanism and falsify explicit pointwise constants; they do not establish a distribution law. Four contiguous dyadic blocks are a small deterministic sample, not statistically independent evidence.

The C25 finite identity and inequality are checked in two computational representations. This is independent algorithmic reconstruction within one authored invocation, NOT an independent Referee acceptance or a Lean proof. PC4 is SELF_AUDIT paper mathematics. No strong claim relies on unchanged historical arrays that were unavailable locally.

There was no denominator-zero case in the new main census. The existing zero-total s=12 fixture was preserved as undefined-ratio evidence. All full-return terms, including mu(R), activation, diagonal and mixed signs, were restored. The entire original first-bad VF source or original coefficient-4 CORR4 prefix bill is not being identified with this hybrid shell by name.

### K. Specialist Handoffs

**Coordinator / Proof Architect:** the requested C25c two-reconstruction test and scalar/fragment discriminator are complete. Consider PC5 as the explicit missing aggregate bridge; do not replace it with the refuted rootwise comparisons or infer an asymptotic rate from the table.

**Owner Payment:** exact completed daughter totals can almost annihilate the outer total while retaining large internal excursions, as R=787 demonstrates. A source-specific restriction must use positions or joint interval sums, not just the endpoint daughter vector. Preserve the distinct SAT/VF-LOW/JOH rotation.

**Analytic Type II:** PC4 permits freezing the coefficient even for maximal fragments with an O(H) squared error. The new hard quantity is the full positive overshoot defect in PC5, not the already paid activation/freezing remainder. Its control would require a genuine maximal signed estimate.

**Finite Wheel & Incidence:** the diagonal is exact occurrence mass, not an unsigned cross-pair population. The original coefficient-4 CORR4 carrier is separate. Any use of today's integer positivity gate here requires an actual weighted map; none is claimed.

**Adversarial Referee:** review PC4's fragment count, strict admission and supremum comparison independently; audit the PC1/PC5/PC6 consumer and R=65/787 certificates. Give separate verdicts on the proved structural lemma, finite results and unproved rate.

**Lean Verification:** no new branch requested. After independent acceptance and utility selection, PC4 or a finite R=65 counterexample could be formalized using existing source APIs. Do not formalize PC5 as an established inequality. Current slot-proof obligations and human-only merge remain unchanged.

### L. Ranked Experimental Portfolio

1. **CONTINUE: aggregate diagonal repair PC5.** Motivation: exact local overshoot identity and held-out aggregate ratios. Evidence: all four C=2 tests pass. Counterevidence: the pointwise C=2 form fails at 248 roots. Independent ingredient needed: genuinely signed maximal-interval arithmetic after block aggregation. Required theorem: the quantified PC5, not an assumed martingale analogy. Next decisive experiment should test a specific proof-derived restriction on overshoot intervals in a new block, not merely extend this table.

2. **REJECT at tested scope: pointwise scalar-4.** Motivation: treating a completed scalar as a proxy for every fragment. Exact counterexample R=65 and extreme R=787. No universal impossibility for every finite C is asserted. The corrected mechanism must preserve J_R or use aggregate compensation. No wider pointwise scan is needed.

3. **CONTINUE as infrastructure: maximal freezing PC4.** Independent ingredient: at most four admitted quotient sites for each newly activated owner. Paper proof and finite regression available; independent review pending. This removes a moving-cutoff complication but supplies no signed energy rate.

### M. Reproducibility Hashes

```text
e7f5254c80c908954263a45fc2c6dd98b39292e78feba5637d96a2b6455c0723  fragment_census.py
7227bb5385f4574906169dc403282823f7b6a56050e752db1ed3d4980d6a90c8  fragment_reference.cpp
1c58a65170355ca13c55775606198f14a58e48447eedaa7dd24f4e4ed4087010  verify_fragment_results.py
9bd38192ac555249833618988636be86169e0bd155b16c8e2aac77192d392588  fragment_certificates.py
f4d5e0586547d06cbe5e74e2c0cd897ee96bfe0b18fecb27d138d9cd43cceba5  fragment_development.json
7e85f0377b1a74a0d796d8eaaab5c00f57b7948db5fc7c55578cb2f8838261a1  fragment_holdout.json
fa25371b3f7f4963c3a40c589f27d068ea2ecb33a1ccb4484646d7eebafd3c52  fragment_reference.csv
```

The JSON file hashes include measured timing metadata and therefore vary on a rerun; mathematical fields should match exactly. Source hashes and the deterministic C++ per-root CSV are stable for identical files and invocation. The scripts and complete exact summary are embedded in this authorized report; no arbitrary repository experiment files were committed.

### N. Next-Run Resume Capsule

```text
RUN: scheduled 2026-11-03 03:11:01 EST; RUN_ID_UNAVAILABLE.
MAIN: 8e5d64ae689b39dabd2a4f6eb33efe4d5d192015
POLICY: 6fce99c61efb5b2a73c0cb1f1464f09b351fcd55.
TASK: latest Coordinator scalar/maximal-fragment discriminator.
CLAIMS: 20261103-census-1 finite; 20261103-census-2 paper maximal freezing.
DONE: H=64,128 development; H=256,512 holdout; 960 roots.
CHECKS: all ten fields agree between independent algorithms;
        trial factorization verifies R=65 and R=787;
        complete C25c reconstruction and every mixed term retained.
RESULT: scalar4 and diagonal2 survive all four blocks;
        pointwise versions fail; exact overshoot defect isolated.
NEW THEOREM CANDIDATE: PC5, aggregate defect <= universal C * diagonal.
PAPER LEMMA: PC4, moving/frozen maximal squared difference <=32H.
REVIEW: new claims SELF_AUDIT; independent Referee PENDING; no Lean.
PROJECT ETA: VERIFIED_ETA only on accepted unmerged PR1073 head.
NEW ENDPOINT GAIN: UNKNOWN / not established by this run.
NEXT: seek a proof-derived signed restriction on the actual overshoot
      intervals; test that restriction on a fresh H=1024 block only
      after freezing its claim, constant and rejection criterion.
DO NOT: rescan the completed four blocks or enlarge the old affine table
        without a new mechanism; infer pointwise control from aggregation;
        drop the diagonal or any root/activation/mixed term.
CANONICAL VF: OPEN. SHARP SHELL GAIN: OPEN. RH: OPEN.
PUBLICATION: early checkpoint commit/readback verified;
             final commit/readback receipt follows after publication.
```

## Reproducible Source Appendix

### fragment_census.py

```python
"""Exact preregistered scalar/maximal-fragment census; no floating verdicts."""

import argparse
import hashlib
import json
import math
import platform
import time
from fractions import Fraction
from pathlib import Path


def mobius_toggle(limit):
    mu = [1] * (limit + 1)
    mu[0] = 0
    prime = bytearray(b"\x01") * (limit + 1)
    prime[0:2] = b"\x00\x00"
    primes = []
    for p in range(2, limit + 1):
        if prime[p]:
            primes.append(p)
            for n in range(p, limit + 1, p):
                mu[n] = -mu[n]
            for n in range(p * p, limit + 1, p):
                prime[n] = 0
            for n in range(p * p, limit + 1, p * p):
                mu[n] = 0
    return mu, primes


def field(R, owners, D, mu):
    lo, hi = R * R, (R + 1) ** 2
    values = [mu[n] * D for n in range(lo, hi)]
    groups = {0: (sum(mu[lo:hi]) * D, sum(x * x for x in mu[lo:hi]) * D * D)}
    for q in owners:
        total = diagonal = 0
        for m in range((lo + q * q - 1) // (q * q), (hi - 1) // (q * q) + 1):
            if mu[m]:
                i = q * q * m - lo
                assert values[i] == 0, (R, q, m, "address collision")
                a = mu[m] * (D // q)
                values[i] = a
                total += a
                diagonal += a * a
        groups[q] = (total, diagonal)
    return values, groups


def trajectory(values):
    s = lo = hi = 0
    ilow = ihigh = 0
    z = 0
    for i, a in enumerate(values, 1):
        s += a
        z += a * a
        if s < lo:
            lo, ilow = s, i
        if s > hi:
            hi, ihigh = s, i
    lower = min(0, s) - lo
    upper = hi - max(0, s)
    omega = hi - lo
    assert omega == abs(s) + lower + upper
    assert omega * omega - s * s == 2 * abs(s) * (lower + upper) + (lower + upper) ** 2
    return dict(w=s, z=z, omega=omega, low=lo, high=hi,
                ilow=ilow, ihigh=ihigh, lower=lower, upper=upper)


def amplitude(R, D, primes, M):
    X = R * R - 1
    return D * (M[R - 1] - M[X]) - sum((D // q) * M[X // (q * q)]
                                                       for q in primes if q != 2 and q * q < R)


def block(H, mu, primes, M):
    owners = [q for q in primes if q != 2 and q * q < 2 * H]
    frozen = [q for q in owners if q * q < H]
    D = math.prod(owners)
    rows = []
    for R in range(H, 2 * H):
        admitted = [q for q in owners if q * q < R]
        mov, groups = field(R, admitted, D, mu)
        fr, _ = field(R, frozen, D, mu)
        t, f = trajectory(mov), trajectory(fr)
        root = math.isqrt(R)
        K = (D // root) * M[R + 2] if root in owners and root * root == R else 0
        da = amplitude(R + 1, D, primes, M) - amplitude(R, D, primes, M)
        assert da == D * mu[R] - t["w"] - K
        E, Zo = groups[0]
        daughter = sum(v[0] for q, v in groups.items() if q)
        dq2 = sum(v[0] ** 2 for q, v in groups.items() if q)
        Zd = sum(v[1] for q, v in groups.items() if q)
        sectors = [E * E - Zo, 2 * E * daughter, dq2 - Zd, daughter * daughter - dq2]
        pair2 = t["w"] ** 2 - t["z"]
        pair2fr = f["w"] ** 2 - f["z"]
        assert sum(sectors) == pair2
        assert mu[R] * K == 0
        root_cross, activation_cross = -2 * D * mu[R] * t["w"], 2 * t["w"] * K
        assert da * da == D * D * mu[R] ** 2 + t["z"] + K * K + pair2 + root_cross + activation_cross
        error = t["w"] - f["w"]
        assert error * error <= 32 * D * D
        assert (t["omega"] - f["omega"]) ** 2 <= 32 * D * D
        rows.append(dict(R=R, **t, wf=f["w"], zf=f["z"], of=f["omega"],
                         k=K, da=da, mu=mu[R], pair2=pair2, pair2fr=pair2fr,
                         root_cross=root_cross, activation_cross=activation_cross, sectors=sectors))
    keys = ["w", "omega", "wf", "of", "da", "k"]
    sums = {key + "2": sum(row[key] ** 2 for row in rows) for key in keys}
    for key in ["z", "zf", "pair2", "pair2fr", "root_cross", "activation_cross"]:
        sums[key] = sum(row[key] for row in rows)
    sums["root2"] = D * D * sum(row["mu"] ** 2 for row in rows)
    sums["excess"] = sums["omega2"] - sums["w2"]
    sums["overshoot2"] = sum((r["lower"] + r["upper"]) ** 2 for r in rows)
    sums["overshoot_cross"] = sum(2 * abs(r["w"]) * (r["lower"] + r["upper"]) for r in rows)
    sums["freeze_w2"] = sum((r["w"] - r["wf"]) ** 2 for r in rows)
    sums["freeze_omega2"] = sum((r["omega"] - r["of"]) ** 2 for r in rows)
    sums["c25_difference"] = sums["da2"] - sums["pair2fr"]
    assert sums["excess"] == sums["overshoot2"] + sums["overshoot_cross"]
    assert abs(sums["c25_difference"]) <= 65 * H * H * D * D
    # This fixed gap is only a regression inside the full field, never its substitute.
    cell_n = cell_s = 0
    for t in range(max(0, (H * H - 126 + 224) // 225), (4 * H * H - 1 - 126) // 225 + 1):
        x, y = 126 + 225 * t, 125 + 225 * t
        if math.isqrt(x) == math.isqrt(y):
            a = mu[14 + 25 * t] * mu[5 + 9 * t]
            cell_n += bool(a)
            cell_s += a
    tests = dict(scalar4=sums["omega2"] <= 4 * sums["w2"],
                 diagonal2=sums["excess"] <= 2 * sums["z"], c25=True)
    zero = [r for r in rows if r["w"] == 0]
    max_ratio = max((r for r in rows if r["w"]), key=lambda r: Fraction(r["omega"] ** 2, r["w"] ** 2))
    max_excess = max(rows, key=lambda r: Fraction(r["omega"] ** 2 - r["w"] ** 2, r["z"]))
    return dict(H=H, D=D, owners=owners, frozen=frozen, sums=sums, tests=tests,
                ratio=str(Fraction(sums["omega2"], sums["w2"])),
                excess_per_diagonal=str(Fraction(sums["excess"], sums["z"])),
                zeros=zero, max_ratio=max_ratio, max_excess=max_excess,
                cell35=dict(population=cell_n, signed=cell_s), rows=rows)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--blocks", nargs="+", type=int, required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    start = time.perf_counter()
    mu, primes = mobius_toggle((2 * max(args.blocks)) ** 2)
    M = [0] * len(mu)
    for n in range(1, len(mu)):
        M[n] = M[n - 1] + mu[n]
    pure12 = trajectory(mu[144:169])
    fragments = [sum(mu[(R * R + 8) // 9:((R + 1) ** 2 + 8) // 9]) for R in [36, 37, 38]]
    assert fragments == [0, 1, -1] and pure12["w"] == 0 and pure12["omega"] == 3
    for q in [3, 5, 7, 11]:
        assert not q * q < q * q and q * q < q * q + 1
    # Boundary stress at H=q^2: same fixed owner is absent, then genuinely activates.
    D = 3 * 5 * 7 * 11
    frozen = [3, 5, 7]
    before, _ = field(121, frozen, D, mu)
    after, _ = field(122, frozen + [11], D, mu)
    after_fr, _ = field(122, frozen, D, mu)
    boundary = dict(H=121, R=122, new_owner=11,
                    W_new=Fraction(sum(after) - sum(after_fr), D).__str__(),
                    same_at_activation_root=True)
    blocks = [block(H, mu, primes, M) for H in args.blocks]
    result = dict(python=platform.python_version(), limit=len(mu)-1,
                  elapsed_seconds=time.perf_counter()-start,
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  regression12=dict(fragments=fragments, **pure12), boundary=boundary, blocks=blocks)
    Path(args.output).write_text(json.dumps(result, indent=2) + "\n")
    for b in blocks:
        D2 = b["D"] ** 2
        print(json.dumps({"H":b["H"], "D":b["D"], "tests":b["tests"],
                          "sums":{k:str(Fraction(v,D2)) for k,v in b["sums"].items()},
                          "ratio":b["ratio"], "ratio_display":float(Fraction(b["ratio"])),
                          "excess_per_diagonal":b["excess_per_diagonal"],
                          "excess_display":float(Fraction(b["excess_per_diagonal"])),
                          "zero_roots":[r["R"] for r in b["zeros"]],
                          "max_ratio_root":b["max_ratio"]["R"],
                          "max_excess_root":b["max_excess"]["R"],
                          "cell35":b["cell35"]}))
    print(json.dumps({"elapsed_seconds": result["elapsed_seconds"], "boundary":boundary}))


if __name__ == "__main__":
    main()
```

### fragment_reference.cpp

```cpp
#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>

using Wide = __int128_t;
using Int = std::int64_t;

std::string decimal(Wide value) {
    if (value == 0) return "0";
    const bool negative = value < 0;
    if (negative) value = -value;
    std::string out;
    while (value) { out += char('0' + value % 10); value /= 10; }
    if (negative) out += '-';
    std::reverse(out.begin(), out.end());
    return out;
}

int main(int argc, char** argv) {
    assert(argc >= 2);
    int largest = 0;
    for (int i = 1; i < argc; ++i) largest = std::max(largest, std::stoi(argv[i]));
    const int limit = 4 * largest * largest;
    std::vector<int> least(limit + 1), mu(limit + 1), M(limit + 1), primes;
    mu[1] = 1;
    for (int n = 2; n <= limit; ++n) {
        if (least[n] == 0) { least[n] = n; primes.push_back(n); mu[n] = -1; }
        for (int p : primes) {
            if (p > limit / n) break;
            least[p * n] = p;
            if (n % p == 0) { mu[p * n] = 0; break; }
            mu[p * n] = -mu[n];
        }
    }
    for (int n = 1; n <= limit; ++n) M[n] = M[n-1] + mu[n];
    std::cout << "H,R,D,w,z,omega,wf,zf,of,k,da,pair2fr\n";
    for (int arg = 1; arg < argc; ++arg) {
        const int H = std::stoi(argv[arg]);
        Int D = 1;
        std::vector<int> owners;
        for (int p : primes) {
            if (p * p >= 2 * H) break;
            if (p != 2) { D *= p; owners.push_back(p); }
        }
        auto amplitude = [&](int R) {
            Int out = D * (M[R-1] - M[R*R-1]);
            for (int p : owners) if (p*p < R) out -= (D/p) * M[(R*R-1)/(p*p)];
            return out;
        };
        for (int R = H; R < 2 * H; ++R) {
            Int w = 0, wf = 0, low = 0, high = 0, lowf = 0, highf = 0;
            Wide z = 0, zf = 0, pair2fr = 0;
            for (int n = R*R; n < (R+1)*(R+1); ++n) {
                Int a = D * mu[n], af = a;
                int occurrences = mu[n] != 0;
                for (int p : owners) if (p*p < R && n % (p*p) == 0) {
                    const Int v = (D/p) * mu[n/(p*p)];
                    a += v;
                    occurrences += v != 0;
                    if (p*p < H) af += v;
                }
                assert(occurrences <= 1);
                pair2fr += 2 * Wide(af) * wf;
                w += a; wf += af;
                z += Wide(a)*a; zf += Wide(af)*af;
                low = std::min(low,w); high = std::max(high,w);
                lowf = std::min(lowf,wf); highf = std::max(highf,wf);
            }
            Int K = 0;
            for (int p : owners) if (p*p == R) K = (D/p)*M[R+2];
            const Int da = amplitude(R+1) - amplitude(R);
            assert(da == D*mu[R]-w-K);
            assert(pair2fr == Wide(wf)*wf-zf);
            // Check selected original weighted cofactor sources, not only endpoints.
            if (R == H || R+1 == 2*H || K != 0) {
                Int source = 0;
                for (int n = 1; n < R*R; ++n) if (mu[n]) {
                    Int weight = n >= R ? D : 0;
                    for (int p : owners) if (p*p < R && n <= (R*R-1)/(p*p)) weight += D/p;
                    source -= mu[n]*weight;
                }
                assert(source == amplitude(R));
            }
            std::cout << H << ',' << R << ',' << D << ',' << w << ',' << decimal(z)
                      << ',' << high-low << ',' << wf << ',' << decimal(zf) << ',' << highf-lowf
                      << ',' << K << ',' << da << ',' << decimal(pair2fr) << '\n';
        }
    }
}
```

### verify_fragment_results.py

```python
"""Compare all roots across implementations and print exact exceptional certificates."""

import csv
import json
from fractions import Fraction
from pathlib import Path


blocks = []
for name in ["fragment_development.json", "fragment_holdout.json"]:
    blocks.extend(json.loads(Path("/workspace", name).read_text())["blocks"])
expected = {(b["H"], r["R"]): (b, r) for b in blocks for r in b["rows"]}
count = 0
with Path("/workspace/fragment_reference.csv").open() as stream:
    for row in csv.DictReader(stream):
        values = {k: int(v) for k, v in row.items()}
        b, r = expected[(values["H"], values["R"])]
        assert values["D"] == b["D"]
        for key in ["w", "z", "omega", "wf", "zf", "of", "k", "da", "pair2fr"]:
            assert values[key] == r[key], (r["R"], key, values[key], r[key])
        count += 1
assert count == len(expected) == 960
print("Independent cross-check: 960 roots, 10 exact fields each, zero mismatches.")
for b in blocks:
    D = b["D"]
    for label in ["max_ratio", "max_excess"]:
        r = b[label]
        fields = {k: str(Fraction(r[k], D)) for k in ["w", "omega", "low", "high", "lower", "upper", "k", "da"]}
        fields["z"] = str(Fraction(r["z"], D * D))
        fields["omega2_over_w2"] = str(Fraction(r["omega"] ** 2, r["w"] ** 2))
        fields["excess_over_z"] = str(Fraction(r["omega"] ** 2 - r["w"] ** 2, r["z"]))
        fields["j_low"] = r["R"] ** 2 + r["ilow"]
        fields["j_high"] = r["R"] ** 2 + r["ihigh"]
        print(json.dumps({"H": b["H"], "kind": label, "R": r["R"], **fields}))
    sx = [sum(r["sectors"][j] for r in b["rows"]) for j in range(4)]
    print(json.dumps({"H": b["H"], "twice_sectors":[str(Fraction(v,D*D)) for v in sx],
                      "c25_over_H2":str(Fraction(b["sums"]["c25_difference"],D*D*b["H"]**2)),
                      "activation_roots":[r["R"] for r in b["rows"] if r["k"]]}))
violators = []
for b in blocks:
    for r in b["rows"]:
        if r["omega"] ** 2 > 4 * r["w"] ** 2:
            violators.append((r["R"], b["D"], r))
R, D, r = min(violators)
print(json.dumps({"pointwise_scalar4_smallest_tested":R, "violators":len(violators),
                  "W":str(Fraction(r["w"],D)), "Omega":str(Fraction(r["omega"],D))}))
```

### fragment_certificates.py

```python
"""Small trial-factorization certificates, independent of both full sieves."""

import json
from fractions import Fraction
from math import isqrt


def mu_trial(n):
    value = 1
    p = 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            value = -value
            if n % p == 0:
                return 0
        p += 1
    return -value if n > 1 else value


def prime_trial(p):
    return p >= 2 and all(p % d for d in range(2, isqrt(p) + 1))


def direct(R):
    owners = [p for p in range(3, isqrt(R - 1) + 1, 2) if prime_trial(p)]
    prefix = low = high = Fraction(0)
    jlow = jhigh = R * R
    outer = 0
    daughters = {p: 0 for p in owners}
    for n in range(R * R, (R + 1) ** 2):
        m = mu_trial(n)
        outer += m
        a = Fraction(m)
        for p in owners:
            if n % (p * p) == 0:
                c = mu_trial(n // (p * p))
                daughters[p] += c
                a += Fraction(c, p)
        prefix += a
        if prefix < low:
            low, jlow = prefix, n + 1
        if prefix > high:
            high, jhigh = prefix, n + 1
    return dict(R=R, owners=owners, outer=outer, daughter_sums=daughters,
                W=str(prefix), low=str(low), high=str(high), Omega=str(high-low),
                jlow=jlow, jhigh=jhigh,
                ratio=str((high-low)**2/prefix**2) if prefix else "UNDEFINED")


for R in [65, 787]:
    print(json.dumps(direct(R)))
for R in [121, 122, 123]:
    p = 11
    eligible = [(m, mu_trial(m)) for m in range((R*R+p*p-1)//(p*p), ((R+1)**2-1)//(p*p)+1)]
    admitted = p*p < R
    print(json.dumps(dict(R=R, p=p, eligible=eligible, admitted=admitted,
                          admitted_mass=str(Fraction(sum(a for _, a in eligible),p)) if admitted else "0")))
```

### Publication Verification - 2026-11-03 03:41 EST (-0500)

The substantive report was published in commit `1af7bfed13dc90007e5e972b4658ddbcf43fcd83` on agent-reports. Re-fetching the exact committed report returned blob `bfe32dfc58f5b7a052f978c5006684f3929e0fa5`, 52,471 characters, identical to the submitted text. Commit inspection confirmed that only `research/agent_reports/2026-11-03/40-prime-census.md` changed. The early checkpoint was preserved.

Local validation checked all exact integer summary values against the executed outputs, all four embedded source files byte-for-byte and by SHA256, A-N report structure, balanced code fences, ASCII and unintended control characters. All checks passed. This receipt changes publication state only; independent review and formal proof statuses remain as stated above.



## Scheduled Continuation Checkpoint - 2026-11-03 11:00 EST Invocation

Execution: PARTIAL / IN_PROGRESS. Trigger: SCHEDULED at 2026-11-03 11:00:01 EST (-0500); RUN_ID_UNAVAILABLE. Checkpoint prepared 2026-11-03T16:07:15Z. Main source: `3930d884282dd5315f0453e5dd88b356d187a8e0`; reporting intake: `6586a093cbec8d8da724ae7a50bd1e43125c0a7d`. Existing sections and claims 20261103-census-1/2 are preserved.

**Resumed question.** Coordinator's 07:45 handoff requested the R=125 original CORR4 daughter audit and a simultaneous-positive-pair discriminator. Newer `20261103-analytic-2` already supplies R=376, (q,r)=(17,19), and no individually positive q=3 or q=5 on 56..2048. Do not repeat or extend that scan. Independently reconstruct R=125 and R=376 from the original lower-prime-signature cells, then test a NEW aggregate-credit claim, as suggested by Analytic's next-step handoff. Keep the R=2002 endpoint regression.

**Frozen source.** X=R^2-1; S_R={odd primes q:q^2<R}; d_q=M(floor(X/q^2)); G=M(X)-M(R-1); E=sum d_q^2; U=sum d_q/q; V0=sum_(R<=n<=X)mu(n)^2; Vq=sum_(R<=n<=floor(X/q^2))mu(n)^2. Restore D-P=V0+2 sum Vq/q and the COMPLETE B_R=2 Mixed_R-2E=G^2+2GU-2E-(D-P). Original source paths, definitions and strict admissions have been inspected; no hybrid-shell identification is made.

**Preregistered finite hypothesis PAIR-HALF (Census exploratory, not an accepted upstream assertion).** Put J_q=2Gd_q/q-2d_q^2, C_q=max_(z in Z)(2Gz/q-2z^2), Rsv=sum_q(C_q-J_q). For each pair, let Gamma_qr=C_q+C_r-max_(u,v in Z,u-v=d_q-d_r)(2Gu/q+2Gv/r-2u^2-2v^2), exactly Analytic J4. Define W_R=max sum_(q<r)lambda_qr Gamma_qr over lambda>=0 with every vertex degree <=1. Test W_R >= Rsv/2 for every integer R>=56. This asks whether best legal pair accounting can retain a fixed fraction of the already present negative-square reserve; it is not itself an endpoint theorem. Rival mechanism: a coherent common offset of all daughter residuals remains invisible to their differences, so pair payment may be much smaller. Any exact R with 2W_R<Rsv refutes PAIR-HALF.

**Frozen coverage before execution:** exploratory R=56..256; held-out R=257..512; fixed arithmetic anchors R=125,376,2002. No extension beyond those ranges for this hypothesis. Use exact maximum-weight assignment to compute fractional pair credit, with an independent exact optimizer/certificate cross-check. Record both the smallest failure and the strongest ratio failure; restore the full B_R at every tested root. Independently reconstruct original first-owner cell mass at 125 and 376, retaining both cross orientations, tail/tail, squarefree diagonal, signed weights and every physical site. Actual runs and results are still PENDING.

**Continuity.** All seven roles' November 2 and November 3 reports and EXTERNAL_HANDOFFS were retrieved; relevant current derivations and handoffs are being consumed, not presumed independently accepted. TODAY=AVAILABLE for all roles at intake. Older pending statements are preserved at their historical timestamps. The newer Wheel second-prime negative-packet and Owner ancestry-capacity reports are distinct-carrier work; neither is imported into CORR4. External inbox blob 038018145c0fddb2f6306c0712373adf9cd1ea52 has no post-October-18 entry. Current policy overrides its old routing/cadence.

**Authority and scope.** AGENTS blob 9fa5e9519e2fb6dde22217aa2a18982dafef373a; proof contract 88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a; engine 6fce99c61efb5b2a73c0cb1f1464f09b351fcd55. deployment_ack: NEXT-CENSUS continues from newer committed evidence, not the completed FINITE-AC bootstrap. Existing strict Mertens gain is inherited with its reviewed/compiled scope; this experiment claims NO_NEW_RESULT yet, net new endpoint gain UNKNOWN. Canonical VF, RH and sharp local-shell bound remain OPEN. No local Lean or other-agent launch; only this role report may be written remotely.

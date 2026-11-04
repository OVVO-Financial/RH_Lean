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


## Scheduled Continuation Final Synthesis - Claims 20261103-census-3 And 20261103-census-4

This completes the scheduled 2026-11-03 11:00:01 EST (-0500) invocation. RUN_ID_UNAVAILABLE. Synthesis and final validation prepared at 2026-11-03 11:20 EST. Earlier same-day claims and their publication history are preserved. The prepublication main refresh returned the same source SHA.

### A. Most Important Discovery

**The best legally degree-limited pair credit can miss almost all of the negative-square reserve already present in genuine CORR4 arithmetic.** The preregistered PAIR-HALF assertion fails at R=57, the first failing root in its legal domain R>=56. At R=59 the optimal recovery is exactly 7/430 of the reserve, about 1.63%. A common integer offset in the daughter residuals explains this failure: every pair difference forgets that offset, although it strongly affects the original signed expression.

This is a falsifier of a specified auxiliary constant-fraction recovery claim, **not** a refutation of the full mixed bound or of all pair methods. The full original bill is negative at both witnesses, and at every root in the frozen experiment. At R=59 the daughters oppose G, so their direct one-sided signs remain useful even though the difference-only recovery is poor.

- `20261103-census-3`: FINITE_COMPUTATION, with PAIR-HALF REFUTED. Independent arithmetic algorithms, exact optimization duals and original first-owner-cell reconstruction agree.
- `20261103-census-4`: PAPER_PROOF, SELF_AUDIT only, for the common-offset obstruction and its retained-offset refinement of the pair bound. Independent Referee review PENDING; no new Lean theorem.
- New endpoint gain: UNKNOWN. Canonical actual-prime VF, RH and the sharp local-square-shell improvement remain OPEN.

### B. Authority And Continuity

Source main: `3930d884282dd5315f0453e5dd88b356d187a8e0`, retrieved from the live main branch at this invocation. Reporting intake: `6586a093cbec8d8da724ae7a50bd1e43125c0a7d`. Initial observed clock was 2026-11-03T16:00:46Z; early checkpoint was prepared at 16:07:15Z. The source snapshots, not reporting-branch copies of policy, govern this work.

Canonical declaration: `VFCanonicalSquareVonKochStatement`, in `research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean`, blob `79030d70e8d3e0d08eef9bac53fef95c36eca2fb`:

```text
exists C>=0, forall integer R>=2,
 |pi(R^2)-VF_can(R^2)| <= C R log R.
```

This experiment instead supports the sufficient CORR4 mixed-source route. It does not identify that route's carrier with actual-prime VF, the hybrid square shell, or ideal-character OAI coefficients.

| Authority | Blob SHA |
| --- | --- |
| AGENTS.md | 9fa5e9519e2fb6dde22217aa2a18982dafef373a |
| CURRENT_PROOF_CONTRACT.md | 88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a |
| Stable task selector | d05c327ae694ea54b599dab0a21032a056b521f1 |
| Broad-search policy | b5c063c51556ba57c4b25bcc380a606fa8daa207 |
| Complete-return contract | 16838f7f3c8724b970f8b8ece0bceaab9418066d |
| Persistent research engine | 6fce99c61efb5b2a73c0cb1f1464f09b351fcd55 |
| Current role prompts | 7366bb71e8a97fd11689a64311c7f590edeb1adf |
| Dynamic protocol | fe21d2824491fb001726311f736b9825a8f97eca |
| Multi-run policy | 643cfd596116720a8e5b1efc07a6124b55d70946 |

The following actual report bytes were retrieved; relevant findings, current derivations and continuation sections were read. This is continuity, not an independent audit of every upstream theorem.

| Role | November 2 blob | November 3 intake blob |
| --- | --- | --- |
| Coordinator | 1e932d4ce0eb0fd2c5f4507f6b111194d633eb32 | f9c04a1099048cd0b02fd5264b753e916cbcd521 |
| Owner | abfe546d72b151f4cd200fc61de3197efe23a65c | 0688ba1d205ac2e846c3c3a55adfc267a6eb6a40 |
| Analytic | 8e48b59611aa1d0bfa3577ed0a4a3bc0d0fcae73 | 79f5f11020d7038028f4ddfe92ff3f95d4bd0798 |
| Wheel | abf8ac8c22a708886183849552c90dd62787ac8d | 15802d31f6b7abf3ffff97a5a57942baf3bc2d07 |
| Census | 2cd84c57ab18d923e97368764f29f4ccd2ec3bb3 | 09ecf82c4a8d5d36b10ed6d64167d695e096ce03 |
| Referee | 814af1684df66e6ac99b8df1f102cb592b316f89 | 226a5a6d971f347b45e016a046007bc4ceb368ee |
| Lean | 02d19d792e26f072004cb5909f149538752626e9 | 579d19654925823b5fa2ef849366da2925d2c1b0 |

TODAY=AVAILABLE for every named role; YESTERDAY=CARRY_FORWARD where the current derivation depends on it. Earlier reports' missing-stage statements remain true at their own observation times. External inbox `038018145c0fddb2f6306c0712373adf9cd1ea52` has no entry later than October 18. EXT-20261014-3/5 and EXT-20261018-PNT-1..3 retain their source/restoration warnings; their old routing and cadence are superseded.

**Nonduplicate selection.** Coordinator `20261103-coordinator-1`, section H, requested R=125 plus simultaneous-positive small daughters. Newer Analytic `20261103-analytic-2`, J1-J8, already supplied R=376 and a 56..2048 scan. Its Census handoff explicitly asked for original-cell verification and a frozen aggregate-credit test. This invocation takes that next step instead of repeating the (3,5) search. Wheel W1-W10 supplies the one-use reserve; Analytic J4/J6 supplies the difference-conditioned cap and degree constraint. Their proof claims are not silently upgraded to independent Referee acceptance here.

The completed earlier Census fragment/burst experiments, fixed (3,5) hybrid affine saturation, Wheel's FINITE-AC partial-lift negatives, and Owner's ancestry-capacity obstruction are retained without rerunning or importing their carriers. In particular, PC5 remains a distinct conjecture; Referee's comparison-sequence obstruction is not a genuine-Mobius counterexample to it.

### C. Frozen Question And Competing Explanations

The exact preregistration was published before execution in commit `784290f8d47a2690fc5a3f290ba14c9f432ad7f8`, blob `092d6dfdc6e406f1990e7feaa6a77ac525efa2f0`, and read back byte-for-byte. Only this report changed.

**PAIR-HALF:** for every integer R>=56, the maximum pair credit W_R with vertex degree at most one is at least half the actual discarded reserve Rsv_R. Definitions follow below. This is a Census exploratory assertion, not a claim attributed to an analyst or an accepted sufficient endpoint estimate.

**Rival:** common offsets of nested daughter residuals can carry most of that reserve while leaving all annular differences unchanged. Rejection rule: any exact root with 2W_R<Rsv_R.

Frozen exploration: 56..256. Frozen validation/holdout: 257..512. Fixed anchors: 125,376,2002. The new aggregate statistic was not inspected before registration. These root ranges overlap earlier studies of different observables, and R=376 was a known arithmetic anchor; no statistical independence or wholly unseen arithmetic sample is claimed. No extension to a larger range was performed. After discovery, roots 57 and 59 were added only to independent certificate reconstruction, not to the scan domain.

### D. Exact Original Carrier

All quantities are exact integers or rationals. Put

```text
X=R^2-1; S={q odd prime:q^2<R}; Y_q=floor(X/q^2);
M(y)=sum_(1<=n<=y)mu(n); d_q=M(Y_q); G=M(X)-M(R-1);
U=sum_q d_q/q; E=sum_q d_q^2;
a(n)=sum_q 1_(n<=Y_q)/q; t(n)=1_(R<=n);
D=sum_(1<=n<=X)mu(n)^2(t(n)+a(n))^2;
P=sum_(1<=n<=X)mu(n)^2 a(n)^2;
V0=sum_(R<=n<=X)mu(n)^2;
Vq=sum_(R<=n<=Y_q)mu(n)^2;
D-P=V0+2 sum_q Vq/q;
B_R=2 Mixed_R-2E=G^2+2GU-2E-(D-P).
```

Admission is strict: q^2=R is excluded, and an admitted daughter has Y_q>=R+1. No shifted Mertens daughter, completed owner population, dropped squarefree diagonal or empirical mean-centered covariance is substituted.

Original first-owner cells use squarefree n in 1..X, lower-prime signature `{ell<p:ell divides n}`, p-free base and p-divisible child. Each oriented cell contributes

```text
A_base*T_child + T_base*A_child + T_base*T_child,
A_branch=sum_(n in branch)mu(n)a(n),
T_branch=sum_(n in branch)mu(n)t(n).
```

This retains both prefix/tail orientations and tail/tail. The first-owner label p is distinct from the daughter label q. Pair multiplicities are counted before aggregation, not deduplicated by equal amplitudes.

| Source path | Blob SHA | Role |
| --- | --- | --- |
| RHLean/Proof/SignedTransportAmplificationAudit.lean | 746f35f126f36e024d39e38c92dde30aabca266b | Literal q^2 cutoff, unshifted daughter square |
| research/CANONICAL_ROUGH_Q2_TAIL_REDUCTION.lean | ebca096e83009a7df514d00b6a2696be86a94c55 | Strict low-owner set and E |
| research/GLOBAL_RETURNED_CORE_WEIGHTED_MOBIUS_COORDINATE.lean | f0e2e672a1ed369d1dc6dacbe9024c65e986a3c8 | U and actual reciprocal site weights |
| research/GLOBAL_RETURNED_CORE_WEIGHTED_GRAM.lean | dbaf123113b544d0b19c7c3c6b92a1288a26cfb8 | Actual far-tail coefficient and site |
| research/GLOBAL_RETURNED_CORE_FIRST_OWNER_GRAM.lean | 36141a8caec5f99d6c40cb72ae1fdbcf6f462b82 | Physical diagonal and first-owner assembly |
| research/GLOBAL_RETURNED_CORE_FIRST_OWNER_CELLS.lean | 5ca177548e91dd8bc6535e9913b29dc81cdfccea | Signatures, base/child fibers |
| research/GLOBAL_RETURNED_CORE_RECIPROCAL_PREFIX_SIGNED_CELL_SPLIT.lean | 29bb263ddd07b12a2dd5ccf6a12aecaf627134d8 | Mixed_R with every cross orientation |
| research/GLOBAL_RETURNED_CORE_PREFIX_TAIL_MIXED_REMAINDER_IDENTITY.lean | d17aeb639bb47d79333cf0d00760c2604feddfdf | P and exact restored source |
| research/GLOBAL_RETURNED_CORE_POST789_DIAGONAL_SUBTRACTED_CONTROL.lean | ba95beda901719afaabca9011b8dbae6fc69662d | Actual endpoint gap G |
| research/CORR4_MIXED_TAIL_RECORD_PLATEAU_20261026.lean | a4abeb13653076bedd8e1173c933ee3324bfea26 | corr4_mixed_tail_eq_actual_endpoint_gap |
| research/CORR4_OAI_POWER_MIXED_TAIL_GATE_20261025.lean | bb0ee1252e7ba10c44ae5b8d827573d6c581b73a | Conditional complete mixed-power consumer |

The displayed definitions and original identity were inspected in these main sources. This run executed no Lean and does not claim a fresh compilation of those older modules.

### E. Exact Pair Optimization

For each q define

```text
J_q(d)=2Gd/q-2d^2;
C_q=max_(z in Z) J_q(z);
r_q=C_q-J_q(d_q)>=0;
Rsv=sum_q r_q;
Delta_qr=d_q-d_r;
Gamma_qr=C_q+C_r-max_(u-v=Delta_qr;u,v in Z)(J_q(u)+J_r(v)).
```

Gamma is exactly Analytic J4, with no diagonal counted twice. Let

```text
W=max sum_(q<r)lambda_qr Gamma_qr,
lambda_qr>=0, sum_(r!=q)lambda_qr<=1 for every q;
U_pair=G^2-(D-P)+sum_q C_q-W.
```

Then B_R=U_pair-(Rsv-W), and 0<=W<=Rsv. The full signed source is reconstructed at every tested root, not just the pair statistic.

**Optimization certificate.** With k=|S|, L=product_q q and integer symmetric matrix H_ij=L Gamma_ij, H_ii=0, the optimum is

```text
W=(1/(2L)) max_(permutations pi) sum_i H_(i,pi(i)).
```

For completeness: a legal fractional matching gives a symmetric doubly stochastic matrix by filling its diagonal with 1-degree(i). Its assignment objective is twice the matching objective. Conversely a permutation produces legal lambda_ij=(1_(pi(i)=j)+1_(pi(j)=i))/2, with fixed points ignored. The finite doubly stochastic assignment theorem proves equality. More importantly, every computed value also has a direct exact certificate that does not require trusting the optimizer: nonnegative rational y_i with y_i+y_j>=Gamma_ij and sum y_i=W, together with a feasible permutation attaining W.

The primary code uses integer subset dynamic programming. The independent check uses integer Hungarian potentials and verifies every primal/dual constraint exactly. All assignments for k<=5 are additionally enumerated exhaustively. A separate derivation computes Gamma from the sum/difference parity-coset formula instead of the primary quadratic maximization. No floating-point optimization or numerical tolerance is used.

### F. Results And Minimal Certificates

| Range | Roots | PAIR-HALF failures | First failure | Least W/Rsv | Root attaining least ratio |
| --- | ---: | ---: | ---: | --- | ---: |
| Exploration 56..256 | 201 | 65 | 57 | 7/430 | 59 |
| Holdout 257..512 | 256 | 37 | 258 | 1050736/6722409 | 309 |
| Fixed anchor 2002 | 1 | 1 | 2002 | 1395112628272540205/3007170565684034518 | 2002 |

All 458 full B_R values and all 458 pair envelopes U_pair are negative. This finite fact is not an all-scale sign theorem or exponent estimate. There is no numerical error in the sign decisions.

**Smallest legal failure R=57.**

```text
X=3248; M(X)=17; M(56)=-2; G=19;
q=(3,5,7); Y=(360,129,66); d=(-1,-1,-1);
V=(185,45,7); V0=1943; E=3; U=-71/105;
D-P=6259/3; B=-61496/35;
Rsv=6544/105;
Gamma_35=12/5; Gamma_37=68/21; Gamma_57=4/7;
W=68/21; W/Rsv=85/1636<1/2.
```

The matching consisting only of edge (3,7) attains W. Dual y=(266/105,0,74/105) has sum 68/21 and satisfies all three pair constraints. R=56 passes, so 57 is the smallest failure among all admissible roots below or equal to it, not merely the smallest selected example.

**Strongest frozen failure R=59.**

```text
X=3480; M(X)=9; M(58)=0; G=9;
q=(3,5,7); Y=(386,139,71); d=(-2,-4,-3);
V=(198,50,9); V0=2083; E=29; U=-199/105;
D-P=15663/7; B=-78704/35;
C=(4,8/5,4/7); J=(-20,-232/5,-180/7);
Rsv=688/7;
Gamma_35=8/5; Gamma_37=0; Gamma_57=8/5;
W=8/5; W/Rsv=7/430.
```

Dual y=(0,8/5,0) proves no legal weighted collection of pairs can beat 8/5; either nonzero edge attains it. Thus the result is not a poor choice of pairing. Constants greater than 7/430 cannot give an all-R lower fraction for this exact observable. No claim is made that 7/430 itself is valid or optimal at all scales.

**Original-cell independent verification.** Trial factorization, without using either sieve's mu values, reconstructed every physical site and first-owner split. At each split the child has p in its prime signature and the base does not; every lower-prime signature is retained. Aggregated products count exactly the full number of unordered distinct squarefree-site pairs. They do not explicitly loop over billions of pairs.

| R | Squarefree sites | Nonempty splitting cells | Represented unordered pairs | Mixed_R | B_R=2 Mixed_R-2E |
| ---: | ---: | ---: | ---: | --- | --- |
| 57 | 1977 | 1976 | 1953276 | -30643/35 | -61496/35 |
| 59 | 2119 | 2118 | 2244021 | -38337/35 | -78704/35 |
| 125 | 9501 | 9500 | 45129750 | -161069/33 | -328672/33 |
| 376 | 85948 | 85947 | 3693486378 | -201054737297/4849845 | -411004090324/4849845 |

At R=125, both-cross cell mass=-10919/33 and tail/tail=-4550. Their sum is Mixed_R. All q=(3,5,7,11) contribute T=(-2054/3,-118,-58,10/11). This independently verifies Wheel's positive q=11 term and negative complete bill.

At R=376, both-cross cell mass=-16004051477/4849845 and tail/tail=-38156. The unshifted daughters are (-19,12,-19,-5,-3,-4,-1) at q=(3,5,7,11,13,17,19), E=917 and D-P=5907946801/62985. The corrected positive pair is T_17=86/17 and T_19=136/19; its sum is 3946/323. The complete bill remains negative. This independently verifies Analytic's witness directly on original mixed cells, not only its endpoint formula.

The R=2002 regression gives G=208, E=8367, U=-233438518043839321/6541380665835015 and B=-17420832319643298618328/6541380665835015; every corrected T_q is nonpositive. Original-cell reconstruction at that large anchor was not run or claimed; two independent arithmetic methods checked its endpoint/diagonal quantities.

### G. Hidden Variable And Exact Retained-Offset Bound

**Claim 20261103-census-4, PAPER_PROOF / SELF_AUDIT.** This is a finite algebraic restriction applicable to the genuine source, not a newly proved distribution theorem for mu.

Fix any nonempty finite set of positive labels q, integer G and integers d_q. Define C,J,Gamma as above, k=|S| and

```text
e_q=d_q-G/(2q);
e_bar=(1/k)sum_q e_q;
Lambda=2k*(e_bar^2-dist(e_bar,Z)^2)>=0.
```

For EVERY legal nonnegative degree-at-most-one choice of lambda,

```text
Rsv-sum_(q<r)lambda_qr Gamma_qr >= Lambda.             (PC6)
```

In particular Rsv-W>=Lambda. The actual complete source therefore has the sharper upper bound

```text
B_R <= G^2-(D-P)+sum_q C_q
       -sum_(q<r)lambda_qr Gamma_qr-Lambda.             (PC7)
```

**Proof.** For an integer h, replace every d_q by d_q+h in this auxiliary integer optimization. Every Delta_qr and hence every Gamma_qr is unchanged. The degree-limited pair inequality holds for every such translated integer vector, so

```text
sum_q J_q(d_q+h) <= sum_q C_q-sum_(q<r)lambda_qr Gamma_qr.
```

Completion of squares gives

```text
sum_q J_q(d_q+h)-sum_q J_q(d_q)
 =2k*(e_bar^2-(e_bar+h)^2).
```

Maximizing over integer h yields exactly Lambda, proving PC6. Adding G^2-(D-P) proves PC7. No daughter-square credit is used twice: Lambda is proved to fit inside the residual left AFTER the pair credit, not added on an unsupported orthogonality assertion.

The same calculation shows that fixing every daughter difference while relaxing only the absolute integer anchor has exact optimal complete bill B_R+Lambda. The translated vectors are an explicitly labeled algebraic relaxation; they are **not** asserted to occur as Mobius prefixes or to preserve a physical first-bad predicate. All observed d_q used for counterexamples remain genuine.

**At R=59**, e_bar=-281/70 and the maximizing common shift is h=4. It changes d=(-2,-4,-3) to the auxiliary vector (2,0,1), preserving all differences. Lambda=3384/35, and the exact identity

```text
Rsv-W=688/7-8/5=3384/35=Lambda
```

holds. Thus even retaining the full list of mutual daughter differences leaves precisely this large common-offset loss in the sharp integer relaxation. PC7 recovers the actual B at this root. At R=57 the analogous common shift is 3 and Rsv-W=Lambda=2068/35.

**Finite discrimination.** The condition 2 Lambda>Rsv already forces failure of PAIR-HALF without solving for W. It explains 57 of 65 exploratory failures and 28 of 37 held-out failures. It does not explain the isolated R=2002 failure, so the common offset is a substantial mechanism, not a claim to classify every failure. Every computed row satisfies PC6 exactly. These post-discovery checks use the frozen rows; they are not a new independent holdout.

A looser convenient diagnostic follows from e-variance: W<=2 sum_q(e_q-e_bar)^2+k/2. This follows from Gamma_qr<=(e_q-e_r)^2+1, the degree constraint and (u-v)^2<=2u^2+2v^2. It was checked exactly but is weaker than retaining the actual offset in PC6 at the decisive roots.

The newly identified variable is the absolute daughter-prefix anchor, equivalently the common component of e. Merely adding more pair differences cannot detect a simultaneous integer translation. Direct sign information, an actual anchor constraint, or a joint estimate retaining that component can; none is supplied automatically by a global Mertens bound.

### H. Methods, Precision And Reproducibility

Environment actually observed: Python 3.12.14; g++ 13.3.0 (Ubuntu 13.3.0-6ubuntu2~24.04); Linux 6.18.57 x86_64. No random seed, external numerical library, probable-prime test, transcendental weight or floating-point sign decision is used.

Primary arithmetic: linear least-prime-factor Mobius sieve to exactly 4,008,003, integer Mertens and squarefree-count prefixes. Independent C++ arithmetic: divisor-convolution inversion mu(1)=1 and mu(n)=-sum_(d|n,d<n)mu(d), with independently trial-tested owner primes. Every M(X), M(R-1), d_q, V0 and Vq agrees on all 458 roots. Important witnesses additionally use independent trial factorization and literal first-owner grouping. The prefix and mixed reconstructions agree with difference exactly zero.

Complexity: primary sieve O(N), divisor inversion O(N log N), assignment O(k 2^k), with k<=13. The first-owner split uses multiples of actual primes and occupied signature aggregates, rather than quadratic pair enumeration. Sieve storage uses integer arrays. No hardware benchmark or peak-memory measurement is claimed.

Initial primary execution reported 2.0255568500000436 seconds; a final-source reproducibility rerun after removing unused imports reported 1.9766602909999165 seconds. The final verifier reported 0.810653099000092 seconds. These are measured diagnostic timings, not portable performance guarantees. The verifier additionally checks the entire AMP square, including the prefix/prefix cell mass and both original diagonals, with exact zero discrepancy. All mathematical outputs are exact; JSON elapsed-time fields naturally vary on reproduction.

Executed commands, using the complete source appended below:

```bash
python reserve_census.py
g++ -O2 -std=c++17 -Wall -Wextra -Werror mobius_reference.cpp -o mobius_reference
./mobius_reference > reference_rows.txt
python verify_reserve.py
python common_mode_audit.py
```

| Executed source | SHA256 |
| --- | --- |
| reserve_census.py | 3ab987d4b53f88b6057c0f14bb0290fe4727594573cd904b6f134244695a2387 |
| mobius_reference.cpp | f54fa323c9a3e1a3ecab9fba2b3e99f00c74890c56edef98e7404ff617924e70 |
| verify_reserve.py | 4d7c583a1849c814e80734a2d5148178d6db053047de5588164d3e422167dbb3 |
| common_mode_audit.py | 174cf5c594c315ad1162e51c0df283e7a097225025c9f804148665dfc6661946 |

Observed artifacts: reserve_results.json SHA256 `ef513422bdf00b4286bf2d22f21a6b85a222ddcdace1e3d93ce19b3a9c677bfb`; reference_rows.txt `45f139060cfc7a4aa2efca94acd385873ea29fce3227b82815490b6145745e60`; verification_results.json `585bd9fe0c46bbeabd1165449c64401aee81f2b284bddd2588a2c8d73d2785d9`; common_mode_results.json `7664708d5effcd4518253c45e15bb1d3e39098517cd4d06a867c47eb34c6dc30`. The sources are embedded because a hash alone is not a retrievable reproducer. No experimental files are committed outside this report.

### I. Proof Impact And First Missing Estimate

PAIR-HALF is REFUTED. Degree normalization remains essential, but correct normalization by itself does not ensure a useful fixed-fraction recovery. PC6/PC7 give an exact repair retaining the common component, with constant one and all original diagonals still present.

The actual sufficient consumer `mertensPowerBound_of_corr4MixedTailBill` takes beta>=1/2, A>=0 and the uniform all-R premise

```text
B_R <= A R^(4 beta), every integer R>=56.
```

It does not take PAIR-HALF, a local sign observation, or a favorable finite ratio. To improve an incoming beta_in one still needs an independently proved complete bound at some fixed beta_out<beta_in. PC7 offers a valid upper expression with the common-offset term restored, but **no all-scale arithmetic estimate for it is established here**. Treating that entire upper expression as a small assumed supplier would not close the proof. Neither this result nor the finite negativity provides a power saving.

Source-qualified novelty: the current W1-W10/J1-J8 records and the inspected main CORR4/cell modules were compared. The individual and pair completions are existing infrastructure, not rediscovered theorems. This report adds the exact aggregate-credit falsifiers, original-cell audit, and explicit common-offset loss/refinement. No exhaustive repository or literature-priority claim is made.

### J. GitHub And Formal Status

Live PR discovery found #1079 as the sole open PR, draft at head `bdaf5c642b51c732a3e755b2e799c8c5ec628508`. At inspection 11 attached workflows succeeded and two failed, including dedicated Native LOW-first run 41659485228. No repaired or verified new #1079 theorem is claimed. This invocation changed none of its files, statuses or workflows.

Recent accepted changes were checked from actual PR metadata: #1073 merged to main at 13:14:29Z, merge `0ac2bcccfc18d3f37d220b2758b29010a1b538c8`; stacked #1074/#1075/#1076 reached main through #1077 at 13:52:39Z, merge `acffafc79df1a3713e77dcd14eb551b7413d00c2`; #1078 merged at 14:37:17Z, current main. #1078's complete moving-prime-window note explicitly labels its new signed estimate OPEN; its source is different from this experiment and is not imported as a bound.

Inherited strict Mertens result: `research/oai_434/VF919NativeStrictMertens.lean`, unchanged blob `b33a4883e1ddb0551b0f11f062bce46680d87450`, contains `native_mertens_uniform_strict_gap` and `native_mertens_fixed_strict_power`. Exact tested #1073 head `9cbfce5295343bcb411e6d2cb159b59995cd985b` has 13 successful attached workflows. Dedicated run 41554561404 / job 125650160501 was actually read: terminal checks pass and the displayed axioms for those statements are propext, Classical.choice and Quot.sound. The earlier independent Referee acceptance is carried forward at unchanged scope. This is reuse of tested-head evidence now integrated into main, not a fresh cold rebuild or an independent Census audit of the entire analytic proof.

Programme gate: inherited VERIFIED_ETA on main at that previously accepted scope. This run's new endpoint gain is UNKNOWN; broad portfolio support remains unchanged and no team-wide narrowing is requested. Formal status of new claims 3/4: not compiled. Computational independence here means different algorithms in this invocation, not independent Referee acceptance.

### K. Specialist Handoffs

- Coordinator: retire PAIR-HALF specifically; preserve the full signed route. The common-offset component is an explicit missing variable in a difference-only recovery claim, not a new universal obstruction to CORR4.
- Analytic: the R=376 witness is verified from original first-owner cells. J6 alone loses almost all available reserve at R=59; PC7 restores a rigorously disjoint common-offset contribution. A useful next attempt must retain an actual prefix anchor or direct one-sided sign information, then reach an independently justified all-scale estimate.
- Wheel: W1's q=11 example at R=125 is confirmed with the entire D-P and every admitted daughter. Do not enlarge the pair scan; the degree and absolute-anchor qualifications are now explicit. Keep the separate FINITE-AC/MU-LIFT rotation.
- Owner: no prime-indicator VF capacity or first-escape theorem follows from this Mobius calculation. Your physical squareful ancestry witness remains a separate ready audit candidate.
- Referee: independently check PC6/PC7 via the common integer shift and the two exact dual certificates. Distinguish the algebraic translated-vector relaxation from genuine arithmetic, and the refuted half-fraction assertion from the unrefuted full source bound.
- Lean: no immediate new proof branch is requested. After independent review and utility selection, PC6/PC7 are finite algebra candidates with exact source identification; do not formalize the unproved all-scale bound as though its input were paid.

These handoffs are published in this report only. No agent was launched and no other report, issue, PR or comment was changed.

### L. Ranked Hypothesis Portfolio

| Candidate | Evidence / counterevidence | Independent ingredient needed | Disposition |
| --- | --- | --- | --- |
| Best degree-limited pair credit always recovers >=1/2 reserve | Exact R=57 and R=59 counterexamples, certified optimal credit | None can rescue this exact assertion | Reject |
| Retain common offset in addition to pair differences | PC6/PC7 paper proof; exact equalities at 57/59; all 458 checks pass | Source-specific anchored signed estimate, not merely more differences | Continue, independent review pending |
| Full mixed source obeys a stronger uniform power bound | All frozen roots negative, but no all-scale argument | Genuine complete arithmetic bound with paid parent and overlap terms | Open; do not infer from this sample |
| Earlier PC5 genuine maximal-fragment diagonal repair | Earlier fixed-block evidence; generic support/prefix inference refuted by Referee | Ordered multiplicative-sign information on actual hybrid source | Retain separately; no new scan |

### M. Next-Run Resume Capsule

```text
RUN: SCHEDULED 2026-11-03 11:00:01 EST (-0500); RUN_ID_UNAVAILABLE.
MAIN: 3930d884282dd5315f0453e5dd88b356d187a8e0.
ENGINE: 6fce99c61efb5b2a73c0cb1f1464f09b351fcd55.
TASK: CORR4 original-cell audit and preregistered aggregate-credit discriminator.
CLAIMS: 20261103-census-3 FINITE_COMPUTATION / PAIR-HALF REFUTED;
        20261103-census-4 PAPER_PROOF, SELF_AUDIT, independent review PENDING.
COMPLETED: R=56..512 plus 2002; 458 exact primal/dual certificates;
  independent divisor inversion at every root; trial-factor original cells
  at 57,59,125,376; full source and every diagonal/cross term restored.
DISCOVERY: mutual daughter differences forget the common integer offset;
  Rsv-W>=Lambda; R=59 has optimal W/Rsv=7/430.
DO_NOT_REPEAT: 56..2048 simultaneous-positive scan; current 458-root scan;
  earlier CORR4 <=20000 table or fragment fits without a new prediction.
FIRST_OPEN: a genuinely arithmetic, uniformly bounded complete source,
  not PAIR-HALF or an assumed target-strength upper envelope.
NEXT_DECISIVE_ACTION: test a specifically proposed absolute-anchor/sign
  restriction on the existing counterexample roots BEFORE widening a range.
  If no such supplier is ready, take a different ready portfolio audit,
  such as Owner's sparse physical ancestry-capacity witness or Wheel's
  five-band second-prime classification, after checking their review status.
PROJECT_GAIN: inherited reviewed strict Mertens result on main;
  NEW_RUN_GAIN: UNKNOWN; RH/canonical VF/sharp local shell remain OPEN.
PERMISSIONS: only own report written; no local Lean, no agents launched,
  no branch/PR/workflow/issue/schedule/permission changes or merge.
```

### N. Reproducible Source Appendix

The following four complete source files reproduce the exact experiment, independent arithmetic checks, optimization certificates and original-cell audits. Running the post-discovery common-mode audit does not enlarge the preregistered range.


#### reserve_census.py

```python
"""Exact preregistered CORR4 pair-credit discriminator, 2026-11-03."""

from array import array
from fractions import Fraction as F
from math import prod
import json
import platform
import time


def linear_mobius(limit):
    least = array('i', [0]) * (limit + 1)
    mu = array('b', [0]) * (limit + 1)
    mu[1] = 1
    primes = []
    for n in range(2, limit + 1):
        if least[n] == 0:
            least[n] = n
            primes.append(n)
            mu[n] = -1
        for p in primes:
            m = p * n
            if m > limit:
                break
            least[m] = p
            if n % p == 0:
                break
            mu[m] = -mu[n]
    mertens = array('i', [0]) * (limit + 1)
    squarefree = array('i', [0]) * (limit + 1)
    for n in range(1, limit + 1):
        mertens[n] = mertens[n - 1] + mu[n]
        squarefree[n] = squarefree[n - 1] + mu[n] * mu[n]
    return mu, mertens, squarefree, primes


def assignment_dp(weights):
    """Integer maximum assignment; half its value is fractional matching."""
    k = len(weights)
    best = [None] * (1 << k)
    previous = [None] * (1 << k)
    best[0] = 0
    for mask in range(1 << k):
        i = mask.bit_count()
        if i == k:
            continue
        for j in range(k):
            if not mask & (1 << j):
                next_mask = mask | (1 << j)
                candidate = best[mask] + weights[i][j]
                if best[next_mask] is None or candidate > best[next_mask]:
                    best[next_mask] = candidate
                    previous[next_mask] = (mask, j)
    permutation = []
    mask = (1 << k) - 1
    while mask:
        mask, j = previous[mask]
        permutation.append(j)
    return best[-1], list(reversed(permutation))


def evaluate(root, mertens, squarefree, primes):
    x = root * root - 1
    qs = [p for p in primes if p > 2 and p * p < root]
    k = len(qs)
    scale = prod(qs)
    ys = [x // (q * q) for q in qs]
    ds = [mertens[y] for y in ys]
    vs = [squarefree[y] - squarefree[root - 1] for y in ys]
    g = mertens[x] - mertens[root - 1]
    v0 = squarefree[x] - squarefree[root - 1]
    e = sum(d * d for d in ds)
    ul = sum(d * (scale // q) for q, d in zip(qs, ds))
    dpl = v0 * scale + 2 * sum(v * (scale // q) for q, v in zip(qs, vs))
    js = [2 * g * d * (scale // q) - 2 * d * d * scale for q, d in zip(qs, ds)]
    cs = []
    for q in qs:
        nearest = (abs(g) + q) // (2 * q)
        cs.append(2 * nearest * (abs(g) - q * nearest) * (scale // q))
    gamma = [[0] * k for _ in range(k)]
    for i in range(k):
        for j in range(i + 1, k):
            q, r = qs[i], qs[j]
            delta = ds[i] - ds[j]
            center = F(g * (q + r), 4 * q * r) - F(delta, 2)
            lo = center.numerator // center.denominator
            candidates = []
            for t in (lo, lo + 1):
                candidates.append(2 * g * ((t + delta) * (scale // q) + t * (scale // r))
                                  - 2 * ((t + delta) ** 2 + t * t) * scale)
            gamma[i][j] = gamma[j][i] = cs[i] + cs[j] - max(candidates)
            assert 0 <= gamma[i][j] <= cs[i] - js[i] + cs[j] - js[j]
    optimum, permutation = assignment_dp(gamma)
    reserve = F(sum(cs) - sum(js), scale)
    credit = F(optimum, 2 * scale)
    bill = F(g * g * scale + 2 * g * ul - 2 * e * scale - dpl, scale)
    envelope = F(g * g * scale - dpl + sum(cs), scale) - credit
    assert envelope - bill == reserve - credit >= 0
    residuals = [F(d) - F(g, 2 * q) for q, d in zip(qs, ds)]
    mean = sum(residuals) / k
    variance = sum((value - mean) ** 2 for value in residuals)
    upper_credit = 2 * variance + F(k, 2)
    assert credit <= upper_credit
    # Fix all daughter differences and optimize only their common integer shift.
    center = -mean
    lo = center.numerator // center.denominator
    shift = min((lo, lo + 1), key=lambda h: sum((value + h) ** 2 for value in residuals))
    lost_common = 2 * k * (mean * mean - (mean + shift) ** 2)
    all_difference_envelope = bill + lost_common
    assert lost_common >= 0
    return {
        'R': root, 'X': x, 'Mroot': mertens[root - 1], 'MX': mertens[x],
        'G': g, 'q': qs, 'Y': ys, 'd': ds, 'V': vs, 'V0': v0, 'E': e,
        'L': scale, 'U': F(ul, scale), 'DP': F(dpl, scale), 'B': bill,
        'T': [F(j - 2 * v * (scale // q), scale) for j, v, q in zip(js, vs, qs)],
        'C_scaled': cs, 'J_scaled': js, 'Gamma_scaled': gamma,
        'reserve': reserve, 'credit': credit, 'ratio': credit / reserve if reserve else None,
        'pair_half': 2 * credit >= reserve, 'permutation': permutation,
        'pair_envelope': envelope, 'residual_mean': mean, 'variance': variance,
        'credit_upper': upper_credit, 'mean_obstruction': 2 * upper_credit < reserve,
        'common_shift': shift, 'common_loss': lost_common,
        'all_difference_envelope': all_difference_envelope,
    }


def serial(value):
    if isinstance(value, F):
        return str(value)
    raise TypeError(type(value).__name__)


def summarize(rows):
    fails = [r for r in rows if not r['pair_half']]
    nonzero = [r for r in rows if r['ratio'] is not None]
    worst = min(nonzero, key=lambda r: r['ratio'])
    return {'count': len(rows), 'failures': len(fails),
            'first_failure': fails[0]['R'] if fails else None,
            'minimum_ratio_R': worst['R'], 'minimum_ratio': worst['ratio'],
            'mean_obstruction_count': sum(r['mean_obstruction'] for r in rows),
            'max_B_R': max(rows, key=lambda r: r['B'])['R'],
            'positive_B_count': sum(r['B'] > 0 for r in rows),
            'positive_pair_envelope_count': sum(r['pair_envelope'] > 0 for r in rows)}


def main():
    start = time.perf_counter()
    mu, mertens, squarefree, primes = linear_mobius(2002 ** 2 - 1)
    roots = list(range(56, 513)) + [2002]
    rows = [evaluate(r, mertens, squarefree, primes[:20]) for r in roots]
    summary = {'python': platform.python_version(), 'limit': len(mu) - 1,
               'exploration': summarize(rows[:201]), 'holdout': summarize(rows[201:-1]),
               'elapsed_seconds': time.perf_counter() - start}
    result = {'summary': summary, 'rows': rows}
    with open('reserve_results.json', 'w', encoding='ascii') as handle:
        json.dump(result, handle, default=serial, sort_keys=True, indent=2)
    print(json.dumps(summary, default=serial, sort_keys=True))
    selected = {56, 125, 376, 2002, summary['exploration']['minimum_ratio_R'],
                summary['holdout']['minimum_ratio_R']}
    for row in rows:
        if row['R'] in selected:
            print(json.dumps(row, default=serial, sort_keys=True))


if __name__ == '__main__':
    main()
```


#### mobius_reference.cpp

```cpp
#include <iostream>
#include <vector>
#include <cmath>

int main() {
    const int N = 2002 * 2002 - 1;
    std::vector<int> mu(N + 1), M(N + 1), sf(N + 1);
    mu[1] = 1;
    // Divisor convolution inversion, independent of the multiplicative sieve.
    for (int d = 1; d <= N; ++d)
        for (int n = 2 * d; n <= N; n += d) mu[n] -= mu[d];
    for (int n = 1; n <= N; ++n) {
        if (mu[n] < -1 || mu[n] > 1) return 1;
        M[n] = M[n - 1] + mu[n];
        sf[n] = sf[n - 1] + mu[n] * mu[n];
    }
    for (int R = 56; R <= 2002; ++R) {
        if (R > 512 && R != 2002) continue;
        const int X = R * R - 1;
        std::cout << R << ' ' << M[X] << ' ' << M[R - 1] << ' '
                  << sf[X] - sf[R - 1];
        for (int q = 3; q * q < R; q += 2) {
            bool prime = true;
            for (int d = 2; d * d <= q; ++d) if (q % d == 0) prime = false;
            if (!prime) continue;
            const int Y = X / (q * q);
            std::cout << ' ' << q << ' ' << M[Y] << ' ' << sf[Y] - sf[R - 1];
        }
        std::cout << '\n';
    }
}
```


#### verify_reserve.py

```python
"""Independent exact assignment dual and literal first-owner-cell checks."""

from array import array
from fractions import Fraction as F
from itertools import permutations
from math import isqrt, prod
import json
import time


def hungarian_dual(weights):
    n = len(weights)
    u, v, p, way = ([0] * (n + 1) for _ in range(4))
    for i in range(1, n + 1):
        p[0] = i
        j0 = 0
        minimum = [None] * (n + 1)
        used = [False] * (n + 1)
        while True:
            used[j0] = True
            i0 = p[j0]
            delta, j1 = None, None
            for j in range(1, n + 1):
                if not used[j]:
                    current = -weights[i0 - 1][j - 1] - u[i0] - v[j]
                    if minimum[j] is None or current < minimum[j]:
                        minimum[j], way[j] = current, j0
                    if delta is None or minimum[j] < delta:
                        delta, j1 = minimum[j], j
            for j in range(n + 1):
                if used[j]:
                    u[p[j]] += delta
                    v[j] -= delta
                elif minimum[j] is not None:
                    minimum[j] -= delta
            j0 = j1
            if p[j0] == 0:
                break
        while j0:
            j1 = way[j0]
            p[j0] = p[j1]
            j0 = j1
    dual_twice = [-u[i] - v[i] for i in range(1, n + 1)]
    assert all(z >= 0 for z in dual_twice)
    for i in range(n):
        for j in range(n):
            assert dual_twice[i] + dual_twice[j] >= 2 * weights[i][j]
    return dual_twice


def trial_mu(n):
    value, sign = n, 1
    p = 2
    while p * p <= value:
        if value % p == 0:
            value //= p
            sign = -sign
            if value % p == 0:
                return 0
        p = 3 if p == 2 else p + 2
    return -sign if value > 1 else sign


def first_owner_cells(root):
    """Split lower-prime signatures, summing every literal mixed cell."""
    x = root * root - 1
    mu = array('b', [0] + [trial_mu(n) for n in range(1, x + 1)])
    prime = bytearray(b'\x01') * (x + 1)
    prime[0] = prime[1] = 0
    for p in range(2, isqrt(x) + 1):
        if prime[p]:
            for n in range(p * p, x + 1, p):
                prime[n] = 0
    owners = [q for q in range(3, isqrt(root - 1) + 1) if prime[q]]
    scale = prod(owners)
    a = [0] * (x + 1)
    for q in owners:
        for n in range(1, x // (q * q) + 1):
            a[n] += (scale // q) * mu[n]
    tail = [mu[n] if n >= root else 0 for n in range(x + 1)]
    total_sites = sum(m != 0 for m in mu)
    groups = {1: [sum(a), sum(tail), total_sites]}
    signature = array('i', [1]) * (x + 1)
    mixed = prefix = tailtail = crosses = 0
    cell_count = pair_count = 0
    by_owner = []
    for p in range(2, x + 1):
        if not prime[p]:
            continue
        children = {}
        for n in range(p, x + 1, p):
            if mu[n]:
                sig = signature[n]
                item = children.setdefault(sig, [0, 0, 0])
                item[0] += a[n]
                item[1] += tail[n]
                item[2] += 1
                signature[n] *= p
        owner_mixed = 0
        for sig, child in children.items():
            total = groups[sig]
            base = [total[i] - child[i] for i in range(3)]
            assert sig * p not in groups
            groups[sig], groups[sig * p] = base, child
            cross = base[0] * child[1] + base[1] * child[0]
            tt = base[1] * child[1]
            pp = base[0] * child[0]
            crosses += cross
            tailtail += tt
            prefix += pp
            cell = cross + scale * tt
            mixed += cell
            owner_mixed += cell
            pair_count += base[2] * child[2]
            cell_count += bool(base[2] and child[2])
        if owner_mixed:
            by_owner.append((p, F(owner_mixed, scale)))
    assert pair_count == total_sites * (total_sites - 1) // 2
    assert all(count in (0, 1) for _, _, count in groups.values())
    dp = sum((tail[n] * scale + a[n]) ** 2 - a[n] ** 2 for n in range(1, x + 1))
    assert dp % scale == 0
    prefix_diagonal = sum(value * value for value in a)
    full_diagonal = prefix_diagonal + dp
    assert 2 * prefix + prefix_diagonal == sum(a) ** 2
    assert 2 * (prefix + mixed * scale) + full_diagonal == (sum(a) + scale * sum(tail)) ** 2
    return {'R': root, 'sites': total_sites, 'cells': cell_count,
            'unordered_pairs': pair_count, 'Mixed': F(mixed, scale),
            'prefix_cell_mass': F(prefix, scale * scale),
            'both_cross_cell_mass': F(crosses, scale), 'tail_tail_cell_mass': tailtail,
            'DP': F(dp, scale * scale), 'G': sum(tail), 'U': F(sum(a), scale),
            'positive_owner_mass': sum(v for _, v in by_owner if v > 0),
            'negative_owner_mass': sum(v for _, v in by_owner if v < 0),
            'largest_positive_owner': max(by_owner, key=lambda v: v[1]),
            'largest_negative_owner': min(by_owner, key=lambda v: v[1])}


def main():
    start = time.perf_counter()
    with open('reserve_results.json', encoding='ascii') as handle:
        rows = json.load(handle)['rows']
    with open('reference_rows.txt', encoding='ascii') as handle:
        reference = {int(line.split()[0]): list(map(int, line.split())) for line in handle}
    certificates = []
    for row in rows:
        ref = reference[row['R']]
        assert ref[1:4] == [row['MX'], row['Mroot'], row['V0']]
        assert ref[4::3] == row['q'] and ref[5::3] == row['d'] and ref[6::3] == row['V']
        k, g = len(row['q']), row['G']
        # A second cap derivation: complete the squares in sum/difference coordinates.
        cs, js = [], []
        weights = [[0] * k for _ in range(k)]
        for q, d in zip(row['q'], row['d']):
            z = F(g, 2 * q)
            near = z.numerator // z.denominator
            dist = min(abs(z - near), abs(z - near - 1))
            cs.append(F(g * g, 2 * q * q) - 2 * dist * dist)
            js.append(2 * F(g * d, q) - 2 * d * d)
        for i in range(k):
            for j in range(i + 1, k):
                q, r = row['q'][i], row['q'][j]
                delta = row['d'][i] - row['d'][j]
                aa, bb = F(g * (r - q), 2 * q * r), F(g * (q + r), 2 * q * r)
                center = (bb - delta) / 2
                near = center.numerator // center.denominator
                rho = min(abs(bb - delta - 2 * near), abs(bb - delta - 2 * (near + 1)))
                joint = F(g * g, 2) * (F(1, q * q) + F(1, r * r)) - (delta - aa) ** 2 - rho ** 2
                gamma = (cs[i] + cs[j] - joint) * row['L']
                assert gamma.denominator == 1
                weights[i][j] = weights[j][i] = gamma.numerator
        assert weights == row['Gamma_scaled']
        dual = hungarian_dual(weights)
        optimum = F(sum(dual), 2 * row['L'])
        assert optimum == F(row['credit'])
        permutation = row['permutation']
        assert sorted(permutation) == list(range(k))
        assert F(sum(weights[i][permutation[i]] for i in range(k)), 2 * row['L']) == optimum
        assert sum(cs) - sum(js) == F(row['reserve'])
        if k <= 5:
            brute = max(sum(weights[i][p[i]] for i in range(k)) for p in permutations(range(k)))
            assert F(brute, 2 * row['L']) == optimum
        certificates.append({'R': row['R'], 'dual_twice_scaled': dual})
    cells = []
    for root in (57, 59, 125, 376):
        result = first_owner_cells(root)
        row = next(r for r in rows if r['R'] == root)
        assert result['G'] == row['G'] and result['U'] == F(row['U'])
        assert result['DP'] == F(row['DP'])
        assert 2 * result['Mixed'] - 2 * row['E'] == F(row['B'])
        cells.append(result)
        print('CELLS', json.dumps(result, default=str, sort_keys=True))
    result = {'verified_rows': len(rows), 'cells': cells, 'dual_certificates': certificates,
              'elapsed_seconds': time.perf_counter() - start}
    with open('verification_results.json', 'w', encoding='ascii') as handle:
        json.dump(result, handle, default=str, sort_keys=True, indent=2)
    print('VERIFIED', len(rows), 'elapsed_seconds', result['elapsed_seconds'])


if __name__ == '__main__':
    main()
```


#### common_mode_audit.py

```python
"""Post-discovery checks of the exact common-offset obstruction; no new scan."""

from fractions import Fraction as F
import json


with open('reserve_results.json', encoding='ascii') as handle:
    rows = json.load(handle)['rows']

for row in rows:
    reserve, credit, loss = map(F, (row['reserve'], row['credit'], row['common_loss']))
    assert reserve - credit >= loss >= 0
    k, g = len(row['q']), row['G']
    shifted = [d + row['common_shift'] for d in row['d']]
    direct = sum(2 * F(g * d, q) - 2 * d * d for q, d in zip(row['q'], shifted))
    actual = sum(2 * F(g * d, q) - 2 * d * d for q, d in zip(row['q'], row['d']))
    assert direct - actual == loss
    # All pair differences and hence all Gamma values survive the optimizing shift.
    assert all(shifted[i] - shifted[j] == row['d'][i] - row['d'][j]
               for i in range(k) for j in range(k))

result = {}
for name, sample in [('exploration', rows[:201]), ('holdout', rows[201:-1]), ('anchor', rows[-1:])]:
    failures = [r for r in sample if not r['pair_half']]
    result[name] = {'rows': len(sample), 'pair_half_failures': len(failures),
                    'forced_by_common_mode': sum(2 * F(r['common_loss']) > F(r['reserve']) for r in sample),
                    'pair_envelope_equals_all_difference': sum(F(r['pair_envelope']) == F(r['all_difference_envelope']) for r in sample),
                    'max_lost_ratio_R': max(sample, key=lambda r: F(r['common_loss']) / F(r['reserve']))['R']}
print(json.dumps(result, sort_keys=True))
with open('common_mode_results.json', 'w', encoding='ascii') as handle:
    json.dump(result, handle, sort_keys=True, indent=2)
```


### Verified Publication Receipt - 2026-11-03 11:22 EST

The completed synthesis and all four executable sources were published in commit `12c3aec267e04e364c9ff5ea1d942d777902e65d`, content blob `f4b1e85d89607a1ad2b4a54fa660d60b13b58eb9`. At 2026-11-03T16:22:00Z, pinned readback matched all 104,498 characters exactly. The commit inspection confirmed only `research/agent_reports/2026-11-03/40-prime-census.md` changed, with 812 additions and zero deletions. All earlier same-day content and the preregistration checkpoint were preserved. This receipt is appended only after that verification.

Final mathematical checks: 458 independent arithmetic comparisons and exact primal/dual certificates passed; original first-owner reconstruction and full AMP square restoration passed at R=57,59,125,376; no unresolved discrepancy. A final report-only sign-check command initially had a quoting/parenthesis error, was corrected, and returned true for negativity of every stored B and pair envelope. The arithmetic programs were unaffected. Main remained `3930d884282dd5315f0453e5dd88b356d187a8e0`; #1079 remained open/draft at the inspected unchanged head. No GitHub mutation outside this authorized report occurred.


## Scheduled Continuation Checkpoint - 2026-11-03 19:00 EST Invocation

Actual trigger: 2026-11-03T19:00:01-05:00. RUN_ID_UNAVAILABLE.
Checkpoint written at 2026-11-03T19:06 EST. Status: PARTIAL; no new result or completed integral evaluation claimed.

Main refreshed to `25127ac796a1d2ace7a8b3ddb27a02154cc48ef2`; AGENTS blob `b878d396c387a57bd0b5165fecf10d15ef3732cd`; proof-contract blob `63f7553bf6e5f2a16e37808116c643dc0dcc50e1`; source-first policy `b6980c30e63bb8c9ddfc8d6fa86a2bb401707fa6`. SOURCE_FIRST_VERSION=2026-11-03. Selected NEXT-CENSUS. All November 2/3 named role files and external inbox were retrieved at reporting snapshot `78ce7dc8eb16986f22f4c0624ff8e01ceaa14fe3`; applicable findings are continuity evidence, not new proof authority. Today's reports are available; independent review of this new experiment is PENDING.

### Preregistered Experiment

Resume Wheel `20261103-wheel-3` O1-O4, not the completed native CORR4 scan. The exact source is pinned OAI `1581d4cbdd69a0faf34b2089614fe2a814316a6a`, `LowSlotPolynomial.compensation_tuple_low_polynomial` (blob `b1dcb5a1e51afad1d39ccd91fa58a764e39629ba`). In the actual code J indexes UNSELECTED slots. Canonical ideal labels are retained using `canonicalSlotEquiv`, not deduplicated by norm.

Question: does the conjugate-prime incidence graph determine the complete multiplicity of a product-norm fiber? Rival H0: only the bound m<=2^|J| is robust, with arbitrary intermediate positive multiplicities. Candidate H1: for full Cartesian, pairwise-disjoint prime-ideal slots each nonempty norm fiber has m=2^c, where c counts residual alternating cycles after forced assignments; terminal separated norm bands permit only same-slot conjugate switches. A multiplicity outside {0,1,2,4,...}, disagreement with the independent reconstruction, or loss of an original occurrence rejects H1.

Frozen exploratory domain: all assignments of the six actual split prime ideals above 7,13,19 to absent/slot0/slot1/slot2 (4096 placements), every J subset (8 masks). Held-out domain: 512 deterministic placements of the eight split ideals above 31,37,43,61 and the inert ideals above 5,11 into absent/four slots, every J; seed 20261103. Include exact p^2 forced assignments, loops, parallel cycles, empty/full/partial J, empty pools, and explicit exclusions. Stress tests deliberately delete one tuple from a four-element fiber or violate slot disjointness; these test necessity of hypotheses and are not legal terminal counterexamples.

Freeze rational norm-only slot weights and compare the COMPLETE symbolic Hermitian polynomial by direct ordered pairs versus separately grouped fibers. Actual selected inverse integrals remain symbolic. No invented values for H_J(L), no arbitrary complex vector labeled actual OAI, and no native Mobius substitution. Direct certified OAI integration is presently BLOCKED (`UNSUPPORTED_DIRECT_OAI`): no concrete admissible calibration/character/Schwartz-window instance with certified tail and numerical integration has been constructed. The authorized fallback is an exact finite source sub-identity, NOT a numerical positive C_low witness. Principal and nonprincipal characters remain universally quantified in the symbolic identity, not numerically tested.

A further source check is mandatory: `LowNormalized` has positive injective ell and common norm windows [a Z^ell_i,b Z^ell_i]. Once these bands separate, cross-slot conjugacy cycles cannot occur. Do not promote a merely disjoint arbitrary-slot example as an asymptotic terminal example.

PR #1083 was live OPEN/DRAFT at head `e859ade072681f0a0dc596198eaa2f2863b91525`: 13 check runs successful, dedicated low-first-slot-proof IN_PROGRESS. This is newer than Wheel's failed-head observation; no complete CI or axiom certification is claimed. The existing strict-slot gain is inherited at its previously reviewed scope only; this run's new endpoint gain is UNKNOWN.

Planned output: exact finite certificates, a source-scoped proof or smallest falsifier, all missing return terms, and a nonduplicate resume capsule. Only this own dated report may be written remotely.

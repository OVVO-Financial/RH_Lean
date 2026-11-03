# RH | Owner Payment - 2026-11-03

**Completed finding:** an exactly matched zero-mass prime layer acquires coherent mass T_R ~ (49/165)(R^2-1)/log(R^2-1) under root doubling. Its full return cancels this component exactly. New status: PAPER_PROOF / REFUTED homogeneous transfer / no new endpoint gain. Detailed final synthesis and verification follow the preserved checkpoint.


## Early Research Checkpoint

**Status:** PARTIAL / IN_PROGRESS. **Trigger:** scheduled invocation begun 2026-11-03 00:09 EST (-0500); RUN_ID_UNAVAILABLE.

### A. Mathematical question

Resume the overdue SAT route at the exact restoration V(R,K,j)+U(R,K,j)=M(R^2-1). Test a genuinely two-depth/two-scale signed removal-return identity, eliminate the terminal coordinates, and determine whether anything independently restrictive remains. The bounded fixed-depth crossing at 18349 is established infrastructure, not a new gain mechanism. No new theorem is asserted in this checkpoint.

### B. Authority and continuity

Pinned main: 8e5d64ae689b39dabd2a4f6eb33efe4d5d192015.
AGENTS.md: 9fa5e9519e2fb6dde22217aa2a18982dafef373a.
CURRENT_PROOF_CONTRACT.md: 88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a.
Research-engine policy: 6fce99c61efb5b2a73c0cb1f1464f09b351fcd55.

Canonical target remains: exists C>=0, for every integer R>=2,
|pi(R^2)-VF_can(R^2)| <= C R log R.
The canonical bound, RH and the sharp signed square-shell improvement remain unproved on main.

Today upstream: TODAY=PENDING (dated directory absent at intake).
Yesterday: YESTERDAY=CARRY_FORWARD, agent-reports snapshot f50a849226f7c095c16f91e794de976ac2f05706.
Latest Coordinator: 20261102-coordinator-3, blob 1e932d4ce0eb0fd2c5f4507f6b111194d633eb32.
Latest Owner: 20261102-owner-3, blob abfe546d72b151f4cd200fc61de3197efe23a65c.
SAT continuation: 20261101-owner-1/2, blob 40ad74dd7378834a48203153afc30618233f4b04.
External inbox: 038018145c0fddb2f6306c0712373adf9cd1ea52; no entry newer than October 18.

Material SAT source blobs:
- SquareRootPostCrossingTail.lean: 660772bad3663d14c0f3390e26925b57d1390080.
- SquareRootCanonicalRoughCovariance.lean: 8c125b69cc0fbee577d063bcfa606843152868f3.
- SquareRootFixedCrossing18349.lean: aee06fd1687a70621e551451115d42e2aecade05.

Open draft PRs: #1073 through #1076. Main includes merged #1070, #1071 and #1072. Referee 20261102-referee-3 and Coordinator 20261102-coordinator-3 record VERIFIED_ETA on #1073 head 9cbfce5295343bcb411e6d2cb159b59995cd985b only; exact source/CI refresh is continuing. Do not promote this to main, RH, or a sharp shell-energy result.

### C. Execution and resume plan

deployment_ack: current engine and main consumed; NEXT-OWNER adjusted to overdue SAT by protected rotation and the latest Coordinator assignment. Actual preceding sequence was JOH / VF-LOW / JOH. This invocation will supply SAT; it will not repeat JOH or the already paid activation norm.

Preregistered falsification: test fully restored depth differences and moving root/prime admission, including legal zero-defect and top-fibre cases. An identity that cancels every terminal coordinate and becomes zero is IDENTITY_ONLY, not an independent bound. An actual weighted operator that still contains a terminal Mertens mode must expose it.

Author review will be SELF_AUDIT. No local Lean execution, proof branch, PR mutation, schedule change, or other agent launch is authorized or performed. Final A-K findings, exact missing lemma and publication receipt will follow in this same daily file.

---

## Completed SAT Investigation - Claim 20261103-owner-1

**Research status:** COMPLETE. **Invocation:** the scheduled 00:09 EST run, not a second execution. **Synthesis:** 2026-11-03 00:24 EST (-0500).
**Classification:** PAPER_PROOF / EXACT SOURCE-PRESERVING DILATION; PAPER_PROOF / COHERENT ZERO-LAYER ACTIVATION; REFUTED / HOMOGENEOUS DEPTH-TRANSFER CONTROL; IDENTITY_ONLY / COMPLETE TERMINAL RESTORATION; FINITE_COMPUTATION / EXACT REGRESSIONS.
**New endpoint gain from this invocation:** NONE. Independent Referee acceptance and Lean formalization of this new claim: PENDING.

### A. Most important mathematical development

A zero signed reciprocal layer does not stay zero under a root doubling, even when its actual prime labels and both admission boundaries are preserved exactly.

Let X=R^2-1, Y=(2R)^2-1, R>=7, and let P_R(K) be the repository's literal truncated upper-middle packet. The original quotient-two layer satisfies

~~~text
P_R(2)-P_R(1) = 0.
~~~

Under the source-preserving depth map K -> 4(K+1)-1, the same prime labels occupy depths 8 through 11. Their new contribution is

~~~text
T_R := P_(2R)(11)-P_(2R)(7)
     = 2[pi(floor(X/2))-pi(floor(X/3))]
       -[pi(floor(Y/10))-pi(floor(Y/11))].                 (50)

N_R := pi(floor(X/2))-pi(floor(X/3)),
N_R <= T_R <= 2N_R.                                     (51)

T_R ~ (49/165) X/log X  as R -> infinity.                (52)
~~~

Every retained prime contributes +1 or +2 after doubling, although its original complete contribution was zero. This is genuine arithmetic coherence, not random-sign behavior or a copied historical occurrence.

Consequently no finite constant can give the homogeneous transfer

~~~text
|P_(2R)(11)-P_(2R)(7)| <= C |P_R(2)-P_R(1)|             (FALSE)
~~~

for every R>=7. At R=7 the two sides before multiplication by C are exactly 5 and 0. The error is not a negligible boundary: (52) also excludes T_R=O(R^(2-delta)) for any fixed delta>0.

Complete restoration remains essential. For the actual completed-layer coupled tail U_R(K),

~~~text
U_R(K)+P_R(K)=M(R^2-1),
[U_(2R)(11)-U_(2R)(7)]-[U_R(2)-U_R(1)] = -T_R.          (53)
~~~

Thus the fully restored two-depth rectangle is zero. The nonzero arithmetic restriction is real, but it resides in a component exactly compensated by its original complement. It does not constrain the two terminal Mertens values or improve their bound.

### B. Current authoritative objective

Pinned and final-refreshed main: 8e5d64ae689b39dabd2a4f6eb33efe4d5d192015, unchanged during this investigation.

Canonical objective, still OPEN on main:

~~~text
exists C>=0, forall integers R>=2,
  |pi(R^2)-VF_can(R^2)| <= C R log R.
~~~

The SAT carrier used here is the actual rational Mobius square-prefix population, not the prime-counting defect, ideal-character coefficients, or the original masked #915 VF/NNS statistic. Its internal RH-scale consumer requires the complete square-prefix Mertens energy bound. No direct identification with the VF physical source is claimed.

Authority hashes are in the checkpoint. Additional policy bytes read include role prompts 7366bb71e8a97fd11689a64311c7f590edeb1adf and dynamic protocol fe21d2824491fb001726311f736b9825a8f97eca. The protected SAT turn follows the latest Coordinator correction, rather than repeating the preceding JOH assignment.

Material original-source files, all at pinned main unless marked PR-head:

| File | Blob SHA | Relevant declaration or scope |
| --- | --- | --- |
| RHLean/Proof/LargePrimeTerminalFlipLayers.lean | b7617df21b81002854a0d311ef7e02d9494154c3 | P_R(K), actual layer card, partial packet, full-layer identity |
| RHLean/Analysis/SquareRootShallowReciprocalCrossing.lean | a6ed67f08cf5b225783feb0076e45a1ddb21920a | Endpoint-parametric layer and fixed-dilation native PNT |
| RHLean/Analysis/SquareRootPostCrossingTail.lean | 660772bad3663d14c0f3390e26925b57d1390080 | Raw tail, coupled tail, exact terminal reconstruction |
| RHLean/Analysis/SquareRootCanonicalRoughCovariance.lean | 8c125b69cc0fbee577d063bcfa606843152868f3 | Complete renewal collapse; mean/covariance restoration |
| RHLean/Analysis/SquareRootMiddleSequentialCoherence.lean | 510d173308e1ffc3732d02d8d9d6ed603190f6aa | Literal quotient-two zero layer and completed fresh-prime parents |
| RHLean/Analysis/SquareRootFixedCrossing18349.lean | aee06fd1687a70621e551451115d42e2aecade05 | Already established crossing, not re-proved |
| RHLean/Analysis/SquareRootTransportTopFibreNoGo.lean | fcc63e7bcb6927122075c39ccacaca445685729e | Retained coherent top-prime population |
| RHLean/Analysis/TwoABScaleTransfer.lean | fae76878063583322a48a329810cc1cc7b037ee7 | Source entry/smooth/transport accounting |
| RHLean/Analysis/PrimeDilateCofactorPrimeWindows.lean | 5efc31a80d069d9dd29374a8b5384a03c44de3d4 | Prior cofactor-window interface; different from endpoint dilation |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb | Canonical target and explicit classical consumer |

The new paper proof uses the compiled native PNT only at fixed dilation parameters. No new external literature theorem is imported. Existing native-decision crossing certificates are historical source evidence; Owner ran no Lean checks and proposes no new native-evaluation proof.

**Project gain status, separate from this result.** Referee 20261102-referee-3 and Coordinator 20261102-coordinator-3 accept VERIFIED_ETA on PR #1073 head 9cbfce5295343bcb411e6d2cb159b59995cd985b only. This run matched that exact head, inspected its unconditional terminal declarations and refreshed all 13 successful attached workflows, including run 41554561404. The strict endpoint files match the reviewed blobs:

- VF919NativeStrictSevenEighths.lean: efbf2780f0b453a702fb8847f2d360d8faf0fa66.
- VF919NativeStrictMertens.lean: b33a4883e1ddb0551b0f11f062bce46680d87450.

The terminal statement is an existential fixed positive gap below 7/8 for the genuine Mertens exponent and a fixed power bound. The existing Referee's standard-axiom and live-dependency audit is carried forward; this Owner source/CI refresh is not a new independent audit of that entire analytic proof. Main still contains the non-strict baseline. Neither the sharp local shell estimate nor RH follows.

Latest observed open PR evidence:

| PR | Exact head | State observed during this run |
| --- | --- | --- |
| 1073 | 9cbfce5295343bcb411e6d2cb159b59995cd985b | Draft, unmerged; 13/13 workflows successful; independently accepted at this head |
| 1074 | 5f53bca7d728576efcbbf2762885b7720e89aef7 | Draft, unmerged; 7/7 workflows successful; stronger-scope independent verdict not retrieved |
| 1075 | acaa66c510259a6722e3d5590106fcb9b7d50181 | Draft, unmerged; 8 successful workflows and dedicated failure 41580316113 |
| 1076 | f676c9b13960f8c80b68bdf35a5f04b07370e228 | Draft, unmerged; 8/8 returned workflows successful, including 41579190117; new independent scope review PENDING |

This supersedes yesterday's stale #1075/#1076 heads and pending-CI observations, not its mathematical review scope. Owner performed no PR or CI mutation.

### C. Structural hypothesis investigated

The resumed step was 20261101-owner-2: bounded fixed-depth crossing plus full restoration is target-equivalent. Coordinator 20261102-coordinator-3 requested an explicit genuinely two-depth/two-scale test before terminal elimination.

Three distinct possibilities were compared:

1. A terminal-free linear rectangle of fully restored packets. This cancels algebraically and cannot by itself restrict Mertens.
2. Exact alignment of prime cutoffs under endpoint dilation, allowing the same real prime cohort to be followed without an admission approximation. This survives as (54)-(57).
3. Persistence or homogeneous contraction of a zero-mass reciprocal layer under that aligned dilation. This fails by the coherent activation theorem (50)-(52).

The selected deep investigation was the second/third pair. It avoids an arbitrary model: each term is the actual integer n=pm with its original Mobius sign, largest-prime owner p, physical endpoint and once-only occurrence.

The result does not refute a theorem restricted to a valid sign-crossing seat. Depths 1 and 2 in this witness are not asserted to satisfy SquareRootPacketCrossesAt. It refutes an unconditional layer-transfer supplier that could otherwise be mistakenly used inside a crossing argument.

### D. Mathematical derivation

**D1. Literal packet and complete return.**

Write M(t)=sum_(1<=m<=t) mu(m), X_R=R^2-1, and

~~~text
N_R(d) = # {prime p : max(R,floor(X_R/(d+1))) < p
                       <= floor(X_R/d)},
P_R(K) = -sum_(1<=d<=K) M(d) N_R(d).
~~~

The strict condition is p>R, not p>=R. These are exactly the layer cards and integer packet in LargePrimeTerminalFlipLayers. No artificial eligible prime is admitted.

For K>=1 set j=N_R(K). The compiled full-layer identity identifies the partial packet at j with P_R(K). Define U_R(K) to be the real integer value of the original coupled tail at that full seat. Its original population form is

~~~text
U_R(K) = squareRootSmoothMass(R-1)
         + P_R(R-1)-P_R(K),
P_R(K)+U_R(K)=M(X_R).                                    (54)
~~~

Thus all original smooth mass, raw late transport, top fibre, unit anchor and terminal mass are retained. This is a specialization of the unconditional exact identity, not an invocation of the unproved tail bound.

**D2. An exact dilation that fixes the prime cutoff.**

Let a>=2, K>=1 and R>=a(K+1)+1 be integers. Set

~~~text
X=R^2-1,  Y=(aR)^2-1=a^2 X+(a^2-1),
K'=a^2(K+1)-1,  B=floor(X/(K+1)).
~~~

Then

~~~text
floor(Y/(K'+1))=B,   B>=aR,   K'<aR.                    (55)
~~~

Proof: write X=(K+1)b+r with 0<=r<K+1. The remainder a^2 r+(a^2-1) is between 0 and a^2(K+1)-1, proving the floor equality. Also
R^2-1-aR(K+1)=R(R-a(K+1))-1>=0, proving B>=aR. The depth bound follows from the same hypothesis.

Consequently both packets have the same strict prime cutoff B:

~~~text
P_R(K)     = -sum_(prime B<p<=X) M(floor(X/p)),
P_(aR)(K') = -sum_(prime B<p<=Y) M(floor(Y/p)).            (56)
~~~

For a surviving prime p, if d=floor(X/p), then

~~~text
a^2 d <= floor(Y/p) <= a^2(d+1)-1.
~~~

This follows by dividing X=dp+r, 0<=r<p, and retaining the exact a^2-1 endpoint correction. It is not a rounded real scaling law.

The full chronological change is therefore

~~~text
P_(aR)(K')-P_R(K)
 = -sum_(prime B<p<=X) [M(floor(Y/p))-M(floor(X/p))]
   -sum_(prime X<p<=Y) M(floor(Y/p)).                    (57)
~~~

The first sum consists only of newly admitted cofactors of surviving owners. The second is the actual new-prime birth population. Neither is dropped.

For both endpoints Z=X,Y, B>=sqrt(Z). Any n<=Z with largest prime p>B has that prime exactly once and has cofactor m<p. There cannot be two such prime factors. Hence mu(pm)=-mu(m), even when mu(m)=0, and the rough part is exactly (56). If

~~~text
A_B(Z)=sum_(1<=n<=Z, largest_prime_factor(n)<=B) mu(n),
largest_prime_factor(1)=1,
~~~

then U_R(K)=A_B(X), U_(aR)(K')=A_B(Y). This proves that the complement in (54) is a genuine population, not an unspecified error variable. The complete annulus identity is

~~~text
M(Y)-M(X)
 = [A_B(Y)-A_B(X)] + [P_(aR)(K')-P_R(K)].                 (58)
~~~

**D3. Coherent activation of the zero layer.**

Take a=2 and the two lower depths K=1,2. Their aligned upper depths are 7,11. For R>=7,

~~~text
floor(Y/8)=floor(X/2),  floor(Y/12)=floor(X/3),
L_R={prime p : floor(X/3)<p<=floor(X/2)}.
~~~

Every p in L_R exceeds 2R, so it remains a legal post-root owner at both scales. Its old quotient is 2; its new quotient lies in {8,9,10,11}. Direct factorization gives

~~~text
M(2)=0,
(M(8),M(9),M(10),M(11))=(-2,-2,-1,-2).
~~~

Thus each old complete fibre has mass zero, while its new mass -M(floor(Y/p)) is +1 or +2. The only weight-1 fibres have new quotient 10. Their full interval
(floor(Y/11),floor(Y/10)] lies inside L_R. Counting these exceptions gives (50) and (51).

Equivalently, the old physical pair p,2p cancels. The new physical integers mp in X<mp<=Y contribute the positive residual. No old integer is duplicated; different p cannot share a new physical integer because their product exceeds Y.

Apply the already compiled fixed-dilation native PNT:

~~~text
N_R * log(X)/X -> 1/2-1/3 = 1/6,
[pi(floor(Y/10))-pi(floor(Y/11))] * log(X)/X
  -> 4/10-4/11 = 2/55.
~~~

Therefore the limit in (52) is 2/6-2/55=49/165. In particular T_R is eventually strictly positive. For every R>=7 it is nonnegative, and it is positive whenever L_R is nonempty. No unproved claim that every such interval contains a prime is needed.

**D4. Top-fibre and birth restoration.**

The same calculation shows why the old top fibre cannot be ignored. Its old quotient is 1 and mass is -1; after doubling its quotient is in {4,5,6,7}, whose Mertens values are (-1,-2,-1,-2). Its new surviving-owner mass is again +1 or +2.

For the complete K=2 -> 11 packet, put

~~~text
I_R = -sum_(prime floor(X/3)<p<=X) M(floor(Y/p)),
B_R = -sum_(prime X<p<=Y) M(floor(Y/p)).
~~~

Every term of I_R is +1 or +2. The new-prime population has quotients 1,2,3 and exactly

~~~text
B_R = -pi(Y)+pi(floor(Y/2))+pi(floor(Y/3))-pi(X),
P_(2R)(11)=I_R+B_R.                                    (59)
~~~

Fixed-dilation PNT gives the consistency check

~~~text
I_R ~ (1157/1155) X/log X,
B_R ~ -(5/3) X/log X,
I_R+B_R ~ -(256/385) X/log X.                           (60)
~~~

These fixed-depth PNT consequences are not claimed as a new analytic estimate. They show that coherent positive inherited fibres and negative new-prime mass are both macroscopic. Their mutual signed interaction and the smooth complement remain essential.

**D5. Eliminate terminal coordinates and restore the quadratic terms.**

Subtract (54) across the two depths at each scale. Define

~~~text
dP_R=P_R(2)-P_R(1)=0,
dU_R=U_R(2)-U_R(1)=0,
dP_(2R)=P_(2R)(11)-P_(2R)(7)=T_R,
dU_(2R)=U_(2R)(11)-U_(2R)(7)=-T_R.
~~~

Thus the terminal-free full rectangle is exactly zero, while its two components are nonzero and opposite. At quadratic level,

~~~text
(dP_(2R)+dU_(2R))^2
 = T_R^2+T_R^2-2T_R^2=0.                               (61)
~~~

At each individual depth the original terminal square remains

~~~text
M(X_R)^2=P_R(K)^2+U_R(K)^2+2P_R(K)U_R(K).               (62)
~~~

No diagonal, off-diagonal, anchor or cross-generation term has been discarded. Equations (61)-(62) are not the repository's centered NNS covariance definition; they are the exact scalar square of this SAT decomposition.

### E. Quantitative consequence

The new uniform restriction is (51), and the independent quantitative obstruction is (52). A genuine complete zero layer can acquire order R^2/log R signed mass under an exactly aligned two-scale return. Therefore neither zero-layer persistence, homogeneous old-layer domination, nor a power-smaller unreturned boundary error can be used on this carrier.

The full complementary rectangle has the same magnitude and opposite sign. Both component squares have order R^4/(log R)^2 and are canceled by their mixed term. This is precisely why a favorable local sign cannot be promoted to global payment.

No upper estimate for the complete Mertens, canonical VF, sharp shell, FINITE-AC or JOH objective improves in this run. The stronger project-level PR #1073 bound is existing upstream evidence and is not credited to (50)-(62).

### F. Falsification and circularity review

**Exact small witness.** At R=7, X=48, Y=195:

| Prime p | Old quotient | Old mass | New quotient | New mass |
| ---: | ---: | ---: | ---: | ---: |
| 17 | 2 | 0 | 11 | 2 |
| 19 | 2 | 0 | 10 | 1 |
| 23 | 2 | 0 | 8 | 2 |

Thus N_7=3 and T_7=5. Every prime is greater than the new root 14, and every displayed cofactor is smaller than its owner.

The complete endpoint reconstruction is:

| Root | Depth | P | U | P+U |
| ---: | ---: | ---: | ---: | ---: |
| 7 | 1 | -6 | 3 | -3 |
| 7 | 2 | -6 | 3 | -3 |
| 14 | 7 | -9 | 3 | -6 |
| 14 | 11 | -4 | -2 | -6 |

At root 14, the original mixed term 2PU changes from -54 to +16 as the depth changes, while the full square stays 36:
81+9-54=36 and 16+4+16=36. This refutes any inference that an isolated split's mixed-term sign is invariant under exact regrouping.

**Preregistered finite checks.** Exploratory roots 7..64; held-out roots 65..128 and 257,317. Exact integer arithmetic checked 124 roots and 1,940 admissible cutoff alignments with dilation factors 2,3,4. Maximum sieve endpoint was 401955. Independent physical-integer sums, using largest-prime ownership, checked the smooth/rough reconstruction at roots 7,8,16,65. Trial-factorization Mobius values through 195 independently checked the small witness.

| R | N_R | T_R |
| ---: | ---: | ---: |
| 7 | 3 | 5 |
| 8 | 3 | 6 |
| 16 | 8 | 14 |
| 64 | 91 | 160 |
| 65 | 96 | 171 |
| 128 | 307 | 548 |
| 257 | 1074 | 1916 |
| 317 | 1571 | 2793 |

These finite checks verify implementations and refute the universal homogeneous claim; they are not the proof of the asymptotic. The asymptotic follows from the exact formula and fixed-dilation PNT.

**Novelty and scope audit.** The zero M(2) fibre, full-layer/terminal identity, prime-window reindexing, native PNT and 18349 crossing were already established and are explicitly reused. The additional statement is the aligned root-dilation map and its coherent 2 -> {8,9,10,11} activation with exact 49/165 coefficient. Relevant original declarations and targeted repository searches were checked; no matching theorem was located. This is not an exhaustive originality claim.

The result preserves strict root cutoffs, both square-minus-one endpoints, the top cofactor 1, squareful zeros, actual prime labels, their physical integers and exact complements. It uses no independence, random-sign substitution, cloned history or target-sized supplier. It does not falsify the valid 18349 crossing, an eventual first-bad argument, general cross-scale compensation, or the canonical theorem.

Reproducer: Python 3.12.14; SHA-256 a75678a69054ffce72d7e594faf02529b9dee30e51be77823fe5bca5357c18f6. Its complete source is embedded after the resume capsule. Owner performed no Lean execution.

### G. Conceptual interpretation

A complete signed fibre is not a sufficient state variable for its future arithmetic return. Its zero can conceal a fixed, highly coherent family of newly admitted cofactors. Tracking only the old scalar discards this information even when the owner and the prime cutoff remain unchanged.

The square-minus-one clock makes this especially transparent: it permits an exact, not approximate, alignment of prime boundaries under root dilation. The failure is therefore intrinsic to signed cofactor completion, not an endpoint-rounding artifact.

Conversely, complete restoration still prevents this coherence from becoming a global theorem. The return complement changes by exactly the opposite amount. The correct next mechanism must constrain an actual signed interaction beyond an unweighted depth rectangle.

### H. Competing mechanisms

| Mechanism | Established / missing | Obstruction and decisive test | Disposition |
| --- | --- | --- | --- |
| Bounded fixed-depth crossing | Established crossing and exact terminal equivalence; no independent tail bound | Preserve 18349 and residual <21; do not re-derive them | Retain infrastructure, not a gain supplier |
| Exactly aligned two-scale zero-layer contraction | Exact cutoff map proved; contraction false | R=7 gives 0 -> 5; asymptotic defect 49/165 | ABANDON homogeneous form |
| Terminal-free full depth rectangle | Exact identity zero | Restore U and the -2T_R^2 cross term | IDENTITY_ONLY |
| Joint inherited/new-prime/smooth compensation | Genuine source map (57)-(59); no new global estimate | All three populations can be large; norming them separately loses compensation | CONTINUE with a quantitatively specified signed input |
| Growing-depth centered prime-window estimate | Exact partial source below; only inherited absolute envelope known | Fixed-depth principal modes must be subtracted exactly; growing-parameter uniformity is missing | Exploratory next SAT candidate, not a narrowed team campaign |

The next growing-depth candidate does not replace the protected VF-LOW and JOH workspaces.

### I. Specialist handoffs

**Coordinator / Proof Architect:** record claim 20261103-owner-1 as a genuine arithmetic obstruction to homogeneous two-scale layer propagation, with exact common-cutoff realization. The requested terminal-elimination test has been completed: this rectangle yields no extra restriction on the two terminal Mertens values. SAT coverage is restored. Do not classify the positive 49/165 component as a global gain or a global impossibility theorem.

**Analytic Type II:** on a future appropriate turn, examine the precise growing-band prime-error functional in section J. Fixed-depth native PNT proves (52)/(60) but gives no uniform growing-depth power saving. Preserve the separate due NYMAN assignment; this report does not redirect it.

**Finite Wheel & Incidence:** the exact floor identity (55) may be useful for real cutoff alignment. Verify that any proposed generalization retains the a^2-1 correction and one owner per physical integer. The old quotient-two family is a compulsory test for zero-state compression, not a request to repeat CORR4 incidence scans.

**Prime Census:** no larger supportive scan is requested. The embedded R=7 witness suffices to reject homogeneous transfer. A new experiment should be preregistered only after a specific growing-depth centered estimate or a signed complete recurrence is proposed.

**Adversarial Referee:** independently audit (55), the strict admission B>=aR, the cofactor interval 8..11, the exact prime-count exception formula, the 49/165 limit, and the all-return cancellation (61). Separate verdicts for the source map, quantitative obstruction and absence of endpoint improvement. This report is SELF_AUDIT until that review occurs.

**Lean Verification:** no new branch is requested. After independent acceptance and utility review, the small finite target is the exact identity (50), count bounds (51), and the R=7 homogeneous-control falsifier, using the existing full-layer and reciprocal-count APIs. The PNT asymptotic is secondary. Preserve active proof priorities and human-only merge.

### J. First independently missing lemma

The canonical SAT tail bound remains target-equivalent, so it is not relabeled as a smaller elementary lemma.

A specific nonterminal input for the next SAT investigation is the following growing reciprocal-band error, with the original floors and signed Mertens coefficients retained. For integer R>=16 let

~~~text
Y=(2R)^2-1,  D=floor(sqrt R),
L_R(d)=Li_2(floor(Y/d))-Li_2(floor(Y/(d+1))),
E_R=-sum_(D<=d<2D) M(d)[N_(2R)(d)-L_R(d)].              (63)
~~~

Here Li_2(t)=integral_2^t du/log u. The exact original band is

~~~text
P_(2R)(2D-1)-P_(2R)(D-1)
 = -sum_(D<=d<2D) M(d)L_R(d) + E_R.                     (64)
~~~

This is a prime-count/model split, not a replacement of actual primes by density. The band is strictly above the new root; all its original admissions hold. The model term, remaining depths, births, smooth population and mixed terms are still unpaid in any global application.

For any already certified fixed envelope |M(n)|<=C n^b, 1/2<b<1, positivity and telescoping of the two counting/model measures give only

~~~text
|E_R| <<_b C Y D^(b-1) <<_b C R^((3+b)/2).              (65)
~~~

Indeed |M(d)|<=C(2D)^b and the total prime-plus-Li variation over this band is O(Y/D). Main's 7/8 positive-loss bound supplies exponent 31/16+epsilon. The existing strict PR-head improvement merely changes this inherited exponent to 31/16-gap/2, after choosing its fixed envelope; that substitution is not a new SAT saving.

The first independently missing candidate inequality is a fixed delta>0 improvement over (65), uniform in the growing D=floor(sqrt R), proved from additional signed prime/cofactor arithmetic rather than by substituting a better prefix exponent:

~~~text
exists delta>0, forall epsilon>0, exists C_epsilon,R_epsilon,
forall integers R>=R_epsilon,
  |E_R| <= C_epsilon R^((3+b)/2-delta+epsilon).           (OPEN)
~~~

This controls only an explicitly defined proper source band. It is not claimed equivalent to RH or sufficient alone for any complete endpoint gain. Its value would be an independently improved part of a varying-depth transfer. A complete consumer and all complementary signed interactions would still need to be supplied. No such power saving was proved here.

### K. Next-run resume capsule

~~~text
CLAIM: 20261103-owner-1, equations (50)-(65).
RUN: scheduled 2026-11-03 00:09 EST; RUN_ID_UNAVAILABLE.
MAIN: 8e5d64ae689b39dabd2a4f6eb33efe4d5d192015.
ENGINE: 6fce99c61efb5b2a73c0cb1f1464f09b351fcd55.
SELECTED: overdue SAT; actual two-depth/two-scale derivation completed.
PROJECT_GATE: VERIFIED_ETA_ON_PR1073_HEAD_ONLY, adopted at unchanged reviewed
              head with refreshed terminal source and CI; not on main.
THIS_RUN_GAIN: NONE; complete endpoint improvement UNKNOWN from this work.
NEW_PROOF: exact K -> a^2(K+1)-1 cutoff alignment; true quotient-two layer
           changes from zero to T_R ~ (49/165) X/log X under root doubling.
FALSIFIER: R=7, primes 17,19,23, old mass 0, new mass 5.
FULL_RETURN: coupled-tail rectangle -T_R; restored rectangle and its square 0.
REVIEW: SELF_AUDIT; independent Referee PENDING; no new Lean execution.
SAT_NEXT: growing-band E_R in (63); test a new signed estimate beyond (65).
ROTATION: latest three substantive Owner turns are VF-LOW / JOH / SAT.
NEXT_DISTINCT_ROUTE: VF-LOW; resume the actual frozen-field/fragment bridge
                     from Coordinator C20-C25, not the already paid K norm.
OTHER_WORKSPACE: JOH colored-backlog identity and fixed-weight no-go remain.
CANONICAL_VF: OPEN. SHARP_SHELL_GAIN: OPEN. RH: OPEN.
~~~

Continuity at agent-reports snapshot f50a849226f7c095c16f91e794de976ac2f05706:

| November 2 report | Blob | Relevant evidence consumed |
| --- | --- | --- |
| Coordinator 00/90 | 1e932d4ce0eb0fd2c5f4507f6b111194d633eb32 | Latest SAT assignment; C20-C25; PR-only gate and coverage correction |
| Owner | abfe546d72b151f4cd200fc61de3197efe23a65c | Claims 1-3; sparse convolution and JOH no-gos |
| Analytic | 8e48b59611aa1d0bfa3577ed0a4a3bc0d0fcae73 | Claim 3 cutoff freezing; no prefix-to-shell inference |
| Wheel | abf8ac8c22a708886183849552c90dd62787ac8d | Parity obstruction and claim 3 support/factorial frontier |
| Census | 2cd84c57ab18d923e97368764f29f4ccd2ec3bb3 | R=18988 literal SQRT-BURST falsifier; no all-scale fit |
| Referee | 814af1684df66e6ac99b8df1f102cb592b316f89 | Claim 3 exact-head strict-gain verdict; previous scope repairs retained |
| Lean | 02d19d792e26f072004cb5909f149538752626e9 | Merged 1070/1071 history; latest run 3 only a partial checkpoint |

TODAY=PENDING for upstream reports at intake. YESTERDAY=CARRY_FORWARD is the actual November 2 material above. The older November 1 Owner report was additionally retrieved solely to resume the SAT derivation, not misdated as yesterday. External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 contains no later entry than October 18; its historical all-R payment no-go and original-source safeguards are preserved, not reclassified as a ban on signed cross-scale methods.

Publication scope: only this authorized daily Owner report on agent-reports. No main, Lean source, other report, issue, branch, PR, workflow, schedule or permission was modified. GitHub reporting was available; no publication blocker occurred. Final commit and readback receipt is recorded after publication.

### Reproducible Exact Regression

The following is the executed script, retained in the authorized report so continuation does not depend on a private scratch file.

~~~python
"""Exact regression for the source-faithful SAT depth-dilation claim.

Exploratory roots: 7..64. Held-out roots: 65..128, 257, 317.
All identities are checked before any table is printed. No exponent is fitted.
"""

from bisect import bisect_right
from fractions import Fraction
from math import isqrt


ROOTS = list(range(7, 129)) + [257, 317]
LIMIT = (2 * max(ROOTS)) ** 2 - 1
mu = [1] * (LIMIT + 1)
mu[0] = 0
largest = [1] * (LIMIT + 1)
primes = []
for p in range(2, LIMIT + 1):
    if largest[p] != 1:
        continue
    primes.append(p)
    for n in range(p, LIMIT + 1, p):
        largest[n] = p
        mu[n] = -mu[n]
    for n in range(p * p, LIMIT + 1, p * p):
        mu[n] = 0
M = [0] * (LIMIT + 1)
for n in range(1, LIMIT + 1):
    M[n] = M[n - 1] + mu[n]


def pi(x):
    return bisect_right(primes, x)


def packet(r, k):
    x = r * r - 1
    return -sum(
        M[d] * (pi(max(r, x // d)) - pi(max(r, x // (d + 1))))
        for d in range(1, k + 1)
    )


def smooth(x, boundary):
    return sum(mu[n] for n in range(1, x + 1) if largest[n] <= boundary)


def trial_mu(n):
    sign = 1
    for p in range(2, isqrt(n) + 1):
        if n % p:
            continue
        n //= p
        sign = -sign
        if n % p == 0:
            return 0
    return -sign if n > 1 else sign


assert [M[n] for n in [2, 8, 9, 10, 11]] == [0, -2, -2, -1, -2]
for n in range(1, 196):
    assert mu[n] == trial_mu(n)

rows = []
for r in ROOTS:
    x, y = r * r - 1, (2 * r) ** 2 - 1
    fibre = primes[pi(x // 3):pi(x // 2)]
    assert all(p > 2 * r for p in fibre)
    assert all(x // p == 2 and 8 <= y // p <= 11 for p in fibre)
    old = -sum(M[x // p] for p in fibre)
    lifted = -sum(M[y // p] for p in fibre)
    explicit = 2 * (pi(x // 2) - pi(x // 3)) - (pi(y // 10) - pi(y // 11))
    assert old == packet(r, 2) - packet(r, 1) == 0
    assert lifted == packet(2 * r, 11) - packet(2 * r, 7) == explicit
    assert len(fibre) <= lifted <= 2 * len(fibre)
    assert x // 2 == y // 8 and x // 3 == y // 12
    survivors = primes[pi(x // 3):pi(x)]
    born = primes[pi(x):pi(y)]
    inherited = -sum(M[y // p] for p in survivors)
    birth = -sum(M[y // p] for p in born)
    assert all(-M[y // p] in [1, 2] for p in survivors)
    assert birth == -pi(y) + pi(y // 2) + pi(y // 3) - pi(x)
    assert inherited + birth == packet(2 * r, 11)
    u1, u2 = M[y] - packet(2 * r, 7), M[y] - packet(2 * r, 11)
    assert u2 - u1 == -lifted
    assert lifted ** 2 + (u2 - u1) ** 2 + 2 * lifted * (u2 - u1) == 0
    if r in [7, 8, 16, 64, 65, 128, 257, 317]:
        rows.append((r, len(fibre), lifted, M[x], M[y]))

cut_checks = 0
for a in [2, 3, 4]:
    for r in range(3, 65):
        x, y = r * r - 1, (a * r) ** 2 - 1
        for k in range(1, (r - 1) // a):
            assert r >= a * (k + 1) + 1
            kp = a * a * (k + 1) - 1
            b = x // (k + 1)
            assert b >= a * r and b == y // (kp + 1)
            common = primes[pi(b):pi(x)]
            births = primes[pi(x):pi(y)]
            increment = -sum(M[y // p] - M[x // p] for p in common)
            increment -= sum(M[y // p] for p in births)
            assert packet(a * r, kp) - packet(r, k) == increment
            cut_checks += 1

# Independent physical-integer and cofactor reconstructions at frozen fixtures.
for r in [7, 8, 16, 65]:
    for a, k in [(2, 1), (2, 2), (3, 1)]:
        if r < a * (k + 1) + 1:
            continue
        x, y = r * r - 1, (a * r) ** 2 - 1
        b = x // (k + 1)
        kp = a * a * (k + 1) - 1
        for root, endpoint, depth in [(r, x, k), (a * r, y, kp)]:
            rough = sum(mu[n] for n in range(1, endpoint + 1) if largest[n] > b)
            assert rough == packet(root, depth)
            assert smooth(endpoint, b) + rough == M[endpoint]

r = 7
x, y = r * r - 1, (2 * r) ** 2 - 1
print('roots_checked', len(ROOTS), 'cut_lock_checks', cut_checks, 'limit', LIMIT)
print('R, old_fibre_count, lifted_mass, M(X), M(Y)')
for row in rows:
    print(row)
print('R7 primes', primes[pi(x // 3):pi(x // 2)])
print('R7 quotient_and_weight', [(p, x // p, y // p, -M[y // p]) for p in primes[pi(x // 3):pi(x // 2)]])
print('R7 packets', [(root, k, packet(root, k), M[root * root - 1] - packet(root, k)) for root, k in [(7, 1), (7, 2), (14, 7), (14, 11)]])
constant = 2 * (Fraction(1, 2) - Fraction(1, 3)) - 4 * (Fraction(1, 10) - Fraction(1, 11))
assert constant == Fraction(49, 165)
print('PNT_coefficient', constant)
cohort = 2 * (1 - Fraction(1, 3)) - (1 - Fraction(4, 5))
cohort -= 4 * (Fraction(1, 6) - Fraction(1, 7))
cohort -= 4 * (Fraction(1, 10) - Fraction(1, 11))
birth_coefficient = -4 + Fraction(4, 2) + Fraction(4, 3) - 1
assert cohort == Fraction(1157, 1155)
assert birth_coefficient == -Fraction(5, 3)
assert cohort + birth_coefficient == -Fraction(256, 385)
print('cohort_birth_total_coefficients', cohort, birth_coefficient, cohort + birth_coefficient)

~~~

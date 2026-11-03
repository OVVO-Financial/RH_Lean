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


### Publication Verification

The early checkpoint was committed as 59ac3074afce52683b2d6e3d53a6ba2926e8bb47 and read back exactly at blob c2b3bf7de273d30457f1e26d90e66eee5345b3bb.

The completed mathematical synthesis was committed as 442d25ff82f127be715a9021e275c81edd3ac552 at 2026-11-03T05:28:59Z. Readback returned blob 32cdd51ecfcbb8f4761b090c9b8cfc685902de6e and exactly matched the submitted 36,278 characters. Commit inspection confirmed that only research/agent_reports/2026-11-03/10-owner-payment.md changed. The report contains all A-K sections, claim 20261103-owner-1, equations (50)-(65), the exact witness, full signed reconstruction, current PR evidence and the executed reproducer. ASCII/control-character and balanced-code-fence checks passed.

This receipt records publication only. It does not convert the new paper proof into independent Referee acceptance or Lean verification, and it adds no endpoint gain.

Published report: https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-11-03/10-owner-payment.md


---

## Scheduled Continuation Checkpoint - 2026-11-03 08:09 EST (-0500)

**Execution:** PARTIAL / IN_PROGRESS; scheduled invocation, RUN_ID_UNAVAILABLE. This is a new invocation, preserving the completed 00:09 SAT run and claim 20261103-owner-1 above.

**A. Mathematical question.** Resume the due VF-LOW actual-prime source, following Coordinator 20261103-coordinator-1. Investigate whether a proper current semiprime class admits a once-only historical-prime pairing with its original VF weights, and whether first-lower-escape chronology supplies anything beyond that proper-class restriction after the full historical complement and quadratic mixed terms return. Do not promote eligible ancestry to masked/clipped returned-cell admission.

**B. Authority.** Latest actual main is 8e5d64ae689b39dabd2a4f6eb33efe4d5d192015. AGENTS blob 9fa5e9519e2fb6dde22217aa2a18982dafef373a; proof-contract blob 88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a; engine blob 6fce99c61efb5b2a73c0cb1f1464f09b351fcd55. Canonical actual-prime VF von Koch bound remains OPEN. Source audit f7d046d8d94962e18f794deee7e33ce7508a0e74 explicitly makes the full #915 payment equivalent to absence of first bad; it is not an independent missing lemma.

**C. Continuity and scope.** TODAY=AVAILABLE for all seven roles; YESTERDAY=CARRY_FORWARD with retrieved Nov 2 reports. Own previous blob 5c085d12ca455327b2a9ab42d7e55a1b6b2d631b; Coordinator today f9c04a1099048cd0b02fd5264b753e916cbcd521. External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 has no new entry after Oct 18. Latest open PR heads: #1073 9cbfce5295343bcb411e6d2cb159b59995cd985b (draft), #1074 5f53bca7d728576efcbbf2762885b7720e89aef7 (draft), #1075 c54bce957fa8c49ca944852b3a1b0e143f2d693b and #1076 f676c9b13960f8c80b68bdf35a5f04b07370e228 (non-draft). Earlier formal gain verdicts are scoped PR-head evidence, not main or a gain from this run.

**D. Preregistered stress test and next step.** Preserve the actual current odd seats, strict square boundaries, least-prime owner, once-only historical prime, block of that historical occurrence, original seat weight, full complement and original compressed norm restoration. Test same-block collisions and the first range where a uniform pair-sign claim is legitimate; a first-bad-conditioned counterexample requires that actual premise and will not be inferred from an unconditional example. Then attempt to aggregate the proper-class inequality without spending a historical prime twice across blocks. Read current definitions before choosing the threshold. Any new proof is PAPER_PROOF / SELF_AUDIT pending independent review, not Lean certified.

**Deployment and route record.** Current engine consumed; selected VF-LOW by actual last rotation VF-LOW / JOH / SAT. Next distinct route remains JOH. No local Lean, proof mutation, PR mutation, schedule change or other-agent launch. Shell clone was unavailable (HTTP tunnel 403); authenticated GitHub reads work, so this does not block research or publication.


---

## Scheduled Continuation Final Synthesis - Claim 20261103-owner-2

**Invocation:** SCHEDULED, begun 2026-11-03 08:09:02 EST (-0500), RUN_ID_UNAVAILABLE. This continues the verified 08:09 checkpoint, not the earlier 00:09 SAT run.
**Status:** PAPER_PROOF / SELF_AUDIT; FINITE_COMPUTATION with rational interval certificates; REFUTED at the stated unconditional supplier scopes. Independent Referee review and new Lean formalization: PENDING. **Net new endpoint gain: UNKNOWN; no improvement claimed.**

### A. Most Important Mathematical Development

**Ancestry alone has finite signed capacity, and genuine physical VF demand can exceed it even when every prime ancestor is available.** For infinitely many genuine primes q, construct distinct current composites n=m*q with m supported on {3,5,7}, in one actual dyadic square-root run. Every n is squareful but not a perfect square. Their positive original VF weight grows without bound; their entire prime-divisor ancestry is only {3,5,7,q}. A once-only allocation from negative historical prime divisors cannot pay this population, even after granting a full unit to each of those four primes. This is O4 below, not a counterexample to RH or to a first-bad-conditioned assertion.

An exact finite witness uses q=1000000000039 and 118 constructed composites. Their total original weight lies in [4.31356094,4.31356095], exceeding the enlarged capacity 4. Primality, factor support, strict square boundaries and logarithmic weight intervals were checked using exact integer/rational arithmetic. No scan through the enormous endpoint was needed or claimed.

The positive result is O1: for every run A<=r<B of at most floor(log_2(A))/3 blocks, A>=1024, the complete current large-prime composite population groups with one historical prime per label. Every nonempty grouped packet is < -799/4096 in VF-minus-prime sign, uniformly in all factor depths, including squareful cofactors. O2 proves a logarithmic horizon is the correct order for this particular once-only mechanism: an explicit prime family has packet limit c-1 when its run length is floor(c log q).

O3 identifies the admission limitation: in the original final half-history, only cofactor-3 descendants have their prime tag present. Every cofactor >=5 requires opening the earlier anchor. The short-run result is therefore not free #915 capacity or a returned-cell theorem.

### B. Current Authoritative Objective

Main inspected: **8e5d64ae689b39dabd2a4f6eb33efe4d5d192015**. Authority hashes:

| File | Blob SHA |
| --- | --- |
| AGENTS.md | 9fa5e9519e2fb6dde22217aa2a18982dafef373a |
| CURRENT_PROOF_CONTRACT.md | 88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a |
| Task selector | d05c327ae694ea54b599dab0a21032a056b521f1 |
| Broad-search policy | b5c063c51556ba57c4b25bcc380a606fa8daa207 |
| Complete-return contract | 16838f7f3c8724b970f8b8ece0bceaab9418066d |
| Persistent research engine | 6fce99c61efb5b2a73c0cb1f1464f09b351fcd55 |
| Role prompts | 7366bb71e8a97fd11689a64311c7f590edeb1adf |
| All-vector source directive | 0b8733cbb3eabeb0954df4a77cfccde25f54c4a0 |
| Dynamic protocol | fe21d2824491fb001726311f736b9825a8f97eca |
| Multirun policy | 643cfd596116720a8e5b1efc07a6124b55d70946 |

The canonical objective remains

~~~text
exists C>=0, forall integer R>=2,
  |pi(R^2)-VF_can(R^2)| <= C R log R.
F_R=sum_(2<=r<R)(2r+1)/log(r^2+r+1/2),
D_R=pi(R^2)-F_R,       D_can(R)=D_R-sqrt(2).
~~~

This run stays on actual-prime VF-LOW. It does not identify w_r-1_Prime(n) with mu(n), the hybrid mu*kappa field, or ideal-character coefficients. The canonical quadratic correction remains D_can^2=D_R^2-2sqrt(2)D_R+2. The canonical von Koch consumer retains its explicit classical-criterion interface.

The first-lower-breach necessary condition P_R+S_R+K*((R+1)log(R+1)-R log R)<m_R, S_R=D_R+KR log R, is established infrastructure, not a new result here. Full #915 payment is audited as equivalent to no first bad, not an independently smaller supplier.

Material original Lean definitions/theorems inspected at main:

| File under research/ | Blob SHA | Scope used |
| --- | --- | --- |
| VF_MID_VON_KOCH_BRIDGE.lean | 32d4b0d74ecadc9780b9841d40357f6ff02369f0 | Original midpoint, mass and finished sum; definitions excerpt |
| VF_MID_ODD_FRACTIONAL_CLUSTER.lean | 942badff45c03d2a9e97789b57d1bd8052232191 | Odd seats, exactly r seats, w_r=m_r/r |
| VF_MID_SIGNED_SEAT_CHARGE.lean | 87a6654a4a4337b409fde69aa15d7264d8b721b6 | Literal signed charge, prime/composite cases |
| VF_MID_FIRST_BAD_HISTORY_COMPRESSION.lean | d9cc97541f9713b6eec8df30885e9ca830478e59 | Historical anchor and run telescope |
| VF_MID_915_EXACT_HISTORICAL_NNS_COMPRESSION.lean | 6cc6b2a9d25279dd44fb65cb222f5d6846a912d4 | Squared-denominator restoring price |
| VF_MID_915_SOURCE_PAYMENT_CONTENT_AUDIT.lean | f7d046d8d94962e18f794deee7e33ce7508a0e74 | Two-number source and target equivalence |
| VF_MID_THIRTY_FACTOR_RANGE_LOWER_GATE.lean | ab0f7d0adfb4b71c1b1e36447b2373a56b44ead4 | Existing near-wall necessity |
| VF_MID_FIRST_BAD_WEIGHTED_OWNER_FUBINI.lean | 4679d7edae521dd4d9f0238aa4201445b1fdb9a9 | Squarefree active carrier; omitted/restoring terms |
| VF_MID_FIRST_BAD_RESTORING_DECOMPOSITION.lean | 41ca385cb2bd0706db21007e19cd2b0b1aaa4b3e | Full normalized numerator D_(R+1)^2 |
| VF_MID_HISTORICAL_PRIME_MULTIPLICITY.lean | 71197c4b3a72a286efe32018b74d1fc5aff46222 | Prior small-owner uniqueness/multiplicity |
| VF_MID_OWNER_SIGNED_PAIR_BOUNDS.lean | f77418156653f1d93c0bcd4ca6587fc0987e3b95 | Prior restricted pair bounds |
| VF_MID_SAME_TAG_SHARP_PACKET.lean | 9f69aa4f5eaa278d4cf176397abb5cabf4ae832f | Prior small-prime-owner packet limits |
| VF_MID_SAME_TAG_DYADIC_FIBRE.lean | 2b72e43ae4de32b7fac44c4c559ca6597488db6d | Prior restricted prime-cofactor counts |
| VF974_ORIGINAL_FIRSTBAD_GLOBAL_RESIDUAL_DOMINANCE_20261018.lean | 26fd4533e37390326b96740182f5900f9057b305 | Existing positive first-bad anchor obstruction |
| VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb | Canonical target and classical interface |

**Formal frontier, separate from this result.** Main includes merged #1070-#1072. Open #1073/#1074 remain draft; #1075/#1076 are non-draft and unmerged. Exact-head CI refreshed: #1073 9cbfce5295343bcb411e6d2cb159b59995cd985b, 13 successes; #1074 5f53bca7d728576efcbbf2762885b7720e89aef7, 7; #1075 c54bce957fa8c49ca944852b3a1b0e143f2d693b, 9; #1076 f676c9b13960f8c80b68bdf35a5f04b07370e228, 8. No workflow launched.

PR #1073's strict Mertens file was retrieved at blob b33a4883e1ddb0551b0f11f062bce46680d87450, including unconditional native_mertens_uniform_strict_gap. PR #1076's endpoint file was retrieved at blob 115d2b19148fa37c329329f153eceea512ade377, including construction before quantified Mertens losses/prefixes. Existing independent acceptance belongs to 20261102-referee-3 and 20261103-referee-1; their standard-axiom/dependency audits and today's Lean evidence are carried forward. This run inspected terminal source/status, not that entire analytic proof independently. Programme gate: VERIFIED_ETA / PR_HEAD_ONLY at reviewed heads. Main and this VF claim receive no such upgrade. Protected portfolios remain.

### C. Structural Hypotheses Investigated

Resume point: Coordinator 20261103-coordinator-1, section H, requested a prime-side ancestry restriction with original historical/current weights. Previous VF-LOW claim 20261102-owner-2 was hybrid-Mobius work without that bridge; it is retained, not promoted.

1. A short root run has enough once-only historical large-prime charge for all its descendants, including nonprime/squareful cofactors. This survives as O1.
2. First-escape chronology or simple concatenation extends that capacity to long runs. Unconditional concatenation fails, with the logarithmically sharp O2 family. No actual first-bad instance is claimed.
3. Other historical prime divisors can always repair the long-run deficit. This enlarged ancestry-only supplier fails by O4.

The new content is not the old isolated semiprime gap, fixed-cofactor cut reassembly, or a renamed endpoint inequality: it is a growing short-run bound on all factor depths, its asymptotic horizon, and an all-prime-ancestor capacity obstruction on genuine squareful physical seats.

### D. Mathematical Derivation

#### O1. Uniform All-Depth Short-Run Signed Bound

For A>=1024, k=floor(log_2 A), 1<=L<=floor(k/3), set B=A+L and retain

~~~text
C(A,B)={(r,n): A<=r<B, r^2<n<(r+1)^2, n odd},
w_r=(2+1/r)/log(r^2+r+1/2), c(r,n)=w_r-1_Prime(n).
E(A,B)={(r,n) in C(A,B): n composite, P+(n)>=B}.
Q(A,B)={P+(n): (r,n) in E(A,B)}.
E_q={(r,n) in E(A,B): P+(n)=q}, h_q=floor(sqrt q).
P_q=w_(h_q)-1+sum_((r,n) in E_q)w_r.
~~~

Each n in E is uniquely n=a*q with a>=3 odd, a<q, and q occurring once: n<B^2<=q^2, and two primes >=B cannot divide n. The actual least-prime owner remains minFac(a); reindexing does not change that owner or create an occurrence. Cofactors need not be prime or squarefree.

All tags are historical before root A: q<B^2/3<=16A^2/27<A^2, since k<=A and B<=4A/3. Thus h_q<A. Also q>=B>A>=1024 gives h_q>=32, so each q is a genuine prior odd-seat prime, not a square. Distinct tags are distinct historical integers.

For fixed q,r there is at most one descendant: two odd multiples differ by at least 2q>=2(r+1), greater than the band's width 2r+1. Hence |E_q|<=L. This proves multiplicity without cloning history.

Using log 2>2/3, for r>=A>=2^k,

~~~text
w_r < 3(2+1/1024)/(4k)=6147/(4096k).
~~~

For h_q>=32, log(h_q^2+h_q+1/2)>20/3 and 2+1/h_q<=65/32, giving w_(h_q)<39/128. Therefore

~~~text
P_q < -1+39/128+(k/3)*6147/(4096k)
    = -799/4096 < -3/16,
P(A,B):=sum_(q in Q)P_q <= -(799/4096)|Q|.             (66)
~~~

The aggregate includes empty Q and is strict for nonempty Q. Constants and factor-depth coverage are uniform in A,B,q. This is an actual-weight signed proper-class estimate, not an NNS half-bound.

#### O2. Sharp Order Of The Logarithmic Horizon

Let q be an odd prime, B=q, A=q-L, with L>=2, L<q/2 and L^2<2q. The COMPLETE q-descendant fibre is

~~~text
n_j=q(q-2j), j=1,...,L-1,
floor(sqrt(n_j))=q-j-1.
~~~

Indeed n_j<(q-j)^2 and n_j-(q-j-1)^2=2q-(j+1)^2>0. Conversely every odd cofactor a<q is q-2j; n_j>A^2 is equivalent to j<=L-1 under L^2<2q. Thus

~~~text
P_q(q-L,q)=w_(floor(sqrt q))-1
              +sum_(j=1..L-1)w_(q-j-1).               (67)
~~~

Fix c>0 before q and choose L=floor(c log q). The hypotheses hold eventually. Uniformly for r=q+O(log q), w_r log q ->1, and w_(floor(sqrt q))->0. Therefore along genuine primes

~~~text
P_q(q-floor(c log q),q) -> c-1.                       (68)
~~~

Only elementary weight asymptotics and infinitely many primes are used, not PNT or random signs. For c<1 the packet is eventually negative; for c>1 it is eventually positive. No sign assertion at c=1. O1's constant is not claimed optimal, but a universal greatest-prime-only nonpositive packet theorem cannot extend to all c>1 logarithmic lengths or all dyadic lengths.

A coarse dyadic witness is q=2053, A=1026, B=2052. Exactly 770 odd cofactors satisfy A^2<a*q<B^2; all are <q. Since r<B<2^12, midpoint(r)<B^2 and w_r>1/12. Their packet is therefore >770/12-1=379/6.

#### O3. Exact Final Half-History Admission

Let R=B-1 and H=floor(R/2)+1=ceil(B/2), the original half-history starting root. In O1,

~~~text
h_q>=H iff the descendant cofactor a is 3.            (69)
~~~

If a>=5, q=n/a<B^2/5<H^2. Conversely 16k<=2^k<=A for k>=10, so L<=A/48. With A>=1024, H<=(B+1)/2<=25A/48 and 3H^2<A^2. Thus a=3 gives q=n/3>A^2/3>H^2. This covers every descendant, including repeated tags; a tag inside final half-history has only the a=3 descendant.

All a>=5 tags are below the half-history anchor. Counting them as half-run cells is false before masks/clipping are considered. Composite a makes n->q a multi-step factor path, not the single first-owner edge n->n/minFac(n). Squareful a makes n absent from the squarefree active physical carrier in VF_MID_FIRST_BAD_WEIGHTED_OWNER_FUBINI, while its VF charge remains in the omitted/restoring population.

This unconditional admission restriction also holds under a genuine first-bad premise. It neither excludes first bad nor proves masked returned-cell admission.

#### O4. All Prime Ancestors Still Fail Long-Run Capacity

The falsified unconditional supplier permits nonnegative allocations x_(n,p) only at prime divisors p|n, demands sum_p x_(n,p)>=w_(floor(sqrt n)), and spends each historical prime's negative charge at most once. Even enlarging each capacity to 1 cannot make this true on all legal raw populations.

For prime q>=35^96 choose t with 35^(2t)<=q<35^(2(t+1)), so t>=48. For every 0<=b,c<=t put

~~~text
v=5^b 7^c, a=max{j>=0:3^j v<q},
m_(b,c)=3^a v, n_(b,c)=q*m_(b,c),
A=(q-1)/2, B=q-1.
~~~

Because v<=sqrt q and q>=81, a>=2. Maximality yields q/3<m<q. Unique factorization gives distinct m. Since q,m are odd and unequal, m<=q-2. Consequently

~~~text
A^2<q^2/3<n<=q(q-2)<(q-1)^2=B^2.
~~~

Every n is an actual odd composite with unique greatest prime q; q<A^2 is historical. Every n is divisible by 9 and is squareful, but q has exponent one, so n is not a square and no strict square boundary removes it. Its least-prime owner is 3. All prime-divisor ancestors belong to {3,5,7,q}, independently of t.

For r=floor(sqrt n)<B, midpoint(r)<B^2 and w_r>1/log B>1/log q. Hence

~~~text
sum_(b,c)w_(floor(sqrt n_(b,c)))
 > (t+1)^2/log q
 > (t+1)/(2 log 35)
 > (t+1)/12 >=49/12>4.                               (70)
~~~

Here log 35<6 follows from 35<2^6 and log 2<1. Summing any proposed allocations gives demand>4 but enlarged capacity<=4, a contradiction. This is a finite weighted-neighborhood obstruction, not an application of an unverified matching theorem. Demand tends to infinity along primes.

The unit capacities deliberately favor the supplier. Actual negative VF prime charge max(0,1-w_(floor(sqrt p))) is <=1 where the seat exists. Prime 3 belongs to the initial prime-count anchor, not a fictitious r=1 VF seat; a unit is explicitly granted. Primes 5,7 have w_2>1, so their physical VF charges are positive, not negative. The proof does not obtain credit from them. Even adding the other fixed initial-anchor unit cannot repair the unbounded family.

**Finite witness:** q=1000000000039. Use all b,c>=0 with 9*5^b*7^c<=q and the same maximal exponent a. There are 118 distinct cofactors, with total demand in [4.31356094,4.31356095]. Trial division by every prime <=1000000 certifies q's primality. Integer checks certify all factors and locations. This sparse witness does not claim a census up to B^2.

#### O5. Complete Source And Quadratic Restoration

For O1 set X=sum_E w_r, Y=sum_(q in Q)(1-w_(h_q)), and Z equal to the signed sum over EVERY current seat in C(A,B)\E, including primes, other composites and squareful seats. Then

~~~text
P=X-Y, C=-D_A+Y+Z,  -D_B=C+P.                        (71)
~~~

C means exactly the initial anchor -D_2=-2, all prior odd seats up to A except the selected primes Q, and the entire current complement. It is not an unspecified error. Main's physical historical telescope proves this reconstruction.

All cross terms remain:

~~~text
D_B^2=C^2+P^2+2CP,
P^2=sum_q P_q^2+2sum_(q<q')P_q P_q'.                  (72)
~~~

O1's cross-tag products in P^2 are positive, not orthogonal. At a first lower breach D_B<-K B log B, K>=0, the consequence is only

~~~text
C>K B log B+(799/4096)|Q|.                            (73)
~~~

This localizes the necessary pressure into the explicit complement; it does not exclude it. Prior lower safety gives -D_A<=K A log A but no new bound on Y+Z. No first-bad-conditioned counterexample was established.

At the final production root R=B-1 retain

~~~text
Source=D_B=D_R+P_R-m_R,
beta_R=m_R+(1-2w_R)P_R,
TotalMass=(|D_R|+beta_R)^2.
~~~

Opening history into positive mass U and negative magnitude V requires the exact existing correction

~~~text
(U+V+beta_R)^2-(|U-V|+beta_R)^2
 =4UV+2beta_R(U+V-|U-V|).                             (74)
~~~

Equations (71)-(74) return history, anchors, all current complements, squareful terms, and cross-owner/cross-generation interactions. O1 does not bound 2D_B^2-TotalMass or authorize a larger denominator. O4 is a concrete reason squarefree active estimates cannot silently dispose of physical squareful restoration.

### E. Quantitative Consequence

O1 gives a uniform negative mass >=799/4096 per distinct tag on the stated logarithmic run, including multiple real descendants and arbitrary factor depth. O2 identifies an order-sharp length obstruction for the same resource. O4 rejects even the all-prime-ancestor resource on a structured genuine squareful subfamily.

These change the plausible suppliers, but improve no global upper bound for VF, Mertens, sharp shell energy, FINITE-AC, CORR4 or JOH. Concatenation repeats historical q; O2/O4 show why that loss is real. Returning C restores an unpaid signed global interaction.

### F. Falsification And Circularity Review

The early checkpoint registered complete factor-depth, history, collision and first-escape-scope tests. Fixed thin-run roots A=1024,1031,2048,4096 and boundary fixtures q=2053,4099 were chosen before their execution. The subsequently developed smooth-ancestry construction was tested at q=65537 and q=1000000000039; it was not called an upstream preregistered claim.

| A | B | Tags | Descendants | Max multiplicity | Squareful descendants | Tags in half-history | Below anchor |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1024 | 1027 | 1793 | 1963 | 3 | 324 | 161 | 1632 |
| 1031 | 1034 | 1773 | 1952 | 3 | 332 | 160 | 1613 |
| 2048 | 2051 | 3609 | 3923 | 3 | 671 | 296 | 3313 |
| 4096 | 4100 | 9415 | 10580 | 4 | 1826 | 706 | 8709 |

Every current seat was directly factored; an independent enumeration of all candidate prime labels/odd cofactors reconstructed exactly E. Per-block uniqueness, multiplicity, (69), and symbolic coefficient-by-coefficient restoration (71) passed. The all-scale proof is separate from this table.

Selected certified sign intervals for (67):

| q | L | Descendants | Packet interval |
| ---: | ---: | ---: | --- |
| 2053 | 3 | 2 | [-0.47283502,-0.47283501] |
| 2053 | 5 | 4 | [-0.21047960,-0.21047959] |
| 2053 | 7 | 6 | [0.05190948,0.05190949] |
| 2053 | 15 | 14 | [1.10180332,1.10180333] |
| 4099 | 4 | 3 | [-0.39741417,-0.39741416] |
| 4099 | 8 | 7 | [0.08358530,0.08358531] |

The positive fixtures violate O1's length restriction, not O1. None is asserted first bad. The L=1 diagnostic has no current descendant and is not counted as a nonempty packet.

Logarithm certificates use exact range reduction x=2^k y, 1<=y<2, and 40 terms of log y=2sum_(j>=0)u^(2j+1)/(2j+1), u=(y-1)/(y+1), with a geometric upper bound on the positive tail. Reciprocal bounds certify original weights. No floating sign or fitted exponent is used. Final reproducer SHA256: 8276b6de782055fe8542086a79eb451c3e53f14914792705dd76ed6220129acb. Full executed source follows. A scratch-output variable reuse was corrected and the complete script rerun before publication; no mathematical fixture changed.

BLOCK R=549, JOH owner-3/two-owner reversals, SAT R=7 zero-layer activation, and original no-cloning/anchor constraints remain. They were not rerun or relabeled as first-bad witnesses. O4 is NOT a Mobius counterexample: its constructed seats have mu(n)=0 and strictly positive physical VF charge.

### G. Conceptual Interpretation

A historical prime has finite negative physical mass. Multiplication by several fixed small primes creates many distinct real composite occurrences, and their original VF weights can outweigh ALL prime-ancestor capacity. This is deterministic factor-depth/chronology dependence, not a probabilistic phenomenon.

Short-run negativity survives because a large prime occurs at most once per square block and VF weights are logarithmically small. The resulting logarithmic lifetime does not last across long runs. In addition, all but cofactor-3 tags lie behind the compressed half-history anchor. A global argument requires genuinely nonlocal signed compensation, not a longer ancestry-only list or cloned history.

### H. Competing Mechanisms

- Uniform logarithmic-window raw packets: retain O1 as a proper-class lemma, review pending.
- Unconditional greatest-prime capacity over long runs: abandon by O2.
- Unconditional repair using all historical prime divisors: abandon by O4; first-bad-restricted variants were not refuted.
- Direct admission of the whole packet into squarefree first-owner cells: reject without the missing multi-step/squareful source bridge.
- Complete complementary signed interaction under first escape: open; no target-equivalent bound assumed.
- JOH and SAT: preserve distinct committed derivations; JOH is the next protected turn.

### I. Specialist Handoffs

**Coordinator:** record O1 as a uniform raw signed restriction, O2/O4 as scoped obstructions. O4 is the strongest strategic development: even every prime ancestor cannot fund full-depth physical demand. This does not close/refute VF-LOW or justify narrowing the team.

**Referee:** independently check O1's injectivity/constant, O2's complete fibre/c-1 limit, O3's half-history iff, O4's finite allocation contradiction and the 3/5/7 anchor qualifications. Audit (71)-(74) before any global reading. No acceptance or launch is claimed here.

**Wheel:** a possible replacement incidence relation must be source-authorized, genuinely non-divisor or collectively signed, and retain once-only capacity plus squareful/anchor return. Divisor-only incidence cannot evade O4.

**Census:** reproduce q=2053,L=7, then the sparse 118-seat q=1000000000039 witness. Exact trial division and rational log intervals suffice; no enormous endpoint sieve. Rival predictions are demand<=4 versus demand>4 with prime-divisor union {3,5,7,q}. The A=1024/B=1027 fixture checks O1/O3. No range extension requested.

**Analytic:** no imported analytic bound is used here. O4 is invisible to squarefree-only mu fields. Any analytic transfer must retain physical squareful restoration and cannot turn an existing prefix gain into local-shell/VF control.

**Lean:** no new proof task before independent review. If useful and accepted, O1/O3 are finite arithmetic/log bounds; O4 is a source-specific no-go. Existing strict-gap audit work has priority. Do not implement an unproved first-bad compensation or identify greatest-prime grouping with first-owner cells.

### J. First Independently Missing Lemma

The attempted next supplier was

~~~text
for every legal current subset F in the selected run,
sum_(n in F)w_(floor(sqrt n))
 <=sum_(p in primeDivisors(F))availableHistoricalNegativeCharge(p).
~~~

O4 refutes it even after enlarging the right side to the number of prime ancestors. It must be marked REFUTED, not retained as open.

**No qualified independent replacement is obtained in this run.** For this partition the exact surviving quantitative gap is signed control of C+P in (71), with original compression and (74). Its target-size bound would merely restate the endpoint problem, and is not offered as a smaller lemma. A new mechanism must first exhibit a real non-divisor or collective signed interaction compensating the disclosed squareful family without reusing history. The first bridge to test is actual occurrence/mask/weight admission of that proposed interaction, including its squareful and anchor entries. No such theorem is assumed.

This is a completed falsification, not a universal impossibility conclusion about first-escape-conditioned or nonlocal approaches.

### K. Next-Run Resume Capsule

~~~text
MAIN: 8e5d64ae689b39dabd2a4f6eb33efe4d5d192015.
RUN: scheduled 2026-11-03 08:09:02 EST; RUN_ID_UNAVAILABLE.
CLAIM: 20261103-owner-2, O1-O5, equations (66)-(74).
PRIMARY: VF-LOW, literal w_r-1_Prime(n), not hybrid mu.
RESULT: uniform logarithmic-window signed bound; c-1 horizon;
        half-history cofactor-3 classification; all-ancestor capacity no-go.
STATUS: PAPER_PROOF / SELF_AUDIT; independent acceptance and Lean PENDING.
TESTS: exact rational/integer; sparse 118-seat witness verified.
NEW ENDPOINT GAIN: UNKNOWN; none asserted.
PROJECT GATE: existing VERIFIED_ETA / PR_HEAD_ONLY; no narrowing.
LATEST OWN ROUTES: JOH (20261102-owner-3), SAT (20261103-owner-1),
                   VF-LOW (this run). NEXT: JOH.
JOH RESUME: equations (48)-(49), chronology and unequal-count tails;
            fixed nonnegative two-owner potentials already fail at roots 4,8.
SAT RESUME: 20261103-owner-1 equation (63), growing-band prime error
            with terminal return; do not repeat the zero-layer proof.
VF-LOW RESUME: no unconditional ancestry-capacity revival; identify an
               actual new signed/source-admitted interaction first.
~~~

Retrieved continuity and relevant findings/continuations read; not an independent audit of every upstream derivation:

| Role | Nov 2 blob | Nov 3 intake blob |
| --- | --- | --- |
| Coordinator 00/90 | 1e932d4ce0eb0fd2c5f4507f6b111194d633eb32 | f9c04a1099048cd0b02fd5264b753e916cbcd521 |
| Owner | abfe546d72b151f4cd200fc61de3197efe23a65c | 5c085d12ca455327b2a9ab42d7e55a1b6b2d631b |
| Analytic | 8e48b59611aa1d0bfa3577ed0a4a3bc0d0fcae73 | 7a167a551ca047c0b5bccf6220f40152d78ea176 |
| Wheel | abf8ac8c22a708886183849552c90dd62787ac8d | ae0ce9040b145c8b2ee04418e02a363d10b5da38 |
| Census | 2cd84c57ab18d923e97368764f29f4ccd2ec3bb3 | 09ecf82c4a8d5d36b10ed6d64167d695e096ce03 |
| Referee | 814af1684df66e6ac99b8df1f102cb592b316f89 | 226a5a6d971f347b45e016a046007bc4ceb368ee |
| Lean | 02d19d792e26f072004cb5909f149538752626e9 | 579d19654925823b5fa2ef849366da2925d2c1b0 |

TODAY=AVAILABLE for all roles; YESTERDAY=CARRY_FORWARD. Coordinator 00/90 blobs match. Latest Coordinator 20261103-coordinator-1 restores actual-prime VF-LOW and leaves JOH next. Analytic's NYMAN tail, Wheel's daughter restrictions, Census PC4/PC5 and Referee's prefix/support no-go were read as distinct-carrier context, not imported VF inequalities. External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 has no entry after October 18; EXT-20261018-PNT-1..3 and EXT-20261014-5 keep their scopes.

Checkpoint commit c6911a223876821783e7595c6d78bfe1b6cfbea6 was inspected and read back exactly at blob 910c85c43c5157e1ea2029e0b2e27cd45769f769; only this daily report changed. Final receipt follows after commit/readback.

Limitations: shell GitHub clone returned tunnel HTTP 403; connector reads/writes worked. One source fetch timed out and succeeded on retry. No local Lean, CI launch, proof-source edit, branch/PR mutation, other-report edit, agent launch, schedule change or merge occurred. Only this role's existing report is published.

### Executed Reproducer

Standard-library Python scratch code, embedded for reproduction rather than added to proof sources. SHA256 recorded above.


~~~python
"""Exact raw-VF packet tests; rational intervals certify displayed signs."""

from collections import Counter, defaultdict
from bisect import bisect_left, bisect_right
from fractions import Fraction as F
from functools import cache
from math import isqrt
import json


def primes_up_to(n):
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, isqrt(n) + 1):
        if sieve[p]:
            sieve[p * p : n + 1 : p] = b"\x00" * ((n - p * p) // p + 1)
    return [p for p in range(2, n + 1) if sieve[p]]


def factor(n, primes):
    ans = []
    for p in primes:
        if p * p > n:
            break
        if n % p == 0:
            e = 0
            while n % p == 0:
                e += 1
                n //= p
            ans.append((p, e))
    if n > 1:
        ans.append((n, 1))
    return ans


def log_series(x, terms=40):
    assert 1 <= x <= 2
    u = (x - 1) / (x + 1)
    total = F(0)
    power = u
    for j in range(terms):
        total += 2 * power / (2 * j + 1)
        power *= u * u
    tail = 2 * power / ((2 * terms + 1) * (1 - u * u))
    return total, total + tail


LOG2 = log_series(F(2))


@cache
def weight(r):
    assert r >= 2
    x = F(2 * r * r + 2 * r + 1, 2)
    k = x.numerator.bit_length() - x.denominator.bit_length()
    while x < 2**k:
        k -= 1
    while x >= 2 ** (k + 1):
        k += 1
    low, high = log_series(x / 2**k)
    low += k * LOG2[0]
    high += k * LOG2[1]
    numerator = F(2 * r + 1, r)
    return numerator / high, numerator / low


def packet_interval(q, roots):
    lo, hi = weight(isqrt(q))
    lo -= 1
    hi -= 1
    for r in roots:
        wl, wh = weight(r)
        lo += wl
        hi += wh
    return lo, hi


def outward_decimal(interval, digits=8):
    lo, hi = interval
    scale = 10**digits
    a = lo.numerator * scale // lo.denominator
    b = -((-hi.numerator * scale) // hi.denominator)
    return [str(F(a, scale)), str(F(b, scale))]


FIXTURES = [1024, 1031, 2048, 4096]
PRIMES = primes_up_to(max(FIXTURES) + 20)
LABEL_PRIMES = primes_up_to((max(FIXTURES) + 10) ** 2 // 3)
results = []
for a in FIXTURES:
    k = a.bit_length() - 1
    length = k // 3
    b = a + length
    half_anchor = b // 2 + b % 2
    by_q = defaultdict(list)
    current = set()
    prime_counts = Counter()
    smooth_counts = Counter()
    squareful_rough = 0
    for r in range(a, b):
        for n in range(r * r + 1, (r + 1) ** 2):
            if n % 2 == 0:
                continue
            fac = factor(n, PRIMES)
            if len(fac) == 1 and fac[0][1] == 1:
                prime_counts[r] += 1
                continue
            q = fac[-1][0]
            if q >= b:
                assert fac[-1][1] == 1
                assert q < a * a
                assert n // q < q
                assert r not in [v[0] for v in by_q[q]]
                assert (isqrt(q) >= half_anchor) == (n // q == 3)
                by_q[q].append((r, n, n // q))
                assert n not in current
                current.add(n)
                squareful_rough += any(e > 1 for _, e in fac)
            else:
                smooth_counts[r] += 1

    # Reconstruct independently using every odd cofactor of every candidate q.
    reconstructed = set()
    for q in LABEL_PRIMES[bisect_left(LABEL_PRIMES, b):bisect_right(LABEL_PRIMES, (b*b-1)//3)]:
        start = max(3, a * a // q + 1)
        start += (start % 2 == 0)
        for cofactor in range(start, (b * b - 1) // q + 1, 2):
            n = cofactor * q
            if a * a < n < b * b:
                assert isqrt(n) ** 2 != n
                reconstructed.add(n)
    assert reconstructed == current

    # Symbolic identity: the packet plus its explicit complement is the
    # original current run. Historical prime subtraction is restored once.
    packet_coeff = Counter()
    current_coeff = Counter()
    for q, entries in by_q.items():
        assert len(entries) <= length
        packet_coeff[isqrt(q)] += 1
        for r, _, _ in entries:
            packet_coeff[r] += 1
            current_coeff[r] += 1
    complement_coeff = Counter()
    for r in range(a, b):
        complement_coeff[r] += r - current_coeff[r]
    for q in by_q:
        complement_coeff[isqrt(q)] -= 1
    summed = {r: packet_coeff[r] + complement_coeff[r]
              for r in packet_coeff.keys() | complement_coeff.keys()}
    assert all(v == (r if a <= r < b else 0) for r, v in summed.items())
    assert -len(by_q) + (len(by_q) - sum(prime_counts.values())) == -sum(prime_counts.values())
    assert sum(prime_counts.values()) + sum(smooth_counts.values()) + len(current) == sum(range(a, b))

    # The all-scale proof supplies a rational upper certificate. No floating
    # logarithm is used to determine a sign or certify an all-scale statement.
    uniform_upper = F(39, 128) - 1 + length * F(6147, 4096 * k)
    assert uniform_upper <= -F(799, 4096) < -F(3, 16)
    results.append({"A": a, "B": b, "labels": len(by_q), "current": len(current),
                    "max_multiplicity": max(map(len, by_q.values()), default=0),
                    "squareful_current": squareful_rough,
                    "in_half_history": sum(isqrt(q) >= half_anchor for q in by_q),
                    "pre_half_anchor": sum(isqrt(q) < half_anchor for q in by_q),
                    "uniform_packet_upper": str(uniform_upper)})

# Preregistered near-boundary family, not a first-bad-conditioned example.
edge_results = []
for q, lengths in [(2053, [1, 3, 5, 7, 9, 15]), (4099, [1, 4, 8, 16])]:
    assert factor(q, PRIMES) == [(q, 1)]
    for length in lengths:
        a, b = q - length, q
        assert length * length < 2 * q
        direct = [(isqrt(m * q), m) for m in range(3, q, 2) if a * a < m * q < b * b]
        expected = [(q - j - 1, q - 2 * j) for j in range(1, length)]
        assert direct == sorted(expected, key=lambda t: t[1])
        lo, hi = packet_interval(q, [r for r, _ in direct])
        sign = "positive" if lo > 0 else "negative" if hi < 0 else "undecided"
        edge_results.append({"q": q, "A": a, "B": b, "L": length,
                             "occurrences": len(direct), "sign": sign,
                             "packet_interval": outward_decimal((lo, hi))})

q = 2053
a, b = (q - 1) // 2, q - 1
roots = [isqrt(m * q) for m in range(3, q, 2) if a * a < m * q < b * b]
assert len(roots) == 770
assert len(roots) == (q - 1) // 2 - ((a * a // q + 1) // 2)
assert all(a <= r < b for r in roots)
assert b < 2**12
dyadic_lower = F(len(roots), 12) - 1
assert dyadic_lower == F(379, 6)
dyadic_result = {"q": q, "A": a, "B": b, "occurrences": len(roots),
                 "strict_packet_lower_bound": str(dyadic_lower)}

ancestor_results = []
for q in [65537, 1000000000039]:
    assert factor(q, primes_up_to(isqrt(q))) == [(q, 1)]
    a, b = (q - 1) // 2, q - 1
    cofactors = []
    power5 = 1
    while 9 * power5 <= q:
        power7 = 1
        while 9 * power5 * power7 <= q:
            m = power5 * power7
            exponent3 = 0
            while 3 * m < q:
                m *= 3
                exponent3 += 1
            assert exponent3 >= 2
            assert q < 3 * m < 3 * q
            cofactors.append(m)
            power7 *= 7
        power5 *= 5
    assert len(set(cofactors)) == len(cofactors)
    roots = [isqrt(m*q) for m in cofactors]
    assert all(a*a < m*q < b*b and isqrt(m*q)**2 != m*q for m in cofactors)
    lo = sum((weight(r)[0] for r in roots), F(0))
    hi = sum((weight(r)[1] for r in roots), F(0))
    # Give a whole unit to each of the four prime ancestors. This is a
    # deliberately enlarged capacity, not a redefinition of VF weights.
    ancestor_results.append({"q": q, "A": a, "B": b, "cofactors": len(cofactors),
                             "demand_interval": outward_decimal((lo, hi)),
                             "generous_ancestor_capacity": 4,
                             "exceeds_generous_capacity": lo > 4})
assert ancestor_results[-1]["exceeds_generous_capacity"]

print(json.dumps({"thin_runs": results, "boundary_family": edge_results,
                  "dyadic_falsifier": dyadic_result,
                  "all_ancestor_falsifiers": ancestor_results,
                  "log_interval_terms": 40, "arithmetic": "integer and exact Fraction"}, indent=2))

~~~


Execution closure: substantive mathematics COMPLETE at 2026-11-03 08:40 EST (-0500). The final refresh found that main had advanced to 0ac2bcccfc18d3f37d220b2758b29010a1b538c8 during this invocation; the verified closure audit below supersedes the intake branch/PR status.


### Publication Verification And Latest-Main Closure - 2026-11-03 08:47 EST

This is a status correction and verified publication receipt, not a new mathematical claim. Sections B/K above retain the intake snapshot for chronology. The word "remained" in the earlier closure sentence has been corrected: main advanced during the run.

- Latest actual main, independently returned by the git-ref, branch and main-commit-list reads: **0ac2bcccfc18d3f37d220b2758b29010a1b538c8**, merging #1073 at 2026-11-03 08:14:29 EST. Intake was 8e5d64ae689b39dabd2a4f6eb33efe4d5d192015.
- Re-fetched at that exact commit: AGENTS.md blob 9fa5e9519e2fb6dde22217aa2a18982dafef373a and CURRENT_PROOF_CONTRACT.md blob 88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a are byte-identical to the instructions read at intake. The recursive tree comparison also confirms that the other authority documents and all original VF arithmetic source files cited in this report are unchanged. Thus O1-O5 retain their original source basis and stated scope.
- Re-fetched main:research/oai_434/VF919NativeStrictMertens.lean, blob b33a4883e1ddb0551b0f11f062bce46680d87450, byte-identical to the #1073 head previously read. Its terminal strict Mertens exponent, fixed positive power saving, and complete signed-pair statements are now on main, not merely PR-head evidence. This is an upstream promotion, not a result of today's Owner work and not a proof of the canonical VF endpoint.
- GitHub returned 11 push workflows for this exact main commit, all completed successfully. The relevant Original OAI GaussianSubset to RHLean NNS typecheck run is 41642582431; Lean source audits is 41642582330. No local Lean execution or CI launch was performed. No claim is made that CI alone replaces independent mathematical review.
- PR #1074 merged at 08:22:23 EST and #1075 at 08:22:43 EST, both into agent/lean-verification/finite-slot-reflected-gain-20261102, NOT into main. Their merge commits are 18de4861b324a5139922879ebce3062d589c58d2 and 902d9cc2001413a6376e0bf1fe2e5ebfdfcc7fd4. Do not infer main inclusion from their closed/merged status.
- PR #1076 remains open against that proof branch, now at head 9041df50518bd63f250bf701f849903e27d816b2. The earlier source/CI observations above apply only to its then-observed f676c9b13960f8c80b68bdf35a5f04b07370e228 head; the newer head was not independently re-audited in this invocation. No acceptance or green-CI claim is transferred to it.
- The substantive report was published in commit **f23680751966ab0da5f2831a147b2d399dfadb77**, blob **ba0d7343e202d26c7f779977e9f4fc640744a3ce**. Commit inspection showed exactly one changed file, this authorized daily Owner report. Re-fetch matched the submitted content exactly, including the preserved earlier report/checkpoint and the complete executed reproducer.
- Before this receipt update, the same current blob was freshly re-fetched and matched exactly. The receipt commit itself is checked after publication; its result is not presupposed here.

Final disposition: PAPER_PROOF / SELF_AUDIT plus FINITE_COMPUTATION and scoped REFUTED mechanisms; independent review and Lean formalization of O1-O5 remain PENDING. Canonical VF endpoint gain remains UNKNOWN. Next protected Owner route remains JOH. No other repository file, proof branch, PR, schedule, workflow or permission was changed by this execution.


---

## Scheduled JOH Continuation Checkpoint - 2026-11-03 16:15 EST Invocation

**Status: IN_PROGRESS / PARTIAL.** The due protected route is JOH. Earlier fixed nonnegative owner prices are already refuted by the genuine balanced roots 4 and 8; this run will test a chronology-dependent order restriction on the original prime-minus-floor-Li stream, with full unmatched-tail and historical-anchor restoration. No new theorem is claimed at this checkpoint.

- Actual run: scheduled 2026-11-03 16:15:01 EST; RUN_ID_UNAVAILABLE. Checkpoint time: 2026-11-03 21:18:28 UTC.
- Refreshed main: ad763e3f6ef1f13ff2eeac5b7647d6116923bded, including merged #1081. AGENTS blob 9fa5e9519e2fb6dde22217aa2a18982dafef373a; proof contract blob 88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a; research engine blob 6fce99c61efb5b2a73c0cb1f1464f09b351fcd55.
- Resumed derivation: 20261102-owner-3, equations (48)-(49), colored backlog area and exact unequal-count return; latest Coordinator 20261103-coordinator-2 explicitly assigns JOH next. Latest completed owned turns are JOH (Nov 2 owner-3), SAT (Nov 3 owner-1), VF-LOW (Nov 3 owner-2).
- Original source re-fetched: VF_MID_FLOOR_LI_SIGNED_POPULATION_BALANCE.lean (9a9336dad72171b6d572a1c1ae88d1ae8b56b530), VF_MID_FLOOR_LI_DISCRETE_BACKLOG.lean (4255ca0dffe480f2aec6bd0b68797bbd293396c3), JOH weighted-composite contract (27e28f09e9f79e8a60d524e5fcb6f19904fa55f5).
- Continuity: all seven roles' Nov 2 and available Nov 3 reports retrieved at reporting head f0a7bf2655f1df641ab8e8624fc92ec811c967a5; applicable findings are being read. TODAY=AVAILABLE; YESTERDAY=CARRY_FORWARD. External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 has no new entry after Oct 18.
- Upstream gain: VERIFIED_ETA / ON_MAIN is inherited from committed Referee/Coordinator evidence for the native strict Mertens endpoint, not this run's result and not the canonical actual-prime VF theorem. Current #1082 is an open draft at 0b41bfa95bf2dbeb6facf051014d41688dd62e26; no compilation conclusion is inferred from its title.
- Planned discriminator: determine whether causal matching or a time-varying owner potential produces a genuinely new one-sided restriction, and test every proposed order premise against the actual event stream. Generic rearrangements may diagnose insufficiency but will never be reported as genuine arithmetic counterexamples.
- Permissions: own daily report only. Shell clone failed with CONNECT tunnel HTTP 403; GitHub connector retrieval works. No local Lean, branch/PR change, agent launch, or schedule change.

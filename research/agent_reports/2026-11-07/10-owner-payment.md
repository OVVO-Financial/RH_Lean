# RH | Owner Payment - 2026-11-07

## A. Most Important Mathematical Development

**Large shared ancestry is a sparse, exactly controllable interaction sector, not an automatically favorable sign sector.** On the original SAT interior cofactor interval `D<c<2D`, the graph of nonzero Mobius pairs satisfying `7*gcd(c,d)>=2D` is a **matching**. Its only reduced pairs are `(2,3)`, `(3,5)`, and `(5,6)`. No cofactor occurs twice. The first two types have equal Mobius signs; the third has opposite signs and cancels the original common prime-error anchor exactly. The constant `2/7` is sharp for the uniform matching statement.

Consequently, for the ACTUAL prime-error weights `e_c`,

```text
|2 sum_(D<c<d<2D, gcd(c,d)>=2D/7) mu(c)mu(d)e_c e_d|
  <= sum_(matched c) mu(c)^2 e_c^2.                         (SG2)
```

A second, growing-core incidence bound controls the much larger sector `gcd(c,d)>=ceil(sqrt D)`. With the established best explicit boundary `b_*=7/8-delta_*`, it gives

```text
|C_(gcd>=ceil(sqrt D))(R)| <<_epsilon R^(3/4+3b_*+epsilon)
                         = R^(27/8-3delta_*+epsilon).      (SG4)
```

Thus this entire sector is paid below the proposed proper-interior energy scale `R^(4b_*-1/16+epsilon)`. This uses independently proved factor-incidence control and the already available prime-error input. It does **not** control the lower-GCD pairs, the anchor, or the joint smooth/model/complement return. No new Mertens, canonical VF, or RH endpoint is established.

| Claim | Mathematical result | Classification |
| --- | --- | --- |
| 20261107-owner-1/SG1 | Sharp `2D/7` matching classification on genuine nonzero cofactor support | PAPER_PROOF |
| 20261107-owner-1/SG2 | Exact signed packet squares, sharp diagonal domination, and selective anchor cancellation | PAPER_PROOF / IDENTITY_ONLY for the reconstruction |
| 20261107-owner-1/SG3 | Uniform divisor-weighted bound for every growing GCD cutoff | PAPER_PROOF |
| 20261107-owner-1/SG4 | Original prime-error sector estimate and low-GCD inverse localization | PAPER_PROOF; application of established analytic input |
| 20261107-owner-1/SG5 | Exact graph/source checks, certified opposite cross signs, and failed wider matching | FINITE_COMPUTATION / REFUTED auxiliary claims |

All new mathematics is **SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED**. Status: `INDEPENDENT_COMPONENT_ADVANCE`; `eta_gate=SEARCH_BROAD`; `net_endpoint_gain=UNKNOWN`; `NEW_VERIFIED_ENDPOINT_GAIN=NONE`. Existing strict endpoint gains are preserved, not reset to zero. No literature-priority claim is made.

Actual invocation: **SCHEDULED 2026-11-07T00:09:01-05:00**, America/New_York; `RUN_ID_UNAVAILABLE`; run label `20261107-owner-1`. This final synthesis completes the early checkpoint, not another invocation.

## B. Current Authoritative Objective

Latest authoritative main at closeout: **1c057c1d65b6d4cb4d59d207f69a815c52353314**, human merge of #1100. Original source inspection and derivation were pinned to **d4df133117c5b58f90979d2eb680167ef37995cf**; every material source and policy blob below is unchanged at the new main. The canonical target remains

```text
VFCanonicalSquareVonKochStatement:
exists C>=0, forall integers R>=2,
 |pi(R^2)-VF_can(R^2)| <= C R log R.
```

The canonical phase is `vfCanonical=vfMid+sqrt(2)`. The inspected terminal theorem `riemannHypothesis_of_vfCanonicalSquare` still takes the explicit `ClassicalVonKochRHCriterion` and the unproved arithmetic statement. This research does not discharge either by a conditional green theorem.

`baseline_ack=PAID_BASELINE_EXACT_CONSUMER_V1`, policy blob **13d58dd12d90fbf1160812c7c93442dc5d0576ac**. `deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1`, blob **ffd8f1c65cc4da656174956d4e03b48bea46768b**. SAT was selected by protected rotation and the cofactor-pair question, consistent with the latest Coordinator handoff. No unrelated OAI reconstruction or mandatory sharp-shell norm was imposed.

The original Lean definitions and proof statements were fetched at the derivation pin. Closeout re-fetched both authority files and compared the complete new tree, verifying all material blobs unchanged. Material source blobs:

| File | Blob SHA | Actual scope consumed |
| --- | --- | --- |
| AGENTS.md | 48b2a58ab5fcd402321a4dace511c7d54bf688a1 | Live authority and own-report-only permissions |
| CURRENT_PROOF_CONTRACT.md | 7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c | Original canonical target and distinct carriers |
| RHLean/Proof/LargePrimeTerminalFlipLayers.lean | b7617df21b81002854a0d311ef7e02d9494154c3 | Terminal sign, clipped prime prefix, complete packet and finite Abel theorem |
| RHLean/Analysis/SquareRootPostCrossingTail.lean | 660772bad3663d14c0f3390e26925b57d1390080 | Full negative transport and smooth-plus-tail return |
| RHLean/Proof/PrimeSieveSquareRootTransport.lean | 721b7f557ea9f253598b1ae3508f31d9f10a9f4f | Genuine smooth/transport populations and complete source |
| RHLean/Analysis/SquareRootTransportTopFibreNoGo.lean | fcc63e7bcb6927122075c39ccacaca445685729e | Existing top-prime obstruction; not the new graph theorem |
| research/oai_434/VF919NativeStrictMertens.lean | b33a4883e1ddb0551b0f11f062bce46680d87450 | Native growth at the actual Hecke boundary and strict-gap statements |
| research/oai_434/VF919ExplicitFixedSourceSlotCount.lean | bad5aab0a60e96d19e7c9550cd7c0a072288bc0f | Exact fixed-count boundary and `explicitSlotCount_two_le` |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb | Canonical target and explicit terminal hypotheses |
| research/NNS_SIGNED_PRIME_WINDOW_COVARIANCE_20261103.md | c6b88c91b5d7b5a14e1c1c3d5a48ca1a60e7c839 | Distinct original moving prime-window source for the qualified cross-route application |

The baseline used is not merely rounded 7/8. Put

```text
N_* = explicitSlotCount >= 2,
delta_* = 1/(288 N_*),
b_* = 7/8-delta_* >= 503/576 > 3/4.
```

The native declarations yield `MertensGrowthAtMost b_*`, meaning an envelope with EVERY positive exponent loss, not a no-loss bound at `b_*`. Yesterday's **20261106-owner-1/BT1-BT2** converts an available fixed Mertens power to `Delta(x)=O(x^b log x)`. Applying this at slightly enlarged powers yields

```text
for every epsilon>0, |Delta(x)| <<_epsilon x^(b_*+epsilon), x>=2. (BP)
```

This is an established-input consequence, not a new theorem claimed here. It uses the classical zero-free-to-prime-error transfer with prime powers and the Li_2 constant restored. The graph inequalities SG1-SG3 do not depend on BP at all. SG4 states exactly where BP is used. The previous rounded `29/16` SAT interior certificate is already paid; it is not reopened.

The November 6 Owner final section supplies reusable exact-head evidence for #1091 at **6778fd4c25b0f369d311e6e71223e168e329b4bf**, including run **41898325686**, job **126813711885**, and standard-axiom audits. The relevant current source blobs match those retrieved in that verified report. This execution inspected the live statements and reused that evidence; it did not perform a new Lean compilation or independently repeat its audit.

Direct intake PR discovery: #1100 was the only open PR, non-draft, at **e52207d527da684346e151d4ff680696c88e8fa7**; all 13 returned checks were successful at that exact head. The closeout refresh verified its human merge at **2026-11-07T05:19:51Z**, merge commit **1c057c1d65b6d4cb4d59d207f69a815c52353314**. The open/draft list is now empty. Recent #1096-#1099 merges were also directly checked. Their finite cancellation, CORR4 sampling, baseline-policy and Nyman obstruction scopes, and #1100's radical-increment identity, remain distinct from SG1-SG4.

## C. Structural Hypothesis Investigated

**H-SPARSE:** Large common ancestry constrains the possible reduced factors so strongly that the complete interaction graph has small operator norm, even though individual signs need not be favorable. This survives and gives SG1-SG4.

**H-WIDER:** The same constant-one matching bound persists at the wider threshold `gcd(c,d)>=D/4`. This is false, already at `D=4`, and fails in infinite genuine squarefree families. The corrected sharp uniform matching threshold is `2D/7`.

**H-SIGN control:** Shared ancestry itself makes the weighted sector nonpositive. This is an already-known unsafe general shortcut, not a newly proposed global strategy. On this exact narrower source it fails at `R=64`; nonnegativity also fails at `R=65`. These are source regressions, not novelty claims for the general sign no-go.

The graph is a classification of the **original off-diagonal pairs**, not a replacement stochastic coefficient model and not a split into unrelated squared populations. Every pair has exactly one gcd. This makes the complementary interaction accounting exact.

## D. Mathematical Derivation

### D0. Original Arithmetic Carrier And Complete Return

For integers `q>=3`, `D>=1`, `2D<q`, set

```text
Y=q^2-1, x_c=floor(Y/c), P=Y/D,
M(d)=sum_(1<=n<=d) mu(n), Delta(t)=pi(t)-Li_2(t),
e_c=Delta(x_c)-Delta(x_(2D)), D<c<2D,
I=sum_(D<c<2D) mu(c)e_c,
A=M(D)[Delta(x_D)-Delta(x_(2D))],
T=-sum_(D<=d<2D) M(d)[pi(x_d)-pi(x_(d+1))],
L=-sum_(D<=d<2D) M(d)[Li_2(x_d)-Li_2(x_(d+1))],
E=T-L=-A-I.                                               (D0)
```

Every admitted owner prime lies in `(x_(2D),x_D]`. Since `x_(2D)>=q+1`, it satisfies `p>q>c` for every physical cofactor in its fiber. The original sign theorem gives `mu(pc)=-mu(c)`, including squareful zeros. Distinct owners cannot represent the same integer below `q^2`, because their product is too large. Nothing in the graph argument replaces actual prime membership with Li density or admits an extra physical site.

Let `P_q(K)=squareRootTruncatedUpperMiddlePacket(q,K)` and let `S_q(Y)` be the genuine Mobius mass of `1<=n<=Y` with greatest prime factor at most q, including 1. Then the existing source theorems give

```text
T=P_q(2D-1)-P_q(D-1),
C=S_q(Y)+P_q(D-1)+P_q(q-1)-P_q(2D-1),
M(Y)=T+C=L+E+C.                                          (RETURN)
```

The quantitative specialization is `q=2R`, `D=floor(sqrt R)`, integer `R>=16`. The graph theorem itself holds for every integer `D>=1` and every set of real weights. This source is not the clipped original VF/#915 payment denominator.

### D1. SG1: Sharp Matching Classification

Let `V_D={c: D<c<2D, mu(c)!=0}` and put an unordered edge `{c,d}`, `c<d`, exactly when `g=gcd(c,d)` satisfies `7g>=2D`. Then every edge, uniquely, is one of

```text
A-type: {2g,3g},  D<2g<3g<2D, mu(g)!=0, gcd(g,6)=1;
B-type: {3g,5g},  D<3g<5g<2D, mu(g)!=0, gcd(g,15)=1;
C-type: {5g,6g},  D<5g<6g<2D, mu(g)!=0, gcd(g,30)=1,
                    7g>=2D.
```

The cutoff is automatic for A and B. All three types are disjoint edges, including between types.

**Classification proof.** Write `c=ga`, `d=gb`, `a<b`, `gcd(a,b)=1`. Squarefree c,d force g,a,b squarefree and `gcd(g,ab)=1`. One cannot have `a=1`: then `g=c>D`, and `d>=2g>2D`. Also `b=d/g<2D/g<=7`. Thus `a,b` belong to `{2,3,5,6}`. Since `b/a=d/c<2`, the only coprime choices are `(2,3)`, `(3,5)`, `(5,6)`. The converse follows immediately from the displayed support and coprimality conditions. Their Mobius products are respectively `+1,+1,-1`.

**No reused vertex.** Each individual type is a matching: if `ag=bh` for its coprime distinct a,b, then `b|g`, violating `gcd(g,ab)=1`. For different types, there are only four endpoint identifications to examine in each case:

| Types meeting | Why a common vertex is impossible |
| --- | --- |
| A and B | Coprimality excludes two identifications. In either remaining one, the two other endpoints have ratio `5/2`, impossible inside a strict dyadic interval. |
| A and C | Every identification forces 2 or 3 into a cofactor from which it is excluded. |
| B and C | Coprimality excludes two identifications. The remaining two force the other endpoints to have ratio exactly 2, again impossible. |

For example, `3g=6h` in B/C forces `g=2h`; their other endpoints are `10h` and `5h`. If `5g=5h`, the other endpoints are `3g` and `6g`. The strict physical walls therefore matter. This proves the matching property for all D, without a size estimate for M or Delta.

**Sharp threshold.** For any fixed `0<=alpha<2/7`, take arbitrarily large squarefree t coprime to 210, and set

```text
D=21t+1, vertices 30t,35t,42t.
gcd(30t,42t)=6t, gcd(35t,42t)=7t.
```

All three are genuine squarefree vertices in `(D,2D)`. Since `6t/(21t+1)->2/7`, both edges are present at cutoff `alpha D` for sufficiently large t. Vertex `42t` is reused. Such t exist, for example primes exceeding 7. Thus no smaller constant works uniformly. Taking `R=D^2` realizes these actual cofactor labels in the original SAT family; this is not an artificial factorization countermodel.

### D2. SG2: Exact Signed Packets And Anchor Conservation

For any real weights e, write `u_c=mu(c)e_c`,

```text
V=sum_(c in V_D) e_c^2,
C_hi=2 sum_(edges {c,d}) mu(c)mu(d)e_c e_d,
C_lo=2 sum_(D<c<d<2D, 7*gcd(c,d)<2D) mu(c)mu(d)e_c e_d.
```

Because each vertex is used at most once, `2|e_c e_d|<=e_c^2+e_d^2` proves

```text
|C_hi| <= sum_(matched c) e_c^2 <= V.                       (SG2a)
```

Equivalently the signed off-diagonal matrix is a disjoint union of two-by-two blocks with entries `+1` or `-1` off the diagonal, and isolated zeros. Its operator norm is at most one, exactly one when an edge exists. Equality in the uniform constant-one bound is attained, for example on the edge `(10,15)` at `D=8` with equal nonzero weights and all other weights zero. This arbitrary-weight equality certifies sharpness of the bound, not any assertion about the actual Delta weights.

More importantly, the full square is reconstructed as

```text
I^2 = V+C_hi+C_lo
    = sum_(edges {c,d}) (mu(c)e_c+mu(d)e_d)^2
       +sum_(unmatched c) e_c^2 + C_lo.                    (SG2b)
```

All cross-packet interactions are precisely C_lo. No diagonal is counted twice and no interaction between packets has disappeared.

For the literal `e_c=Delta(x_c)-Delta(x_(2D))`, the packet sums are

```text
A-type: -mu(g)[Delta(x_(2g))+Delta(x_(3g))-2Delta(x_(2D))];
B-type: -mu(g)[Delta(x_(3g))+Delta(x_(5g))-2Delta(x_(2D))];
C-type:  mu(g)[Delta(x_(6g))-Delta(x_(5g))].               (SG2c)
```

Only C-type cancels the common anchor. Its exact real-prime term is the discrepancy of `(x_(6g),x_(5g)]`, with the displayed sign and actual integer floors. The positive types retain twice the anchor. This explains why a local sign-reversing pairing cannot be promoted to a global anchored covariance saving.

At `gcd(c,d)>=D/3`, the C-type is excluded because `6g<2D`; thus every nonzero multiplicative pair product in that more extreme sector is positive. Weighted products may nevertheless have either sign because their two prime errors need not have the same sign.

### D3. SG3: A Uniform Growing-Cutoff Bound

For any real `G>=1`, let `C_>=G` be the same complete off-diagonal sum restricted by `gcd(c,d)>=G`. Its graph need not be a matching. If `deg_G(c)` is its degree, then

```text
|C_>=G| <= sum_(c in V_D) deg_G(c)e_c^2
        <= (1+D/G) sum_(c in V_D) tau(c)e_c^2.              (SG3a)
```

**Proof.** For a fixed c, each neighbor d has one actual gcd g dividing c, with `g>=G`. Write `d=gb`. The open interval `D/g<b<2D/g` contains at most `D/g+1<=D/G+1` integers. There are at most tau(c) possible g. Summing `2|e_c e_d|<=e_c^2+e_d^2` over edges charges each diagonal exactly its degree, proving both inequalities. The relaxed count may include inadmissible b; that is an upper bound, not an assertion of source admission.

For every fixed epsilon>0, squarefree `c<2D` satisfies `tau(c)=2^omega(c)<=K_epsilon D^epsilon`. An elementary proof splits its primes at `2^(1/epsilon)`: the finitely many smaller primes contribute a constant, and every larger prime p satisfies `2<=p^epsilon`. Thus, uniformly in D,G and the actual weights,

```text
|C_>=G| <<_epsilon (1+D/G) D^epsilon V.                   (SG3b)
```

This explicit degree loss is indispensable. SG3 does not pretend that a cofactor with many neighbors supplies multiple independent copies of one diagonal budget. Unlike a fixed-core asymptotic, its constant is uniform when G and D grow.

### D4. SG4: Original Prime-Error Application And Inverse Restriction

Use BP(b) with fixed b in `(3/4,1)`, and retain every positive exponent loss. All `x_c`, `D<=c<=2D`, lie in `[P/4,P]`. Therefore

```text
V <<_epsilon D P^(2b+epsilon),
|C_(gcd>=2D/7)| <<_epsilon R^(1/2+3b+epsilon),
|C_(gcd>=ceil(sqrt D))| <<_epsilon R^(3/4+3b+epsilon).     (SG4a)
```

Here and below `q=2R`, `D=floor(sqrt R)`, `Y=q^2-1`. The last bound follows from SG3 with `D/G<=sqrt D`. All epsilon losses are chosen smaller at the input before being collected at the output. Constants are independent of R, q, the changing cutoffs and the selected prime populations.

At the strongest explicit baseline b=b_*, these powers are respectively

```text
diagonal / extreme matching sector: 25/8-3delta_*+epsilon;
growing large-GCD sector:           27/8-3delta_*+epsilon;
prior whole-interior certificate:   29/8-3delta_*+epsilon;
established whole M(Y)^2 ceiling:   7/2 -4delta_*+epsilon.
```

The last line is a different, already established complete statistic. It is not an upper bound for I^2 by itself.

For every fixed `0<eta<b-3/4`, the growing sector and diagonal are below `R^(4b-eta+epsilon)`. At b=b_*, `eta=1/16` is admissible because `b_*-3/4>=71/576>1/16`. This is a **proper-sector** margin, never VERIFIED_ETA for the global programme.

There is a precise inverse localization. Put `G=ceil(sqrt D)` and let C_<G be the actual complementary pair sum. Then

```text
I_R^2 = V_R+C_>=G(R)+C_<G(R),
C_<G(R) >= I_R^2 - K_epsilon R^(3/4+3b+epsilon).          (SG4b)
```

Thus a large violation of the stronger I_R bound cannot be explained by the already controlled large-GCD sector; it forces large positive LOW-GCD signed interaction. This is an independently proved necessary arithmetic restriction, not a claim that such an interaction is impossible.

### D5. All Remaining Source Terms

The complete equations remain

```text
E^2=A^2+I^2+2AI,
M(Y)^2=L^2+E^2+C^2+2LE+2LC+2EC.                         (D5)
```

A still has only the inherited `O_epsilon(R^(2b+epsilon))` amplitude certificate. The signed combination `L+C` and its interactions with A,I are not paid by the graph theorem. No complement is required to be small separately; a successful joint-source theorem may bypass separate I control.

If a later proof changes prime counts to psi, the original step weight remains

```text
k(t)=sum_(D<=d<2D) M(d) 1_(x_(d+1)<t<=x_d),
E=-integral k(t)/log t [dpsi(t)-dt]
   +sum_(p prime, j>=2) k(p^j)/j.
```

No prime-power term is dropped, and `k(t)` is not silently replaced by an unfloored surrogate. This run works directly with pi and Li_2 and therefore introduces no new explicit-formula truncation or prime-power loss.

## E. Quantitative Consequence

The new independently justified restriction is a uniform bound for a **proper part of the genuine signed covariance**. It removes all `gcd(c,d)>=ceil(sqrt D)` interactions from the first unpaid interior inequality at `eta=1/16`, while the stronger exact matching theorem explains their extremal factor geometry and anchor behavior.

The complete endpoint has **no new proved gain**. Even a proof of the remaining low-GCD estimate would still need A and the joint `L+C` return. The original global square-of-sum, local shell energy, SAT interior, and clipped VF payment have not been identified with one another.

## F. Falsification And Circularity Review

**Exact matching failure below the claimed scope.** At `D=4`, the wider cutoff `gcd>=D/4` includes all three edges among the genuine squarefree vertices 5,6,7. Vertex 5 already has two neighbors. Taking `u_c=mu(c)e_c=1` on those three vertices gives cross term 6 and diagonal 3. This refutes the universal constant-one weighted bound at the wider cutoff. The vector is synthetic and is not called an actual prime-error counterexample. The infinite `(30t,35t,42t)` family proves sharpness of 2/7, not just failure at a small scale.

**Boundary falsifier.** Replacing the original interval by the closed interval `[D,2D]` fails already at D=3: 3,5,6 form a triangle. The primitive pair `(1,2)` can then enter, and the ratio-two exclusion fails. The theorem retains its original strict endpoints.

**Actual signed prime-error controls.** The following rational outward enclosures use genuine prime counts and certified Li_2 integrals; they are not floating-point sign tests. At R=64 and 65, D=8 and the 2D/7 graph consists only of `(10,15)`:

| R | x_10 | x_15 | Common x_16 | Prime counts above anchor | Certified complete C_hi |
| ---: | ---: | ---: | ---: | --- | --- |
| 64 | 1638 | 1092 | 1023 | 87, 10 | `[0.248840, 0.248841]` |
| 65 | 1689 | 1126 | 1056 | 86, 11 | `[-3.492972, -3.492970]` |

Both Mobius products equal +1. The sign reversal is in the true arithmetic weights, not in a substituted random model. No universal favorable cross sign follows from the matching. The existing general ancestry-sign counterexamples remain credited to prior work.

**Executed finite scope, preregistered before the first run:**

| Test | Successful scope |
| --- | --- |
| Exact predicted graph and endpoint nonreuse | D=1..256; 2,859 edges |
| Four deterministic integer-vector full-square tests | 1,024 cases |
| Growing cutoff degree inequality | Every nonzero vertex, D=1..256, G=ceil(sqrt D) |
| Sharpness family | t=1,11,13,17,19 |
| Actual prime-error cross signs | R=16..256 and 483,484,485; 244 roots |
| Certified sign outcomes | 71 positive, 43 negative, 130 exactly empty/zero; no undecided signs |
| Independent symbolic Li_2/full source return | R=64,81,100,121,255,256,257,484 |
| Complete original quadratic pair checks | 641 pairs; all anchor/complement terms retained |
| Once-only actual prime/cofactor occurrences | 130,731 sites, including squareful zero coefficients |

The Li certifier integrates through 44,435 with denominator `2^128`, the credited 48-term atanh logarithm intervals, and composite Simpson error using `|f''''(x)|<=1544/n^4` on `[n,n+1]` for `f=1/log x`. The maximum interval width is

```text
40223641190371220089464147653477 /
340282366920938463463374607431768211456.
```

The helper is reused from the November 6 Owner appendix's credited Census reference; it is not new research. This invocation needs Li values, not their integer floors, so no approximate floor is used. Separately, formal independent Li_2 symbols verify the complete polynomial identities without numerical integration.

At R=484, D=22, the C-type packet `(35,42)` with g=7 cancels `Delta(21295)` exactly and retains `Delta(26772)-Delta(22310)`. This is the tested original anchor cancellation, not deletion of all anchors.

**Execution correction preserved.** The first harness wrongly asserted that the selected D=22 branching fixture was the earliest D/4 failure. Exhaustive enumeration returned the earlier D=4 fixture. The harness assertion was corrected, the registered domain was unchanged, and the complete verifier then passed. The all-D 2/7 graph checks had already passed before that diagnostic failure. The final strengthened verifier and Python syntax compilation both exited successfully; these repeated runs are not counted as independent experiments.

**No-go and novelty check.** Current repository searches found the prior general gcd-sign warnings, ancestry classifications and distinct prime-window Co-Div source. None supplies this sharp dyadic matching theorem or its source-specific sector estimate. Text checks of the retrieved November 6 reports found no same claim. A limited external search supplied no theorem used in the proof. This is not exhaustive literature-priority evidence. BP, finite Abel, terminal sign and complete smooth-return identities are explicitly reused rather than re-credited.

## G. Conceptual Interpretation

Common ancestry does two different things. At very large gcd it restricts the reduced factors to a finite, resource-disjoint graph, so its covariance cannot exceed one diagonal budget. Slightly farther out, the first genuinely opposite-sign primitive pair is `(5,6)`, and only that packet removes the common anchor. These are exact restrictions on collective interactions, not empirical independence.

When the factor core grows, branching returns. SG3 charges its actual maximum incidence instead of cloning the same coefficient. The remaining possible concentration is consequently localized to smaller gcd, where many more primitive relationships are possible. The theorem does not prohibit those configurations, but it gives a concrete reason to move the next arithmetic attack away from already paid large ancestry.

## H. Competing Mechanisms

| Mechanism | Established content | First missing input / strongest obstruction | Decision |
| --- | --- | --- | --- |
| Sharp large-GCD signed packets | SG1-SG2, exact optimal matching and selective anchor cancellation | Does not control cross-packet/low-GCD interactions; D/4 and closed-wall extensions fail | Keep as a useful component theorem |
| Growing large-GCD graph control | SG3-SG4 pays g>=ceil(sqrt D) using BP | The lower-GCD prime-error cross sum remains; triangle/degree loss is explicit | Use to localize the next SAT attempt |
| Uniform favorable ancestry signs | Both actual signs occur at R=64,65 | Source-level counterexamples | Do not use as a supplier |
| Uniform single-zero annihilation | Yesterday's RZ2-RZ3 forbid it at their precise operator scope | Not a lower bound for actual E_R or a ban on joint compensation | Remains abandoned in its refuted form |
| Full joint source compensation | Original L,E,C and A,I remain available | Neither today's graph estimate nor old BT2 pays the complete return | Continue as an alternative to separately bounding I |

This does not establish that SAT is more promising than the other protected routes. It is more concrete than the previous undifferentiated OPEN-SAT-CROSS inventory because a growing proper sector is now bounded. VF-LOW and JOH remain protected; next Owner route is VF-LOW.

## I. Specialist Handoffs And Continuity

**Coordinator:** register SG1-SG4 as paper/self-audited component progress. The strongest new concept is the optimal factor-induced matching with exact anchor-selective packets. Its first missing ingredient is actual lower-GCD prime-error correlation, followed by the full source return. Do not convert the displayed 1/16 component margin to a global gain or narrow the nine-route programme.

**Adversarial Referee:** reconstruct SG1 from the strict dyadic interval and squarefree support before reading the proof. Challenge all inter-type vertex identifications, the inclusive `7g>=2D` threshold, the sharpness family, SG3's uniform degree cost, and SG4's every-positive-loss comparison with b_*. Check the D=4 and closed D=3 obstructions and certified R=64/65 signs. Independent review is requested, not presumed delivered by this self-audit.

**Lean Verification:** after independent acceptance and a utility assessment, SG1-SG2 are elementary candidates using existing Mobius multiplicativity and finite sums. Exact statement: for integer D>=1, graph on squarefree `D<c<2D` with `7*gcd(c,d)>=2D` has degree at most one; classify edges and derive the real-weight inequality. No analytic Delta estimate need be axiomatized to formalize that lemma. No implementation, proof branch or PR is requested before qualification.

**Finite Wheel & Incidence:** the graph matching is on cofactor labels, not your physical greatest-prime donor matching. It proves a once-only quadratic budget, not an injection paying the MU-LIFT residual. SG3 is a uniform growing-incidence inequality; no fixed-prime bank or repeated donor credit is used. The sharp branching family can be independently checked without a large census.

**Analytic Type II:** the genuine new unpaid interior source can be restricted to `gcd(c,d)<ceil(sqrt D)` at the displayed energy scale. Do not infer orthogonality from this localization. The matching theorem also applies exactly to a **proper cofactor block** of the November 3 native moving-window source by taking

```text
e_c=n_r(c)=pi(floor(((r+1)^2-1)/c))-pi(floor((r^2-1)/c)),
D<c<2D<=r.
```

This is a literal substitution into an arbitrary-weight finite theorem, not a rational-Mobius/Hecke identification. It controls only that block's large-GCD submatrix. Cross-block pairs, the root-prime gate, low population and complete shell return remain. No exponent transfer to CODIV or OAI is asserted.

**Prime Census:** a small independent check should prioritize endpoint classification and the explicit branching/anchor fixtures, not extend the 244-root sign scan or fit a power. Distinguish the universal-vector failure from the actual Delta sign controls. A future experiment should test an explicitly proposed primitive-pair arithmetic restriction; no such independent signed law is currently established.

**Two-day continuity.** At intake November 7 returned 404: upstream **TODAY=PENDING; YESTERDAY=CARRY_FORWARD**. The following actual November 6 report blobs were retrieved; relevant conclusions, source/return qualifications and handoffs were read, not every unrelated executable appendix rerun:

| Role | November 6 blob | Consumed continuation |
| --- | --- | --- |
| Coordinator AM, PM same directory-listed blob | 8812a90540fb511279b5f4ce08e108ef717d5ef1 | 23:09 CS1-CS4; SAT due; independent-source strategy |
| Owner | 1856a96aaaa9d86a5ee2d59ffe50ced936443fa6 | SAT BT/RZ, VF-LOW DR, JOH MS; complete current rotation |
| Analytic | 7997620b6ab7eb0701296994734ee910df3c3ba1 | FP parent-mode limit, RM full return, AQ large-cube proper estimate |
| Wheel | 3099558194a00358962ff1844bf283e625b9283d | CP/PB return limitations, GF greatest-prime deficit and cross-label repair |
| Census | c34ac074296e8b2e5b20dee3a2ce02518571206c | GM/HC resource corrections; FW weighted sign and radical increments |
| Referee | da3265467c799e9d21832ab25245617ba3b15a54 | Scoped CP/RM/NS acceptance; new spectral-jump obstruction and pending non-Nyman reviews |
| Lean | b8bfe3ce9c20d7903395364efb39bcec974c8a2f | #1097/#1099 scopes and #1100 exact-head FW3 implementation |

The external inbox blob **038018145c0fddb2f6306c0712373adf9cd1ea52** has no November entry. Preserve **EXT-20261018-PNT-1..3**, **EXT-20261017-XCOORD-1** and **EXT-20261014-5** at their actual prime, boundary, anchor and unconditional-versus-first-bad scopes. None supplies the lower-GCD estimate. The existing R=549 BLOCK falsifier and historical prime-window counterexamples are unchanged; they were not rerun on an unrelated carrier.

All handoffs are published asynchronously through this own report. No agent was launched and no other role's file, issue or PR was modified.

## J. First Independently Missing Lemma

The old BT2 threshold is paid. After SG4, a sufficient remaining **proper-interior** assertion is, for some fixed `0<eta<b_*-3/4`,

```text
for every epsilon>0, exists K_epsilon,R_epsilon,
for all integer R>=R_epsilon:
  2 sum_(D<c<d<2D, gcd(c,d)<ceil(sqrt D))
       mu(c)mu(d)e_c e_d
    <= K_epsilon R^(4b_*-eta+epsilon).                   (OPEN-SAT-LOWGCD)
```

With the paid sectors restored, this is equivalent at this power scale to the stronger I_R energy statement. It is **not an independently proved supplier** and not the canonical/global target; it still leaves A and L+C unpaid. No claim of independent ease is made.

The smallest separate mathematical candidate for the next SAT investigation is a bound of the same shape on the **primitive `gcd(c,d)=1` subpopulation alone**, using the actual anchored prime errors. It is a proper subset when D is large, is not claimed equivalent to the full source, and would still leave every `2<=g<ceil(sqrt D)` sector and their correctly counted weights. No proof, automatic scaling from g=1, or sign rule is known. A valid next advance must identify a genuine arithmetic correlation restriction there, or change to a joint L/E/C mechanism; renaming OPEN-SAT-LOWGCD is not progress.

## K. Next-Run Resume Capsule And Publication

```text
RUN: 20261107-owner-1; SCHEDULED 00:09:01 EST; RUN_ID_UNAVAILABLE.
MAIN AT CLOSEOUT: 1c057c1d65b6d4cb4d59d207f69a815c52353314.
DERIVATION PIN: d4df133117c5b58f90979d2eb680167ef37995cf; all material blobs unchanged.
POLICIES: PAID_BASELINE_EXACT_CONSUMER_V1 / NO_PIGEONHOLING_ROUTE_SELECTOR_V1.
ROUTE: SAT; original q=2R, D=floor(sqrt R), Y=q^2-1, Delta=pi-Li_2.
NEW SG1: exact matching for gcd>=2D/7; types (2,3),(3,5),(5,6);
         threshold sharp by (30t,35t,42t), D=21t+1.
NEW SG2: |C_hi|<=matched diagonal; only (5g,6g) cancels common anchor.
NEW SG3: |C_>=G|<=(1+D/G)sum tau(c)e_c^2, uniform growing G.
NEW SG4: G=ceil(sqrt D) gives R^(3/4+3b_*+epsilon), proper sector only.
NEXT SAT GAP: genuine low-GCD prime-error pairs; then A and L+C return.
FALSIFIERS: D/4 graph fails D=4; closed walls fail D=3;
            actual C_hi positive R=64, negative R=65.
FINITE: D<=256, 2859 edges, 1024 vector checks; 244 certified roots;
        8 symbolic complete returns, 130731 once-only physical sites.
REVIEW: SELF_AUDIT; independent review PENDING; NOT_FORMALIZED.
GLOBAL: no new complete exponent; established strict baseline retained.
NEXT DISTINCT OWNER ROUTE: VF-LOW; resume 20261106-owner-2/DR1-DR7.
JOH: retain MS1-MS4 and pending review; no restart of old fixed-length work.
```

Early checkpoint commit **a4f7a5e03e1bc567b8a606f1b8fd037a99b9e32c**, blob **3ac56acb2e0a72e6676519a91613454c60d25aa1**, was read back byte-for-byte; commit metadata listed only this authorized report. Its parent report-branch commit was **054f63067093353a4893295d39781def3e2772c1**. The complete checkpoint is preserved below. Final publication will be certified by an actual immutable-commit readback, not by this prospective statement.

Actual limitations: no independent mathematical review, new Lean compilation or CI launch occurred. No external analytic theorem was newly imported beyond the explicitly carried BT baseline. The finite checks do not prove BP or an asymptotic lower-GCD bound. Only this role's report is published; no main/source/policy/workflow/other-report/proof-branch/PR/schedule/permission change was made.

### Prepublication Freshness

At **2026-11-07T05:30:25Z**, the newest main, both authority files, the complete tree and #1100 merge metadata were checked. The only changed blobs since the derivation pin are the Nyman radical-increment Lean file, its regression script and its workflow. SAT definitions, all listed material sources and governing instructions are byte-identical by blob identity; the two authority files were also directly re-fetched and compared. No new review of the unrelated Nyman proof is claimed. Today's report directory still contains only this Owner checkpoint: upstream **TODAY=PENDING; YESTERDAY=CARRY_FORWARD** remains accurate at this refresh.

## Reproducibility

Final exact verifier SHA-256: **92b9e97eee7d46f9ea0901a7f31c8fd086ffc8fb201a02180bbee9e6347cccec**.
Credited logarithm helper SHA-256: **33464a4aa23a2480eae2971e38666a8272b0fee107cb4e93fbceee12480038f4**.
Preregistration SHA-256: **86ec2660e53518d41b3f1f0a33677fc096263967ca5c36a07e1aed1823f7eb13**.

Executed under Python 3.12.13; the complete verifier and syntax compilation passed. The exact registration, helper and verifier follow so this report is independently reproducible without a proof-branch write.

### Frozen Test Registration

```text
# SAT Large-GCD Test Registration

Run: 20261107-owner-1. Registered before execution.

- Original source: q=2R, Y=q^2-1, D=floor(sqrt R), e_c=Delta(floor(Y/c))-Delta(floor(Y/(2D))), D<c<2D.
- H1: on squarefree vertices the graph 7*gcd(c,d)>=2D is exactly the primitive types (2,3), (3,5), (5,6), with no repeated endpoint.
- H2: the same graph remains a matching under 4*gcd(c,d)>=D. Search for the first failure; the anticipated branching family is (30t,35t,42t), D=21t+1, squarefree t coprime to 210.
- H3: same-gcd ancestry forces a favorable nonpositive weighted cross term. This is a falsification control, not a revived all-gcd conjecture. Certify signs using actual pi-Li_2.
- Graph domain: D=1..256. Check the exact matching and complete-square identities on four fixed integer vectors. Check the growing cutoff G=ceil(sqrt D) and explicit divisor-degree bound.
- Original prime-error domain: R=16..256 plus held-out roots 483,484,485. Interval quadrature through the largest required x_D, without requiring Li_2 floors. Ambiguous signs remain unknown.
- Complete original source and symbolic Li_2 reconstruction: R in {64,81,100,121,255,256,257,484}. Preserve A,I,L,E,C and every square cross term. Reconstruct smooth and unselected physical terms independently.
- Boundary controls: (c,d)=(5g,6g), D=3g+1 for squarefree g coprime to 30; t in {1,11,13,17,19} for sharpness family. Synthetic vectors refute only universal coefficient inequalities, not actual Delta estimates.
- All arithmetic except certified interval division is integer/Fraction. No exponent fitting, zero computation, Lean execution, or claim of independent external review.

The logarithm interval helper is copied from November 6 Owner's credited Census reference, blob 1856a96aaaa9d86a5ee2d59ffe50ced936443fa6. The graph theorem and source tests are new; the helper is not a new discovery.
```

### Credited Logarithm Interval Helper

```python
"""Exact JOH clock test with independently certified Li_2 floors."""

import hashlib
import json
import platform
import time
from collections import Counter
from decimal import Decimal, localcontext
from math import isqrt
from pathlib import Path

S = 1 << 128
LIMIT = 16640
SCALES = (128, 256, 512, 1024, 2048, 4096, 8192)


def ceildiv(a, b):
    return -((-a) // b)


def mul(a, b):
    return a[0] * b[0] // S, ceildiv(a[1] * b[1], S)


def log_unit(num, den):
    # 1 <= num/den <= 2; 48 atanh terms, with an explicit geometric tail.
    t = ((num - den) * S // (num + den),
         ceildiv((num - den) * S, num + den))
    t2 = mul(t, t)
    p = t
    lo = hi = 0
    for k in range(48):
        lo += p[0] // (2 * k + 1)
        hi += ceildiv(p[1], 2 * k + 1)
        p = mul(p, t2)
    tail = ceildiv(18 * S, 8 * 97 * 3 ** 97)
    return 2 * lo, 2 * hi + tail


LOG2 = log_unit(2, 1)


def log_ratio(num, den=1):
    assert num >= den > 0
    k = (num // den).bit_length() - 1
    v = log_unit(num, den << k)
    return v[0] + k * LOG2[0], v[1] + k * LOG2[1]


def invlog(num, den):
    lo, hi = log_ratio(num, den)
    assert lo > 0
    return S * S // hi, ceildiv(S * S, lo)
```

### Complete Executed Verifier

```python
"""Exact SAT cofactor graph and complete-source regression.

Finite checks support, but do not replace, the report's all-scale proof.
Li intervals use the credited 128-bit outward-rounded reference helper.
"""

from collections import Counter
from fractions import Fraction as F
from itertools import combinations
from math import gcd, isqrt

from li_reference import S, ceildiv, invlog


GRAPH_LIMIT = 256
ROOTS = tuple(range(16, 257)) + (483, 484, 485)
SOURCE_ROOTS = (64, 81, 100, 121, 255, 256, 257, 484)
LIMIT = max(4 * r * r - 1 for r in ROOTS + SOURCE_ROOTS)


def sieve(n):
    mu = [1] * (n + 1)
    mu[0] = 0
    largest = [0] * (n + 1)
    prime = bytearray(b"\x01") * (n + 1)
    prime[:2] = b"\x00\x00"
    for p in range(2, n + 1):
        if not largest[p]:
            for k in range(p, n + 1, p):
                largest[k] = p
                mu[k] = -mu[k]
            for k in range(p * p, n + 1, p * p):
                mu[k] = 0
            for k in range(p * p, n + 1, p):
                prime[k] = 0
    pi = [0] * (n + 1)
    mertens = [0] * (n + 1)
    for k in range(1, n + 1):
        pi[k] = pi[k - 1] + prime[k]
        mertens[k] = mertens[k - 1] + mu[k]
    return mu, largest, prime, pi, mertens


mu, largest, prime, pi, M = sieve(LIMIT)


def edges(D, numerator=2, denominator=7):
    vertices = [c for c in range(D + 1, 2 * D) if mu[c]]
    return [(c, d) for c, d in combinations(vertices, 2)
            if denominator * gcd(c, d) >= numerator * D]


def predicted_edges(D):
    out = []
    for a, b in ((2, 3), (3, 5), (5, 6)):
        for g in range(1, D + 1):
            if (D < a * g < b * g < 2 * D and 7 * g >= 2 * D
                    and mu[g] and gcd(g, a * b) == 1):
                out.append((a * g, b * g))
    return sorted(out)


def divisor_count(n):
    return sum(n % d == 0 for d in range(1, n + 1))


edge_total = 0
vector_checks = 0
first_branch = None
for D in range(1, GRAPH_LIMIT + 1):
    high = edges(D)
    assert high == predicted_edges(D), D
    degree = Counter(c for edge in high for c in edge)
    assert max(degree.values(), default=0) <= 1, D
    edge_total += len(high)
    vertices = [c for c in range(D + 1, 2 * D) if mu[c]]
    all_pairs = list(combinations(vertices, 2))
    for mode in range(4):
        values = {c: (1 if mode == 0 else (-1) ** c if mode == 1
                      else c % 7 - 3 if mode == 2 else mu[c])
                  for c in vertices}
        I = sum(mu[c] * values[c] for c in vertices)
        diagonal = sum(values[c] ** 2 for c in vertices)
        C_hi = 2 * sum(mu[c] * mu[d] * values[c] * values[d]
                       for c, d in high)
        C_lo = 2 * sum(mu[c] * mu[d] * values[c] * values[d]
                       for c, d in all_pairs if 7 * gcd(c, d) < 2 * D)
        matched = set(degree)
        packets = sum((mu[c] * values[c] + mu[d] * values[d]) ** 2
                      for c, d in high)
        packets += sum(values[c] ** 2 for c in vertices if c not in matched)
        assert abs(C_hi) <= sum(values[c] ** 2 for c in matched)
        assert I * I == diagonal + C_hi + C_lo == packets + C_lo
        vector_checks += 1
    looser = edges(D, 1, 4)
    deg_loose = Counter(c for edge in looser for c in edge)
    if first_branch is None and max(deg_loose.values(), default=0) > 1:
        vertex = min(c for c in deg_loose if deg_loose[c] > 1)
        first_branch = (D, vertex, [e for e in looser if vertex in e])
    G = isqrt(D)
    G += G * G < D
    general = [(c, d) for c, d in all_pairs if gcd(c, d) >= G]
    deg_general = Counter(c for edge in general for c in edge)
    for c, degree_c in deg_general.items():
        assert degree_c <= (F(D, G) + 1) * divisor_count(c)

print("observed_first_D_over_4_branch:", first_branch, flush=True)
assert first_branch == (4, 5, [(5, 6), (5, 7)])
print("graph_D_range:", (1, GRAPH_LIMIT), "edges:", edge_total)
print("complete_vector_checks:", vector_checks)
print("first_D_over_4_branch:", first_branch)

for t in (1, 11, 13, 17, 19):
    D = 21 * t + 1
    assert mu[t] and gcd(t, 210) == 1
    a, b, c = 30 * t, 35 * t, 42 * t
    assert D < a < b < c < 2 * D
    assert gcd(a, c) == 6 * t and gcd(b, c) == 7 * t
    assert mu[a] == mu[c] == -mu[t] and mu[b] == mu[t]
print("sharpness_family: PASS (t=1,11,13,17,19)")
for D, support, expected in ((4, (5, 6, 7), 6), (22, (30, 35, 42), 4)):
    selected = [edge for edge in edges(D, 1, 4)
                if all(c in support for c in edge)]
    # The coefficient vector is u_c=mu(c)e_c=1 on these actual vertices.
    assert 2 * len(selected) == expected > len(support)
    print("universal_vector_obstruction:", D, "cross=", expected,
          "diagonal=", len(support))
closed = [(c, d) for c, d in combinations((3, 5, 6), 2)
          if 7 * gcd(c, d) >= 2 * 3]
assert closed == [(3, 5), (3, 6), (5, 6)]
# (3,6) is a further edge whose primitive cofactor 1 enters at a closed wall.
assert len(closed) == 3
print("closed_wall_control_D3: three squarefree vertices, triangle")
for b in (F(7, 8), F(503, 576), F(4, 5)):
    diagonal_power = F(1, 2) + 3 * b
    growing_power = F(3, 4) + 3 * b
    assert 4 * b - growing_power == b - F(3, 4)
    assert growing_power - diagonal_power == F(1, 4)
assert F(503, 576) - F(3, 4) > F(1, 16)
print("exact_power_accounting: PASS; eta=1/16 is only a proper-sector margin")


def li_bounds(nmax):
    out = [(0, 0)] * (nmax + 1)
    lo = hi = 0
    for n in range(2, nmax):
        m = 64 if n < 16 else 16 if n < 128 else 4
        lower = upper = 0
        for i in range(m + 1):
            w = 1 if i in (0, m) else 4 if i % 2 else 2
            f = invlog(n * m + i, m)
            lower += w * f[0]
            upper += w * f[1]
        error = ceildiv(1544 * S, 180 * m ** 4 * n ** 4)
        lo += lower // (3 * m) - error
        hi += ceildiv(upper, 3 * m) + error
        out[n + 1] = (lo, hi)
    return out


def interval_product(a, b):
    products = [x * y for x in a for y in b]
    return min(products), max(products)


li_limit = max((4 * r * r - 1) // isqrt(r) for r in ROOTS)
li = li_bounds(li_limit)
first_positive = first_negative = None
first_positive_pair = None
counts = Counter()
for R in ROOTS:
    Y, D = 4 * R * R - 1, isqrt(R)
    anchor = Y // (2 * D)
    actual = {}
    for c in range(D + 1, 2 * D):
        x = Y // c
        count = (pi[x] - pi[anchor]) * S
        actual[c] = (count - li[x][1] + li[anchor][0],
                     count - li[x][0] + li[anchor][1])
    if R in (64, 65):
        print("actual_endpoint_counts:", R,
              [(c, Y // c, pi[Y // c] - pi[anchor]) for c in (10, 15)],
              "anchor", anchor)
    low = high = 0
    for c, d in edges(D):
        p = interval_product(actual[c], actual[d])
        if mu[c] * mu[d] < 0:
            p = (-p[1], -p[0])
        low += 2 * p[0]
        high += 2 * p[1]
        if p[0] > 0 and first_positive_pair is None:
            first_positive_pair = (R, D, c, d, gcd(c, d),
                                   F(2 * p[0], S * S), F(2 * p[1], S * S))
    if low > 0:
        counts["positive"] += 1
        if first_positive is None:
            first_positive = (R, D, low, high)
    elif high < 0:
        counts["negative"] += 1
        if first_negative is None:
            first_negative = (R, D, low, high)
    elif low == high == 0:
        counts["zero"] += 1
    else:
        counts["undecided"] += 1


def rational_bracket(lo, hi, den=S * S):
    scale = 10 ** 6
    return (F(lo * scale // den, scale), F(ceildiv(hi * scale, den), scale))


print("actual_error_roots:", len(ROOTS), "Li_cutoff:", li_limit)
print("Li_interval_width_upper:", F(max(hi - lo for lo, hi in li), S))
print("certified_large_gcd_signs:", dict(counts))
for label, row in (("first_positive", first_positive), ("first_negative", first_negative)):
    if row:
        print(label, row[:2], rational_bracket(row[2], row[3]))
if first_positive_pair:
    print("first_positive_pair:", first_positive_pair[:5],
          rational_bracket(first_positive_pair[5].numerator * first_positive_pair[6].denominator,
                           first_positive_pair[6].numerator * first_positive_pair[5].denominator,
                           first_positive_pair[5].denominator * first_positive_pair[6].denominator))


# Formal Li values keep every endpoint and quadratic cross term exact.
def poly(const=0, terms=()):
    p = Counter({(): const})
    for x, a in terms:
        p[(x,)] += a
    return {k: v for k, v in p.items() if v}


def add(*polys):
    out = Counter()
    for p in polys:
        for k, v in p.items():
            out[k] += v
    return {k: v for k, v in out.items() if v}


def scale(a, p):
    return {k: a * v for k, v in p.items() if a * v}


def mul(p, q):
    out = Counter()
    for a, u in p.items():
        for b, v in q.items():
            out[tuple(sorted(a + b))] += u * v
    return {k: v for k, v in out.items() if v}


symbolic_pairs = negative_packets = physical_sites = 0
for R in SOURCE_ROOTS:
    q, Y, D = 2 * R, 4 * R * R - 1, isqrt(R)
    x = {d: Y // d for d in range(1, q + 1)}
    anchor = x[2 * D]
    e = {c: poly(pi[x[c]] - pi[anchor], ((x[c], -1), (anchor, 1)))
         for c in range(D + 1, 2 * D)}
    I = add(*(scale(mu[c], e[c]) for c in e))
    A = scale(M[D], poly(pi[x[D]] - pi[anchor], ((x[D], -1), (anchor, 1))))
    T = -sum(M[d] * (pi[x[d]] - pi[x[d + 1]]) for d in range(D, 2 * D))
    L = add(*(poly(terms=((x[d], -M[d]), (x[d + 1], M[d])))
              for d in range(D, 2 * D)))
    E = add(poly(T), scale(-1, L))
    assert E == scale(-1, add(A, I))
    packet = [0]
    for d in range(1, q):
        packet.append(packet[-1] - M[d] * (pi[max(q, x[d])] - pi[max(q, x[d + 1])]))
    smooth = sum(mu[n] for n in range(1, Y + 1) if largest[n] <= q)
    C = smooth + packet[D - 1] + packet[q - 1] - packet[2 * D - 1]
    assert T == packet[2 * D - 1] - packet[D - 1]
    assert M[Y] == T + C
    assert add(L, E, poly(C)) == poly(M[Y])
    full_square = add(mul(L, L), mul(E, E), poly(C * C),
                      scale(2, mul(L, E)), scale(2 * C, L), scale(2 * C, E))
    assert full_square == poly(M[Y] ** 2)
    diag = add(*(scale(mu[c] ** 2, mul(e[c], e[c])) for c in e))
    cross_hi, cross_lo = {}, {}
    for c, d in combinations(e, 2):
        pair = scale(2 * mu[c] * mu[d], mul(e[c], e[d]))
        if 7 * gcd(c, d) >= 2 * D:
            cross_hi = add(cross_hi, pair)
        else:
            cross_lo = add(cross_lo, pair)
        symbolic_pairs += 1
    assert mul(I, I) == add(diag, cross_hi, cross_lo)
    for c, d in edges(D):
        g = gcd(c, d)
        if (c // g, d // g) == (5, 6):
            joined = add(scale(mu[c], e[c]), scale(mu[d], e[d]))
            exact = scale(mu[g], poly(pi[x[d]] - pi[x[c]],
                                     ((x[d], -1), (x[c], 1))))
            assert joined == exact and (anchor,) not in joined
            negative_packets += 1
    seen = set()
    for p in range(anchor + 1, x[D] + 1):
        if prime[p]:
            assert p > q
            k = Y // p
            assert D <= k < 2 * D
            for c in range(1, k + 1):
                n = p * c
                assert n not in seen and mu[n] == -mu[c]
                seen.add(n)
    physical_sites += len(seen)
    assert sum(mu[n] for n in seen) == T
    print("source_fixture:", (R, D, T, C, M[Y], len(edges(D))))

print("symbolic_pair_checks:", symbolic_pairs, "negative_anchor_packets:", negative_packets)
print("unique_physical_occurrences:", physical_sites)
print("PASS: exact source, Li symbols, all mixed squares, graph and prime-error intervals")
print("FINITE ONLY; no global saving, independent review, or Lean execution")
```

## Archived Early Checkpoint - Same Invocation

The following original checkpoint is retained as execution history. Its PENDING items and PR/main statuses are superseded by the final synthesis above; it was not a separate run.

# RH | Owner Payment - 2026-11-07

## A. Most Important Mathematical Development

IN_PROGRESS / PARTIAL. SAT is selected by protected rotation. Yesterday's BT1-BT2 already pay the former interior threshold from the established Mertens input; that result is not being rediscovered. The new question is whether large shared prime ancestry forces a sparse interaction graph on the ORIGINAL cofactor pairs, allowing a proper covariance sector to be bounded without any prime-error independence assumption. No new theorem or exponent gain is claimed at this checkpoint.

## B. Current Authoritative Objective

Main: d4df133117c5b58f90979d2eb680167ef37995cf.
AGENTS.md blob: 48b2a58ab5fcd402321a4dace511c7d54bf688a1.
CURRENT_PROOF_CONTRACT.md blob: 7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c.
baseline_ack=PAID_BASELINE_EXACT_CONSUMER_V1, policy blob 13d58dd12d90fbf1160812c7c93442dc5d0576ac.
deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1, policy blob ffd8f1c65cc4da656174956d4e03b48bea46768b.

Canonical target remains an all-R bound |pi(R^2)-VF_can(R^2)| <= C R log R. The explicit classical criterion premise of its terminal consumer remains. Existing strict native Mertens bounds and global signed-prefix covariance are paid baselines at their actual scopes, not new discoveries.

## C. Structural Hypothesis Investigated

For q=2R, Y=q^2-1, D=floor(sqrt R), x_c=floor(Y/c), retain
e_c=Delta(x_c)-Delta(x_(2D)), Delta=pi-Li_2, D<c<2D.
The exact source is I=sum mu(c)e_c, with cross term
2 sum_(D<c<d<2D) mu(c)mu(d)e_c e_d.
Test whether the sector gcd(c,d)>=D/3 on nonzero coefficients is a disjoint matching with prescribed reduced cofactor pairs, and whether a controlled extension to growing factor cores gives a useful sector bound. Challenge any proposed negative-sign interpretation and retain the entire lower-GCD complement.

## D. Mathematical Derivation

PENDING. Source definitions and established finite Abel/full smooth-return theorems were inspected in LargePrimeTerminalFlipLayers.lean (b7617df21b81002854a0d311ef7e02d9494154c3), SquareRootPostCrossingTail.lean (660772bad3663d14c0f3390e26925b57d1390080), and PrimeSieveSquareRootTransport.lean (721b7f557ea9f253598b1ae3508f31d9f10a9f4f).

## E. Quantitative Consequence

PENDING. No gain beyond the strongest applicable established input is asserted. The full return is M(Y)=L+E+C, E=-A-I, and includes every mixed term.

## F. Falsification And Circularity Review

Planned exact tests: classify every nonzero cofactor edge in a fixed small range; check no endpoint is reused; test sharpness when the GCD threshold is lowered; reconstruct complete source squares using formal independent Li_2 symbols and exact prime counts. Finite success will not prove an all-scale prime-error bound.

## G. Conceptual Interpretation

PENDING. Arithmetic factor constraints, not stochastic signs, determine the investigated graph.

## H. Competing Mechanisms

Continue exact factor-incidence bounds and the genuinely unpaid joint lower-GCD prime-error source. Do not reopen the already paid BT2 threshold or the RZ2-refuted uniform per-zero annihilator. VF-LOW and JOH retain yesterday's DR and MS results at their reviewed or unreviewed scopes.

## I. Specialist Handoffs

TODAY=PENDING for all upstream roles at intake (November 7 directory returned 404); YESTERDAY=CARRY_FORWARD. Retrieved November 6 Coordinator, Owner, Analytic, Wheel, Census, Referee and Lean reports, plus EXTERNAL_HANDOFFS.md. Coordinator's 23:09 SAT recommendation agrees with protected rotation. Precise new handoffs will follow the derivation. No specialist was launched.

## J. First Independently Missing Lemma

The original OPEN-SAT-CROSS remains unproved. This run attempts an independently justified proper-sector restriction, not an assumption of that whole bound.

## K. Next-Run Resume Capsule

Run 20261107-owner-1; SCHEDULED 2026-11-07T00:09:01-05:00; RUN_ID_UNAVAILABLE.
Last three Owner routes: November 6 SAT, VF-LOW, JOH. Current SAT; next distinct route VF-LOW.
Open PR #1100 is ready/non-draft at e52207d527da684346e151d4ff680696c88e8fa7; 13 checks observed successful at that head. It is not main. Recent #1096-#1099 merges were directly checked. No new Lean execution occurred.
eta_gate=SEARCH_BROAD; independent review=PENDING; NEW_VERIFIED_ENDPOINT_GAIN=NONE.
Publication verification is pending the actual commit/readback.


## Verified Publication Receipt - 20261107-owner-1

At **2026-11-07T05:32:37Z**, research commit **a4a5abf075341e8c8d325e2986df1fb9b5afee9b** and report blob **c6e3e3295c4ca3ccd778b3926d613eb323015d4e** were re-fetched. The complete report matched the submitted text byte-for-byte, including the original checkpoint and the exact reproducibility sources. Commit metadata listed only this authorized Owner report. The final source refresh observed main **1c057c1d65b6d4cb4d59d207f69a815c52353314**, with all SAT and policy blobs unchanged after the human merge of #1100.

Final research status: **PAPER_PROOF / FINITE_COMPUTATION; SELF_AUDIT; INDEPENDENT_REVIEW_PENDING; NOT_FORMALIZED**. Publication is verified; independent mathematical acceptance and a new complete endpoint gain are not claimed. Next protected Owner route: **VF-LOW**. No background computation remains running.

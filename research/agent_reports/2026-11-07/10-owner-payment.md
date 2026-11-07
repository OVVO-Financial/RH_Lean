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


## Scheduled VF-LOW Continuation Checkpoint - 2026-11-07 08:09 EST Invocation

### A. Most Important Mathematical Development

PARTIAL / IN_PROGRESS. No new theorem is claimed at this checkpoint. Resume
20261106-owner-2/DR1-DR7, particularly the demand-rich/prime-poor interval
obstruction. Investigate whether the established zero-free strip, classical
zero-density estimates, and the exact chronological reserve yield a quantitative
exceptional-set restriction at the ORIGINAL square sample locations. An
average-in-location result alone does not justify this sampling.

### B. Current Authoritative Objective

Actual scheduled trigger 2026-11-07T08:09:01-05:00; RUN_ID_UNAVAILABLE.
Current main: 1c057c1d65b6d4cb4d59d207f69a815c52353314.
AGENTS blob 48b2a58ab5fcd402321a4dace511c7d54bf688a1; proof-contract blob 7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c.
baseline_ack=PAID_BASELINE_EXACT_CONSUMER_V1, policy 13d58dd12d90fbf1160812c7c93442dc5d0576ac.
deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1, policy ffd8f1c65cc4da656174956d4e03b48bea46768b.

The canonical actual-prime von Koch objective is unchanged and open.
The native replay and existing strict slot gap remain established; they are
not re-proved or counted as a new gain. This investigation uses the native
zeta strip as an existing input to a different proper-source estimate.
Original VF seat-charge source: 87a6654a4a4337b409fde69aa15d7264d8b721b6.

### C. Structural Hypothesis Investigated

For the original dense triple rectangle and globally capacity-limited earlier
prime allocation, the reserve is the maximum future signed interval deficit.
A large reserve may persist over a physical neighborhood because the genuine
positive demand has a factor-sensitive local upper bound. If proved, this
thickness could transfer an analytic exceptional-measure estimate to square
roots without assuming independence or favorable placement of exceptions.

### D-K. Pending Derivation, Tests And Handoff

Pending: complete analytic derivation with quantified height truncation;
actual prime-power removal; finite and square-boundary falsification;
full signed complement and quadratic return; comparison with DR4;
independent review and formalization status; final source/PR freshness.
No all-root canonical or Mertens improvement is asserted.

Continuity: all today/yesterday role reports have been retrieved; relevant
mathematical sections are being checked. Today's Coordinator synthesis is
available (4a71edcce4c44a309640d36e9453d016e5b188a9), including PG1-PG5.
Its next protected Owner route is VF-LOW. Yesterday's DR derivation is
CARRY_FORWARD, not new work. Latest external inbox remains
038018145c0fddb2f6306c0712373adf9cd1ea52 with no entry newer than October 18.
Open PRs: #1102 (proof head 5b246ac81398ae8ee8f177dc9acda18288765a4e)
and #1101 (unmerged policy, not authority). #1100 is merged on current main.

Selected route VF-LOW; last actual Owner routes JOH, SAT, this VF-LOW;
next distinct protected route JOH. eta_gate=SEARCH_BROAD.
No agent launch, Lean execution, proof-source write, branch/PR or schedule
change is authorized or performed. Direct shell clone failed with CONNECT
403; connected GitHub retrieval works. Publication is claimed only after
commit verification and immutable readback.

## VF-LOW Reserve Thickness And Square-Sampled Energy - 20261107-owner-2

### A. Most Important Mathematical Development

**PAPER_PROOF / INDEPENDENT_COMPONENT_ADVANCE / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED.** The unchanged dense three-prime rectangle of 20261106-owner-2/DR1-DR7 admits a new all-scale restriction on its actual once-only chronological response. With the same donor cap and allocation, there are constants K,C,N0 such that

```text
sum_(integer N<=R<2N) |Q_N(R^2)|^2 <= C N^3/(log N)^6,
for every integer N>=N0.                                  (RS4)
```

This improves the prior consequence `O(N^(31/10)/(log N)^8)` obtained by summing DR4's pointwise bound. The simultaneously allocated dyadic response therefore satisfies

```text
sum_(integer R>=R0) |Q(R^2)|^2/R^3 < infinity.              (RS5)
```

The new structural step is **one-sided reserve persistence**: a large future funding requirement cannot disappear to the right without spending positive demand. The actual factor-sensitive demand bound makes any large value at a square boundary persist on a physical interval of length N. This supplies a rigorous transfer from a prime-poor exceptional-set estimate to the original square samples. Almost-everywhere information alone would not supply that transfer.

The analytic engine is explicitly reused from yesterday's **20261106-owner-3/MS2**, not rediscovered: the established zeta zero boundary plus the classical 12/5 zero-density estimate and the full high-zero tail. The new work is its source-faithful application to the dense reserve, the sampling proof, and the weighted all-scale conclusion. Its inherited analytic proof remains at paper/self-audit scope; this run checks the specialization, not independent Referee acceptance.

For the actual best input `b_*=7/8-delta_*`, where `delta_*=1/(288 explicitSlotCount)>0`, put `s_*=(4/5)(1-b_*)=1/10+(4/5)delta_*`. The more precise new exceptional-root bound is

```text
#{N<=R<2N : |Q_N(R^2)|>2K N/(log N)^3}
  <<_epsilon N^(1-2s_*+epsilon).                           (RS3)
```

The rounded power is `4/5+epsilon`, with the existing strict slot gain retained in the displayed formula. This is NOT a new zero-free strip or Mertens exponent. Neither the pointwise proper-class target `O(N log N)` nor the full canonical VF target is established. The original complement and its mixed term remain present and uncontrolled. **NEW_VERIFIED_ENDPOINT_GAIN=NONE; eta_gate=SEARCH_BROAD.**

Claim ledger: RS1 PAPER_PROOF (finite persistence); RS2 PAPER_PROOF (specialization of inherited analytic input and prime-poor cover); RS3 PAPER_PROOF (source-exact square sampling); RS4-RS5 PAPER_PROOF (proper-source quantitative bounds); RS6 FINITE_COMPUTATION plus REFUTED (two-sided demand-only shortcut). No new claim is PROVED_IN_LEAN.

### B. Current Authoritative Objective

Actual invocation: SCHEDULED **2026-11-07T08:09:01-05:00**, America/New_York; RUN_ID_UNAVAILABLE. Route **VF-LOW**, resuming DR5's demand-rich/prime-poor obstruction as suggested by today's Coordinator. This is the second actual Owner invocation represented in this daily file, after SAT. Protected route sequence: yesterday JOH, today SAT, this VF-LOW; next JOH. No additional execution or schedule is inferred.

Latest actual main at intake and the 13:32 UTC prepublication refresh: **1c057c1d65b6d4cb4d59d207f69a815c52353314**, tree **beb042acf728f3447aa7f18456c678d048360ab2**. `baseline_ack=PAID_BASELINE_EXACT_CONSUMER_V1`; `deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1`. Main's paid baseline and strict gap are preserved, not listed as unproved suppliers. Unmerged policy PR #1101 is not authority.

Material blobs actually retrieved at that main, with original relevant definitions and theorem statements inspected:

| Source | Blob SHA |
| --- | --- |
| AGENTS.md | 48b2a58ab5fcd402321a4dace511c7d54bf688a1 |
| CURRENT_PROOF_CONTRACT.md | 7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c |
| Paid-baseline correction, 20261106 | 13d58dd12d90fbf1160812c7c93442dc5d0576ac |
| Independent multi-front policy, 20261104 | ffd8f1c65cc4da656174956d4e03b48bea46768b |
| Native square-clock selector, 20261029 | 973d3d549a52a1afe2f02bfdcf8cc35fb6a76515 |
| Broad-search policy, 20261031 | 8317f08996b65f2e4b32c00c91b31cb6d0c09718 |
| Source-faithful complete-return contract, 20261031 | 4775ee5fd95f279beab08a75d1e17127078b19a6 |
| VF_MID_SIGNED_SEAT_CHARGE.lean | 87a6654a4a4337b409fde69aa15d7264d8b721b6 |
| VF_MID_ODD_FRACTIONAL_CLUSTER.lean | 942badff45c03d2a9e97789b57d1bd8052232191 |
| VF_MID_NATIVE_LYAPUNOV_SEAT_GRAM.lean | 23e7b0c5c9f4b50997a508345d91f30364f93f10 |
| VF_MID_915_EXACT_HISTORICAL_NNS_COMPRESSION.lean | 6cc6b2a9d25279dd44fb65cb222f5d6846a912d4 |
| VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |
| oai_434/VF919NativeSevenEighthsReplay.lean | 111c933a7ca15647105ce6a4d0f3cbfc3cde81f4 |
| oai_434/VF919NativeStrictMertens.lean | b33a4883e1ddb0551b0f11f062bce46680d87450 |
| oai_434/VF919ExplicitFixedSourceSlotCount.lean | bad5aab0a60e96d19e7c9550cd7c0a072288bc0f |

The canonical definitions, all with natural logarithms, remain

```text
w_r=(2+1/r)/log(r^2+r+1/2),
F_R=sum_(2<=r<R) r*w_r,
D_R=pi(R^2)-F_R,  D_can(R)=D_R-sqrt(2),
exists C>=0, forall integer R>=2, |D_can(R)|<=C R log R.     (OPEN)
```

For each actual odd nonsquare seat `r^2<n<(r+1)^2`, the original charge is `w_r-1_Prime(n)`. There are r seats per block. Composite charge is positive w_r; prime charge is `-(1-w_r)`. The original starting anchor is `-D_2=-2`. The canonical/RH bridge still has its explicit `ClassicalVonKochRHCriterion` and arithmetic antecedent; green conditional code does not establish those premises.

The inherited input used here is concrete: `native_zeta_zero_re_le_hecke_beta` and `native_beta_le_explicit_slot_count` imply that every actual nontrivial zeta zero has real part at most b_*. `explicitSlotCount_two_le` gives `503/576<=b_*<7/8`. This is a fixed repository constant, independent of N, the root, the prime donor, and the zero height. We use the zero-location statement, not an unproved transfer from global Mobius energy to local prime covariance.

**PR/CI status.** Current open PRs are #1102, non-draft head `5b246ac81398ae8ee8f177dc9acda18288765a4e`, and policy #1101, non-draft head `690477c55070aabafefbaff883880a5c37c44370`. #1102 has 13 successful retrieved checks at its exact head; it is not main. Its detailed GL2 log verdict is attributed to today's Lean report, not claimed as a log reread here. Recent merged #1100, #1099, #1098, #1097 and #1096 were discovered; their radical/moment/sampling/policy results do not prove RS1-RS5.

The inherited strict-baseline #1091 head `6778fd4c25b0f369d311e6e71223e168e329b4bf` also has 13 successful retrieved checks. Its actual dedicated run **41898325686**, job **126813711885**, was fetched and read: the fixed-count endpoint audit succeeds and `native_beta_le_explicit_slot_count` uses only `[propext, Classical.choice, Quot.sound]`. This is reused exact-head evidence, not a new build. No local Lean, new CI execution, or independent mathematical review occurred.

### C. Structural Hypothesis Investigated

Preserve the exact DR carrier. For integer N sufficiently large let ell=log N, X=N^2, and

```text
S_N={prime p: sqrt N<p<=(11/10)sqrt N},
T_N={prime q: (3/2)N<q<=(7/4)N},
F_N={q*p*s: q in T_N, p,s in S_N, p<s}.
d_n=w_(floor sqrt n) on F_N, and 0 otherwise,
a_N=1/ceil(ell)^2,
c_n=a_N*(1-w_(floor sqrt n)) on actual primes X<n<4X,
    and 0 otherwise.
```

Each selected site occurs once by unique factorization and separated factor ranges. It is odd, squarefree and has exactly three distinct factors; `3X/2<n<=847X/400<4X`. Donors are genuine prime occurrences, chronologically earlier than the demands they fund, not divisor-parent edges or returned-mask admissions. Each donor's total used fraction is at most a_N, however many demands share it. The construction allocates the entire rectangle simultaneously.

The inherited reserve and allocated response are

```text
b_N(t)=max(0,max_(t<m<=4X) sum_(t<n<=m)(d_n-c_n)),
u_p=min(c_p,b_N(p)),
Q_N(t)=sum_(X<n<=t)d_n-sum_(X<p<=t)u_p=-b_N(t).             (DR1)
```

The maximum may be taken over integer endpoints; define b_N as a right-continuous step function for real t. DR1 proves the exact recurrence, global FIFO feasibility and zero boundary inventories. DR3-DR4 give, uniformly for intervals I=(t,t+H] inside [X,4X],

```text
D_N(I)<=C0 N/ell^3 * (1+(H/N)/log(2+H/N)),                 (D)
H>=H0:=2(4X)^(21/40) ==> D_N(I)<=C_N(I),
sup_t b_N(t)<=C1 N^(21/20)/ell^4,  b_N(X)=b_N(4X)=0.       (B)
```

These are reused results, not new claims. For (D), each unordered pair p<s gives a q-interval of length comparable to H/N; summing the uniform prime upper bound counts each selected site exactly once. The primary [Montgomery-Vaughan Theorem 2, (1.12)](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf#page=3) was rechecked. For (B), the actual input is the forward **count** lower bound in [Baker-Harman-Pintz, concluding p.562](https://www.cs.umd.edu/~gasarch/BLOGPAPERS/BakerHarmanPintz.pdf#page=31), not just one prime. Concatenation gives capacity of order H/ell^3 for H>=H0, whereas demand is O(H/ell^4). No assumption of initial reserve is made.

The tested hypothesis is that factor-limited demand prevents a sparse set of bad physical intervals from hiding at all relevant square boundaries. A competing two-sided continuity conjecture is false: fresh prime capacity can increase the reserve when there is no positive demand. Only the correct one-sided statement is used.

### D. Mathematical Derivation

#### RS1. Finite One-Sided Persistence

For arbitrary finite nonnegative demand and capacity, and all real A<=t<=s<=B,

```text
b(s)>=b(t)-D((t,s]).                                     (RS1)
```

If b(t)=0 there is nothing to prove. Otherwise choose an endpoint m attaining its positive maximum. If m<=s, then `b(t)<=D((t,m])<=D((t,s])`. If m>s, split its signed sum at s; its first part is at most D((t,s]), and its remaining part is at most b(s). Both cases give the inequality. No allocation, prime distribution, independence or favorable covariance is assumed in this finite lemma. In the feasible actual source it describes the same b_N and Q_N, not a new auxiliary boundedness hypothesis.

#### RS2. Prime-Poor Exceptional Measure With Complete Zero-Height Return

This subsection specializes the already supplied 20261106-owner-3/MS2 machinery to the fixed shift t+h. Its new analytic parameter is h in `[c sqrt(X), C X^(21/40)]`, with fixed positive c,C. For a fixed boundary `1/2<=b<=7/8`, assume every nontrivial zeta zero satisfies beta<=b. Put `U=X/h` and `s=(4/5)(1-b)`. The specialized estimate is

```text
J_psi(X,h):=integral_X^(4X) |psi(t+h)-psi(t)-h|^2 dt
 <<_(b,epsilon,c,C) X^epsilon *
    [X*h + X*h^2 * ((X/h)^(12/5)/X^2)^(1-b)]
 <<_(b,epsilon,c,C) h^2 X^(1-s+epsilon).                  (RS2a)
```

The independent density input is `N(sigma,V)<<V^((12/5)(1-sigma))*log^B(2V)` uniformly for `1/2<=sigma<=1`. Its statement and scope were checked in the author's [Zaccagnini, Section 2.1, (4)](https://people.dmi.unipr.it/alessandro.zaccagnini/psfiles/papers/Q429.pdf#page=3). No density hypothesis or pair-correlation conjecture is assumed. The symmetric explicit formula and unit-height zero count are classical ingredients also inspected in [Saffari-Vaughan, Section 6](https://www.numdam.org/article/AIF_1977__27_2_1_0.pdf#page=20). The following retained derivation is an audit of the existing MS2 method, not a quotation of a new theorem from either paper.

For a finite set of actual zeros up to height V, integrated expansion of `sum c_rho t^rho` over a fixed-ratio interval pays each pair by a kernel of size `(1+|gamma-gamma'|)^(-1)`. The actual count of zeros in each unit-height interval is O(log(2V)); hence every row sum is O(log^2(2V)). Weighted Cauchy gives

```text
integral |sum c_rho t^rho|^2 dt
  << X log^2(2V) sum |c_rho|^2 X^(2 beta).
```

For powers `t^(rho-1)` the same proof has X^(-1) instead of X. This retains all diagonal and off-diagonal terms before bounding them; no zero-pair independence is used. Constants are uniform for the fixed-ratio intervals inside [X,5X].

Define `S_X(V)=sum_(|gamma|<=V) X^(2 beta)`. Integrating the low-height increment over [t,t+h] and using Cauchy/Fubini gives squared norm at most `h^2 X^(-1) log^2(2U) S_X(U)`. A high band `V<|gamma|<=2V` has increment `F_V(t+h)-F_V(t)`, where `F_V(t)=sum t^rho/rho`. Translation preserves Lebesgue measure, and the preceding pair bound gives squared norm at most `X V^(-2) log^2(2V) S_X(2V)`.

Layer-cake and the density estimate imply

```text
S_X(V) << X V log(2V)
 + log X log^B(2V) integral_(1/2)^b
                    X^(2 sigma) V^((12/5)(1-sigma)) d sigma.
```

In the high squared bound, the exponent of V is at most `-4/5` throughout that integral; the beta<=1/2 part decays as V^(-1). Summing the square roots over V=2^j U converges geometrically, even with the logarithmic factors. Minkowski pays all cross-height terms. Only after this tail comparison at U do we maximize in sigma: `2 log X-(12/5)log U>0` in the stated range, so the maximum is at b. This proves the first bound in RS2a. Maximizing at b before summing arbitrary high V would not be justified.

The symmetric explicit formula identifies the L2 limit with the actual psi difference almost everywhere, using admissible symmetric heights if necessary. Endpoint prime powers form a null set in this integral; the next step handles their contribution separately. The constant term cancels, the trivial-zero increment is negligible, and the low/high mixed term is paid by the squared triangle inequality, not set to zero. Finally `U<=c^(-1)sqrt X`, so `U^(12/5)/X^2<<X^(-4/5)`. The term Xh is smaller than the second upper scale since `s<=2/5`. These facts prove the second bound with constants independent of X and h in the specified range.

Define the actual prime-poor set

```text
E_h={t in [X,4X]: pi(t+h)-pi(t)<=h/(4 log(5X))}.
```

For such t the contribution of first powers of primes to the psi increment is at most h/4. Squares contribute `O((h/sqrt X+1)log X)`. Since `h<<X^(21/40)=o(X^(2/3))`, each higher exponent contributes O(1) possible integer powers, with O(log X) exponents and weights O(log X). Thus the whole higher-prime-power contribution is `O((h/sqrt X+log X)log X)=o(h)` uniformly here. For sufficiently large X, every t in E_h satisfies `|psi(t+h)-psi(t)-h|>=h/2`. Chebyshev and RS2a give

```text
Lebesgue_measure(E_h)<<_epsilon X^(1-s+epsilon).            (RS2b)
```

Now return to the exact reserve. Choose a fixed L0 large enough that

```text
8 C0 [1/L+1/log(2+L)]<=1/128  for every L>=L0.
```

Choose fixed K larger than the demand constants in (D) for all H<=L0 N, including H=N, and write `B_N=K N/ell^3`. If b_N(t)>B_N, a maximizing interval (t,t+H] has positive deficit, H>L0 N by (D), and H<H0 by (B). Every actual prime has `c_p>=1/(8ell^2)` for large N. Therefore

```text
pi(t+H)-pi(t) < 8ell^2 D_N((t,t+H])
             <= H/(128ell).
```

Choose a power of two h with H/2<h<=H. Monotonicity of prime counts gives `pi(t+h)-pi(t)<=h/(64ell)<=h/(4log(5X))`. This h lies between L0 N/2 and H0. Only O(log N) such dyadic lengths occur. Consequently, after absorbing that logarithm in an arbitrary positive loss,

```text
measure{t in [X,4X]: b_N(t)>B_N}
  <<_epsilon X^(1-s+epsilon).                             (RS2c)
```

Every length, threshold and exceptional event in this argument concerns the same actual prime/composite source. The huge but fixed choices of L0,K and N0 are not evaluated by the finite tests.

#### RS3. Sampling The Actual Square Boundaries

For every integer N<=R<2N, (D) and our choice of K give `D_N((R^2,R^2+N])<=B_N`. RS1 then shows

```text
b_N(R^2)>2B_N ==> b_N(t)>B_N
                 for every t in [R^2,R^2+N).
```

These intervals all lie in [X,4X] and are pairwise disjoint: consecutive squares are separated by `2R+1>N`. Thus

```text
N * #{N<=R<2N : b_N(R^2)>2B_N}
 <= measure{t in [X,4X]: b_N(t)>B_N}.
```

Combining this with RS2c and renaming the arbitrary positive loss proves RS3. No integer square is discarded as a null-set exception. This is the essential source-specific sampling bridge.

#### RS4-RS5. Mean Square And Once-Only All-Scale Energy

The nonexceptional roots contribute at most `4K^2 N^3/ell^6`. Use the inherited uniform bound (B) at every exceptional root, retaining the exact exceptional exponent from RS3:

```text
sum_(N<=R<2N) b_N(R^2)^2
 << N^3/ell^6 + C_epsilon N^(31/10-2s_*+epsilon)/ell^8.
                                                               (RS4a)
```

Because `s_*>=1/10`, the second power is at most `29/10+epsilon`, strictly below 3 for fixed epsilon<1/10. It is eventually absorbed by the first term. This proves RS4 for every sufficiently large integer N, not only a selected subsequence.

For the global construction use only N=2^k>=N0. Its donor intervals `(N^2,4N^2)` are disjoint, and each completed shell has Q_N=0 exactly. Therefore at any physical cut at most one shell contributes. No earlier prime is cloned and no historical reserve is accumulated. Since R>=N on that shell,

```text
sum_(N<=R<2N) Q(R^2)^2/R^3 <= C/(log N)^6.
```

Summation over k converges, proving RS5. Finite initial scales are left in the original complement, as in DR4, not silently dropped from the canonical object.

### E. Quantitative Consequence And Complete Return

The precise improvement packet is:

| Item | Exact scope |
| --- | --- |
| Established inputs | DR1/DR3/DR4 on this genuine dense rectangle; existing b_* zero boundary; inherited MS2 full-height method; classical 12/5 density |
| New arithmetic | Factor-sensitive demand forces persistent physical neighborhoods for high square-sampled reserves |
| First loss | DR3 upper-bounds positive q-counts; RS2 uses absolute integrated zero-pair row sums, then low/high Cauchy and a dyadic exceptional-set union |
| Old selected energy | Summing the pointwise DR4 estimate gives `N^(31/10)/ell^8` |
| New selected energy | `N^3/ell^6`, with the exceptional term `N^(31/10-2s_*+epsilon)/ell^8` |
| RMS comparison | Old `N^(21/20)/ell^4`; new `N/ell^3`; this is a root average, NOT a pointwise estimate |
| Actual complete consumer | The exact original VF split below; no new full endpoint bound follows without further signed information |

Let C_F(R) retain the original anchor -2, every unselected positive seat, every squareful/exceptional contribution, each unused fraction of every donor, all other primes, and every initial-scale term. The exact complete equations remain

```text
-D_R = C_F(R)+Q(R^2),
D_R^2=C_F(R)^2+Q(R^2)^2+2*C_F(R)*Q(R^2),
D_can(R)^2=D_R^2-2*sqrt(2)*D_R+2.                         (RETURN)
```

RS4 bounds the Q-square on a dyadic block, not the C_F-square or the mixed term. Even Q<=0 says nothing about the mixed sign without C_F. Weighted Cauchy could control the mixed term only with an additional estimate on C_F in the same norm; none is assumed or proved. Conversely a future full argument may use compensation without separately bounding C_F. The ordinary native square-shell Lyapunov identity retains history-current, diagonal and anchor terms; this report does not turn it into zero covariance.

The original #915 source is still `Source=D_(R+1)` and `TotalMass=(|D_R|+beta_R)^2`, not an enlarged denominator. Decompressing historical positive/negative masses U,V restores exactly `4UV+2 beta_R(U+V-|U-V|)`. This bill, genuine clipping/admission and the first-bad premise are not paid by RS4 or RS5. The final canonical phase is explicitly present in RETURN. **Canonical VF, original #915, a new Mertens exponent and RH are not concluded.**

### F. Falsification And Circularity Review

**RS6: actual tests, not asymptotic evidence.** Development N=9216 and held-out N=10000 were frozen before execution. They contain respectively three and four small primes, so the fixtures test simultaneous pair families and shared donor use beyond yesterday's two-small-prime cases. There was no range extension, exponent fit or claim that these N exceed the analytic N0.

The prior DR helper supplies rational log enclosures at scale 10^40, 50 atanh terms after power-of-two reduction, an outward geometric tail, and original w_r enclosures with denominator 10^18. Integer sieving is exact. For each lower/upper envelope the new verifier recomputes the full chronological reserve, capacity-limited FIFO, one-sided persistence at every square and event in its N-neighborhood, the high-reserve measure, and every original block's full signed/quadratic reconstruction. All assertions and Python syntax compilation passed.

| Fixture | Selected sites | q-primes | Used prime occurrences per envelope | Allocation edges | Nonzero square samples |
| --- | --- | --- | --- | --- | --- |
| N=9216; small primes 97,101,103 | 732 | 244 | 8784 | 8784 | 5 |
| N=10000; small primes 101,103,107,109 | 1560 | 260 | 18720 | 18723 | 12 |

There are 12,710 and 17,750 persistence checks per envelope and 9,216 and 10,000 complete-square checks per envelope. The exact squared-reserve sums are enclosed by these integer numerator intervals, all divided by 10^40:

```text
N=9216:
[430043108024829000662538278727035597212,
 430043108024829010006964115810926933612] / 10^40
N=10000:
[644034756025160402085410569353264938529,
 644034756025160418872147551500942585379] / 10^40
```

Enclosure follows because increasing every weight increases d and decreases c, so the maximum defining b is monotone; b>=0 then makes its square monotone. This is not a floating-point fit.

The stronger conjecture `|b(s)-b(t)|<=D((t,s])` is **REFUTED on the actual source**. At genuinely used prime p=135482381 in the N=9216 fixture, D((p-1,p])=0 whereas b(p)-b(p-1)>0, with certified interval

```text
[856747932727355146,856747932727355257] / 10^20.
```

The second fixture independently has the same obstruction at p=156179939. Both primes were also trial-divided in the regression. This refutes only the two-sided auxiliary claim, not RS1 or the canonical objective.

All 97,655 signed sequences of lengths 1 through 7 over {-2,-1,0,1,2} passed 3,326,415 ordered-cut persistence checks. These generic sequences test the finite lemma, not prime-distribution hypotheses. The four tested arithmetic threshold levels 0,1/100,1/20,1/10 had **zero roots satisfying the sufficient thick-root test**; their sampling-count inequalities were therefore vacuous. This limitation was recorded before the revised test. A separate explicitly synthetic feasible fixture, capacity 20 at site 20 and demand 20 at site 60 on (16,64], gives exactly three thick roots 5,6,7 at threshold 10, disjoint neighborhood measure 12 and high-reserve measure 40. It verifies a nonvacuous finite sampling case, not an arithmetic prediction.

Density-one information without persistence was rejected: a function supported only on integer squares can have zero Lebesgue support measure while every square sample is large. This generic warning is not asserted to be an actual prime-source counterexample. RS1 plus (D), not numerical density, excludes that shortcut for the present reserve.

Exact rational exponent tests retain the preliminary valid but weaker truncated 8/3 path (`s=1/14`, exceptional energy `207/70` at b=7/8). On rereading MS2 we replaced it with the stronger already available full-height 12/5 method (`s=1/10`, exceptional energy `29/10`). The initial path was not disproved; presenting it as the strongest new analytic result would have ignored continuity. Diagnostic b=503/576 gives s=73/720 and exceptional energy 1043/360. Neither diagnostic b is substituted for the unevaluated actual slot count in the theorem.

Circularity audit: RS1 is finite algebra; (D) is an independent upper sieve bound on actual factors; (B) uses an established short-interval prime lower bound; the zero boundary is an already compiled incoming result; density is an independent classical theorem. No all-scale canonical target, bounded new potential, independence axiom or desired prime-poor exclusion is assumed. The new claims are proper-source restrictions, not target-equivalent relabelings. The full-source RETURN is an identity only.

### G. Conceptual Interpretation

A prime-poor physical set is not automatically harmless or harmful at square boundaries. The directional way a true reserve changes supplies the missing connection: it can rise at a prime, but it can fall only by paying genuine selected composite demand. The multiplicative rectangle bounds that demand over a square-scale neighborhood. This makes high square values measurable at positive physical width, and converts inherited analytic information into a new restriction on the genuine signed allocation.

The resulting critical weighted energy is finite across all dyadic generations because old inventories close exactly, not because generations are independent. This changes what is known about the dense component while leaving room for a small exceptional set of large pointwise values. It neither vindicates ancestor-only payment nor excludes a more effective joint-source mechanism.

### H. Competing Mechanisms

| Mechanism | Status and obstruction | Decision |
| --- | --- | --- |
| Ancestor-only dense payment | Earlier CR3 capacity obstruction still applies | Abandon that fixed-budget universal claim |
| Chronological reserve plus factor-limited thickness | RS1-RS5 give new proper-source sampled energy | Continue at component scope; independent review next |
| Two-sided demand-only continuity | Actual prime-site counterexample in RS6 | Abandon; keep one-sided RS1 |
| Prime lower bound on every DR5 mesoscopic interval | OPEN-VF-DR-SI remains unsupplied | Keep as sufficient, not necessary; no stochastic substitute |
| Joint C_F/Q signed compensation | Exact RETURN available; no favorable mixed estimate | Preserve as distinct global option |
| Generic low-gcd sign-matrix spectral contraction | Today's Coordinator PG1-PG3 preserves conjugation and sharp clique obstruction | Do not reopen as a shortcut to the full signed sum |

No protected route is replaced by this component result. The next Owner route is JOH, resuming MS1-MS4 and their unfavorable complete endpoint comparison rather than redoing the prime-count clock bridge.

### I. Specialist Handoffs And Research Continuity

**Coordinator:** evaluate RS4-RS5 as a proper-source quantitative advance obtained by a new sampling bridge with inherited analytic inputs. Keep `NEW_VERIFIED_ENDPOINT_GAIN=NONE`. It is more useful than repeating DR's ancestry count or imposing a generic sign-matrix contraction; it does not justify centralizing all roles on payment or zero-density. The global conceptual question is whether the exact residual can exploit Q's weighted energy without assuming the desired bound.

**Analytic Type II:** independently audit RS2a-c as the fixed-shift specialization of MS2, especially the all-height geometric comparison before density maximization, the prime-power bound uniformly up to X^(21/40), and constants uniform across the O(log N) dyadic h. Your GL large-gcd result concerns a different genuine Mobius carrier; no transfer of its unsigned support estimate to prime membership is asserted. Keep your protected next route.

**Finite Wheel:** examine whether additional genuine factor incidence can force a stronger demand bound inside the remaining prime-poor exceptional intervals. A useful claim must cover the whole q*p*s rectangle with overlap counted once. Today's DI overlap at R=70/shared210 and positive mixed term at R=65 prohibit inferring full disjointness or an automatically negative mixed term.

**Prime Census:** do not extend the prime sieve solely to fit the asymptotic powers. If reviewing RS1-RS3, independently certify the two fixed actual fixtures and the explicitly synthetic nonvacuous sampling regression. Any proposed improvement should discriminate whether high reserve can persist on a shorter/larger quantitatively forced interval; freeze its exact coefficients, thresholds and held-out test first. Today's SC example X=21754 shows why endpoint-disjoint edges alone do not make label surplus additive; our verifier instead caps each physical prime's total coefficient globally.

**Adversarial Referee:** attack RS1-RS5 independently, with priority on real-cut endpoint cases, the high-zero tail, strict-gap substitution, prime powers, disjoint N-neighborhood sampling, and the dyadic once-only sum. Check that the root-exception count is never promoted to a pointwise bound and that RETURN retains C_F/Q mixing and the sqrt(2) phase. Author self-audit is not your acceptance. The small-gcd signed estimate remains open even though today's GL/ratio-profile work constrains its complementary region.

**Lean Verification:** after independent acceptance and an identified consumer, RS1 and its abstract disjoint-neighborhood corollary are finite candidates. Required hypotheses are nonnegative d,c, the exact future-deficit maximum, a uniform demand bound on every chosen neighborhood, and disjoint equal-length neighborhoods. Do not formalize an assumed RS2 or an unproved full endpoint as a wrapper. No new proof branch, PR or CI run is requested by this report.

All seven roles' relevant **today and yesterday** report sections were retrieved and read. `TODAY=AVAILABLE`; yesterday's valid evidence is `YESTERDAY=CARRY_FORWARD` at its original scope. This does not certify later unobserved scheduled runs.

| Role | November 6 blob | November 7 intake blob |
| --- | --- | --- |
| Coordinator 00 and 90, identical bytes | 8812a90540fb511279b5f4ce08e108ef717d5ef1 | 4a71edcce4c44a309640d36e9453d016e5b188a9 |
| Owner 10 | 1856a96aaaa9d86a5ee2d59ffe50ced936443fa6 | 1006bb9f0c61a22ceeb7fab25d177a40dc24f25e |
| Analytic 20 | 7997620b6ab7eb0701296994734ee910df3c3ba1 | 6712040159ca37ef3257cf507ec8198fd26fbb91 |
| Wheel 30 | 3099558194a00358962ff1844bf283e625b9283d | b943f16b0fedbcefa53545f8a7c77482e688399e |
| Census 40 | c34ac074296e8b2e5b20dee3a2ce02518571206c | c9d78787ca4fca22f89bc9bcaf886e5ae74deda2 |
| Referee 50 | da3265467c799e9d21832ab25245617ba3b15a54 | 787a9030cc6d6f8f63fa89cd3a99d7cf54e25ea5 |
| Lean 60 | b8bfe3ce9c20d7903395364efb39bcec974c8a2f | 7df1e5d73bfe6cbbb2fa76d6380d7d456a938c11 |

Continuity retained: today's Owner SG1-SG4 give the sharp 2/7 high-gcd matching sector, not a low-gcd full bound. Coordinator PG1-PG3 keeps the balanced-sign conjugation and actual squarefree clique obstruction. Analytic GL controls large-gcd absolute support with growing parameters; Lean's #1102 is a scoped formal refinement, not signed small-gcd cancellation. Yesterday's DR1-DR7, JOH MS1-MS4, Analytic FP/RM/AQ, Wheel CP/PB/GF and Referee's two-daughter equivalence/clock variance remain at their stated carriers. Census GM's X=145 replacement, HC's reused donor 87283 and FW's N=690,H=186 weighted-Nyman sign failure are preserved, not imported as prime-source counterexamples. The universal BLOCK R=549 refutation remains intact.

The external inbox `research/agent_reports/EXTERNAL_HANDOFFS.md`, blob **038018145c0fddb2f6306c0712373adf9cd1ea52**, was read. Its latest entries remain October 18. EXT-20261018-PNT-1..3, EXT-20261017-XCOORD-1 (including q=R endpoint separation), and EXT-20261014-5 (unconditional versus first-bad qualification) supply no missing uniform short-interval statement. No newer external input is invented. These are published asynchronous handoffs; no other agent was launched or contacted through an unauthorized write.

### J. First Independently Missing Lemma

RS4's paper derivation is complete from the displayed established inputs, but independent review and formalization are pending. For the still-open proper-class pointwise target, preserve the original claim unchanged:

**OPEN-VF-DR-SI, CONJECTURE / SUFFICIENT, NOT NECESSARY.** There exist kappa>0 and N1 such that for every integer N>=N1 and every real interval `(x,x+H] subset [N^2,4N^2]` with

```text
N(log N)^4 log log N <= H <= 2(4N^2)^(21/40),
pi(x+H)-pi(x) >= kappa H/log N.
```

This is an independently stated actual-prime lower bound, not assumed and not newly proved. The existing DR argument shows it would exclude positive deficits on that range and leave O(N log N) on shorter intervals. RS2-RS3 bound exceptions but do not remove them. A weaker factor-sensitive exclusion limited to genuinely demand-rich intervals may suffice; proving merely that exceptions are few is not that exclusion.

The distinct global question is an independently justified restriction on the exact complement and its interaction with Q. Writing a bound for `C_F+Q` would merely restate the unresolved target unless accompanied by new arithmetic. No such lemma is claimed proved here, and OPEN-VF-DR-SI alone would still not close the full source.

### K. Next-Run Resume Capsule And Publication State

```text
RUN: 20261107-owner-2; SCHEDULED 08:09:01 EST; RUN_ID_UNAVAILABLE.
MAIN: 1c057c1d65b6d4cb4d59d207f69a815c52353314.
POLICIES: PAID_BASELINE_EXACT_CONSUMER_V1;
          NO_PIGEONHOLING_ROUTE_SELECTOR_V1.
ROUTE: VF-LOW; exact DR dense rectangle and same capped prime allocation.
NEW: RS1 one-sided reserve thickness; RS3 actual square-sample return;
     RS4 selected root energy <=C N^3/log^6 N;
     RS5 sum Q(R^2)^2/R^3 finite for the once-only dyadic construction.
REUSED: DR1/DR3/DR4, MS2 full-height zero method, compiled b_* and 12/5 density.
BEST EXCEPTION POWER: 1-2s_*=4/5-(8/5)delta_*, plus arbitrary positive loss.
FIRST SIGN LOSS: positive q-count upper bound, then integrated zero-pair absolute row bound.
COMPLETE RETURN: -D=C_F+Q, all squares/mixed terms and canonical sqrt(2) phase.
NO CLAIM: pointwise O(N log N), full VF, original915 payment, new Mertens exponent or RH.
FALSIFIER: two-sided demand-only continuity fails at actual used prime 135482381.
FINITE: 97655 generic sequences; 3326415 cut checks;
        exact fixtures N=9216 and held-out10000; synthetic thick-root test separately labeled.
REVIEW: SELF_AUDIT; INDEPENDENT_REVIEW_PENDING; NOT_FORMALIZED.
FIRST MISSING SUPPLIER: OPEN-VF-DR-SI or an independent factor-sensitive exceptional exclusion.
NEXT PROTECTED OWNER ROUTE: JOH; resume MS1-MS4 without claiming their worse endpoint beats b_*.
NEXT VF ACTION: independent RS1-RS5 audit; then study the residual exceptional configuration,
                not another reserve identity or larger nondiscriminating census.
ETA_GATE: SEARCH_BROAD; NEW_VERIFIED_ENDPOINT_GAIN=NONE.
```

The early checkpoint commit **63ddbbb050d3bea88bf869109bb3fa70bfad0f84**, blob **0d6fc493fc0635254e50b6872e69960a290fa9cf**, was verified by immutable exact-content readback and a report-only commit audit. The current append completes its research stages while preserving every prior byte, including today's SAT result and older receipts. The final synthesis is PENDING_READBACK until the publication receipt below records an actual verified write.

Actual limitations: direct shell GitHub transport returned CONNECT 403; connected GitHub read/write tools worked. No local Lean, new CI run, proof source/branch/PR, issue, shared report, main, schedule or permission was changed. PDF OCR was checked against the relevant displayed mathematical statements; no unsupported probabilistic model, recent preprint claim or fitted exponent was used. Scoped source/report searches did not locate this same reserve-energy application; that is not an exhaustive literature novelty claim. No future background execution is promised.

### Reproducibility Appendix - RS6

Executed with Python 3.12.13; syntax checks and the complete revised verifier exited 0. The helper is the explicitly credited prefix of 20261106-owner-2's published exact verifier, not a new interval algorithm. The registration preserves its initial frozen test and subsequent disclosed addendum. SHA-256:

```text
reserve_interval_helper.py
05d46897638d6a29e05a254ef24f84fee92bc23172b9be96f80db15ca76aa9d6
reserve_sampling_verify.py
36d7b42e76d4c2768f84e23353c9fa801fc91df7014996b5f10f3cdddc3712f0
reserve-test-registration.md, including pre-rerun addendum
4bad407219684f3976f6dfcb522dcce3183e36e36a9a209400dd27f5415371ee
```

The following complete sources are archived inside this authorized report only. They test the finite structural claims and arithmetic reconstruction, not the density theorem, asymptotic constants, infinite zero sum or independently accepted proof status.

#### Frozen Test Registration And Disclosed Addendum

```text
# Frozen VF-LOW Test Registration

Run: 20261107-owner-2; scheduled 08:09 EST.

- Actual carrier: the unchanged q*p*s rectangle; original w_r logarithmic weights; each actual donor prime capped at 1/ceil(log N)^2.
- Development N=9216; held-out N=10000. These deliberately include at least three small primes and multiple factor-pair families. No range extension or exponent fit.
- Use the prior DR rational logarithm enclosure helper, credited to 20261106-owner-2, and exact integer sieving.
- New finite claims: one-sided reserve persistence b(s)>=b(t)-D(t,s); disjoint physical-neighborhood sampling inequality at square roots; exact high-reserve measure; all original source and quadratic reconstruction.
- Counterclaim to falsify: absolute reserve movement is bounded by positive demand alone. A genuinely used prime with no demand changes the reserve, so this should fail.
- Generic finite test: all sequences of lengths 1..7 over {-2,-1,0,1,2}; every ordered cut pair; boundary cases and backwards recurrence. Synthetic cases are tests of the finite lemma, not arithmetic predictions.
- Exact exponent test: use rational arithmetic for b=7/8 and 503/576, verify a=(1+2(1-b))/(2+8(1-b)/3), delta=2a-1=(1-b)(2-8a/3), and exceptional squared-root cost 31/10-2delta<3.
- Rejection: any recurrence, allocation, source, sampling, or exponent mismatch requires correction and an explicitly reported rerun. No finite survival proves a uniform analytic bound.

## Addendum Before Revised Test Execution

The first execution passed, but the sufficient thick-root condition was empty at every tested level in the genuine arithmetic fixtures. Preserve that fact; it is not a nonvacuous sampling certificate. Add the synthetic feasible sequence on (16,64] with capacity 20 at site 20 and demand 20 at site 60, neighborhood length 4, root samples 4,5,6,7, and threshold 10. It predicts exactly three thick roots and high-reserve measure 40. This is explicitly a generic lemma fixture, not a prime-source example.

After rereading yesterday's 20261106-owner-3/MS2 full-height estimate, reuse its already derived 12/5 density argument instead of presenting the weaker truncated 8/3 route as new. Keep the original rational checks as a valid weaker comparison. Add delta=(4/5)(1-b), bad-root power 1-2delta, exceptional-energy power 31/10-2delta, for b=7/8 and 503/576. Expected rounded powers: delta=1/10, bad-root=4/5, energy=29/10. The strict-slot gap must remain symbolic in the theorem, not be replaced by either diagnostic value.
```

#### Credited Exact Interval Helper

```python
"""Finite source and allocation checks; no asymptotic inference."""

from bisect import bisect_left, bisect_right
from collections import Counter
from functools import lru_cache
from itertools import product
from math import isqrt
import hashlib
import json

SCALE = 10**40
WD = 10**18
TERMS = 50


def ceildiv(n, d):
    return -(-n // d)


def mul(a, b):
    return a[0] * b[0] // SCALE, ceildiv(a[1] * b[1], SCALE)


def small_log(n, d):
    assert d <= n <= 2*d
    u = ((n-d)*SCALE//(n+d), ceildiv((n-d)*SCALE, n+d))
    u2 = mul(u, u)
    power = u
    low = high = 0
    for j in range(TERMS):
        low += 2*power[0]//(2*j+1)
        high += ceildiv(2*power[1], 2*j+1)
        power = mul(power, u2)
    high += ceildiv(2*power[1]*SCALE, (2*TERMS+1)*(SCALE-u2[1]))
    return low, high


LOG2 = small_log(2, 1)


def log_interval(n, d=1):
    assert n >= d > 0
    k = n.bit_length()-d.bit_length()
    den = d << k
    if den > n:
        k -= 1
        den //= 2
    lo, hi = small_log(n, den)
    return lo+k*LOG2[0], hi+k*LOG2[1]


@lru_cache(None)
def weight(r):
    lo, hi = log_interval(2*r*r+2*r+1, 2)
    num = (2*r+1)*SCALE*WD
    return num//(r*hi), ceildiv(num, r*lo)


def sieve(n):
    flags = bytearray(b'\x01')*(n+1)
    flags[:2] = b'\x00\x00'
    for p in range(2, isqrt(n)+1):
        if flags[p]:
            flags[p*p:n+1:p] = b'\x00'*((n-p*p)//p+1)
    return flags
```

#### New Reserve And Square-Sampling Verifier

```python
"""Exact reserve persistence and square-sampling checks, not an exponent fit."""

from bisect import bisect_right
from collections import Counter
from fractions import Fraction
from itertools import product
from math import isqrt
import hashlib
import json

from reserve_interval_helper import SCALE, WD, log_interval, sieve, weight


def generic():
    sequences = pairs = 0
    for length in range(1, 8):
        for values in product((-2, -1, 0, 1, 2), repeat=length):
            b = [0] * (length + 1)
            d = [0]
            for value in values:
                d.append(d[-1] + max(0, value))
            for i in range(length - 1, -1, -1):
                b[i] = max(0, b[i + 1] + values[i])
            for i in range(length + 1):
                for j in range(i, length + 1):
                    assert b[j] >= b[i] - (d[j] - d[i])
                    pairs += 1
            sequences += 1
    return {"sequences": sequences, "ordered_cut_checks": pairs}


def powers():
    out = []
    for b in (Fraction(7, 8), Fraction(503, 576)):
        w = 1 - b
        a = (1 + 2*w) / (2 + Fraction(8, 3)*w)
        delta = 2*a - 1
        assert delta == w*(2 - Fraction(8, 3)*a)
        assert delta == 2*w/(3 + 4*w)
        assert Fraction(31, 10) - 2*delta < 3
        out.append({"method": "weaker_truncation", "b": str(b), "a": str(a), "delta": str(delta),
                    "bad_root_power": str(1 - 2*delta),
                    "exceptional_energy_power": str(Fraction(31, 10) - 2*delta)})
        full_delta = Fraction(4, 5)*w
        assert full_delta > delta
        assert Fraction(31, 10) - 2*full_delta < 3
        out.append({"method": "inherited_full_height", "b": str(b),
                    "delta": str(full_delta), "bad_root_power": str(1 - 2*full_delta),
                    "exceptional_energy_power": str(Fraction(31, 10) - 2*full_delta)})
    return out


def synthetic_sampling():
    # A generic non-prime fixture; the real arithmetic tests are separate.
    d, c, b = [0]*65, [0]*65, [0]*65
    c[20], d[60] = 20, 20
    for n in range(64, 16, -1):
        b[n - 1] = max(0, b[n] + d[n] - c[n])
    assert b[16] == b[64] == 0
    thick = [r for r in range(4, 8) if b[r*r] > 10 + sum(d[r*r + 1:r*r + 5])]
    measure = sum(b[t] > 10 for t in range(16, 64))
    assert thick == [5, 6, 7] and measure == 40
    assert 4*len(thick) <= measure
    for r in thick:
        assert all(b[t] > 10 for t in range(r*r, r*r + 4))
    return {"synthetic_only": True, "thick_roots": thick,
            "neighborhood_measure": 4*len(thick), "high_reserve_measure": measure}


def trial_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def arithmetic(N, flags):
    small = [p for p in range(2, 2*N) if flags[p]]
    ss = [p for p in small if N < p*p and 100*p*p <= 121*N]
    qs = [q for q in small if 3*N < 2*q and 4*q <= 7*N]
    fs = sorted(q*p*s for q in qs for i, p in enumerate(ss) for s in ss[i + 1:])
    assert len(ss) >= 3 and len(fs) == len(set(fs))
    assert all(2*n > 3*N*N and 400*n <= 847*N*N for n in fs)
    assert all(n % 2 and isqrt(n)**2 != n and not flags[n] for n in fs)
    lo, hi = log_interval(N)
    assert lo//SCALE == hi//SCALE
    k = lo//SCALE + 1
    den = WD*k*k
    counts = Counter(isqrt(n) for n in fs)
    prime_counts = {r: flags.count(1, r*r + 1, (r + 1)**2) for r in range(N, 2*N)}
    result = []
    for side in (0, 1):
        demand = {n: weight(isqrt(n))[side]*k*k for n in fs}
        used = {}
        capacities = {}
        b = 0
        fi = len(fs) - 1
        n = fs[-1]
        while fi >= 0 or b:
            if b == 0 and fi >= 0:
                n = fs[fi]
            if fi >= 0 and n == fs[fi]:
                b += demand[n]
                fi -= 1
                n -= 1
                continue
            p = flags.rfind(1, N*N + 1, n + 1)
            next_d = fs[fi] if fi >= 0 else N*N
            if p < next_d:
                n = next_d
                continue
            assert p > N*N
            cap = WD - weight(isqrt(p))[side]
            take = min(b, cap)
            assert take > 0
            used[p], capacities[p] = take, cap
            b -= take
            n = p - 1

        events = sorted(fs + list(used))
        reserves = []
        prefix_d = [0]
        inv = 0
        queue = []
        qi = 0
        pair_count = 0
        for n in events:
            if n in used:
                assert flags[n] and used[n] <= capacities[n]
                inv += used[n]
                queue.append([n, used[n]])
            else:
                remain = demand[n]
                inv -= remain
                while remain:
                    p, amount = queue[qi]
                    take = min(remain, amount)
                    assert p < n and p > max(qs) and n % p != 0
                    remain -= take
                    queue[qi][1] -= take
                    if queue[qi][1] == 0:
                        qi += 1
                    pair_count += 1
            assert inv >= 0
            reserves.append(inv)
            prefix_d.append(prefix_d[-1] + demand.get(n, 0))
        assert inv == 0
        assert sum(used.values()) == sum(demand.values())

        # Omitted primes occur only while the current future reserve is zero.
        backward = 0
        for i in range(len(events) - 1, -1, -1):
            assert backward == reserves[i]
            n = events[i]
            backward = max(0, backward + demand.get(n, 0) - capacities.get(n, 0))
        assert backward == 0

        def reserve(t):
            i = bisect_right(events, t) - 1
            return reserves[i] if i >= 0 else 0

        def demanded(t, s):
            return prefix_d[bisect_right(events, s)] - prefix_d[bisect_right(events, t)]

        # Check the new one-sided statement at each genuine square and every
        # event in its physical neighborhood, including the right endpoint.
        checks = 0
        sampled = []
        for r in range(N, 2*N):
            t = r*r
            sampled.append(reserve(t))
            i, j = bisect_right(events, t), bisect_right(events, t + N)
            for s in [t + N] + events[i:j]:
                assert reserve(s) >= reserve(t) - demanded(t, s)
                checks += 1

        sampling = []
        for level in (Fraction(0), Fraction(1, 100), Fraction(1, 20), Fraction(1, 10)):
            B = level*den
            thick = sum(reserve(r*r) > B + demanded(r*r, r*r + N)
                        for r in range(N, 2*N))
            measure = sum((events[i + 1] - n) for i, n in enumerate(events[:-1])
                          if reserves[i] > B)
            assert N*thick <= measure
            sampling.append({"level": str(level), "thick_roots": thick,
                             "high_reserve_measure": measure})

        pi_base = flags.count(1, 0, N*N + 1)
        anchor = sum(r*weight(r)[side]*k*k for r in range(2, N)) - pi_base*den
        whole = complement = anchor
        qmass = 0
        uroot = Counter()
        for p, take in used.items():
            uroot[isqrt(p)] += take
        full_checks = 0
        for r in range(N, 2*N):
            assert qmass == -sampled[r - N]
            assert whole == complement + qmass
            assert whole**2 == complement**2 + qmass**2 + 2*complement*qmass
            # D_can^2 in the basis (1,sqrt(2)), including the original anchor.
            assert (whole**2 + 2*den**2, 2*whole*den) == (
                complement**2 + qmass**2 + 2*complement*qmass + 2*den**2,
                2*(complement + qmass)*den)
            total = r*weight(r)[side]*k*k - prime_counts[r]*den
            selected = counts[r]*weight(r)[side]*k*k - uroot[r]
            whole += total
            complement += total - selected
            qmass += selected
            full_checks += 1
        assert qmass == 0 and whole == complement

        p = min(used)
        # A real negative prime source changes reserve with no positive demand.
        assert demanded(p - 1, p) == 0
        assert reserve(p) - reserve(p - 1) == used[p] > 0
        for p0 in sorted(used)[:8]:
            assert trial_prime(p0)
        result.append({"side": side, "used_prime_count": len(used),
                       "allocated_edges": pair_count, "persistence_checks": checks,
                       "full_square_checks": full_checks, "sampling": sampling,
                       "root_energy_numerator": sum(v*v for v in sampled),
                       "root_energy_denominator": den*den,
                       "nonzero_root_samples": sum(v > 0 for v in sampled),
                       "maximum_root_numerator": max(sampled),
                       "maximum_physical_numerator": max(reserves),
                       "weight_denominator": den,
                       "two_sided_demand_only_counterexample_prime": p,
                       "positive_jump_numerator": used[p],
                       "donor_sha256": hashlib.sha256(str(sorted(used.items())).encode()).hexdigest()})
    assert result[0]["root_energy_numerator"] <= result[1]["root_energy_numerator"]
    return {"N": N, "small_primes": ss, "q_count": len(qs), "site_count": len(fs),
            "site_sha256": hashlib.sha256(str(fs).encode()).hexdigest(), "envelopes": result}


if __name__ == "__main__":
    print(json.dumps({"generic": generic(), "powers": powers(),
                      "synthetic_sampling": synthetic_sampling()}), flush=True)
    flags = sieve(4*10000**2)
    for N in (9216, 10000):
        print(json.dumps(arithmetic(N, flags)), flush=True)
```

### Verified Publication Receipt - 20261107-owner-2

At **2026-11-07T13:39:30Z (08:39:30 America/New_York)**, research commit **7bb2a16015161ca2bc80bd0c6673d595c29f37c9** and report blob **aafcd01bdc5064f0429847c14b23af2093d87742** were re-fetched at the immutable commit. All **109,508 characters** matched the submitted text exactly, including the executable appendix. Commit metadata listed only `research/agent_reports/2026-11-07/10-owner-payment.md`; all prior report bytes and the early checkpoint were preserved. The source main remained **1c057c1d65b6d4cb4d59d207f69a815c52353314** on closing refresh.

This records completed publication verification, not independent mathematical acceptance. Final research status: **PAPER_PROOF / FINITE_COMPUTATION; INDEPENDENT_COMPONENT_ADVANCE; SELF_AUDIT; INDEPENDENT_REVIEW_PENDING; NOT_FORMALIZED; NEW_VERIFIED_ENDPOINT_GAIN=NONE**. RS4-RS5 concern only the exact selected component. The proper pointwise and full canonical objectives remain open, with their original complement and mixed terms retained. Next protected Owner route: JOH. No Lean source, proof branch, PR, central instructions, other role report, schedule, permission or main was modified.


## Scheduled JOH Continuation Checkpoint - 20261107-owner-3

### A. Mathematical question and status

IN_PROGRESS / PARTIAL. Resume 20261106-owner-3/MS1-MS4 on the original Li_2 arrival clock. The established local variance improves a component but its complete returned exponent is worse than the certified native boundary. This invocation investigates a joint signed clock/level return, with both endpoint halos and original integrated Johnston weight retained, before asking for a stronger isolated variance. No new theorem or endpoint gain is asserted at this checkpoint.

### B. Live authority and continuity

Actual trigger: scheduled 2026-11-07T16:15:01-05:00, America/New_York; RUN_ID_UNAVAILABLE. Main fetched as cae99df1c3ea24ff4113063bf09f6fd07517ad93, tree 087a31436295ea4b0307d3d851f363c5370dba5f. AGENTS blob 0a99faf8458809ac772d470d704c5433f373bda8; CURRENT_PROOF_CONTRACT blob d1d6fd558ee23927bd9f70ffdc375bafd1dbb67a. high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1; chain_ack=CANCELLATION_CHAIN_REUSE_V1; baseline_ack=PAID_BASELINE_EXACT_CONSUMER_V1; deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1.

Due protected route: JOH, following today's SAT then VF-LOW. Current Coordinator's 15:13 synthesis recommends precisely this continuation. Both Eastern dates' seven-role reports have been retrieved; relevant sections are being checked. TODAY=AVAILABLE; YESTERDAY=CARRY_FORWARD at original scope. External inbox remains blob 038018145c0fddb2f6306c0712373adf9cd1ea52 with no new November entry. No open/draft PRs were returned. #1102, #1103, #1104 and #1105 are now merged; their new moment/count interfaces do not identify ideal characters with actual prime occurrences.

### C. Exact source and first consumer

L(t)=Li_2(t), Q(n)=floor L(n), B(n)=pi(n)-Q(n)-1, G(N)=sum_(2<=n<N)B(n). The source prime/model mismatch is native primitiveMismatch(n-1); B is native integer backlog minus one. Arrivals b_j=min{n>=2:Q(n)>=j} and increments pi(b_(j+h))-pi(b_j)-h are genuine prime counts with the complete upper halo. Preserve the classical li(2) correction in Johnston's external criterion, odd-square owner boundaries, and the initial level.

The common endpoint remains complete canonical HIGH, with fixed-cutoff LOW already O(R). JOH's eventual G(R^2)<0 is an independently sufficient RH route through its established external analytic criterion; it is not a new quantitative bridge or an assumed sign. Reuse the strongest applicable actual native strict boundary, retaining its source hypotheses and every-positive-loss quantifiers. Source refresh includes the original floor-Li balance/backlog/transport modules and native strict-Mertens/fixed-count declarations. The new work must locate a smaller independently provable joint restriction, or explicitly report why the tested consumer does not improve the endpoint.

### D-K. Pending work

Derivation, falsification, full signed and quadratic return, endpoint comparison, source/evidence ledger, specialist handoffs, and immutable final readback are pending. Earlier SAT/VF-LOW findings, code, receipts and correction history above remain unchanged. No Lean/source/policy/PR/schedule edits or other-agent launches are authorized or attempted. eta_gate=SEARCH_BROAD; NEW_VERIFIED_ENDPOINT_GAIN=NONE.

## Complete JOH Return And Low-Zero Failure Localization - 20261107-owner-3

### A. Most Important Mathematical Development

**PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED.** The complete original Johnston floor-Li source has a useful inverse restriction, obtained without reconstructing its level from short-clock variance. Under the repository's already supplied nontrivial-zero boundary beta <= b < 1, the exact logarithmic transfer and an established zero-density theorem pay the ENTIRE sufficiently high zero tail below the prime-square bias scale. Any large-scale failure of G(N)<0 must therefore be carried by a quantitatively negative, bounded-height group of actual off-critical zeros.

Write a=30/13, d_a(b)=2-a(1-b), and nu_a(b)=(b-1/2)/d_a(b). For fixed 1/2<=b<=7/8 and

```text
nu_a(b) < nu < 1/a,
A_N = N^(3/2)/log N,
D_N = {actual zeros rho=beta+i*gamma, counted with multiplicity:
       0<|gamma|<=N^nu and beta>1/2+1/log N},
```

the new inverse conclusion is, for EVERY sufficiently large integer N,

```text
G(N)>=0  ==>  sum_(rho in D_N) K_rho(N) <= -A_N/2.       (JT3)
```

The sum is real because conjugate zeros are included. In particular D_N must be nonempty. K is the exact kernel in D below, not its leading logarithmic approximation. This is a proved implication under the displayed incoming boundary, NOT a proof that the forced configuration is impossible.

At rounded b=7/8, the admissible height threshold is nu>39/178, compared with nu>3/8 from the same kernel plus total-zero counting alone. The reused classical density coefficient 12/5 would already give nu>15/68. The strict actual baseline is retained by using nu_a(b), not by replacing b with 7/8 in the theorem. These are zero-HEIGHT thresholds, not Mertens exponents. No optimal density threshold is claimed.

A particularly simple, completely returned fixed-power consequence uses nu=9/40:

```text
G(N) = -sum_(0<|gamma|<=N^(9/40)) K_rho(N) - P_2(N)
       + O(N^(3/2-21/4160)),                            (JT2-return)
P_2(N) = (1/2) sum_(p prime, p^2<N) (N-p^2)
       ~ (2/3) A_N.
```

This pays the discarded-height part, every higher prime power and the exact floor/constant/lower-end restoration. The remaining finite zero sum is NOT bounded at a new global power. The full endpoint and JOH eventual sign remain OPEN. **NEW_VERIFIED_ENDPOINT_GAIN=NONE; eta_gate=SEARCH_BROAD.**

Claim ledger: JT1 exact source/logarithmic-kernel return and its uniform estimate, PAPER_PROOF with IDENTITY_ONLY subclaims; JT2 complete tail bound and returned remainder, PAPER_PROOF / INDEPENDENT_COMPONENT_ADVANCE; JT3 failure localization, PAPER_PROOF / INVERSE_RESTRICTION; JT4 logarithmic-freezing obstruction, PAPER_PROOF on a specified analytic-mode domain, not an actual off-line-zero counterexample; JT5 exact original-prime tests and scoped shortcut refutations, FINITE_COMPUTATION. No new result is PROVED_IN_LEAN. Classical analytic ingredients are credited; no literature-priority claim is made.

### B. Current Authoritative Objective

Actual invocation: SCHEDULED 2026-11-07T16:15:01-05:00, America/New_York; RUN_ID_UNAVAILABLE. This completes the earlier checkpoint, not another execution. Protected sequence today is SAT, VF-LOW, JOH; next SAT.

Main at intake: **cae99df1c3ea24ff4113063bf09f6fd07517ad93**, tree **087a31436295ea4b0307d3d851f363c5370dba5f**. Current HIGH policy blob **be8168b67584d9d8ebbaa732a30c51509137543e**. high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1; chain_ack=CANCELLATION_CHAIN_REUSE_V1; baseline_ack=PAID_BASELINE_EXACT_CONSUMER_V1; deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1.

For fixed Lambda>=0, the complete common object is

```text
M(R^2-1)=canonicalLowPrefix_Lambda(R-1)
          +canonicalHighPrefix_Lambda(R-1),
|canonicalLowPrefix_Lambda(R-1)| <= (floor Lambda+1) R.
```

The desired new HIGH amplitude must beat the strongest applicable existing boundary, with the final partial-square O(R) cost and positive-loss spending retained. This run instead uses the independently sufficient JOH route: eventual G(R^2)<0, with the correct classical-li convention, implies RH by the established external Johnston criterion and the repository's recorded discrete transfer. That sign is NOT assumed. An isolated prime-power or clock estimate is not a quantitative map to canonical HIGH.

The strongest directly available native arithmetic boundary inspected is **b_base=HeckeZeroSupremum.beta**, with `native_mertens_growth_at_hecke_beta` and `native_zeta_zero_re_le_hecke_beta`, and b_base<7/8. The actual-source theorem `native_beta_le_true_physical_slot_minimum` additionally supplies a fixed D and m=actualSlotMinimum D>0 with b_base<=7/8-m/24. The explicit-count bound 7/8-1/(288 explicitSlotCount) is also retained, not confused with an optimized or equal boundary. JT1-JT3 are parameter theorems and can take b=b_base. No numerical value or uniformity as b varies is inferred from an existential witness.

For every positive epsilon, the existing Mertens and complete signed-pair consequences already apply at b_base. They do not imply a new sharp shell variance or the desired JOH sign. Our final complete source still has only the inherited b_base-scale global control; the new height localization is not an exponent improvement.

Material source blobs, all retrieved at the pinned main:

| File | Blob SHA |
| --- | --- |
| AGENTS.md | 0a99faf8458809ac772d470d704c5433f373bda8 |
| CURRENT_PROOF_CONTRACT.md | d1d6fd558ee23927bd9f70ffdc375bafd1dbb67a |
| docs/RHLEAN_COMPLETE_SIGNED_HIGH_ATTACK_20261107.md | be8168b67584d9d8ebbaa732a30c51509137543e |
| docs/RHLEAN_REUSE_CANCELLATION_CHAIN_20261107.md | 28e2ab47c68bc83b91ae02b6112b94867b021b32 |
| research/VF_MID_FLOOR_LI_SIGNED_POPULATION_BALANCE.lean | 9a9336dad72171b6d572a1c1ae88d1ae8b56b530 |
| research/VF_MID_FLOOR_LI_DISCRETE_BACKLOG.lean | 4255ca0dffe480f2aec6bd0b68797bbd293396c3 |
| research/VF_MID_FLOOR_LI_TRANSPORT_CANCELLATION.lean | eb84f59055bd31dc117be034d45c92eb9dab8f27 |
| research/LI_FAN_ONE_SIDED_WEIGHTED_COMPOSITE_RH_CONTRACT_20261022.md | 27e28f09e9f79e8a60d524e5fcb6f19904fa55f5 |
| research/oai_434/VF919NativeSevenEighthsReplay.lean | 111c933a7ca15647105ce6a4d0f3cbfc3cde81f4 |
| research/oai_434/VF919NativeStrictMertens.lean | b33a4883e1ddb0551b0f11f062bce46680d87450 |
| research/oai_434/VF919ActualSlotMinRetighten.lean | 138c4726085995b966204406805f70082402bec4 |
| research/oai_434/VF919ExplicitFixedSourceSlotCount.lean | bad5aab0a60e96d19e7c9550cd7c0a072288bc0f |
| RHLean/Analysis/CanonicalHighSectorCore.lean | dd02fc8fabfe4004c6b0d50374b3b8752607b168 |
| RHLean/Analysis/CanonicalLowOccupancy.lean | b958da340d107cdd00015d2827b9a728357b4d8e |

Live discovery returned no open/draft PRs. #1102, #1103, #1104 and #1105 are now human-merged; stale unmerged labels in earlier reports are historical. #1105's two-error moment interface and #1103's licensing package do not themselves prove a complete new endpoint and are not imported into prime occurrences. Today's Coordinator/Lean evidence for their dedicated checks is attributed, not represented as a new build here.

The existing strict-baseline proof was checked directly against #1091 head **6778fd4c25b0f369d311e6e71223e168e329b4bf**: all twelve retrieved workflows succeeded. Dedicated run **41898325686**, job **126813711885**, was fetched; its log verifies exact actual-source-minimum terminal types and standard axioms `[propext, Classical.choice, Quot.sound]`, and the explicit-count terminal. The three strict/actual-minimum/explicit-count files were re-fetched at that head and matched current main byte-for-byte and by blob. This is reused exact-head evidence, not a fresh main-wide compilation. No local Lean was run.

### C. Structural Hypothesis Investigated

The full original carrier is

```text
L(t)=Li_2(t), Q(n)=floor L(n), B(n)=pi(n)-Q(n)-1,
G(N)=sum_(2<=n<N) B(n)
    =sum_(3<=k<N)(N-k) [1_Prime(k)-Q(k)+Q(k-1)].
```

B is native integer backlog minus one; the bracketed atom is native primitiveMismatch(k-1), not mu(k). The same G is the complete one-sided weighted composite removal A(N)-T(N)-L_model(N), with every odd-square boundary at N=R^2 restored. The exact Li clock b_j and MS1-MS4 remain valid at their original scope.

Three possibilities were distinguished. Continuing to apply Cauchy to short-clock increments retains MS4's weaker returned endpoint and is not a new mechanism. Freezing the final logarithmic transfer at 1/log N can lose a large mode-dependent term. The selected hypothesis is that the exact POSITIVE logarithmic transfer of the integrated Chebyshev discrepancy retains enough inverse-height decay to pay all high zeros jointly with the original prime-power corrections. This succeeds at the tail and inverse-theorem levels; it does not establish favorable cancellation of the remaining low zeros.

This is a new continuation of the authorized JOH route and current Coordinator's complete-return request, not a departure from the campaign or a request to centralize all investigators on zero-density methods. The local derivative/clock covariance is not declared equal to a global level covariance.

### D. Mathematical Derivation

#### JT1. Exact Logarithmic Return, With All Arithmetic Restored

Use the following established analytic inputs at their original scopes. Johnston's [Lemma 2.6 and its displayed integrated explicit formula](https://arxiv.org/pdf/2201.06184#page=4) provide the unconditional formula used below; RH is used in his subsequent bound, NOT in that identity. His Theorem 1.1 is the external sign consumer. The uniform density input is [Guth-Maynard, Theorem 1.2 and (1.4)](https://arxiv.org/pdf/2405.20552#page=2): N(sigma,T)<<_epsilon T^((30/13)(1-sigma)+epsilon). The earlier 12/5 alternative is the recorded [Zaccagnini Section 2.1 density input](https://people.dmi.unipr.it/alessandro.zaccagnini/psfiles/papers/Q429.pdf#page=3). [Brent-Platt-Trudgian, Corollary 1](https://maths-people.anu.edu.au/brent/pd/rpb276-MC-preprint.pdf#page=3) implies the unconditional all-ordinate bound sum_rho gamma^(-2)<1/20, multiplicities included. Ordinary PNT is used only for the prime-square asymptotic. These are imported established facts, not this run's discoveries or new Lean declarations.

The density statement's positive loss is retained. If its o(1) formulation is read only for fixed sigma, monotonicity in sigma and a finite fixed mesh give the required uniform positive-loss version on [1/2,b]. Fix the mesh after the desired loss, then take the maximum of finitely many constants. No growing-parameter uniformity is silently assumed.

For real X>=2 let

```text
Pi(t)=sum_(p^k<=t) 1/k,
F(t)=integral_2^t (psi(u)-u) du,
c=li(2),
W_X(t)=1/log t + (X-t)/(t log^2 t),
v_X(t)=-W_X'(t)
      =(X+t)/(t^2 log^2 t)+2(X-t)/(t^2 log^3 t) >= 0,
T_X[f]=f(X)/log X + integral_2^X f(t) v_X(t) dt.
```

Stieltjes partial summation for the ACTUAL prime powers gives

```text
Pi(t)-li(t) = (psi(t)-t)/log t
 + integral_2^t (psi(u)-u)/(u log^2 u) du + 2/log 2-c.
```

Integrate over t and use F(2)=0. Fubini and integration by parts yield exactly

```text
integral_2^X (Pi(t)-li(t)) dt = T_X[F]+(2/log 2-c)(X-2).  (1)
```

The integrated explicit formula is

```text
F(t)=-sum_rho t^(rho+1)/(rho(rho+1)) + E(t),
E(t)=2-t log(2*pi)+zeta'(-1)/zeta(-1)
     -sum_(r>=1) t^(1-2r)/(2r(2r-1)).                  (2)
```

The zero sum is absolutely and locally uniformly convergent here. There is no half-weight ambiguity after integration. E(t)=O(t) on t>=2. Apply the SAME linear operator T_X to (2), retaining its lower-end constants, and define

```text
K_rho(X) = 1/(rho(rho+1)) *
 [X^(rho+1)/log X + integral_2^X t^(rho+1) v_X(t) dt].   (3)
```

For an integer N>=3, put

```text
P_k(N)=(1/k) sum_(p prime, p^k<N)(N-p^k),
P_ge3(N)=sum_(k>=3)P_k(N),
E_floor(N)=sum_(n=2)^(N-1) integral_n^(n+1)
                       [li(t)-Q(n)-1] dt,
U(N)=T_N[E]+(2/log 2-c)(N-2)+E_floor(N).
```

Then the COMPLETE original source is exactly

```text
G(N)=-sum_rho K_rho(N)-P_2(N)-P_ge3(N)+U(N).            (4)
```

Every p^k is an actual occurrence, with its original 1/k multiplicity; the prime 2 and all its powers are included. Replacing <N by <=N changes nothing because a boundary atom has weight zero. No actual prime is replaced by floor-Li membership. The subtraction Pi-pi is exact before any estimate. In the odd-owner presentation, T(R^2) still contains sum_(odd 3<=s<R)(R^2-s^2); (4) is not permission to delete that term.

Since 0<=L(n)-Q(n)<1 and 0<=L(t)-L(n)<=1/log 2 on a unit cell,

```text
0 <= E_floor(N) <= (c+1/log 2)(N-2).
```

The strict positivity c>1 explains the chosen -1 centering, without changing the classical li convention. Because |E(t)|<=Ct and T_N is positive, T_N[E]=O(N); explicitly T_N[t]=O(N). Thus U(N)=O(N). Also

```text
0<=P_ge3(N)<<N^(4/3) log N,
P_2(N)=(1/2) integral_2^N pi(sqrt t) dt
      =(2/3+o(1)) N^(3/2)/log N.                       (5)
```

The second conclusion is ordinary PNT plus integration, not a square-root error theorem. No rate for that o(1) is used as a power-saving remainder: P_2 is retained EXACTLY in JT2-return.

For a fixed zero boundary b<1, the functional equation also gives beta>=1-b. Uniformly for sigma in [1-b,b],

```text
T_N[t^(sigma+1)]
 = N^(sigma+1)/log N * (1+O_b(1/log N)),
|K_rho(N)| <= C_b N^(beta+1)/(gamma^2 log N).            (6)
```

To see the first estimate, integrate the three positive terms in v_N: the leading two integrals are N integral t^(sigma-1)/log^2 t and integral t^sigma/log^2 t; both have order N^(sigma+1)/log^2 N uniformly away from sigma=0. The third has one additional logarithm. Splitting at sqrt N supplies an elementary uniform bound near the fixed lower endpoint. The second estimate uses |rho(rho+1)|>=gamma^2. This positive-operator bound retains the whole logarithmic correction, not a truncation of (3).

#### JT2. All-Height Tail And Complete Signed Remainder

The proof works for either a=12/5 with its fixed logarithmic density loss, or a=30/13 with every positive exponent loss. Fix b and epsilon before N,T. For 2<=T<=N^(1/a),

```text
sum_(|gamma|>T) |K_rho(N)|
 <<_(a,b,epsilon) N^epsilon *
       [N^(3/2)/T + N^(b+1)/T^(2-a(1-b))].             (7)
```

Here is the full tail argument. On a band V<|gamma|<=2V, layer-cake gives

```text
sum N^beta << N^(1/2) V log(2V)
 + log N integral_(1/2)^b N^sigma
                            V^(a(1-sigma)+epsilon_0) d sigma.
```

After division by V^2, the exponent of V in the integral is at most a/2-2+epsilon_0<0. Choose epsilon_0 below half this fixed negative margin. Sum all dyadic bands FIRST, using this uniform geometric decay. The resulting integral is bounded by a constant times

```text
integral_(1/2)^b N^sigma T^(a(1-sigma)-2+epsilon_0) d sigma.
```

Only now use T<=N^(1/a), so N^sigma T^(a(1-sigma)) is nondecreasing in sigma. Its maximum occurs at b. Multiply by N/log N from (6), and absorb the fixed logs and T^epsilon_0 into N^epsilon. This proves (7), including arbitrary high heights and their original multiplicities. Maximizing at b at every unbounded V before summation would be invalid; that shortcut is not used. No zero-pair independence is needed because this is an absolutely convergent first-moment return.

For fixed nu_a(b)<nu<1/a and any fixed

```text
0<kappa<min{nu, d_a(b)*nu-(b-1/2), 1/6},
```

choose the internal positive loss small enough. Equations (4), (5), (7) imply

```text
G(N)=-S_(N^nu)(N)-P_2(N)+O_(a,b,nu,kappa)(N^(3/2-kappa)),
S_T(N)=sum_(0<|gamma|<=T) K_rho(N).                     (8)
```

The constants are uniform for every sufficiently large INTEGER N, not only a dyadic sequence. In the concrete a=30/13, b<=7/8, nu=9/40 case the worst tail exponent before loss is

```text
15/8-(89/52)*(9/40)=3099/2080=3/2-21/2080.
```

Spending epsilon=21/4160 yields the fixed remainder in A; higher powers and U are smaller. At b=7/8-delta, the same tail exponent is 3099/2080-(79/52)delta. The exact minimum in (8) must still be taken when delta is not small. No existential strict gain is erased or silently made numerical.

#### JT3. A Signed Inverse Theorem For Actual Failure

Split S_(N^nu)=S_safe+S_danger at beta=1/2+1/log N. For every zero in the safe part and 2<=t<=N,

```text
|t^(rho+1)| <= e*t^(3/2).
```

Positivity of T_N and the unconditional all-zero sum bound give

```text
|S_safe| <= (e/20) T_N[t^(3/2)]
         = (e/20+o(1)) A_N.                            (9)
```

This includes the critical line, all left-half-plane mates, repeated zeros and both ordinate signs; it does not assert that any of these sums vanishes. With (5) and (8), G(N)>=0 forces

```text
-S_danger >= (2/3-e/20+o(1)) A_N > A_N/2
```

for all sufficiently large N, since e<3 and 2/3-3/20=31/60>1/2. This proves JT3 and the bounded-height, quantitatively off-critical witness. At N=R^2 the same statement holds with height R^(2nu) and beta>1/2+1/(2log R), uniformly for all sufficiently large integer R.

The theorem supplies an independent necessary configuration for a failure of the original weighted-composite sign. It does NOT exclude that configuration, prove RH, or infer finite-height RH verification from a numerical zero list. If b=1/2 is supplied, the danger set is empty and the familiar RH-sign implication follows; using that special case without its boundary premise would be circular.

#### JT4. Why The Exact Kernel Must Not Be Frozen

For a FIXED complex s with Re(s)=sigma>0, s not 0 or -1, the kernel (3) has the expansion

```text
K_s(N)=N^(s+1)/(s(s+1)log N)
 + (2s+1)N^(s+1)/(s^2(s+1)^2 log^2 N)
 + O_s(N^(sigma+1)/log^3 N)+O_s(N).
```

It follows by the same endpoint integration of v_N, without changing the source definition. For sigma>1/2 the magnitude of the nonzero second coefficient grows faster than A_N. Thus a uniform analytic-mode argument cannot call the discarded logarithmic correction O(A_N) merely because it contains one extra log. This is a scoped analytic obstruction, NOT evidence that an actual off-critical zeta zero exists and NOT a refutation of collective cancellation of such modes. The full K is used throughout JT1-JT3.

### E. Quantitative Consequence And Complete Return

The new quantitative result is the proper-spectrum bound (7), its fully restored original-source remainder (8), and the inverse statement JT3. The change is from short-clock variance plus level-reconstruction Cauchy to the actual triangularly weighted source before norms. It avoids MS4's loss but does not bound the remaining signed low spectrum.

For complete quadratic accounting put Z=S_(N^nu), P=P_2, and E_rest=-sum_(|gamma|>N^nu)K_rho-P_ge3+U. These are real. Before any inequality,

```text
G=-Z-P+E_rest,
G^2=Z^2+P^2+E_rest^2+2ZP-2Z E_rest-2P E_rest.
```

All within-Z zero pairs, safe/danger mixing, high/low mixing, prime-power mixing, initial constants and floor rounding are retained by this identity. The sign proof uses a one-sided linear comparison of the COMPLETE source, not a claim that any cross term is negative. The alternative exact finite arithmetic test uses G=G_Pi-P_2-P_ge3 and checks all six corresponding terms.

The native canonical HIGH consequence currently remains the paid one at b_base. Taking absolute values of the remaining low sum in (8) yields only inherited b-scale control for G; it does not improve a zero boundary or Mertens exponent. A new estimate on the remaining joint sum would still be needed. No source-specific OAI LOW moment, arbitrary Hecke phase, fixed-window variance or prime-only density has been used in its place. Original #915's normalization, historical compression and first-bad premises are untouched and unpaid by this result.

### F. Falsification And Circularity Review

JT5's purpose and ranges were frozen before execution. The rational Li-floor helper is reused unchanged from 20261106-owner-3/MS5, itself credited there to Census 20261105-census-2. All 256 registered endpoints passed: development 4<=N<=256, held-out N=529,1024,2048. Seventeen square endpoints additionally passed the exact odd-interior plus odd-square boundary reconstruction. All floors through 2048 were certified by outward integer log/Simpson bounds; no floating-point sign decision was used.

Two deliberately incomplete claims are REFUTED on actual arithmetic:

| Shortcut and first development witness | Exact result |
| --- | --- |
| Replace pi by Pi without restoring prime powers, N=7 | G=-1, G_Pi=1/2, P_2=3/2, P_ge3=0; the sign reverses |
| Treat the omitted mixed term in (G_Pi-P)^2 as nonpositive, N=71 | G=-157, G_Pi=-7/60, P=9413/60; omitted -2G_Pi P=65891/1800>0 |

The first exact mixed-term identity mismatch is already N=5, where -2G_Pi P=-1/2. N=71 is specifically the first POSITIVE omitted term, not the first nonzero term. Final verifier logging was tightened to report both witnesses within the unchanged registered range.

Held-out complete returns (all exact rationals):

| N | G | G_Pi | P_2 | P_ge3 |
| --- | --- | --- | --- | --- |
| 529 | -2707 | 2057/2520 | 3205/2 | 2785397/2520 |
| 1024 | -6703 | -5408/45 | 3953 | 118342/45 |
| 2048 | -16599 | -31069/210 | 20415/2 | 655573/105 |

The tests also verify the triangular primitive mismatch, weighted odd-composite identity, every quadratic cross term, strict prime-power boundaries and exact rational tail exponents. They DO NOT verify the analytic zero-density theorem, the infinite kernel series, the all-scale inverse statement, or attainment of its unknown N0. No actual zero computation was performed. The wrong-symbolic-kernel issue in JT4 is established analytically, not disguised as an actual-zero numerical falsifier.

Important self-audit checks: sum dyadic high heights before maximizing in beta; retain functional-equation lower bounds when using uniform kernel constants; retain arbitrary positive density loss; spend it before claiming a fixed remainder; retain P_2 exactly instead of treating its PNT o(1) as a power; preserve c=li(2), F(2)=0 and native backlog's -1; retain every prime power including powers of 2. The safe/danger split uses no stochastic assumption. Author self-audit is not independent Referee acceptance.

Scoped searches of the inspected source tree and both dates' relevant reports found the inherited MS/RS high-tail arguments but not this complete G-kernel/height-failure implication. This is not an exhaustive novelty search. The existing Johnston RH equivalence makes it especially important NOT to label an unproved low-spectrum sign condition as an elementary independent supplier.

### G. Conceptual Interpretation

The exact triangular Johnston weight supplies two inverse-zero factors before logarithmic transport. Keeping that weight exposes an absolutely summable high-height tail and a real negative prime-square term. The earlier moving-clock energy was asking a derivative statistic to recover a global level; the direct return shows precisely which actual low-zero configuration would instead have to carry a failure.

This is a structural localization of the COMPLETE source, with an independent quantitative tail payment, not a cancellation theorem for its hard finite spectrum. The logarithmic correction is part of that spectrum, not harmless bookkeeping. Arithmetic ancestry remains exact through the prime-power subtraction and weighted owner partition; no copied historical occurrence or altered admission mask is introduced.

### H. Competing Mechanisms

| Mechanism | Established result and strongest obstruction | Decision |
| --- | --- | --- |
| MS moving-clock variance plus endpoint Cauchy | MS1-MS3 remain paper-level inputs; MS4 returns a boundary worse than the paid one | Preserve component work; do not repeat it as a bootstrap |
| Exact complete Johnston return and high-tail payment | JT1-JT3 localize every possible sign failure; dangerous low signed sum still open | Continue, independent audit first |
| Freeze logarithmic transfer at its endpoint | JT4 exposes a potentially super-bias correction for allowed off-line modes | Reject that unquantified simplification; retain K |
| Favorable pairwise or per-lag signs | Prior X=209 halo/per-lag counterexamples and today's mixed-term witness remain | Do not infer full compensation from selected signs |
| Low dangerous spectrum always above -A_N/2 | Sufficient via JT3; not independently established and target-strength in consequence | CONJECTURE / CONDITIONAL, not a supplied lemma |

Protected VF-LOW RS/DR and SAT SG/BT/RZ work is not retired. The next Owner route is SAT. No other investigator's rotation is reset.

### I. Specialist Handoffs And Continuity

**Coordinator:** register JT2 as a fully restored proper-tail estimate and JT3 as a necessary low-height configuration for an original JOH failure. It meets the requested full signed return without claiming a new global exponent. Keep the native b_base comparator, SEARCH_BROAD and nine routes. Do not replace the unresolved low signed sum by finite-height RH as an assumed input.

**Analytic:** independently check T_X, the all-height absolute tail, finite-mesh density uniformity and the order of summation/maximization. The use of the current Guth-Maynard density theorem is a documented external input on actual zeta zeros, not a new RH_Lean density proof or a transfer from ideal coefficients. The optional moving-band question in J is smaller than the whole sign criterion but not sufficient alone.

**Wheel:** compare only through an actual map: (4) counts unique prime powers and exactly restores pi, whereas your LR three-root cofactor incidence concerns different Mobius coefficients. The exact odd-square boundary remains in T(R^2). No LR multiplicity bound is asserted to control these zero phases.

**Census:** the development N=7/N=71 and held-out N=529 sign/cross-term checks are sufficient source regressions; no larger sign or zero-height scan is requested. Any future numerical test of K must certify the entire logarithmic kernel and analytic tail, not truncate a zero list and infer an all-scale sign. The unknown N0 is not a finite certificate.

**Referee:** priority is independent reconstruction of (1)-(4), then (7)-(9) and the aggregate JT3 sign. Try to break lower-end constants, denominator signs, density losses, multiple zeros, all-N uniformity and the use of PNT only for P_2's asymptotic. Review the actual full source, not a frozen-log variant. No independent acceptance is presumed.

**Lean:** no new proof branch or wrapper is requested before independent analytic review and a consuming proof choice. The finite prime-power and triangular identities are elementary, but a formalization must not assume the unproved low signed bound or pretend the classical density/explicit-formula bridge is already imported. Reuse the existing strict-baseline evidence.

Relevant committed sections from both Eastern dates were retrieved and read; TODAY=AVAILABLE for all seven, YESTERDAY=CARRY_FORWARD at original scope. No later scheduled run or review is presumed. Intake reporting head was **c06219edf131961b6b1ecf0aa08d3b0b30afc1f0**.

| Role | November 6 blob | November 7 intake blob |
| --- | --- | --- |
| Coordinator 00/90, identical directory blobs | 8812a90540fb511279b5f4ce08e108ef717d5ef1 | 785c56207f0745244d8c2503a18ed7b4d91b39e6 |
| Owner 10 | 1856a96aaaa9d86a5ee2d59ffe50ced936443fa6 | 432fc87602f97318fdac212002b52ac29f12a0e0 |
| Analytic 20 | 7997620b6ab7eb0701296994734ee910df3c3ba1 | 1315b3c9deba1148338d9023af349ee8a246dae7 |
| Wheel 30 | 3099558194a00358962ff1844bf283e625b9283d | b973552f1574e39afe6dbc165bde3635f12c9ead |
| Census 40 | c34ac074296e8b2e5b20dee3a2ce02518571206c | 3fae830e34c590d32c31ad77cad3ace833eb3ff5 |
| Referee 50 | da3265467c799e9d21832ab25245617ba3b15a54 | 65384576327e1ae2c976fca368c83690fc8a95dd |
| Lean 60 | b8bfe3ce9c20d7903395364efb39bcec974c8a2f | 2998b7339ea4b3e3fd2fd1d26f839527fd5adc95 |

Current Coordinator RG1-RG5 and Referee MH1-MH4 remain separate exact-consumer investigations. #1105 now supplies MH1 only, not MH2/MH3 or RG4. Analytic GL's large-gcd tail, FT's full Nyman norm and AQ's proper cube sector; Wheel DI/LR and earlier PB/GF; Census SC/RC and prior FW; Referee's NC/PF and previous spectral verdicts keep their original hypotheses. None supplies a sign for our low spectrum. Existing X=209, N=690/H=186, X=87283 donor-reuse and R=549 BLOCK counterexamples remain at their own carriers.

The external inbox was read at **038018145c0fddb2f6306c0712373adf9cd1ea52**. No post-October-18 entry exists in that snapshot. EXT-20261018-PNT-1..3, EXT-20261017-XCOORD-1's q=R boundary, and EXT-20261014-5's unconditional-versus-first-bad qualification are retained; they supply no missing low-zero estimate. All handoffs are published here only; no other agent was launched or another report edited.

### J. First Independently Missing Lemma

JT1-JT3 have complete paper arguments from the explicit incoming and external inputs; independent review and formalization remain pending. To close JOH one must still exclude the aggregate configuration in JT3. The full condition S_danger(N)>-A_N/2 for every large N would suffice, but is target-strength in consequence and is NOT presented as an independently known or easier lemma.

A smaller OPTIONAL new quantitative test is the following proper moving-band assertion, with b fixed, nu chosen as above and nu>1/5:

```text
Z_mid(N)=sum_(N^(1/5)<|gamma|<=N^nu,
             beta>1/2+1/log N) K_rho(N),
|Z_mid(N)| << N^(3/2)/(log N)^2  for every large integer N.  (OPEN-JOH-MID)
```

This is CONJECTURE / EXPLORATORY, not a premise in JT1-JT3. The proved uniform-a tail bound at its lower cutoff gives at rounded b=7/8 only exponent 797/520=3/2+17/520, before positive loss. Other stronger sigma-dependent density estimates may improve that comparison and must be substituted before treating 17/520 as an optimal deficit. No optimality claim is made. The question asks for a genuinely stronger restriction on a MOVING band, from actual zero phases or another established analytic theorem, not a larger isolated clock variance scan.

Success would further localize possible failure below N^(1/5); it would NOT control lower-height zeros or settle the original sign. Fixed off-critical zeros eventually lie outside this moving band, so the proposed statement is not merely the assertion that all such zeros are absent. The smaller statement's independence from RH is not claimed as a formal logical separation. A source-valid obstruction, or a proof using a sharper existing supplier, would both be useful. The full low-spectrum exclusion remains the unresolved endpoint problem.

### K. Next-Run Resume Capsule And Publication State

```text
RUN: 20261107-owner-3; scheduled 16:15:01 EST; RUN_ID_UNAVAILABLE.
MAIN: cae99df1c3ea24ff4113063bf09f6fd07517ad93.
ACKS: COMPLETE_SIGNED_HIGH_ATTACK_V1; CANCELLATION_CHAIN_REUSE_V1;
      PAID_BASELINE_EXACT_CONSUMER_V1; NO_PIGEONHOLING_ROUTE_SELECTOR_V1.
ROUTE: JOH; full G(N)=sum(pi-floor Li_2-1), original triangular weights.
NEW: exact positive logarithmic kernel, complete high-height tail,
     and quantitative necessary dangerous-low-zero aggregate at every failure.
INPUTS: fixed native zero boundary; credited density and explicit formula;
        unconditional reciprocal-ordinate square sum; PNT for P_2 only.
HEIGHT: nu>(b-1/2)/(2-(30/13)(1-b)); nominal threshold 39/178.
CONCRETE RETURN: nu=9/40, fixed error power 3/2-21/4160.
RETAINED: exact P_2, every higher power, floor/li(2)/lower-end constants,
          safe/danger and full quadratic interactions, odd-square boundaries.
UNPAID: signed low spectrum; original JOH sign and complete new HIGH endpoint.
FINITE: 256 certified original-source returns, 17 square boundaries,
        N=7 omitted-power sign reversal, N=71 positive omitted mixed term.
SCOPE: PAPER_PROOF / SELF_AUDIT; independent review PENDING; NOT_FORMALIZED.
NEXT JOH: independently audit JT1-JT3; compare actual suppliers for OPEN-JOH-MID.
NEXT PROTECTED OWNER ROUTE: SAT; resume SG/BT/RZ without repeating paid tails.
ETA_GATE: SEARCH_BROAD; NEW_VERIFIED_ENDPOINT_GAIN=NONE.
```

Early checkpoint commit **8b740d65018f89e61978346a0c12316c926282f4**, blob **56f391da9d8acfaf652f4e9afcc12936771c8c5e**, was re-fetched at the immutable commit and matched exactly. This append preserves all prior report bytes. Final publication remains PENDING_READBACK until the actual receipt below.

Actual limitations: no independent review, new Lean build or zero computation occurred. The classical Huxley original-paper download attempted during comparison returned HTTP 403; its inaccessible text is not relied on for an additional claimed sharper result. The retrieved primary Guth-Maynard, Johnston and Brent-Platt-Trudgian papers support the actual stated inputs. No main/source/policy/workflow/proof branch/PR/issue/schedule or another role's report was modified. No future background work is promised.

### Reproducibility Appendix - JT5

The new test registration and complete executed verifier follow. The helper is exactly the `Archived Reference Helper` already preserved in the [November 6 Owner MS5 appendix](https://github.com/OVVO-Financial/RH_Lean/blob/c06219edf131961b6b1ecf0aa08d3b0b30afc1f0/research/agent_reports/2026-11-06/10-owner-payment.md); it was extracted unchanged, not silently replaced. SHA256: helper `4e55172eca1a33ae27b5e3c96d087ded3983f9d44fdd28c151c7374359fab420`; final verifier `95a033e3da27623e731e4a62ff51b23c44073b43673b6f7273db99eae93b5923`; preregistration `33f31c554c4efc758162c89a5153f6ea3f173876b782618ff8ccdb9deac093b0`. Python syntax compilation and the executed assertions passed. These hashes certify the printed experiment's files, not the analytic theorems.

#### Frozen Test Registration

```text
# Frozen JOH Integrated-Return Test

Run: 20261107-owner-3. Frozen before the new verifier is executed.

- Actual carrier: primes, unique prime powers with weight 1/k, certified floor(Li_2(n)), B(n)=pi(n)-Q(n)-1, and G(N)=sum B(n).
- Development: all integers 4 <= N <= 256. Held out: N=529, 1024, 2048. Li floor certification through 2048.
- Verify the exact triangular source, integrated prime-power correction, least-prime odd-owner count including odd-square endpoints, and all quadratic cross terms.
- Rival shortcut: replace pi by prime-power count Pi without restoring the weighted power terms. Seek the first sign-changing example in the development range; do not extend the search if absent.
- Rival shortcut: remove the mixed term from (G_Pi-P)^2. Seek the first actual arithmetic mismatch, not a synthetic Mobius model.
- Exact rational parameter tests: a=12/5 and a=30/13, b in {1/2,3/4,7/8,7/8-1/1000000}; cutoff thresholds, concrete nu=9/40, strict-loss spending, and limiting equality at the threshold.
- Analytic check: prove the positive log-transfer kernel by differentiation and integration by parts. No finite zero list, floating-point zero sign, or finite data are claimed to certify the infinite tail or its all-scale inverse consequence.
- Reuse the previously printed rational Simpson/log helper unchanged. New tests must label finite evidence separately from the paper theorem and must not pretend the unknown asymptotic threshold is reached.
```

#### Executed Verifier

```python
"""Exact registered arithmetic checks for the complete JOH prime-power return."""

from fractions import Fraction as F
from math import isqrt

from joh_clock_reference import S, certify_floors, sieve


LIMIT = 2048
DEVELOPMENT = range(4, 257)
HELD_OUT = (529, 1024, 2048)
q, bounds, width, margin = certify_floors(LIMIT)
prime, pi = sieve(LIMIT)
primes = [p for p in range(2, LIMIT + 1) if prime[p]]

power_atoms = []
for p in primes:
    k, power = 2, p * p
    while power <= LIMIT:
        power_atoms.append((power, p, k))
        k += 1
        power *= p
assert len({v for v, _, _ in power_atoms}) == len(power_atoms)

power_count = [F(0) for _ in range(LIMIT + 1)]
for power, p, k in power_atoms:
    for n in range(power, LIMIT + 1):
        power_count[n] += F(1, k)

g = [0] * (LIMIT + 1)
gp = [F(0)] * (LIMIT + 1)
for n in range(2, LIMIT):
    g[n + 1] = g[n] + pi[n] - q[n] - 1
    gp[n + 1] = gp[n] + pi[n] + power_count[n] - q[n] - 1

first_sign = None
first_mixed_mismatch = None
first_positive_mix = None
rows = []
square_checks = 0
for N in list(DEVELOPMENT) + list(HELD_OUT):
    p2 = sum((F(N - power, k) for power, _, k in power_atoms
              if power < N and k == 2), F(0))
    p3 = sum((F(N - power, k) for power, _, k in power_atoms
              if power < N and k >= 3), F(0))
    powers = p2 + p3
    assert g[N] == gp[N] - powers
    triangular = sum((N - k) * (prime[k] - q[k] + q[k - 1])
                     for k in range(3, N))
    assert triangular == g[N]
    odd_candidates = sum(N - k for k in range(3, N, 2))
    composite = sum(N - k for k in range(3, N, 2) if not prime[k])
    model = sum(q[2:N])
    assert g[N] == odd_candidates - composite - model
    assert g[N] ** 2 == gp[N] ** 2 + powers ** 2 - 2 * gp[N] * powers
    assert (g[N] ** 2 == gp[N] ** 2 + p2 ** 2 + p3 ** 2
            - 2 * gp[N] * p2 - 2 * gp[N] * p3 + 2 * p2 * p3)

    if N in DEVELOPMENT and first_sign is None and g[N] < 0 <= gp[N]:
        first_sign = (N, g[N], str(gp[N]), str(p2), str(p3))
    if N in DEVELOPMENT and first_mixed_mismatch is None and gp[N] * powers:
        first_mixed_mismatch = (N, str(-2 * gp[N] * powers))
    if N in DEVELOPMENT and first_positive_mix is None and gp[N] < 0 and powers:
        first_positive_mix = (N, g[N], str(gp[N]), str(powers),
                              str(-2 * gp[N] * powers))

    R = isqrt(N)
    if R * R == N:
        interior = sum(N - k for r in range(2, R)
                       for k in range(r * r + 1, (r + 1) ** 2)
                       if k % 2 and not prime[k])
        square_boundary = sum(N - r * r for r in range(3, R, 2))
        assert composite == interior + square_boundary
        square_checks += 1
    if N in HELD_OUT:
        rows.append((N, g[N], str(gp[N]), str(p2), str(p3)))

assert first_sign is not None
assert first_mixed_mismatch is not None
assert first_positive_mix is not None

exponent_rows = []
for a in (F(12, 5), F(30, 13)):
    for b in (F(1, 2), F(3, 4), F(7, 8), F(7, 8) - F(1, 10**6)):
        d = 2 - a * (1 - b)
        threshold = (b - F(1, 2)) / d
        assert d > 0 and 0 <= threshold < 1 / a
        assert b + 1 - d * threshold == F(3, 2)
        nu = F(9, 40)
        assert threshold < nu < 1 / a
        tail_power = b + 1 - d * nu
        saving = F(3, 2) - max(F(3, 2) - nu, tail_power)
        assert saving > 0
        assert max(F(3, 2) - nu, tail_power) + saving / 2 < F(3, 2)
        exponent_rows.append((str(a), str(b), str(threshold),
                              str(tail_power), str(saving)))

assert (F(7, 8) - F(1, 2)) / (2 - F(12, 5) / 8) == F(15, 68)
assert (F(7, 8) - F(1, 2)) / (2 - F(30, 13) / 8) == F(39, 178)
assert F(15, 8) - F(9, 40) * F(89, 52) == F(3099, 2080)
assert F(3, 2) - F(3099, 2080) == F(21, 2080)
assert F(1, 2) + F(3, 20) < F(2, 3)

print('PASS exact actual-source returns:', len(DEVELOPMENT) + len(HELD_OUT))
print('PASS square-endpoint interior/boundary returns:', square_checks)
print('First dropped-prime-power sign reversal:', first_sign)
print('First nonzero omitted mixed term:', first_mixed_mismatch)
print('First positive omitted mixed term:', first_positive_mix)
print('Held-out (N,G,G_Pi,P2,P_ge3):', rows)
print('Exact (density,b,threshold,tail_power,saving):', exponent_rows)
print('Li certificate maximum width:', F(width, S))
print('Li certificate minimum floor margin:', F(margin, S))
print('FINITE ONLY: no zero-list or all-scale analytic validation was performed')
```

#### Verified Execution Output

```text
PASS exact actual-source returns: 256
PASS square-endpoint interior/boundary returns: 17
First dropped-prime-power sign reversal: (7, -1, '1/2', '3/2', '0')
First nonzero omitted mixed term: (5, '-1/2')
First positive omitted mixed term: (71, -157, '-7/60', '9413/60', '65891/1800')
Held-out (N,G,G_Pi,P2,P_ge3): [(529, -2707, '2057/2520', '3205/2', '2785397/2520'), (1024, -6703, '-5408/45', '3953', '118342/45'), (2048, -16599, '-31069/210', '20415/2', '655573/105')]
Exact (density,b,threshold,tail_power,saving): [('12/5', '1/2', '0', '33/25', '9/50'), ('12/5', '3/4', '5/28', '287/200', '13/200'), ('12/5', '7/8', '15/68', '597/400', '3/400'), ('12/5', '874999/1000000', '1874995/8499988', '74624977/50000000', '375023/50000000'), ('30/13', '1/2', '0', '681/520', '99/520'), ('30/13', '3/4', '13/74', '1487/1040', '73/1040'), ('30/13', '7/8', '39/178', '3099/2080', '21/2080'), ('30/13', '874999/1000000', '4874987/22249970', '3098999/2080000', '21001/2080000')]
Li certificate maximum width: 40222755730802479125082494402985/340282366920938463463374607431768211456
Li certificate minimum floor margin: 35228265328053005012477392063787261/340282366920938463463374607431768211456
FINITE ONLY: no zero-list or all-scale analytic validation was performed
```

Final authority refresh at 2026-11-07T21:35:08Z (16:35:08 EST) again returned main `cae99df1c3ea24ff4113063bf09f6fd07517ad93` and no open/draft PRs. No authority change was detected during this investigation.

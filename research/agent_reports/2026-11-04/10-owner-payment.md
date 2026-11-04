# RH | Owner Payment - 2026-11-04

**Completed mathematical finding:** the genuine growing reciprocal-band prime error from 20261103-owner-1, equation (63), has the improved bound **E_R = O(R^(11/6))** from the unchanged, already-established fixed Mertens envelope with exponent 7/8. The earlier envelope was R^(31/16); the proper-band saving is 5/48. This is a baseline-derived supporting estimate, **not a new Mertens exponent, independent endpoint gain, or RH proof**. Both endpoint anchors and the full original complement remain present.

Actual invocation: scheduled 2026-11-04 00:09 EST (-0500), America/New_York; RUN_ID_UNAVAILABLE. This synthesis completes that invocation, not a second run. Claim **20261104-owner-1**, subclaims S1-S5. Mathematical status: PAPER_PROOF / SELF_AUDIT, IDENTITY_ONLY where specified, and certified FINITE_COMPUTATION with scoped REFUTED shortcuts. Independent Referee review and new Lean formalization: PENDING.

## A. Most Important Mathematical Development

The growing-band question can be advanced without postulating a new signed prime-error theorem. An exact Abel transform differentiates the Mertens coefficient: the interior coefficients become individual mu(d), while the two genuine Mertens endpoint weights remain. An elementary log-hyperbola argument transports the SAME known prefix envelope to a prime-error envelope. Their combination proves a fixed power improvement over the previous source-specific bound.

For any fixed 1/2 <= b < 1 and C >= 1 satisfying |M(n)| <= C n^b for every integer n >= 1, put alpha = 1/(2-b). The new proved implication is

```text
|pi(x)-Li_2(x)| <<_(b,C) x^alpha                    (S2)
|E_R| <<_(b,C) R^((1+3alpha)/2),  R >= 16.          (S3)
```

Here Li_2(x)=integral_2^x dt/log t, not principal-value li. The complete proof appears in D. All constants are independent of x and R; neither an improved b nor any unknown correlation estimate is used.

Compared with the previous bound R^((3+b)/2), the exponent saving is

```text
delta_band(b) = (1-b^2)/(2(2-b)) > 0.
b=7/8: alpha=8/9, old=31/16, new=11/6, saving=5/48.
```

This repairs the previous claim that only the crude bound was presently supplied by the prefix input. The Abel identity and general hyperbola method are standard; the new contribution relative to the retrieved continuation is their explicit, source-faithful quantitative application to equation (63). It is not a claim of literature novelty.

There is no newly proved cancellation inside the remaining OAI all-selected inverse row. Native mu and ideal-character phases are not identified. The additional signed-LOW campaign stays SEARCH_BROAD.

## B. Current Authoritative Objective

Pinned main: **040980c16901af749202e9b0f91211c43909404a**. Canonical target remains OPEN:

```text
VFCanonicalSquareVonKochStatement:
  exists C >= 0, forall natural R >= 2,
    |pi(R^2)-vfCanonical(R^2)| <= C R log R.
```

The canonical sqrt(2) phase and its actual-prime carrier are unchanged. The explicit classical von Koch criterion is not supplied by this run. The distinct SAT carrier is the original rational Mobius square prefix and its strict post-root prime transport, not the original masked/clipped #915 physical VF source.

### Authority And Source Ledger

All RH_Lean files below were fetched at the pinned main, not inferred from reports.

| File | Blob SHA | Scope actually inspected |
| --- | --- | --- |
| AGENTS.md | b878d396c387a57bd0b5165fecf10d15ef3732cd | Current authority, own-report-only permissions, no local Lean or agent launches |
| CURRENT_PROOF_CONTRACT.md | 63f7553bf6e5f2a16e37808116c643dc0dcc50e1 | Canonical target, complete source, current OAI priority |
| docs/RHLEAN_NATIVE_SQUARE_CLOCK_AGENT_DIRECTIVE_20261029.md | 3cb817ab9aae51429858d5a98727e16dbd072d47 | Live task selector |
| docs/RHLEAN_BROAD_SEARCH_UNTIL_ETA_20261031.md | f5d754ce6b06d98643f30beeccb4bf7bd1f6242a | Protected portfolios and complete-gain gate |
| docs/RHLEAN_SOURCE_FAITHFUL_COMPLETE_RETURN_AGENT_CONTRACT_20261031.md | 4775ee5fd95f279beab08a75d1e17127078b19a6 | Original occurrence, signed restoration, uniformity |
| docs/RHLEAN_OAI_LOW_SOURCE_FIRST_AGENT_CONTRACT_20261103.md | b6980c30e63bb8c9ddfc8d6fa86a2bb401707fa6 | SOURCE_FIRST_VERSION 2026-11-03 |
| docs/RHLEAN_SEVEN_AGENT_RESEARCH_ENGINE_20261101.md | 495fa9ee2067ccf5db9dc3c48ffaaadcd6485aa4 | Persistent NEXT-OWNER and protected SAT rotation |
| docs/RHLEAN_ALL_VECTOR_AGENT_PROMPTS_20261030.md | 6fa78bdecd4670075350f269f54e88618359e94d | Current Owner role |
| docs/DYNAMIC_RESEARCH_AGENTS.md | ea90322f257a12dc694ca4a188fe4c5715880c79 | Research/report workflow |
| RHLean/Proof/LargePrimeTerminalFlipLayers.lean | b7617df21b81002854a0d311ef7e02d9494154c3 | Actual packet, clipped prime prefix, finite Abel theorem, integer layer cards |
| RHLean/Analysis/SquareRootPostCrossingTail.lean | 660772bad3663d14c0f3390e26925b57d1390080 | Full packet and coupled-tail/Mertens equality; target-equivalent bounded-tail consumer |
| research/PNT_FIRST_LAMBDA_HYPERBOLA_ANCHOR_20261018.lean | c67797ae7cda0ad9a7c393c69715016685a14d0a | Existing Mobius/log/von-Mangoldt identities; distinct full error and model |
| research/oai_434/VF919NativeStrictMertens.lean | b33a4883e1ddb0551b0f11f062bce46680d87450 | native_mertens_fixed_strict_power and explicit no-Mobius/Hecke-identification scope |
| research/oai_434/VF919OriginalLowTupleSignedGram.lean | c1b7b46a9e62a5b2f3729618c4dd24e31558166f | Literal LOW atoms, complete Hermitian Gram and NNS equality |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb | Actual target definition and conditional classical interface |

Original OAI pin: **openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a**, under lean/OAI/NumberTheory/DirichletL/Detector/.

| File | Blob SHA |
| --- | --- |
| LowSlotSplit.lean | 8c8fe01a1b3fffe3b06839c2befc2ddae39a2c9b |
| LowSlotPolynomial.lean | b1dcb5a1e51afad1d39ccd91fa58a764e39629ba |
| LowTupleGram.lean | 710598c8bef4d1a1ec98aa7e68b00369962c3d17 |

### Live PR And Formal Evidence

The open/draft PR collection returned **no entries**. PR #1083 is merged, head **1ae84e2ff019b266114c100f43016eeec71144a9**, merge **040980c16901af749202e9b0f91211c43909404a**, human merge time 2026-11-04T00:27:40Z. All **13 returned head-associated workflows** completed successfully, including dedicated run **41744927180** and source-audit run **41744927164**. This run refreshed those results; it did not launch CI.

The prior Coordinator/Referee inspection records a synthetic PR-merge checkout 06cac0b95a56fdef0f61294e257e67ee2146c32c and a signed-Gram blob identical to current main. Their recorded terminal axiom lists are exactly propext, Classical.choice, Quot.sound. That qualified log evidence is carried forward, not falsely described as a fresh log audit here. The three source identities are established infrastructure, not a new inequality.

Recent work verified by live metadata: #1084 policy, #1082 owner diagonal, #1081 exceptional Gram and #1079 slot-minimum work are merged; #1080 is closed without merge; #1073 is merged. The existing strict Mertens result is used at its inherited accepted scope, not reproved. No new value of its gap is invented.

### Continuity

At intake the November 4 report directory returned 404. **TODAY=PENDING; YESTERDAY=CARRY_FORWARD.** All seven November 3 role reports were retrieved at reporting snapshot **9ae0ffc891087365ed088a35fbbe09e4afe0af18**; applicable claim, correction and resume sections were read. The matching Coordinator mirrors were not counted as two independent reports.

| November 3 role | Blob SHA | Relevant continuity |
| --- | --- | --- |
| Coordinator 00/90 | e35ab2cd9cba2a47ac5be53b09938b37a0c20df3 | Latest 20261103-coordinator-3, C37-C40, SAT continuation, all-selected OAI localization |
| Owner | d52c74b76c2914c3be694f39cd7afe9b122a4834 | owner-1 equations (63)-(65), owner-2 O1-O5, owner-3 JH1-JH10 |
| Analytic | 2b9c3dbab6039e3c30a5ece3e473290af5dbbf0b | CD1-CD6 logarithmic fragment control, not fixed-power shell gain; N9 reciprocal-Mobius constants already used |
| Wheel | cd7777180bb5c2c899a60bdd699b99be8e12a672 | Original LOW O1-O4 coherence; MU-LIFT retained top-prime obstruction |
| Census | eb9a2e0cf7772f22060aec07e0bcddd24ace9cd9 | census-5/6 exact norm-fiber cycle multiplicity; actual integrals not evaluated |
| Referee | 583ce524628577818603ffd4e9ec0eb3673a3f37 | referee-8/9/10 source audit, nonempty moving mass, empty packet; scoped prior corrections |
| Lean | fc27fb1ae103e60ff600e5a24ce6716937da3884 | lean-3 independent paper qualification of R9/R10, heterogeneous mass core; uncompiled draft and reported write blocker |

External inbox **038018145c0fddb2f6306c0712373adf9cd1ea52** has no entry newer than October 18. EXT-20261018-PNT-1/2/3, the q=R correction in EXT-20261017-XCOORD-1, and EXT-20261014-5 retain their original scope. They do not provide a new ideal-tuple occurrence map. No historical finite scan was rerun as this run's result.

## C. Structural Hypothesis Investigated

The latest completed Owner turns were SAT / VF-LOW / JOH. SAT is due and explicitly assigned by Coordinator 20261103-coordinator-3. This run resumes equation (63), rather than restarting fixed-depth zero-layer arithmetic or diverting all protected work to OAI.

Three mathematical possibilities were compared:

1. Treat each short prime interval independently. This retains large |M(d)| weights and gives the previous crude envelope; ordinary fixed-dilation PNT does not supply growing-window uniformity.
2. Differentiate the exact Mertens weights and retain BOTH endpoint contributions. This is the selected mechanism. Pair it with an explicitly proved transport of the unchanged Mertens input to the actual prime discrepancy.
3. Assume favorable signs of the error or discard its endpoint anchors. This is not needed by the proof and is falsified by source-admitted certified examples below.

The candidate does not assume Mertens growth below the repository's existing input. It uses the deterministic multiplicative identity mu * log = Lambda, not independence between primes and Mobius signs. A generic comparison sequence with the same prefix envelope but without this convolution identity would not supply S2.

## D. Mathematical Derivation

### S1. Literal Band And Exact Endpoint Accounting

Let R >= 16 be an integer and set

```text
q = 2R, Y = q^2-1, D=floor(sqrt R), B=2D-1,
x_d=floor(Y/d), M(t)=sum_(1<=n<=floor(t)) mu(n),
Delta(x)=pi(x)-Li_2(x),
N_q(d)=#{prime p: max(q,x_(d+1)) < p <= x_d}.
```

For D <= d <= B, x_(d+1) >= x_(2D) >= q. Indeed D<R and Y >= 4RD = q(2D). Thus the original clipping agrees exactly with these endpoints. Every admitted prime is strictly greater than q, and d<q<p. In particular p occurs only once in every original integer pc with 1<=c<=d, so mu(pc)=-mu(c), including squareful-cofactor zeros.

Write the genuine band and the original model/error split as

```text
T_R = P_q(B)-P_q(D-1) = -sum_(d=D..B) M(d) N_q(d),
L_R = -sum_(d=D..B) M(d)[Li_2(x_d)-Li_2(x_(d+1))],
E_R = T_R-L_R
    = -sum_(d=D..B) M(d)[Delta(x_d)-Delta(x_(d+1))].       (S1a)
```

All prime owners in (x_(2D),x_D] occur once; expanding -M(d) retains every cofactor c, sign and physical integer. No prime eligibility is substituted for actual admission.

Discrete summation by parts gives exactly

```text
E_R = -M(D) Delta(x_D) + M(B) Delta(x_(2D))
      -sum_(d=D+1..B) mu(d) Delta(x_d).                  (S1b)
```

Proof: the coefficient of Delta(x_D) is -M(D); that of each interior Delta(x_d) is M(d-1)-M(d)=-mu(d); the final coefficient is M(B). This is a specialization of the already-compiled finite Abel pattern in squareRootTruncatedUpperMiddlePacket_eq_abel, not a newly discovered general identity.

Because M(B)=M(D)+sum_(D<d<=B)mu(d), its centered, anchor-preserving form is

```text
E_R = -M(D)[Delta(x_D)-Delta(x_(2D))]
      -sum_(d=D+1..B)mu(d)[Delta(x_d)-Delta(x_(2D))].     (S1c)
```

The coefficient sum is zero, so changing Li_2 by a fixed constant would cancel in THIS band. Nevertheless the actual Li_2 convention is used throughout, including the certified examples. Neither endpoint may be removed individually.

### S2. Elementary Prime-Error Transport From The Same Prefix Input

**Theorem.** Fix 1/2<=b<1 and C>=1. If |M(n)|<=C n^b for every integer n>=1, then there is K_(b,C) such that, for all real x>=2,

```text
|psi(x)-x| <= K_(b,C) x^(1/(2-b)) log(2x),
|pi(x)-Li_2(x)| <= K_(b,C) x^(1/(2-b)).                 (S2)
```

Constants are uniform in x. The proof does not assume any short-interval estimate or new zero-free region. The real extension M(t)=M(floor t) inherits the same bound.

**Step 1: constants in the harmonic Mobius sums.** Partial summation under b<1 gives locally uniform convergence near s=1 of F(s)=sum mu(n)n^(-s) and its derivative. For real s>1, the divisor identity mu*1=epsilon and absolute convergence give F(s)zeta(s)=1. The simple pole of zeta at 1 has residue 1, hence F(1)=0 and F'(1)=1. Therefore

```text
sum_(n>=1) mu(n)/n = 0,
sum_(n>=1) mu(n)log(n)/n = -1,
A(y):=sum_(n<=y)mu(n)/n = O_(b,C)(y^(b-1)),
B(y):=sum_(n<=y)mu(n)log(n)/n
     = -1 + O_(b,C)(y^(b-1)log(2y)).                    (S2a)
```

For example the first tail is bounded by C y^(b-1)[1+1/(1-b)]; integrating |M(t)|(1+log t)t^(-2) supplies the second with constants depending only on b,C. Termwise differentiation is justified by uniform tails for s in a closed interval strictly above b. These constants were already used in Analytic N9; they are not new discoveries.

The standard inputs were checked in the primary [NIST DLMF zeta definition](https://dlmf.nist.gov/25.2#i) and [Mobius inversion formulas](https://dlmf.nist.gov/27.5). Only the pole normalization and convolution identities are taken from those references; the transport estimate is proved here, not attributed to them.

**Step 2: complete log-hyperbola, with its overlap.** Put S(u)=sum_(1<=m<=u)log m. For 1<=y<=x, mu*log=Lambda gives the exact identity

```text
psi(x)=sum_(d<=y)mu(d) S(x/d)
       +sum_(m<=x/y)log(m)[M(x/m)-M(y)].                (S2b)
```

Every pair dm<=x is counted once: d<=y in the first term, d>y in the second. The subtraction M(y) is mandatory; this is not a cloned overlap or an unexplained analytic error.

Integral comparison of log m, with floor(u) retained, gives uniformly for u>=1

```text
S(u)=u log u-u+O(log(2u)).
```

Thus the first term of S2b equals

```text
x[(log x-1)A(y)-B(y)] + O(y log(2x))
 = x + O_(b,C)(x y^(b-1) log(2x)+y log(2x)).           (S2c)
```

The second term has absolute value at most

```text
C x^b sum_(m<=x/y) m^(-b)log m
 + C y^b sum_(m<=x/y)log m
 <<_(b,C) x y^(b-1) log(2x).                          (S2d)
```

The elementary bound sum_(m<=z)m^(-b)log m <<_b z^(1-b)log(2z) follows by integral comparison. Choosing y=x^alpha with alpha=1/(2-b) balances y=x y^(b-1) and proves the psi estimate in S2. Nonintegral y is harmless because both sides of S2b use the same d<=y and M(y); rounding y comparably gives the same bound.

**Step 3: restore prime powers and the Li normalization.** With vartheta(x)=sum_(p<=x)log p,

```text
0<=psi(x)-vartheta(x)<<sqrt(x)(log(2x))^2.
```

This follows simply by counting prime powers p^k<=x for k>=2. Since alpha>=2/3, that error is absorbed into O_(b,C)(x^alpha log(2x)); no prime-power term is discarded. Stieltjes partial summation gives

```text
pi(x)-Li_2(x)
 = [vartheta(x)-x]/log x
   +integral_2^x [vartheta(t)-t]/[t(log t)^2] dt
   +2/log 2.                                           (S2e)
```

The fixed constant is checked at x=2. The first term is O(x^alpha). For the integral use log(2t)/log t <=2 for t>=2 and integrate t^(alpha-1)/log t <= t^(alpha-1)/log 2. This proves the second estimate in S2 without an extra logarithmic loss. The theorem is deliberately weaker than any sharper zero-free-region transfer that may be available; no unverified stronger bridge is needed.

### S3. New Bound For The Actual Growing Band

Apply S2 at every original integer cutoff x_d. Since x_d<=Y/D and |mu(d)|<=1, S1b yields

```text
|E_R| <= [|M(D)|+|M(B)|+sum_(D<d<=B)|mu(d)|]
           * max_(D<=d<=2D)|Delta(x_d)|
      <<_(b,C) D (Y/D)^alpha
       = O_(b,C)(Y^alpha D^(1-alpha)).                 (S3a)
```

Here M(D),M(B)=O(CD^b)=O(CD); the endpoint bound is not omitted. For R>=16, D is comparable to sqrt R and Y is comparable to R^2, so

```text
|E_R| <<_(b,C) R^((1+3/(2-b))/2).                     (S3b)
```

Subtracting this exponent from (3+b)/2 gives delta_band(b) above. This holds at the SAME b; it is not the previous formula with a newly conjectured smaller prefix exponent substituted.

The main declaration native_mertens_fixed_strict_power gives a fixed envelope strictly below 7/8. Weakening that already-established envelope to b=7/8 gives directly

```text
exists K>=0, forall integers R>=16, |E_R|<=K R^(11/6). (S3c)
```

No numerical K is evaluated. If one elects to use only the older all-positive-loss 7/8 input, the conclusion is instead O_epsilon(R^(11/6+epsilon)); take the input loss sufficiently small and use continuity of 1/(2-b). This distinction prevents assuming a fixed endpoint envelope from an epsilon-loss statement alone.

### S4. Complete Physical Return And Every Cross Term

Let A_q(Y)=sum_(n<=Y, largest_prime_factor(n)<=q)mu(n), with largest_prime_factor(1)=1. The source theorem gives

```text
M(Y)=A_q(Y)+P_q(q-1),
C_R=A_q(Y)+P_q(D-1)+[P_q(q-1)-P_q(B)],
M(Y)=T_R+C_R=L_R+E_R+C_R.                             (S4a)
```

C_R is explicitly the entire smooth population plus every unselected reciprocal layer, including the prime-only top layer, residual cofactor classes and terminal layers. The native strict p>q rule is unchanged. This is an exact population complement, not a conjectural error.

The full square is

```text
M(Y)^2=T_R^2+C_R^2+2T_R C_R
       =L_R^2+E_R^2+C_R^2
         +2L_R E_R+2L_R C_R+2E_R C_R.                 (S4b)
```

Neither a selected sum of squares nor a local favorable sign replaces this expression. No size bound for L_R+C_R is supplied by S3. The crude model bound can still be of order R^((3+b)/2)/log R, and it cannot be discarded. Moreover 11/6 exceeds the inherited terminal root-scale exponent 7/4 by 1/12. Even this improved error estimate alone is not strong enough to improve that terminal exponent.

### S5. Bounded Source-First Comparison, Not A New Bridge Claim

The literal OAI source has J unselected, SelectedSlot J its complement, original lowSelectedWeight containing the conjugate Hecke coefficient and logarithmic phase, and lowUnselectedWeight containing (-1)^|J| L^(-3/2) and the original windows. LowSlotPolynomial retains the selected inverse integral, calibration, W0/W1, lowOuterCutoff and (sqrt(Q))^(-1)/(2pi). LowTupleGram then uses norm_sum_le over the original unselected tuples. The merged NNS theorem equals the complete diagonal plus ordered Hermitian off-diagonal; it supplies no sign estimate.

For J=empty, the outer tuple is the unique empty function, L=1 and the outer weight is 1. Thus its outer cross Gram is zero; the source still contains every selected slot inside the inverse row. Referee-10 already establishes this observation. It is reused, not republished as a new discovery.

**A concrete limited mapping obstruction:** at the actual SAT root parameter R=16, p=131 is an admitted owner in (127,255], quotient 7. The distinct original integers 131 and 262 have coefficients -1 and +1, respectively, in the literal band. An occurrence-by-occurrence injection of these native physical seats into the singleton J=empty OUTER tuple carrier is impossible. This refutes only a direct outer-atom bijection. Grouping is possible but must preserve its fiber coefficient and all cross terms; a representation inside the selected inverse row is not ruled out. No nonzero OAI integral or terminal norm lower bound is inferred from the witness.

The full native-owner-to-selected-OAI occurrence/weight map remains UNPROVED. This run therefore exports no SAT gain into OAI. The due SAT route was authorized to replace the default deeper OAI packet, and this bounded comparison preserves the source-first safeguards.

## E. Quantitative Consequence

| Quantity | Proven scope | Exponent or consequence |
| --- | --- | --- |
| Prime error Delta(x) | PAPER_PROOF from fixed genuine Mertens envelope b | x^(1/(2-b)), uniformly in real x>=2 |
| Actual growing SAT error E_R | PAPER_PROOF from the SAME b | R^((1+3/(2-b))/2) |
| b=7/8 proper-band comparison | Baseline-derived supporting theorem | 31/16 -> 11/6, saving 5/48 |
| Complete band T_R | Exact model/error reconstruction only | No new bound for the unremoved model L_R |
| Complete M(Y), canonical VF, sharp shell energy | No new bound | New endpoint gain UNKNOWN; none established |
| Original OAI squared LOW / amplitude / final beta | No same-source transfer | UNKNOWN / UNKNOWN / UNKNOWN |

The prior proposed OPEN inequality (63) at unchanged b has now been met in the displayed proper-band sense by S3. Its demanded source of improvement is made explicit: Mobius/log convolution plus exact finite Abel differentiation, not a stronger assumed b or small positive Gamma. If the strategic intent was a genuinely NEW arithmetic hypothesis beyond all consequences of the known prefix envelope, this does not supply one. It identifies a paid baseline consequence so the next investigation can start at a stricter, genuinely unpaid correlation problem.

## F. Falsification And Circularity Review

### Exact And Certified Tests

The preregistered discovery roots were 16..36; held-out roots were 64,65,127,128. After locating the first suitable zero upper-endpoint Mertens coefficient, R=400 (B=39, M(B)=0) was declared and added as a targeted control before its band calculation. This was not an undisclosed supportive range scan. All 26 roots were checked using integer arithmetic for the population, coefficient maps and full square. A separate trial-factorization check verified mu at 1..1023. The log-hyperbola S2b was checked in 30 independent (X,y) cases by expanding coefficients of log p exactly, not by comparing decimal logarithms.

Across the band checks, **62,311 physical occurrences** were reconstructed from actual prime owners and cofactors, including squareful zero terms. Every owner was strictly above 2R; physical integers were unique within each band; mu(pc)=-mu(c), both Abel forms, the literal complement and every integer quadratic cross term agreed.

Li_2 values were enclosed with 180-bit outward-rounded rational interval arithmetic, 90 terms of the range-reduced atanh logarithm series, and 180 terms of the Ei series with an explicit positive geometric tail. Euler's constant cancels in Li_2=Ei(log x)-Ei(log 2). The certificate is embedded below. These are finite certificates, not a numerical proof of the asymptotic estimate.

| R | D | T_R | C_R | M(Y) | Certified E_R enclosure | Certified omitted S1b endpoint contribution |
| ---: | ---: | ---: | ---: | ---: | --- | --- |
| 16 | 4 | 33 | -37 | -4 | [-1.863905,-1.863904] | [2.294736,2.294737] |
| 25 | 5 | 75 | -76 | -1 | [0.135496,0.135497] | [-0.770760,-0.770759] |
| 36 | 6 | 109 | -111 | -2 | [0.959642,0.959643] | [6.506339,6.506340] |
| 64 | 8 | 255 | -287 | -32 | [-7.601680,-7.601679] | [-13.987591,-13.987590] |
| 128 | 11 | 723 | -709 | 14 | [-9.190005,-9.190004] | [-6.918154,-6.918153] |
| 400 | 20 | 3060 | -3010 | 50 | [-40.299278,-40.299277] | [-111.457328,-111.457327] |

Thus both universal favorable-sign shortcuts are REFUTED: E_R need not be nonpositive or nonnegative. Deleting the S1b endpoint contribution is also REFUTED by R=16. These statements are auxiliary failures, not counterexamples to S3 or RH.

At R=16 the complete square is 1089+1369-2442=16. At R=25 it is 5625+5776-11400=1. The large mixed cancellation is present explicitly. Neither the improving error bound nor the sign reversal makes that complement disappear.

### Self-Audit

The argument retains every finite-hyperbola overlap, floor, prime power, Li_2 constant and Mertens endpoint. The only quantitative input is the already-established fixed prefix envelope, used on the genuine mu. The reciprocal-series constants follow from that envelope and the elementary zeta pole, not an assumed desired prime-error estimate. There is no circular use of E_R, terminal M(Y), or an unknown owner covariance bound.

Targeted source/report search found the existing finite Abel identities and log-hyperbola infrastructure, but no identical S3 source-specific estimate in the retrieved continuation. This is not an exhaustive historical originality claim. In particular, S1 and S2a are explicitly reused standard mathematics. No new result is labeled PROVED_IN_LEAN.

## G. Conceptual Interpretation

The Mertens layer weight should not be normed before its exact discrete derivative is used. Its derivative is the actual coefficient mu(d), whose absolute size is at most one. That arithmetic dependence allows a global prime-error envelope to constrain the complete growing family of short reciprocal windows, without pretending that every short interval individually enjoys a sharp relative error.

The multiplicative identity mu*log=Lambda makes this more than an arbitrary-sequence Abel exercise: it connects the same genuine coefficient system to actual prime counts. However, this transfer is weaker than the inherited Mertens bound when returned to the terminal source. The result improves a proper sector and clarifies which stronger correlation is still missing; it does not bootstrap the known exponent.

## H. Competing Mechanisms

| Mechanism | Established and missing | Obstruction / decisive test | Decision |
| --- | --- | --- | --- |
| Exact Abel plus baseline log-hyperbola transport | S1-S3 pay the stated growing E_R sector | L_R and full complement remain; no endpoint bootstrap | Retain as paid supporting estimate after review |
| Independent centered mu/prime-error correlation | Defined precisely in J; no new cancellation theorem | Must beat the absolute interior bound and preserve the endpoint | Continue on a future SAT turn |
| Universal sign or endpoint deletion | False on genuine admitted roots | R=16 negative E and nonzero endpoint; R=25 positive E | Abandon only these shortcuts |
| Native outer-owner to all-selected OAI atom identification | Literal sources compared; no full bridge | J=empty singleton versus multiple native seats; phases/inverse weights not mapped | Reject direct outer bijection; inner-source transfer remains open |
| VF-LOW / JOH chronology | Prior O1-O5 and JH1-JH10 preserved at their actual status | Squareful capacity and adjacent-excursion falsifiers still binding | Keep protected rotation; VF-LOW next |

## I. Specialist Handoffs

**Coordinator:** register 20261104-owner-1/S3 as a baseline-derived PAPER_PROOF / SELF_AUDIT proper-band saving, not VERIFIED_ETA. The previous SAT equation (63) is paid at exponent 11/6 using the unchanged b=7/8 input; its full consumer is not. Separate paid baseline transport from genuinely new cancellation. Keep VF-LOW next and the nine-route programme intact.

**Adversarial Referee:** independently check S2a's derivative sign, the complete S2b overlap, y=x^(1/(2-b)), prime-power restoration, the +2/log 2 constant in S2e, both S1b endpoint signs and the exponents 11/6, 5/48 and 85/48. Challenge uniformity in x and R, the exact fixed-power versus epsilon-loss input, and whether the conclusion has been over-promoted. Give separate verdicts on S2, S3 and the certified auxiliary falsifiers. This author's checks are SELF_AUDIT only.

**Analytic Type II:** on a compatible future turn, assess the proper interior correlation in J against the now-paid baseline bound. No new OAI inverse-row or short-interval theorem is requested by analogy. Preserve due NYMAN and OAI/CODIV rotation. Your N9 reciprocal-Mobius constants are reused, not rediscovered.

**Finite Wheel & Incidence:** a useful additional structural input would constrain the actual signs mu(d) jointly with the prime-error differences at the original x_d, with the precise moving cutoff. Pure ancestry counts or a completed period on another source do not pay this correlation. No new scan or immediate diversion from CORR4 is requested.

**Prime Census:** the smallest independent check is R=16/R=25 with actual primes, all cofactor occurrences, both endpoints and interval-certified Li_2. Rival hypotheses are boundary-free Abel or a universal sign; both have explicit falsifiers. No larger exponent fit is useful. The reproducer also includes held-out boundary transitions and exact log-prime coefficient tests.

**Lean Verification:** no new proof branch or implementation is requested before independent acceptance and utility selection. If qualified, the finite band-Abel specialization can reuse squareRootTruncatedUpperMiddlePacket_eq_abel; the quantitative prime transport requires the genuine mu*log identity, summation by parts and the actual fixed Mertens envelope. Do not encode S2 or its prime-error conclusion as an unexplained project axiom. Your existing qualified moving-mass task remains separate.

These are published asynchronous handoffs in this authorized report, not claims that another agent has launched, reviewed or implemented the work.

## J. First Independently Missing Lemma

The former equation (63) target should not stay listed as untouched: S3 supplies an explicit improvement from existing inputs. The next candidate requiring genuinely new signed arithmetic is the proper interior expression

```text
I_R=sum_(D<d<2D) mu(d)[Delta(x_d)-Delta(x_(2D))].
```

Fix the existing b=7/8 envelope, so alpha=8/9. A concrete independent supplier to attempt is

```text
exists kappa>0, forall epsilon>0, exists C_epsilon,R_epsilon,
forall integers R>=R_epsilon:
  |I_R| <= C_epsilon R^(11/6-kappa+epsilon).            (OPEN-SAT-I)
```

No such kappa is proved or numerically inferred here. This is a proper component, not the canonical target renamed. Its relevance and limitation are exact: S1c gives E_R=-A_R-I_R, where

```text
A_R=M(D)[Delta(x_D)-Delta(x_(2D))],
|A_R| << R^(b/2+3alpha/2) = R^(85/48).
```

Therefore OPEN-SAT-I would give an additional E_R saving of min(kappa,1/16), up to arbitrary positive losses. Even the displayed separate endpoint estimate is still 1/48 above the inherited terminal exponent 7/4. This is an upper-bound limitation, NOT a lower bound or an impossibility theorem for joint cancellation. A complete endpoint improvement must additionally control or recombine the actual endpoint, model and C_R terms. They cannot be silently declared paid.

The next decisive mathematical action is to identify a genuine multiplicative/prime-location restriction yielding OPEN-SAT-I, or a precisely weaker independently useful estimate; mere centering or assuming the desired norm is not an input. This is queued after the protected VF-LOW and JOH turns.

## K. Next-Run Resume Capsule

```text
RUN: scheduled 2026-11-04 00:09 EST; RUN_ID_UNAVAILABLE.
MAIN: 040980c16901af749202e9b0f91211c43909404a.
REPORT_INTAKE: 9ae0ffc891087365ed088a35fbbe09e4afe0af18.
SOURCE_FIRST_VERSION: 2026-11-03.
POLICY: b6980c30e63bb8c9ddfc8d6fa86a2bb401707fa6.
ENGINE: 495fa9ee2067ccf5db9dc3c48ffaaadcd6485aa4.
TASK: due SAT, resume 20261103-owner-1 (63)-(65), bounded OAI comparison.
NEW CLAIM: 20261104-owner-1/S2-S3, paper proof, independent review PENDING.
LAST JUSTIFIED: exact E_R Abel endpoints; prime alpha=1/(2-b);
                E_R << R^((1+3alpha)/2), same fixed b.
EXPLICIT APPLICATION: b=7/8 gives 31/16 -> 11/6, local saving 5/48.
FULL RETURN: M(Y)=L_R+E_R+C_R; all six quadratic pieces retained.
FIRST OPEN: OPEN-SAT-I; endpoint bound 85/48 and full model/complement remain.
FINITE: 26 roots, 62311 occurrences, 30 exact log-hyperbola checks;
        1023 independent trial-factorization Mobius checks.
FALSIFIERS: R16 E<0 and endpoint nonzero; R25 E>0.
REVIEW: SELF_AUDIT; no new Lean theorem, no local Lean execution.
OAI: J unselected; J=empty is all selected, one outer atom, outer cross=0.
FIRST SIGN LOSS: original LowTupleGram norm_sum_le after exact Fubini.
OAI POWERS: inverse squared 5/6-2d+507epsilon; sqrt(Q) normalization;
            original Gaussian/full LOW 3/16; signal beta-11/16.
OAI NET: squared gain UNKNOWN; amplitude gain UNKNOWN; final beta UNKNOWN.
OAI RETURN: original principal/HIGH/remote/exceptions/tails not paid anew.
PR1083: merged, head 1ae84e2ff019b266114c100f43016eeec71144a9;
        13 returned head-associated workflows SUCCESS.
GATE: inherited strict-slot credit only; additional signed LOW SEARCH_BROAD.
NEW COMPLETE-ENDPOINT GAIN: NONE; canonical VF and RH remain OPEN.
LATEST OWNER ROTATION: VF-LOW (Nov3 owner-2), JOH (Nov3 owner-3), SAT (this run).
NEXT DISTINCT ROUTE: VF-LOW, preserve owner-2 O1-O5 source and capacity no-go.
JOH RESUME: owner-3 JH1-JH10, no adjacent-excursion payment revival.
SAT RESUME: S3 paid at paper level; attack OPEN-SAT-I only after rotation.
DEPLOYMENT_ACK: current main/source-first policy consumed through source audit,
                new same-b quantitative derivation and source-admitted tests.
```

### Execution And Publication Discipline

The early checkpoint was committed as **f05553af1226e7ac748c6696edb649f8217e52ca**, re-fetched at that commit as blob **c86aed5b4c69f73cc27faeb8472ba8d8c3e928ef**, and matched the submitted bytes exactly. It is preserved below. Final publication is certified only by the subsequent commit/readback receipt.

Executed commands: the embedded Python verifier and Python bytecode syntax check both passed. Verifier SHA256: **7d498342c68b308205a9ff6dea4dfc00a0edfd4c86cfc642561640ad7ca052ac**. The verifier performs no Lean execution and evaluates no OAI inverse integral. It is a finite audit, not the proof of S2/S3.

Direct shell cloning failed with CONNECT tunnel HTTP 403; connector reads and own-report publication worked. One large recursive-tree request failed, so targeted file reads were used. A guessed optional VF919NativeMertens path did not exist; the actual retrieved VF919NativeStrictMertens declaration supplies the input and is recorded above. These limitations did not block the mathematical work. Lean's earlier write-access report is not diagnosed anew here and is not a blocker for this own-report run.

No main, Lean source, central instruction, other-agent report, proof branch, PR, workflow, schedule, permission, or repository protection was modified. No other agent was launched and no merge was attempted. No background continuation is promised.

## Reproducibility Appendix

The complete executed verifier follows. Its interval enclosures use exact rational arithmetic and outward rounding; displayed decimals in the table are outward-rounded enclosures, not equalities.

```python
"""Exact SAT band regression and certified Li_2 boundary diagnostics.

Discovery roots 16..36; held-out 64,65,127,128. No asymptotic fit.
Targeted zero-endpoint control R=400 has B=39 and M(B)=0.
Interval arithmetic certifies Li signs; symbolic coefficient maps certify
identities independently of floating-point or quadrature cancellation.
"""

from collections import defaultdict
from fractions import Fraction
from functools import cache
from math import isqrt
import json

BITS = 180
SCALE = 1 << BITS
LOG_TERMS = 90
EI_TERMS = 180
ROOTS = list(range(16, 37)) + [64, 65, 127, 128, 400]
LIMIT = (2 * max(ROOTS)) ** 2 - 1


def ceildiv(a, b):
    return -((-a) // b)


def rat(n, d=1):
    return n * SCALE // d, ceildiv(n * SCALE, d)


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def sub(a, b):
    return a[0] - b[1], a[1] - b[0]


def scale(a, n):
    return (a[0] * n, a[1] * n) if n >= 0 else (a[1] * n, a[0] * n)


def mul(a, b):
    products = [x * y for x in a for y in b]
    return min(products) // SCALE, ceildiv(max(products), SCALE)


def div(a, b):
    assert b[0] > 0
    quotients = [Fraction(x * SCALE, y) for x in a for y in b]
    lo, hi = min(quotients), max(quotients)
    return lo.numerator // lo.denominator, ceildiv(hi.numerator, hi.denominator)


def small_log(n, d):
    assert d <= n <= 2 * d
    u = rat(n - d, n + d)
    u2 = mul(u, u)
    power, result = u, rat(0)
    for j in range(LOG_TERMS):
        result = add(result, div(scale(power, 2), rat(2 * j + 1)))
        power = mul(power, u2)
    tail = div(scale(power, 2), scale(sub(rat(1), u2), 2 * LOG_TERMS + 1))
    return result[0], result[1] + tail[1]


LOG2 = small_log(2, 1)


def log_rational(n, d=1):
    assert n > 0 and d > 0
    k = n.bit_length() - d.bit_length()
    num, den = (n, d << k) if k >= 0 else (n << (-k), d)
    if num < den:
        k -= 1
        num *= 2
    assert den <= num < 2 * den
    return add(small_log(num, den), scale(LOG2, k))


def ei_without_gamma(z):
    assert z[0] > 0
    result = log_rational(z[0], SCALE)[0], log_rational(z[1], SCALE)[1]
    term = rat(1)
    for k in range(1, EI_TERMS + 1):
        term = div(mul(term, z), rat(k))
        result = add(result, div(term, rat(k)))
    first = div(div(mul(term, z), rat(EI_TERMS + 1)), rat(EI_TERMS + 1))
    ratio = div(z, rat(EI_TERMS + 2))
    assert ratio[1] < SCALE
    tail = div(first, sub(rat(1), ratio))
    return result[0], result[1] + tail[1]


BASE = ei_without_gamma(LOG2)


@cache
def li(n):
    assert n >= 2
    return sub(ei_without_gamma(log_rational(n)), BASE)


def mobius_trial(n):
    sign, d = 1, 2
    while d * d <= n:
        if n % d == 0:
            n //= d
            sign *= -1
            if n % d == 0:
                return 0
        d += 1
    return -sign if n > 1 else sign


prime = bytearray(b"\x01") * (LIMIT + 1)
prime[:2] = b"\x00\x00"
mu, largest = [1] * (LIMIT + 1), [1] * (LIMIT + 1)
mu[0] = 0
for p in range(2, LIMIT + 1):
    if prime[p]:
        for n in range(p, LIMIT + 1, p):
            largest[n] = p
            mu[n] *= -1
            if n != p:
                prime[n] = 0
        for n in range(p * p, LIMIT + 1, p * p):
            mu[n] = 0
M, pi = [0] * (LIMIT + 1), [0] * (LIMIT + 1)
for n in range(1, LIMIT + 1):
    M[n], pi[n] = M[n - 1] + mu[n], pi[n - 1] + prime[n]
assert all(mu[n] == mobius_trial(n) for n in range(1, 1024))


def normalized(coefficients):
    return {n: c for n, c in coefficients.items() if c}


def value(coefficients, source):
    total = rat(0)
    for n, c in coefficients.items():
        total = add(total, scale(source(n), c))
    return total


def enclosure(a, places=6):
    unit = 10 ** places
    return [str(Fraction(a[0] * unit // SCALE, unit)),
            str(Fraction(ceildiv(a[1] * unit, SCALE), unit))]


records = []
physical_count = 0
positive, negative = [], []
for R in ROOTS:
    Y, D = (2 * R) ** 2 - 1, isqrt(R)
    B = 2 * D - 1
    x = {d: Y // d for d in range(D, B + 2)}
    assert x[2 * D] >= 2 * R
    original, abel, centered = defaultdict(int), defaultdict(int), defaultdict(int)
    for d in range(D, B + 1):
        original[x[d]] -= M[d]
        original[x[d + 1]] += M[d]
    abel[x[D]] -= M[D]
    abel[x[B + 1]] += M[B]
    for d in range(D + 1, B + 1):
        abel[x[d]] -= mu[d]
    centered[x[D]] -= M[D]
    centered[x[B + 1]] += M[D]
    for d in range(D + 1, B + 1):
        centered[x[d]] -= mu[d]
        centered[x[B + 1]] += mu[d]
    assert normalized(original) == normalized(abel) == normalized(centered)
    assert sum(original.values()) == 0
    coeff = normalized(original)
    band = sum(c * pi[n] for n, c in coeff.items())
    physical = []
    for p in range(x[2 * D] + 1, x[D] + 1):
        if prime[p]:
            d = Y // p
            assert D <= d <= B and p > 2 * R
            for c in range(1, d + 1):
                assert c < p and mu[p * c] == -mu[c]
                physical.append((p * c, p, c, -mu[c]))
    assert len({n for n, _, _, _ in physical}) == len(physical)
    assert sum(v for _, _, _, v in physical) == band
    physical_count += len(physical)
    total_packet = -sum(M[Y // p] for p in range(2 * R + 1, Y + 1) if prime[p])
    smooth = sum(mu[n] for n in range(1, Y + 1) if largest[n] <= 2 * R)
    complement = smooth + total_packet - band
    assert band + complement == M[Y]
    model = value(coeff, li)
    error = sub(rat(band), model)
    boundary_coeff = {x[D]: -M[D], x[B + 1]: M[B]}
    boundary = value(boundary_coeff, lambda n: sub(rat(pi[n]), li(n)))
    if error[0] > 0:
        positive.append(R)
    if error[1] < 0:
        negative.append(R)
    # Full source square, including all mixed terms, is exact in integers.
    assert band * band + complement * complement + 2 * band * complement == M[Y] ** 2
    if R == 400:
        assert M[B] == 0 and M[D] != 0
    if R in (16, 24, 25, 35, 36, 64, 65, 127, 128, 400):
        records.append({"R": R, "Y": Y, "D": D,
                        "M_D": M[D], "M_B": M[B],
                        "prime_owners": pi[x[D]] - pi[x[2 * D]],
                        "physical_occurrences": len(physical),
                        "band": band, "complement": complement, "M_Y": M[Y],
                        "E_interval": enclosure(error),
                        "omitted_boundary_interval": enclosure(boundary)})

# Independently reconstruct the exact log-hyperbola by prime factorizations:
# coefficient of log(p), not a floating-point logarithm, decides equality.
hyperbola_cases = 0
for X in (16, 31, 64, 127, 255, 1023):
    for y in sorted({1, isqrt(X), X // 3, X - 1, X}):
        coefficient = defaultdict(int)
        for d in range(1, X + 1):
            if d <= y:
                for m in range(1, X // d + 1):
                    coefficient[m] += mu[d]
        for m in range(1, X // y + 1):
            coefficient[m] += M[X // m] - M[y]
        factors = defaultdict(int)
        for m, c in coefficient.items():
            n, p = m, 2
            while p * p <= n:
                while n % p == 0:
                    factors[p] += c
                    n //= p
                p += 1
            if n > 1:
                factors[n] += c
        expected = {}
        for p in range(2, X + 1):
            if prime[p]:
                q, k = p, 0
                while q <= X:
                    k += 1
                    q *= p
                expected[p] = k
        assert normalized(factors) == expected
        hyperbola_cases += 1

budgets = []
for b in (Fraction(1, 2), Fraction(3, 4), Fraction(7, 8), Fraction(15, 16)):
    alpha = 1 / (2 - b)
    old, new = (3 + b) / 2, (1 + 3 * alpha) / 2
    delta = (1 - b * b) / (2 * (2 - b))
    assert old - new == delta and delta > 0
    budgets.append({"b": str(b), "prime_exponent": str(alpha),
                    "old": str(old), "new": str(new), "gain": str(delta)})

print(json.dumps({"root_count": len(ROOTS), "roots": ROOTS,
                  "physical_occurrences": physical_count,
                  "trial_mobius_checks": 1023,
                  "symbolic_log_hyperbola_cases": hyperbola_cases,
                  "positive_error_roots": positive,
                  "negative_error_roots": negative,
                  "interval_bits": BITS, "log_terms": LOG_TERMS,
                  "ei_terms": EI_TERMS, "records": records,
                  "exponent_checks": budgets,
                  "Lean": "NOT_RUN", "OAI_integrals": "NOT_EVALUATED"}, indent=2))
```

### Recorded Exact Output

```json
{
  "root_count": 26,
  "roots": [
    16,
    17,
    18,
    19,
    20,
    21,
    22,
    23,
    24,
    25,
    26,
    27,
    28,
    29,
    30,
    31,
    32,
    33,
    34,
    35,
    36,
    64,
    65,
    127,
    128,
    400
  ],
  "physical_occurrences": 62311,
  "trial_mobius_checks": 1023,
  "symbolic_log_hyperbola_cases": 30,
  "positive_error_roots": [
    25,
    29,
    36
  ],
  "negative_error_roots": [
    16,
    17,
    18,
    19,
    20,
    21,
    22,
    23,
    24,
    26,
    27,
    28,
    30,
    31,
    32,
    33,
    34,
    35,
    64,
    65,
    127,
    128,
    400
  ],
  "interval_bits": 180,
  "log_terms": 90,
  "ei_terms": 180,
  "records": [
    {
      "R": 16,
      "Y": 1023,
      "D": 4,
      "M_D": -1,
      "M_B": -2,
      "prime_owners": 23,
      "physical_occurrences": 118,
      "band": 33,
      "complement": -37,
      "M_Y": -4,
      "E_interval": [
        "-372781/200000",
        "-58247/31250"
      ],
      "omitted_boundary_interval": [
        "143421/62500",
        "2294737/1000000"
      ]
    },
    {
      "R": 24,
      "Y": 2303,
      "D": 4,
      "M_D": -1,
      "M_B": -2,
      "prime_owners": 44,
      "physical_occurrences": 223,
      "band": 61,
      "complement": -63,
      "M_Y": -2,
      "E_interval": [
        "-6755081/1000000",
        "-168877/25000"
      ],
      "omitted_boundary_interval": [
        "160303/500000",
        "320607/1000000"
      ]
    },
    {
      "R": 25,
      "Y": 2499,
      "D": 5,
      "M_D": -2,
      "M_B": -2,
      "prime_owners": 42,
      "physical_occurrences": 272,
      "band": 75,
      "complement": -76,
      "M_Y": -1,
      "E_interval": [
        "16937/125000",
        "135497/1000000"
      ],
      "omitted_boundary_interval": [
        "-19269/25000",
        "-770759/1000000"
      ]
    },
    {
      "R": 35,
      "Y": 4899,
      "D": 5,
      "M_D": -2,
      "M_B": -2,
      "prime_owners": 72,
      "physical_occurrences": 465,
      "band": 128,
      "complement": -109,
      "M_Y": 19,
      "E_interval": [
        "-107439/31250",
        "-3438047/1000000"
      ],
      "omitted_boundary_interval": [
        "-318031/62500",
        "-1017699/200000"
      ]
    },
    {
      "R": 36,
      "Y": 5183,
      "D": 6,
      "M_D": -1,
      "M_B": -2,
      "prime_owners": 67,
      "physical_occurrences": 529,
      "band": 109,
      "complement": -111,
      "M_Y": -2,
      "E_interval": [
        "479821/500000",
        "959643/1000000"
      ],
      "omitted_boundary_interval": [
        "6506339/1000000",
        "325317/50000"
      ]
    },
    {
      "R": 64,
      "Y": 16383,
      "D": 8,
      "M_D": -2,
      "M_B": -1,
      "prime_owners": 137,
      "physical_occurrences": 1465,
      "band": 255,
      "complement": -287,
      "M_Y": -32,
      "E_interval": [
        "-95021/12500",
        "-7601679/1000000"
      ],
      "omitted_boundary_interval": [
        "-13987591/1000000",
        "-1398759/100000"
      ]
    },
    {
      "R": 65,
      "Y": 16899,
      "D": 8,
      "M_D": -2,
      "M_B": -1,
      "prime_owners": 141,
      "physical_occurrences": 1500,
      "band": 264,
      "complement": -278,
      "M_Y": -14,
      "E_interval": [
        "-723303/125000",
        "-5786423/1000000"
      ],
      "omitted_boundary_interval": [
        "-165663/12500",
        "-13253039/1000000"
      ]
    },
    {
      "R": 127,
      "Y": 64515,
      "D": 11,
      "M_D": -2,
      "M_B": -2,
      "prime_owners": 348,
      "physical_occurrences": 5141,
      "band": 712,
      "complement": -744,
      "M_Y": -32,
      "E_interval": [
        "-629317/62500",
        "-10069071/1000000"
      ],
      "omitted_boundary_interval": [
        "-5243727/1000000",
        "-2621863/500000"
      ]
    },
    {
      "R": 128,
      "Y": 65535,
      "D": 11,
      "M_D": -2,
      "M_B": -2,
      "prime_owners": 352,
      "physical_occurrences": 5203,
      "band": 723,
      "complement": -709,
      "M_Y": 14,
      "E_interval": [
        "-1838001/200000",
        "-2297501/250000"
      ],
      "omitted_boundary_interval": [
        "-3459077/500000",
        "-6918153/1000000"
      ]
    },
    {
      "R": 400,
      "Y": 639999,
      "D": 20,
      "M_D": -3,
      "M_B": 0,
      "prime_owners": 1570,
      "physical_occurrences": 42931,
      "band": 3060,
      "complement": -3010,
      "M_Y": 50,
      "E_interval": [
        "-20149639/500000",
        "-40299277/1000000"
      ],
      "omitted_boundary_interval": [
        "-6966083/62500",
        "-111457327/1000000"
      ]
    }
  ],
  "exponent_checks": [
    {
      "b": "1/2",
      "prime_exponent": "2/3",
      "old": "7/4",
      "new": "3/2",
      "gain": "1/4"
    },
    {
      "b": "3/4",
      "prime_exponent": "4/5",
      "old": "15/8",
      "new": "17/10",
      "gain": "7/40"
    },
    {
      "b": "7/8",
      "prime_exponent": "8/9",
      "old": "31/16",
      "new": "11/6",
      "gain": "5/48"
    },
    {
      "b": "15/16",
      "prime_exponent": "16/17",
      "old": "63/32",
      "new": "65/34",
      "gain": "31/544"
    }
  ],
  "Lean": "NOT_RUN",
  "OAI_integrals": "NOT_EVALUATED"
}
```

---

## Preserved Early Checkpoint

The following checkpoint is preserved verbatim, including its then-pending status. The completed synthesis above supersedes that execution status without erasing the record.

# RH | Owner Payment - 2026-11-04

## A. Most Important Mathematical Development

**PARTIAL / IN_PROGRESS.** No new result is claimed at this checkpoint. The due SAT question is the genuine growing reciprocal-band prime error from 20261103-owner-1, equation (63). I will test an exact Abel/endpoint decomposition, keeping both endpoint anchors, all original prime occurrences, and the complete smooth/remaining-depth return. The newest source-first handoff isolates the original OAI all-selected packet: J is unselected, so J=empty has one outer tuple and no outer cross-cancellation.

Invocation: scheduled 2026-11-04 00:09 EST, America/New_York; RUN_ID_UNAVAILABLE. Checkpoint prepared 00:35 EST.

## B. Current Authoritative Objective

main: 040980c16901af749202e9b0f91211c43909404a.
AGENTS: b878d396c387a57bd0b5165fecf10d15ef3732cd.
CURRENT_PROOF_CONTRACT: 63f7553bf6e5f2a16e37808116c643dc0dcc50e1.
SOURCE_FIRST_VERSION: 2026-11-03; policy b6980c30e63bb8c9ddfc8d6fa86a2bb401707fa6.
Engine: 495fa9ee2067ccf5db9dc3c48ffaaadcd6485aa4.

Canonical actual-prime target remains OPEN:
exists C>=0, forall integers R>=2,
|pi(R^2)-VF_can(R^2)| <= C R log R.

PR #1083 is human-merged, head 1ae84e2ff019b266114c100f43016eeec71144a9, merge 040980c16901af749202e9b0f91211c43909404a. Live open/draft PR collection is empty. Exact-head CI inspection is pending in this checkpoint, not presumed from merge. Original OAI pin: 1581d4cbdd69a0faf34b2089614fe2a814316a6a.

Original sources retrieved and inspected:
- LargePrimeTerminalFlipLayers.lean: b7617df21b81002854a0d311ef7e02d9494154c3.
- SquareRootPostCrossingTail.lean: 660772bad3663d14c0f3390e26925b57d1390080.
- VF919OriginalLowTupleSignedGram.lean: c1b7b46a9e62a5b2f3729618c4dd24e31558166f.
- OAI LowSlotPolynomial.lean: b1dcb5a1e51afad1d39ccd91fa58a764e39629ba.
- OAI LowSlotSplit.lean: 8c8fe01a1b3fffe3b06839c2befc2ddae39a2c9b.

## C. Continuity And Selected Hypothesis

TODAY=PENDING for upstream reports: November 4 directory returned 404 at intake.
YESTERDAY=CARRY_FORWARD from agent-reports 9ae0ffc891087365ed088a35fbbe09e4afe0af18. Retrieved all seven November 3 role reports and external inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 (no entry later than October 18).

Resumed SAT carrier:
Y=(2R)^2-1; D=floor(sqrt R);
E_R=-sum_(D<=d<2D) M(d)[N_(2R)(d)-Li_2(floor(Y/d))+Li_2(floor(Y/(d+1)))].
Its inherited crude bound is R^((3+b)/2) for |M(n)|<=C n^b, b<1.
A possible new restriction must improve this on the actual growing band without deleting endpoint or historical terms.

Protected sequence carried forward: SAT / VF-LOW / JOH on November 3; this turn is SAT. Next distinct route: VF-LOW. The source-first bridge is a cross-source audit, not permission to reset this rotation. Coordinator 20261103-coordinator-3 specifically preserves this SAT continuation.

Carry-forward findings: Owner-1 zero-layer 0->5 at R=7; Owner-2 squareful prime-ancestor capacity obstruction; Owner-3 adjacent excursion payment refuted at roots 12/35. Referee-9/10 and Lean-3 qualify moving nonempty LOW mass on original untilted geometry; empty packet remains unpaid. Coordinator C38-C39 positive selected-support density is SELF_AUDIT, not an inverse-row lower bound. No Mobius/Hecke source identification is assumed.

## D. Derivation And Falsification Plan

Compare exact summation by parts with centered endpoint differences and source-faithful prime/cofactor reindexing. Test legal small and held-out roots, zero Mertens endpoint coefficients, root truncation, squareful cofactors, and all return terms. Any numerical Li decisions will use certified arithmetic or be explicitly non-rigorous diagnostics. Synthetic signs will not stand in for genuine Mobius coefficients.

## E-K. Pending Research And Publication

Substantive derivation, quantitative consequence, circularity review, competing mechanisms, precise specialist handoffs and final resume capsule are PENDING and will be appended in this same report. Review is SELF_AUDIT unless independently published evidence is obtained. No local Lean, proof/source modification, other-report edit, agent launch, schedule change, PR mutation or merge is authorized or performed.

Existing one-shot strict-slot endpoint credit is inherited only; additional signed-LOW gate SEARCH_BROAD; net new endpoint gain UNKNOWN. Source-faithful complete return remains mandatory.

---

## Verified Publication Receipt - 2026-11-04 00:47 EST

The completed synthesis, claim 20261104-owner-1/S1-S5, full executed verifier, exact output and preserved early checkpoint were published in commit **fe552dad704e6a4014103ef64e56cd3ee7c97181**, report blob **9560bd392e13c2d5bf0990f94876de126df62906**. Fetching the report at that commit returned all **53,246 characters**, exactly matching the submitted bytes. Commit inspection confirmed exactly one changed file: this authorized Owner report.

The early checkpoint is retained verbatim in its historical section. Report checks found all A-K sections, balanced code fences and ASCII text; the verifier and its syntax check passed. These checks are not independent mathematical review or Lean certification.

Closing main refresh still returned **040980c16901af749202e9b0f91211c43909404a**. The latest November 4 directory check contained only this Owner report, so upstream **TODAY=PENDING; YESTERDAY=CARRY_FORWARD** remains the observed state, not an assumed agent failure. Immediately before this receipt update the live report blob/content matched the verified substantive version.

**Execution: COMPLETE. Publication: substantive commit verified.** S2/S3 remain PAPER_PROOF / SELF_AUDIT; independent Referee and Lean review PENDING. New complete-endpoint gain: NONE. Next protected Owner route: VF-LOW. This receipt's own commit/readback is checked after writing, not presupposed.

---

## Scheduled VF-LOW Continuation Checkpoint - 2026-11-04 08:09 EST Invocation

### A. Most Important Mathematical Development

Execution **IN_PROGRESS / PARTIAL**. No new theorem is asserted at this checkpoint. The selected falsifiable repair of yesterday's ancestry-capacity mechanism is: does restricting to genuine **squarefree** composite seats restore a once-only prime-divisor payment? Yesterday's O4 counterexample was squareful; it does not by itself answer that restricted question. I will test distinct squarefree divisor products with their actual VF weights, not replace those weights by Mobius signs.

### B. Authority And Continuity

Actual trigger: scheduled 2026-11-04T08:09:02-05:00; platform identifier RUN_ID_UNAVAILABLE. Local continuation label: **20261104-owner-2**. Checkpoint prepared 08:15 EST. Latest actual main: **040980c16901af749202e9b0f91211c43909404a**; AGENTS blob **b878d396c387a57bd0b5165fecf10d15ef3732cd**; proof contract **63f7553bf6e5f2a16e37808116c643dc0dcc50e1**; SOURCE_FIRST_VERSION=2026-11-03, source-first policy **b6980c30e63bb8c9ddfc8d6fa86a2bb401707fa6**.

Both November 3 and November 4 named handoff sets were retrieved at reporting snapshot **bcf9cda3a2060405d46555ef048f3007cbcc1213**, with applicable current findings and continuation sections read. TODAY=AVAILABLE for all roles; YESTERDAY=CARRY_FORWARD where referenced. External inbox **038018145c0fddb2f6306c0712373adf9cd1ea52** has no post-October-18 entry. No absent execution is inferred.

Protected rotation: Nov 3 VF-LOW owner-2, Nov 3 JOH owner-3, Nov 4 SAT owner-1; **VF-LOW is due**. Resume O1-O5/(66)-(74), respecting the existing squareful 118-seat obstruction and complete historical restoration. Coordinator **20261104-coordinator-1/C41-C43**, today Referee counting-versus-inverse distinction, and the accepted moving-mass/empty-J reduction are continuity constraints, not new quantitative suppliers.

Live PR list is empty. #1083 is **MERGED**, head **1ae84e2ff019b266114c100f43016eeec71144a9**, merge **040980c16901af749202e9b0f91211c43909404a**. All 14 returned head-associated check runs are successful. Literal Gram source blob **c1b7b46a9e62a5b2f3729618c4dd24e31558166f** and gain-ledger blob **5e7cea836158fc819f37e71da5fe55c8a8dce44e** were inspected on main. No new local Lean or CI execution is claimed.

### C. Structural Hypothesis And Preregistered Test

Compare: (1) squarefreeness rescues prime-divisor capacity; (2) many distinct subset products overload even the enlarged one-unit-per-prime ancestry budget. Construct squarefree odd cofactors from a finite set of distinct genuine primes, place them with a new greatest prime q inside the exact open-square run, and verify every actual occurrence, factor, owner, historical location, and weight. Reject (1) only if the genuine weighted demand exceeds even the enlarged capacity. Seek an all-scale construction as well as the smallest useful reproducible exact witness. No first-bad hypothesis is asserted by such a witness.

The source-qualified owner-to-OAI comparison remains limited: original LowSlotPolynomial/LowTupleGram and LowSelectedSum were retrieved at openai/math **1581d4cbdd69a0faf34b2089614fe2a814316a6a**, blobs **b1dcb5a1e51afad1d39ccd91fa58a764e39629ba**, **710598c8bef4d1a1ec98aa7e68b00369962c3d17**, **a54eb9ec6a5beb0db57ce9baa658718aab808af1**. J is unselected; the binding J=empty outer carrier is a singleton. A many-seat bijection to that outer carrier is impossible; any useful bridge must enter the actual selected inverse sum with its Hecke phase and divisor marks. No such weight-preserving map or signed gain is assumed.

### D-K. Pending Research

Derive the precise squarefree construction or falsifier, restore the full signed complement and every quadratic cross term, inspect relevant active-carrier conditions without inferring returned-mask admission, classify quantitative relevance, and append specialist handoffs plus a resume capsule. Canonical VF and RH remain OPEN; additional signed-LOW eta remains SEARCH_BROAD. Publication is established only after commit/readback. Only this own dated report is authorized for remote modification.

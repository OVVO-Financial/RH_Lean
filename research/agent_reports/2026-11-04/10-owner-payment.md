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


---

## Scheduled VF-LOW Final Synthesis - Claim 20261104-owner-2

### A. Most Important Mathematical Development

**Squarefreeness does not repair the once-only ancestry-payment mechanism. Nor does restricting to factor depth three.** There are genuine squarefree odd seats, each the product of exactly three distinct primes and each inside the original processed squarefree carrier of its own square block, whose total VF weight exceeds every available historical prime-divisor charge even if each ancestor is generously given one full unit.

The explicit witness has **435 distinct physical seats and 31 distinct prime ancestors**. At q=490001 its actual positive demand lies in **[33.59618270,33.59618271]**, versus actual historical negative capacity **[21.26725110,21.26725111]**. The much more generous capacity 31 already fails: an elementary exact bound gives demand **>3132/95**, exceeding 31 by **187/95**. Deleting any six of these seats still leaves demand **>31+719/475**.

More strongly, SF3 gives an infinite fixed-depth construction. With k=2^t, t>=11, demand divided by even the enlarged ancestry capacity is greater than

~~~text
k(k-1) / [(k+1) 4t(4t+1)] -> infinity.
~~~

Along these constructed scales the required congestion is at least a constant times q^(1/4)/(log q)^2. The construction uses an elementary central-binomial prime count and Bertrand's postulate, not PNT, random signs, a fitted exponent, or the desired VF estimate.

**Classification:** SF1-SF4 are PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING; the specified squarefree bounded-capacity supplier is REFUTED; SF2's numerical certificates are FINITE_COMPUTATION. SF5 is exact source restoration, not a new cancellation theorem. No new Lean theorem, global upper bound, first-bad counterexample, or endpoint gain is claimed.

This is a substantive strengthening of **20261103-owner-2/O4**, whose explicit obstruction was squareful with unbounded factor depth. That result remains valid and unchanged. The new obstruction survives the squarefree-active restriction, has constant depth three, and includes only actual negative historical prime seats. It does not use the exceptional prime-3 anchor or positive VF charges of primes 5 and 7.

Actual invocation: scheduled **2026-11-04T08:09:02-05:00**, RUN_ID_UNAVAILABLE. The early checkpoint and this synthesis belong to the same invocation. Protected route: **VF-LOW**; next distinct route: **JOH**. Additional signed-LOW gate remains **SEARCH_BROAD**.

### B. Current Authoritative Objective

Main was refreshed at intake and again during closeout and remains **040980c16901af749202e9b0f91211c43909404a**. Main AGENTS blob is **b878d396c387a57bd0b5165fecf10d15ef3732cd**; proof contract **63f7553bf6e5f2a16e37808116c643dc0dcc50e1**; source-first policy **b6980c30e63bb8c9ddfc8d6fa86a2bb401707fa6**; research engine **495fa9ee2067ccf5db9dc3c48ffaaadcd6485aa4**. Current policies, not older one/day or frozen PR prose, govern this run.

The original actual-prime objective remains

~~~text
exists C>=0, forall integer R>=2:
  |pi(R^2)-F_R-sqrt(2)| <= C R log R,
F_R=sum_(2<=r<R) (2r+1)/log(r^2+r+1/2).
~~~

It is OPEN. Put D_R=pi(R^2)-F_R. The canonical phase is retained: D_can(R)=D_R-sqrt(2), so D_can(R)^2=D_R^2-2sqrt(2)D_R+2. The von Koch consumer still has its explicit classical-criterion interface.

The literal source examined here is

~~~text
C(A,B)={(r,n): A<=r<B, r^2<n<(r+1)^2, n odd},
w_r=(2+1/r)/log(r^2+r+1/2),
c(r,n)=w_r-1_Prime(n).
~~~

Its exact signed sum is D_A-D_B. The coefficients are NOT mu(n). In particular all new selected n have mu(n)=-1 but physical VF charge +w_r.

Material original sources were fetched at the main SHA, including their proofs and relevant hypotheses:

| File | Blob SHA |
| --- | --- |
| research/VF_MID_VON_KOCH_BRIDGE.lean | 32d4b0d74ecadc9780b9841d40357f6ff02369f0 |
| research/VF_MID_ODD_FRACTIONAL_CLUSTER.lean | 942badff45c03d2a9e97789b57d1bd8052232191 |
| research/VF_MID_SIGNED_SEAT_CHARGE.lean | 87a6654a4a4337b409fde69aa15d7264d8b721b6 |
| research/VF_MID_FIRST_BAD_AFFINE_OWNER_SPLICE.lean | 29953ea50b87868e6462ab6d885af03c1d6ec42a |
| research/VF_MID_ONE_BLOCK_SOURCE_TO_RANK_INLET.lean | dd4ff316e51501a3ca9404e0c2c3e754f154ac6e |
| research/VF_MID_PHI_CUTOFF_TELESCOPE.lean | 0490b63a8752c13e3552a3ea8ed1eba36579c927 |
| research/VF_MID_FIRST_BAD_WEIGHTED_OWNER_FUBINI.lean | 4679d7edae521dd4d9f0238aa4201445b1fdb9a9 |
| research/VF_MID_FIRST_BAD_HISTORY_COMPRESSION.lean | d9cc97541f9713b6eec8df30885e9ca830478e59 |
| research/VF_MID_915_EXACT_HISTORICAL_NNS_COMPRESSION.lean | 6cc6b2a9d25279dd44fb65cb222f5d6846a912d4 |
| research/VF_MID_FIRST_BAD_RESTORING_DECOMPOSITION.lean | 41ca385cb2bd0706db21007e19cd2b0b1aaa4b3e |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |
| research/oai_434/VF919OriginalLowTupleSignedGram.lean | c1b7b46a9e62a5b2f3729618c4dd24e31558166f |
| research/oai_434/VF919OriginalGainComponentLedger.lean | 5e7cea836158fc819f37e71da5fe55c8a8dce44e |

The actual active-carrier admission used below is from **vfMidSquarefreeProcessedOwnerSites**, **vfMidFrozenProcessedOwnerPrimes**, **vfMidOneBlockProcessedSquarefreePhysicalCarrier**, and the original least-owner cutoff theorem. It is admission to the processed physical carrier at EACH original root. It is not admission to a chosen returned child/signature/mask or a hypothetical first-bad packet.

### C. Structural Hypothesis Investigated

Resume point: **20261103-owner-2/O1-O5, equations (66)-(74)**, and Coordinator **20261104-coordinator-1**, section H. The question was whether the squareful obstruction could be avoided by restricting the proposed divisor-only resource to squarefree processed seats, possibly of bounded depth, after removing an already-paid short logarithmic packet.

Three competing possibilities were compared:

1. Squarefreeness eliminates the overload because a prime cannot recur within a cofactor. SF2-SF3 refute this: different squarefree cofactors share the same small set of genuine primes.
2. A fixed factor-depth cutoff repairs the resource. SF3 refutes this already at exactly three distinct prime factors, without an asymptotic-depth limit.
3. A source-qualified non-divisor interaction or a genuinely joint signed estimate can compensate the family. This remains possible; no such complete theorem is established here. The obstruction does not forbid compensation from the original complement.

The first two are materially stricter repairs than the already-refuted unrestricted O4 claim. Repeating the old squareful witness alone would not decide them. The initial finite design used distinct prime subset products; the derivation strengthened it to products of exactly TWO distinct small primes followed by one new greatest prime.

### D. Mathematical Derivation

#### SF1. Exact Placement, Ownership, And Weight Lemma

Let q>=11 be an odd prime and let S be a finite set of distinct odd primes, all less than q. Let F be a set of distinct products

~~~text
n=q*p*s,  p,s in S, p<s,  q/4 < p*s < q.
A=(q-1)/2, B=q-1, r(n)=floor(sqrt n).
~~~

Then every n is an odd, squarefree composite of depth three, with greatest prime q and least prime p. There are no repeated occurrences: unique factorization recovers {p,s} from n/q.

Because p*s>q/4,

~~~text
n>q^2/4>A^2.
~~~

Because p*s and q are odd and p*s<q, p*s<=q-2, whence

~~~text
n<=q(q-2)<(q-1)^2=B^2.
~~~

The q-adic valuation of n is exactly one, so n is not a square. Therefore

~~~text
A<=r(n)<B,  r(n)^2<n<(r(n)+1)^2.                       (SF1a)
~~~

All ancestors are historical: q<A^2 for q>=11, and p,s<q. Also p<=sqrt(p*s)<sqrt(q)<A<=r(n). Thus p belongs to the original frozen processed-owner set even at cutoff A, and n belongs to the squarefree processed-owner fiber at its actual root. The exact source definitions make this an original-carrier statement, not mere prime eligibility. It still says nothing about later clipped/returned source masks.

For fixed q, two distinct odd multiples differ by at least 2q. Every block here has width 2r+1<2q. Hence at most one selected seat lies at each root. Finally,

~~~text
0<log(r^2+r+1/2)<2log q,  2+1/r>2,
w_r > 1/log q.                                         (SF1b)
~~~

Every selected term keeps its literal VF weight. No descendant replaces its parent weight, and no historical prime is cloned.

#### SF2. Explicit Squarefree Counterexample

Let S be ALL primes in [500,700], explicitly

~~~text
503,509,521,523,541,547,557,563,569,571,
577,587,593,599,601,607,613,617,619,631,
641,643,647,653,659,661,673,677,683,691.
~~~

Take q=490001 and all 435 unordered pairs p<s from S. Exact trial division certifies every listed prime and q. Independently, an integer smallest-prime-factor sieve and a scan through the full cofactor interval reconstruct the same 435 products.

Their cofactors range from 256027 to 471953. Thus q/4<p*s<q. SF1 applies with

~~~text
A=245000, B=490000,
354194<=r(n)<=480892,
#F=435, #primeDivisors(F)=31.
~~~

There are 29 actual least-prime owner labels, 435 distinct root locations, no squareful seat, and no strict-square-boundary omission. The final production root is R=B-1=489999 and R/2+1=A, so these are genuine seats in the original final half-history run, not a distant model population. No first-bad premise is claimed.

Since q<2^19 and

~~~text
log 2 = 2 sum_(j>=0) (1/3)^(2j+1)/(2j+1)
      < 2/3 + (2/3)*(1/27)/(1-1/9) = 25/36,
~~~

SF1 gives w_r>36/475 and consequently

~~~text
X:=sum_(n in F)w_(r(n)) >435*(36/475)=3132/95>31.       (SF2a)
~~~

For every historical ancestor a in Q=S union {q}, its actual negative capacity is y_a=1-w_(floor(sqrt a)). Here 0<y_a<1. Therefore Y=sum_Q y_a<31 and X-Y>187/95, even before using the sharper rational intervals.

Suppose nonnegative allocations x_(n,a) are permitted only when a is a prime divisor of n, must satisfy sum_a x_(n,a)>=w_(r(n)), and may spend each historical ancestor at most once. Even enlarging every capacity to 1 yields

~~~text
X <= sum_n sum_(a|n) x_(n,a)
   = sum_(a in Q) sum_(n:a|n) x_(n,a) <=31,
~~~

contradicting SF2a. The original actual capacities are smaller, so they cannot rescue this supplier.

**Residual after one short packet.** Every root in [A,B) is below 2^19, so the O1 horizon floor(log_2(root)/3) is at most 6. SF1 allows at most one selected n per root. Removing ANY six seats, in particular those removed by any single O1-eligible short subrun within this run, leaves

~~~text
X_remaining >429*(36/475)=31+719/475.                  (SF2b)
~~~

This even re-grants the entire 31-unit ancestor capacity to the residual. In an actual sequential payment some of that history has already been spent, so the real residual resource is no larger. This does not refute O1, whose own restricted packet remains valid.

#### SF3. Infinite Constant-Depth Overload

For every integer t>=11 put k=2^t. There exist k distinct primes in (k,k^2]. Here is a self-contained elementary count, avoiding an imported short-interval/PNT estimate.

For even N, the central binomial coefficient satisfies

~~~text
2^N/(N+1) <= binom(N,N/2) <= N^pi(N).
~~~

The first inequality follows because the central term is the maximum of N+1 nonnegative binomial coefficients summing to 2^N. For the second, for each prime a the factorial valuation formula gives

~~~text
v_a binom(N,N/2)
 =sum_(j>=1)[floor(N/a^j)-2floor((N/2)/a^j)]
 <=floor(log_a N),
~~~

because every bracket is 0 or 1. Thus each prime-power contribution is at most N. Taking logarithms at N=k^2=2^(2t) gives

~~~text
pi(k^2) >= [k^2-(2t+1)]/(2t) >=2k                    (t>=5).
~~~

The final elementary inequality is k^2-(2t+1)>=4tk. It holds at t=5; if f(t)=2^(2t)-(2t+1)-4t*2^t, then f(t+1)-4f(t)=8(t-1)2^t+6t+1>0, proving it for all later t. Since pi(k)<=k, at least k primes lie in (k,k^2]. Select any k of them as S.

There are k(k-1)/2 distinct unordered semiprime products p*s, all in (2^(2t),2^(4t)). Partition them into the 2t dyadic bins [2^j,2^(j+1)), 2t<=j<4t. One bin contains N_t>=k(k-1)/(4t) products. By Bertrand's postulate choose a prime

~~~text
2^(j+1)<q<2^(j+2).
~~~

The upper endpoint is a composite power of two, so the usual non-strict upper bound is strict here. In particular every small prime is below q and

~~~text
q/4 < p*s <q,
2k^2<q<2k^4.
~~~

Apply SF1 to all products in that bin. Its population has at most k+1 distinct ancestors. Since log q<(4t+1)log 2<4t+1,

~~~text
X_t > N_t/(4t+1)
    >= k(k-1)/[4t(4t+1)].                            (SF3a)
~~~

Therefore

~~~text
X_t/#Q_t >= X_t/(k+1)
 > k(k-1)/[(k+1)4t(4t+1)] -> infinity.               (SF3b)
~~~

This lower bound exceeds 1 for every t>=11: k(k-1)/(k+1)>k-2 and 2^t-2>4t(4t+1) starts at t=11 and persists by induction. Consequently no fixed per-ancestor congestion constant can fund all these genuine squarefree depth-three populations.

A useful scale version follows without a fitted exponent. For k>=4,

~~~text
X_t/#Q_t > k/(40t^2)
          > (q/2)^(1/4) / [10(log_2 q)^2].            (SF3c)
~~~

Indeed 4t(4t+1)<=20t^2, k(k-1)/(k+1)>=k/2, q<2k^4, and q>2k^2 implies t<(log_2 q)/2. This is a lower bound on the resource congestion along the constructed unbounded prime scales. It is NOT a lower bound on the complete signed endpoint defect.

**Imported theorem and exact source:** the only nontrivial external existence input is Bertrand's postulate, stated and proved as Nat.exists_prime_lt_and_le_two_mul in [the pinned Mathlib file](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/NumberTheory/Bertrand.lean), blob **25029ababf90aa3d54a7b483c01bb6c0c4ddb9aa**. That Mathlib revision was read from main lake-manifest.json. Its input is a nonzero natural n and conclusion n<p<=2n; here n=2^(j+1). No parameter-uniformity or new analytic bound is assumed. The present combined proof has NOT been compiled in Lean.

#### SF4. Necessary Non-Divisor Contribution

Suppose a proposed nonnegative payment of these same seats is enlarged to allow other resources, but all prime-divisor history together still has total capacity <=#Q_t. Summing the original demands shows that payment not drawn from that ancestry must contribute at least

~~~text
ExternalPayment >= X_t-#Q_t,
ExternalPayment/X_t
 > 1-[(k+1)4t(4t+1)]/[k(k-1)] ->1.                  (SF4)
~~~

This is an inverse restriction on any such payment design: on this family, almost all demand eventually needs a different resource. It does not assert that the external resource exists, is negative, or is admitted to the original returned source. Collective signed compensation need not be representable as nonnegative allocations at all; SF4 does not prohibit it.

#### SF5. Complete Original Signed And Quadratic Return

Define Q as the ACTUAL prime-divisor union of F, X=sum_F w_r, and Y=sum_Q(1-w_(floor(sqrt a))). For our examples and the SF3 construction these historical charges are genuinely negative. Let Z be the signed charge of EVERY current seat in C(A,B) outside F, with actual primes, other squarefree composites, squareful composites and all original open-square conventions retained.

Put

~~~text
P=X-Y,
C=-D_A+Y+Z.
-D_B=C+P.                                             (SF5a)
~~~

C is not an invented residual with an assumed bound. Because every a in Q is historical before A, it is exactly the initial anchor -D_2=-2, every historical odd seat before A OTHER THAN those primes Q, and the complete current complement Z. Adding Y removes each selected historical negative occurrence once. All current F occurrences and all historical Q occurrences are disjoint.

The complete square is

~~~text
D_B^2=C^2+P^2+2CP,
P^2=X^2+Y^2-2XY.                                    (SF5b)
~~~

X^2 retains all 435 diagonal terms and every cross-owner/cross-root term; Y^2 retains all historical diagonal and cross-prime terms; -2XY retains EVERY historical/current interaction. There is no decomposition into independent owner squares. Positive P does not imply positive -D_B because the original C may compensate it.

At the actual final root R=B-1, preserve

~~~text
Source=D_B=D_R+P_R-m_R,
beta_R=m_R+(1-2w_R)P_R,
TotalMass=(|D_R|+beta_R)^2.
~~~

If all original history is decompressed into upper/lower masses U,V, its exact existing price remains

~~~text
(U+V+beta_R)^2-(|U-V|+beta_R)^2
 =4UV+2beta_R(U+V-|U-V|).                            (SF5c)
~~~

These are the compiled historical/NNS identities cited in B, not newly invented payment capacity. No conclusion about 2D_B^2-TotalMass follows from SF2-SF4. No full endpoint prime census up to B^2 was executed or claimed.

### E. Quantitative Consequence

The independent quantitative result is an **ancestry-resource lower bound**, not an improved global upper estimate: fixed-depth squarefree populations require unbounded, indeed at least q^(1/4)/log^2(q)-order, congestion along the constructed scales if payment is confined to prime-divisor history. The exact 435-seat witness rejects unit capacity, and the residual survives one original short-logarithmic packet.

Thus the old squareful-only objection cannot be repaired merely by discarding squareful restoration, imposing bounded factor depth, invoking distinct factors, or using each prime ancestor once. Any proposed global repair must have genuinely new source information.

The original canonical VF bound, full #915 payment, global signed LOW improvement and RH receive **no new upper bound**. Net endpoint gain: **UNKNOWN / NONE ESTABLISHED**. The inherited reviewed one-shot strict-slot result keeps its prior formal scope; this run does not count it as a renewed gain.

### F. Falsification And Circularity Review

The strongest positive claim tested was the squarefree fixed-depth ancestry-capacity repair. Its exact hypotheses are refuted by SF2, not by synthetic signs. Every n is a legal original integer with all factors and original weights preserved.

| q | A,B | Demand X | Actual ancestor capacity Y | Signed packet X-Y |
| ---: | --- | --- | --- | --- |
| 490001 | 245000,490000 | [33.59618270,33.59618271] | [21.26725110,21.26725111] | [12.32893159,12.32893160] |
| 500009 | 250004,500008 | [33.56997131,33.56997132] | [21.26748363,21.26748364] | [12.30248767,12.30248769] |
| 1000003 | 500001,1000002 | [32.69548954,32.69548955] | [21.27516333,21.27516334] | [11.42032620,11.42032621] |

All three have exactly the same 435 distinct cofactor products, 31 ancestor primes, 29 first owners and squarefree depth three. The first witness is not claimed minimal. The other two are held-out location/weight tests, not a fitted asymptotic sample.

Primality was checked by trial division and an independently structured smallest-factor sieve. Each cofactor family was independently reconstructed by scanning the whole exact cofactor interval. Logarithms were certified with rational range reduction x=2^h y, 1<=y<2, and 24 terms of 2sum u^(2j+1)/(2j+1), u=(y-1)/(y+1). The remaining tail is bounded by 2u^(49)/(49(1-u^2)). Each weight interval is rounded outward to a common denominator 10^12 before aggregation; displayed eight-place intervals are again rounded outward. There are no floating-point sign decisions.

Additional executed checks: 100 small central-binomial cases with every prime valuation, 46 exact power-parameter cases t=5..50, 400 signed-restoration substitutions, and 125 original-compression substitutions. Those finite substitutions are sanity checks; the all-scale proofs are the derivations above. A repeated small-prime factor is rejected as squareful. At q=2000003 the unchanged cofactor pool fails SF1 admission, so it is explicitly NOT a valid same-family counterexample.

**Correction history within this run:** the first script demanded that a coarse uniform lower bound prove six-seat-deletion overload at every held-out q. At q=1000003 that coarse lower bound is insufficient (-14/125 surplus), although the actual statement survives. The final script instead verifies the stronger certified actual-weight deletion bound, which is positive (>1.2386 there). SF2b's purely rational six-seat bound is asserted for q=490001 (and also holds for 500009), not silently universalized. The final horizon uses the largest permitted O1 horizon anywhere in [A,B), namely 6, not only the starting-root horizon 5. The full final verifier was rerun successfully after both adjustments.

**No circularity:** SF3 uses no Mertens/VF/LOW target bound. Squarefreeness and mu=-1 are true factorization facts but never substituted for w_r. The ancestry budget is deliberately enlarged, making the contradiction stronger. The current complement, full quadratic interactions, final mask admission, first-bad conditioning, and canonical phase remain explicit.

**Novelty check:** relevant main ancestry/congestion notes and the retrieved November 3/4 reports were searched. CANONICAL_ANCESTRY_WEIGHTED_CONGESTION.md, blob **e8d9b0d1a61cadc1bf72a93554bad13f4a01baa0**, treats a different saturated q<R carrier and a q^-2-weighted resource; this result does NOT refute that reciprocal theorem. Yesterday's squareful O4, the short-horizon O1/O2 theorem, and today’s ideal-counting lower bounds remain distinct. No exhaustive claim of historical novelty beyond this checked continuation is made.

### G. Conceptual Interpretation

The overload does not come from repetitions of a prime within one integer. It comes from many distinct two-prime cofactors reusing the same finite ancestry pool across different physical integers. Bounded factor depth controls the number of ancestors of ONE seat, but not the aggregate weighted demand served by those ancestors.

The first-owner map is genuinely unique and all selected roots are distinct. Those facts coexist with severe once-only historical congestion. In particular, a unique owner or an injective per-block occurrence map cannot supply the missing global resource bound by itself.

The original global system may compensate this positive proper-class packet through non-divisor primes, other historical/current terms, or a joint signed identity. SF5 is the exact place those possibilities remain. The right conclusion is to retire this repaired divisor-payment supplier, not the entire VF-LOW architecture.

### H. Competing Mechanisms

| Mechanism | Established / missing input | Disposition |
| --- | --- | --- |
| Squarefree or fixed-depth repair of once-only prime-divisor payment | SF2-SF3 give legal depth-three counterexamples and unbounded congestion | ABANDON this unconditional supplier |
| One O1 short packet followed by the same ancestor budget on the residual | SF2b survives even after re-granting all history; repeated q credit is not new capacity | REJECT this residual repair; retain O1 at its true local scope |
| New non-divisor or collective signed original-source interaction | SF4 gives a necessary resource scale; actual occurrence/weight/mask map and signed estimate are still absent | CONTINUE only with a concrete new source relation |
| Native source relabeled as the OAI outer LOW tuples | Already blocked by binding J=empty singleton; actual selected inverse is a different carrier | Do not reopen the completed outer-bijection question; selected-source bridge remains unproved |

This preserves the current broad programme. It does not duplicate the Analytic all-selected inverse estimate or Wheel’s due FINITE-AC work.

### I. Specialist Handoffs

**Coordinator:** register **20261104-owner-2/SF1-SF4** as self-audited paper results, with a new fixed-depth squarefree refinement of O4, not a global upper-bound advance. The strategic point is that squareful restoration is no longer the only obstruction to once-only ancestry funding. Preserve C41-C43 and route rotation; JOH is next.

**Adversarial Referee:** independently check the central-binomial count, the 2t-bin pigeonhole, Bertrand endpoints, original processed-carrier membership, the congestion factor in SF3c, and the full return SF5. Verify that the finite q=490001 family has 435 seats and 31 ancestors, and that removing any six still exceeds 31. Review scope before any formalization; author's review is SELF_AUDIT.

**Prime Census:** smallest decisive reproduction is the single q=490001/S=[500,700] prime family with exact factorization and rational logs. Null is X<=31, falsifier is X>31; exact elementary gap is 187/95. The held-out q=1000003 requires the certified weight bound for deletion, not the coarse lower bound. No endpoint sieve to q^2, bigger range, or exponent fit is requested.

**Finite Wheel:** a bounded-degree or squarefree ancestry graph can still have this large weighted neighborhood deficit. Check a proposed repair against SF3 before exporting an owner multiplicity cap. Your q^-2 daughter resources and finite-A/C source are different; retain their original weights and complements.

**Analytic Type II:** these are original VF prime-indicator coefficients, even though all selected integers have mu=-1. No transfer to a Mobius shell or Hecke inverse follows. A new signed analytic packet would need to include C in SF5 or exhibit a proved smaller independently useful source comparison. Today’s ambient cube-count energy cannot be substituted for this physical history.

**Lean Verification:** no new proof branch is requested before independent acceptance and utility selection. If qualified, SF1 plus the fixed 435-seat certificate is an implementation-sized finite source lemma; the all-scale SF3 additionally needs the elementary binomial prime-count argument and the existing Bertrand theorem. Do not encode an unknown payment inequality as a hypothesis and call it proved. Keep your independently qualified moving-mass task separate.

These are asynchronous report handoffs only. No specialist was launched, and no claim of independent review or formalization is made.

### J. First Independently Missing Lemma

The precise supplier tested here was the squarefree depth-three neighborhood inequality

~~~text
forall legal F in C(A,B), supported on squarefree depth-three seats:
  sum_F w_r <= sum_(a in primeDivisors(F)) availableHistoricalCredit(a),
~~~

even with one unit per ancestor, and even after one short-log packet. It is **REFUTED**, not an open theorem to keep attempting.

**No qualified independent replacement quantitative supplier was obtained.** For a proposed non-divisor resource, the first missing step is its actual occurrence/weight/admission identity and once-only allocation, with SF4's necessary external contribution. A bound for C+P at canonical size would simply restate the original target; it is NOT presented as a smaller last lemma.

The next protected JOH turn has an already well-posed smaller arithmetic question from **20261103-owner-3/JH9-JH10**, which is carried forward without rederiving it. Let b_j be consecutive genuine floor-Li arrivals; select EVEN j for which b_j,b_(j+1) are composite and the interior contains exactly two primes p_j<q_j. These closed slots are disjoint. Seek an independent signed restriction, or a precise falsifier, for

~~~text
W(X)=sum_(selected slots contained in [X,2X])
       [b_j+b_(j+1)-p_j-q_j].
~~~

No favorable sign or power bound is asserted. All other events, the historical anchor and terminal return must be restored before a JOH endpoint claim. This is the exact next source-level question, not a renamed canonical bound.

### K. Next-Run Resume Capsule

~~~text
RUN: scheduled 2026-11-04 08:09:02 EST (-0500); RUN_ID_UNAVAILABLE.
LOCAL LABEL / CLAIM: 20261104-owner-2, SF1-SF5.
MAIN: 040980c16901af749202e9b0f91211c43909404a, refreshed unchanged.
SOURCE_FIRST_VERSION: 2026-11-03.
POLICY: b6980c30e63bb8c9ddfc8d6fa86a2bb401707fa6.
ENGINE: 495fa9ee2067ccf5db9dc3c48ffaaadcd6485aa4.
PRIMARY: VF-LOW, literal w_r-1_Prime(n), all original square boundaries.
NEW RESULT: squarefree depth-three once-only ancestry capacity is refuted;
            all-scale lower congestion and external-resource inverse.
EXPLICIT: q490001, 435 seats, 31 ancestors, X>3132/95>31;
          any six-seat deletion still X>31+719/475.
GENERAL: k=2^t, t>=11, X/(k+1)>k(k-1)/[(k+1)4t(4t+1)].
FULL RETURN: -D_B=(-D_A+Y+Z)+(X-Y); retain complete square and NNS price.
STATUS: PAPER_PROOF / SELF_AUDIT; FINITE_COMPUTATION; supplier REFUTED.
REVIEW / FORMAL: independent review PENDING; NOT_FORMALIZED.
FIRST GAP: no qualified non-divisor or complete signed replacement;
           do not relabel canonical-sized C+P control as an elementary lemma.
LAST ROUTES: JOH (Nov3 owner-3), SAT (Nov4 owner-1), VF-LOW (this run).
NEXT DISTINCT ROUTE: JOH, original selected even-slot midpoint W(X).
SAT RESUME: OPEN-SAT-I plus actual anchor/model/complement; C43 retained.
VF RESUME: SF3, not squareful-only O4; masks/first-bad conditional scope unpaid.
ETA: SEARCH_BROAD for additional signed LOW; no new net endpoint gain.
DEPLOYMENT_ACK: current policy consumed, protected VF-LOW ticket executed,
                literal original sources inspected and a new falsifier proved.
~~~

#### Source-First Comparison And Formal Evidence

The latest source-first correction is reused, not claimed as new mathematics: **J is unselected**, and the binding all-selected J=empty outer tuple is a singleton. Today’s own SAT report already gave a legal multiple-native-occurrence obstruction to an outer-atom injection. This run does not repeat that claim as novelty.

Original openai/math pin: **1581d4cbdd69a0faf34b2089614fe2a814316a6a**. Freshly inspected original files:

| Original file under lean/OAI/NumberTheory/DirichletL/ | Blob |
| --- | --- |
| Detector/LowSlotPolynomial.lean | b1dcb5a1e51afad1d39ccd91fa58a764e39629ba |
| Detector/LowTupleGram.lean | 710598c8bef4d1a1ec98aa7e68b00369962c3d17 |
| Detector/LowSelectedSum.lean | a54eb9ec6a5beb0db57ce9baa658718aab808af1 |
| Detector/Physical.lean | f0012db7d94f8f23893732b923c3b346f2fc89bf |

The actual atom retains (-1)^|J| L^(-3/2), original windows, 1/(2pi sqrt(Qphysical)), the Mellin integral, W0/W1, cutoff, calibration and the selected inverse row. The latter is the sum of the ACTUAL lowSelectedWeight times lowMarkedInverseRow, including conjugate Hecke coefficients, logarithmic phase, selected ideal divisibility and all ray correction terms. Grouping our VF seats into it has not been proved. The many distinct first owners here are not automatically its slots.

The first local cross-unselected sign loss is still LowTupleGram's norm_sum_le following exact LowSlotPolynomial Fubini. The NNS identity keeps the full ordered Hermitian Gram; it creates no new sign inequality. Reviewed **20261103-referee-9/10** and **20261103-lean-3**, with today’s uncompiled central consumer, pay nonempty moving mass at their stated original geometry and leave the all-selected inner source open. No actual OAI integral was evaluated by this run.

Power ledger carried forward at its source-verified scope: inverse squared baseline 5/6-2d+507epsilon; normalization by sqrt(Qphysical); original complete LOW amplitude 3/16 plus loss; signal beta-11/16; difference beta-7/8. A new saving nu in the fully normalized LOW square could supply at most nu/2 in amplitude, only after original HIGH/principal/remote/exceptional/tail return. **New nu, amplitude gain, and net beta are UNKNOWN.** Marked-HIGH t/2 and the finite one-shot slot tilt are not paid again.

GitHub status was verified, not inferred from stale policy prose. No open/draft PRs at intake; #1083 is merged at main, while #1080 is closed unmerged and #1079/#1081/#1082/#1084 are merged. At #1083 head **1ae84e2ff019b266114c100f43016eeec71144a9**, all 14 returned checks are completed/success. The dedicated [job 126295407267](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41744927180/job/126295407267) actually tested PR merge **06cac0b95a56fdef0f61294e257e67ee2146c32c**, not a fresh raw-head checkout. Both bridge and gain-ledger files were fetched at head, tested merge and main, and their full bytes and blob SHAs agree.

The runner **scripts/lean/slot_anchored/run_anchored_in_verified_ci.sh**, blob **1b8973bf270dda5ee9635d42f4c89a82f2e2b82a**, uses warning-fatal Lean and checks terminal logs for sorryAx/admitAx. The retrieved log shows Lean 4.34.1, the exact OAI pin, and [propext, Classical.choice, Quot.sound] for the three literal LOW equality/Gram/NNS declarations. Existing unrelated Wiener.lean sorry warnings were visible; no blanket hole-free claim about all dependencies is made. The scoped terminal axiom lists above contain no sorryAx. This run launches no CI and supplies no new formal theorem.

#### Continuity And Publication Evidence

Both dated report sets were retrieved at **bcf9cda3a2060405d46555ef048f3007cbcc1213**; relevant mathematical findings, source qualifications, handoffs and continuation sections were consumed. This was not an independent audit of every upstream derivation or embedded verifier.

| Role file | November 3 blob | November 4 intake blob |
| --- | --- | --- |
| 00-coordinator-am | e35ab2cd9cba2a47ac5be53b09938b37a0c20df3 | 6f00c4e1055a03325e8c152d4bcb505e254b8ecc |
| 10-owner-payment | d52c74b76c2914c3be694f39cd7afe9b122a4834 | 546f46832e12fdf80d32713d26978e63e1d7b7d5 |
| 20-analytic-type-ii | 2b9c3dbab6039e3c30a5ece3e473290af5dbbf0b | a0b8ee1e2c50d6ba926bc948a8896e78982f895f |
| 30-finite-wheel | cd7777180bb5c2c899a60bdd699b99be8e12a672 | 364e6a0a29f8513d5471352d563a49e9b933c2e3 |
| 40-prime-census | eb9a2e0cf7772f22060aec07e0bcddd24ace9cd9 | 108303ebdf61dc64cacd16651521ea39468292a3 |
| 50-adversarial-referee | 583ce524628577818603ffd4e9ec0eb3673a3f37 | dd02c8e7072b9390119da35a204924ddad721d06 |
| 60-lean-verification | fc27fb1ae103e60ff600e5a24ce6716937da3884 | 4585dc42e267f62da5c13624f2a5a4494aa79c53 |

TODAY=AVAILABLE; YESTERDAY=CARRY_FORWARD where cited. Coordinator mirrors had matching tree blobs on each date. Consumed current claims include Coordinator C41-C43; Owner S1-S5 and previous O1-O5/JH1-JH10; Analytic's proper Nyman head/tail with unpaid middle; Wheel's ideal-counting/CORR4 separation; Census cube-incidence R1-R3; Referee's counting-measure/row-admission restriction; and Lean's uncompiled moving-mass continuation. None is silently upgraded to a new VF or Hecke estimate.

External inbox **038018145c0fddb2f6306c0712373adf9cd1ea52** has no new entry since October 18. EXT-20261018-PNT-1..3, EXT-20261017-XCOORD-1's q=R correction, and EXT-20261014-5 retain their original scopes; none supplies the missing occurrence bridge here.

The early checkpoint was committed as **2b6f2da40fd37a4faf99e22ef34790a28a49bf50**, blob **a699910ccb50e45dbc21ad57d9bee4acb23dc495**. Exact readback matched every submitted byte, preserved the entire preceding daily report, and commit inspection showed only this authorized file changed.

Final verifier SHA256: **50c753746e84f4d965da26b5d953bfed71f8242f4bd9e109f19994a4aceab9b1**. The full verifier and Python syntax check passed after the documented corrections. Its complete source and recorded output follow. No local Lean execution occurred. No local clone or endpoint sieve was required. The connector's code search follows a default branch, so every relied-upon discovered definition was re-fetched at the stated immutable source pin.

Only this own dated report is a remote write target. No main, Lean source, central policy, other report, issue, proof branch, PR, workflow, schedule, protection or permission was modified. No agent was launched, and no merge was attempted. Final publication is claimed only after the separate commit/readback verification below.

### Complete Executed Verifier

~~~python
"""Exact finite audit of the squarefree VF ancestry-capacity obstruction.

No Lean is executed. The all-scale proof is in the Owner report.
"""

from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
from math import comb, isqrt
import json


def trial_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def smallest_factors(limit):
    spf = list(range(limit + 1))
    for p in range(2, isqrt(limit) + 1):
        if spf[p] == p:
            for n in range(p * p, limit + 1, p):
                if spf[n] == n:
                    spf[n] = p
    return spf


def log_unit_bounds(x, terms=24):
    assert 1 <= x <= 2
    u = (x - 1) / (x + 1)
    power = u
    lower = F(0)
    for j in range(terms):
        lower += 2 * power / (2 * j + 1)
        power *= u * u
    tail = 2 * power / ((2 * terms + 1) * (1 - u * u))
    return lower, lower + tail


LOG2 = log_unit_bounds(F(2))
DEN = 10**12
assert LOG2[1] < F(25, 36) < F(7, 10)


def ceil_fraction(x):
    return -((-x.numerator) // x.denominator)


@lru_cache(None)
def weight_interval(r):
    assert r >= 2
    x = F(2 * r * r + 2 * r + 1, 2)
    k = x.numerator.bit_length() - x.denominator.bit_length()
    if x < 2**k:
        k -= 1
    lo, hi = log_unit_bounds(x / 2**k)
    lo += k * LOG2[0]
    hi += k * LOG2[1]
    numerator = F(2 * r + 1, r)
    lower = numerator / hi
    upper = numerator / lo
    return (lower * DEN).__floor__(), ceil_fraction(upper * DEN)


def display_interval(lo, hi):
    scale = 10**8
    a = lo * scale // DEN
    b = -((-hi * scale) // DEN)
    def dec(n):
        return f"{n // scale}.{n % scale:08d}"
    return [dec(a), dec(b)]


S = [p for p in range(500, 701) if trial_prime(p)]
Q_VALUES = [490001, 500009, 1000003]
SPF = smallest_factors(max(Q_VALUES))
assert len(S) == 30 and all(SPF[p] == p for p in S)
assert all(trial_prime(q) and SPF[q] == q for q in Q_VALUES)


def audit(q):
    a, b = (q - 1) // 2, q - 1
    pairs = list(combinations(S, 2))
    products = {p * s for p, s in pairs}
    assert len(products) == len(pairs) == 435
    # A differently structured scan reconstructs the exact cofactor population.
    recovered = set()
    support = set(S)
    for m in range(q // 4 + 1, q):
        if m % 2 == 0:
            continue
        p = SPF[m]
        s = m // p
        if p in support and s in support and p != s:
            recovered.add(m)
    assert recovered == products
    current_intervals = []
    roots = []
    owner_counts = Counter()
    for p, s in pairs:
        m, n = p * s, q * p * s
        r = isqrt(n)
        assert p < s < q and SPF[m] == p
        assert m % (p * p) != 0 and m % (s * s) != 0
        assert 4 * m > q and m < q
        assert a * a < n < b * b
        assert r * r < n < (r + 1) * (r + 1)
        assert a <= r < b and p <= r
        assert q < a * a and all(z < a * a for z in (p, s))
        assert b == 2 * a and (b - 1) // 2 + 1 == a
        roots.append(r)
        owner_counts[p] += 1
        current_intervals.append(weight_interval(r))
    assert len(set(roots)) == 435  # q >= b gives at most one per root.
    historical = [weight_interval(isqrt(p)) for p in S + [q]]
    assert all(0 < lo <= hi < DEN for lo, hi in historical)
    xlo = sum(z[0] for z in current_intervals)
    xhi = sum(z[1] for z in current_intervals)
    ylo = 31 * DEN - sum(z[1] for z in historical)
    yhi = 31 * DEN - sum(z[0] for z in historical)
    assert xlo > 31 * DEN
    bits = q.bit_length()
    per_seat = F(36, 25 * bits)
    assert q < 2**bits and F(xlo, DEN) > 435 * per_seat > 31
    horizon = ((b - 1).bit_length() - 1) // 3
    after_deletion = xlo - horizon * max(z[1] for z in current_intervals)
    assert after_deletion > 31 * DEN
    return {
        "q": q, "A": a, "B": b, "seats": 435,
        "prime_ancestor_count": 31,
        "cofactor_range": [min(products), max(products)],
        "root_range": [min(roots), max(roots)],
        "first_owner_count": len(owner_counts), "mobius_each": -1,
        "current_weight_interval": display_interval(xlo, xhi),
        "historical_negative_capacity_interval": display_interval(ylo, yhi),
        "signed_packet_interval": display_interval(xlo - yhi, xhi - ylo),
        "elementary_demand_lower": str(435 * per_seat),
        "elementary_unit_capacity_excess": str(435 * per_seat - 31),
        "short_run_horizon": horizon,
        "after_any_horizon_seat_deletion_excess":
            str((435 - horizon) * per_seat - 31),
        "certified_after_deletion_excess_lower":
            str(F(after_deletion - 31 * DEN, DEN)),
    }


results = [audit(q) for q in Q_VALUES]
# Out-of-domain controls must not be smuggled into the squarefree family.
assert any(4 * p * s <= 2000003 for p, s in combinations(S, 2))
assert len({S[0], S[0], Q_VALUES[0]}) != 3

# Verify the elementary central-binomial input on a small exact finite range.
for n in range(1, 101):
    N = 2 * n
    c = comb(N, n)
    primes = [p for p in range(2, N + 1) if trial_prime(p)]
    assert 2**N <= (N + 1) * c <= (N + 1) * N**len(primes)
    for p in primes:
        v, z = 0, c
        while z % p == 0:
            v += 1
            z //= p
        assert p**v <= N
for t in range(5, 51):
    k = 2**t
    assert k * k - (2 * t + 1) >= 4 * t * k
    if t >= 11:
        assert k * (k - 1) > (k + 1) * 4 * t * (4 * t + 1)

# Complete signed restoration, including the original compression cost.
restoration_checks = 0
for d, x, y, z in [(F(d), F(x, 3), F(y, 5), F(z, 7))
                    for d in range(-2, 3) for x in range(4)
                    for y in range(4) for z in range(-2, 3)]:
    packet, complement = x - y, -d + y + z
    total = -d + x + z
    assert total == packet + complement
    assert total**2 == packet**2 + complement**2 + 2 * packet * complement
    restoration_checks += 1
for u in range(5):
    for v in range(5):
        for current in range(5):
            assert (u + v + current)**2 - (abs(u - v) + current)**2 == (
                4 * u * v + 2 * current * (u + v - abs(u - v)))

print(json.dumps({"prime_support": S, "fixtures": results,
                 "central_binomial_checks": 100,
                 "power_parameter_checks": 46,
                 "signed_restoration_checks": restoration_checks,
                 "compression_checks": 125,
                 "source_admission_controls": "passed",
                 "scope": "exact finite arithmetic; no first-bad or OAI integral claim"},
                indent=2))

~~~

### Recorded Exact Output

~~~json
{
  "prime_support": [
    503,
    509,
    521,
    523,
    541,
    547,
    557,
    563,
    569,
    571,
    577,
    587,
    593,
    599,
    601,
    607,
    613,
    617,
    619,
    631,
    641,
    643,
    647,
    653,
    659,
    661,
    673,
    677,
    683,
    691
  ],
  "fixtures": [
    {
      "q": 490001,
      "A": 245000,
      "B": 490000,
      "seats": 435,
      "prime_ancestor_count": 31,
      "cofactor_range": [
        256027,
        471953
      ],
      "root_range": [
        354194,
        480892
      ],
      "first_owner_count": 29,
      "mobius_each": -1,
      "current_weight_interval": [
        "33.59618270",
        "33.59618271"
      ],
      "historical_negative_capacity_interval": [
        "21.26725110",
        "21.26725111"
      ],
      "signed_packet_interval": [
        "12.32893159",
        "12.32893160"
      ],
      "elementary_demand_lower": "3132/95",
      "elementary_unit_capacity_excess": "187/95",
      "short_run_horizon": 6,
      "after_any_horizon_seat_deletion_excess": "719/475",
      "certified_after_deletion_excess_lower": "1063305173509/500000000000"
    },
    {
      "q": 500009,
      "A": 250004,
      "B": 500008,
      "seats": 435,
      "prime_ancestor_count": 31,
      "cofactor_range": [
        256027,
        471953
      ],
      "root_range": [
        357792,
        485778
      ],
      "first_owner_count": 29,
      "mobius_each": -1,
      "current_weight_interval": [
        "33.56997131",
        "33.56997132"
      ],
      "historical_negative_capacity_interval": [
        "21.26748363",
        "21.26748364"
      ],
      "signed_packet_interval": [
        "12.30248767",
        "12.30248769"
      ],
      "elementary_demand_lower": "3132/95",
      "elementary_unit_capacity_excess": "187/95",
      "short_run_horizon": 6,
      "after_any_horizon_seat_deletion_excess": "719/475",
      "certified_after_deletion_excess_lower": "1050385049893/500000000000"
    },
    {
      "q": 1000003,
      "A": 500001,
      "B": 1000002,
      "seats": 435,
      "prime_ancestor_count": 31,
      "cofactor_range": [
        256027,
        471953
      ],
      "root_range": [
        505991,
        686989
      ],
      "first_owner_count": 29,
      "mobius_each": -1,
      "current_weight_interval": [
        "32.69548954",
        "32.69548955"
      ],
      "historical_negative_capacity_interval": [
        "21.27516333",
        "21.27516334"
      ],
      "signed_packet_interval": [
        "11.42032620",
        "11.42032621"
      ],
      "elementary_demand_lower": "783/25",
      "elementary_unit_capacity_excess": "8/25",
      "short_run_horizon": 6,
      "after_any_horizon_seat_deletion_excess": "-14/125",
      "certified_after_deletion_excess_lower": "1238669058799/1000000000000"
    }
  ],
  "central_binomial_checks": 100,
  "power_parameter_checks": 46,
  "signed_restoration_checks": 400,
  "compression_checks": 125,
  "source_admission_controls": "passed",
  "scope": "exact finite arithmetic; no first-bad or OAI integral claim"
}
~~~



## Verified Publication Receipt - 20261104-owner-2

The completed VF-LOW synthesis, full executed verifier and exact output were published in commit **aafddf3c7f2d66039d0412ccac4e45f495e6c211**, report blob **dc9788b7aca0e16ed7e07770e5d354bbd3f0dd66**. Re-fetch at that immutable commit matched every submitted byte. The entire pre-existing daily report and this invocation's early checkpoint remain unchanged as exact prefixes. Commit inspection showed exactly one changed file: this authorized Owner report.

Claim **20261104-owner-2/SF1-SF4** remains PAPER_PROOF / SELF_AUDIT, with the unit-capacity supplier REFUTED and exact finite certificates verified; independent review is PENDING and no new Lean compilation is claimed. Full-source SF5 is identity-only. No global VF/RH upper bound or new signed-LOW exponent has been established. Research execution and the verified synthesis publication are COMPLETE; next protected route is JOH. This receipt is an append to the same 08:09 EST invocation, not another run.



## Scheduled JOH Continuation Checkpoint - 2026-11-04 16:15 EST Invocation

### A. Most Important Mathematical Question

**IN_PROGRESS / PARTIAL.** Resume the proper-class double-arrival question from 20261103-owner-3/JH9-JH10 and the latest Coordinator synthesis. Let L=Li_2, Q(n)=floor(L(n)), and b_j=min{n>=2:Q(n)>=j}. For EVEN j with composite consecutive arrivals b_j,b_(j+1) and exactly two genuine interior primes p_j<q_j, investigate a_j=b_j+b_(j+1)-p_j-q_j. No favorable sign or aggregate bound is assumed.

### B. Current Authority And Continuity

Actual main: 1daca8d582c361983567f0b6e99d447a77c3aea5 (merged policy #1092). AGENTS blob 547dda0d9456e7a4e1165dc72d59da6f70d5c023; CURRENT_PROOF_CONTRACT blob 7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c; independent multi-front policy blob ffd8f1c65cc4da656174956d4e03b48bea46768b. deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1. JOH is independently selected and due after today's SAT owner-1 and VF-LOW owner-2, not a compulsory OAI assignment.

All seven roles' November 4 and November 3 reports and the external inbox have been retrieved at reporting intake 5ca60b1734d89c85a9d60bcc643023844b480127. TODAY=AVAILABLE; YESTERDAY=CARRY_FORWARD. The external inbox remains 038018145c0fddb2f6306c0712373adf9cd1ea52, with no new entry after October 18. Latest Coordinator explicitly supports this JOH question. Prior JH adjacent-excursion falsifiers at roots 12/35 and SF1-SF5 squarefree ancestry overload remain valid; they are not rebranded as today's result.

Original integer-potential and mismatch definitions were read from VF_MID_FLOOR_LI_SIGNED_POPULATION_BALANCE.lean (9a9336dad72171b6d572a1c1ae88d1ae8b56b530), the discrete backlog source (4255ca0dffe480f2aec6bd0b68797bbd293396c3), and transport cancellation (eb84f59055bd31dc117be034d45c92eb9dab8f27). The JOH external-consumer contract is unchanged at 27e28f09e9f79e8a60d524e5fcb6f19904fa55f5. Main canonical target remains OPEN. Open/draft PR collection is empty at intake; #1085, #1090 and #1091 are now merged at their distinct previously reviewed scopes. Current main has two successful policy/inventory workflows, not a new proof compilation.

### C. Preregistered Derivation And Falsification

Test H-JOH-EVEN-SIGN: every selected even-j double-arrival slot has a_j<=0. Also test the stronger dyadic aggregate variant W(X)<=0 over all selected slots fully contained in [X,2X], for integer X. A positive local slot refutes only the local version; a positive full W is needed to refute the aggregate version. Use development integers through 2048, held-out 2049..4096; widen only for a specifically identified new hypothesis, not a fitted exponent.

Explore an exact neutral-packet decomposition at Li arrivals, preserving true prime/composite membership, both endpoint demands, historical anchor, every unselected event, and the full quadratic return. Derive any deterministic slot-length or placement restriction independently; distinguish arithmetic facts from parity/model controls. Floors used in promoted witnesses will receive rational interval certificates, and primes/factors exact verification.

### D-K. Pending Work

Derivation, decisive test output, quantitative relevance, independent-review requests and the complete A-K synthesis remain PENDING. No new theorem or exponent gain is asserted in this checkpoint. Trigger: actual scheduled invocation 2026-11-04T16:15:01-05:00; RUN_ID_UNAVAILABLE. No agent launch, Lean execution, source edit, PR, schedule or policy mutation is authorized or planned. Only this existing daily report is updated.


## Scheduled JOH Final Synthesis - Claim 20261104-owner-3

Actual invocation: scheduled **2026-11-04T16:15:01-05:00**, RUN_ID_UNAVAILABLE. This completes the checkpoint above, not a separate execution. Selected route: **JOH**. Next protected route: **SAT**, then VF-LOW. `deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1` at main **1daca8d582c361983567f0b6e99d447a77c3aea5**.

### A. Most Important Mathematical Development

**The unresolved within-slot sign is not needed to pay this part of the JOH source.** Every disjoint even-index double-arrival packet has a bounded primitive, so its entire accumulated contribution is O(N), with no assumed sign. More substantially, retaining the ACTUAL backlog at every floor-Li arrival compresses the complete JOH statistic with an explicit, nonnegative placement error:

```text
G(N) = U(N) + E_place(N),
0 <= E_place(N) <= pi(N) log N <= (13/10) N   (N>=17).
```

Here U uses actual prime counts at the original arrival locations, original cell lengths, the initial anchor and the final partial cell. E_place is the exact sum of within-cell prime displacements, not an unspecified error. The final inequality uses the established prime-count estimate in Johnston's Lemma 2.2, not RH, PNT in short intervals, a random model or the desired bound.

Thus all within-Li-cell positional information costs only O(N) in this integrated statistic. The remaining serious question is the weighted history of the sampled count backlogs, not the sign of each microscopic midpoint. This is a source-qualified proper-term estimate and a reason to redirect the local investigation, **not** a bound for U or a new global exponent.

The proposed sign rules are also **REFUTED** on genuine arithmetic. Even-index slots of the SAME length six, SAME least-owner pair (2,2), and SAME twin-prime gap have opposite areas: (194,197,199,200) gives -2; (820,821,823,826) gives +2. The complete selected dyadic aggregate has W(512)=+1 and the held-out W(2048)=+3. No claim about an eventual-only sign is refuted by these finite witnesses.

Evidence: LC1 is IDENTITY_ONLY; LC2 and LC4 are **PAPER_PROOF / SELF_AUDIT** quantitative proper-sector results; LC3 is **FINITE_COMPUTATION / REFUTED** at the displayed universal scopes; LC5 is a **PAPER_PROOF / TARGET_EQUIVALENT** consumer reformulation, not an independently paid supplier. Independent review and new Lean formalization remain PENDING. **No new complete-endpoint gain, canonical bound or RH proof.**

### B. Current Authoritative Objective

Canonical target, unchanged and OPEN:

```text
exists C>=0, forall integer R>=2:
  |pi(R^2) - F_R - sqrt(2)| <= C R log R,
F_R = sum_(2<=r<R) (2r+1)/log(r^2+r+1/2).
```

The exact original JOH carrier is

```text
L(x)=Li_2(x)=integral_2^x du/log u,
Q(n)=floor(L(n)), B(n)=pi(n)-Q(n)-1,
eta(k)=1_Prime(k)-Q(k)+Q(k-1),
G(N)=sum_(2<=n<N) B(n)=sum_(3<=k<N)(N-k) eta(k).
```

The Lean primitive is `eta(k)=vfMidFloorLiPrimitiveMismatch(k-1)`, not the declaration at k. The continuous external consumer uses classical li, with its fixed li(2) offset; it is not silently replaced by Li_2. The actual-prime canonical phase is still sqrt(2), with its full quadratic phase correction if that coordinate is used.

Material bytes fetched from the pinned main:

| Source | Blob SHA | Relevant scope |
| --- | --- | --- |
| AGENTS.md | 547dda0d9456e7a4e1165dc72d59da6f70d5c023 | Independent routing, source integrity and own-report-only writes |
| CURRENT_PROOF_CONTRACT.md | 7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c | Canonical objective and source safeguards |
| Independent multi-front policy | ffd8f1c65cc4da656174956d4e03b48bea46768b | NO_PIGEONHOLING_ROUTE_SELECTOR_V1 |
| Stable task selector | 4fbab59cc6fcc33a4f4e7a8ef447b2f7947b53dd | Protected Owner VF-LOW/SAT/JOH rotation |
| Research engine | 6c1d1c10e2755017ffe9d7f40df8b9ae7692f23a | Resume exact derivations and preserve evidence |
| VF_MID_FLOOR_LI_SIGNED_POPULATION_BALANCE.lean | 9a9336dad72171b6d572a1c1ae88d1ae8b56b530 | Actual integer potential, ternary mismatch, exact Abel carrier |
| VF_MID_FLOOR_LI_DISCRETE_BACKLOG.lean | 4255ca0dffe480f2aec6bd0b68797bbd293396c3 | Actual square-backlog recurrence and owner census |
| VF_MID_FLOOR_LI_TRANSPORT_CANCELLATION.lean | eb84f59055bd31dc117be034d45c92eb9dab8f27 | Existing chamber identity and full boundary-energy correction |
| VF_MID_915_FLOOR_LI_TRANSPORT_BOUNDARY.lean | 10829c3857b6a375d1dd8179f78a35550c9e67d8 | Original history/anchor remains; no extra denominator capacity |
| PrimeSieveLipschitzExcursion.lean | 3eec4abf544310871088dae648fbed1f400cf35a | Original Li integral and drift theorem |
| LI_FAN_ONE_SIDED_WEIGHTED_COMPOSITE_RH_CONTRACT_20261022.md | 27e28f09e9f79e8a60d524e5fcb6f19904fa55f5 | Paper JOH eventual-square consumer and physical weights |
| VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb | Canonical definition and explicit classical-criterion premise |
| VF_MID_FLOOR_LI_TRANSPORT_MINING.md | 14f86c0038da3371353a94fce2510dabf03ccd62 | Existing transport identities, finite lifetime observations only |

The last eight mathematical files have the same material SHAs as the applicable earlier sources, but their bytes were retrieved and relevant definitions/proofs read, not assumed cached. The source search found existing generic chamber and quadratic identities; these are reused, not claimed as new. No identical all-Li-cell placement bound was located in the scoped sources and two-day handoffs; no exhaustive or literature-novelty claim is made.

Live PR collection: no open or draft PR at intake. Human merges #1085, #1090 and #1091 were directly confirmed. Their independently audited central moving-mass, fixed-log Nyman and explicit fixed-slot-count results retain the scopes recorded by today's Coordinator; none is a JOH estimate. Main's two returned workflows are successful Proof inventory and Documentation checks, not a new JOH compilation. No new or local Lean execution occurred.

### C. Structural Hypotheses Investigated

Resume **20261103-owner-3/JH9-JH10**, its section J proper-class question, and **20261104-coordinator-2**, section H. Today's prior actual Owner turns were SAT owner-1 and VF-LOW owner-2, so this independently useful JOH turn completes the protected triple.

Three moves were distinguished:

1. **H-JOH-EVEN-SIGN:** every selected even-index double-arrival slot has nonpositive midpoint area. The stricter source restriction excludes yesterday's odd-index first witness; a new genuine test was necessary.
2. **H-JOH-EVEN-DYADIC:** W(X)<=0 for every integer X>=5, including every selected slot fully contained in [X,2X]. A local counterexample alone would not disprove this aggregate version.
3. Pay bounded, zero-total-mass packets geometrically, then test whether the same clock geometry controls ALL within-slot placement. This yields LC2 and LC4 without requiring either sign conjecture.

The first two tests were recorded in the early checkpoint before execution. Development range was 2..2048; held-out was 2049..4096. No larger range or fitted exponent was used. The all-cell compression was derived after the packet bound and added as a disclosed second-stage verification, not retroactively described as preregistered.

Wording correction to the preserved checkpoint: the aggregate sign assertion is logically WEAKER than a universal pointwise sign assertion. Refuting the aggregate is a stronger falsification than exhibiting just one positive packet. The tested definitions and rejection conditions were unchanged.

### D. Mathematical Derivation

#### LC1. Genuine Admission And Neutral Packet

For integers j with b_j>=5 define

```text
b_j=min{n>=2: Q(n)>=j}.
```

L is increasing and unbounded. Its integer increments above four are less than one, so these are strictly increasing arrivals with Q(b_j)=j and Q(n)=j on b_j<=n<b_(j+1). Retain these INTEGER arrivals, not continuous inverse-Li roots.

Select any subfamily of EVEN j for which b=b_j and c=b_(j+1) are composite and the interior contains exactly two primes p<q. Even indexing makes the closed slots pairwise disjoint: c=b_(j+1)<b_(j+2). The actual nonzero mismatch events on the closed slot are exactly

```text
b(-1), p(+1), q(+1), c(-1).
```

There is no hidden prime/model coincidence here: the endpoints are composite, and there is no model arrival in the interior. Every prime/composite keeps its original location, factorization and occurrence. The slot is a genuine source subset, not just eligible ancestry.

Its primitive and accumulated contribution at ANY integer cutoff N are

```text
k_j(n)=-1_(b<=n<p)+1_(q<=n<c),
P_j(N)=-(N-b)_+ +(N-p)_+ +(N-q)_+ -(N-c)_+.
```

These are specializations of the existing signed-transport chamber identity. In particular, for N>=c,

```text
P_j(N)=a_j=b+c-p-q=(c-q)-(p-b).                 (LC1)
```

Zero mass makes the completed contribution independent of N. It does not force its sign to vanish. A cutoff inside the packet retains the displayed clipped formula; it is never replaced prematurely by a_j.

#### LC2. An Independent All-Scale Bound For The Selected Class

Let S be ANY subfamily just defined, finite or infinite. It is locally finite. Put

```text
K_S(n)=sum_(j in S) k_j(n),
P_S(N)=sum_(2<=n<N) K_S(n).
```

Since the chamber supports are disjoint,

```text
|K_S(n)|<=1,                |P_S(N)|<=N-2.       (LC2a)
```

This is uniform in the scale, chosen subfamily, number of packets, owner labels and factor depth. It includes every partial terminal packet, without any probabilistic or prime-distribution premise.

For a complete selected slot put u=p-b>=1, v=c-q>=1 and d=q-p>=2. These primes exceed two, so d is even. With ell=c-b=u+d+v,

```text
|a_j|=|v-u|<=u+v-2=ell-d-2<=ell-4.             (LC2b)
```

For S_X consisting of ALL selected slots contained in [X,2X], m_X=#S_X, disjointness gives the exact uniform restriction

```text
|W(X)| <= sum_(j in S_X)|a_j|
       <= sum_(j in S_X)(b_(j+1)-b_j)-4m_X
       <= X-4m_X <= X.                          (LC2c)
```

This answers the requested proper-class signed-estimate question without a sign law. It is not a bound for the original full G.

To restore that full source define eta_star by deleting ONLY these four actual events per selected slot, define B_star=B-K_S, and G_star(N)=sum_(2<=n<N)B_star(n). The complement retains every other event, all original anchors and squareful terms. Then

```text
G=G_star+P_S,
G^2=G_star^2+2G_star P_S+P_S^2.                 (LC2d)
```

The complete mixed term is present. Its honest magnitude price is at most 2(N-2)|G_star|+(N-2)^2 in the difference of squares; no diagonal-only inference is made. This is a JOH source comparison, not a replacement for #915's compressed historical denominator.

#### LC3. Exact Sign Falsifiers

The interval certificate proves the relevant Q floors, and independent integer sieve/trial factorization certifies prime membership.

| j | (b,p,q,c) | a_j | Least owners of (b,c) | Endpoint factorizations |
| ---: | --- | ---: | --- | --- |
| 48 | (194,197,199,200) | -2 | (2,2) | 194=2*97; 200=2^3*5^2 |
| 150 | (820,821,823,826) | +2 | (2,2) | 820=2^2*5*41; 826=2*7*59 |
| 328 | (2109,2111,2113,2117) | +2 | (3,29) | 2109=3*19*37; 2117=29*73 |
| 330 | (2124,2129,2131,2132) | -4 | (2,2) | 2124=2^2*3^2*59; 2132=2^2*13*41 |

For j=150, Q(819)=149, Q(820)=...=Q(825)=150 and Q(826)=151. The positive witness satisfies ALL fixed hypotheses. The held-out j=328 positive witness even has both endpoint demands squarefree; simply removing squareful demands cannot rescue the universal sign claim.

The complete [512,1024] selected population consists of exactly:

```text
j=116: (597,599,601,603), area 0;
j=148: (806,809,811,813), area -1;
j=150: (820,821,823,826), area +2.
W(512)=1.
```

Thus H-JOH-EVEN-DYADIC is refuted without dropping unfavorable slots. Additional complete dyadic totals: W(128)=-2, W(256)=0, W(1024)=-4, W(2048)=+3. The first positive integer-X window within the declared scan is X=413. These are finite universal-claim falsifiers, not assertions of infinitely many sign changes or asymptotic frequency.

#### LC4. Full Li-Cell Compression With A Paid Placement Error

**Theorem (paper).** Fix any original arrival a=b_(j0)>=5 and an integer N>=a. For each j>=j0 with b_j<N let

```text
t_j=min(b_(j+1),N), ell_j=t_j-b_j, h_j=B(b_j),
U_a(N)=G(a)+sum_j ell_j*h_j,
E_a(N)=sum_j sum_(b_j<p<t_j, p prime) (t_j-p).
```

Then, for every such a,N,

```text
G(N)=U_a(N)+E_a(N),
0<=E_a(N)<=pi(N)log N,
0<=E_a(N)<=(13/10)N  when N>=17.                (LC4)
```

Constants are independent of a, j0, N, cell count and all factorizations. The finite or truncated last cell is included by t_j. No count assumption on any cell and no disjoint-even restriction are needed.

**Proof.** For b_j<=n<t_j, Q(n)=j, hence exactly

```text
B(n)=B(b_j)+pi(n)-pi(b_j).
```

Sum this over the original integers in that cell. Finite Fubini gives

```text
sum_(b_j<=n<t_j)B(n)
 = ell_j B(b_j)+sum_(b_j<p<t_j, p prime)(t_j-p).
```

These cells partition [a,N), and the initial G(a) is kept. Boundary primes p=b_j already belong to h_j; a prime at the next boundary belongs to the next h, not this cell. A prime at N has zero weight and is excluded. The map counts every original interior prime once, with its exact weight. In particular the error is nonnegative.

For a cell containing an interior prime, t_j>=b_j+2. Its last integer t_j-1 has the SAME floor j as b_j, so

```text
0 <= L(t_j-1)-L(b_j) < 1,
(t_j-1-b_j)/log(t_j-1)
 <= integral_(b_j)^(t_j-1) du/log u < 1.
```

Consequently each original displacement satisfies

```text
0<t_j-p<=t_j-b_j-1<log(t_j-1)<=log N.
```

At most pi(N) primes occur in the error sum, proving its first bound. The last uses the classical explicit estimate pi(x)<1.3*x/log x for x>=17, stated in [Johnston, Lemma 2.2](https://arxiv.org/html/2201.06184v2#S2), with x=N. Its hypotheses concern the SAME genuine prime count, and its constant is absolute. No short-interval input is imported. Even the elementary weaker E_a(N)<=N log N follows without that external estimate and is smaller than the later RH-scale signed margin.

This is a justified comparison, not a claim that actual primes are located at b_j. The omitted positions are recovered exactly in E_a. The floor phase, unequal prime counts, simultaneous prime/model events and every original square boundary are retained through the actual b_j and h_j.

For a=5 (Q(4)=1,Q(5)=2,G(5)=0, certified below), write U=U_5 and E_place=E_5. Full quadratic accounting is

```text
G^2=U^2+2U E_place+E_place^2,
|G^2-U^2| <= (13/5)N|U|+(169/100)N^2   (N>=17).
```

There is no claim that the entire squared error costs only O(N^2); its cross term remains. LC2 and LC4 are alternative decompositions of the SAME source and are not two independent cancellation credits to add.

#### LC5. Endpoint Relevance And Its Limitation

Let H(x)=integral_2^x(pi(t)-li(t))dt with classical li. The existing JOH paper bridge gives G(N)-H(N)=O(N). The source was checked against [Johnston's original theorem and proof](https://arxiv.org/html/2201.06184v2#S3): under RH, the proof yields H(x)<=-c*x^(3/2)/log x eventually for some c>0; if RH is false, it gives positive values of order x^kappa along an unbounded sequence for some kappa>3/2. These are external analytic inputs, not new formal imports.

LC4 therefore yields U(N)-H(N)=O(N). Under RH, U(N)<=G(N)<0 eventually. If RH is false, transfer the positive H values to integers with O(x) cost, and then to a nearest square with O(x^(3/2)) cost using the elementary |B(n)|=O(n) bound. The x^kappa term dominates both costs, as well as E_place=O(x), so U(R^2)>0 for arbitrarily large R. Hence, at PAPER scope with the stated external ingredients,

```text
RH iff U(R^2)<0 for every sufficiently large integer R. (LC5)
```

This is explicitly **TARGET_EQUIVALENT**. The independent gain is payment of E_place, not proof of this remaining sign. No target-strength bound on U is assumed. At N=R^2, the paid placement error is O(R^2), versus the external RH negative-margin scale R^3/log R; the original canonical pointwise bound is not inferred from this first moment alone.

An elementary inverse statement records where a hypothetical large positive discrepancy must reside:

```text
G(N)>=Y  ==>  U(N)>=Y-(13/10)N.
```

Similarly LC2 gives G_star(N)>=Y-(N-2). Thus neither these double-arrival packets nor ANY within-single-Li-cell prime placement can create an asymptotic superlinear positive discrepancy while the corresponding retained source remains small. This does not supply an impossibility theorem for the retained source.

### E. Quantitative Consequence

New independent restrictions at paper scope: |W(X)|<=X-4m_X; |K_S|<=1 and |P_S(N)|<=N-2 with complete terminal clipping; and the full proper-error bound 0<=E_place(N)<=(13/10)N. They hold uniformly on the actual prime/floor-Li source, not merely at the tested scales.

The conclusion is stronger strategically than another local sign catalogue: the whole within-clock position bill is already lower order for the JOH endpoint, despite genuine positive packets. Further work trying to prove a universal midpoint sign is both falsified in its stated form and unnecessary for paying this term. The complete sampled history U remains unpaid, including cross-cell coherence and the original initial condition.

No incoming 7/8 estimate was needed or bootstrapped. No new upper bound on full G, canonical VF, original #915 NNS, or Mertens was obtained. New net endpoint gain **UNKNOWN / NONE ESTABLISHED**; independent-innovation gate remains **SEARCH_BROAD**. Previously reviewed fixed-slot results retain their separate scopes without being counted again.

### F. Falsification And Circularity Review

The final program certifies every Q(n), 2<=n<=4096, using integer-only outward-rounded intervals with denominator 2^200, 80 terms of the range-reduced log series and 180 terms of the positive Ei series. Its analytic identity is F(z)=log z+sum_(k>=1)z^k/(k*k!), F'(z)=exp(z)/z; L(n)=F(log n)-F(log 2), so Euler's constant cancels. Explicit geometric tails are included. The minimum noninitial distance to an integer exceeds 9/100000; the largest interval width is below 10^(-50). No floating-point sign decision is used.

All prime flags through 4096 agree between an Eratosthenes sieve and independent trial factorization. There are 41 selected slots: 12 positive, 13 negative, 16 zero. Development has 13 slots, held-out has 28, with no straddler at 2048. All 2044 integer windows 5<=X<=2048 satisfy LC2c. The finite survival of this bound is regression evidence for its separate proof, not its justification.

Executed exact checks: 4095 original/complement/packet prefix reconstructions, 8190 full quadratic identity/bound checks, and 4092 all-cell compression checks. Every partial cutoff is included. E_place was independently reconstructed from literal prime displacement weights, not only defined as G-U.

| N | Original G(N) | Sampled U(N) | E_place(N) |
| ---: | ---: | ---: | ---: |
| 512 | -2595 | -2808 | 213 |
| 1024 | -6703 | -7134 | 431 |
| 2048 | -16599 | -17485 | 886 |
| 4096 | -42284 | -44049 | 1765 |

Separate extraction of the 41 neutral packets gives at N=4096: original G=-42284, packet P_S=-2, retained G_star=-42282. The all-cell sampled U=-44049 is a DIFFERENT retained coordinate; these must not be conflated. The roots 12/35 anchored values remain unchanged; yesterday's witnesses are used only as regressions.

Stress points addressed: prime at a cell boundary, composite/squareful endpoints, squarefree held-out demands, coincident arrivals, even-index nonoverlap, a cutoff inside a packet/cell, zero-area packets, and opposite signs with the same owner/length/twin-gap signature. The bound does not claim a family covers every event. The residual is explicitly the original complement. Duplicate prime histories, unsigned replacement of global covariance, and altered Li constants are absent.

The prior generic transport identity already exists on main. The paper additions are the checked disjoint-source upper bound and ALL-cell logarithmic-displacement estimate, plus their quantitative implication for this investigation. LC5 remains target-equivalent and supplies no new arithmetic sign. No independent Referee acceptance or Lean compilation is asserted.

### G. Conceptual Interpretation

The four-event motif has zero mass but a nonzero first moment. Its positive and negative areas depend on placement, and genuine factors do not fix the orientation. Yet its primitive has bounded height. Disjointness converts that fact into a global bound even when all packet areas conspire with the same sign.

The wider compression is more decisive. At the fixed Li clock, all information about prime positions INSIDE a cell is an explicitly paid linear error. The possible large signed defect is carried by how many prime arrivals have accumulated by successive clock boundaries and how those signed levels persist across many cells. This distinguishes local timing from cross-cell count history without pretending they are independent. The new representation is useful because the discarded information has an independently proved price.

### H. Competing Mechanisms

| Mechanism | Established restriction / obstruction | Missing input and disposition |
| --- | --- | --- |
| Universal even-slot midpoint sign | LC3 genuine +2; same owners/width/twin gap also gives -2 | ABANDON that universal sign, not eventual or global compensation |
| Nonpositive complete dyadic selected area | W(512)=1, held-out W(2048)=3 | ABANDON universal version; no asymptotic sign conclusion |
| Bounded neutral-packet removal | LC2 pays the selected class, including terminal clipping, at O(N) | RETAIN as a proper-sector tool; no claim on its complement |
| All-cell placement compression | LC4 pays every local positional error at O(N) | CONTINUE with sampled count history; U's sign is target-equivalent and OPEN |
| Growing-window count correlations | Exact h_(j+h)-h_j carrier below | Exploratory independent candidate; no theorem or complete consumer yet |
| SAT moving-band interior | owner-1 S3 bound and OPEN-SAT-I | Next protected turn, retain endpoint/model/zero-layer return |
| VF-LOW ancestry payment | owner-2 SF1-SF5 fixed-depth squarefree overload | Do not revive once-only capacity; next after SAT |

The compression is more useful than the falsified local sign as a decomposition because it actually pays a whole term. It is not evidence that JOH has become easier than other routes; its remaining count-history source is still target-strength.

### I. Specialist Handoffs

**Coordinator:** register 20261104-owner-3 LC2/LC4 as new self-audited paper proper-sector bounds, LC3 as exact sign falsifiers, and LC5 as target-equivalent. Stop assigning the nonpositive even-slot midpoint law as an unpaid necessity. A serious next JOH mechanism must constrain cross-cell sampled counts or their complete signed history. Preserve distinct next Owner SAT and then VF-LOW turns; do not narrow the nine-route programme.

**Referee:** independently reconstruct LC4 before reading the proof: original b_j, h_j, truncated t_j, exact E_a, and 0<=E_a<=pi(N)log N. Challenge N versus N-1, prime arrivals at boundaries, missing G(a), and the use of the genuine explicit pi upper bound. Separately test LC2's infinite-subfamily local finiteness and all-prefix clipping, LC3's entire W(512) population, and LC5's external square interpolation. Return separate scope verdicts; no global gain is proposed.

**Census:** a small independent replication is enough: certify the two same-owner six-length slots, all three W(512) slots, and the held-out W(2048) total; reconstruct G/U/E at 512 and 4096. Rival claims are sign-only versus bounded-but-both-sign placement. Required exactness is integer primality plus certified floors. Any positive W disproves the universal aggregate claim; a larger range is not needed to strengthen that conclusion.

**Analytic:** if a future JOH support turn is warranted, examine the precise growing-arrival-window variance candidate in J, including actual sampled windows and halo. Any theorem must be translated with correct sampling weights; do not import an all-real interval average without its discrete-sampling bridge. Even a positive result does not control the initial backlog or full cross-window coherence. No Mobius-to-Hecke map is presumed.

**Wheel:** the same (least owner 2,2), twin-prime gap and slot length permit both signs. Local factor labels alone cannot decide this midpoint. Seek genuine restrictions on the COUNT innovation sequence, not another price for an already paid within-cell displacement. Preserve squareful and coincidence events.

**Lean:** no speculative supplier or immediate proof-branch request. After independent acceptance and utility review, LC2 is a finite disjoint-chamber consequence of existing transport declarations; LC4 requires exact floor-cell partition and Li drift/lower-integral ingredients, with the established prime-count upper bound stated honestly. Formalizing the identity alone must not be labeled the O(N) estimate or the remaining U sign. Existing accepted implementation work is not displaced.

These are published asynchronous handoffs, not claims that any specialist was launched or has reviewed the work.

### J. First Independently Missing Lemma

There is **no identified independently justified supplier closing the remaining U sign**. That sign is explicitly target-equivalent and must not be renamed as an elementary last lemma.

A proper, falsifiable next quantitative candidate for a later JOH turn is the following original COUNT-increment question. For real X sufficiently large set h=floor(X^(1/4)), J_X={j:X<=b_j<2X}, and

```text
V_clock(X)=sum_(j in J_X)
  |pi(b_(j+h))-pi(b_j)-h|^2
 =sum_(j in J_X)|B(b_(j+h))-B(b_j)|^2.

OPEN-JOH-CLOCK-VAR (exploratory):
exists absolute C,A>=0 and X0, forall X>=X0,
  V_clock(X) <= C X h (log X)^A.
```

Every interval is the literal original (b_j,b_(j+h)] with all multiplicities and its upper halo retained; Q(b_(j+h))-Q(b_j)=h exactly. The question asks for an independent growing-window prime-count restriction, not a bound for G renamed. No proof, literature novelty, optimal exponent, or implication to RH is claimed. Its existing literature status has not been fully audited in this invocation. It would control a proper increment energy, while any constant offset of the level sequence is invisible to it; therefore the initial history and global signed consumer would remain separate obligations. This explicit limitation prevents selling it as a complete supplier.

Before new computation, Analytic should check applicable established prime short-interval variance results and the exact discrete-sampling bridge. Any requested finite test must freeze C,A and range separately; an unspecified constant is not falsifiable by a finite scan. This is a future candidate, not an extra launch or a reason to skip the next SAT turn.

The immediately due next Owner action remains the already specified **OPEN-SAT-I** from owner-1: with b=7/8, alpha=8/9, seek a fixed kappa>0 in the true interior I_R bound R^(11/6-kappa+epsilon), preserving the separate 85/48 endpoint and full model/complement. Do not repeat the paid S3 derivation or claim its interior saving alone beats the terminal 7/4 exponent.

### K. Next-Run Resume Capsule

```text
RUN: actual scheduled 2026-11-04T16:15:01-05:00; RUN_ID_UNAVAILABLE.
MAIN: 1daca8d582c361983567f0b6e99d447a77c3aea5.
POLICY: NO_PIGEONHOLING_ROUTE_SELECTOR_V1 / ffd8f1c65cc4da656174956d4e03b48bea46768b.
INTAKE_REPORT_HEAD: 5ca60b1734d89c85a9d60bcc643023844b480127.
EARLY_CHECKPOINT: 7368003a54ca0738fee7b7f8145fdf5106a66609.
EARLY_BLOB: 380ce83816eaf3e4dd1109cae767d90156940175; exact readback PASS.
ROUTE/TASK: JOH / genuine even-arrival area, then all-cell placement compression.
CLAIM: 20261104-owner-3 / LC1-LC5.
NEW INDEPENDENT RESTRICTION: |K_S|<=1, |P_S(N)|<=N-2, |W(X)|<=X-4m_X;
  0<=E_place(N)<=pi(N)log N<=1.3N, exact G=U+E_place.
FALSIFIERS: j150 +2 versus j48 -2 with identical owners/length/twin gap;
  full W(512)=1; held-out W(2048)=3.
PAID: within-cell placement, not actual count-level history U.
COMPLETE RETURN: all original anchors, boundary coincidences, clipped last cell;
  G^2=U^2+2UE+E^2, and separate G_star/P decomposition with mixed term.
REVIEW: SELF_AUDIT; independent Referee PENDING. FORMAL: NOT_COMPILED_THIS_RUN.
CONSUMER: external Johnston plus O(N) bridge; U eventual sign TARGET_EQUIVALENT.
NEW COMPLETE-ENDPOINT GAIN: UNKNOWN / NONE; canonical VF and RH OPEN.
OWNED ROTATION TODAY: SAT owner-1; VF-LOW owner-2; JOH owner-3.
NEXT: SAT OPEN-SAT-I with full endpoint/model/complement; then VF-LOW.
JOH FUTURE: cross-cell count increments, not a revived local midpoint sign.
PERMISSIONS: only this own dated report; no source/PR/agent/schedule/main action.
```

#### Two-Day Continuity

All listed reports were actually retrieved at the intake reporting SHA. Relevant findings, corrections and continuation sections were read; this is not independent acceptance of all their claims. TODAY=AVAILABLE for every role; YESTERDAY=CARRY_FORWARD. Coordinator 00/90 mirror blobs agree in the fetched directory metadata.

| Role | November 3 blob | November 4 intake blob |
| --- | --- | --- |
| Coordinator | e35ab2cd9cba2a47ac5be53b09938b37a0c20df3 | f4297e525684aa149b9f7bd037bc1507e9f3a3e4 |
| Owner | d52c74b76c2914c3be694f39cd7afe9b122a4834 | bef2ab8cefd691a868d8f1acdfe696af41266d16 |
| Analytic | 2b9c3dbab6039e3c30a5ece3e473290af5dbbf0b | 5e489bffbce7fe986b9f48c73cb409beaa151f82 |
| Wheel | cd7777180bb5c2c899a60bdd699b99be8e12a672 | 6a773f357029bb97cf34110532c7de1f7bb38f3f |
| Census | eb9a2e0cf7772f22060aec07e0bcddd24ace9cd9 | 9f634c872fe98f82676c263a4faba35dff3ac4f0 |
| Referee | 583ce524628577818603ffd4e9ec0eb3673a3f37 | 11eaf073fad23591cdf6d8fe83209042139e54c5 |
| Lean | fc27fb1ae103e60ff600e5a24ce6716937da3884 | 1519754f2b440abd6821a960926028dc776c8576 |

Consumed scope: latest Coordinator C45-C48 Nyman cutoff/deficit work and distinct JOH assignment; Owner SAT S1-S5, VF SF1-SF5 and yesterday JH1-JH10; Analytic CODIV logarithmic maximal estimate and CF1-CF3; Wheel top-prime packet obstruction and completion coherence; Census exact norm/factor collisions; Referee's scoped CF acceptance and moving-mass/small-row restrictions; Lean's actual Nyman and central-mass formal evidence. None is silently imported as a bound on the present prime-clock source. External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 is unchanged, with latest entries October 18; EXT-20261018-PNT-1..3 and EXT-20261014-5 remain source-qualified safeguards, not current routing.

#### Execution And Publication Discipline

The early checkpoint was committed and read back exactly; commit inspection showed only this authorized report changed. The full synthesis is published only after current-blob refresh and exact readback; the following receipt will record that verified commit, not a presumed outcome.

Direct shell GitHub access failed with CONNECT tunnel HTTP 403; connected GitHub reads and report writing worked. No local Lean or background mathematical process remains. No main, shared instruction, proof source, other agent report, issue, PR, workflow, permission, protection or schedule was modified. No agent was launched and no merge was attempted.

Final verifier source SHA256: **41a854b5741dd3b0396a8a809270d82e3e9f978bec877cdb264173c1102c2dd7**. Reused certificate library SHA256: **c6411707d81bbc6f74246ecab45eaa8d353650258ae969e08342717eb5dbbd86**. The library is reproduced verbatim from the available prior proof method, not called a new algorithm. Exact selected-slot data digest: **e9b1ab26ae9cae521490e754bd40b1af202c6f3cefc7c8b1503ef4bca86f4b2e**. Both scripts passed syntax checks; the final verifier exited zero.

### Complete Executed Certificate

The two program blocks below are the exact executed sources, followed by the exact output. No finite test is promoted to an all-scale theorem or Lean proof.


#### joh_interval_base.py

```python
"""Rational dyadic interval certificate for the selected genuine JOH events.

All arithmetic deciding a floor or sign uses Python integers. Natural logs
use range reduction and the atanh series with an explicit geometric tail.
Li_2 uses the convergent Ei series; Euler's constant cancels exactly.
"""

import json
from fractions import Fraction
from math import isqrt

BITS = 200
SCALE = 1 << BITS
LOG_TERMS = 80
EI_TERMS = 180


def ceildiv(a, b):
    return -((-a) // b)


def rational(n, d=1):
    return n * SCALE // d, ceildiv(n * SCALE, d)


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def sub(a, b):
    return a[0] - b[1], a[1] - b[0]


def mul(a, b):
    assert a[0] >= 0 and b[0] >= 0
    return a[0] * b[0] // SCALE, ceildiv(a[1] * b[1], SCALE)


def div(a, b):
    assert a[0] >= 0 and b[0] > 0
    return a[0] * SCALE // b[1], ceildiv(a[1] * SCALE, b[0])


def times(a, n):
    return (a[0] * n, a[1] * n) if n >= 0 else (a[1] * n, a[0] * n)


def small_log(n, d):
    assert d <= n <= 2 * d
    u = rational(n - d, n + d)
    u2 = mul(u, u)
    power, result = u, rational(0)
    for j in range(LOG_TERMS):
        result = add(result, div(times(power, 2), rational(2 * j + 1)))
        power = mul(power, u2)
    tail = div(times(power, 2), times(sub(rational(1), u2), 2 * LOG_TERMS + 1))
    return result[0], result[1] + tail[1]


LOG2 = small_log(2, 1)


def log_rational(n, d=1):
    assert n > 0 and d > 0
    k = n.bit_length() - d.bit_length()
    if k >= 0:
        den, num = d << k, n
    else:
        den, num = d, n << (-k)
    if num < den:
        k -= 1
        num *= 2
    assert den <= num < 2 * den
    return add(small_log(num, den), times(LOG2, k))


def ei_without_gamma(z):
    assert z[0] > 0
    result = (log_rational(z[0], SCALE)[0], log_rational(z[1], SCALE)[1])
    term = rational(1)
    for k in range(1, EI_TERMS + 1):
        term = div(mul(term, z), rational(k))
        result = add(result, div(term, rational(k)))
    first = div(div(mul(term, z), rational(EI_TERMS + 1)), rational(EI_TERMS + 1))
    ratio = div(z, rational(EI_TERMS + 2))
    tail = div(first, sub(rational(1), ratio))
    return result[0], result[1] + tail[1]


BASE = ei_without_gamma(LOG2)


def li_interval(n):
    if n == 2:
        return rational(0)
    return sub(ei_without_gamma(log_rational(n)), BASE)


def sieve(n):
    p = bytearray(b"\x01") * (n + 1)
    p[:2] = b"\x00\x00"
    for k in range(2, isqrt(n) + 1):
        if p[k]:
            p[k * k:n + 1:k] = b"\x00" * ((n - k * k) // k + 1)
    return p


def factor(n):
    result = []
    for d in range(2, isqrt(n) + 1):
        while n % d == 0:
            result.append(d)
            n //= d
    if n > 1:
        result.append(n)
    return result



```

#### joh_even_slots.py

```python
"""Preregistered JOH even-arrival tests; every floor decision is certified."""

from fractions import Fraction
import hashlib
import json
from joh_interval_base import SCALE, li_interval, log_rational, sieve, factor

END = 4096
DEVELOPMENT_END = 2048
prime = sieve(END)
assert all(bool(prime[n]) == (factor(n) == [n]) for n in range(2, END + 1))
floors = {2: 0}
margin = SCALE
width = 0
for n in range(3, END + 1):
    lo, hi = li_interval(n)
    assert lo // SCALE == hi // SCALE, (n, lo, hi)
    floors[n] = lo // SCALE
    margin = min(margin, lo - floors[n] * SCALE,
                 (floors[n] + 1) * SCALE - hi)
    width = max(width, hi - lo)

arrivals = {}
for n in range(3, END + 1):
    jump = floors[n] - floors[n - 1]
    assert jump in (0, 1)
    if jump:
        arrivals[floors[n]] = n

slots = []
for j, b in arrivals.items():
    if j % 2 or b < 5 or j + 1 not in arrivals:
        continue
    c = arrivals[j + 1]
    inside = [n for n in range(b + 1, c) if prime[n]]
    if prime[b] or prime[c] or len(inside) != 2:
        continue
    p, q = inside
    a = b + c - p - q
    assert abs(a) <= c - b - 4
    assert factor(p) == [p] and factor(q) == [q]
    assert len(factor(b)) >= 2 and len(factor(c)) >= 2
    slots.append(dict(j=j, b=b, p=p, q=q, c=c, area=a,
                      owners=[factor(b)[0], factor(c)[0]],
                      factors=[factor(b), factor(c)]))

events = [0] * (END + 1)
chambers = [0] * (END + 1)
for s in slots:
    b, p, q, c = (s[k] for k in ('b', 'p', 'q', 'c'))
    for k, sign in ((b, -1), (p, 1), (q, 1), (c, -1)):
        eta = int(prime[k]) - floors[k] + floors[k - 1]
        assert eta == sign and events[k] == 0
        events[k] = sign
    for n in range(b, p):
        assert chambers[n] == 0
        chambers[n] = -1
    for n in range(q, c):
        assert chambers[n] == 0
        chambers[n] = 1

count = 1
K = P = G = Gstar = Bstar = 0
compressed = placement = 0
prime_counts = {2: 1}
arrival_backlog = {}
current_arrival = None
compression_samples = []
compression_checks = 0
return_checks = quadratic_checks = 0
samples = []
for n in range(2, END + 1):
    if n >= 3:
        count += prime[n]
        eta = int(prime[n]) - floors[n] + floors[n - 1]
        K += events[n]
        Bstar += eta - events[n]
    B = count - floors[n] - 1
    prime_counts[n] = count
    if n in arrivals.values():
        current_arrival = n
        arrival_backlog[n] = B
    assert K == chambers[n] and abs(K) <= 1
    assert B == Bstar + K
    assert G == Gstar + P
    direct = sum(-max(n-s['b'], 0) + max(n-s['p'], 0)
                 + max(n-s['q'], 0) - max(n-s['c'], 0) for s in slots)
    assert P == direct and abs(P) <= n - 2
    assert G * G == Gstar * Gstar + 2 * Gstar * P + P * P
    assert abs(G * G - Gstar * Gstar) <= 2 * (n-2) * abs(Gstar) + (n-2)**2
    return_checks += 1
    quadratic_checks += 2
    if n in (144, 169, 1225, 1296, 2048, 4096):
        samples.append(dict(N=n, B=B, K=K, G=G, packet=P, complement=Gstar))
    if n >= 5:
        assert G == compressed + placement
        direct_placement = 0
        for j, b in arrivals.items():
            if b < 5 or b >= n:
                continue
            t = min(arrivals.get(j + 1, END + 1), n)
            direct_placement += sum(t-p for p in range(b+1, t) if prime[p])
        assert placement == direct_placement >= 0
        log_lo, _ = log_rational(n)
        assert placement * SCALE <= count * log_lo
        if n >= 17:
            assert 10 * placement <= 13 * n
        if n in (512, 1024, 2048, 4096):
            compression_samples.append(dict(N=n, G=G, sampled=compressed,
                                            placement=placement, pi=count))
        compression_checks += 1
        compressed += arrival_backlog[current_arrival]
        placement += count - prime_counts[current_arrival]
    G += B
    P += K
    Gstar += Bstar

Wrows = []
for X in range(5, END // 2 + 1):
    sub = [s for s in slots if X <= s['b'] and s['c'] <= 2 * X]
    W = sum(s['area'] for s in sub)
    abs_sum = sum(abs(s['area']) for s in sub)
    spans = sum(s['c']-s['b'] for s in sub)
    assert abs(W) <= abs_sum <= spans - 4 * len(sub) <= X - 4 * len(sub)
    Wrows.append(dict(X=X, W=W, count=len(sub), abs_sum=abs_sum,
                      spans=spans, j=[s['j'] for s in sub]))

def first_sign(rows, sign, field):
    return next((s for s in rows if sign * s[field] > 0), None)

def slot_summary(rows):
    return dict(count=len(rows), positive=sum(s['area'] > 0 for s in rows),
                zero=sum(s['area'] == 0 for s in rows),
                negative=sum(s['area'] < 0 for s in rows),
                sum_area=sum(s['area'] for s in rows),
                first_positive=first_sign(rows, 1, 'area'),
                first_negative=first_sign(rows, -1, 'area'))

result = dict(
    scope='FINITE_COMPUTATION; not an asymptotic sign or frequency theorem',
    certified_integers=[2, END],
    minimum_floor_margin=str(Fraction(margin, SCALE)),
    maximum_li_interval_width=str(Fraction(width, SCALE)),
    development=slot_summary([s for s in slots if s['c'] <= DEVELOPMENT_END]),
    held_out=slot_summary([s for s in slots if s['b'] > DEVELOPMENT_END]),
    boundary_straddlers=[s for s in slots if s['b'] <= DEVELOPMENT_END < s['c']],
    full=slot_summary(slots),
    first_positive_W=first_sign(Wrows, 1, 'W'),
    first_negative_W=first_sign(Wrows, -1, 'W'),
    dyadic_W=[r for r in Wrows if r['X'] & (r['X'] - 1) == 0],
    restored_prefix_samples=samples,
    return_checks=return_checks,
    quadratic_checks=quadratic_checks,
    dyadic_window_checks=len(Wrows),
    compression_checks=compression_checks,
    compression_samples=compression_samples,
    positive_dyadic_slots=[s for s in slots if 512 <= s['b'] and s['c'] <= 1024],
    witness_floor_values={n: floors[n] for n in (193, 194, 197, 199, 200,
                                               819, 820, 821, 823, 825, 826,
                                               2108, 2109, 2111, 2113, 2116, 2117)},
)
print(json.dumps(result, sort_keys=True, indent=2))
print('SLOT_DATA_SHA256', hashlib.sha256(json.dumps(slots, sort_keys=True).encode()).hexdigest())

```

#### Exact Output

```text
{
  "boundary_straddlers": [],
  "certified_integers": [
    2,
    4096
  ],
  "compression_checks": 4092,
  "compression_samples": [
    {
      "G": -2595,
      "N": 512,
      "pi": 97,
      "placement": 213,
      "sampled": -2808
    },
    {
      "G": -6703,
      "N": 1024,
      "pi": 172,
      "placement": 431,
      "sampled": -7134
    },
    {
      "G": -16599,
      "N": 2048,
      "pi": 309,
      "placement": 886,
      "sampled": -17485
    },
    {
      "G": -42284,
      "N": 4096,
      "pi": 564,
      "placement": 1765,
      "sampled": -44049
    }
  ],
  "development": {
    "count": 13,
    "first_negative": {
      "area": -2,
      "b": 194,
      "c": 200,
      "factors": [
        [
          2,
          97
        ],
        [
          2,
          2,
          2,
          5,
          5
        ]
      ],
      "j": 48,
      "owners": [
        2,
        2
      ],
      "p": 197,
      "q": 199
    },
    "first_positive": {
      "area": 2,
      "b": 820,
      "c": 826,
      "factors": [
        [
          2,
          2,
          5,
          41
        ],
        [
          2,
          7,
          59
        ]
      ],
      "j": 150,
      "owners": [
        2,
        2
      ],
      "p": 821,
      "q": 823
    },
    "negative": 4,
    "positive": 3,
    "sum_area": -5,
    "zero": 6
  },
  "dyadic_W": [
    {
      "W": 0,
      "X": 8,
      "abs_sum": 0,
      "count": 0,
      "j": [],
      "spans": 0
    },
    {
      "W": 0,
      "X": 16,
      "abs_sum": 0,
      "count": 0,
      "j": [],
      "spans": 0
    },
    {
      "W": 0,
      "X": 32,
      "abs_sum": 0,
      "count": 0,
      "j": [],
      "spans": 0
    },
    {
      "W": 0,
      "X": 64,
      "abs_sum": 0,
      "count": 0,
      "j": [],
      "spans": 0
    },
    {
      "W": -2,
      "X": 128,
      "abs_sum": 2,
      "count": 2,
      "j": [
        48,
        56
      ],
      "spans": 12
    },
    {
      "W": 0,
      "X": 256,
      "abs_sum": 0,
      "count": 1,
      "j": [
        94
      ],
      "spans": 6
    },
    {
      "W": 1,
      "X": 512,
      "abs_sum": 3,
      "count": 3,
      "j": [
        116,
        148,
        150
      ],
      "spans": 19
    },
    {
      "W": -4,
      "X": 1024,
      "abs_sum": 12,
      "count": 7,
      "j": [
        198,
        216,
        262,
        276,
        280,
        304,
        310
      ],
      "spans": 54
    },
    {
      "W": 3,
      "X": 2048,
      "abs_sum": 53,
      "count": 28,
      "j": [
        324,
        328,
        330,
        332,
        340,
        344,
        348,
        358,
        364,
        390,
        398,
        410,
        446,
        456,
        464,
        482,
        484,
        486,
        492,
        508,
        510,
        524,
        536,
        542,
        546,
        564,
        566,
        570
      ],
      "spans": 225
    }
  ],
  "dyadic_window_checks": 2044,
  "first_negative_W": {
    "W": -2,
    "X": 100,
    "abs_sum": 2,
    "count": 1,
    "j": [
      48
    ],
    "spans": 6
  },
  "first_positive_W": {
    "W": 1,
    "X": 413,
    "abs_sum": 3,
    "count": 4,
    "j": [
      94,
      116,
      148,
      150
    ],
    "spans": 25
  },
  "full": {
    "count": 41,
    "first_negative": {
      "area": -2,
      "b": 194,
      "c": 200,
      "factors": [
        [
          2,
          97
        ],
        [
          2,
          2,
          2,
          5,
          5
        ]
      ],
      "j": 48,
      "owners": [
        2,
        2
      ],
      "p": 197,
      "q": 199
    },
    "first_positive": {
      "area": 2,
      "b": 820,
      "c": 826,
      "factors": [
        [
          2,
          2,
          5,
          41
        ],
        [
          2,
          7,
          59
        ]
      ],
      "j": 150,
      "owners": [
        2,
        2
      ],
      "p": 821,
      "q": 823
    },
    "negative": 13,
    "positive": 12,
    "sum_area": -2,
    "zero": 16
  },
  "held_out": {
    "count": 28,
    "first_negative": {
      "area": -4,
      "b": 2124,
      "c": 2132,
      "factors": [
        [
          2,
          2,
          3,
          3,
          59
        ],
        [
          2,
          2,
          13,
          41
        ]
      ],
      "j": 330,
      "owners": [
        2,
        2
      ],
      "p": 2129,
      "q": 2131
    },
    "first_positive": {
      "area": 2,
      "b": 2109,
      "c": 2117,
      "factors": [
        [
          3,
          19,
          37
        ],
        [
          29,
          73
        ]
      ],
      "j": 328,
      "owners": [
        3,
        29
      ],
      "p": 2111,
      "q": 2113
    },
    "negative": 9,
    "positive": 9,
    "sum_area": 3,
    "zero": 10
  },
  "maximum_li_interval_width": "509517/1606938044258990275541962092341162602522202993782792835301376",
  "minimum_floor_margin": "150567783471251571167945556070712817530817720815572100393/1606938044258990275541962092341162602522202993782792835301376",
  "positive_dyadic_slots": [
    {
      "area": 0,
      "b": 597,
      "c": 603,
      "factors": [
        [
          3,
          199
        ],
        [
          3,
          3,
          67
        ]
      ],
      "j": 116,
      "owners": [
        3,
        3
      ],
      "p": 599,
      "q": 601
    },
    {
      "area": -1,
      "b": 806,
      "c": 813,
      "factors": [
        [
          2,
          13,
          31
        ],
        [
          3,
          271
        ]
      ],
      "j": 148,
      "owners": [
        2,
        3
      ],
      "p": 809,
      "q": 811
    },
    {
      "area": 2,
      "b": 820,
      "c": 826,
      "factors": [
        [
          2,
          2,
          5,
          41
        ],
        [
          2,
          7,
          59
        ]
      ],
      "j": 150,
      "owners": [
        2,
        2
      ],
      "p": 821,
      "q": 823
    }
  ],
  "quadratic_checks": 8190,
  "restored_prefix_samples": [
    {
      "B": -5,
      "G": -431,
      "K": 0,
      "N": 144,
      "complement": -431,
      "packet": 0
    },
    {
      "B": -5,
      "G": -553,
      "K": 0,
      "N": 169,
      "complement": -553,
      "packet": 0
    },
    {
      "B": -9,
      "G": -8392,
      "K": 0,
      "N": 1225,
      "complement": -8394,
      "packet": 2
    },
    {
      "B": -9,
      "G": -9055,
      "K": 0,
      "N": 1296,
      "complement": -9058,
      "packet": 3
    },
    {
      "B": -12,
      "G": -16599,
      "K": 0,
      "N": 2048,
      "complement": -16594,
      "packet": -5
    },
    {
      "B": -12,
      "G": -42284,
      "K": 0,
      "N": 4096,
      "complement": -42282,
      "packet": -2
    }
  ],
  "return_checks": 4095,
  "scope": "FINITE_COMPUTATION; not an asymptotic sign or frequency theorem",
  "witness_floor_values": {
    "193": 47,
    "194": 48,
    "197": 48,
    "199": 48,
    "200": 49,
    "819": 149,
    "820": 150,
    "821": 150,
    "823": 150,
    "825": 150,
    "826": 151,
    "2108": 327,
    "2109": 328,
    "2111": 328,
    "2113": 328,
    "2116": 328,
    "2117": 329
  }
}
SLOT_DATA_SHA256 e9b1ab26ae9cae521490e754bd40b1af202c6f3cefc7c8b1503ef4bca86f4b2e

```


### Verified Publication Receipt - 2026-11-04 16:32 EST

**Execution COMPLETE; substantive publication PUBLISHED_AND_READBACK_VERIFIED.** The complete LC1-LC5 synthesis, A-K sections, exact certificates/output, source/continuity ledger and specialist handoffs were published in commit **a61a3061d46162455737c642c5bdd04162ba5977**, at 2026-11-04T21:32:05Z. Immutable-commit readback matched all **157316 characters** exactly, blob **e20bef70743ed5555737a2951f04e9937d50e11c**. GitHub commit inspection confirms exactly this authorized Owner report changed, with **1205 additions and zero deletions**. The entire prior report and early checkpoint remain an unchanged prefix.

Main was rechecked before publication and remained **1daca8d582c361983567f0b6e99d447a77c3aea5**; no open or draft PR was returned. Every other November 4 upstream report retained its intake blob at the final directory refresh. The latest branch version was freshly fetched again before this receipt and matched the verified synthesis. This receipt records the preceding verified publication, not its own future commit; its own readback is checked after writing.

New mathematical status remains **PAPER_PROOF / SELF_AUDIT**, with **FINITE_COMPUTATION** and the specifically **REFUTED** universal sign assertions. Independent review and Lean formalization are PENDING. The complete sampled count-history bound, new endpoint exponent, canonical VF bound and RH remain OPEN. No source or policy edit, other-report change, agent launch, local Lean execution, PR/workflow mutation, merge, permission or schedule change occurred.

# RH | Owner Payment - 2026-11-05

## A. Most Important Mathematical Development

**IN_PROGRESS / PARTIAL.** No new theorem is asserted yet. This invocation resumes the genuine SAT growing-band interior correlation OPEN-SAT-I from 20261104-owner-1, S1-S4 and section J. The candidate is to exploit genuine multiplicative or convolution cancellation before taking absolute values, retaining both Mertens endpoint weights and the full smooth/unselected-layer complement. A second possibility is a rigorous obstruction showing why a proposed local prime-factor pairing does not control this source.

Actual invocation: scheduled 2026-11-05 00:09 EST (-0500), America/New_York; RUN_ID_UNAVAILABLE. Claim reserved: **20261105-owner-1**. This is the early checkpoint for one actual invocation, not an additional run.

## B. Current Authoritative Objective

Pinned main: **ff620da3c0d2c29585805960c6be183c07f16556**. AGENTS blob **547dda0d9456e7a4e1165dc72d59da6f70d5c023**; proof contract blob **7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c**; independent multi-front policy blob **ffd8f1c65cc4da656174956d4e03b48bea46768b**.

Canonical actual-prime objective remains:
`exists C>=0, forall natural R>=2, |pi(R^2)-vfCanonical(R^2)| <= C R log R`.

SAT source: q=2R, Y=q^2-1, D=floor(sqrt R), B=2D-1, x_d=floor(Y/d), Delta=pi-Li_2. The original band is
`T_R=-sum_(D<=d<=B) M(d)[pi(x_d)-pi(x_(d+1))]`.
Exact return:
`M(Y)=T_R+C_R=L_R+E_R+C_R`,
with C_R the actual smooth population and every unselected reciprocal layer, and
`E_R=-M(D)[Delta(x_D)-Delta(x_(2D))]-I_R`,
`I_R=sum_(D<d<2D)mu(d)[Delta(x_d)-Delta(x_(2D))]`.
The complete square retains all six model/error/complement terms.

Original source blobs inspected:
- LargePrimeTerminalFlipLayers.lean: b7617df21b81002854a0d311ef7e02d9494154c3.
- SquareRootPostCrossingTail.lean: 660772bad3663d14c0f3390e26925b57d1390080.
- PNT_FIRST_LAMBDA_HYPERBOLA_ANCHOR_20261018.lean: c67797ae7cda0ad9a7c393c69715016685a14d0a.
- VF919NativeStrictMertens.lean: b33a4883e1ddb0551b0f11f062bce46680d87450.
- VF_CANONICAL_SQRT_TWO_VON_KOCH.lean: 79030d70e8d3e0d08eef9bac53fef95c36eca2fb.

## C. Continuity And Selected Hypothesis

TODAY=PENDING for upstream reports at intake; YESTERDAY=CARRY_FORWARD. November 4 report bytes for all seven roles and the external inbox were retrieved. Owner's completed order was SAT owner-1, VF-LOW owner-2, JOH owner-3; SAT is next. Latest Coordinator C49-C52 preserves this rotation. Its Nyman separate-correction obstruction is a useful warning about genuine mixed cancellation, not an input to the SAT bound. External inbox remains blob 038018145c0fddb2f6306c0712373adf9cd1ea52.

Prior SAT result S3: from the unchanged fixed genuine Mertens envelope b=7/8, E_R=O(R^(11/6)); OPEN-SAT-I asks for an independent positive power improvement of the centered interior. The separately bounded endpoint has exponent 85/48, still above terminal 7/4. No endpoint gain is claimed.

Live open/draft PR collection: empty. Newly merged #1093 is Nyman flat-taper complete return at main; #1090 and #1091 are also merged. Historical claims that #1085 or #1087 remain drafts are superseded by actual merged metadata. None of those different-carrier results pays OPEN-SAT-I.

deployment_ack: NO_PIGEONHOLING_ROUTE_SELECTOR_V1 consumed at the pinned main; independently chosen due SAT route. No compulsory OAI audit or tiny-slot optimization. SEARCH_BROAD for new work; inherited previously verified strict-slot theorem is not erased or reproved.

## D. Derivation And Falsification Plan

Attempt exact multiplicative pairing / divisor-convolution control of I_R before using a generic variation bound. Compare any gain with the paid 11/6 bound at the SAME fixed b. Test exceptional repeated factors, actual moving prime admission, both endpoints, squareful zeros, and complete return. Small exact development roots 16..36 and held-out 64,65,127,128 are reserved only for NEW identities or falsifiers, not to repeat yesterday's accepted sign census.

## E-K. Pending Research And Publication

Full proof or first unsupported inequality, quantitative consequence, falsification, conceptual interpretation, competing hypotheses, specialist handoffs and continuation capsule will be appended to this same file. Independent review and any new Lean verification are PENDING. No local Lean, source edit, PR/issue edit, agent launch, merge or schedule action is authorized or performed.

Direct shell GitHub fetch failed with HTTP 403; connected GitHub reads work. Publication is claimed only after commit inspection and exact readback.


## Final Research Synthesis - 20261105-owner-1

This completes the scheduled 2026-11-05 00:09 EST invocation. RUN_ID_UNAVAILABLE. New claims RC1-RC5 are **PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED**. RC6 is **FINITE_COMPUTATION**. The early checkpoint above remains preserved. Publication is verified in the receipt appended after the synthesis.

### A. Most Important Mathematical Development

**The actual growing SAT band contains a rigid semiprime population that no small-prime-only cancellation can remove. Nevertheless, the known Mertens envelope forces substantial compensation between different remaining factor groups.** The two statements are compatible and quantitatively explicit.

Let W_R be ANY finite set of primes at most D=floor(sqrt R), allowed to vary arbitrarily with R. Group the genuine physical integers in the band by the integer left after removing all W_R-prime factors. After optimal opposite-sign cancellation inside each group, the remaining absolute mass V_R(W_R) satisfies

~~~text
V_R(W_R) >= N_R,
N_R ~ R^2/(3 log^2 R).                                    (RC1-RC2)
~~~

This is a lower bound on a specified absolute-remainder certificate, **not on |T_R|, |I_R|, |M(Y)|, or the original #915 NNS statistic**. From the unchanged genuine input |M(n)|<=C n^b, 0<b<1, one also has

~~~text
|T_R| << R^((3+b)/2)/log R,
min(P_R^+,P_R^-) >= (1-o(1)) R^2/(6 log^2 R),
0 <= 1+rho_R^core << R^(-(1-b)) log^2 R,                  (RC3)
~~~

uniformly over those W_R. Here P_R^+,P_R^- are the positive and negative magnitudes of the complete grouped band, and rho_R^core is defined exactly in D3. At b=7/8 the last exponent is -1/8. This is a **baseline-derived signed restriction on this particular complete band**, not a new Mertens bound or assumed zero covariance.

**The same packet has an exact quantitative inverse criterion.** Let Z_R be its prime-minus-Li_2 discrepancy, defined in D4. For every fixed 2/3<sigma<1, the following three statements are equivalent, each with every positive exponent loss:

~~~text
Delta(x) = O_epsilon(x^(sigma+epsilon))                  (all real x>=2);
Z_R = O_epsilon(R^(1/2+3sigma/2+epsilon))                (all integer R>=16);
Z_(N^2) = O_epsilon(N^(1+3sigma+epsilon))                (all integer N>=4).
                                                                    (RC5)
~~~

Thus a separate packet bound Z_R=O_epsilon(R^(11/6-kappa+epsilon)), 0<kappa<1/3, already has exactly the ordinary prime-error demand sigma=8/9-2kappa/3. The rounded 7/8 boundary corresponds to kappa=1/48. This is **TARGET_EQUIVALENT to the displayed prime-error envelope**, not to the canonical RH target and not a proof of either upper bound.

OPEN-SAT-I remains OPEN. A bound for the whole I_R does not imply a bound for Z_R alone: the remaining signed terms can cancel it. The development rejects an incomplete small-prime pairing method and identifies the true arithmetic content of one possible separate-payment repair; it does not reject joint cancellation.

### B. Current Authoritative Objective

Main at intake: **ff620da3c0d2c29585805960c6be183c07f16556**, the human merge of #1093. The canonical actual-prime objective remains

~~~text
exists C>=0, forall natural R>=2,
  |pi(R^2)-vfCanonical(R^2)| <= C R log R.
~~~

The inspected canonical consumer still takes ClassicalVonKochRHCriterion explicitly. The established VF_can-Li_2 coordinate bridge is not this open bound.

**Route selected:** SAT, resuming 20261104-owner-1/S1c and OPEN-SAT-I, as independently warranted by the protected rotation and Coordinator 20261104-coordinator-3, section H. Newest routing is NO_PIGEONHOLING_ROUTE_SELECTOR_V1. No unrelated OAI source audit or tiny-slot optimization is imposed.

#### Material Source Ledger

All listed source contents were fetched at the pinned main; the declarations relevant to this argument were inspected.

| Source | Blob SHA | Role |
| --- | --- | --- |
| AGENTS.md | 547dda0d9456e7a4e1165dc72d59da6f70d5c023 | Authority and own-report-only permissions |
| CURRENT_PROOF_CONTRACT.md | 7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c | Canonical target and complete-source safeguards |
| Independent multi-front policy | ffd8f1c65cc4da656174956d4e03b48bea46768b | Current task selection |
| Stable task selector | 4fbab59cc6fcc33a4f4e7a8ef447b2f7947b53dd | Protected route continuation |
| Broad-search policy | 8317f08996b65f2e4b32c00c91b31cb6d0c09718 | Independent full-return gain gate |
| Complete-return contract | 4775ee5fd95f279beab08a75d1e17127078b19a6 | Exact source and signed reconstruction |
| Research engine | 6c1d1c10e2755017ffe9d7f40df8b9ae7692f23a | Resumable investigations |
| Current role prompts | 53143573cd5b014178d11ded008dbfb1a7e6dcc5 | Owner role and no autonomous launches |
| Dynamic protocol | 23b6fae1d3b6b5a69155628df709d255aea7aeca | Publication and evidence discipline |
| RHLean/Proof/LargePrimeTerminalFlipLayers.lean | b7617df21b81002854a0d311ef7e02d9494154c3 | Literal packet, true terminal sign and Abel theorem |
| RHLean/Analysis/SquareRootPostCrossingTail.lean | 660772bad3663d14c0f3390e26925b57d1390080 | Complete smooth/transport return, conditional consumer |
| RHLean/Proof/PrimeSieveSquareRootTransport.lean | 721b7f557ea9f253598b1ae3508f31d9f10a9f4f | Existing arbitrary-prime compression; not rediscovered |
| RHLean/Analysis/SquareRootTransportTopFibreNoGo.lean | fcc63e7bcb6927122075c39ccacaca445685729e | Existing top-prime obstruction; distinguished below |
| RHLean/Proof/LowWheelFrozenSecondContactRoughPrefix.lean | 1dfcff95e9f9bba337626dc06c73cf5f28c4e826 | Different admitted carrier; no unsupported transfer |
| research/PNT_FIRST_LAMBDA_HYPERBOLA_ANCHOR_20261018.lean | c67797ae7cda0ad9a7c393c69715016685a14d0a | Existing full convolution and overlap safeguards |
| research/oai_434/VF919NativeStrictMertens.lean | b33a4883e1ddb0551b0f11f062bce46680d87450 | native_mertens_fixed_strict_power; existing input only |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb | Canonical definition and explicit classical interface |

The source theorem native_mertens_fixed_strict_power supplies an existential fixed power below 7/8. Weakening it gives the fixed b=7/8 envelope used in RC3. This run neither reproves that theorem nor claims its positive margin is renewable. New gains are evaluated separately from the inherited strict-slot result.

#### Current PR And Verification Evidence

The live open/draft collection returned no entries. #1093 is merged, final proof head **a54f0cf9535c548920dae3412e3fbe6d6584e029**. All **12** returned workflows at that head were freshly checked as completed/success, including dedicated Nyman run **41955044802** and targeted iteration **41955044794**. Lean's prior report gives the exact theorem, standard axioms and synthetic-merge tree match; those log details are carried forward, not falsely called a new log audit here.

Recent merged work also includes #1092 routing, #1091 fixed-slot endpoint, #1090 Nyman high-coefficient invariant, #1087 and #1085 original LOW moving-mass work. Their old draft descriptions are historical. None supplies OPEN-SAT-I, and no local Lean or new CI was executed.

### C. Structural Hypotheses Investigated

1. **Local multiplicative cancellation.** Perhaps toggling small prime factors through complete admitted cofactor fibres leaves a sufficiently small boundary. Existing prime-dilate compression already gives the exact one-prime identity. RC1-RC2 test the stronger claim after arbitrary cancellation inside any small-prime-deleted core, even with a growing wheel.
2. **Joint signed compensation.** If local cancellation is insufficient, does the genuine source force compensation between the remaining groups? RC3 answers yes at the known input exponent, while explicitly retaining the whole square.
3. **Separate centered-packet payment.** Perhaps the rigid positive packet becomes a harmless error after its exact Li_2 model is subtracted. RC4 gives the correct subtraction; RC5 identifies the full all-scale analytic strength of improving that error separately.

These are different moves: finite prime-factor conservation, a signed global consequence of the existing input, and an inverse sampling/telescoping theorem. No independence of mu and primes is assumed.

### D. Mathematical Derivation

#### D0. The Exact Original Carrier

For integer R>=16 put

~~~text
q=2R, Y=q^2-1, D=floor(sqrt R), B=2D-1, x_d=floor(Y/d),
P_band={prime p: x_(2D)<p<=x_D},
Omega_R={(p,c): p in P_band, 1<=c<=floor(Y/p)}.
~~~

Every owner p is strictly above q: Y>=4RD implies x_(2D)>=q. Its quotient is in [D,B], and c<p. Thus the original source theorem gives mu(pc)=-mu(c), including zero weights for squareful c. Two different owners cannot produce the same physical integer below Y, because their product would exceed q^2>Y. The unit cofactor and all squareful-zero terms are retained.

The actual band is

~~~text
T_R=sum_((p,c) in Omega_R) mu(pc)
   =-sum_(D<=d<=B) M(d)[pi(x_d)-pi(x_(d+1))]
   =squareRootTruncatedUpperMiddlePacket(q,B)
     -squareRootTruncatedUpperMiddlePacket(q,D-1).
~~~

Its exact model and error are L_R and E_R from the earlier report:

~~~text
L_R=-sum_(D<=d<=B) M(d)[Li_2(x_d)-Li_2(x_(d+1))],
E_R=T_R-L_R=-A_R-I_R,
A_R=M(D)[Delta(x_D)-Delta(x_(2D))],
I_R=sum_(D<c<2D) mu(c)[Delta(x_c)-Delta(x_(2D))].
~~~

Here Delta=pi-Li_2 and Li_2(x)=integral_2^x dt/log t. Nothing is centered by an empirical mean.

Let A_q(Y) sum mu(n) over all n<=Y with largest prime factor at most q, including n=1. Define the full original complement

~~~text
C_R=A_q(Y)+P_q(D-1)+[P_q(q-1)-P_q(B)],
P_q(K)=squareRootTruncatedUpperMiddlePacket(q,K).
M(Y)=T_R+C_R=L_R+E_R+C_R.                                (RETURN)
~~~

This retains every unselected reciprocal layer, the prime-only layer and the smooth population. It is not the masked #915 VF source.

#### D1. RC1: A Rigid Semiprime Rectangle

Define

~~~text
ell_R=floor(Y/(2D)), u_R=floor(3Y/(4D)),
Cprime_R={prime c: D<c<=5D/4},
Pprime_R={prime p: ell_R<p<=u_R},
a_R=#Cprime_R, b_R=#Pprime_R,
N_R=a_R*b_R.
~~~

**Theorem RC1.** Every pair (p,c) in Pprime_R x Cprime_R is an actual distinct member of Omega_R and has

~~~text
Y/2 < pc <= 15Y/16,       mu(pc)=+1.                     (RC1a)
~~~

For a finite prime set W, let core_W(n) be n with every factor belonging to W removed, with its full valuation. If W contains neither p nor c, the physical integer n=pc is the only positive integer at most Y with core_W equal to n. Consequently it is a singleton in the actual source, not merely in the chosen rectangle.

**Proof.** The strict lower bounds p>Y/(2D) and c>D give pc>Y/2. The upper bounds give pc<=(3Y/(4D))*(5D/4)=15Y/16. The bounds on p put floor(Y/p) between D and 2D-1; pc<=Y admits c. Also c<p, so the two factors are distinct primes and mu(pc)=1. Unique factorization and p>q prove injectivity. If core_W(n')=pc with p,c outside W, then n'=pc*t for a W-smooth positive integer t. If t>=2, n'>Y. Thus t=1 and n'=pc. This argument preserves the actual endpoint, multiplicity and source admission; an eligible partner outside Y is not admitted.

The finite rectangle may be empty at small D. No nonemptiness is asserted at every R.

#### D2. RC2: Sharp Within-Core Residual And A Growing-Wheel Barrier

For the nonzero original physical occurrences define

~~~text
g_R(a;W)=sum_(n in Omega_R, core_W(n)=a) mu(n),
V_R(W)=sum_a |g_R(a;W)|,
T_R=sum_a g_R(a;W).
~~~

The notation n in Omega_R uses the proved unique physical-integer map, not a new population.

**Conservation theorem.** Any removal of disjoint opposite-sign pairs, or any zero-sum packets, confined to individual cores leaves absolute mass at least V_R(W). For unit-weight original occurrences this minimum is attained by pairing positive and negative signs inside each core. Indeed if a class contains h positive and k negative terms, any cancellation preserves h-k and leaves at least |h-k| terms; pairing min(h,k) attains equality. No historical term or physical occurrence is reused.

If W is supported on primes at most q, none of the rectangle owners belongs to W. RC1 gives the sharper necessary inequality

~~~text
V_R(W) >= b_R * #{c in Cprime_R: c notin W}.              (RC2a)
~~~

In particular, for ANY W_R supported at most D, even a scale-dependent set of arbitrary size,

~~~text
V_R(W_R) >= N_R.                                        (RC2b)
~~~

The only external quantitative input for counting the rectangle is the ordinary prime number theorem pi(t)~t/log t. Apply it separately to the two fixed-ratio intervals; floor changes alter counts by at most a constant. This gives

~~~text
a_R ~ D/(4 log D),
b_R ~ Y/[4D log(Y/D)],
N_R ~ Y/[16 log D log(Y/D)]
    ~ R^2/(3 log^2 R).                                  (RC2c)
~~~

The theorem and normalization were checked against [NIST DLMF 27.2.3](https://dlmf.nist.gov/27.2.E3) and [DLMF 27.12](https://dlmf.nist.gov/27.12). No short-interval PNT or quantitative error term is imported. All wheel uniformity is pointwise in RC2b, so its constants do not depend on the size, variation or product of W_R.

For every fixed delta>0, no such V_R(W_R) is O(R^(2-delta)). Therefore a proof consisting only of these cancellations followed by a triangle inequality cannot produce the desired subquadratic absolute certificate. This refutes that METHOD, not the band bound or OPEN-SAT-I.

**Inverse coverage restriction.** If a larger W_R, still supported at most q, is claimed to give V_R(W_R)<<R^(theta+epsilon), theta<2, then RC2a and PNT force

~~~text
#{c in Cprime_R: c notin W_R}
    << R^(theta-3/2+epsilon) log R,
missing fraction << R^(theta-2+epsilon) log^2 R.         (RC2d)
~~~

Thus any such pairing certificate must admit nearly all primes from this cofactor-scale interval, or stop using only within-core absolute remainder. Near-complete coverage is NECESSARY, not sufficient. The hypothesis that rectangle owners are outside W is essential.

The full square is preserved:

~~~text
T_R^2=sum_a g_R(a)^2 + 2 sum_(a<b) g_R(a)g_R(b).          (RC2e)
~~~

If the complete ordered square is also grouped by its two cores and each class is normed separately, its total variation is V_R(W)^2, at least N_R^2. This remains a certificate lower bound, never a lower bound on T_R^2. Cross-core signs are not disposable.

#### D3. RC3: The Existing Input Forces Cross-Core Compensation

Assume the genuine prefix envelope |M(n)|<=C n^b for a fixed 0<b<1. On the original band, floor(Y/p)<=2D, so

~~~text
|T_R| <= C(2D)^b * #P_band
      <<_(b,C) D^b * Y/[D log(Y/D)]
      <<_(b,C) R^((3+b)/2)/log R.                        (RC3a)
~~~

Only the elementary upper consequence of PNT and the known source envelope are used. No unsigned count is substituted for T_R itself.

For any W_R supported at most D set

~~~text
P_R^+=sum_a max(g_R(a),0),
P_R^-=sum_a max(-g_R(a),0),
V_R=P_R^++P_R^-,   T_R=P_R^+-P_R^-.
~~~

RC2 and RC3a imply |T_R|/V_R << R^(-(1-b)/2) log R ->0, uniformly over W_R. Hence

~~~text
min(P_R^+,P_R^-)=(V_R-|T_R|)/2
 >= (N_R-|T_R|)/2
 >= (1-o(1)) R^2/(6 log^2 R).                           (RC3b)
~~~

Both signs must eventually carry this much mass after even optimal small-prime cancellation. In particular, the rigid positive packet is compensated outside its core classes. Define, for the resulting nonzero denominator,

~~~text
rho_R^core=-2P_R^+P_R^- / [(P_R^+)^2+(P_R^-)^2].
1+rho_R^core=T_R^2/[(P_R^+)^2+(P_R^-)^2]
           <=2T_R^2/V_R^2
           << R^(-(1-b)) log^2 R.                       (RC3c)
~~~

The complete identity T_R^2=(P_R^+)^2+(P_R^-)^2-2P_R^+P_R^- is the justification. There is no omitted cross term, phase randomization or independent-sign hypothesis.

At the inherited fixed b=7/8, RC3a gives 31/16 and RC3c gives -1/8. This is a new source-specific consequence of the already paid prefix envelope plus the rigid-core population, not new independent cancellation improving that envelope. rho_R^core is neither the repository's original #915 NNS statistic nor yesterday's root/smooth rho. No finite exact zero-covariance assertion is made.

#### D4. RC4: Restore The Prime Model Before Interpreting The Obstruction

The rectangle's genuine mass is N_R. Its exact allocated Li_2 model and error are

~~~text
F_R^rect=a_R[Li_2(u_R)-Li_2(ell_R)],
Z_R=N_R-F_R^rect
   =a_R[Delta(u_R)-Delta(ell_R)].                        (RC4a)
~~~

This model is an actual subset of the existing model allocation. Expanding L_R by cofactors gives

~~~text
L_R=-M(D)[Li_2(x_D)-Li_2(ell_R)]
    -sum_(D<c<2D) mu(c)[Li_2(x_c)-Li_2(ell_R)].
~~~

For every c in Cprime_R, u_R<=x_c and mu(c)=-1. Split that same original interval at u_R. Therefore no new density model, weight or prime occurrence has been introduced.

Define the remainder by deleting precisely these rectangle subintervals from the cofactor-prime/model integrals. Then

~~~text
T_R=N_R+T_R^rem,    L_R=F_R^rect+L_R^rem,
E_R=Z_R+E_R^rem,    I_R=-Z_R+I_R^rem,
E_R^rem=-A_R-I_R^rem.                                   (RC4b)
~~~

Equivalently, use the signed measure dnu=dpi-dt/log t on the original interval (ell_R,x_c]; remove (ell_R,u_R] only when c belongs to Cprime_R. This defines I_R^rem explicitly rather than calling an unspecified error small.

If an available genuine prime-error envelope is |Delta(x)|<<x^alpha, alpha>0, then

~~~text
|Z_R| << a_R (Y/D)^alpha
       << R^((1+3alpha)/2)/log R.                       (RC4c)
~~~

Using the carried-forward paper S2 with the unchanged b=7/8 gives alpha=8/9 and |Z_R|<<R^(11/6)/log R. This is a supporting consequence, not a newly proved fixed kappa. The S2 transfer retains its prior PAPER_PROOF / review-pending status; RC4c itself is an immediate implication from the explicitly displayed prime-error premise.

Thus the large N_R and its singleton signs do NOT prove Z_R large. The actual prime-model compensation has been restored.

Every original quadratic term remains:

~~~text
M(Y)^2=L_R^2+E_R^2+C_R^2
       +2L_R E_R+2L_R C_R+2E_R C_R,
E_R^2=Z_R^2+(E_R^rem)^2+2Z_R E_R^rem.                   (RC4d)
~~~

The full band, error and terminal source must not be replaced by a sum of selected squares.

#### D5. RC5: A Separate Packet Rate Is Exactly An Ordinary Prime-Error Rate

**Theorem.** Fix 2/3<sigma<1. The three all-positive-loss statements in A are equivalent. Constants may depend on sigma and the positive loss, never on x, R or N. It is sufficient in the third statement to assume every sufficiently large integer N, not merely an arbitrary unbounded subsequence.

**Forward implication.** Under Delta(x)=O_epsilon(x^(sigma+epsilon)), RC4a and a_R<=D, Y/D comparable to R^(3/2), give

~~~text
|Z_R| << R^(1/2+3sigma/2+epsilon).
~~~

Choose the input loss small enough to pay the factor 3/2. This proves the all-R statement; substituting R=N^2 proves the cubic-sampling statement.

**Inverse implication: exact endpoints.** At R=N^2, D=N and Y=4N^4-1, so

~~~text
ell_(N^2)=2N^3-1,       u_(N^2)=3N^3-1,
Z_(N^2)=[pi(floor(5N/4))-pi(N)]
          *[Delta(3N^3-1)-Delta(2N^3-1)].                (RC5a)
~~~

The cofactor factor is at least c N/log N for all sufficiently large N by the ordinary PNT. Dividing the assumed cubic-sampling bound, and absorbing a logarithm into an arbitrarily small loss, gives for every eta>0

~~~text
|Delta(3N^3-1)-Delta(2N^3-1)|
    <<_eta N^(3sigma+eta).                              (RC5b)
~~~

No sharper PNT error is assumed in this division.

**Interpolate the true moving sample.** Put t_N=2N^3-1. The gap is exactly

~~~text
t_(N+1)-t_N=6N^2+6N+2=O(t_N^(2/3)).
~~~

For arbitrary real x>=t_4 choose the integer N with t_N<=x<t_(N+1). Both x-t_N and |(3/2)x-(3N^3-1)| are O(x^(2/3)). For any u,v>=2, actual integer prime counting and the Li_2 integral give the deterministic inequality

~~~text
|Delta(u)-Delta(v)|
 <= |u-v|+1+|u-v|/log 2.                                (RC5c)
~~~

This restores every intermediate prime and endpoint; it does not assume prime-gap regularity. Combining RC5b-c and choosing eta appropriately yields

~~~text
Delta((3/2)x)-Delta(x)=O_epsilon(x^(sigma+epsilon)),       (RC5d)
~~~

because sigma>2/3. The proof does not claim the same sampling deduction below 2/3.

**Telescope, without a hidden limiting constant.** Descend from x by the fixed factor 3/2 until reaching a fixed compact interval [x_0,(3/2)x_0). Sum RC5d over these scales. Since sigma+epsilon>0, the sum of their powers is a convergent geometric majorant times x^(sigma+epsilon); Delta is bounded on the compact remainder. Thus Delta(x)=O_epsilon(x^(sigma+epsilon)) for every real x>=2. This proves the inverse and all three equivalences.

**Exponents and actual relevance.** With sigma=8/9-2kappa/3,

~~~text
1/2+3sigma/2=11/6-kappa;
kappa=1/48 corresponds to sigma=7/8;
0<kappa<1/3 keeps sigma>2/3.                             (RC5e)
~~~

For example kappa=1/24 would demand sigma=31/36. This is a one-to-one comparison of the named packet rate with an ordinary prime-error rate, not a proof that either rate is false or independently missing at every kappa. Existing stronger analytic transfers may already pay some parameter range. To beat an actual inherited strict boundary 7/8-delta_0, the comparison requires kappa>1/48+3delta_0/2; merely beating the rounded 7/8 label is not enough.

Most importantly, RC5 applies to a SEPARATE Z_R estimate. The original interior can have I_R^rem approximately Z_R. No inference from a bound for I_R to a bound for Z_R is licensed. The theorem therefore diagnoses a proof architecture, not a necessary standalone bill for every valid SAT proof.

### E. Quantitative Consequence

| Result | Established scope | Not established |
| --- | --- | --- |
| RC1-RC2 | Actual semiprime singleton conservation; V_R(W)>=N_R~R^2/(3 log^2 R), uniformly for W supported at most D | No lower bound on the actual signed band or centered error |
| RC3 | Forced cross-core compensation from the SAME known Mertens exponent; 1+rho_R^core=O(R^(-1/8)log^2 R) at b=7/8 | No new input exponent and no original #915 NNS identification |
| RC4 | Exact prime/model allocation; conditional proper-sector error O(R^(11/6)/log R) from carried S2 | No fixed positive saving for I_R |
| RC5 | Exact all-scale rate equivalence at 2/3<sigma<1; cubic mesh and complete endpoint restoration | No proof of a stronger ordinary prime-error envelope |
| Complete original return | M(Y)=L_R+E_R+C_R, all cross terms retained | No new Mertens exponent, canonical VF estimate or RH |

This run supplies a **proof-method obstruction, a baseline-derived signed restriction, and a target-equivalent proper-sector inverse criterion**. It supplies no independent quantitative improvement to the unresolved full estimate. NEW_NET_ENDPOINT_GAIN=NONE; the stronger endpoint remains UNKNOWN / OPEN.

### F. Falsification And Circularity Review

#### Exact Computation

The first roots were fixed as 16..36, with held-out 64,65,127,128. R=256 was added explicitly before its computation to test partial wheel coverage when the cofactor rectangle contains two primes, 17 and 19. This was not an undisclosed exponent scan.

The final executed integer verifier checks:

- 26 roots and 38,371 actual physical occurrences, including squareful zeros and the genuine once-only owner.
- 1,425 rectangle occurrences, including strict Y/2 and closed 15Y/16 bounds.
- 346 wheel instances: every subset of primes at most D, larger admissible wheel controls, and partial cofactor coverage.
- Explicit within-class attaining matchings, unique leftover occurrence IDs and all forced singletons.
- Independently accumulated diagonal and ordered off-diagonal terms, complete band/complement square and exact prime-2 compression.
- 26 exact Li-model partitions as formal linear combinations of Li_2(integer); no numerical Li values or unproved signs.
- 192 exact cubic-mesh endpoint checks and four rational exponent checks.
- Independent trial-factorization verification of mu and largest prime factor for 1..2048.

The script and Python syntax check exited successfully. These finite tests do not certify PNT, the asymptotic limits or the all-scale inverse theorem.

| R | Rectangle N_R | V_R(all primes<=D) | T_R | Complete C_R | M(Y) |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 16 | 12 | 33 | 33 | -37 | -4 |
| 25 | 0 | 75 | 75 | -76 | -1 |
| 36 | 35 | 109 | 109 | -111 | -2 |
| 64 | 0 | 275 | 255 | -287 | -32 |
| 127 | 176 | 744 | 712 | -744 | -32 |
| 128 | 178 | 753 | 723 | -709 | 14 |
| 256 | 882 | 2804 | 1710 | -1686 | 24 |

**Smallest declared scope controls.** At R=16, n=5*131=655 is a genuine positive singleton for W={2,3}. Its proposed doubled partner 1310 exceeds Y=1023 and is not admitted. If W is enlarged to {2,3,5}, n=655 and the original negative prime occurrence 131 have the same core and can cancel; the exclusion of the cofactor prime is essential. The lower-half pair 131 and 262 cancels for W={2}, showing why pc>Y/2 matters. The admitted squareful-zero occurrence 524=4*131 remains zero.

The rectangle count is 12 but |M(1023)|=4. Thus promoting the certificate lower bound to a lower bound on the terminal magnitude is **REFUTED** on the declared original source. The complete square is 33^2+(-37)^2+2*33*(-37)=16, not at least 12^2.

#### Prior Work And Duplication Audit

The arbitrary-prime shell compression is already compiled in PrimeSieveSquareRootTransport; it is explicitly reused, not claimed as new. The compiled top-fibre no-go concerns quotient depth one and primes above Y/2. That population is absent from this growing-depth band. RC1 instead uses distinct semiprimes in the actual D..2D-1 layers and is uniform over a growing set of cancelled small primes.

Wheel 20261104-wheel-3/QC1-QC3 concerns rational square classes of the complete lifted ordered square. RC2 concerns deletion of specified small primes in this different, actual SAT carrier; these equivalence relations and estimates are not identified. Its useful warning about absolute-remainder certificates is retained. Existing low-wheel frozen rough-prefix identities have their own tagged transport carrier and do not automatically admit these SAT partners.

Targeted main code searches for the combined packet/semiprime and rough-core/rectangle terms returned no matches. That is a limited nonduplication check, not an exhaustive historical or literature novelty claim. The underlying factorization, PNT, Abel and geometric-telescope ingredients are standard; the new contribution is their precise source-specific combination and quantitative consequences.

#### Self-Audit

Every new arithmetic occurrence is an actual pc in the original source. Both strict prime thresholds, all cofactor weights, zero weights, unique owner, original model, endpoint and complement are preserved. No historical source is cloned. The lower bound is on a method's retained total variation, not on an unproved signed norm. RC3 consumes the already established input and is not an independent supplier improving it. RC5 assumes the candidate bound only to prove its precise implication and converse; neither antecedent is silently promoted to a theorem.

No empirical covariance or exponent fit is used. The cubic interpolation error is paid, and every sufficiently large N is required. No sparse-subsequence or sigma<=2/3 extension is claimed. No zeta-to-prime or prime-to-Mertens quantitative bridge beyond the inspected/input statements is silently imported.

### G. Conceptual Interpretation

Small-prime factor operations can remove many exact parent-child pairs, but the cutoff concentrates a positive population in the top physical half, where any further multiplication leaves the source. This obstruction survives arbitrary growth of the wheel as long as its prime support stays below the cofactor interval.

The obstruction does not make the whole band positive. On the contrary, the existing input forces large negative compensation in other factor groups. The difference between local cancellation and complete cancellation is therefore a proved feature of this genuine source, not a heuristic.

Subtracting the correct prime model changes the question again. A coherent same-sign semiprime rectangle becomes an ordinary prime-discrepancy increment. The exact cubic-sample telescope shows why improving that packet separately can simply rehouse a familiar global prime-error problem. A useful next mechanism must preserve joint compensation or introduce genuinely stronger arithmetic, rather than treat either local sign pairing or density subtraction as automatic payment.

### H. Competing Mechanisms

| Mechanism | Established / missing | Decisive obstruction or test | Decision |
| --- | --- | --- | --- |
| Small-prime-only core cancellation, then absolute values | RC1-RC2 prove a uniform subquadratic-certificate obstruction | Genuine semiprime rectangle; missing cofactor-prime coverage | Abandon this closing method, retain exact identities |
| Cross-core signed compensation | RC3 proves it at inherited scale; stronger rate not supplied | Full grouped square must retain negative mixed mass | Continue as structure, not a new endpoint proof |
| Pay the centered rigid packet separately | RC4 exact; RC5 gives the true all-scale analytic demand | Uniform cubic samples imply ordinary prime-error bound | Revise: compare to known prime-error strength before assuming payment |
| Joint I_R and complete-return estimate | Original source intact; OPEN-SAT-I and later return still unpaid | A Z_R bound is not necessary if the complement cancels it | Continue on the next SAT turn |
| VF-LOW and JOH | Prior SF1-SF5 and LC1-LC5 retain exact scopes | No changed assumption reopens their failed shortcuts | Preserve rotation; VF-LOW next |

### I. Specialist Handoffs

**Coordinator:** register RC1-RC2 as a source-specific method obstruction, RC3 as a baseline-derived supporting signed restriction, and RC5 as an exact equivalence to the displayed ordinary prime-error rate. None is VERIFIED_ETA. The strongest new concept is the rigid original semiprime rectangle together with its complete centered-rate interpretation. This makes a small-prime-only absolute closure less promising; it does not disfavor genuine joint signed estimates. Keep the next Owner route VF-LOW.

**Adversarial Referee:** review RC1's actual prime admission and singleton proof, RC2's uniformity over changing W and exact factor 1/3, RC3's use of the inherited b rather than a new cancellation input, and RC5's every-N quantifiers, cubic mesh, deterministic prime-count increment, positive-loss allocation and downward telescope. Attempt to break the implication by moving between samples or deleting the model/endpoints. Separate author self-audit from independent acceptance.

**Finite Wheel & Incidence:** the exact necessary condition RC2d is a useful restriction on any proposed core-preserving wheel pairing. It tolerates a growing wheel, unlike a fixed-wheel-only argument. Check whether a proposed method crosses these core classes or explicitly introduces primes at the true cofactor scale. Compare with QC1-QC3 without conflating square classes with deleted-prime cores. No new broad census is requested.

**Analytic Type II:** assess a joint bound for the original I_R, not an automatically separate bound for Z_R. RC5 exposes the exact prime-error supplier needed by that particular packet. Any improvement must be compared with the inherited strict boundary, not only 7/8. A transfer of your CODIV logarithmic maximal bounds would need the actual moving prime/model measure and endpoint map; no such bridge is asserted. Preserve your due NYMAN/OAI/CODIV rotation.

**Prime Census:** the smallest independent test is R=16, W={2,3} and W={2,3,5}, with 655, 131 and the inadmissible 1310. The first tests singleton conservation; the second falsifies dropping the wheel-support hypothesis. R=256 tests one-of-two cofactor-prime coverage. Reconstruct the entire original band and C_R and compare their full square; do not test a floating-point asymptotic exponent. Li_2 need not be evaluated to verify the exact model coefficient map.

**Lean Verification:** no new implementation is requested before independent review and utility selection. RC1's finite admission/singleton statement and RC2's finite signed class conservation are possible small qualified lemmas using the existing terminal-flip definitions. RC5 requires actual real prime counts, Li_2, PNT and all-scale interpolation, not a new assumed project axiom. The existing complete-return and prime-dilate identities should be reused. No global bound is handed off as proved.

These are asynchronous handoffs published in this own report. No specialist was launched, and no review or formalization is presumed.

### J. First Independently Missing Lemma

The original proper interior supplier remains the precise open statement

~~~text
exists kappa>0, forall epsilon>0, exists C_epsilon,R_epsilon,
forall integers R>=R_epsilon:
 |sum_(D<c<2D) mu(c)[Delta(x_c)-Delta(x_(2D))]|
    <= C_epsilon R^(11/6-kappa+epsilon).                 (OPEN-SAT-I)
~~~

It is a proper source component, not the canonical endpoint renamed. RC1-RC5 do not prove it. The genuine next mathematical challenge is a joint restriction on the cofactor signs and prime-discrepancy increments across different cores, retaining the model and endpoint. No smaller independently established supplier for that joint restriction was found in this invocation.

A proposal to pay Z_R separately must state its sigma=8/9-2kappa/3 prime-error input explicitly, or prove it independently; RC5 prevents calling it an elementary residual. A proposal to finish by small-prime core pairing and triangle is ruled out by RC2. Neither diagnosis prohibits a jointly compensated analytic estimate.

Even a positive answer to OPEN-SAT-I must return through E_R=-A_R-I_R. The previously available separate endpoint bound is R^(85/48), above the inherited terminal 7/4 root exponent, and L_R+C_R remains. These are upper-bound limitations, not lower bounds ruling out joint compensation. New full-endpoint gain remains UNKNOWN.

### K. Next-Run Resume Capsule

~~~text
RUN: scheduled 2026-11-05 00:09 EST; America/New_York; RUN_ID_UNAVAILABLE.
MAIN: ff620da3c0d2c29585805960c6be183c07f16556.
POLICY: NO_PIGEONHOLING_ROUTE_SELECTOR_V1; ffd8f1c65cc4da656174956d4e03b48bea46768b.
CLAIM: 20261105-owner-1 / RC1-RC6.
ROUTE: SAT; original q=2R, Y=q^2-1, D=floor(sqrt R) packet.
SOURCE: LargePrimeTerminalFlipLayers b7617df21b81002854a0d311ef7e02d9494154c3.
LAST JUSTIFIED:
  rigid semiprime rectangle, uniform deleted-small-prime core conservation;
  N_R ~ R^2/(3 log^2 R);
  known b forces cross-core balance, not a new b;
  centered rectangle Z_R exactly equivalent to ordinary prime error
  at exponent sigma, via all cubic samples and mesh exponent 2/3.
INVERSE: Z_R exponent 11/6-kappa <-> prime-error 8/9-2kappa/3,
  0<kappa<1/3; kappa=1/48 corresponds to rounded 7/8.
FIRST OPEN: OPEN-SAT-I, jointly; original A_R, L_R, C_R remain.
COMPLETE RETURN: M(Y)=L_R+E_R+C_R; E_R=Z_R+E_R^rem; all mixed terms.
FINITE: 26 roots, 38371 original occurrences, 1425 rectangle occurrences,
  346 wheels, 192 cubic-mesh checks, four rational exponent checks.
SCOPE FALSIFIERS: 655 singleton at W={2,3}, not W={2,3,5};
  1310 not admitted; 524 squareful zero; N_R=12>|M(1023)|=4.
REVIEW: SELF_AUDIT; independent Referee PENDING; no new Lean execution.
GATE: SEARCH_BROAD for additional gain; inherited strict-slot theorem retained.
NEW GLOBAL EXPONENT GAIN: NONE; canonical VF and RH OPEN.
ROTATION: Nov4 owner-2 VF-LOW; Nov4 owner-3 JOH; this run SAT.
NEXT DISTINCT ROUTE: VF-LOW; resume SF1-SF5 and the full source complement.
NEXT SAT: preserve cross-core/model cancellation; no repeated fixed-wheel scan
  or assumed separate Z_R improvement.
~~~

#### Today / Yesterday Continuity

At intake, no November 5 upstream report was present: **TODAY=PENDING; YESTERDAY=CARRY_FORWARD**. All seven November 4 report contents were retrieved, and the applicable findings, corrections and continuation sections were read. Their executable appendices were not all rerun.

| November 4 role | Retrieved blob | Consumed evidence |
| --- | --- | --- |
| Coordinator 00/90 | 68495a5e913eee0e788940a683cf16ec4d0984cc | C49-C52 separate-component warning; explicit SAT handoff |
| Owner | 560b0b7617703b64e728e12e60a390646c9379ea | S1-S5, OPEN-SAT-I; SF1-SF5 and LC1-LC5 continuity |
| Analytic | 04ffb1b41d8b6afe5a5d89754f5ccbc8d9682d58 | M1-M4 logarithmic maximal bounds; no same-source SAT bridge |
| Wheel | 37ad6a1230fbb46369311790ed5686baf1775598 | QC1-QC3 exact square-class cancellation obstruction |
| Census | 4bd5319fa3d13219cdad006dce4a854b606c2f7c | Nyman N=120 and N=42 falsifiers; scope warning only |
| Referee | 0e4fdfbf90d52a74074e04ef6cb6988339dc8d84 | referee-9..12 separate drift and complete-return safeguards |
| Lean | 5fce0138779d67eda4e69c13230274e6419de894 | #1093 exact theorem/CI evidence, updated by actual human merge |

Coordinator mirror blob identities agree. The external inbox is unchanged at **038018145c0fddb2f6306c0712373adf9cd1ea52**, with latest entries October 18. EXT-20261018-PNT-1..3, EXT-20261017-XCOORD-1 and EXT-20261014-5 retain their source and denominator qualifications; none pays today's bound.

#### Publication And Tool Discipline

Early checkpoint commit **10e4f4a6c01a0c3a3a4ab75fb8c4bfa37570d89d**, blob **e1d0f915653de14824e1a4b9617fbb4c7438d496**, was inspected and read back exactly; its only changed file is this authorized report. Final publication is recorded only after its own commit/readback.

Direct shell GitHub access returned CONNECT tunnel HTTP 403. Connected reads and report writing worked. No main, source, policy, other report, issue, PR, workflow, permission or schedule was changed. No agent was launched, no local Lean was run, and no background computation remains.

### Reproducibility Appendix

The following is the exact final executed verifier. It uses integer arithmetic, exact rational exponent checks, actual sieved/trial-checked mu, and symbolic Li_2 coefficient vectors. It does not evaluate a new analytic bound.


Verifier SHA256: **9d98b39df2c62cc1f5cb25eef6c9ab45fe4d43533f27683cb5c666db9e8633ac**.

~~~python
"""Exact SAT core-conservation tests, with source-faithful signed return.

The roots and controls below are fixed before running. No asymptotic
exponent is estimated. Formal Li symbols verify model accounting exactly.
"""

from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations
from math import isqrt
import hashlib
import json


DEVELOPMENT = tuple(range(16, 37))
HELD_OUT = (64, 65, 127, 128)
# A disclosed targeted case has two cofactor primes, so partial coverage is tested.
TARGETED = (256,)
ROOTS = DEVELOPMENT + HELD_OUT + TARGETED
LIMIT = 4 * max(ROOTS) ** 2 - 1


def sieve(limit):
    prime = bytearray(b"\x01") * (limit + 1)
    prime[:2] = b"\x00\x00"
    mu = [1] * (limit + 1)
    mu[0] = 0
    largest = [1] * (limit + 1)
    for p in range(2, limit + 1):
        if prime[p]:
            for n in range(p, limit + 1, p):
                mu[n] *= -1
                largest[n] = p
            for n in range(p * p, limit + 1, p * p):
                mu[n] = 0
            if p * p <= limit:
                prime[p * p:limit + 1:p] = b"\x00" * ((limit - p * p) // p + 1)
    return prime, mu, largest


def factor(n):
    factors = []
    for d in range(2, isqrt(n) + 1):
        while n % d == 0:
            factors.append(d)
            n //= d
    if n > 1:
        factors.append(n)
    return factors


def core(n, wheel):
    for p in wheel:
        while n % p == 0:
            n //= p
    return n


def clean(v):
    return {k: a for k, a in v.items() if a}


def model_from_layers(D, B, x, mertens):
    result = Counter()
    for d in range(D, B + 1):
        result[x[d]] -= mertens[d]
        result[x[d + 1]] += mertens[d]
    return clean(result)


prime, mu, largest = sieve(LIMIT)
primes = [n for n in range(2, LIMIT + 1) if prime[n]]
mertens = [0] * (LIMIT + 1)
pi = [0] * (LIMIT + 1)
for n in range(1, LIMIT + 1):
    mertens[n] = mertens[n - 1] + mu[n]
    pi[n] = pi[n - 1] + prime[n]
for n in range(1, 2049):
    fs = factor(n)
    independently = 0 if len(set(fs)) < len(fs) else (-1) ** len(fs)
    assert mu[n] == independently
    assert largest[n] == max(fs, default=1)

rows = []
stats = Counter()
digest = hashlib.sha256()
controls = {}
for R in ROOTS:
    q, Y, D = 2 * R, 4 * R * R - 1, isqrt(R)
    B = 2 * D - 1
    x = {d: Y // d for d in range(D, 2 * D + 1)}
    L, U = Y // (2 * D), 3 * Y // (4 * D)
    band_primes = [p for p in primes if x[2 * D] < p <= x[D]]
    cofactor_primes = [c for c in primes if D < c and 4 * c <= 5 * D]
    rectangle_primes = [p for p in band_primes if p <= U]
    assert L >= q and U < x[D]
    atoms = {}
    for p in band_primes:
        k = Y // p
        assert p > q and D <= k <= B
        for c in range(1, k + 1):
            n = p * c
            assert n not in atoms and largest[n] == p
            assert mu[n] == -mu[c]
            atoms[n] = dict(p=p, c=c, k=k, sign=mu[n])
    total = sum(a['sign'] for a in atoms.values())
    layer_total = -sum(mertens[d] * (pi[x[d]] - pi[x[d + 1]])
                       for d in range(D, B + 1))
    assert total == layer_total
    smooth = sum(mu[n] for n in range(1, Y + 1) if largest[n] <= q)
    unselected = sum(mu[n] for n in range(1, Y + 1)
                     if largest[n] > q and n not in atoms)
    complement = smooth + unselected
    assert total + complement == mertens[Y]
    assert total**2 + complement**2 + 2 * total * complement == mertens[Y]**2

    rectangle = {p * c for p in rectangle_primes for c in cofactor_primes}
    count = len(cofactor_primes) * len(rectangle_primes)
    assert len(rectangle) == count
    for n in rectangle:
        a = atoms[n]
        assert a['sign'] == 1 and 2 * n > Y and 16 * n <= 15 * Y
        assert a['c'] > D and a['p'] > q and mu[a['c']] == -1

    # The prime-2 compression is existing infrastructure, not a new theorem.
    matched = set()
    for n, a in atoms.items():
        if a['c'] % 2 == 1 and 2 * a['c'] <= a['k'] and a['sign']:
            assert 2 * n in atoms and atoms[2 * n]['sign'] == -a['sign']
            assert n not in matched and 2 * n not in matched
            matched.update((n, 2 * n))
    survivors = {n for n, a in atoms.items() if a['sign'] and n not in matched}
    assert survivors == {n for n, a in atoms.items()
                         if a['sign'] and a['c'] % 2 == 1 and 2 * n > Y}
    assert sum(atoms[n]['sign'] for n in survivors) == total
    assert rectangle <= survivors

    # Exhaust all wheels supported at most D, then test larger admissible wheels.
    small = [p for p in primes if p <= D]
    wheels = [tuple(s) for j in range(len(small) + 1)
              for s in combinations(small, j)]
    wheels += [tuple(small + cofactor_primes), tuple(p for p in primes if p <= q)]
    if R in TARGETED:
        assert cofactor_primes == [17, 19]
        wheels += [tuple(small + [c]) for c in cofactor_primes]
    full_small = None
    for wheel in wheels:
        groups = defaultdict(list)
        for n, a in atoms.items():
            if a['sign']:
                groups[core(n, wheel)].append((n, a['sign']))
        totals = {key: sum(sign for _, sign in group) for key, group in groups.items()}
        l1 = sum(abs(v) for v in totals.values())
        leftovers = []
        for group in groups.values():
            pos = [n for n, sign in group if sign == 1]
            neg = [n for n, sign in group if sign == -1]
            cancel = min(len(pos), len(neg))
            leftovers.extend(pos[cancel:] + neg[cancel:])
        assert len(leftovers) == l1 and len(set(leftovers)) == l1
        forced = {n for n in rectangle if atoms[n]['c'] not in wheel}
        for n in forced:
            assert core(n, wheel) == n and groups[n] == [(n, 1)]
            assert n in leftovers
        assert l1 >= len(forced)
        assert sum(totals.values()) == total
        positive = sum(max(v, 0) for v in totals.values())
        negative = sum(max(-v, 0) for v in totals.values())
        assert (positive - negative)**2 == total**2
        assert positive**2 + negative**2 - 2 * positive * negative == total**2
        diag = sum(v * v for v in totals.values())
        running = cross = 0
        for v in totals.values():
            cross += 2 * running * v
            running += v
        assert diag + cross == total**2
        assert l1**2 >= len(forced)**2
        if wheel == tuple(small):
            full_small = dict(l1=l1, diagonal=diag, ordered_cross=cross,
                              positive=positive, negative=negative)
        stats['wheel_checks'] += 1

    # Exact model partition in the free vector space on Li_2(integer).
    original_model = model_from_layers(D, B, x, mertens)
    expanded = Counter({x[D]: -mertens[D], x[2 * D]: mertens[D]})
    for c in range(D + 1, B + 1):
        expanded[x[c]] -= mu[c]
        expanded[x[2 * D]] += mu[c]
    assert clean(expanded) == original_model
    rectangle_model = Counter({U: len(cofactor_primes), L: -len(cofactor_primes)})
    other_model = Counter(expanded)
    for endpoint, value in rectangle_model.items():
        other_model[endpoint] -= value
    restored = Counter(other_model)
    for endpoint, value in rectangle_model.items():
        restored[endpoint] += value
    assert clean(restored) == original_model
    assert count == sum(value * pi[endpoint] for endpoint, value in rectangle_model.items())
    interior = sum(mu[c] * (pi[x[c]] - pi[x[2 * D]]) for c in range(D + 1, B + 1))
    assert total == -mertens[D] * (pi[x[D]] - pi[x[2 * D]]) - interior
    assert sum(mu[c] * len(rectangle_primes) for c in cofactor_primes) == -count
    if R == 16:
        assert atoms[655]['sign'] == 1 and 1310 not in atoms
        assert core(655, (2, 3)) == 655
        assert core(655, (2, 3, 5)) == core(131, (2, 3, 5)) == 131
        assert atoms[131]['sign'] == -1 and atoms[262]['sign'] == 1
        assert atoms[524]['sign'] == 0
        assert count > abs(mertens[Y])
        controls = dict(singleton=655, inadmissible_partner=1310,
                        expanded_wheel_opposite_pair=[131, 655],
                        lower_half_opposite_pair=[131, 262], squareful_zero=524,
                        rectangle_count=count, mertens=mertens[Y])
    row = dict(R=R, D=D, Y=Y, L=L, U=U,
               cofactor_primes=cofactor_primes, owner_count=len(rectangle_primes),
               rectangle=count, total=total, complement=complement,
               mertens=mertens[Y], atoms=len(atoms),
               nonzero=sum(bool(a['sign']) for a in atoms.values()),
               binary_survivors=len(survivors), full_small_wheel=full_small)
    rows.append(row)
    digest.update(json.dumps(row, sort_keys=True).encode())
    stats['roots'] += 1
    stats['physical_occurrences'] += len(atoms)
    stats['rectangle_occurrences'] += count
    stats['model_partitions'] += 1

for N in tuple(range(4, 65)) + (101, 127, 257):
    R, D, Y = N * N, N, 4 * N**4 - 1
    L, U = Y // (2 * D), 3 * Y // (4 * D)
    assert L == 2 * N**3 - 1 and U == 3 * N**3 - 1
    next_L = 2 * (N + 1)**3 - 1
    gap = next_L - L
    assert gap == 6 * N * N + 6 * N + 2
    for x in (L, L + 1, next_L - 1):
        assert L <= x < next_L
        assert x - L <= gap
        assert abs(3 * x - 2 * U) <= 3 * gap + 1
        stats['cubic_mesh_checks'] += 1

for kappa in (Fraction(1, 96), Fraction(1, 48), Fraction(1, 24), Fraction(1, 3)):
    sigma = Fraction(8, 9) - Fraction(2, 3) * kappa
    assert Fraction(1, 2) + Fraction(3, 2) * sigma == Fraction(11, 6) - kappa
    if kappa == Fraction(1, 48):
        assert sigma == Fraction(7, 8)
    if kappa == Fraction(1, 3):
        assert sigma == Fraction(2, 3)
    stats['exponent_checks'] += 1

print(json.dumps(dict(scope='FINITE_COMPUTATION, not an asymptotic estimate',
                     development=list(DEVELOPMENT), held_out=list(HELD_OUT),
                     targeted=list(TARGETED),
                     counts=dict(stats), controls=controls,
                     samples=[r for r in rows if r['R'] in (16, 25, 36, 64, 65, 127, 128, 256)],
                     data_sha256=digest.hexdigest()), sort_keys=True, indent=2))

~~~

#### Exact Output

~~~text
{
  "controls": {
    "expanded_wheel_opposite_pair": [
      131,
      655
    ],
    "inadmissible_partner": 1310,
    "lower_half_opposite_pair": [
      131,
      262
    ],
    "mertens": -4,
    "rectangle_count": 12,
    "singleton": 655,
    "squareful_zero": 524
  },
  "counts": {
    "cubic_mesh_checks": 192,
    "exponent_checks": 4,
    "model_partitions": 26,
    "physical_occurrences": 38371,
    "rectangle_occurrences": 1425,
    "roots": 26,
    "wheel_checks": 346
  },
  "data_sha256": "36a8864f50659837040faa7627860ebad1ccb44d074956e372c543623f12be58",
  "development": [
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
    36
  ],
  "held_out": [
    64,
    65,
    127,
    128
  ],
  "samples": [
    {
      "D": 4,
      "L": 127,
      "R": 16,
      "U": 191,
      "Y": 1023,
      "atoms": 118,
      "binary_survivors": 33,
      "cofactor_primes": [
        5
      ],
      "complement": -37,
      "full_small_wheel": {
        "diagonal": 33,
        "l1": 33,
        "negative": 0,
        "ordered_cross": 1056,
        "positive": 33
      },
      "mertens": -4,
      "nonzero": 95,
      "owner_count": 12,
      "rectangle": 12,
      "total": 33
    },
    {
      "D": 5,
      "L": 249,
      "R": 25,
      "U": 374,
      "Y": 2499,
      "atoms": 272,
      "binary_survivors": 75,
      "cofactor_primes": [],
      "complement": -76,
      "full_small_wheel": {
        "diagonal": 105,
        "l1": 75,
        "negative": 0,
        "ordered_cross": 5520,
        "positive": 75
      },
      "mertens": -1,
      "nonzero": 213,
      "owner_count": 21,
      "rectangle": 0,
      "total": 75
    },
    {
      "D": 6,
      "L": 431,
      "R": 36,
      "U": 647,
      "Y": 5183,
      "atoms": 529,
      "binary_survivors": 109,
      "cofactor_primes": [
        7
      ],
      "complement": -111,
      "full_small_wheel": {
        "diagonal": 109,
        "l1": 109,
        "negative": 0,
        "ordered_cross": 11772,
        "positive": 109
      },
      "mertens": -2,
      "nonzero": 405,
      "owner_count": 35,
      "rectangle": 35,
      "total": 109
    },
    {
      "D": 8,
      "L": 1023,
      "R": 64,
      "U": 1535,
      "Y": 16383,
      "atoms": 1465,
      "binary_survivors": 275,
      "cofactor_primes": [],
      "complement": -287,
      "full_small_wheel": {
        "diagonal": 375,
        "l1": 275,
        "negative": 10,
        "ordered_cross": 64650,
        "positive": 265
      },
      "mertens": -32,
      "nonzero": 1037,
      "owner_count": 70,
      "rectangle": 0,
      "total": 255
    },
    {
      "D": 8,
      "L": 1056,
      "R": 65,
      "U": 1584,
      "Y": 16899,
      "atoms": 1500,
      "binary_survivors": 286,
      "cofactor_primes": [],
      "complement": -278,
      "full_small_wheel": {
        "diagonal": 396,
        "l1": 286,
        "negative": 11,
        "ordered_cross": 69300,
        "positive": 275
      },
      "mertens": -14,
      "nonzero": 1062,
      "owner_count": 73,
      "rectangle": 0,
      "total": 264
    },
    {
      "D": 11,
      "L": 2932,
      "R": 127,
      "U": 4398,
      "Y": 64515,
      "atoms": 5141,
      "binary_survivors": 1078,
      "cofactor_primes": [
        13
      ],
      "complement": -744,
      "full_small_wheel": {
        "diagonal": 1040,
        "l1": 744,
        "negative": 16,
        "ordered_cross": 505904,
        "positive": 728
      },
      "mertens": -32,
      "nonzero": 3566,
      "owner_count": 176,
      "rectangle": 176,
      "total": 712
    },
    {
      "D": 11,
      "L": 2978,
      "R": 128,
      "U": 4468,
      "Y": 65535,
      "atoms": 5203,
      "binary_survivors": 1087,
      "cofactor_primes": [
        13
      ],
      "complement": -709,
      "full_small_wheel": {
        "diagonal": 1049,
        "l1": 753,
        "negative": 15,
        "ordered_cross": 521680,
        "positive": 738
      },
      "mertens": 14,
      "nonzero": 3607,
      "owner_count": 178,
      "rectangle": 178,
      "total": 723
    },
    {
      "D": 16,
      "L": 8191,
      "R": 256,
      "U": 12287,
      "Y": 262143,
      "atoms": 18991,
      "binary_survivors": 4254,
      "cofactor_primes": [
        17,
        19
      ],
      "complement": -1686,
      "full_small_wheel": {
        "diagonal": 3100,
        "l1": 2804,
        "negative": 547,
        "ordered_cross": 2921000,
        "positive": 2257
      },
      "mertens": 24,
      "nonzero": 12568,
      "owner_count": 441,
      "rectangle": 882,
      "total": 1710
    }
  ],
  "scope": "FINITE_COMPUTATION, not an asymptotic estimate",
  "targeted": [
    256
  ]
}

~~~

### Verified Publication Receipt - 2026-11-05 00:36 EST

**Execution COMPLETE; substantive report PUBLISHED_AND_READBACK_VERIFIED.** The full RC1-RC6 synthesis, A-K sections, exact verifier/output, source ledger and specialist handoffs were published in commit **2312f30f3fed5e1029778f5f8bbdf297d9ac53ea**, blob **ceeb4b4d68453c6ce7d79d6b72c04c8a109af199**. Immutable-commit readback matched all **57,883 characters** exactly. Commit inspection confirms that only this authorized Owner report changed. The original early checkpoint remains an unchanged prefix.

Main was rechecked before publication and remained **ff620da3c0d2c29585805960c6be183c07f16556**. Today's upstream directory still contained no other role report: TODAY=PENDING; YESTERDAY=CARRY_FORWARD. The current branch report was freshly fetched again before this receipt and matched the verified synthesis.

This receipt records the already verified substantive commit, not its own future commit; the receipt write is followed by its own exact readback. The downloadable report mirrors the final published content.

Mathematical status remains **PAPER_PROOF / SELF_AUDIT**, with **FINITE_COMPUTATION**, the specified **REFUTED** method extensions, and **TARGET_EQUIVALENT** RC5 only relative to its stated prime-error envelope. Independent review and new Lean formalization remain PENDING. **No new global exponent bound, canonical VF bound, or RH proof was established.**



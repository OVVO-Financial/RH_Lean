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




## Scheduled VF-LOW Continuation Checkpoint - 2026-11-05 08:09 EST Invocation

### A. Mathematical Question
**IN_PROGRESS / PARTIAL.** Resume 20261104-owner-2/SF1-SF5 at the actual VF-weighted squarefree depth-three source. The once-only divisor-ancestor capacity repair is already refuted and will not be rerun. Investigate a different chronological signed response, including non-divisor prime seats, or an exact source-preserving transformation whose independently bounded remainder permits such a response. All original complementary seats, historical anchors and mixed terms remain mandatory. No new theorem is claimed at this checkpoint.

### B. Authority And Continuity
Actual scheduled trigger: 2026-11-05T08:09:01-05:00; RUN_ID_UNAVAILABLE.
Claim reserved: **20261105-owner-2**. Main **ff620da3c0d2c29585805960c6be183c07f16556**; AGENTS **547dda0d9456e7a4e1165dc72d59da6f70d5c023**; contract **7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c**; multi-front policy **ffd8f1c65cc4da656174956d4e03b48bea46768b**. deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1; selected route VF-LOW, next JOH.

Two-day report bytes and external inbox retrieved at report snapshot **4651229e596a82fdf1ce570d2326720d5803b5b9**. Today Coordinator, Owner, Wheel, Census, Referee and Lean are AVAILABLE. Analytic TODAY=PENDING, YESTERDAY=CARRY_FORWARD (Nov4 M1-M6, CF1-CF3, P1-P10 at their distinct scopes). Consume Coordinator C53-C57 as scoped relaxation evidence, not a theorem about genuine VF signs. The 435-seat/31-ancestor counterexample and SF3 infinite construction are retained. External inbox remains **038018145c0fddb2f6306c0712373adf9cd1ea52**, latest entry Oct18.

Original signed-seat source **87a6654a4a4337b409fde69aa15d7264d8b721b6**, weighted physical Fubini **4679d7edae521dd4d9f0238aa4201445b1fdb9a9**, restoring decomposition **41ca385cb2bd0706db21007e19cd2b0b1aaa4b3e**, historical NNS compression **6cc6b2a9d25279dd44fb65cb222f5d6846a912d4**, canonical consumer **79030d70e8d3e0d08eef9bac53fef95c36eca2fb** were fetched and their relevant declarations inspected. Canonical actual-prime bound remains OPEN; its terminal consumer retains ClassicalVonKochRHCriterion.

Live open/draft collection contains only #1094, DRAFT/UNMERGED, head **1ea4a8a4308976721a3841998d6c3a4554f7a9c9**. #1093, #1092, #1091 and #1090 are merged. No different-carrier Nyman theorem pays the VF source.

### C. Derivation And Falsification Plan
Compare local chronological payment with a logarithmically normalized complete-source relation. Seek an independent restriction, not another capacity renaming. Freeze any concrete inequality before computing; test source weights, square boundaries, prime powers, occurrence reuse and every quadratic complement. Use exact integer/rational tests or certified intervals and label finite evidence separately.

### D-K. Pending
Derivation, quantitative consequence, circularity audit, handoffs, source/check evidence and a precise resume capsule will be appended to this same report. New independent review and Lean verification are PENDING. No local Lean execution, source/PR edits, agent launches, merges or schedule changes.


## Scheduled VF-LOW Final Synthesis - 20261105-owner-2

Actual invocation: **2026-11-05T08:09:01-05:00**, SCHEDULED, RUN_ID_UNAVAILABLE. This completes the checkpoint above, not another run. Selected protected route: **VF-LOW**; next **JOH**. New results are **PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED**, except the explicitly labeled finite tests and conditional corollary. No literature-originality claim, new complete-endpoint gain, canonical bound or RH proof.

Status ledger: **CR1-CR2 PAPER_PROOF** (independent quantitative restriction on the stated proper subsource); **CR3 PAPER_PROOF / REFUTED** (the precisely specified ancestry-only supplier); **CR4 IDENTITY_ONLY** (complete reconstruction, no new estimate); **CR5 FINITE_COMPUTATION** (reproducer executed successfully); **OPEN-VF-CR-DENSE CONJECTURE**. The full residual bound is **TARGET_EQUIVALENT / OPEN**. No new result is labeled PROVED_IN_LEAN.

### A. Most Important Mathematical Development

**The ancestry obstruction has two different scales, and they must not be confused.** A single family from yesterday's SF1-SF3 has at most one composite per square block. Its entire positive VF charge is already O(N/log N), below the canonical N log N tolerance. Failure to pay that family exactly from its ancestors does NOT refute a method allowing a canonical-sized unpaid remainder.

There is nevertheless a stronger genuine obstruction. The new three-prime rectangle in CR3, with MANY distinct greatest-prime labels, has

```text
positive demand X_N ~ N^2/(200 log^4 N),
distinct historical prime ancestors A_N ~ N/(4 log N).
```

Consequently, for every fixed K,C>=0, eventually

```text
X_N > K A_N + C N log N.                             (CR3)
```

Thus ancestor-only bounded-capacity payment fails even after allowing an RH-scale remainder, on actual squarefree depth-three seats. This refutes a specified supplier, not the complete VF bound: the original non-ancestor complement remains.

**A constructive alternative survives at a proper-subsource scale.** CR1-CR2 allocate earlier, actual prime-seat charge to sparse positive VF populations, with NO repeated expenditure. A classical quantitative PNT input yields some fixed c>0 such that any actual composite selection with at most `floor(exp(c sqrt(log N)))` seats per root in each sufficiently large dyadic root shell has a chronological signed response Q(T) satisfying

```text
Q(T)<=0,
|Q(T)| << T exp(-c sqrt(log T))/log T,
total fraction spent from each donor prime <=1/2.     (CR2)
```

Constants are uniform over all those selections. The source weights are the original w_r and -(1-w_s), not prime-density replacements. Fractional use is an exact partition of each original coefficient, with its unused remainder retained. The selected positive mass can itself be much larger than N log N. This is an independently justified proper-sector signed restriction, NOT a bound for the complete defect or a returned-cell admission theorem.

For the exact old 435-seat witness, 435 DISTINCT primes from the immediately preceding square blocks pay the demand using less than one tenth of each donor's genuine charge. Conversely, at r=145 four different least-owner/greatest-prime families overdraw their shared nearest donor. Both facts are verified below. Availability of non-divisor primes is real; simultaneous allocation and unfinished chronological return are the issue.

### B. Current Authoritative Objective

Intake/source-inspection main: **ff620da3c0d2c29585805960c6be183c07f16556**. Latest main refreshed before publication: **884de7a1fa7687d483a7b5272bff6c9d53790367**. AGENTS: **547dda0d9456e7a4e1165dc72d59da6f70d5c023**. Contract: **7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c**. Current multi-front policy: **ffd8f1c65cc4da656174956d4e03b48bea46768b**. `deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1`.

The final refresh fetched AGENTS and the contract again and verified their hashes unchanged. The complete nontruncated compare from intake to final main contains only the three additions for merged #1094: its Nyman correction-energy source, workflow and regression script. All VF source blobs below and all governing instructions are therefore unchanged at the final main. The new Nyman source was also fetched and read, blob **e5453cd32c3c4ebf9ebf41927bcb92e534b2ece7**: its high-support energy lower bound is a COMPONENT bound with an exact signed base/correction split, not a full residual lower bound. It does not alter this VF argument or the protected rotation.

The canonical arithmetic assertion remains

```text
exists C>=0, forall integer R>=2,
  |pi(R^2)-F_R-sqrt(2)| <= C R log R,
F_R=sum_(2<=r<R)(2r+1)/log(r^2+r+1/2).
```

It is OPEN. The source declaration `riemannHypothesis_of_vfCanonicalSquare` still requires `ClassicalVonKochRHCriterion` explicitly. The inherited fixed strict Mertens/slot result is not erased, optimized, or counted as a new gain here.

Original sources fetched at this immutable main, with relevant definitions/proofs inspected:

| Source under research/ | Blob SHA | Use |
| --- | --- | --- |
| VF_MID_VON_KOCH_BRIDGE.lean | 32d4b0d74ecadc9780b9841d40357f6ff02369f0 | Literal midpoint, band mass and finished mass |
| VF_MID_ODD_FRACTIONAL_CLUSTER.lean | 942badff45c03d2a9e97789b57d1bd8052232191 | Exact r odd seats and w_r |
| VF_MID_SIGNED_SEAT_CHARGE.lean | 87a6654a4a4337b409fde69aa15d7264d8b721b6 | Actual prime/composite signs and block sum |
| VF_MID_ONE_BLOCK_SOURCE_TO_RANK_INLET.lean | dd4ff316e51501a3ca9404e0c2c3e754f154ac6e | Squarefree processed admission; squareful terms remain physical |
| VF_MID_FIRST_BAD_WEIGHTED_OWNER_FUBINI.lean | 4679d7edae521dd4d9f0238aa4201445b1fdb9a9 | Original active carrier, strict owner and returned-fibre hypotheses |
| VF_MID_NATIVE_LYAPUNOV_SEAT_GRAM.lean | 23e7b0c5c9f4b50997a508345d91f30364f93f10 | Exact full run and historical/current Gram |
| VF_MID_FIRST_BAD_RESTORING_DECOMPOSITION.lean | 41ca385cb2bd0706db21007e19cd2b0b1aaa4b3e | Full numerator equals next defect squared |
| VF_MID_915_EXACT_HISTORICAL_NNS_COMPRESSION.lean | 6cc6b2a9d25279dd44fb65cb222f5d6846a912d4 | Original historical compression price |
| VF_MID_OWNER_SIGNED_PAIR_BOUNDS.lean | f77418156653f1d93c0bcd4ca6587fc0987e3b95 | Existing pair bounds, not a new global source estimate |
| VF_MID_SQUARE_THETA_NATIVE_DESCENT.lean | 250b9ca670fb60914a11fee769ff84e116340fe8 | Existing logarithmic-coordinate relation; not rediscovered |
| VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb | Actual target and explicit classical consumer |

The existing `VF_MID_915_MIDDLE_PRIME_COMPOSITE_CAPACITY.md`, blob **8eb751bee0a6e4055c76916eb9a8d8324742b72a**, already warns that a physical donor need not be a multiplicative descendant. Its theorem counts positive composite resources for a DIFFERENT middle-prime population. CR1-CR2 are instead a weighted chronological negative-prime allocation, a simultaneous load bound, and a bound for EVERY unfinished root-prefix return. Neither establishes #915 payment. Scoped code searches located no identical theorem; this is not an exhaustive novelty claim.

### C. Structural Hypotheses Investigated

Resume: **20261104-owner-2/SF1-SF5**, Coordinator **20261105-coordinator-1**, sections C/H, and today's own **20261105-owner-1/RC1-RC6** at their SAT-only scope. Prior protected order was VF-LOW, JOH, SAT; this VF-LOW turn continues the rotation.

Three genuinely different moves were considered:

1. Use actual earlier NON-DIVISOR primes and prove the allocation, uniform budget and unfinished return. This produces CR1-CR2 and the finite witness.
2. Replace VF charges by a logarithmic factor coordinate. The existing theta/descent source already supplies that equality; no new estimate emerged. It is not re-credited as research progress.
3. Aggregate many genuine greatest-prime families and permit an N log N residual in the failed ancestry supplier. This yields CR3, rather than repeating the already accepted single-q overload.

The finite donor question was fixed before computation: q=490001, held-out q=1000003, the original 30 primes in [500,700], one donor chosen as the largest prime below r(n)^2. Test donor primality, previous-block admission, uniqueness, non-divisibility and used fraction <1/10. The duplicate-resource search on r=16..512 was a separate falsifier. The four-distinct-owner r=145 refinement, multiscale packet check and dense rectangle checks were disclosed second-stage tests AFTER the first result, not retroactively preregistered.

### D. Mathematical Derivation

#### D0. Original Carrier And Signs

For r>=2 the physical sites are odd n with r^2<n<(r+1)^2. Put

```text
w_r=(2+1/r)/log(r^2+r+1/2),
c(r,n)=w_r-1_Prime(n),
D_R=pi(R^2)-F_R,
sum_(A<=r<B,n physical)c(r,n)=D_A-D_B.                 (0)
```

Every selected composite has positive charge w_r, regardless of its Mobius sign or squarefreeness. A donor prime p has its own root s=floor(sqrt p), charge `-y_p=-(1-w_s)`. Primes at square endpoints do not exist in the ranges used. No even site, duplicated integer, changed weight, or assumed returned mask is introduced.

#### CR1. Local Chronological Reserve Lemma

Fix integer N>=64 and 1<=h<=N/2. Let `L(x)=Li_2(x)` and

```text
E_N=max_(integer s, N/2<=s<=2N) |pi(s^2)-L(s^2)|.
Assume E_N <= N h/[8 log(2N)].                        (1)
```

Let k be a nonnegative integer and F be ANY set of actual positive composite sites in roots [N,2N), with at most k sites per root. For each b=N+jh<2N, define source roots `[b,min(b+h,2N))` and donor primes

```text
P_b={prime p:(b-h)^2<p<b^2},
X_b=sum_(selected source sites in that cell) w_r,
Y_b=sum_(p in P_b)y_p,
lambda_b=X_b/Y_b.                                    (2)
```

The donor intervals are disjoint. All their primes occur strictly before every site in the corresponding source cell. They are genuine physical odd prime seats at roots at least N/2.

Writing a=b-h, the ordinary prime-error identity and monotonicity of 1/log give

```text
#P_b >= (b^2-a^2)/log(b^2)-2E_N
     >= N h/[2 log(2N)]-2E_N
     >= N h/[4 log(2N)].                             (3)
```

This is NOT PNT used as a pointwise prime indicator: (3) is a proved interval count, and (2) retains every actual prime with its actual weight.

For s>=N/2, `w_s<=3/[2 log(N/2)]<=2/log N<=1/2` when N>=64; the middle inequality uses N>=16. For current r>=N, also w_r<=2/log N. Hence

```text
Y_b >= N h/[8 log(2N)],
X_b <= 2 k h/log N,
0<=lambda_b <=16 k log(2N)/(N log N)<=32 k/N.          (4)
```

In particular k<=N/128 implies lambda_b<=1/4. Assign the exact fraction lambda_b of EACH donor's negative coefficient to this cell. The packet sum is exactly `X_b-lambda_b Y_b=0`. The unused coefficient `-(1-lambda_b)y_p` remains at the SAME prime occurrence. This is a partition of unity, not cloned history or a replacement of y_p by 1.

Let Q_b(T) be this packet's original signed charge over roots <T. All negative terms precede all positive terms. Therefore

```text
-X_b<=Q_b(T)<=0,
Q_b(T)=0 outside (b-h,min(b+h,2N)).                   (5)
```

Inside a source cell, exactly `Q_b(T)=-sum_(remaining selected r>=T)w_r`; inside its donor cell it is the negative fraction of the ACTUAL donor prefix. No favorable empirical covariance is assumed.

At any root cut T, at most TWO such packets from one N-shell are unfinished. Consequently

```text
-4 k h/log N <= Q_N(T):=sum_b Q_b(T)<=0.              (6)
```

This is the quantitative chronological return, not merely the completed zero sum. The assertion is uniform in the actual selected sites, their arithmetic factors, masks imposed only on the positive selection, and the final partial source cell. It does NOT allow an additional arbitrary mask on the donor prime set without reproving (3).

#### CR2. One Simultaneous All-Scale Response

Take dyadic N>=N0, integers h_N<=N/2 satisfying (1), and caps k_N<=N/128. Select at most k_N actual composites per root in [N,2N). Use CR1 on each shell. Every selected site belongs to exactly one source cell. A prime at root s can occur in donor cells from at most TWO dyadic shells, since their supports lie in `[N/2,2N)`, which implies `s/2<N<=2s`. Its TOTAL used fraction

```text
theta_p=sum_(cells using p)lambda_b <=1/2.            (7)
```

Each prime is represented once with coefficient `-theta_p y_p` in the paid response and once with complementary coefficient `-(1-theta_p)y_p` in the residual. Products between these two coefficient parts remain in the full quadratic reconstruction. The two parts are NOT independent occurrences.

Define the locally finite physical signed primitive

```text
Q(T)=sum_(selected (r,n), r<T) w_r
     -sum_(donor prime p, floor(sqrt p)<T)theta_p y_p.
```

It is nonpositive for every integer T, by (5). Only at most two dyadic shells have unfinished packets at T; within each, at most two packets are open. Thus

```text
|Q(T)|<=8 max_(dyadic N, T/2<N<=2T) k_N h_N/log N.    (8)
```

The maximum over an empty set is zero. The constants do not depend on the selected family.

**Independent analytic input and its exact use.** The classical quantitative PNT states that for some fixed c0>0,
`|pi(x)-li(x)|=O(x exp(-c0 sqrt(log x)))`.
The theorem and normalization were checked in [NIST DLMF 27.12.5](https://dlmf.nist.gov/27.12.E5). Here `li-Li_2=li(2)` is a fixed constant and is retained in the bound for E_N. This classical result supplies no RH-scale bound. On the whole fixed-ratio interval `[N^2/4,4N^2]` it gives `E_N=O(N^2 exp(-c1 sqrt(log N)))` for some fixed c1>0, uniformly in all cell endpoints.

For example choose

```text
h_N=ceil(8 E_N log(2N)/N + sqrt N).
```

Then (1) holds exactly, h_N=o(N), and for some c>0, after increasing N0,

```text
h_N << N exp(-2c sqrt(log N)),
k_N=floor(exp(c sqrt(log N))) <= N/128.
```

Apply (7)-(8), enlarging constants for comparable N and T, to obtain

```text
Q(T)<=0,
|Q(T)| << T exp(-c sqrt(log T))/log T,                (9)
theta_p=O(k_(comparable s)/s)=o(1),  theta_p<=1/2.
```

No numerical threshold N0 or explicit c is claimed. Defining h_N using the genuine finite E_N is not assuming the desired VF bound: the much weaker, independently established classical PNT supplies all the growth used in (9). This proves existence of a uniform arithmetic response, not an efficient prime-counting algorithm.

**The positive population need not be already negligible.** For large N, every square block has at least floor(r/3)-1 odd multiples of 3, all composite in this range. Thus one may select k_N actual composite sites at EVERY root. Their original positive mass is at least `N k_N/log(2N)`, because w_r>1/log(2N) on [N,2N). Its ratio to N log N tends to infinity. CR2 therefore pays some proper positive populations larger than the canonical tolerance, rather than merely renaming an already small scalar. These examples may include squareful seats; they are raw VF examples, not automatically Mobius-active examples.

**Conditional power version, separate from (9).** If the stronger input `|pi(x)-Li_2(x)|<=K x^alpha`, 1/2<alpha<1, is supplied, take `h_N=O(N^(2alpha-1)log N+sqrt N)` and `k_N=floor(N^delta)` for any fixed 0<=delta<1, so the capacity condition k_N<=N/128 eventually holds. Then

```text
|Q(T)| << T^(2alpha-1+delta)+T^(1/2+delta)/log T.
```

For alpha=8/9 and delta=1/9 this is O(T^(8/9)). Yesterday's paper S2 derives that prime-error input from the unchanged fixed b=7/8 Mertens envelope. This corollary is **CONDITIONAL on that stated supplier / PAPER-LEVEL application**, not a new Mertens exponent and not Lean-certified. The unconditional classical-PNT theorem (9) does not require S2.

**Non-divisor specialization.** In the old SF1 family put N=(q-1)/2, so its roots lie in [N,2N) and it has at most one site per root. For large N every CR1 donor is >N^2/4>q, while every prime factor of every selected seat is <=q. Hence every donor is coprime to EVERY selected seat. These primes cannot be substituted as divisor-parent edges of the existing multiplicative returned-fibre graph. The theorem is on the genuine raw physical history, not a proved map into those clipped cells.

#### CR3. A Dense Fixed-Depth Obstruction Above The Canonical Remainder

For integer N tending to infinity define two actual prime sets

```text
S_N={prime p:sqrt N<p<=(11/10)sqrt N},
Q_N={prime q:(3/2)N<q<=(7/4)N},
F_N={q p s:q in Q_N, p,s in S_N, p<s}.
```

All factors are odd and distinct for sufficiently large N. Unique factorization makes every physical integer distinct, with greatest prime q and least prime p. Moreover

```text
(3/2)N^2<n<=(847/400)N^2<4N^2,
q/4<p s<q,
q<N^2, p<N.
```

Thus every n is an original strict-square, squarefree depth-three positive seat in roots [N,2N), admitted to the processed physical least-owner carrier. Every ancestor occurs before this run. No perfect square is added. Each fixed q still contributes at most one seat per root, exactly as in SF1; the new effect is simultaneous many-q aggregation.

The ordinary PNT in these fixed-ratio intervals gives

```text
|S_N| ~ sqrt N/(5 log N),
|Q_N| ~ N/(4 log N),
|F_N|=|Q_N| binom(|S_N|,2) ~ N^2/(200 log^3 N).
```

The exact theorem used is `pi(x)~x/log x`, checked in [NIST DLMF 27.2.3](https://dlmf.nist.gov/27.2.E3). No short-interval error estimate is used for these counts. The constants follow from interval lengths 1/10 and 1/4 and `log(sqrt N)=(1/2)log N`.

Uniformly over this rectangle, r/N stays in a fixed compact subinterval of (1,2), so `w_r=(1+o(1))/log N`. Therefore

```text
X_N:=sum_(n in F_N) w_(floor sqrt n)
    ~ N^2/(200 log^4 N),
A_N:=#primeDivisors(F_N)=|S_N|+|Q_N|
    ~ N/(4 log N),
X_N/A_N ~ N/(50 log^3 N) -> infinity.                (10)
```

For any fixed K,C>=0, `K A_N=o(X_N)` and `C N log N=o(X_N)`. This proves CR3. Nonnegative allocations restricted to prime-divisor history, with TOTAL expenditure at most K per distinct ancestor, cannot cover these demands even after discarding a remainder C N log N. It also allows an arbitrarily growing number of local packets as long as their common ancestor budget is still K per prime; the same occurrence cannot replenish itself between packets.

All actual historical ancestor capacities are eventually in (0,1), so replacing them by K=1 only strengthens the rejected supplier. The argument does not claim a positive lower bound for the complete VF defect, since all non-ancestor primes and all remaining physical seats are outside this restricted resource.

**Why this is different from yesterday.** A single SF1 family in [N,2N) has total charge <=2N/log N. It therefore cannot, by itself, refute an O(N log N) remainder repair. CR3 is the genuinely larger joint family needed for that stronger no-go. This is a scope clarification of SF2-SF4, not a retraction of their valid exact-capacity claims.

**Limit of CR2's small-return regime.** A cap k_N=exp(O(sqrt(log N))) can contain at most N k_N sites of F_N, a vanishing proportion `O(k_N log^3 N/N)`. The dense rectangle cannot be covered by declaring all its q-families separately sparse and discarding their resource/return interactions. CR1 may still provide ample donor capacity for a larger k: that fact alone does not keep (8) within N log N. Large unfinished temporal packets, not just availability of negative primes, must be controlled.

#### CR4. Complete Original Return And Covariance

For any finite original history ending at T, include the anchor -D_2=-2. Let C_F(T) retain EVERY unselected positive site, EVERY unused prime coefficient, and all original squareful sites unless actually selected. The original finite initial part below N0 is retained under the SAME coefficient partition: if a first-shell donor lies below N0, its used fraction belongs to Q and only its unused fraction belongs to C_F. No initial prime is retained twice. Then exactly

```text
-D_T=C_F(T)+Q(T),
D_T^2=C_F(T)^2+Q(T)^2+2 C_F(T)Q(T).                  (11)
```

The mixed term is not discarded because Q is small or nonpositive. Its sign depends on C_F. The canonical square retains
`D_can(T)^2=D_T^2-2sqrt(2)D_T+2`.

On one completed packet, if X is selected positive mass, Y is the full donor negative magnitude and C is the entire other source including the anchor, the same equality reads

```text
(C+X-Y)^2
 =C^2+X^2+Y^2+2CX-2CY-2XY
 =C^2+(Y-X)^2-2C(Y-X).                              (12)
```

This preserves all source diagonals, cross-owner/root terms, donor/source interactions and products between used and unused fractions of a prime. A zero packet does NOT create an extra negative energy credit. No sum of isolated packet squares is substituted for (11).

At the original final one-block #915 normalization still retain

```text
Source(R)=D_(R+1),
beta_R=m_R+(1-2w_R)P_R,
TotalMass(R)=(|D_R|+beta_R)^2.
```

If history is decompressed, its exact existing cost remains
`4 U V+2 beta_R(U+V-|U-V|)`. CR1-CR3 do not enlarge this denominator, assert a first-bad premise, establish returned-mask admission, or prove `2 Source^2<=TotalMass`.

Because Q(T)=o(T/log T), replacing -D_T by the fully defined residual C_F(T) preserves the canonical bound up to harmless constants. A bound for that COMPLETE residual is consequently **TARGET_EQUIVALENT**, not a newly narrowed independent supplier.

#### CR5. Executed Exact Falsification And Source Tests

The complete reproducer below uses exact trial division by a sieved list covering every square root involved. No probabilistic primality test is used. Logs use rational range reduction and 24 terms of the atanh series with explicit geometric tail; weights are rounded OUTWARD to denominator 10^14. No floating-point sign decision is used.

| Test | Genuine demand | Genuine donor capacity | Maximum used fraction |
| --- | --- | --- | --- |
| q=490001, 435 distinct source/donor pairs | [33.596182706,33.596182707] | [401.403811100,401.403811101] | [0.084907062,0.084907063] |
| held-out q=1000003, 435 pairs | [32.695489542,32.695489543] | [402.304506351,402.304506352] | [0.082411274,0.082411275] |

Every donor is in root r(n)-1, >q, and in the original [A,B) half-history for these TWO finite fixtures. The maximum distance from r(n)^2 down to its selected prime is 174 and 161 respectively. This is not an all-scale previous-square-prime theorem. The all-scale result only asserts the h_N-cell construction above.

The first fixture starts with n=125453486027, r=354194, donor=125453389613; its last pair is n=231257441953, r=480892, donor=231257115659. Deterministic full-record SHA256 values are in the output below. No endpoint sieve up to q^2 was run.

**Resource-reuse counterexamples.** At r=21, the actual squarefree seats `465=3*5*31` and `483=3*7*23` each fit under donor 439's charge separately. Together their demand exceeds its one genuine capacity by `[0.006664189,0.006664190]`. The fixed scan began at r=16; no global minimality claim outside that search is made.

At r=145 the stronger distinct-owner certificate is

```text
21027=3*43*163,  21185=5*19*223,
21203=7*13*233, 21307=11*13*149,
shared nearest donor=21023, at original root 144.
```

All four least owners AND greatest-prime tags differ. Each pair fits, but total positive demand `[0.805953097,0.805953098]` exceeds the donor capacity `[0.798227505,0.798227506]` by `[0.007725592,0.007725593]`. This refutes the specified independent-family reuse rule, not global prime-resource availability.

Other checks: 704 exact full-square substitutions; complete physical run reconstruction at N=16,32,64,128; a genuine three-shell schedule on N=64,128,256 with 36 packets, 1344 selected composites and 21269 distinct donor primes; total used fraction below 0.063949062 at every donor; 457 root cuts with at most three open packets and prefix debt at most 8.689802460. These small schedules use actual directly verified capacity, not a claimed explicit PNT threshold. Their prime weights and unfinished prefixes are certified; the general theorem is the proof above.

The dense-rectangle tests check unique factorization, all sites, root admission and once-only ancestors at N=10000 and N=90000. They test the exact construction, not the asymptotic inequality's unknown threshold. No fitted exponent or new numerical RH claim is made.

### E. Quantitative Consequence

CR1-CR2 give a proper-source chronological bound using genuine physical negative prime charge and classical PNT, with uniform simultaneous expenditure. They can remove selected positive populations whose total magnitude exceeds N log N while controlling their unfinished signed prefix below that scale. This is an independent arithmetic restriction on a strict subsource.

CR3 proves an above-tolerance, fixed-depth obstruction to a specific ancestor-only supplier. It does not preclude non-divisor compensation. CR4 preserves the complete scalar and square; the complement remains quantitatively OPEN. New complete-source exponent gain is **UNKNOWN / NONE ESTABLISHED**. `eta_gate=SEARCH_BROAD`.

### F. Falsification And Circularity Review

- PNT is applied to exact interval counts; every prime weight remains literal. No random signs, conditional independence or local prime-density replacement is used.
- The error assumption (1) is paid by a known, weak classical PNT rate. It is not a hidden von Koch or improved 7/8 assumption. The separate power corollary keeps its stronger supplier explicit.
- All scale choices are fixed functions of N before choosing the positive population. Bounds are uniform over that entire class. Constants do not depend on F, q, owner labels or T.
- Donors are strictly earlier. Their global fraction is bounded before combining dyadic shells. New charges are not generated when the same prime belongs to two donor pools.
- The squarefree processed carrier is verified for the old witnesses and CR3. The general theorem uses the full raw positive carrier and never labels squareful terms Mobius-active.
- CR2 does not survive arbitrary donor deletion merely because a mask has large density. Condition (3) must be reproved for the ACTUAL retained donor set.
- The old exact ancestry overload remains valid, but its sparse support is too small to refute an allowed N log N remainder. CR3 supplies a different, genuinely larger population.
- Root-lag one is FINITE evidence only; a universal preceding-square prime assertion is not supplied by PNT. No first-bad configuration has been numerically or theoretically constructed.
- The author performed a self-audit, not an independent Referee review. Existing compiled identities and recent green CI do not formalize CR1-CR5.

### G. Conceptual Interpretation

Prime-factor ancestry and chronological negative supply are different resources. A family may have a severe divisor-neighborhood deficit yet admit an inexpensive, occurrence-faithful response from coprime primes. Conversely, many individually sparse factor families can form a dense physical source whose ancestor-only deficit exceeds the canonical tolerance.

The relevant question is therefore not whether each family can find a donor. It is whether all selected families can share the genuine prime resource and keep every unfinished chronological packet within the allowed return scale. CR1-CR2 answer that on a growing but sparse class; CR3 and the finite collisions explain why the conclusion cannot simply be applied separately to every owner.

### H. Competing Mechanisms

| Mechanism | Established | Independent gap / obstruction | Disposition |
| --- | --- | --- | --- |
| Bounded ancestor payment plus canonical-sized remainder | CR3 genuine dense rectangle violates it for every fixed capacity | No repair by squarefreeness, factor-depth three, or packet repetition under the same capacity | REFUTED at exactly this scope |
| Globally budgeted chronological non-divisor packets | CR1-CR2, uniform load and signed unfinished return | General returned-mask bridge and dense-class return are not established | CONTINUE as a proper-source tool |
| Independent nearest-donor payment per owner | Each isolated pair may fit | r=145 spends the same prime four times | REFUTED aggregation rule; not all matching |
| Logarithmic/theta coordinate change alone | Existing main identity | No new independent estimate | Do not rederive as progress |
| Full residual after sparse removal | Exact CR4 | Canonical-sized estimate remains target-equivalent | OPEN, not claimed narrower |

### I. Specialist Handoffs

**Coordinator:** register CR1-CR4 as PAPER_PROOF/SELF_AUDIT, not accepted formal work. The new concept is a globally budgeted, non-divisor chronological response with a controlled unfinished prefix. CR3 strengthens the ancestry no-go to include an N log N residual, while explicitly correcting any overreading of SF3's sparse scope. Do not make this the team's compulsory route. JOH remains Owner's next protected turn.

**Adversarial Referee:** first reconstruct (3)-(8) from the statement. Check PNT normalization, the two-packet/two-shell count, every donor fraction and the prime-square endpoints. Attempt to violate the budget at a dyadic boundary or by a final partial cell. Independently check CR3's constants 1/200 and 1/50 and that all ancestors are genuinely historical. Distinguish the raw physical source from the clipped first-owner graph. No new Lean work should precede this review.

**Prime Census:** independently reproduce the two 435-seat donor fixtures and the r=145 four-owner collision using exact primality and certified logs. The discriminator is EACH global prime fraction, not isolated pair signs. No larger range or exponent fit is needed. Existing pending JOH LC4 arrival-cell fixtures remain a separate higher-priority protected-route support item; this request does not claim they ran.

**Finite Wheel:** the dense CR3 rectangle is an exact shared-ancestry stress test for any proposed capacity plus tolerable residual. A donor outside all factors can pay raw VF charge but is NOT an admissible divisor-parent edge. Your CORR4 auxiliary-sign interpolation results stay on their different carrier; no transfer is claimed.

**Analytic Type II:** the needed class extension is the genuine interval-deficit statement in J, with original weights and a globally compatible fraction of actual prime supply. Fixed-prefix error alone pays only the much coarser h_N return. M1-M6's Mobius/AP log savings do not automatically apply to this prime-indicator source. No OAI equality is asserted.

**Lean Verification:** no proof branch or PR request until independent scope acceptance. If selected as useful after review, CR1's finite weighted allocation and exact prefix-sign statement is an implementation-sized interface; its all-scale corollary additionally needs the actual quantitative PNT bridge. CR3 additionally needs PNT for fixed-ratio intervals. Keep actual suppliers explicit. Unrelated #1094 was draft at intake and was merged during this run; its status is refreshed below.

### J. First Independently Missing Lemma

CR1-CR2 are closed proper-source statements. They do NOT provide a smaller last lemma for the complete canonical defect. No qualified replacement for full #915 payment has been proved, and the residual in (11) is target-equivalent.

A precise, genuinely PROPER-class next hypothesis is **OPEN-VF-CR-DENSE**, on CR3's actual depth-three rectangle. Set `a_N=1/ceil(log N)^2`, `y_p=1-w_(floor sqrt p)`, and for integer N<=u<v<=2N define

```text
J_N(u,v)=sum_(n in F_N, u<=floor sqrt n<v) w_(floor sqrt n)
         -a_N sum_(prime p, u^2<p<v^2) y_p.

Conjectural proper-class bound:
exists C,N0, forall integers N>=N0,
  max_(N<=u<v<=2N) max(J_N(u,v),0) <= C N log N.      (OPEN-VF-CR-DENSE)
```

All endpoints, primes, multiplicities, source weights and the reserved prime fraction are specified. This is a rolling-interval deficit for a strict subpopulation with a deliberately limited non-divisor resource. It is NOT asserted, not inferred from (9), not equivalent by any proved theorem to RH, and not a complete consumer by itself. Dyadic resource fractions a_N are compatible eventually; a source-faithful chronological matching/initial-and-terminal return would still need to be supplied before using such a bound. The current coarse PNT windows do not prove this at N log N scale.

The smallest useful future test is to reconstruct J_N exactly from per-root counts/weights and find a violated proposed explicit constant or claimed sign, not fit an exponent with unknown C. The mathematical task is to obtain a new estimate for these actual short weighted deficits, or show that a proposed estimate only reuses a hidden prime-gap theorem. A bound for the COMPLETE C_F is not relabeled as this narrower question.

Next protected **JOH** work remains the sampled genuine floor-Li backlog U(N) after LC4's already paid O(N) placement sector. This report does not reset that derivation or the SAT OPEN-SAT-I checkpoint.

### K. Continuity, Evidence And Resume Capsule

Two-day report snapshot at intake: **4651229e596a82fdf1ce570d2326720d5803b5b9**. Today's available findings, relevant handoffs and yesterday's continuation sections were read after retrieving their bytes; this is not a claim to independently verify every upstream proof or execute every embedded program.

Consumed: Nov4 Owner SF1-SF5 and LC1-LC5; Nov5 Owner RC1-RC6; Coordinator C53-C57 and its route allocation; Wheel F1-F4; Census R=57/58 joint-cap gaps; Referee's growing-rule scope and independent finite verdicts; Lean's C49 PR-head result. Analytic TODAY=PENDING at intake, YESTERDAY=CARRY_FORWARD to Nov4 P1-P10, CF1-CF3, M1-M6. Different-carrier results are continuity evidence, not unproved VF suppliers. External inbox **038018145c0fddb2f6306c0712373adf9cd1ea52** has no entry after Oct18; EXT-20261014-5 and the existing historical-compression warnings retain their stated scopes.

At intake the only open/draft PR was #1094, head **1ea4a8a4308976721a3841998d6c3a4554f7a9c9**. All 12 returned workflows associated with that head were freshly checked completed/success, including Nyman correction run **42011040577**. The final refresh at approximately **2026-11-05T13:44Z / 08:44 EST** found **NO OPEN OR DRAFT PRS** and separately verified #1094 merged at **2026-11-05T13:35:24Z** into **884de7a1fa7687d483a7b5272bff6c9d53790367**, with that same proof head. #1093 is also MERGED; all 12 returned workflows associated with its final proof head **a54f0cf9535c548920dae3412e3fbe6d6584e029** succeeded, including **41955044802**. #1092, #1091, #1090, #1085 and #1087 are merged. The detailed terminal axiom/log audit is carried from the retrieved Lean/Coordinator reports, NOT falsely described as a fresh log audit here. No new or local Lean execution occurred. The final same-day directory refresh found the same upstream report blobs; Analytic remains TODAY=PENDING / YESTERDAY=CARRY_FORWARD.

The early checkpoint commit **875b3cdcf4fe39e86fa3510229f491ba9a6eb3e4**, blob **dc160adaaf43747b40e6c1e35d0358ab9c29e3dc**, was inspected and fetched at its immutable commit: exact bytes matched, and only this authorized daily report changed. All prior report text is preserved.

```text
RUN: 20261105-owner-2; scheduled 08:09:01 EST; RUN_ID_UNAVAILABLE.
MAIN_FINAL: 884de7a1fa7687d483a7b5272bff6c9d53790367.
MAIN_INTAKE: ff620da3c0d2c29585805960c6be183c07f16556.
AUTHORITY_AND_VF_BLOBS: unchanged by exact final comparison.
PR1094: merged during this invocation; final open/draft list empty.
POLICY: NO_PIGEONHOLING_ROUTE_SELECTOR_V1,
        ffd8f1c65cc4da656174956d4e03b48bea46768b.
PRIMARY: VF-LOW; original w_r-1_Prime on open odd square seats.
CR1: weighted earlier-prime reserve, load <=32k/N, exact zero packets.
CR2: simultaneous dyadic allocation, every donor total <=1/2,
     Q(T)<=0 and classical-PNT sub-von-Koch unfinished return.
CR3: dense three-prime rectangle defeats ancestor capacity PLUS C N log N.
CR4: complete source/Gram and original NNS denominator restored.
CR5: exact donor fixtures and cross-owner reuse counterexamples.
FORMAL/REVIEW: new claims not formalized; independent review PENDING.
FIRST PROPER GAP: OPEN-VF-CR-DENSE; no full-residual bound supplied.
GATE: SEARCH_BROAD; new net endpoint gain UNKNOWN.
LAST THREE OWNER ROUTES: JOH (Nov4 owner-3), SAT (Nov5 owner-1),
                        VF-LOW (this actual invocation).
NEXT: JOH sampled backlog U, preserving LC4 placement payment.
NO REPEAT: single-q overload as evidence against a tolerance repair,
          isolated local pair signs, tiny OAI slot optimization,
          unrelated same-head CI reruns, or unchanged large censuses.
```

Verifier SHA256: **62cfb88414ba393495d8b7e0fd80b8eddf5ad17babed009173b2ac811d706b96**. The exact final verifier/output follow. Only this own report is a remote write target. No source, policy, other report, issue, proof branch, PR, workflow, schedule, permission or main mutation; no agent launch or merge. Direct shell GitHub access returned HTTP 403; the connected GitHub tools worked. Final publication is claimed only after commit inspection and exact immutable readback.

### Reproducibility Appendix - This Invocation

The following is the complete final verifier. It is a finite evidence generator, not a Lean proof or a numerical verification of the asymptotic threshold.

```python
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
from math import isqrt
import hashlib
import json


def sieve(limit):
    a = bytearray(b'\x01') * (limit + 1)
    a[0:2] = b'\x00\x00'
    for p in range(2, isqrt(limit) + 1):
        if a[p]:
            a[p*p:limit+1:p] = b'\x00' * ((limit-p*p)//p+1)
    return [n for n in range(2, limit + 1) if a[n]]


PRIMES = sieve(1_000_004)
PSET = set(PRIMES)


def is_prime(n):
    if n < 2:
        return False
    for p in PRIMES:
        if p*p > n:
            return True
        if n % p == 0:
            return n == p
    raise AssertionError('insufficient trial-prime table')


def previous_prime(n):
    a = n - 1
    if a % 2 == 0:
        a -= 1
    while not is_prime(a):
        a -= 2
    return a


def atanh_log(y, terms=24):
    u = (y-1)/(y+1)
    assert 0 <= u <= F(1, 3)
    z = u
    total = F(0)
    for j in range(terms):
        total += 2*z/(2*j+1)
        z *= u*u
    tail = 2*z/((2*terms+1)*(1-u*u))
    return total, total+tail


LN2 = atanh_log(F(2))
DEN = 10**14


def lower_grid(x):
    return F(x.numerator*DEN//x.denominator, DEN)


def upper_grid(x):
    return F(-((-x.numerator*DEN)//x.denominator), DEN)


@lru_cache(None)
def weight_interval(r):
    assert r >= 2
    x = F(2*r*r+2*r+1, 2)
    h = x.numerator.bit_length()-x.denominator.bit_length()
    while x < 2**h:
        h -= 1
    while x >= 2**(h+1):
        h += 1
    lo, hi = atanh_log(x/F(2**h))
    lo += h*LN2[0]
    hi += h*LN2[1]
    num = 2+F(1, r)
    return lower_grid(num/hi), upper_grid(num/lo)


def show_interval(lo, hi, digits=9):
    scale = 10**digits
    a = lo.numerator*scale//lo.denominator
    b = -((-hi.numerator*scale)//hi.denominator)
    def fixed(v):
        sign = '-' if v < 0 else ''
        v = abs(v)
        return sign+str(v//scale)+'.'+str(v % scale).zfill(digits)
    return [fixed(a), fixed(b)]


def family_certificate(q):
    small = [p for p in PRIMES if 500 <= p <= 700]
    assert is_prime(q) and len(small) == 30
    records = []
    xlo = xhi = ylo = yhi = F(0)
    ratios = []
    for a, b in combinations(small, 2):
        n = q*a*b
        assert q < 4*a*b and a*b < q and a < b < q
        r = isqrt(n)
        assert r*r < n < (r+1)**2
        donor = previous_prime(r*r)
        assert (r-1)**2 < donor < r*r
        assert donor > q and n % donor != 0
        wlo, whi = weight_interval(r)
        vlo, vhi = weight_interval(r-1)
        caplo, caphi = 1-vhi, 1-vlo
        assert caplo > 0 and whi < caplo/10
        ratios.append((wlo/caphi, whi/caplo))
        xlo += wlo
        xhi += whi
        ylo += caplo
        yhi += caphi
        records.append([n, r, donor, r*r-donor])
    assert len(records) == 435
    assert len({v[1] for v in records}) == 435
    assert len({v[2] for v in records}) == 435
    assert all((q-1)//2 <= v[1]-1 < q-1 for v in records)
    encoded = json.dumps(records, separators=(',', ':')).encode()
    return {
        'q': q, 'seats': len(records), 'donors': len(records),
        'source_root_range': [min(v[1] for v in records), max(v[1] for v in records)],
        'largest_backward_integer_gap_from_square': max(v[3] for v in records),
        'demand': show_interval(xlo, xhi),
        'donor_capacity': show_interval(ylo, yhi),
        'max_fraction': show_interval(max(v[0] for v in ratios), max(v[1] for v in ratios)),
        'records_sha256': hashlib.sha256(encoded).hexdigest(),
        'first': records[0], 'last': records[-1],
    }


def triple_seats(r):
    rows = []
    for n in range(r*r+1, (r+1)**2):
        if n % 2 == 0:
            continue
        value, factors = n, []
        for p in PRIMES:
            if p*p > value:
                break
            while value % p == 0:
                factors.append(p)
                value //= p
        if value > 1:
            factors.append(value)
        if len(factors) != 3 or len(set(factors)) != 3:
            continue
        a, b, q = factors
        if q < 4*a*b and a*b < q:
            rows.append([n, a, b, q])
    return rows


def collision_certificate():
    for r in range(16, 513):
        rows = triple_seats(r)
        if not rows:
            continue
        assert len({v[3] for v in rows}) == len(rows)
        donor = previous_prime(r*r)
        assert (r-1)**2 < donor < r*r
        assert donor > max(v[3] for v in rows)
        wlo, whi = weight_interval(r)
        vlo, vhi = weight_interval(r-1)
        if len(rows)*wlo > 1-vlo:
            assert whi < 1-vhi
            return {'root': r, 'donor': donor, 'rows': rows,
                    'demand': show_interval(len(rows)*wlo, len(rows)*whi),
                    'capacity': show_interval(1-vhi, 1-vlo),
                    'excess': show_interval(len(rows)*wlo-(1-vlo), len(rows)*whi-(1-vhi))}
    raise AssertionError('no duplicate-resource counterexample in fixed range')


def symbolic_return_checks():
    count = 0
    for c in range(-5, 6):
        for x in range(0, 8):
            for y in range(x, x+8):
                assert (c+x-y)**2 == c*c+x*x+y*y+2*c*x-2*c*y-2*x*y
                assert (c+x-y)**2 == c*c+(y-x)**2-2*c*(y-x)
                count += 1
    return count


def distinct_owner_collision():
    r = 145
    expected = [[21027, 3, 43, 163], [21185, 5, 19, 223],
                [21203, 7, 13, 233], [21307, 11, 13, 149]]
    actual = triple_seats(r)
    assert all(row in actual for row in expected)
    assert len({row[1] for row in expected}) == 4
    assert len({row[3] for row in expected}) == 4
    donor = previous_prime(r*r)
    assert donor == 21023 and (r-1)**2 < donor < r*r
    lo, hi = weight_interval(r)
    vl, vh = weight_interval(r-1)
    assert hi < 1-vh and 4*lo > 1-vl
    return {'root': r, 'donor': donor, 'rows': expected,
            'demand': show_interval(4*lo, 4*hi),
            'capacity': show_interval(1-vh, 1-vl),
            'excess': show_interval(4*lo-1+vl, 4*hi-1+vh)}


def multiscale_packet_checks():
    packets = []
    prime_load = {}
    selected_sites = set()
    for N in (64, 128, 256):
        h, k = isqrt(N), 3
        for b in range(N, 2*N, h):
            a, c = b-h, min(b+h, 2*N)
            source = []
            donor = []
            for r in range(b, c):
                odd_composites = [n for n in range(r*r+1, (r+1)**2)
                                  if n % 2 and n not in PSET]
                for n in odd_composites[:k]:
                    assert (r, n) not in selected_sites
                    selected_sites.add((r, n))
                    lo, hi = weight_interval(r)
                    source.append((r, n, lo, hi))
            for p in PRIMES:
                if p <= a*a:
                    continue
                if p >= b*b:
                    break
                s = isqrt(p)
                assert a <= s < b
                lo, hi = weight_interval(s)
                donor.append((s, p, 1-hi, 1-lo))
            xlo = sum((v[2] for v in source), F(0))
            xhi = sum((v[3] for v in source), F(0))
            ylo = sum((v[2] for v in donor), F(0))
            yhi = sum((v[3] for v in donor), F(0))
            assert ylo > 0
            llo, lhi = xlo/yhi, xhi/ylo
            assert 0 < llo <= lhi < F(1, 2)
            for s, p, lo, hi in donor:
                prime_load[p] = prime_load.get(p, F(0))+lhi
            packets.append((N, a, b, c, source, donor, llo, lhi, xlo, xhi))
    assert max(prime_load.values()) < F(1, 2)
    max_open = 0
    max_debt_upper = F(0)
    for t in range(56, 513):
        open_count = 0
        debt_upper = F(0)
        for N, a, b, c, source, donor, llo, lhi, xlo, xhi in packets:
            if t <= a or t >= c:
                continue
            open_count += 1
            if t < b:
                debt_upper += lhi*sum((v[3] for v in donor if v[0] < t), F(0))
            else:
                debt_upper += sum((v[3] for v in source if v[0] >= t), F(0))
        assert open_count <= 4
        max_open = max(max_open, open_count)
        max_debt_upper = max(max_debt_upper, debt_upper)
    return {'dyadic_scales': [64, 128, 256], 'k_per_root': 3,
            'packets': len(packets), 'selected_sites': len(selected_sites),
            'donor_prime_occurrences': len(prime_load),
            'max_combined_fraction_upper': show_interval(max(prime_load.values()), max(prime_load.values())),
            'tested_root_cuts': 457, 'max_open_packets': max_open,
            'max_prefix_debt_upper': show_interval(max_debt_upper, max_debt_upper),
            'prefix_sign': 'nonpositive by exact chronological form'}


def sparse_full_source_checks():
    # Exact rational intervals enclose all VF weights on the actual odd seats.
    results = []
    for nroot in (16, 32, 64, 128):
        selected = []
        donors = []
        for r in range(nroot, 2*nroot):
            rows = triple_seats(r)
            if rows:
                p = previous_prime(r*r)
                assert (r-1)**2 < p < r*r
                selected.append((r, rows[0][0]))
                donors.append((r-1, p))
        assert len(set(donors)) == len(donors)
        sel = set(selected)
        don = set(donors)
        assert sel.isdisjoint(don)
        alo = ahi = clo = chi = xlo = xhi = ylo = yhi = F(0)
        for r in range(nroot-1, 2*nroot):
            lo, hi = weight_interval(r)
            for n in range(r*r+1, (r+1)**2):
                if n % 2 == 0:
                    continue
                prime = int(n in PSET)
                zlo, zhi = lo-prime, hi-prime
                alo += zlo
                ahi += zhi
                if (r, n) in sel:
                    assert not prime
                    xlo += lo
                    xhi += hi
                elif (r, n) in don:
                    assert prime
                    ylo += 1-hi
                    yhi += 1-lo
                else:
                    clo += zlo
                    chi += zhi
        assert alo == clo+xlo-yhi and ahi == chi+xhi-ylo
        results.append({'N': nroot, 'selected': len(sel), 'donors': len(don),
                        'full_signed_run': show_interval(alo, ahi),
                        'return_verified': True})
    return results


def adversarial_guard_checks():
    # Required structural guards fail for these deliberately invalid variants.
    assert not (weight_interval(16)[1] < F(1, 10)*(1-weight_interval(15)[1]))
    a = (101, 503)
    assert len(set([a, a])) != len([a, a])
    assert isqrt(101**2)**2 == 101**2
    return {'small_root_one_tenth_guard': 'rejected',
            'duplicated_donor_occurrence': 'rejected',
            'square_boundary': 'excluded'}


def dense_rectangle_checks():
    result = []
    for N in (10000, 90000):
        small = [p for p in PRIMES if p*p > N and 100*p*p <= 121*N]
        large = [q for q in PRIMES if 2*q > 3*N and 4*q <= 7*N]
        roots = {}
        values = set()
        for q in large:
            qroots = set()
            for a, b in combinations(small, 2):
                n = a*b*q
                r = isqrt(n)
                assert N <= r < 2*N and r*r < n < (r+1)**2
                assert q < 4*a*b and a*b < q
                assert a < b < q < N*N
                assert a < N
                assert r not in qroots and n not in values
                qroots.add(r)
                values.add(n)
                roots[r] = roots.get(r, 0)+1
        count = len(large)*len(small)*(len(small)-1)//2
        assert count == len(values) and count > 0
        result.append({'N': N, 'small_prime_count': len(small),
                       'large_prime_count': len(large), 'seats': count,
                       'ancestor_count': len(small)+len(large),
                       'root_range': [min(roots), max(roots)],
                       'max_root_occupancy': max(roots.values())})
    return result


if __name__ == '__main__':
    print(json.dumps({'preregistered_families': [family_certificate(q) for q in (490001, 1000003)],
                      'duplicate_resource_counterexample': collision_certificate(),
                      'distinct_owner_collision': distinct_owner_collision(),
                      'complete_square_substitutions': symbolic_return_checks(),
                      'full_source_checks': sparse_full_source_checks(),
                      'multiscale_packet_checks': multiscale_packet_checks(),
                      'dense_rectangle_checks': dense_rectangle_checks(),
                      'guards': adversarial_guard_checks()}, indent=2))

```

Executed output (exit status 0; syntax compilation also succeeded):

```json
{
  "preregistered_families": [
    {
      "q": 490001,
      "seats": 435,
      "donors": 435,
      "source_root_range": [
        354194,
        480892
      ],
      "largest_backward_integer_gap_from_square": 174,
      "demand": [
        "33.596182706",
        "33.596182707"
      ],
      "donor_capacity": [
        "401.403811100",
        "401.403811101"
      ],
      "max_fraction": [
        "0.084907062",
        "0.084907063"
      ],
      "records_sha256": "214a4881761fd85f0d2319f05d07f19cf86987857898639a4ab185bebb740a77",
      "first": [
        125453486027,
        354194,
        125453389613,
        23
      ],
      "last": [
        231257441953,
        480892,
        231257115659,
        5
      ]
    },
    {
      "q": 1000003,
      "seats": 435,
      "donors": 435,
      "source_root_range": [
        505991,
        686989
      ],
      "largest_backward_integer_gap_from_square": 161,
      "demand": [
        "32.695489542",
        "32.695489543"
      ],
      "donor_capacity": [
        "402.304506351",
        "402.304506352"
      ],
      "max_fraction": [
        "0.082411274",
        "0.082411275"
      ],
      "records_sha256": "39dc43f2200df398006c5cae732be4c99fb6bdc73a3bf182be6a2e74ed408902",
      "first": [
        256027768081,
        505991,
        256026892073,
        8
      ],
      "last": [
        471954415859,
        686989,
        471953886101,
        20
      ]
    }
  ],
  "duplicate_resource_counterexample": {
    "root": 21,
    "donor": 439,
    "rows": [
      [
        465,
        3,
        5,
        31
      ],
      [
        483,
        3,
        7,
        23
      ]
    ],
    "demand": [
      "0.667341365",
      "0.667341366"
    ],
    "capacity": [
      "0.660677176",
      "0.660677177"
    ],
    "excess": [
      "0.006664189",
      "0.006664190"
    ]
  },
  "distinct_owner_collision": {
    "root": 145,
    "donor": 21023,
    "rows": [
      [
        21027,
        3,
        43,
        163
      ],
      [
        21185,
        5,
        19,
        223
      ],
      [
        21203,
        7,
        13,
        233
      ],
      [
        21307,
        11,
        13,
        149
      ]
    ],
    "demand": [
      "0.805953097",
      "0.805953098"
    ],
    "capacity": [
      "0.798227505",
      "0.798227506"
    ],
    "excess": [
      "0.007725592",
      "0.007725593"
    ]
  },
  "complete_square_substitutions": 704,
  "full_source_checks": [
    {
      "N": 16,
      "selected": 13,
      "donors": 13,
      "full_signed_run": [
        "2.211146739",
        "2.211146740"
      ],
      "return_verified": true
    },
    {
      "N": 32,
      "selected": 31,
      "donors": 31,
      "full_signed_run": [
        "2.969532349",
        "2.969532350"
      ],
      "return_verified": true
    },
    {
      "N": 64,
      "selected": 64,
      "donors": 64,
      "full_signed_run": [
        "7.259622938",
        "7.259622939"
      ],
      "return_verified": true
    },
    {
      "N": 128,
      "selected": 128,
      "donors": 128,
      "full_signed_run": [
        "25.394645724",
        "25.394645725"
      ],
      "return_verified": true
    }
  ],
  "multiscale_packet_checks": {
    "dyadic_scales": [
      64,
      128,
      256
    ],
    "k_per_root": 3,
    "packets": 36,
    "selected_sites": 1344,
    "donor_prime_occurrences": 21269,
    "max_combined_fraction_upper": [
      "0.063949061",
      "0.063949062"
    ],
    "tested_root_cuts": 457,
    "max_open_packets": 3,
    "max_prefix_debt_upper": [
      "8.689802459",
      "8.689802460"
    ],
    "prefix_sign": "nonpositive by exact chronological form"
  },
  "dense_rectangle_checks": [
    {
      "N": 10000,
      "small_prime_count": 4,
      "large_prime_count": 260,
      "seats": 1560,
      "ancestor_count": 264,
      "root_range": [
        12497,
        14285
      ],
      "max_root_occupancy": 6
    },
    {
      "N": 90000,
      "small_prime_count": 4,
      "large_prime_count": 1906,
      "seats": 11436,
      "ancestor_count": 1910,
      "root_range": [
        113534,
        125004
      ],
      "max_root_occupancy": 6
    }
  ],
  "guards": {
    "small_root_one_tenth_guard": "rejected",
    "duplicated_donor_occurrence": "rejected",
    "square_boundary": "excluded"
  }
}

```

### Publication Receipt - 20261105-owner-2

**2026-11-05T08:47:22-05:00: COMPLETE / PUBLISHED / VERIFIED.** The substantive report and complete executed verifier were committed as **4c293e33720e34e02c419f97780db6aabb0e630b**, report blob **c1ecd0c9e1308befea90ea959e27c305f492a41f**. The commit was inspected: only `research/agent_reports/2026-11-05/10-owner-payment.md` changed. Re-fetching that path at the immutable commit returned EXACTLY the submitted content, preserving all 62,473 earlier characters. The report was freshly fetched again before adding this receipt. This receipt's resulting commit is also checked by immutable readback before the user-facing completion notice.

Final research status: CR1-CR2 PAPER_PROOF, CR3 PAPER_PROOF/REFUTED supplier, CR4 IDENTITY_ONLY, CR5 FINITE_COMPUTATION. Independent review and Lean formalization are PENDING; the complete canonical arithmetic bound remains OPEN. No execution or endpoint gain is promised after this invocation. Resume the next actual protected JOH turn from the existing LC4/LC5 backlog checkpoint; retain OPEN-VF-CR-DENSE for the next eligible VF-LOW investigation.


## Scheduled JOH Continuation Checkpoint - 2026-11-05 16:15 EST Invocation

### A. Mathematical Question

**IN_PROGRESS / PARTIAL.** Resume 20261104-owner-3/LC4-LC5: the genuine all-cell position error is already paid at O(N), while the weighted count-level backlog remains OPEN. This invocation investigates growing multi-cell count increments and a source-exact coarse-clock reconstruction, including the initial level, unequal prime counts, original boundaries and full mixed terms. No new bound or sign is claimed at this checkpoint.

### B. Authority And Continuity

Actual trigger: SCHEDULED, 2026-11-05T16:15:00-05:00; RUN_ID_UNAVAILABLE; local label **20261105-owner-3**. Checkpoint prepared 16:18 EST. Main **1667c3cf9b4e898bb9afd62ec48e24610b2156ab**, AGENTS **547dda0d9456e7a4e1165dc72d59da6f70d5c023**, proof contract **7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c**, independent-routing policy **ffd8f1c65cc4da656174956d4e03b48bea46768b**. deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1. Protected route JOH follows today's SAT and VF-LOW attempts; next SAT. No mandatory unrelated OAI audit.

November 4 and 5 reports from all seven roles and external inbox were retrieved; TODAY=AVAILABLE, YESTERDAY=CARRY_FORWARD. LC4/LC5 remain paper/self-audit, not independently accepted or newly formalized. Latest Coordinator's JOH shorthand omits the -1 centering; this run retains the original B(n)=pi(n)-floor(Li_2(n))-1 and its original G. All later claims use that convention explicitly. Latest merged work includes #1093/#1094 Nyman interfaces/obstruction and #1095 Euler axiom-audit repair; open/draft collection is empty at intake. None supplies a JOH estimate.

Original source bytes inspected: signed-population balance **9a9336dad72171b6d572a1c1ae88d1ae8b56b530**, discrete backlog **4255ca0dffe480f2aec6bd0b68797bbd293396c3**, transport cancellation **eb84f59055bd31dc117be034d45c92eb9dab8f27**, JOH consumer note **27e28f09e9f79e8a60d524e5fcb6f19904fa55f5**, canonical criterion **79030d70e8d3e0d08eef9bac53fef95c36eca2fb**. The native Lean backlog lacks the centering -1; eta(k) is the native primitive at k-1. Canonical actual-prime von Koch target remains OPEN.

### C. Derivation And Falsification Plan

Compare two distinct moves: an independent arithmetic estimate for growing arrival-clock count increments, and exact coarse-clock compression with an explicit proper-sector error. Audit whether a variance estimate controls the retained level or merely discards the zero-frequency/anchor component. Test the smallest meaningful genuine floor-Li arrival configurations, including prime-at-boundary and partial terminal blocks. Reuse certified floors rather than claiming uncertain numerical floors exact. Preserve LC3's W(512)=1 and W(2048)=3 counterexamples; do not rerun the disproved midpoint sign route.

### D-K. Pending Work

Research derivation, decisive tests, literature qualification, full quantitative relevance, and specialist handoffs remain PENDING. No local Lean execution, source/PR edit, agent launch, policy/schedule change or merge. Only this existing own report is updated. Final publication will require current-blob refresh, commit inspection and exact immutable readback.

## Scheduled JOH Final Synthesis - 20261105-owner-3

Actual invocation: **2026-11-05T16:15:00-05:00**, SCHEDULED, America/New_York; RUN_ID_UNAVAILABLE. This completes the preceding checkpoint, not a separate run. Protected route **JOH** follows today's SAT and VF-LOW work; next **SAT**. New proofs below are **PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED** unless explicitly classified otherwise. No literature-originality claim or complete-endpoint gain.

### A. Most Important Mathematical Development

**A classical continuous prime-interval estimate transfers to the ACTUAL integer floor-Li arrival clock, with a proved sampling and moving-endpoint correction.** Put h=floor(X^(1/4)), let b_j be the original integer floor-Li arrivals, and retain the full upper halo b_(j+h). Then the genuine uncentered count energy satisfies, for every sufficiently large real X,

```text
V_clock(X) = sum_(X<=b_j<2X) [pi(b_(j+h))-pi(b_j)-h]^2
          << X h^2 (log log X)^2 / (log X)^3.             (MC2)
```

This is an independently justified logarithmic restriction on multi-cell COUNT innovations, not just on the already-paid within-cell placement. It saves (log log X/log X)^2 relative to the elementary O(X h^2/log X) envelope. Its independent inputs are Zaccagnini's established short-interval mean square and Montgomery--Vaughan's uniform interval prime upper bound, not RH or the imported 7/8 theorem. The new work here is the exact-source transfer; the external analytic estimates are not claimed as new.

**The quantitative gap is still polynomial.** The previously proposed OPEN-JOH-CLOCK-VAR asks for O(X h (log X)^A), whereas MC2 retains h^2. At h approximately X^(1/4), that is an extra X^(1/4), up to logarithms. No fixed exponent improvement follows. An explicit finite telescope below calibrates a hypothetical X^(-kappa) saving at the Xh level to prime-error exponent 7/8-kappa/2, while retaining the initial history and boundary windows.

There is also a useful signed correction. Grouping h original cells gives an exact whole-source reconstruction with |error|=O(Nh), uniformly in the grouping and initial arrival. **The error is NOT necessarily nonnegative:** the complete genuine two-cell block [5,8) already gives -1. The positive one-cell placement property must not be carried into multi-cell arguments. Both prime and model internal displacements have to return before squaring.

| Claim | Contribution | Classification |
| --- | --- | --- |
| MC1 | Original prime-occurrence labeling, complete clipped overlap Gram | IDENTITY_ONLY |
| MC2 | Uniform logarithmic mean-square bound on actual clock increments | PAPER_PROOF, independent external ingredients, SELF_AUDIT |
| MC3 | Full h-cell return and uniform O(Nh) proper-error bound | PAPER_PROOF; exact decomposition plus independent bound |
| MC4 | Boundary telescope and hypothetical variance-to-prime-error power transfer | IDENTITY_ONLY / CONDITIONAL; supplier unproved |
| MC5 | Exact finite checks and counterexample to coarse-error nonnegativity | FINITE_COMPUTATION / REFUTED at the stated universal scope |

### B. Current Authoritative Objective

Main at intake: **1667c3cf9b4e898bb9afd62ec48e24610b2156ab**. The public arithmetic target is unchanged and OPEN:

```text
VFCanonicalSquareVonKochStatement:
exists C>=0, forall integer R>=2,
 |pi(R^2)-vfMidFinishedMass(R)-sqrt(2)| <= C R log R.
```

The original JOH coordinate used here is

```text
L(x)=Li_2(x)=integral_2^x dt/log t,
Q(n)=floor(L(n)), B(n)=pi(n)-Q(n)-1,
eta(k)=1_Prime(k)-Q(k)+Q(k-1),
G(N)=sum_(2<=n<N) B(n)=sum_(3<=k<N)(N-k) eta(k).
```

The centering -1 is essential to this definition of G. The latest Coordinator ticket writes an uncentered B in shorthand; this report does not silently adopt that change. Native Lean `vfMidPrimeFloorLiIntegerBacklog` is pi-Q; our B is that quantity minus one. Its increments agree exactly, and eta(k) is `vfMidFloorLiPrimitiveMismatch (k-1)`, not the primitive at k. Original Li_2, classical li, and canonical sqrt(2) remain distinct conventions.

Material source bytes were retrieved at the pinned main and the relevant definitions/proofs inspected:

| Source | Blob SHA |
| --- | --- |
| AGENTS.md | 547dda0d9456e7a4e1165dc72d59da6f70d5c023 |
| CURRENT_PROOF_CONTRACT.md | 7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c |
| docs/RHLEAN_INDEPENDENT_MULTIFRONT_NO_PIGEONHOLING_20261104.md | ffd8f1c65cc4da656174956d4e03b48bea46768b |
| docs/RHLEAN_NATIVE_SQUARE_CLOCK_AGENT_DIRECTIVE_20261029.md | 4fbab59cc6fcc33a4f4e7a8ef447b2f7947b53dd |
| docs/RHLEAN_SEVEN_AGENT_RESEARCH_ENGINE_20261101.md | 6c1d1c10e2755017ffe9d7f40df8b9ae7692f23a |
| research/VF_MID_FLOOR_LI_SIGNED_POPULATION_BALANCE.lean | 9a9336dad72171b6d572a1c1ae88d1ae8b56b530 |
| research/VF_MID_FLOOR_LI_DISCRETE_BACKLOG.lean | 4255ca0dffe480f2aec6bd0b68797bbd293396c3 |
| research/VF_MID_FLOOR_LI_TRANSPORT_CANCELLATION.lean | eb84f59055bd31dc117be034d45c92eb9dab8f27 |
| research/LI_FAN_ONE_SIDED_WEIGHTED_COMPOSITE_RH_CONTRACT_20261022.md | 27e28f09e9f79e8a60d524e5fcb6f19904fa55f5 |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |

Reused Lean facts include the signed mismatch/backlog telescope, ternary primitive above four, floor-rounding error less than one, exact Mobius/Abel carrier equality, and quadratic perturbation boundary identity. None is a quantitative bound on today's V_clock. The canonical terminal theorem still has its explicit ClassicalVonKochRHCriterion premise. No local or new Lean execution was performed.

Live discovery found no open/draft PR at intake. #1093, #1094 and #1095 are human-merged. At #1095 head **46e68178192c6e429a02abee9d5b8ebca5de46c8**, the three returned workflows are successful, including original Euler fractional source run **42084042187**. This verifies the current repair's workflow status, not a new JOH compiler run or a proof of MC2. The new mathematical claims have no Lean head.

### C. Structural Hypotheses Investigated

Resume **20261104-owner-3/LC4-LC5**, especially its OPEN-JOH-CLOCK-VAR question, and the November 5 Coordinator's explicit JOH count-history handoff. LC4 paid all within-one-cell displacements at O(N); repeating local midpoint signs would not advance that problem.

Two distinct moves were developed:

1. Transfer an established arithmetic mean-square estimate to literal integer arrival samples, without replacing those samples by an unproved continuous average or freezing a moving endpoint for free.
2. Compress many cells at once and recover every internal model arrival as well as every prime, so a bounded geometric error can be separated honestly from the accumulated level.

The strong Xh variance supplier was not assumed. The early checkpoint preceded the work. A separate preregistration fixed the finite core 2..4096, development through 2048, held-out through 4096, five dyadic clock windows, and h in {1,2,3,5,8} for full-prefix reconstruction. Integers 4097..4224 were certified only for the prescribed upper halo, disclosed before execution. No fitted exponent or wider supportive scan was used.

### D. Mathematical Derivation

#### MC1. Exact Prime Occurrences And The Complete Clock Gram

For j with b_j>=5 set b_j=min{n>=2:Q(n)>=j}. The compiled one-step floor fact and monotonicity give Q(b_j)=j and Q(n)=j on b_j<=n<b_(j+1). Define H_j=B(b_j). For integer h>=1,

```text
delta_j(h)=H_(j+h)-H_j=pi(b_(j+h))-pi(b_j)-h.
```

For each actual prime p assign the label lambda(p)=Q(p-1). Then, exactly,

```text
p in (b_j,b_(j+h)]  iff  j <= lambda(p) < j+h.           (MC1a)
```

Indeed b_j<p iff b_j<=p-1 iff j<=Q(p-1); and p<=b_(j+h) iff Q(p-1)<j+h. This retains a prime equal to the right arrival and excludes a prime equal to the left arrival. Q(p) is NOT an interchangeable label.

For a finite consecutive set J={u,...,v} of starting indices, let P be the actual prime set (b_u,b_(v+h)]. For each p let w(p) count its admitted starting indices; for p,q let K(p,q) count their common admitted starting indices. Explicitly,

```text
K(p,q)=max(0, min(v,lambda(p),lambda(q))
                 -max(u,lambda(p)-h+1,lambda(q)-h+1)+1),
w(p)=K(p,p).

sum_(j in J) delta_j(h)^2
 = sum_(p in P) w(p) + 2 sum_(p<q in P) K(p,q)
   -2h sum_(p in P) w(p) + h^2*#J.                     (MC1b)
```

This is the entire square, not a selected pair statistic. All same-cell and cross-cell prime pairs, prime/model mixed terms, model square and edge clipping are present. A prime can appear in several overlapping windows because that multiplicity is part of V_clock; it is recorded by w and K, not represented as independent historical payment capacity. The labels aggregate actual primes only through their exact fibers. This is not mean-centered empirical covariance or a zero-covariance assertion.

#### MC2. A Genuine Uniform Logarithmic Count-Energy Restriction

**Theorem.** There are absolute constants C and X0 such that, for all real X>=X0, with h=floor(X^(1/4)) and J_X={j:X<=b_j<2X},

```text
sum_(j in J_X) delta_j(h)^2
 <= C X h^2 (log log X)^2/(log X)^3.                    (MC2)
```

All h-cell endpoints are included, even when b_(j+h)>2X. Constants do not depend on X, j, the number of cells, prime factorizations or a chosen subsequence.

**Independent analytic inputs.** Zaccagnini's 1998 main theorem, specialized to epsilon(x)=0, states for y^(1/6)<=L0<=y that

```text
J(y,L0)=integral_y^(2y)
 |pi(t)-pi(t-L0)-L0/log t|^2 dt
 << y L0^2 (log log y)^2/(log y)^4.
```

See [Zaccagnini, Acta Arith. 84 (1998), p.225](https://matwbn.icm.edu.pl/ksiazki/aa/aa84/aa8432.pdf) and the [publisher record](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/84/3/110125/primes-in-almost-all-short-intervals). The actual fixed-length theorem statement was retrieved from the indexed primary first page; direct full-PDF access returned 403. The author's [later paper, Theorem 3.1](https://people.dmi.unipr.it/alessandro.zaccagnini/psfiles/papers/Q429.pdf) was accessible and separately checked, but its multiplicative-window version is NOT silently substituted for the fixed-length theorem.

The second input is the unconditional bound pi(z+y)-pi(z)<2y/log y for z>0,y>1, [Montgomery--Vaughan, The large sieve, Theorem 2 and (1.12), p.121](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf). Only its ordinary-prime q=1 case is used. Neither imported statement assumes RH. These two precise inputs, rather than a generic reference to PNT, are the arithmetic content being transferred.

**Step 1: exact clock geometry.** Minimality of b_j gives

```text
0 <= L(b_j)-j < 1/log(b_j-1).
```

For adjacent arrivals at or above X this implies b_(j+1)-b_j>=log X-2, for sufficiently large X: the Li increase is at least 1-1/log(X-1), while the integral is at most the integer gap divided by log X. Also #J_X is comparable to X/log X: it differs by O(1) from L(2X)-L(X), and elementary integral bounds give both sides. The upper endpoint T_j=b_(j+h) lies below 3X eventually, since the Li increase from 2X to 3X exceeds h+1. Write s_j=T_j-b_j. The exact floor relation gives

```text
|integral_(b_j)^(T_j) dt/log t - h| < 1,
s_j <= (h+1) log(3X),
s_j = h log X + O(h+log X) = h log X + O(h),            (MC2a)
```

uniformly for j in J_X. The last estimate follows by comparing 1/log t to 1/log X on [X,3X], whose difference is O(1/log^2 X), and using h>>log X. No prime distribution is used in this geometry.

**Step 2: pay the moving prime endpoint.** Set L0=h log X and t_j=b_j+L0. The difference T_j-t_j is O(h). The Montgomery--Vaughan bound on an interval of length C0 h, enlarged if necessary, gives

```text
|pi(T_j)-pi(t_j)| << h/log h << h/log X.
```

Also L0/log(t_j)-h=O(h/log X). Therefore, for

```text
f_X(t)=pi(t)-pi(t-L0)-L0/log t,
delta_j(h)=f_X(t_j)+O(h/log X).                         (MC2b)
```

This is a quantified comparison, not a replacement of the original window by a fixed interval without error. Its total squared error costs O(X h^2/log^3 X).

**Step 3: pay discrete sampling.** Set d=(log X)/4. The intervals I_j=[t_j,t_j+d] are disjoint by Step 1 and lie in [X,4X] eventually. For t in I_j, each prime-count endpoint moves at most d, hence at most d+1 integer sites; the continuous density term changes by O(1). Consequently |f_X(t)-f_X(t_j)|=O(log X), with no prime theorem needed. Integration of |f_X(t_j)|^2<=2|f_X(t)|^2+O(log^2 X) yields

```text
sum_(j in J_X)|f_X(t_j)|^2
 << [J(X,L0)+J(2X,L0)]/log X + X log X.                (MC2c)
```

This explicit local comparison is the missing discrete-sampling bridge in the earlier candidate. Density-one continuous behavior by itself was not used as a sampling theorem.

**Step 4: apply the genuine arithmetic theorem.** For all sufficiently large X, both y=X and y=2X satisfy y^(1/6)<=L0<=y. The external fixed-length estimate gives

```text
J(X,L0)+J(2X,L0)
 << X h^2 (log log X)^2/(log X)^2.
```

Combine MC2b-c. The remaining X log X term is absorbed because h^2 is comparable to X^(1/2). This proves MC2. All comparison errors are paid independently; no covariance sign or desired variance hypothesis is inserted.

**Consequence for exceptional count innovations.** For every fixed epsilon>0,

```text
#{j in J_X: |delta_j(h)|>=epsilon*h}
 << epsilon^(-2) X (log log X)^2/(log X)^3.
```

The proportion among the actual number of arrivals, comparable to X/log X, tends to zero. This is a proper-sector restriction, not an endpoint proof; the complete estimate and exceptional cost, rather than merely the phrase 'almost all', are what is available.

#### MC3. Exact Coarse-Clock Return, Including Both Signed Populations

**Theorem.** Fix an original arrival a=b_(j0)>=5, integer h>=1, and N>=a. For each coarse start c_m=b_(j0+mh)<N put t_m=min(b_(j0+(m+1)h),N), and define

```text
K_(a,h)(N)=G(a)+sum_m (t_m-c_m) B(c_m),
P_(a,h)(N)=sum_m sum_(c_m<p<t_m, p prime) (t_m-p),
D_(a,h)(N)=sum_m sum_(c_m<b_j<t_m) (t_m-b_j).
```

Then exactly

```text
G(N)=K_(a,h)(N)+P_(a,h)(N)-D_(a,h)(N),
|G(N)-K_(a,h)(N)| <= h log N * max(pi(N),Q(N)) << Nh.   (MC3a)
```

The final implied constant is absolute and uniform in a,h,N after adjustment for the finite small range. The statement does not require equal prime/model counts, complete terminal cells, a favorable sign or any first-bad condition.

**Proof.** Inside [c_m,t_m),

```text
B(n)-B(c_m)=[pi(n)-pi(c_m)]-[Q(n)-Q(c_m)].
```

Sum over integers n and use finite Fubini on the TWO original step populations. Prime/model coincidences cancel as they should. Boundary events at c_m are already in B(c_m); events at t_m belong to the next block or have zero terminal weight. The initial G(a) and partial last block are explicit.

Since Q(t_m-1)<=Q(c_m)+h-1,

```text
(t_m-1-c_m)/log N
 <= integral_(c_m)^(t_m-1) du/log u < h.
```

Every positive internal displacement is less than h log N. Each original prime and each model arrival is charged at most once in this partition. Thus 0<=P<=h log N*pi(N) and 0<=D<=h log N*Q(N). The elementary |P-D|<=max(P,D), the uniform prime-count bound and L(N)=O(N/log N) prove MC3a. For the latter, splitting the Li integral at sqrt(N) suffices; no short-interval asymptotic is assumed.

For h=1 there is no internal model arrival, D=0, recovering the prior LC4 sign. For h>1 the model return cannot be dropped. Full quadratic accounting is

```text
G^2=K^2+P^2+D^2+2KP-2KD-2PD
   =K^2+2K(P-D)+(P-D)^2.                               (MC3b)
```

In particular the square comparison costs O(Nh*|K|+N^2 h^2), not just the error square. At the separately chosen h(N)=floor(N^(1/4)), the amplitude error is O(N^(5/4)), below the external JOH RH negative-margin scale N^(3/2)/log N. This does NOT prove any sign for K. Nor does an identity at each h(N) justify a fixed-h recurrence across changing N.

This is a source comparison on G, not a new denominator or a replacement for #915's compressed NNS statistic. LC4 and MC3 are alternate decompositions, not cancellation credits to add together.

#### MC4. What A Stronger Clock Bound Would Actually Buy

For any u<=v and h>=1 the complete overlapping-window telescope is

```text
sum_(j=u..v) delta_j(h)
 = sum_(r=1..h) H_(v+r) - sum_(r=0..h-1) H_(u+r).
```

If the two right-hand averages are A_right and A_left and m=v-u+1, Cauchy gives

```text
|A_right-A_left| <= sqrt(m*sum_(j=u..v)delta_j(h)^2)/h. (MC4a)
```

No endpoint is omitted. For u=min J_X and v=max J_X, comparison of these averages to B(floor X), B(floor(2X)) costs O(h log X), using literal clock distances and the ternary primitive. Therefore

```text
|B(floor(2X))-B(floor X)|
 << sqrt((X/log X)*V_clock(X))/h + h log X.             (MC4b)
```

The anchor is not discarded: a uniform bound for these dyadic increments must be summed back to a finite starting level. Applying MC4b recursively to every integer endpoint, with the at-most-one-site odd-endpoint correction, is legitimate. A single dyadic sequence without full endpoint coverage would not suffice.

**Conditional calibration, not an established supplier.** If some fixed 0<kappa<1/4 satisfies, for every epsilon>0 and all sufficiently large real X,

```text
V_clock(X) <<_epsilon X^(5/4-kappa+epsilon),            (UNPROVED)
```

then MC4b and dyadic summation imply

```text
|pi(x)-Li_2(x)| <<_epsilon x^(7/8-kappa/2+epsilon).
```

The h log X boundary has exponent 1/4 and is lower order. Floor rounding and extension from integers to real x cost O(1). The prior Xh polylogarithmic candidate corresponds only to the 7/8 power, not a strictly better power. No claim is made that a global 7/8 prefix bound already supplies this local sum-of-squares premise.

Putting the PROVED MC2 into MC4b yields only O(X log log X/log^2 X) dyadic backlog changes, plus lower-order terms. This is weaker than known effective-PNT global error estimates, so it is not advertised as an improved global prime bound. Its value is a quantified restriction on the actual growing clock source and a precise map of the remaining loss.

### E. Quantitative Consequence

MC2 is a genuine independent all-scale improvement of a proper arithmetic energy envelope. It does not reach OPEN-JOH-CLOCK-VAR: at h approximately X^(1/4), its scale is X^(3/2)(log log X)^2/log^3 X, compared with the requested X^(5/4) polylogarithmic scale. The inherited 7/8 input was neither used nor improved.

MC3 pays all intra-coarse-block shape at O(Nh), preserving its signed return and full square. The outstanding weighted level K, or equivalently the original source after that explicit error, can still dominate. The operator H_j -> H_(j+h)-H_j annihilates constants, but that observation is only algebraic noninjectivity, not a synthetic counterexample to the actual prime sequence. MC4 is the honest way to restore endpoint levels and the finite anchor when a sufficiently strong uniform innovation estimate exists.

At N=R^2, MC3 with h=N^(1/4) costs O(R^(5/2)); this is below the JOH integrated negative-margin scale R^3/log R, not below the canonical POINTWISE target R log R. Those two normalizations must not be confused. No bound on the complete G sign, original #915 source, canonical VF or RH is obtained. **Net new endpoint gain: UNKNOWN / NONE_ESTABLISHED; ETA_GATE=SEARCH_BROAD.**

### F. Falsification And Circularity Review

**Actual finite falsifier of coarse-error nonnegativity.** The certified arrivals b_2=5, b_3=6, b_4=8 give a=5,h=2,N=8, a COMPLETE two-cell block. The only internal prime is 7, contributing P=1; the internal model arrival is 6, contributing D=2. Thus

```text
G(8)=-1, K_(5,2)(8)=0, P=1, D=2, G-K=-1.
```

The first registered partial-cut failure is already N=7,h=2, with P=0,D=1. A genuine multi-cell positive return also occurs at N=15,h=3, with G=-9,K=-10,P=9,D=8. The first complete-negative and multi-cell-positive diagnostics were a disclosed scope refinement after the registered all-prefix sign test failed; no test range was enlarged. These disprove universal nonnegativity only, not an eventual sign or the O(Nh) bound.

**Endpoint-label counterexample.** At X=128,h=3,j=39, the actual interval is (148,163], containing 149,151,157,163. Using Q(p) in place of Q(p-1) omits the right-boundary prime 163. This demonstrates why a superficially similar clock labeling is not source-exact.

**Full Gram checks.** The following are exact integer quantities, not numerical covariance estimates:

| X | h | windows | last halo endpoint | V_clock | prime diagonal | ordered prime off-diagonal | prime/model cross | model square |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 128 | 3 | 25 | 271 | 18 | 73 | 158 | -438 | 225 |
| 256 | 4 | 43 | 533 | 26 | 166 | 500 | -1328 | 688 |
| 512 | 4 | 77 | 1045 | 69 | 301 | 944 | -2408 | 1232 |
| 1024 | 5 | 140 | 2078 | 305 | 683 | 2952 | -6830 | 3500 |
| 2048 | 6 | 256 | 4139 | 533 | 1531 | 8158 | -18372 | 9216 |

Executed checks: **20,460** coarse whole-prefix identities, **20,460** complete quadratic reconstructions, **20,460** finite error-bound checks, **541** literal prime-admission comparisons, five full Gram and five boundary-telescope/Cauchy checks, plus four nonzero-anchor controls. For example a=194 has G(a)=-675 and B(a)=-5; neither can be omitted from its return.

All floors were certified by integer-only outward-rounded intervals, using the prior report's log/Ei method with explicit tails. Prime flags agree with independent trial factorization throughout 2..4224. The minimum noninitial floor margin exceeds 10^(-5); maximum interval width is below 10^(-48). The script exited zero and syntax checks passed. This is regression evidence for identities and the finite falsifier, not a proof of MC2's asymptotic bound or evidence of an optimized exponent.

MC2 was self-audited for the fixed-length versus multiplicative-length distinction, all-halo coverage, separation of samples, both prime endpoints, the h/log X moving-endpoint price, absolute constants, and absorption of X log X. No arbitrary random signs, assumed source admission, deleted adverse pairs or small-variance hypothesis enter its proof. Independent review, including inspection of the imported 1998 fixed-length statement from an accessible full copy, remains requested rather than claimed complete.

The scoped source and two-day report search found no earlier proof of this exact arrival-sampling bound. It did find the older abstract telescopes and LC4, which are explicitly reused. There was no exhaustive literature-novelty search. The known LC3 witnesses W(512)=1 and W(2048)=3 remain preserved and were not the object of another sign scan.

### G. Conceptual Interpretation

The multi-cell problem has two different components. A short-interval theorem constrains actual prime-count innovations on the Li clock after a genuine sampling bridge. Coarse compression pays positional shape, but now that shape is the DIFFERENCE of prime and model displacements, not a positive placement bill.

Neither operation controls the accumulated signed level by itself. The complete overlap Gram exposes the prime-pair, model and boundary interactions needed for a stronger local energy bound; MC4 shows exactly how much of a power saving would survive restoration to actual prime error. This is a concrete restriction and an honest power-budget diagnosis, not a new name for the solved endpoint.

### H. Competing Mechanisms

**Continue:** the original-clock complete Gram, with its independently paid logarithmic mean-square baseline and a precise fixed-power question. Its first unsupported step is quantitative, not source admission or sampling.

**Continue as an alternative:** a genuinely one-sided weighted level/innovation estimate sufficient for the JOH consumer, which may be weaker than controlling the entire nonnegative V_clock. Keep original anchor and all terminal weights. No such signed supplier has been found here.

**Revise:** multi-cell geometric compression must use P-D and its mixed square, not the one-cell positive E_place. Its O(Nh) bound is useful proper-error control, not proof that the weighted retained level is negative.

**Abandon at stated scope:** universal nonnegative coarse placement, and any argument that silently changes Q(p-1) to Q(p). Do not abandon JOH, global compensation, or the nine-route portfolio on the basis of those small counterexamples.

### I. Specialist Handoffs

**Coordinator:** record MC2 as a source-qualified independent logarithmic improvement, not a new exponent or RH result. It answers part of LC4's requested multi-cell COUNT question. The complete power gap is X^(1/4), up to logs, relative to Xh. Keep the weighted-level mechanism as a genuinely different possible consumer. Correct the ticket's B convention or explicitly transport its missing -1. Next Owner route remains SAT.

**Analytic:** independently audit MC2's fixed-length Zaccagnini input and the exact deterministic sampling bridge. The first possible stronger theorem concerns the FULL MC1 clipped prime-pair/model Gram for h=floor(X^(1/4)); do not replace it by arbitrary sparse samples or presume classical almost-all results give Xh energy. Assess whether an actual coefficient-sensitive result can remove the remaining polynomial h loss, or whether a one-sided weighted consumer is more realistic.

**Wheel:** use lambda(p)=Q(p-1) and the exact finite overlap K(p,q) if deriving factor/residue restrictions on the pair term. Same-cell and different-cell prime pairs both occur. Any owner classification must sum back to the complete MC1 expression, including the negative prime/model term and clipping. There is no independent random-sign or disjoint-history model here.

**Census:** independent reproduction can be small: certify b_2,b_3,b_4 and the complete negative [5,8) return; certify the boundary prime 163; reconstruct the five displayed Gram rows from original primes and certified floors, retaining the 4139 halo. The rival hypotheses are nonnegative coarse placement and interchangeable Q(p)/Q(p-1) admission. No wider range or fitted exponent is requested. The earlier LC4 independent replication remains separately pending, not marked done by this author's checks.

**Referee:** reconstruct MC2 from the precise external theorem and clock definitions before comparing the proof. Challenge minimal-arrival overshoot, disjoint sample intervals, the conversion of an O(h) physical endpoint shift into O(h/log X) prime count, and the full range of external constants. Separately review MC3's truncated terminal block and -2PD cross term, and MC4's every-endpoint dyadic return. Return scoped verdicts; these are SELF_AUDIT claims, not prior independent acceptance.

**Lean Verification:** no immediate proof branch is requested for the unreviewed analytic estimate. After independent acceptance and utility review, MC1 admission/overlap and MC3 finite return can be implemented from existing floor-Li definitions. The logarithmic theorem additionally needs honest external analytic imports and its entire sampling proof; a conditional wrapper is not its proof. Do not displace a more consequential already-qualified task merely to formalize another identity.

These are published asynchronous handoffs only. No specialist was launched and no review or future run is represented as complete.

### J. First Independently Missing Lemma

The explicit sufficient local input for a NEW power is

```text
OPEN-JOH-CLOCK-POWER:
exists fixed kappa in (0,1/4), forall epsilon>0,
exists C_epsilon,X_epsilon, forall real X>=X_epsilon,
 sum_(X<=b_j<2X)
  [pi(b_(j+floor(X^(1/4))))-pi(b_j)-floor(X^(1/4))]^2
 <= C_epsilon X^(5/4-kappa+epsilon).
```

This is stronger than the earlier exploratory Xh polylogarithmic supplier and is a proper moving-window energy statement, not an asserted target equivalence. MC2 does NOT prove it. MC4 proves its native prime-error implication; it is therefore not an elementary lemma to be assumed. A direct one-sided weighted estimate might bypass this stronger energy question, but it too needs independent arithmetic and complete return. No smaller accepted supplier closing the JOH sign was identified.

The next actual protected Owner task is the existing SAT **OPEN-SAT-I** from today's owner-1/RC1-RC6: seek a joint genuine cofactor/prime-error restriction, preserving E_R=-A_R-I_R and M(Y)=L_R+E_R+C_R. Its separate R^(85/48) endpoint certificate remains above the inherited 7/4 root power; RC5's centered packet has its stated prime-error-equivalent burden. Do not repeat the refuted bounded-core/triangle payment or transfer today's JOH bound without the true SAT weights.

### K. Next-Run Resume Capsule

```text
RUN: 20261105-owner-3; scheduled 16:15:00 EST; RUN_ID_UNAVAILABLE.
MAIN: 1667c3cf9b4e898bb9afd62ec48e24610b2156ab.
POLICY: NO_PIGEONHOLING_ROUTE_SELECTOR_V1;
  ffd8f1c65cc4da656174956d4e03b48bea46768b.
REPORT INTAKE HEAD: 1101a07e2884fbb54442b097d7837b92e4bd3800.
EARLY CHECKPOINT: 6c22b7389a97292895040e212de21eb6f44a4d35;
  blob 1469549cb2a41add3454ad1894a545ed689325c7; exact readback PASS.
ROUTE: JOH; original centered B=pi-floor(Li_2)-1 and G.
CLAIMS: MC1 exact occurrence/Gram; MC2 true clock log saving;
  MC3 full coarse P-D return and O(Nh); MC4 conditional power bridge;
  MC5 exact finite falsifiers and regression checks.
PAID: sampling, moving-endpoint correction, coarse positional error.
UNPAID: Xh-scale fixed power saving or a sufficient weighted signed level law.
FALSIFIERS: a=5,h=2,N=8 gives P-D=-1; Q(p) drops boundary prime 163.
ALL CROSS TERMS: MC1 full overlap Gram; MC3 K/P/D complete square.
REVIEW: SELF_AUDIT; independent Referee PENDING; NOT_FORMALIZED.
GAIN: none at complete endpoint; canonical VF and RH OPEN; SEARCH_BROAD.
ROTATION: today's SAT owner-1, VF-LOW owner-2, JOH owner-3.
NEXT: SAT joint OPEN-SAT-I and full model/anchor/complement.
JOH RESUME: independently review MC2 before considering stronger clock energy;
  do not rerun old midpoint signs, rename the backlog, or delete D.
```

#### Two-Day Continuity

At this invocation's pinned reporting snapshot, **TODAY=AVAILABLE** for every role and **YESTERDAY=CARRY_FORWARD**. These labels do not overwrite the valid earlier runs' TODAY=PENDING snapshots. Both Coordinator mirror entries have identical blobs. All listed report bytes were retrieved; applicable mathematical findings, requested JOH continuations and scope warnings were read, not all executable appendices rerun.

| Role | November 4 blob | November 5 intake blob |
| --- | --- | --- |
| Coordinator | 68495a5e913eee0e788940a683cf16ec4d0984cc | 88c4b9f83cc3dcea885d0c9ddb1fc26cedef4632 |
| Owner | 560b0b7617703b64e728e12e60a390646c9379ea | b4a4f636ece46d696360b5ca9312c2d1d81498c9 |
| Analytic | 04ffb1b41d8b6afe5a5d89754f5ccbc8d9682d58 | 0774002d5244d373b0230429802cd1cfd8a3a8e8 |
| Wheel | 37ad6a1230fbb46369311790ed5686baf1775598 | 000bd6a7e0900373f8fca05a607676f6170f1032 |
| Census | 4bd5319fa3d13219cdad006dce4a854b606c2f7c | 44f070eed4302f3d8d560346c6fb9b66c35be18a |
| Referee | 0e4fdfbf90d52a74074e04ef6cb6988339dc8d84 | df74121b0a07297776a106ccd1b9d80a36b12fc5 |
| Lean | 5fce0138779d67eda4e69c13230274e6419de894 | c9e8255d2c00a2b317f39531589ac2a16f8e3518 |

Consumed distinctions: Coordinator C58-C61 are paper Nyman finite-mixture restrictions with independent review pending, not a JOH supplier; Owner LC1-LC5, RC1-RC6 and CR1-CR5 retain their exact prior claims and counterexamples; Analytic's logarithmic maximal Mobius bounds do not transfer to prime clocks without a bridge; today's SP1-SP5 Nyman obstruction has its separate scoped Referee acceptance; Wheel's prime-mask four-block asymptotics require forced cross compensation; Census's R=57/58 joint restrictions concern auxiliary CORR4 signs; Referee's Euler audit finding and Lean's #1095 repair are verification evidence, not new arithmetic. None is imported as a missing JOH estimate.

External inbox **038018145c0fddb2f6306c0712373adf9cd1ea52** has no post-October-18 entry. EXT-20261018-PNT-1..3 preserve genuine-prime discrepancy and complete return; EXT-20261014-5 remains the original-denominator, unconditional-all-R obstruction, not a refutation of today's method or conditional first-bad strategies.

#### Reproducibility And Publication Discipline

The complete executed verifier and interval library follow in this report. Verifier SHA-256 **549cd2341d04efe31d73f272a27e42e5a7e0ee2dd72366d2ce8fd197e81e2779**. Interval-library SHA-256 **19d1daf3209f9c5fdc507fc1e36a015285c399e156d5d3318fe2f07970f765b8**; it was extracted from yesterday's actual embedded library with the local trailing newline, not assumed from an unavailable cache. Certified floor-data SHA-256 **a01e7332a25bd065e3ef2f2149046d4e729b8c6e0d40861bca2ee3593c4dfe08**. The preregistration SHA-256 is **c7217204768c3271a0fca1fb7b5c3f668e67a9a982970da9c770389693daacae**.

Actual tool limitation: direct shell access to the primary Zaccagnini PDF and several direct browser PDF endpoints returned HTTP 403. Its indexed primary theorem statement, publisher metadata, author's later theorem statement and the Montgomery--Vaughan original paper were available as described above. The fixed-length theorem is cited with this access limitation; no unseen full-text proof is claimed read. GitHub connected reads and own-report writing worked.

The early checkpoint commit was inspected and re-fetched exactly; only this authorized report changed. The synthesis remains PENDING_READBACK until its own immutable commit/readback receipt. Earlier valid report bytes are preserved. No Lean source, central policy, other report, proof branch, PR, issue, workflow, permission, protection, schedule or main was changed. No agent was launched; no local Lean ran; both finite test executions finished successfully.


### Executed Reproducibility Appendix - 20261105-owner-3

The following are the exact executed files, including each code block's final newline. Place the two Python files in one directory and run `python joh_clock_verify.py`; this uses only the Python standard library. These are reproducibility instructions, not a claim that another agent executed them.

#### Preregistered Scope

```text
# JOH Clock Test Registration

Registered before executing the new test, 2026-11-05, same scheduled 16:15 EST invocation.

- Original carrier: Q(n)=floor(Li_2(n)), B(n)=pi(n)-Q(n)-1, G(N)=sum_(2<=n<N) B(n).
- Reuse the published integer-only interval library from November 4; independently sieve and factor the small primality range.
- Development: integers through 2048. Held-out: 2049 through 4096. No larger-range scan or fitted exponent.
- Test exact h-cell counts and all-pair Gram at X=128,256,512,1024,2048, with h=floor(X^(1/4)) and full upper halo.
- Test coarse-block reconstruction at every N through 4096 for h=1,2,3,5,8 and anchor a=5, restoring both prime and model displacements.
- Rival sign claim: G(N)-K_h(N)>=0 for all h,N, as for the h=1 LC4 placement. Stop the sign search at the first genuine negative value, but complete the registered identity checks.
- Test the exact overlapping-window boundary telescope and its Cauchy bound for specified short ranges of arrival indices.
- Test wrong-label negative control Q(p) versus correct Q(p-1) for primes coinciding with model arrivals, and show dropping the initial level or model returns changes the original statistic.
- Keep the finite computations separate from the independently derived asymptotic theorem; no finite result proves its uniform bound.
- Halo clarification before execution: certify integers through 4224 only to retain all h-cell endpoints for the prescribed X=2048 starts below 4096. The development/held-out core and coarse-prefix test range remain unchanged.
```

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

#### joh_clock_verify.py

```python
"""Exact genuine-prime checks for the registered JOH multi-cell claims."""

from bisect import bisect_left, bisect_right
from collections import Counter
from fractions import Fraction as F
from math import isqrt
import hashlib
import json

from joh_interval_base import SCALE, li_interval, log_rational, sieve, factor


LIMIT = 4224
CORE = 4096
flags = sieve(LIMIT)
floors = [0] * (LIMIT + 1)
pi = [0] * (LIMIT + 1)
prime_sum = [0] * (LIMIT + 1)
g = [0] * (LIMIT + 2)
b = {}
arrival_sum = [0] * (LIMIT + 1)
backlog = [0] * (LIMIT + 1)
min_margin = SCALE
max_width = 0

for n in range(2, LIMIT + 1):
    lo, hi = li_interval(n)
    assert lo // SCALE == hi // SCALE, (n, lo, hi)
    floors[n] = lo // SCALE
    if n > 2:
        min_margin = min(min_margin, lo % SCALE, SCALE - hi % SCALE)
    max_width = max(max_width, hi - lo)
    pi[n] = pi[n - 1] + flags[n]
    prime_sum[n] = prime_sum[n - 1] + n * flags[n]
    backlog[n] = pi[n] - floors[n] - 1
    g[n + 1] = g[n] + backlog[n]
    assert bool(flags[n]) == (factor(n) == [n])
    arrival_sum[n] = arrival_sum[n - 1]
    if n >= 5:
        step = floors[n] - floors[n - 1]
        assert step in (0, 1)
        if step:
            b[floors[n]] = n
            arrival_sum[n] += n

assert b[2] == 5
counts = Counter()
negative = None
positive = None
complete_negative = None
multi_positive = None
samples = []


def coarse(a_index, h, n):
    a = b[a_index]
    k = g[a]
    p_return = d_return = 0
    index = a_index
    while b[index] < n:
        c = b[index]
        t = min(b.get(index + h, LIMIT + 1), n)
        k += (t - c) * backlog[c]
        p_return += t * (pi[t - 1] - pi[c]) - (prime_sum[t - 1] - prime_sum[c])
        d_return += t * (floors[t - 1] - floors[c]) - (arrival_sum[t - 1] - arrival_sum[c])
        if t == n:
            break
        index += h
    return k, p_return, d_return


for n in range(5, CORE + 1):
    for h in (1, 2, 3, 5, 8):
        k, p, d = coarse(2, h, n)
        r = p - d
        assert g[n] == k + r
        assert g[n] ** 2 == k*k + p*p + d*d + 2*k*p - 2*k*d - 2*p*d
        assert r*r == p*p + d*d - 2*p*d
        counts['coarse_return'] += 1
        counts['complete_quadratic_return'] += 1
        if h == 1:
            assert d == 0 and r >= 0
        if r < 0 and negative is None:
            negative = {'N': n, 'h': h, 'G': g[n], 'K': k, 'P': p, 'D': d, 'R': r}
        if r > 0 and positive is None:
            positive = {'N': n, 'h': h, 'G': g[n], 'K': k, 'P': p, 'D': d, 'R': r}
        if r > 0 and h > 1 and multi_positive is None:
            multi_positive = {'N': n, 'h': h, 'G': g[n], 'K': k, 'P': p, 'D': d, 'R': r}
        if r < 0 and n in b.values() and (floors[n] - 2) % h == 0 and complete_negative is None:
            complete_negative = {'N': n, 'h': h, 'G': g[n], 'K': k, 'P': p, 'D': d, 'R': r}
        # An outward lower bound for log(n) makes this a stronger finite check.
        loglo = log_rational(n)[0]
        assert max(p, d) * SCALE <= h * loglo * max(pi[n], floors[n])
        counts['coarse_error_bound'] += 1
        if n in (512, 1024, 2048, 4096) and h in (1, 3, 8):
            samples.append({'N': n, 'h': h, 'G': g[n], 'K': k, 'P': p, 'D': d, 'R': r})

clock_rows = []
label_control = None
for x in (128, 256, 512, 1024, 2048):
    h = isqrt(isqrt(x))
    js = [j for j in b if x <= b[j] < 2*x]
    lo, hi = min(js), max(js)
    assert js == list(range(lo, hi + 1)) and hi + h in b
    deltas = [pi[b[j+h]] - pi[b[j]] - h for j in js]
    for j, delta in zip(js, deltas):
        assert delta == backlog[b[j+h]] - backlog[b[j]]
        literal = [p for p in range(b[j]+1, b[j+h]+1) if flags[p]]
        classified = [p for p in range(b[lo]+1, b[hi+h]+1)
                      if flags[p] and j <= floors[p-1] < j+h]
        assert literal == classified
        wrong = [p for p in range(b[lo]+1, b[hi+h]+1)
                 if flags[p] and j <= floors[p] < j+h]
        if literal != wrong and label_control is None:
            label_control = {'X': x, 'h': h, 'j': j, 'start': b[j], 'end': b[j+h],
                             'literal': literal, 'wrong_Qp': wrong}
        counts['literal_prime_admission'] += 1
    primes = [p for p in range(b[lo]+1, b[hi+h]+1) if flags[p]]

    def overlap(p, q):
        lp, lq = floors[p-1], floors[q-1]
        return max(0, min(hi, lp, lq) - max(lo, lp-h+1, lq-h+1) + 1)

    diagonal = sum(overlap(p, p) for p in primes)
    off = 2 * sum(overlap(p, q) for i, p in enumerate(primes) for q in primes[i+1:])
    mixed = -2*h*diagonal
    model = len(js)*h*h
    variance = sum(d*d for d in deltas)
    assert variance == diagonal + off + mixed + model
    counts['complete_prime_pair_gram'] += 1
    total = sum(deltas)
    boundary = sum(backlog[b[j]] for j in range(hi+1, hi+h+1))
    boundary -= sum(backlog[b[j]] for j in range(lo, lo+h))
    assert total == boundary and total*total <= len(js)*variance
    counts['overlap_telescope_and_cauchy'] += 1
    clock_rows.append({'X': x, 'h': h, 'windows': len(js), 'first_arrival': b[lo],
                       'halo_endpoint': b[hi+h], 'V': variance, 'sum_delta': total,
                       'prime_diagonal': diagonal, 'ordered_prime_off': off,
                       'prime_model_cross': mixed, 'model_square': model,
                       'max_abs_delta': max(map(abs, deltas))})

anchor_controls = []
for ai in (48, 150):
    a = b[ai]
    for h in (2, 5):
        n = a + 37
        k, p, d = coarse(ai, h, n)
        assert g[n] == k+p-d
        assert g[a] != 0 and backlog[a] != 0
        anchor_controls.append({'a': a, 'N': n, 'h': h, 'G_anchor': g[a],
                                'initial_B': backlog[a], 'G': g[n], 'K': k, 'P': p, 'D': d})
        counts['nonzero_anchor_checks'] += 1

assert negative is not None and positive is not None and label_control is not None
result = {'checks': dict(counts), 'certified_core': [2, CORE], 'certified_halo': [CORE+1, LIMIT],
          'floor_margin_gt_1e_minus_5': min_margin * 100000 > SCALE,
          'max_interval_width_lt_1e_minus_48': max_width * 10**48 < SCALE,
          'first_negative_coarse_return': negative, 'first_positive_coarse_return': positive,
          'first_complete_negative_coarse_return': complete_negative,
          'first_multi_cell_positive_return': multi_positive,
          'wrong_prime_clock_label_control': label_control, 'variance_decompositions': clock_rows,
          'coarse_samples': samples, 'nonzero_anchor_controls': anchor_controls,
          'scope': 'Exact finite identities and falsifier only; no asymptotic rate inferred.'}
print(json.dumps(result, indent=2, sort_keys=True))
print('FLOOR_DATA_SHA256', hashlib.sha256(json.dumps(floors[2:]).encode()).hexdigest())
```

#### Final Successful Run Output

```text
{
  "certified_core": [
    2,
    4096
  ],
  "certified_halo": [
    4097,
    4224
  ],
  "checks": {
    "coarse_error_bound": 20460,
    "coarse_return": 20460,
    "complete_prime_pair_gram": 5,
    "complete_quadratic_return": 20460,
    "literal_prime_admission": 541,
    "nonzero_anchor_checks": 4,
    "overlap_telescope_and_cauchy": 5
  },
  "coarse_samples": [
    {
      "D": 0,
      "G": -2595,
      "K": -2808,
      "N": 512,
      "P": 213,
      "R": 213,
      "h": 1
    },
    {
      "D": 504,
      "G": -2595,
      "K": -2776,
      "N": 512,
      "P": 685,
      "R": 181,
      "h": 3
    },
    {
      "D": 1745,
      "G": -2595,
      "K": -2639,
      "N": 512,
      "P": 1789,
      "R": 44,
      "h": 8
    },
    {
      "D": 0,
      "G": -6703,
      "K": -7134,
      "N": 1024,
      "P": 431,
      "R": 431,
      "h": 1
    },
    {
      "D": 1021,
      "G": -6703,
      "K": -7062,
      "N": 1024,
      "P": 1380,
      "R": 359,
      "h": 3
    },
    {
      "D": 3540,
      "G": -6703,
      "K": -6957,
      "N": 1024,
      "P": 3794,
      "R": 254,
      "h": 8
    },
    {
      "D": 0,
      "G": -16599,
      "K": -17485,
      "N": 2048,
      "P": 886,
      "R": 886,
      "h": 1
    },
    {
      "D": 2059,
      "G": -16599,
      "K": -17498,
      "N": 2048,
      "P": 2958,
      "R": 899,
      "h": 3
    },
    {
      "D": 7121,
      "G": -16599,
      "K": -17065,
      "N": 2048,
      "P": 7587,
      "R": 466,
      "h": 8
    },
    {
      "D": 0,
      "G": -42284,
      "K": -44049,
      "N": 4096,
      "P": 1765,
      "R": 1765,
      "h": 1
    },
    {
      "D": 4104,
      "G": -42284,
      "K": -44071,
      "N": 4096,
      "P": 5891,
      "R": 1787,
      "h": 3
    },
    {
      "D": 14275,
      "G": -42284,
      "K": -43697,
      "N": 4096,
      "P": 15688,
      "R": 1413,
      "h": 8
    }
  ],
  "first_complete_negative_coarse_return": {
    "D": 2,
    "G": -1,
    "K": 0,
    "N": 8,
    "P": 1,
    "R": -1,
    "h": 2
  },
  "first_multi_cell_positive_return": {
    "D": 8,
    "G": -9,
    "K": -10,
    "N": 15,
    "P": 9,
    "R": 1,
    "h": 3
  },
  "first_negative_coarse_return": {
    "D": 1,
    "G": -1,
    "K": 0,
    "N": 7,
    "P": 0,
    "R": -1,
    "h": 2
  },
  "first_positive_coarse_return": {
    "D": 0,
    "G": -1,
    "K": -2,
    "N": 8,
    "P": 1,
    "R": 1,
    "h": 1
  },
  "floor_margin_gt_1e_minus_5": true,
  "max_interval_width_lt_1e_minus_48": true,
  "nonzero_anchor_controls": [
    {
      "D": 17,
      "G": -867,
      "G_anchor": -675,
      "K": -875,
      "N": 231,
      "P": 25,
      "a": 194,
      "h": 2,
      "initial_B": -5
    },
    {
      "D": 57,
      "G": -867,
      "G_anchor": -675,
      "K": -880,
      "N": 231,
      "P": 70,
      "a": 194,
      "h": 5,
      "initial_B": -5
    },
    {
      "D": 17,
      "G": -5245,
      "G_anchor": -4938,
      "K": -5271,
      "N": 857,
      "P": 43,
      "a": 820,
      "h": 2,
      "initial_B": -10
    },
    {
      "D": 67,
      "G": -5245,
      "G_anchor": -4938,
      "K": -5304,
      "N": 857,
      "P": 126,
      "a": 820,
      "h": 5,
      "initial_B": -10
    }
  ],
  "scope": "Exact finite identities and falsifier only; no asymptotic rate inferred.",
  "variance_decompositions": [
    {
      "V": 18,
      "X": 128,
      "first_arrival": 129,
      "h": 3,
      "halo_endpoint": 271,
      "max_abs_delta": 2,
      "model_square": 225,
      "ordered_prime_off": 158,
      "prime_diagonal": 73,
      "prime_model_cross": -438,
      "sum_delta": -2,
      "windows": 25
    },
    {
      "V": 26,
      "X": 256,
      "first_arrival": 259,
      "h": 4,
      "halo_endpoint": 533,
      "max_abs_delta": 2,
      "model_square": 688,
      "ordered_prime_off": 500,
      "prime_diagonal": 166,
      "prime_model_cross": -1328,
      "sum_delta": -6,
      "windows": 43
    },
    {
      "V": 69,
      "X": 512,
      "first_arrival": 515,
      "h": 4,
      "halo_endpoint": 1045,
      "max_abs_delta": 2,
      "model_square": 1232,
      "ordered_prime_off": 944,
      "prime_diagonal": 301,
      "prime_model_cross": -2408,
      "sum_delta": -7,
      "windows": 77
    },
    {
      "V": 305,
      "X": 1024,
      "first_arrival": 1024,
      "h": 5,
      "halo_endpoint": 2078,
      "max_abs_delta": 4,
      "model_square": 3500,
      "ordered_prime_off": 2952,
      "prime_diagonal": 683,
      "prime_model_cross": -6830,
      "sum_delta": -17,
      "windows": 140
    },
    {
      "V": 533,
      "X": 2048,
      "first_arrival": 2048,
      "h": 6,
      "halo_endpoint": 4139,
      "max_abs_delta": 4,
      "model_square": 9216,
      "ordered_prime_off": 8158,
      "prime_diagonal": 1531,
      "prime_model_cross": -18372,
      "sum_delta": -5,
      "windows": 256
    }
  ],
  "wrong_prime_clock_label_control": {
    "X": 128,
    "end": 163,
    "h": 3,
    "j": 39,
    "literal": [
      149,
      151,
      157,
      163
    ],
    "start": 148,
    "wrong_Qp": [
      149,
      151,
      157
    ]
  }
}
FLOOR_DATA_SHA256 a01e7332a25bd065e3ef2f2149046d4e729b8c6e0d40861bca2ee3593c4dfe08
```

The final proof-input check also re-retrieved the indexed primary 1998 first-page theorem, confirming its range y^(1/6-epsilon(y))<=L0<=y and the admissible specialization epsilon(y)=0. This did not remove the disclosed full-PDF access limitation. Publication-time main refresh remained 1667c3cf9b4e898bb9afd62ec48e24610b2156ab, and the open/draft PR list remained empty.

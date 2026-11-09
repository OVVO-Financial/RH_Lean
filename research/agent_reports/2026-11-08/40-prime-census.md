# RH | Prime Census Laboratory - 2026-11-08

## Early Research Checkpoint - 20261108-census-1

Execution: PARTIAL / IN_PROGRESS. Scheduled trigger: 2026-11-08 03:11:01 EST.
RUN_ID_UNAVAILABLE. Checkpoint: 2026-11-08 08:16:32 UTC.

### Authority And Continuity

Main: bf4af1cd18aff7c3944a75991aa66371c8afc18a; AGENTS blob 0a99faf8458809ac772d470d704c5433f373bda8;
CURRENT_PROOF_CONTRACT blob d1d6fd558ee23927bd9f70ffdc375bafd1dbb67a.
Reporting intake: 99d676a9835c6400c1bab47b931f34e7301726f5.
high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1;
chain_ack=CANCELLATION_CHAIN_REUSE_V1;
baseline_ack=PAID_BASELINE_EXACT_CONSUMER_V1;
deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1.

The canonical actual-prime VF/von-Koch objective remains open.
The authorized shared objective is an improvement of complete signed HIGH
or an explicitly justified consumer over the strongest applicable baseline.
For a fixed source, merged #1107 supplies b_base=7/8-m/4 with m>0,
with every positive loss; the fixed-power theorem spends half the saving.
Source VF919TotalMassEndpoint.lean blob 827bb952c4d4311d75fd03a2470799dc10b0f7e7.
Run 42437401175 at cd8f98fd6ed2dee3fa08f526eb8ac86c94549da5 is completed/success;
job 128599096276 was read and its terminal standard-axiom checks passed.
This is inherited evidence, not a new compilation. Open #1108 remains unmerged.

November 8 Owner PD, Analytic MP and Wheel SP reports are AVAILABLE.
Coordinator, prior own report, Referee and Lean TODAY=PENDING.
Their November 7 reports were retrieved; relevant results and resume sections
are YESTERDAY=CARRY_FORWARD. The external inbox has no post-October-18 entry.
Prior SC/RC, DI/LR/OC and TF/WS retain their scoped evidence grades.

### Selected Changed Inference

Route CORR4, following today's 20261108-wheel-1/SP2-SP4 handoff.
This is a new original-arithmetic transition test, not a repeat of RC's
scalar rectangle or SP's unchanged cube-range census. Coordinator's
WS-WINDOW-FALSIFIER remains a separate deferred support task.

Original events are (R,q), R>=56, q odd prime, q^2<R,
Y=(R^2-1)//q^2, with genuine d=M(Y).
In a root window [H,H+h), 1<=h<=H, retain q<=Q.
SP proves off-ray injectivity when Q^3<=2H.

Before computation the competing hypotheses are:
1. Off-ray injectivity remains true at Q^3<=4H.
2. Only determinant-one double collisions occur at that wider cutoff,
   necessarily between coprime roots of opposite parity; parity-restricted
   sampling remains injective.
3. Repeated endpoints can be dropped without affecting the signed return.

The discriminator is the exact event multiset, integer determinant R*r-S*q,
root gcd/parity, and the complete original mixed-tail bill. Inverse cutoff
intervals n*q^2<R^2<=(n+1)*q^2 independently reconstruct the population.
The proposed collision penalty is a hypothesis to derive and test, not a
declared result.

### Frozen Domain And Stop Rule

Discovery root windows: H in {56,64,86,128,256,333,550,1024};
held-out H in {2048,4096,8192}. Use h=H and boundary/subwindows h=1,
h=min(7,H), and h=floor(H/2). Q is floor(cuberoot(2H)),
floor(cuberoot(4H)), and neighboring integers, with hypotheses checked
separately. Exact active-mask tests include q^2 and q^2+1.

Independent methods: Python forward event enumeration and a separately
written C++ inverse-interval implementation. Verify genuine Mobius data
by a factorization method independent of the sieve at all small fixtures.
Use exact rational arithmetic for weights and squares.
Signed complete-return tests will be limited to a declared small-root
domain, with full parent, diagonal, ray, tail and historical terms restored.
No floating-point sign decisions or probable-prime tests.

Stop scaling after a legal smallest tested counterexample and a verified
structural explanation; finite survival will not be called an all-scale
bound. Any post-discovery hypothesis or range change will be disclosed.

### Complete Return And Remaining Obligation

G_R=M(R^2-1)-M(R-1), U_R=sum d/q, E_R=sum d^2,
Hdiag_R=sum_(R<=n<=R^2-1) mu(n)^2
        +2*sum_q (1/q)*sum_(R<=n<=Y) mu(n)^2.
B_R=G_R^2+2*G_R*U_R-2*E_R-Hdiag_R.
The actual consumer is Corr4PowerMixedTailBill and
mertensPowerBound_of_corr4MixedTailBill. No estimate for B_R is assumed.
A geometric sampling theorem alone cannot improve the global exponent.

Only this own dated report is authorized for remote writing.
No source/Lean/PR/branch/workflow/schedule changes or agent launches.
Final verified findings, executable code, and a resume capsule will be appended.

## Transition-Collision Synthesis - 20261108-census-1

Research state: COMPLETED / DONE. Final source refresh: 2026-11-08 08:38:45 UTC
(03:38:45 EST). This synthesis supersedes the early IN_PROGRESS status while
preserving that checkpoint verbatim. Publication verification follows below.

### A. Most Important Mathematical Discovery

**The first loss of daughter-endpoint injectivity is not arbitrary reuse: it is a parity-separated, determinant-one collision of two coprime roots. Its reciprocal sampling error is bounded by 2/Q, and its complete signed return retains a parent-disagreement penalty.**

The tempting extension of Wheel SP2's injectivity from Q^3<=2H to Q^3<=4H is FALSE. The smallest counterexample by largest root is

```text
(R,q)=(556,11), (S,r)=(657,13), Y=2554,
M(2554)=-5, 556*13-657*11=1.
```

Both events satisfy the ORIGINAL odd-prime and q^2<R admission conditions. Choose H=556, Q=13, h=102: 13^3=2197<=2224=4H, and both roots lie in [556,658). Neither label divides its root. Exhaustive exact search through largest root 657, followed by an independent Bezout parametrization, establishes minimality in this declared ordering.

The minimality search is exhaustive under the doubled-cube hypotheses: every
candidate has max(q,r)^3<=4*min(R,S), so max(R,S)<=657 restricts the prime
labels to at most 13. TC1 also forces max(R,S)<2*min(R,S), since the label
ratio is below 8/5 and the determinant is one. Thus the search's dyadic
filter does not discard any qualifying collision, even for a noninterval
finite set of roots.

What survives at Q^3<=4H is stronger than a generic multiplicity-two estimate: every colliding label exceeds 5Q/8, every off-ray column has at most two occurrences, and the off-diagonal reciprocal row Gram has norm at most 2/Q. This is a genuine geometric estimate on the literal sampling operator, not a signed cancellation theorem. The complete weighted bill can then be grouped with an explicit nonnegative disagreement penalty, without using a negative square twice.

New proofs below are PAPER_PROOF / SELF_AUDIT, with independent computational reconstructions but no independent Referee acceptance and no new Lean certification. NEW_VERIFIED_ENDPOINT_GAIN=NONE; net_endpoint_gain=UNKNOWN; eta_gate=SEARCH_BROAD. No literature-priority claim is made for determinant spacing, matrix norm estimates, or completing squares.

### B. Current Authority And Exact Objective

This completes the ONE scheduled invocation begun 2026-11-08 03:11:01 EST, not a new run. RUN_ID_UNAVAILABLE. Main at intake is bf4af1cd18aff7c3944a75991aa66371c8afc18a. The source/policy/report blob ledger is appended below.

The canonical declaration inspected is VFCanonicalSquareVonKochStatement in research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean:

```text
exists C>=0, forall integer R>=2,
  |vfCanonicalSquareDefect R| <= C*R*log R.
```

The actual-prime estimate remains open; its RH consumer retains the explicit ClassicalVonKochRHCriterion. The current HIGH directive preserves, for each fixed Lambda>=0,

```text
M(R^2-1)=canonicalLowPrefix_Lambda(R-1)+canonicalHighPrefix_Lambda(R-1),
|canonicalLowPrefix_Lambda(R-1)| <= (floor Lambda+1)*R.
```

These canonical definitions use absolute birth height and both orientations. CORR4 daughter sampling is a different coordinate, not a replacement definition of HIGH.

Strongest consumed same-source main baseline: native_mertens_true_physical_slot_minimum_total_mass, with one fixed source D, m=actualSlotMinimum(D)>0, and every-positive-loss boundary b_base=7/8-m/4. The accompanying fixed-power declaration spends half the gain and gives 7/8-m/8. No numerical m or equality with the true optimal exponent is asserted.

The actual #1107 proof run 42437401175 is completed/success at cd8f98fd6ed2dee3fa08f526eb8ac86c94549da5. Job 128599096276 was fetched: its four terminal audits list only propext, Classical.choice, Quot.sound, including closure size 35731 for the native growth theorem. The comparison from that tested head to current main contains only the separately merged prime-admission files, native root export, workflow/audit files and notes; the consumed OAI endpoint module is unchanged. This reuses exact-head evidence, not a new whole-main rebuild. Human merge occurred at 2026-11-08T03:26:45Z. Open #1108 at a0c986c0343a56e98b7344268fdc0b74aa885cdb was inspected but is not treated as merged authority or a supplier for the new claims.

Compact HIGH task record:

```text
high_attack_ack: COMPLETE_SIGNED_HIGH_ATTACK_V1
chain_ack: CANCELLATION_CHAIN_REUSE_V1
baseline_ack: PAID_BASELINE_EXACT_CONSUMER_V1
deployment_ack: NO_PIGEONHOLING_ROUTE_SELECTOR_V1
route: CORR4 / literal moving daughter prefixes
input: #1097 strict sampling; Wheel SP2 determinant restriction;
       native all-prefix Mertens boundary b_base
consumer: Corr4PowerMixedTailBill -> mertensPowerBound_of_corr4MixedTailBill
change: first-transition collision geometry, reciprocal Gram error,
        once-only weighted daughter-square completion
return: parent square, historical prefix, every ray/tail and physical diagonal
first unpaid step: an actual complete signed bill improvement
new endpoint / compilation / independent review: NONE / NONE / PENDING
```

### C. Competing Hypotheses And Preregistration

The early checkpoint was published and read back before any experiment. The discovery windows, held-out windows, exact masks, independent methods, and stop rule are preserved above and in the executed registration appendix.

| Hypothesis | Discriminator | Outcome |
| --- | --- | --- |
| H1: off-ray injectivity survives Q^3<=4H | Any two eligible nondivisible events with equal Y | REFUTED by 556/657 |
| H2: the doubled range has only determinant-one double collisions, separated by parity | Determinant, gcd, parity, column degree | PAPER_PROOF below; all registered tests passed |
| H3: repetitions can be deleted without changing the signed source | Genuine nonzero M(Y), occurrence-weighted sums and negative squares | REFUTED; M(2554)=-5 and a deletion changes the full bill |

The high-label restriction and reciprocal row-degree bound were proposed before execution. The short-window corollary and exact Gram/cell audits were added after discovery, explicitly recorded as follow-up work. No numerical threshold was fitted to the results. The neighboring-cap controls contained no determinant-two example; a separate algebraically engineered outside-domain control was added and identified as such.

The independent geometric input is reduced-fraction spacing with odd prime denominators. It does not assert independence, random signs, favorable covariance, or disjointness of the underlying integer prefixes.

### D. Original Carrier And Complete Statistic

For every integer R>=56 retain

```text
X_R=R^2-1, S_R={q odd prime: q^2<R},
Y(R,q)=floor(X_R/q^2), d_(R,q)=M(Y(R,q)),
G_R=M(X_R)-M(R-1), U_R=sum_(q in S_R) d_(R,q)/q,
E_R=sum_(q in S_R) d_(R,q)^2,
V0_R=sum_(R<=n<=X_R) mu(n)^2,
Vq_R=sum_(R<=n<=Y(R,q)) mu(n)^2,
Hdiag_R=V0_R+2*sum_(q in S_R) Vq_R/q,
B_R=G_R^2+2*G_R*U_R-2*E_R-Hdiag_R.
```

The inspected definitions are rawQ2ChildCutoff, canonicalRoughLowQ2Owners, canonicalRoughLowQ2DaughterEnergy, lowOwnerReciprocalDaughterWeight, and lowOwnerFirstOwnerPrefixTailMixedCell. Their full signed first-owner reassembly is

```text
B_R=2*lowOwnerPrefixTailMixedRawCellMass(R)
      -2*canonicalRoughLowQ2DaughterEnergy(R).
```

The reciprocal-prefix quarter-energy has already been paid and is not spent again. The physical carrier includes squareful zeros, genuine mu(1), all historical prefix sites and all unordered nonzero distinct-site pairs. No #915 compressed NNS denominator or mean-centered covariance is substituted.

For H>=56, integer Q>=3, and any finite set I of roots R>=H define Omega={(R,q):R in I,q in S_R,q<=Q}. Its off-ray part Omega_o has q not dividing R; the ray part has q dividing R. A physical event is (R,q), not its value Y. Repeated Y does not merge physical occurrences. Interval corollaries use I=[H,H+h), 1<=h<=H.

### E. Executed Results And Independent Checks

| Check | Exact coverage/result |
| --- | --- |
| Forward/inverse event populations | 800,309 events; byte-for-byte identical streams |
| Registered parameter/window cases | 172; H=56,64,86,128,256,333,550,1024,2048,4096,8192 |
| Q^3<=4H / Q^3<=2H cases | 128 / 44 |
| Off-ray collision evaluations in doubled range | 287; 79 distinct event-pair/cutoff witnesses |
| Held-out roots | H=2048,4096,8192, with original frozen caps and windows |
| Inverse interval candidates inspected in C++ | 296,649,869 |
| Exact Gram vector checks | 256, explicitly synthetic geometric vectors |
| Original cube-range ray Gram pairs | 7,864, checked from inverse events |
| New short-window injectivity checks | 65 |
| Complete signed scalar rows | All 1,045 roots R=56..1100, two independent mu algorithms |
| Mobius limit | 1,209,999 |
| Trial-factor mu checks | Every n=1..10000; witness M(2554) also independently summed |
| Complete weighted column-return identities | 172, unit and nonconstant rational weights |
| Genuine weighted TC2 operator inequalities | 172, same small-root windows and two weight profiles |
| Strict active-mask fixtures | Ten odd primes q=3..31, checking roots q^2 and q^2+1 |
| Literal physical-pair reconstruction at R=56 | 1,910 sites, 1,823,095 unordered pairs |
| Separate least-owner/lower-signature reconstruction | 1,909 nonempty mixed cells; same pair count and bill |

All assertions passed. The R=56 bill is exactly -68464/35 in the scalar, literal-pair and first-owner-cell methods. The complete scalar stream uses integer numerators over the product of the admitted odd primes; Python rational results and independently computed C++ numerators agree exactly.

The forward program uses Eratosthenes primality and direct (R,q) enumeration. The inverse program uses trial-division primality and integer intervals

```text
isqrt(n*q^2)+1 <= R <= isqrt((n+1)*q^2),
```

clipped to the original window and R>q^2. Its square-root seed is floating point but corrected in both directions with exact integer comparisons; no acceptance or sign decision depends on rounding. All products in this declared domain fit int64. Signed C++ arithmetic uses 128-bit intermediate numerators.

Python mu comes from a linear prime-factor sieve. C++ instead inverts the divisor sum: mu(1)=1 and mu(n)=-sum_(proper d|n)mu(d). Trial factorization and direct first-owner cells are a third small-domain check. These are different algorithms, not copies of the same intermediate table. They are computational independence within this author's run, not an independent Referee review.

### F. Exact Counterexamples And Boundary Cases

For the minimal doubled-range witness, integer inequalities alone verify the shared cutoff:

```text
2554*121=309034 < 556^2=309136 <= 2555*121=309155,
2554*169=431626 < 657^2=431649 <= 2555*169=431795.
```

Genuine signed data:

| Quantity | Exact value |
| --- | --- |
| M(2554) | -5 |
| M(556^2-1), M(555), G_556 | 165, 5, 160 |
| M(657^2-1), M(656), G_657 | 45, -8, 53 |
| Parent half-targets G_R/(2q), G_S/(2r) | 80/11, 53/26 |
| Full B_556 | -42754054126/230945 |
| Full B_657 | -14830731658/51051 |
| Unit-weight disagreement penalty | 2241009/81796 |
| Cross term in the square of the two weighted daughter occurrences | 50/143 |

The last positive value is specifically 2*M(2554)^2/(11*13), not the complete source covariance. It refutes dropping repeated-value cross terms when that local sum is squared. Deleting the (657,13) occurrence from U and E, while retaining the other source terms, increases the full B_657 by exactly 1180/13. Such deletion is not a legal source reindexing.

The first-owner algorithm separately verifies the full source; defining a complement as a difference is used only as a subsequent conservation test, not as independent proof of that original source formula.

Outside the doubled-cube hypothesis, (81,7) and (127,11) share Y=133 with determinant 2, both roots odd, and M(133)=-2. Both are legal original events in a dyadic root window, but 11^3>4*81. This refutes an unrestricted parity extension, not TC1. No optimality of the doubled-cube constant is claimed.

Exact equality cutoffs are present: Q^3=4H at (H,Q)=(128,8),(1024,16),(8192,32), and Q^3=2H at (256,8),(2048,16). The cases include h=1 and short windows. All active masks remain strict, and q^2 is excluded while q^2+1 is admitted.

The ten separate admission fixtures also check Y(q^2+1,q)=q^2+2. Fixtures below root 56 test the original sampling definition only; they are not used as complete-consumer counterexamples.

All tested full B_R were negative on R=56..1100. This finite observation is not an all-scale theorem or an exponent fit. The largest tested B occurs at R=57 and the smallest at R=1099; these facts are not used to select constants or conjecture a universal sign.

### G. Hidden Variables And The Transition Theorem: TC1

**Claim 20261108-census-1/TC1, PAPER_PROOF.** For H>=56, Q>=3, Q^3<=4H and any finite I subset of the integers R>=H, each off-ray cutoff column has at most two events. Distinct events (R,q),(S,r) sharing that column satisfy

```text
|R*r-S*q|=1, gcd(R,S)=1, R and S have opposite parity,
q>5Q/8 and r>5Q/8.
```

Consequently each parity-restricted off-ray population is injective. Ray and off-ray columns never coincide. On I=[H,H+h), injectivity holds without parity restriction whenever Q*(h-1)<2H-1.

**Proof.** The literal cutoff implies n*q^2<R^2<=(n+1)*q^2. Therefore for two equal cutoffs,

```text
|R*r-S*q|*(R*r+S*q) < q^2*r^2.
```

Distinct off-ray events have nonzero determinant: if q=r, zero determinant gives R=S; if q and r are distinct primes, zero determinant forces q|R and r|S. Also

```text
q^2*r^2/(q+r) <= Q^3/2 <= 2H,
R*r+S*q >= H*(q+r).
```

Thus the absolute nonzero integer determinant is strictly below 2, hence is 1. Every common divisor of R,S divides it. Since q,r are odd, its parity is R-S, giving opposite root parity. Three events in one column would include two roots of the same parity, impossible. This also rules out two same-row events.

For the label restriction suppose q<=5Q/8, r<=Q. The function a^2*b^2/(a+b) increases in both positive variables, so

```text
q^2*r^2/(q+r) <= 25*Q^3/104 < Q^3/4 <= H,
```

contradicting the determinant inequality and |det|>=1. The same holds for r. Monotonicity can be checked without calculus by writing the function as ab/(1/a+1/b).

For the ray separation, n+1=s^2 implies R=q*s in the active range. Indeed R<=q*s; if R<=q*s-1, then s>q and R^2<=q^2*s^2-2qs+1<q^2*(s^2-1), a contradiction. The converse is direct division. Hence a ray column cannot be off-ray.

Finally different odd prime labels differ by at least two. The determinant equation gives

```text
q*|S-R| >= 2H-1, hence Q*|S-R| >= 2H-1.
```

This excludes collisions in the stated short window. These arguments use no measured values or unproved prime-distribution assertion. The occurrence graph is bipartite in ROOT parity; it is not asserted to be a matching or forest on roots. Only each cutoff fibre has size at most two.

### H. Quantitative Sampling Consequence: TC2

Define the off-ray matrix A_o(R,n)=1/q at the unique event (R,q) with cutoff n, and zero otherwise. Let sigma_R=sum_(q:(R,q) in Omega_o)1/q^2 and sigma_*=max_R sigma_R, with zero for an empty population.

**Claim TC2, PAPER_PROOF.** On the TC1 domain,

```text
A_o*A_o^t = diag(sigma_R)+K,
||K||_(2->2) <= 2/Q,
sum_R |sum_(q off-ray small) z_(Y(R,q))/q|^2
  <= min(2*sigma_*, sigma_*+2/Q) * sum_(n in image) |z_n|^2.
```

This is uniform for every real vector z, every finite I, and every stated H,Q. K has nonnegative off-diagonal entries, zero same-parity entries, and entries obtained by summing 1/(qr) over the actual two-event cutoff fibres. No cancellation of K is assumed.

**Proof.** Every event has at most one partner. By TC1 its colliding labels exceed Q/2, so each partner weight is below 4/Q^2. Each row has at most Q/2 odd prime labels. Thus every row sum of K is at most 2/Q. Symmetry and 2|ab|<=a^2+b^2 give |v^t K v|<=(2/Q)||v||^2. Adding the diagonal and using finite-dimensional duality proves the second coefficient. Row Cauchy-Schwarz and column multiplicity at most two give the first coefficient. Take the minimum.

For nonnegative root weights alpha_R define beta_n=max_(events at n)alpha_R. Then the same coefficient gives the source-preserving weighted form

```text
sum_R alpha_R*|sum_(q off-ray small) M(Y(R,q))/q|^2
 <= min(2*sigma_*,sigma_*+2/Q)*sum_n beta_n*M(n)^2.
```

To prove it, omit beta_n=0 columns and replace each matrix entry by sqrt(alpha_R/beta_n)/q. Its diagonal and off-diagonal row sums are bounded by the previous ones. Apply the same norm argument to z_n=sqrt(beta_n)*M(n). The multiplicity and exact weights are retained.

Compared with the coarse multiplicity-two estimate, this recovers the injective leading coefficient with an additive O(1/Q) error, using no PNT. At Q=floor((4H)^(1/3)), the error is O(H^(-1/3)). This is a GEOMETRIC operator improvement only. It neither bounds the sampled Mertens energy at a new power nor supplies the complete signed bill. At small Q the minimum avoids claiming an improvement where the coarse bound is better.

The original Wheel SP2/SP3 claims at Q^3<=2H were independently reconstructed on their exact event and Gram carriers. This is a scoped finite computational cross-check, not a blanket Referee endorsement of every upstream paper claim.

### I. Complete Signed Column Return: TC3

Let U_o(R), E_o(R) be the original sum and square sum over off-ray q<=Q. Preserve the entire complement

```text
F_R=G_R^2+2*G_R*(U_R-U_o(R))-2*(E_R-E_o(R))-Hdiag_R,
B_R=F_R+2*G_R*U_o(R)-2*E_o(R).
```

For alpha_R>=0 and every off-ray column n put

```text
w_n=sum_(events at n) alpha_R,
t_(R,q)=G_R/q,
tbar_n=(sum_(events at n) alpha_R*t_(R,q))/w_n,
A=sum_(off events) alpha_R*t_(R,q)^2,
P=(1/2)*sum_n sum_(events at n) alpha_R*(t_(R,q)-tbar_n)^2,
D=sum_n w_n*(M(n)-tbar_n/2)^2.
```

Omit w_n=0 columns. **Claim TC3, PAPER_PROOF, exact equality:**

```text
sum_R alpha_R*B_R = sum_R alpha_R*F_R + A/2 - P - 2D.
```

This follows by expanding each finite column square. For a double column with events (R,q),(S,r), its new explicit penalty is

```text
P_n=alpha_R*alpha_S/[2*(alpha_R+alpha_S)]*(G_R/q-G_S/r)^2.
```

For unit weights it is (G_R/q-G_S/r)^2/4. The generic variance identity is elementary existing algebra; the new arithmetic information is that its nonzero edges in the transition range can only be the coprime, opposite-parity, high-label pairs in TC1.

If the full weighted bill exceeds L>0, then necessarily either

```text
sum alpha_R*F_R > L/2,
```

or

```text
A>L and P+2D < (A-L)/2.
```

This is an exact necessary alternative, not a proof that either branch is absent. No negative daughter square was spent separately before this equality. At h=1, P=0 and F still contains the full parent square; the statement does not manufacture a pointwise improvement from averaged geometry.

Example complete conservation test, H=550,Q=13,h=550, alpha=1:

```text
sum B = -78391992968780396/314358135,
sum F = -170837186071754912/691587897,
A/2   = 17195434316318/20495475,
P     = 6664083/81796,
2D    = 2875714594527157/901800900.
```

There are 2,279 off-ray columns and seven double columns. The displayed equality holds exactly, with zero residual, and all q>Q/ray contributions and physical diagonals are restored. The other 171 weighted cases also have zero residual.

### J. Proof Impact And Remaining Quantitative Obligation

The arithmetic distinction is now precise: integer rays repeat square-endpoint prefixes; first-transition off-ray collisions couple COPRIME roots of opposite parity near the prime-label cutoff. Neither is a model of independent Mertens values. Their underlying prefixes overlap extensively.

TC2 repairs the multiplicity cost when slightly widening the geometric cutoff. TC3 describes exactly what simultaneous near-saturation would demand of the signed parents. Neither controls the full parent/ray/tail complement. In fact all new collision labels lie at the high end of this selected band, where the existing native-envelope tail method is already available. Do not count that paid tail again or claim that a constant-factor cutoff enlargement changes a power exponent.

The actual consumer requires, for one fixed b_new>=1/2 and some A>=0,

```text
forall R>=56, B_R <= A*R^(4*b_new).
```

It returns MertensPowerBound(b_new), retaining the physical diagonal. To improve the incoming boundary b_base, an independently proved estimate B_R=O_e(R^(4*b_base-eta+e)) would give an every-positive-loss boundary b_base-eta/4; spending e=eta/2 yields the fixed power b_base-eta/8. This is CONDITIONAL and not supplied here. The full bill inequality is not relabeled as an elementary new premise. Canonical LOW and unfinished-square O(R) costs remain paid transfer terms, not new work.

The geometric O(1/Q) error is the only new quantified bound in this run. There is no new all-scale signed Mertens, actual-prime VF, RH, or uniform all-h canonical HIGH exponent bound.

### K. Falsification, Uncertainty And Scope Audit

| Claim | Evidence class | Scope |
| --- | --- | --- |
| TC1: determinant/parity/high-label and short-window theorem | PAPER_PROOF | All finite sets/windows under displayed hypotheses; SELF_AUDIT |
| TC2: sampling Gram and 2/Q norm error | PAPER_PROOF | Geometric operator, with exact weighted corollary; not new signed cancellation |
| TC3: weighted complete-return penalty | PAPER_PROOF | Exact finite identity and necessary alternative; complement retained |
| TC4: doubled injectivity and harmless deletion | REFUTED | Original arithmetic witness, minimal by largest root for injectivity |
| TC5: all registered reconstructions and source checks | FINITE_COMPUTATION | Explicit finite ranges only |

All number-theoretic predicates and comparisons used exact integers or rationals. There are no logarithms, uncertified decimal signs, probable-prime decisions, random seeds, or fitted exponents. Synthetic Gram vectors are explicitly not genuine arithmetic data. The held-out cases were fixed before scanning; the short-window assertion and the 81/127 control are disclosed post-discovery work.

Independent computational methods agreed; there was no unexplained discrepancy or failed mathematical assertion suppressed. The outside-cutoff corpus's failure to find determinant two is recorded, not presented as evidence for an unrestricted theorem. The added control demonstrates the opposite.

Source-fidelity audit: genuine coefficients and all occurrence weights PRESERVED; historical M(R-1) PRESERVED; strict q^2<R and literal R^2-1 floor PRESERVED; squareful zeros and diagonal PRESERVED; all cross terms in the original mixed source PRESERVED and independently reconstructed at R=56; full q-label complement PRESERVED. Original #915 NNS normalization, conductor sectors, canonical ancestry Gram and absorption are NOT_APPLICABLE to this specific CORR4 carrier and are not silently identified with it.

Bounded novelty review: current selected Lean source, the actual SP1-SP5 derivation, DI, own SC/RC, and the relevant current two-day handoffs were inspected. No same transition parity/reciprocal-error theorem was found in that retrieved material. This is neither an exhaustive historical search nor a claim of worldwide novelty.

### L. Continuity And Specialist Handoffs

Today Owner PD, Analytic MP and Wheel SP were available at intake. Coordinator, Referee and Lean were TODAY=PENDING, with November 7 YESTERDAY=CARRY_FORWARD. Own November 7 SC/RC were retrieved. The latest Coordinator WS, Referee TF/RG and Lean #1107 state were read; later human merge supersedes their historical unmerged wording, not their mathematical qualifications.

Execution/publication timestamps preserved from the retrieved handoffs:

| Report and stable run | Latest cited substantive receipt, UTC | Claims carried |
| --- | --- | --- |
| Nov 8 Owner, 20261108-owner-1 | Nov 8 05:32:59 | PD1-PD6 |
| Nov 8 Analytic, 20261108-analytic-1 | Nov 8 06:33:18 | MP1-MP6 |
| Nov 8 Wheel, 20261108-wheel-1 | Nov 8 07:34:03 | SP1-SP5 |
| Nov 7 Coordinator, 20261107-coordinator-2309 | Nov 8 04:35:35 | WS and protected-route handoffs |
| Nov 7 Owner, 20261107-owner-3 | Nov 7 21:37:02 | SG/RS/JT |
| Nov 7 Analytic, 20261107-analytic-3 | Nov 7 22:33:48 | GL/FT/BC |
| Nov 7 Wheel, 20261107-wheel-3 | Nov 7 23:33:09 | DI/LR/OC |
| Nov 7 Census, 20261107-census-2 | Nov 7 16:24:51 | SC/RC |
| Nov 7 Referee, 20261107-referee-3 | Nov 8 01:33:31 | RG/TF and scoped prior acceptance |
| Nov 7 Lean, 20261107-lean-3 | Nov 8 02:28:57 | #1107 and KL |

These are observed report receipts, not independently relaunched stages. Coordinator AM/PM blobs were identical at intake; only the AM text needed a separate content retrieval. Unrelated historical code appendices were not rerun.

Owner's PD small-gap/primitive-ratio estimates, Analytic's MP prime-ray mixed estimate, and Wheel's SP sampling theorem remain their stated paper/self-audit scopes. No automatic transfer between prime-error cofactors, additive windows and moving squared daughter samples was assumed. Prior DI sign/overlap, SC physical/signed-capacity counterexamples and RC zero-gain-face restrictions were reused as cautions, not recomputed as new findings. The external inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 has no post-October-18 entry; EXT-20261018-PNT-1..3, EXT-20261017-XCOORD-1 and EXT-20261014-5 remain carrier/boundary/denominator safeguards, not suppliers for TC1-TC3.

- Proof Architect: record TC4 as the exact limit of an unqualified doubled injectivity extension. TC1-TC2 provide a replacement geometric estimate; TC3 retains the complement alternative. Do not promote it to an endpoint gain or force other routes onto this graph.
- Finite Wheel: SP2/SP3 passed independent finite event/Gram reconstruction. The transition is controlled by root parity and determinant one; use TC1-TC2 if a wider selected cutoff is actually useful. Do not erase the ray branch or repeat this census.
- Analytic: the new collision-root pairs are coprime and opposite parity, but that is not an identification with the physical mu(n)mu(n+k) source in MP/CODIV. A source/weight bridge would be needed before using either route's estimate.
- Owner: TC3's parent-disagreement term is an exact finite diagnostic, not a prime-error estimate. The PD sign-reversal/full-complement checks remain an independent ready Census task.
- Adversarial Referee: independently review the strict determinant bound at Q^3=4H, the label-band monotonicity, weighted column normalization, and every retained complement in TC3. Author self-audit is not your acceptance.
- Lean Verification: TC1-TC2 are review candidates only if an active quantitative consumer needs this interface. Reuse rawQ2ChildCutoff and strict source masks; do not formalize a target-assuming endpoint wrapper or duplicate #1097. No new proof branch or agent launch is requested or performed.

### M. Ranked Experimental Hypothesis Portfolio

| Rank / hypothesis | Evidence and counterevidence | Independent ingredient / next theorem | Disposition |
| --- | --- | --- | --- |
| 1. TC1-TC2 transition geometry | Exact falsifier plus paper replacement and held-out checks; no exponent consequence | Odd-prime determinant spacing and high-label reciprocal bound; independent review | Retain as a proved-on-paper interface; stop unchanged scaling |
| 2. TC3 joint alignment restriction | Exact full-source identity; parent disagreement is measurable but complement may dominate | A genuine joint quantitative estimate, not assumed bill control | Exploratory only; no cancellation claim |
| 3. RC source-backed marked/capacity consumer | Prior exact certificate; BC/source integration and full HIGH return still qualified | Actual compatible count and complete consumer | Carry forward; no unchanged scalar rerun |
| 4. SC/OC capacity-safe MU-LIFT and Owner PD | Physical and signed capacity obstructions preserved; PD offers independent original-prime checks | Correct source capacities or certified original prime-error intervals | Preserve independent routes; do not conflate carriers |

The three investigators retain their own protected portfolios. This Census support choice does not count as their next invocation or reset their rolling coverage. WS-WINDOW-FALSIFIER is deferred, not completed or refuted.

### N. Resume Capsule And Execution Record

```text
RUN: 20261108-census-1, scheduled 03:11:01 EST; RUN_ID_UNAVAILABLE.
MAIN: bf4af1cd18aff7c3944a75991aa66371c8afc18a.
SOURCE: literal CORR4 daughter sampling and full mixed-tail return.
NEW: smallest doubled-range collision (556,11),(657,13), Y=2554, M=-5;
     determinant-one / coprime / opposite-parity classification;
     q,r>5Q/8; reciprocal Gram error <=2/Q;
     complete weighted parent-disagreement penalty.
FINITE: 800309 identical forward/inverse events; 1045 identical signed rows;
        1823095 independently reconstructed physical pairs;
        172 weighted return identities; all exact checks passed.
STATUS: TC1-TC3 PAPER_PROOF/SELF_AUDIT, TC4 REFUTED, TC5 FINITE_COMPUTATION.
REVIEW / NEW LEAN / NEW GLOBAL EXPONENT: PENDING / NONE / NONE.
DO NOT REPEAT: unchanged SP/TC sampling, SC capacity table, RC rectangle,
              paid large-owner tail, baseline endpoint audit.
NEXT SINGLE CENSUS EXPERIMENT: independently certify Owner PD's original
  Li/prime-error sign reversal at R=36 and R=41, with the full R=16
  complement witness, unless a newer source-backed consumer takes priority.
NEXT CORR4 USE: only if an actual signed consumer needs the transition
  interface; otherwise park it and preserve broad independent coverage.
```

Environment actually observed: CPython 3.12.14, g++ 13.3.0, Linux x86_64. Python forward geometry took 1.759 seconds; signed reconstruction took 1.858 seconds; the final Gram/cell/weighted audit elapsed time is in the captured output below. C++ runs completed exit zero but were not separately timed. All necessary sessions finished. No local Lean was run. Only the authorized own report is written remotely; no main, source, other report, issue, comment, branch, PR, workflow, permission, schedule, merge or other-agent launch was modified.

Early checkpoint commit abd2324f4efc0266a28980a372891319f1e33a6e and blob d79b52d1ea96d19b0a781b32159adec7fdb988ed were read back exactly. Final publication evidence is appended only after the write and immutable verification.

Final freshness check at 08:38:45 UTC: main is still
bf4af1cd18aff7c3944a75991aa66371c8afc18a; the sole open PR is still #1108,
non-draft, head a0c986c0343a56e98b7344268fdc0b74aa885cdb. The reports branch
is at the early checkpoint commit abd2324f4efc0266a28980a372891319f1e33a6e,
so no other report has changed since intake and the pending/carry-forward
labels above remain accurate. Both independently produced event streams
and signed streams were compared again and retained their recorded hashes.


### Provenance Ledger


**Authority**

| Path | Git blob SHA |
| --- | --- |
| AGENTS.md | 0a99faf8458809ac772d470d704c5433f373bda8 |
| CURRENT_PROOF_CONTRACT.md | d1d6fd558ee23927bd9f70ffdc375bafd1dbb67a |
| docs/RHLEAN_COMPLETE_SIGNED_HIGH_ATTACK_20261107.md | be8168b67584d9d8ebbaa732a30c51509137543e |
| docs/RHLEAN_REUSE_CANCELLATION_CHAIN_20261107.md | 28e2ab47c68bc83b91ae02b6112b94867b021b32 |
| docs/RHLEAN_PAID_BASELINE_EXACT_CONSUMER_20261106.md | 13d58dd12d90fbf1160812c7c93442dc5d0576ac |
| docs/RHLEAN_INDEPENDENT_MULTIFRONT_NO_PIGEONHOLING_20261104.md | 6ff6eb30b91705af5478d3705849234260f8a7a3 |
| docs/RHLEAN_NATIVE_SQUARE_CLOCK_AGENT_DIRECTIVE_20261029.md | a0198ff1877de2a0ce164ff5a21768583c7a144a |
| docs/RHLEAN_ALL_VECTOR_AGENT_PROMPTS_20261030.md | 151283a82eb699f734b80e67dcee7b24a90d1e1d |
| docs/RHLEAN_SOURCE_FAITHFUL_COMPLETE_RETURN_AGENT_CONTRACT_20261031.md | 4775ee5fd95f279beab08a75d1e17127078b19a6 |
| docs/RHLEAN_SEVEN_AGENT_RESEARCH_ENGINE_20261101.md | 3f4e594c6af26e57ba0800b2a1ec81effb71db13 |
| docs/RHLEAN_BROAD_SEARCH_UNTIL_ETA_20261031.md | 469caefcd2d82f8d59044f67c78c89ebbe613ac7 |
| docs/DYNAMIC_RESEARCH_AGENTS.md | dd99f8d6fff199c9cad363a4ea8d9e721079c4bb |
| docs/RHLEAN_MULTIRUN_DAILY_AGENT_POLICY_20261031.md | 643cfd596116720a8e5b1efc07a6124b55d70946 |

**Inspected original source**

| Path | Git blob SHA |
| --- | --- |
| research/CORR4_SQUARE_CLOCK_SAMPLING_20261106.lean | e823a1a124dc1bfe4c38d4af4ee10c1e481cad2a |
| RHLean/Proof/SignedTransportAmplificationAudit.lean | 746f35f126f36e024d39e38c92dde30aabca266b |
| research/CANONICAL_ROUGH_Q2_TAIL_REDUCTION.lean | ebca096e83009a7df514d00b6a2696be86a94c55 |
| research/GLOBAL_RETURNED_CORE_WEIGHTED_MOBIUS_COORDINATE.lean | f0e2e672a1ed369d1dc6dacbe9024c65e986a3c8 |
| research/GLOBAL_RETURNED_CORE_RECIPROCAL_PREFIX_SIGNED_CELL_SPLIT.lean | 29bb263ddd07b12a2dd5ccf6a12aecaf627134d8 |
| research/GLOBAL_RETURNED_CORE_RAW_PARENT_Q2_MERTENS_REASSEMBLY.lean | 0df95fc520a589925e094651304f15da78bdf5a8 |
| research/GLOBAL_RETURNED_CORE_Q2_DAUGHTER_FIRST_OWNER_GRAM.lean | b57a3e9030445262ec847ca0e20a60bc35ff127c |
| research/CORR4_OAI_POWER_MIXED_TAIL_GATE_20261025.lean | bb0ee1252e7ba10c44ae5b8d827573d6c581b73a |
| research/oai_434/VF919TotalMassEndpoint.lean | 827bb952c4d4311d75fd03a2470799dc10b0f7e7 |
| RHLean/Analysis/CanonicalHighSectorCore.lean | dd02fc8fabfe4004c6b0d50374b3b8752607b168 |
| RHLean/Analysis/CanonicalLowOccupancy.lean | b958da340d107cdd00015d2827b9a728357b4d8e |
| docs/RHLEAN_TOTAL_SLOT_MASS_ENDPOINT_20261107.md | 305c68bb407e2580417373fbf20ca1e29104ec0b |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |
| research/GLOBAL_RETURNED_CORE_FIRST_OWNER_CELLS.lean | 5ca177548e91dd8bc6535e9913b29dc81cdfccea |
| research/GLOBAL_RETURNED_CORE_GLOBAL_FIRST_OWNER_SITE_FUBINI.lean | 4646217f223128a02517bb34403ac3577585a1f2 |
| research/GLOBAL_RETURNED_CORE_CONTINUATION_CARRIER.lean | 34b3c9decd7d32f2262e9a68c1a849f4e705e530 |
| research/GLOBAL_RETURNED_CORE_WEIGHTED_GRAM.lean | dbaf123113b544d0b19c7c3c6b92a1288a26cfb8 |
| research/GLOBAL_RETURNED_CORE_PREFIX_TAIL_MIXED_REMAINDER_IDENTITY.lean | d17aeb639bb47d79333cf0d00760c2604feddfdf |

**Two-day continuity**

| Path | Git blob SHA |
| --- | --- |
| research/agent_reports/2026-11-08/10-owner-payment.md | 79dd00b2c26491ab302ea17d6dbe4e0146d57a97 |
| research/agent_reports/2026-11-08/20-analytic-type-ii.md | b32aa501bff08a8da7ecf387f4e9a168f71ea3e5 |
| research/agent_reports/2026-11-08/30-finite-wheel.md | 5b56caa1e7b3463510a7257b10a784ccc8798621 |
| research/agent_reports/2026-11-07/00-coordinator-am.md | 00a649b70f851ca193e74e5004d0d3390cf9ca18 |
| research/agent_reports/2026-11-07/10-owner-payment.md | 933e8eb23e669594cc687059d75147e6267eec8d |
| research/agent_reports/2026-11-07/20-analytic-type-ii.md | 77f3e5795533041e4356ceb94cb66328da7af27c |
| research/agent_reports/2026-11-07/30-finite-wheel.md | 7739fa5d4cc77f35773b0d4149b2ddd21732a70d |
| research/agent_reports/2026-11-07/40-prime-census.md | 3fae830e34c590d32c31ad77cad3ace833eb3ff5 |
| research/agent_reports/2026-11-07/50-adversarial-referee.md | 426c2abfa5b8926b512e07f05be37692a2416d0b |
| research/agent_reports/2026-11-07/60-lean-verification.md | ec14e2803af8c1e56123682ee61ed927ed4f9450 |
| research/agent_reports/README.md | 98b56f98d625b61b7a6491e360d7870fbfe7e7a1 |
| research/agent_reports/EXTERNAL_HANDOFFS.md | 038018145c0fddb2f6306c0712373adf9cd1ea52 |
| research/agent_reports/REPORT_TEMPLATE.md | cd76e67ca540e8d697ec3a36534cd87263b69bba |

### Reproduction Commands

All five executed source files are included verbatim below. Run them in one directory.

```bash
python geometry.py
g++ -O2 -std=c++17 -Wall -Wextra -pedantic inverse.cpp -o inverse
./inverse
cmp forward-events.txt inverse-events.txt
python signed.py
g++ -O2 -std=c++17 -Wall -Wextra mobius_reference.cpp -o mobius_reference
./mobius_reference
cmp signed-python.txt signed-cpp.txt
python gram_audit.py
```

The complete event stream SHA256 is `25e15da2ae8315b22ad4377895d95257f7f014b2358bfea319bcd5e9305af84e`; both independent streams have this hash. The complete signed stream SHA256 is `86419100930c190944a27f962ae8e797ce89368a2838629d6c9447ec590543ba`; both independent streams have this hash. Output timing fields will vary. The exhaustive inverse method is deliberately slower than forward enumeration; its range is fixed, not an open-ended scan.

### Executed Source Manifest

| File | SHA256 |
| --- | --- |
| preregistration.md | 3c99f92ed14faf7a99dce6fcfc9f18985bdbdb8858a6fa8229dd95fddcce1c87 |
| geometry.py | 1945c59c5b71e7ec3e7c4fc577b2b19d713adf3d94b7ca25e1334cd249f49f51 |
| inverse.cpp | 00ced362a0c1eeb9f6c8a0c256f1eea88ba24c5ea7a2a7b08b7d902bd5669d07 |
| signed.py | c48fc3affc8abbf5f982286eccde7f9940c05d2c061405c70ec35dbc5e82eb97 |
| mobius_reference.cpp | 38aa16879c5dc393b8e1305f984cab563c265283c792fc0548478d83c477c0a5 |
| gram_audit.py | 42b7e281ca7b3e791cb9d89918276c22e216f404cf2be4df4cb5e8914e5e616a |

#### preregistration.md

```markdown
# Exact CORR4 Transition Registration

The early report published at abd2324f4efc0266a28980a372891319f1e33a6e
is the primary preregistration. This file records pre-execution derived tests.

- The proposed doubled-cube theorem is Q^3<=4H: off-ray columns have
  degree at most two; each collision has determinant +/-1, coprime roots,
  and opposite root parity. The cube-range theorem is checked as a subset.
- Before running, test the additional proposed restriction 8q>5Q for
  BOTH labels in each collision; it follows if the elementary inequalities
  2H(q+r)<=2q^2r^2 and Q^3<=4H can be sharpened as expected.
- Test the proposed off-diagonal reciprocal row degree <=2/Q.
  This is a geometric sampling bound, not signed arithmetic cancellation.
- Frozen cases and code use integer forward events, independent inverse
  cutoff intervals, and deterministic trial-division primality in C++.
- All discovered collisions are preserved, including above-cutoff controls.
- Signed tests will use every R=56..1100, linear-sieve Mobius versus
  independent divisor-recursion Mobius. A complete literal site-pair
  reconstruction is required at R=56. Larger signed ranges are not planned.
- Full signed identity test: the column-grouped completion must equal
  the full original bill after the parent, ray/tail, diagonal, and history
  complement is restored. A repeated endpoint does not remove an occurrence.
- Once a legal doubled-cube counterexample is found, attempt a bounded
  exhaustive search for the smallest witness by largest root; the bound
  will be the first observed witness, not an indefinitely growing census.

No experiment results were used to select these tests.

## Disclosed Post-Discovery Audit

After the first forward/inverse run and signed run, the witness
(556,11),(657,13), Y=2554 was known. The next script independently uses
the inverse stream to check the full sampling Gram, parity separation,
and the proposed 2/Q reciprocal row bound. A newly derived short-window
condition Q(h-1)<2H-1 is tested on the SAME fixed corpus, without adjusting
its constant. Synthetic row vectors are marked as geometric tests only.
The R=56 physical pair sum is also rebuilt from the actual least-prime
owner and lower-signature cell definitions, with trial-factor Mobius.
This is independent reconstruction within this run, not Referee acceptance.

The registered neighboring-cap corpus contained no determinant-two example.
A disclosed algebraically engineered negative control was then added:
(R,q)=(81,7), (S,r)=(127,11), both outside the doubled-cube hypothesis.
It is not a failure of the proposed theorem and is not claimed minimal.

Final validation adds the derived weighted TC2 operator inequality on the
same small-root windows and ten fixtures for the preregistered strict-mask
condition, selecting q=3,5,7,11,13,17,19,23,29,31 after discovery.
The smaller fixtures below root 56 concern
the sampling definition only, not the R>=56 complete-source consumer.
```

#### geometry.py

```python
"""Exact forward reconstruction of the registered CORR4 event carrier."""

import hashlib
import json
import math
import time
from collections import defaultdict
from itertools import combinations
from pathlib import Path

ROOTS = [56, 64, 86, 128, 256, 333, 550, 1024, 2048, 4096, 8192]
BASE = Path(__file__).resolve().parent


def cube_floor(n):
    k = 0
    while (k + 1) ** 3 <= n:
        k += 1
    return k


def primes_up_to(n):
    prime = bytearray(b"\1") * (n + 1)
    prime[:2] = b"\0\0"
    for p in range(2, math.isqrt(n) + 1):
        if prime[p]:
            prime[p * p:n + 1:p] = b"\0" * ((n - p * p) // p + 1)
    return [p for p in range(3, n + 1) if prime[p]]


def cases():
    for h0 in ROOTS:
        q2, q4 = cube_floor(2 * h0), cube_floor(4 * h0)
        for q in sorted({q2, q4 - 1, q4, q4 + 1}):
            for width in sorted({1, min(7, h0), h0 // 2, h0}):
                yield h0, q, width


def main():
    start = time.perf_counter()
    primes = primes_up_to(100)
    summaries, collisions = [], []
    event_hash = hashlib.sha256()
    event_count = comparisons = 0
    with (BASE / "forward-events.txt").open("w") as stream:
        for h0, cap, width in cases():
            buckets = defaultdict(list)
            events = []
            for root in range(h0, h0 + width):
                for prime in primes:
                    if prime > cap or prime * prime >= root:
                        break
                    n = (root * root - 1) // (prime * prime)
                    ray = int(root % prime == 0)
                    line = f"{h0} {cap} {width} {root} {prime} {n} {ray}\n"
                    stream.write(line)
                    event_hash.update(line.encode())
                    events.append((root, prime, n, ray))
                    buckets[n].append((root, prime, ray))
                    assert n * prime * prime < root * root <= (n + 1) * prime * prime
                    assert (math.isqrt(n + 1) ** 2 == n + 1) == bool(ray)
            off_pairs = 0
            max_off = 0
            degree = defaultdict(lambda: 0)
            for n, group in buckets.items():
                off = [v for v in group if not v[2]]
                max_off = max(max_off, len(off))
                if off:
                    assert len(off) == len(group)
                for (r0, q, _), (s0, r, _) in combinations(off, 2):
                    det = r0 * r - s0 * q
                    comparisons += 1
                    off_pairs += 1
                    assert abs(det) * (r0 * r + s0 * q) < q * q * r * r
                    if cap ** 3 <= 2 * h0:
                        raise AssertionError("SP2 cube-range collision")
                    if cap ** 3 <= 4 * h0:
                        assert abs(det) == 1
                        assert math.gcd(r0, s0) == 1 and (r0 + s0) % 2 == 1
                        assert 8 * min(q, r) > 5 * cap
                        from fractions import Fraction
                        degree[r0] += Fraction(1, q * r)
                        degree[s0] += Fraction(1, q * r)
                    collisions.append(dict(H=h0, Q=cap, h=width, n=n,
                                           first=[r0, q], second=[s0, r], det=det))
                if cap ** 3 <= 4 * h0:
                    assert len(off) <= 2
            if cap ** 3 <= 4 * h0:
                from fractions import Fraction
                assert max(degree.values(), default=0) <= Fraction(2, cap)
            event_count += len(events)
            summaries.append(dict(H=h0, Q=cap, h=width, events=len(events),
                                  off_pairs=off_pairs, max_off=max_off,
                                  doubled=cap ** 3 <= 4 * h0,
                                  max_degree=str(max(degree.values(), default=0))))
    out = dict(cases=summaries, collisions=collisions,
               event_count=event_count, pair_comparisons=comparisons,
               event_sha256=event_hash.hexdigest(), seconds=time.perf_counter() - start)
    (BASE / "geometry.json").write_text(json.dumps(out, indent=2) + "\n")
    legal = [c for c in collisions if c["Q"] ** 3 <= 4 * c["H"]]
    first = min(legal, key=lambda c: (max(c["first"][0], c["second"][0]),
                                    c["first"], c["second"], c["H"], c["Q"], c["h"]))
    print(json.dumps({k: out[k] for k in ["event_count", "pair_comparisons", "event_sha256", "seconds"]}, indent=2))
    print(json.dumps(dict(cases=len(summaries), legal_pair_evaluations=len(legal),
                          first_doubled_collision=first), indent=2))


if __name__ == "__main__":
    main()
```

#### inverse.cpp

```cpp
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <tuple>
#include <vector>

using I = std::int64_t;

I isqrt(I n) {
    I r = static_cast<I>(std::sqrt(static_cast<long double>(n)));
    while ((r + 1) * (r + 1) <= n) ++r;
    while (r * r > n) --r;
    return r;
}

I cubert(I n) {
    I r = 0;
    while ((r + 1) * (r + 1) * (r + 1) <= n) ++r;
    return r;
}

bool prime(I n) {
    if (n < 2) return false;
    for (I d = 2; d * d <= n; ++d) if (n % d == 0) return false;
    return true;
}

int main() {
    const std::vector<I> roots = {56,64,86,128,256,333,550,1024,2048,4096,8192};
    std::ofstream out("inverse-events.txt");
    I count = 0, intervals = 0;
    for (I H : roots) {
        I q2 = cubert(2 * H), q4 = cubert(4 * H);
        std::set<I> caps = {q2, q4 - 1, q4, q4 + 1};
        std::set<I> widths = {1, std::min(I(7), H), H / 2, H};
        for (I Q : caps) for (I h : widths) {
            std::vector<std::tuple<I,I,I,I>> rows;
            for (I q = 3; q <= Q; q += 2) {
                if (!prime(q)) continue;
                I bottom = std::max(H, q*q + 1), top = H + h - 1;
                if (bottom > top) continue;
                I n0 = (bottom*bottom - 1)/(q*q);
                I n1 = (top*top - 1)/(q*q);
                for (I n = n0; n <= n1; ++n) {
                    ++intervals;
                    I lo = std::max(bottom, isqrt(n*q*q) + 1);
                    I hi = std::min(top, isqrt((n+1)*q*q));
                    for (I R = lo; R <= hi; ++R)
                        rows.emplace_back(R,q,n,I(R % q == 0));
                }
            }
            std::sort(rows.begin(), rows.end());
            for (auto [R,q,n,ray] : rows) {
                out << H << ' ' << Q << ' ' << h << ' ' << R << ' '
                    << q << ' ' << n << ' ' << ray << '\n';
                ++count;
            }
        }
    }
    std::cout << "inverse_events=" << count << " inverse_intervals=" << intervals << '\n';
    return 0;
}
```

#### signed.py

```python
"""Exact signed return, minimal-witness search, and collision completion."""

import hashlib
import json
import math
import platform
import time
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path

from geometry import BASE, cases, primes_up_to


def mobius_linear(limit):
    mu = [0] * (limit + 1)
    least = [0] * (limit + 1)
    primes = []
    mu[1] = 1
    for n in range(2, limit + 1):
        if not least[n]:
            least[n] = n
            primes.append(n)
            mu[n] = -1
        for p in primes:
            if n * p > limit:
                break
            least[n * p] = p
            if n % p == 0:
                break
            mu[n * p] = -mu[n]
    return mu


def mobius_trial(n):
    ans, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            ans = -ans
            if n % p == 0:
                return 0
        p += 1
    return -ans if n > 1 else ans


def main():
    start = time.perf_counter()
    limit = 1100 ** 2 - 1
    mu = mobius_linear(limit)
    M, V = [0] * (limit + 1), [0] * (limit + 1)
    for n in range(1, limit + 1):
        M[n] = M[n - 1] + mu[n]
        V[n] = V[n - 1] + mu[n] ** 2
    assert all(mu[n] == mobius_trial(n) for n in range(1, 10001))
    primes = primes_up_to(100)
    rows = {}
    with (BASE / "signed-python.txt").open("w") as stream:
        for R in range(56, 1101):
            X = R * R - 1
            owners = [q for q in primes if q * q < R]
            denom = math.prod(owners)
            ds = {q: M[X // (q * q)] for q in owners}
            G = M[X] - M[R - 1]
            U = sum((F(d, q) for q, d in ds.items()), F(0))
            E = sum(d * d for d in ds.values())
            Hdiag = V[X] - V[R - 1] + 2 * sum(
                (F(V[X // (q * q)] - V[R - 1], q) for q in owners), F(0))
            bill = G * G + 2 * G * U - 2 * E - Hdiag
            assert (bill * denom).denominator == 1
            stream.write(f"{R} {G} {E} {denom} {int(bill * denom)} {M[X]} {M[R-1]}\n")
            rows[R] = dict(G=G, U=U, E=E, Hdiag=Hdiag, bill=bill, ds=ds)

    # Reconstruct every unordered physical pair at the smallest consumer root.
    R, pair_sum, physical_pairs = 56, 0, 0
    X = R * R - 1
    owners = list(rows[R]["ds"])
    denom = math.prod(owners)
    sites = []
    for n in range(1, X + 1):
        if mu[n]:
            p = mu[n] * sum(denom // q for q in owners if n <= X // (q*q))
            f = mu[n] * int(R <= n)
            sites.append((n, p, f))
    for i, (_, p, f) in enumerate(sites):
        for _, pp, ff in sites[i + 1:]:
            pair_sum += p * ff + f * pp + denom * f * ff
            physical_pairs += 1
    physical_bill = F(2 * pair_sum, denom) - 2 * rows[R]["E"]
    assert physical_bill == rows[R]["bill"]

    # Bounded minimality search: every potentially admitted pair up to 657.
    buckets = defaultdict(list)
    witness_candidates = []
    for R in range(56, 658):
        for q in primes:
            if q*q >= R:
                break
            if q**3 <= 4*R and R % q:
                buckets[(R*R-1)//(q*q)].append((R,q))
    for n, group in buckets.items():
        for (R,q), (S,r) in combinations(group, 2):
            if max(q,r)**3 <= 4*min(R,S) and max(R,S) < 2*min(R,S):
                witness_candidates.append((max(R,S), min(R,S), q, r, n))
    first = min(witness_candidates)
    S, R, q, r, n = first
    witness = dict(R=R, S=S, q=q, r=r, n=n, d=M[n],
                   M_R2=M[R*R-1], M_S2=M[S*S-1],
                   G_R=rows[R]["G"], G_S=rows[S]["G"],
                   B_R=str(rows[R]["bill"]), B_S=str(rows[S]["bill"]))
    assert M[n] == sum(mobius_trial(i) for i in range(1, n + 1))
    x, y = F(rows[R]["G"], q), F(rows[S]["G"], r)
    witness.update(parent_targets=[str(x/2), str(y/2)],
                   disagreement_penalty=str((x-y)**2/4),
                   repeated_column_square=str((F(M[n],q)+F(M[n],r))**2),
                   cross_term=str(F(2*M[n]**2,q*r)))

    # General weighted column completion, including all complementary terms.
    window_results = []
    for H,Q,h in cases():
        if H+h-1 > 1100 or Q**3 > 4*H:
            continue
        for mode in [0,1]:
            columns = defaultdict(list)
            full, complement, A = F(0), F(0), F(0)
            for R in range(H,H+h):
                alpha = F(1) if not mode else F(1+(R-H)%5,5)
                row = rows[R]
                off = {q:d for q,d in row["ds"].items() if q<=Q and R%q}
                Uo = sum((F(d,q) for q,d in off.items()),F(0))
                Eo = sum(d*d for d in off.values())
                full += alpha*row["bill"]
                complement += alpha*(row["bill"]-2*row["G"]*Uo+2*Eo)
                for q in off:
                    columns[(R*R-1)//(q*q)].append((R,q,alpha))
                    A += alpha*F(row["G"]**2,q*q)
            penalty, residual = F(0),F(0)
            pair_columns = 0
            for n, events in columns.items():
                weight = sum((a for _,_,a in events),F(0))
                target_sum = sum((a*F(rows[R]["G"],q) for R,q,a in events),F(0))
                target_sq = sum((a*F(rows[R]["G"]**2,q*q) for R,q,a in events),F(0))
                penalty += (target_sq-target_sum**2/weight)/2
                residual += 2*weight*(M[n]-target_sum/(2*weight))**2
                if len(events)==2:
                    pair_columns += 1
                    (R,q,a),(S,r,b)=events
                    assert (target_sq-target_sum**2/weight)/2 == a*b/(2*(a+b))*(F(rows[R]["G"],q)-F(rows[S]["G"],r))**2
            assert full == complement+A/2-penalty-residual
            assert penalty>=0 and residual>=0
            window_results.append(dict(H=H,Q=Q,h=h,mode=mode,columns=len(columns),
                pair_columns=pair_columns,full=str(full),complement=str(complement),
                A_half=str(A/2),penalty=str(penalty),residual=str(residual)))

    # Independent Bezout parametrization of every minimality-domain collision.
    bezout = []
    for q,r in combinations([p for p in primes if p<=13],2):
        for sign in [-1,1]:
            residue = (sign*pow(r,-1,q))%q
            for R in range(residue,658,q):
                S=(R*r-sign)//q
                if not(56<=R<S<=657 and q*q<R and r*r<S):
                    continue
                if r**3>4*R or S>=2*R:
                    continue
                n=(R*R-1)//(q*q)
                if n==(S*S-1)//(r*r):
                    bezout.append((S,R,q,r,n))
    assert sorted(bezout)==sorted(witness_candidates)
    payload=dict(python=platform.python_version(),limit=limit,
                 signed_roots=len(rows),trial_checks=10000,
                 physical_pairs=physical_pairs,physical_R56_bill=str(physical_bill),
                 smallest_by_max_root=witness,minimality_candidates=len(bezout),
                 weighted_windows=window_results,seconds=time.perf_counter()-start)
    (BASE/"signed.json").write_text(json.dumps(payload,indent=2)+"\n")
    print(json.dumps({k:v for k,v in payload.items() if k!="weighted_windows"},indent=2))
    print("weighted_window_identities",len(window_results))
    print("signed_stream_sha256",hashlib.sha256((BASE/"signed-python.txt").read_bytes()).hexdigest())


if __name__=="__main__":
    main()
```

#### mobius_reference.cpp

```cpp
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

using I = std::int64_t;
using Wide = __int128_t;

std::string decimal(Wide x) {
    if (!x) return "0";
    bool neg=x<0;
    if (neg) x=-x;
    std::string s;
    while(x) { s.insert(s.begin(),char('0'+x%10)); x/=10; }
    return neg ? "-"+s : s;
}

bool prime(int n) {
    if(n<2) return false;
    for(int d=2;d*d<=n;++d) if(n%d==0) return false;
    return true;
}

int main() {
    const int N=1100*1100-1;
    std::vector<int> mu(N+1),M(N+1),V(N+1);
    mu[1]=1;
    // Dirichlet-inverse recursion, independent of factorization or a prime sieve.
    for(int d=1;d<=N;++d)
        for(int n=2*d;n<=N;n+=d) mu[n]-=mu[d];
    for(int n=1;n<=N;++n) {
        if(mu[n]<-1 || mu[n]>1) return 1;
        M[n]=M[n-1]+mu[n];
        V[n]=V[n-1]+mu[n]*mu[n];
    }
    std::ofstream out("signed-cpp.txt");
    for(int R=56;R<=1100;++R) {
        int X=R*R-1;
        std::vector<int> owners;
        I denominator=1;
        for(int q=3;q*q<R;q+=2) if(prime(q)) {
            owners.push_back(q); denominator*=q;
        }
        I G=M[X]-M[R-1],E=0;
        Wide U=0,diag=0;
        for(int q:owners) {
            int Y=X/(q*q);
            E+=I(M[Y])*M[Y];
            U+=Wide(M[Y])*(denominator/q);
            diag+=Wide(V[Y]-V[R-1])*(denominator/q);
        }
        Wide bill=(Wide(G)*G-2*E-(V[X]-V[R-1]))*denominator+2*G*U-2*diag;
        out<<R<<' '<<G<<' '<<E<<' '<<denominator<<' '<<decimal(bill)
           <<' '<<M[X]<<' '<<M[R-1]<<'\n';
    }
    std::cout<<"divisor_recursion_limit="<<N<<" signed_roots=1045\n";
}
```

#### gram_audit.py

```python
"""Post-discovery audits: inverse-stream Gram and literal first-owner cells."""

import json
import math
import time
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, groupby

from geometry import BASE
from signed import mobius_trial, mobius_linear


def audit_gram():
    counts = defaultdict(int)
    outside = []
    max_degree = F(0)
    mu=mobius_linear(1100**2//9)
    prefix=[0]*len(mu)
    for n in range(1,len(mu)):
        prefix[n]=prefix[n-1]+mu[n]
    with (BASE / "inverse-events.txt").open() as stream:
        parsed = (tuple(map(int, line.split())) for line in stream)
        for (H,Q,h), iterator in groupby(parsed, key=lambda x:x[:3]):
            events = list(iterator)
            columns = defaultdict(list)
            for _,_,_,R,q,n,ray in events:
                columns[n].append((R,q,ray))
            if Q**3>4*H:
                for n, group in columns.items():
                    for (R,q,a),(S,r,b) in combinations(group,2):
                        if not a and not b and abs(R*r-S*q)>=2:
                            outside.append(dict(H=H,Q=Q,h=h,n=n,R=R,S=S,q=q,r=r,det=R*r-S*q))
                continue
            counts["doubled_cases"]+=1
            sigma,degree=defaultdict(lambda:F(0)),defaultdict(lambda:F(0))
            offcols={n:group for n,group in columns.items() if not group[0][2]}
            for n,group in offcols.items():
                assert all(not ray for _,_,ray in group)
                assert len(group)<=2
                assert len({R%2 for R,_,_ in group})==len(group)
                for R,q,_ in group:
                    sigma[R]+=F(1,q*q)
                for (R,q,_),(S,r,_) in combinations(group,2):
                    assert abs(R*r-S*q)==1 and math.gcd(R,S)==1
                    assert 8*min(q,r)>5*Q
                    assert Q*abs(R-S)>=2*H-1
                    degree[R]+=F(1,q*r)
                    degree[S]+=F(1,q*r)
                    counts["offray_pair_evaluations"]+=1
            assert max(degree.values(),default=0)<=F(2,Q)
            max_degree=max(max_degree,max(degree.values(),default=0))
            if Q*(h-1)<2*H-1:
                assert all(len(g)==1 for g in offcols.values())
                counts["short_window_injective_cases"]+=1
            if Q**3<=2*H:
                for n,group in columns.items():
                    for (R,q,a),(S,r,b) in combinations(group,2):
                        g=math.gcd(R,S)
                        assert a==b==1 and R//g==q and S//g==r and n==g*g-1
                        counts["SP3_ray_gram_pairs"]+=1
            if H+h-1<=1100:
                for mode in [0,1]:
                    alpha={R:(F(1) if not mode else F(1+(R-H)%5,5)) for R in sigma}
                    U=defaultdict(lambda:F(0))
                    energy=F(0)
                    for n,group in offcols.items():
                        energy+=max(alpha[R] for R,_,_ in group)*prefix[n]**2
                        for R,q,_ in group:
                            U[R]+=F(prefix[n],q)
                    left=sum((alpha[R]*U[R]**2 for R in U),F(0))
                    top=max(sigma.values(),default=F(0))
                    assert left<=min(2*top,top+F(2,Q))*energy
                    counts["genuine_weighted_operator_checks"]+=1
            # Synthetic vectors test the geometric theorem, not Mobius cancellation.
            for mode in [0,1]:
                y={R:(F((-1)**R) if not mode else F(R%7-3,5)) for R in sigma}
                norm=sum((v*v for v in y.values()),F(0))
                lhs=sum((sum((y[R]/q for R,q,_ in group),F(0))**2
                         for group in offcols.values()),F(0))
                diagonal=sum((sigma[R]*y[R]**2 for R in sigma),F(0))
                cross=sum((2*y[R]*y[S]/(q*r) for group in offcols.values()
                           for (R,q,_),(S,r,_) in combinations(group,2)),F(0))
                assert lhs==diagonal+cross
                assert abs(cross)<=F(2,Q)*norm
                assert lhs<=(max(sigma.values(),default=0)+F(2,Q))*norm
                counts["exact_gram_vector_checks"]+=1
    return dict(counts=counts,max_degree=str(max_degree),
                outside_determinant_two=min(outside,key=lambda c:(max(c["R"],c["S"]),c["H"],c["Q"])) if outside else None)


def audit_cells():
    R=56
    X=R*R-1
    primes=[n for n in range(2,X+1) if all(n%d for d in range(2,math.isqrt(n)+1))]
    qs=[q for q in primes if q!=2 and q*q<R]
    denom=math.prod(qs)
    sites=[]
    for n in range(1,X+1):
        mu=mobius_trial(n)
        if mu:
            prefix=mu*sum(denom//q for q in qs if n<=X//(q*q))
            tail=mu*int(R<=n)
            sites.append([n,prefix,tail,()])
    cell_sum=pair_count=nonempty=0
    for p in primes:
        groups=defaultdict(lambda:[0,0,0,0,0,0])
        for n,P,T,sig in sites:
            off=3 if n%p==0 else 0
            groups[sig][off]+=P
            groups[sig][off+1]+=T
            groups[sig][off+2]+=1
        for a,b,c,d,e,f in groups.values():
            cell_sum+=a*e+b*d+denom*b*e
            pair_count+=c*f
            nonempty+=int(c*f>0)
        for site in sites:
            if site[0]%p==0:
                site[3]=site[3]+(p,)
    E=sum(sum(mobius_trial(n) for n in range(1,X//(q*q)+1))**2 for q in qs)
    bill=F(2*cell_sum,denom)-2*E
    expected=json.loads((BASE/"signed.json").read_text())
    assert bill==F(expected["physical_R56_bill"])
    assert pair_count==expected["physical_pairs"]
    return dict(root=R,sites=len(sites),nonempty_cells=nonempty,
                unordered_pairs=pair_count,bill=str(bill))


start=time.perf_counter()
result=dict(gram=audit_gram(),cells=audit_cells())
R,S,q,r=81,127,7,11
assert q*q<R and r*r<S and R%q and S%r and S<2*R
assert (R*R-1)//(q*q)==(S*S-1)//(r*r)==133
assert R*r-S*q==2 and R%2==S%2
result["outside_guard_fixture"]={"R":R,"S":S,"q":q,"r":r,"n":133,"det":2,
    "M_n":sum(mobius_trial(n) for n in range(1,134))}
boundary=[]
for q in [3,5,7,11,13,17,19,23,29,31]:
    assert not q*q<q*q and q*q<q*q+1
    Y=((q*q+1)**2-1)//(q*q)
    assert Y==q*q+2
    boundary.append([q,q*q,q*q+1,Y])
result["strict_boundary_fixtures"]=boundary
result["seconds"]=time.perf_counter()-start
(BASE/"gram-audit.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
```

### Captured Final Gram/Cell Output

```json
{
  "gram": {
    "counts": {
      "doubled_cases": 128,
      "short_window_injective_cases": 65,
      "genuine_weighted_operator_checks": 172,
      "exact_gram_vector_checks": 256,
      "SP3_ray_gram_pairs": 7864,
      "offray_pair_evaluations": 287
    },
    "max_degree": "1/143",
    "outside_determinant_two": null
  },
  "cells": {
    "root": 56,
    "sites": 1910,
    "nonempty_cells": 1909,
    "unordered_pairs": 1823095,
    "bill": "-68464/35"
  },
  "outside_guard_fixture": {
    "R": 81,
    "S": 127,
    "q": 7,
    "r": 11,
    "n": 133,
    "det": 2,
    "M_n": -2
  },
  "strict_boundary_fixtures": [
    [
      3,
      9,
      10,
      11
    ],
    [
      5,
      25,
      26,
      27
    ],
    [
      7,
      49,
      50,
      51
    ],
    [
      11,
      121,
      122,
      123
    ],
    [
      13,
      169,
      170,
      171
    ],
    [
      17,
      289,
      290,
      291
    ],
    [
      19,
      361,
      362,
      363
    ],
    [
      23,
      529,
      530,
      531
    ],
    [
      29,
      841,
      842,
      843
    ],
    [
      31,
      961,
      962,
      963
    ]
  ],
  "seconds": 7.700756647999924
}
```


### Verified Publication Receipt - 20261108-census-1

Verified at 2026-11-08 08:40:30 UTC / 03:40:30 EST.

- Research completion: COMPLETED / DONE; publication of the substantive report succeeded.
- Branch and sole changed path: agent-reports:research/agent_reports/2026-11-08/40-prime-census.md.
- Substantive commit: b5eebf18d6a98591fed9335139e9d39f7ed0eca9.
- Substantive content blob: 5d1a9654d68d8c6862c9bfb4066e1010209d9eea.
- Immutable commit readback: exact match, 68,077 characters. Commit metadata confirms that only the authorized own report changed.
- Substantive report SHA256 before this receipt: 220f617deccffee14153f17e74775d4ea1334008f40fd419901c1f247707c911.
- The early checkpoint remains an exact prefix; this receipt is an append-only follow-up, not a new research invocation.
- New claims remain TC1-TC3 PAPER_PROOF / SELF_AUDIT, TC4 REFUTED, and TC5 FINITE_COMPUTATION. Independent Referee review and new Lean certification remain PENDING; no new global exponent or RH proof is claimed.

This receipt attests the verified preceding substantive commit. The follow-up
receipt commit is checked separately after writing; no self-referential future
commit or unobserved publication is asserted here.


## Scheduled Floor-Two Checkpoint - 20261108-census-2

Execution=PARTIAL / IN_PROGRESS. Trigger: 2026-11-08 11:00:01 EST. RUN_ID_UNAVAILABLE.
Checkpoint: 2026-11-08 16:06:25 UTC. Source main 30c9fade09be0a4cb12776cd324e9fd9a9ed44ac; reports intake e9b83d9687ae3e7585353eda7c910a48d1d91d84.
AGENTS blob 0a99faf8458809ac772d470d704c5433f373bda8; contract d1d6fd558ee23927bd9f70ffdc375bafd1dbb67a.
high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1; chain_ack=CANCELLATION_CHAIN_REUSE_V1;
baseline_ack=PAID_BASELINE_EXACT_CONSUMER_V1; deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1.

Both November 7 and November 8 reports from every role are AVAILABLE. The latest
Wheel HC handoff at 15:46 UTC supplies a new proper-strip question. Existing TC
geometry, now partially merged through #1109, is not rerun. The Coordinator's
prescribed NYMAN fixtures were already executed in Analytic ND; independent review
remains pending and is not claimed completed by this run. The source selector permits
this ready nonduplicate HC follow-up without changing any investigator's coverage.
External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 has no post-Oct-18 entry.

Original Euler kernel, finite-C endpoint, historical envelope and canonical HIGH
sources have been retrieved at current main. #1108 and #1109 are human-merged;
open/draft PR discovery is empty. Baseline #1108 run 42451075330 is successful at
a0c986c0343a56e98b7344268fdc0b74aa885cdb; job 128640229840 was read and its exact
type/terminal standard-axiom checks passed. This is inherited evidence, not a new
build. Use the actual beta growth theorem and total-slot m/4 boundary; a concrete
available fixed power is 7/8-1/(96*explicitSlotCount). No new gain is asserted.

### Frozen Question And Methods


Run: 20261108-census-2, scheduled 2026-11-08 11:00:01 EST.
Source: main 30c9fade09be0a4cb12776cd324e9fd9a9ed44ac.
Purpose: test the j=2 moving-boundary inference in 20261108-wheel-2/HC.

Original definitions: N=R-1, X=R^2-1; genuine Mobius mu;
T(a,b)=floor(X/(ab))-(R+1)floor(N/a)/b.
K>=0 satisfies (M(y)-1)^2<=K(y+1) for every 0<=y<R.
W=floor(R/(4sqrt(K))), B=R-W, I2=[floor(N/3)+1,floor(N/2)].
E2=sum_(a in I2,B<=b<R) mu(a)mu(b)T(a,b).
J2=sum mu(a)mu(b)(floor(X/(ab))-2).
W=0 means empty strip; ordered occurrences, squareful zeros retained.

Competing hypotheses, before execution:
1. The staircase can be erased without changing sign or payment: seek a
   smallest genuine nonzero jump and strict sign reversal.
2. The exact endpoint admits only a single jump, with an explicit
   moving-boundary bilinear form, not an unrestricted multilevel floor.
3. Historical prefix control alone gives a uniform O(R sqrt(K)) strip
   bound even for bounded nonmultiplicative coefficients. This is an
   explicitly synthetic diagnostic, not a statement about genuine mu.
4. A genuine-mu O(R sqrt(K)) strip estimate survives, but needs a new
   boundary estimate beyond the already paid separable term.

Discovery: all R=2..256 and all W=0..floor(R/4); adaptive valid K in
{Kmin,2Kmin,R,R^2,100R^2}; include strict equality boundaries.
Held-out: R in {317,549,1027,2002,4096,8192}; adaptive K values as above.
Literal complete source and all square cross terms: R=2..80 plus 99,317.
Independent algorithm: forward floor enumeration versus inverse hyperbola
row-prefix enumeration, independently trial-factored Mobius values.
All accept/reject comparisons exact integers/rationals; no decimal signs.

Synthetic investigation: derive a bounded-prefix block construction in the
same strip to discriminate envelope-only reasoning. Freeze its formula and
test domain in a dated addendum before executing it; it must not be
substituted for genuine mu or the complete Mertens identity.

Stop: once the minimal genuine falsifier and boundary structure are verified,
do not extend an unchanged census. Do not fit an exponent or universal
constant from a finite maximum. Full complement remains in Q=P+E1+E2+Z.
Unfinished Coordinator NYMAN independent review is not declared completed:
Analytic ND has already executed those prescribed fixtures; this run selects
the newer, nonduplicate HC handoff under the live route selector.


### Complete Return And Permissions

Q_R=P_R+E1_R+E2_R+Z_R and M(R^2-1)=2M(R-1)-Q_R; the complete four-component
square and fixed-cutoff canonical LOW remain present. No bound on Z is assumed.
Only this own report is written remotely. No Lean execution, source change,
other-report edit, branch/PR/workflow/schedule mutation or agent launch.
Verified results, code, precise evidence grades and a continuation capsule follow.


## Floor-Two Boundary Synthesis - 20261108-census-2

This completes the scheduled invocation begun November 8, 2026 at 11:00:01 EST.
The earlier TC report and this invocation's early checkpoint remain unchanged.
Research=COMPLETED; publication is verified in the subsequent receipt.

### A. Most Important Mathematical Discovery

**The adjacent historical floor-two strip has exactly one hyperbolic jump, not a higher-floor cascade. The jump can reverse the genuine signed answer, and historical prefix control by itself cannot pay the original wide strip. A smaller, explicitly admitted strip is nevertheless paid uniformly without new cancellation.**

At the smallest genuine nonzero-jump example, R=6, K=3/2, W=1, the no-jump term is -4/5 while the ORIGINAL strip is +1/5. At R=15,W=1 the reverse sign change occurs: +2/7 becomes -5/7. Thus neither an erased staircase nor a uniform jump-sign assertion survives.

The positive replacement is the paper theorem

```text
16 K W^2 <= R^2 and W^4 <= R^2 K
    ==> |E2(R,W)| <= (61/9) R sqrt(K),
```

for every R>=2 and every actual LowerMertensCriticalEnvelope R K. This bound includes W=0 and is not inferred from a finite maximum. It changes the paid width; the discarded columns are restored to the complement.

A separate family of NON-MOBIUS bounded coefficients satisfies the same shifted historical prefix envelope with K=1 but has E2/R unbounded on the original W=R/4 strip. This refutes only the envelope-only, arbitrary-coefficient extension. It is NOT a counterexample to the actual Mobius strip conjecture, finite-C, Mertens growth, the canonical VF target, or RH.

New evidence: SJ1-SJ4 are PAPER_PROOF / SELF_AUDIT; SJ5 is FINITE_COMPUTATION, with scoped assertions REFUTED by exact witnesses. INDEPENDENT_REVIEW_PENDING; NOT_FORMALIZED. NEW_VERIFIED_ENDPOINT_GAIN=NONE; net_endpoint_gain=NONE; eta_gate=SEARCH_BROAD.

### B. Current Authority And Exact Objective

Pinned main: 30c9fade09be0a4cb12776cd324e9fd9a9ed44ac, retrieved at invocation. AGENTS blob 0a99faf8458809ac772d470d704c5433f373bda8; proof contract d1d6fd558ee23927bd9f70ffdc375bafd1dbb67a. Governing HIGH directive be8168b67584d9d8ebbaa732a30c51509137543e; cancellation-reuse directive 28e2ab47c68bc83b91ae02b6112b94867b021b32.

high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1; chain_ack=CANCELLATION_CHAIN_REUSE_V1; baseline_ack=PAID_BASELINE_EXACT_CONSUMER_V1; deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1. The applicable task selector, seven-role prompts, complete-return contract, persistent-engine, breadth, dynamic, paid-baseline and multifront instructions were retrieved and their applicable provisions inspected.

The canonical theorem remains VFCanonicalSquareVonKochStatement: one constant C>=0 must bound the actual-prime canonical defect by C R log R for every integer R>=2. The original vfCanonical=vfMid+sqrt(2) phase and explicit ClassicalVonKochRHCriterion are unchanged. No claim about that open estimate is made here.

The shared complete signed object is

```text
M(R^2-1)=canonicalLowPrefix_Lambda(R-1)+canonicalHighPrefix_Lambda(R-1),
|canonicalLowPrefix_Lambda(R-1)| <= (floor Lambda+1)R
```

for a fixed Lambda>=0, with absolute birth height and both orientations retained. The ordered Euler strip is a proper piece of a DIFFERENT exact representation, not a new definition of canonical HIGH.

The strongest source-level input remains native_mertens_growth_at_hecke_beta, with its every-positive-loss interpretation. The same-source total-mass theorem supplies the boundary 7/8-m/4 for an admitted fixed source with m=actualSlotMinimum(D)>0. The explicit finite-source instance supplies 7/8-1/(48*explicitSlotCount), and spending half its saving gives the fixed power 7/8-1/(96*explicitSlotCount). Neither upper bound is asserted equal to the unknown true growth boundary. SJ4 below works with ANY applicable fixed b in (1/2,1), retaining its constant and loss spending; the rounded 7/8 example is illustrative only.

PR #1108 is human-merged into 70616fd264e48490f5296a63c79e1ee11ce000b8; #1109 is human-merged into current main. Open/draft PR discovery was empty. The actual #1108 run 42451075330 is completed/success at a0c986c0343a56e98b7344268fdc0b74aa885cdb. Its job 128640229840 was read: exact types and terminal audits, including native_mertens_fixed_explicit_slot_count_total_mass, passed with propext, Classical.choice and Quot.sound only. Comparing that tested head to current main changes only six CORR4-collision implementation/audit files, not the consumed OAI baseline. This is reused exact-head evidence, not a fresh whole-main build or author-created Lean result.

### C. Competing Hypotheses And Selection Discipline

The pre-experiment checkpoint was published and read back at commit 7dd71f8ed80b938a9d290dffc009612f2640b79f, blob 8ff33d211cc91f704203778d2b081707128e60e3. Its frozen domains are preserved above and in the executable appendix.

| Hypothesis | Discriminator | Outcome |
| --- | --- | --- |
| Ignore the floor-two jump without changing the answer or its sign | Genuine ordered-strip reconstruction | REFUTED, R=6 |
| Only one jump level is geometrically possible | Literal endpoint floor minus two | PAPER_PROOF SJ1; exact finite checks agree |
| The same historical envelope alone pays the entire adaptive strip for any bounded coefficients | Same carrier, explicitly nonmultiplicative coefficients | REFUTED at this synthetic/generalized scope by SJ3 |
| A narrower original strip is already paid by existing input and site geometry | Explicit all-K width inequalities | PAPER_PROOF SJ2; exact finite checks agree |
| Actual Mobius wide-strip payment holds uniformly | Original E2 with every valid K | CONJECTURE remains unresolved; finite survival is not proof |

The newer Wheel HC handoff was selected instead of replaying the already verified TC collision census. Coordinator's NYMAN fixture request is not reported completed by this run: Analytic ND has already executed those fixtures, and independent review remains available. No investigator coverage clock was reset.

The safe-width lemma was derived at implementation stage after the original checkpoint, before test outputs were inspected; it was present in the first program. The synthetic family and m values were recorded locally before their execution. The R=8 strict-equality audit and native-power corollary were disclosed post-discovery follow-ups, not held-out predictions. No constant was tuned to observed extrema.

### D. Original Carrier And Full Return

For R>=2 put N=R-1, X=R^2-1, and retain the genuine integer Mobius function, including mu(1)=1 and squareful zeros. The exact rational source inspected in main is

```text
T_R(a,b)=floor(X/(ab))-(R+1)floor(N/a)/b,
Q_R=sum_(1<=a,b<R) mu(a)mu(b)floor(X/(ab)),
P_R=(R+1)sum_(1<=b<R)mu(b)/b.
```

An occurrence is the ORDERED pair (a,b). Equal products are not deduplicated. The historical condition is K>=0 and (M(y)-1)^2<=K(y+1) for EVERY 0<=y<R; y=0 forces K>=1. Experimental K_min is the maximum of those ratios, not an identification with another empirical normalization.

For an integer 0<=W<=R/4, let B=R-W, lo=floor(N/3)+1=ceil(R/3), hi=floor(N/2), I2=[lo,hi], and

```text
m2=M(hi)-M(lo-1),
t_B=sum_(B<=b<R)mu(b)(1-(R+1)/b),
E2=sum_(a in I2,B<=b<R)mu(a)mu(b)T_R(a,b),
J2=sum_(a in I2,B<=b<R,3ab<=X)mu(a)mu(b).
E2=2*m2*t_B+J2.
```

Empty intervals have zero sum. The original wide width is W_K=floor(R/(4sqrt K)). No logarithms or nonrational signs enter the computation: for rational K=p/q, W_K=isqrt(floor(R^2*q/(16p))).

Let E1 be Wheel HC's disjoint floor-one rectangle at the chosen width, and let Z be the original T sum over all other ordered pairs. Recombine BEFORE any norm:

```text
Q=P+E1+E2+Z,
Q^2=P^2+E1^2+E2^2+Z^2
    +2PE1+2PE2+2PZ+2E1E2+2E1Z+2E2Z,
M(X)=2M(N)-Q.
```

The complete source and all six cross interactions were independently enumerated in the finite full-return checks. No original #915 NNS denominator, conductor source or Hecke phase was substituted. Their extra source terms are not applicable to this Euler representation. No energy/window gain is asserted, so a full-window average is not passed off as h=1 control.

### E. Executed Results And Independent Checks

| Check | Exact scope/result |
| --- | --- |
| Genuine strip cases | 10,991 evaluations, including all R=2..256, all W=0..floor(R/4), and adaptive tests |
| Literal floor sites | 5,649,735 evaluations; 3,340 strict-equality evaluations, with overlaps between tested strips retained |
| Adaptive K cases | 1,304; K in {K_min,2K_min,R,R^2,100R^2}, duplicates removed |
| Safe-width cases | 1,304; exact squared 61/9 inequality and site-count inequality passed |
| Held-out R | 317,549,1027,2002,4096,8192, fixed before execution |
| Independent arithmetic | Trial-factor mu for every n=1..8192, inverse row geometry versus forward columns/literal floors; all 10,991 exact outputs agree |
| Complete source | 81 roots: R=2..80,99,317; 276,940 ordered sites; every partition and full square agrees exactly |
| Synthetic cross-check | Five m values; Python inverse 4,793,344 rows versus C++ forward 14,380,032 columns; every integer agrees |

The canonical exact record-stream SHA-256 is 233e3098d9ad71de4e4e7f572db97e4d6a9fc673e4012af8eac1864738a941ca in BOTH genuine implementations. The main mu sieve reaches 100,488 solely for the full endpoint checks. The independent trial implementation does not share the sieve or its intermediate table. The full-source identity at the 81 roots is checked directly against the separately summed genuine M(X), not by defining the complement as a difference.

All held-out minimal envelopes equal 3/2. Compact certified integer enclosures of E2 at the ORIGINAL width are:

| R | W_K | J2 | E2 |
| --- | --- | --- | --- |
| 317 | 64 | -4 | -3<E2<-2 |
| 549 | 112 | 13 | 11<E2<12 |
| 1027 | 209 | -1 | -7<E2<-6 |
| 2002 | 408 | 22 | 36<E2<37 |
| 4096 | 836 | 263 | E2=263 exactly |
| 8192 | 1672 | 181 | 199<E2<200 |

The largest sampled E2^2/(R^2 K) in the ORIGINAL adaptive corpus is 3/200 at R=40,K=3/2,W=8,E2=J2=6. This is a finite diagnostic only. It is not an optimal constant, an asymptotic estimate or evidence that all K and R have been covered. At R=4096 the separable term is zero and the entire strip is the jump J2=263, so erasing the jump cannot be justified even by a small measured separable part.

### F. Exact Falsifiers And Boundary Cases

**Smallest genuine jump/sign reversal in increasing R, then W.** R=6, K=3/2 gives W=1, I2={2}, B=5. The only nonzero site is (2,5), mu(2)mu(5)=1. X=35 gives floor(35/10)=3 and floor(5/2)=2. Thus T=3-14/5=1/5, while replacing the endpoint floor by two gives -4/5. The tested R<6 strips have J2=0. The full historical envelope is checked at every y=0..5, not merely its endpoint.

**Opposite sign.** R=15,W=1 has J2=-1, separable term 2/7, E2=-5/7. It is an admitted adaptive width for K=9, which is larger than the actual K_min=3/2. Thus positivity of the geometric indicator does not impose positivity of the signed jump.

**Equality must be included.** The first nonzero coefficient at 3ab=X is R=8,a=3,b=7. Here X=63, mu(3)mu(7)=1, K_min=3/2, W=1; T=3/7. Replacing <= by < loses the jump and gives -4/7. This is inside the original width/source hypotheses.

**Full original return at R=6.** The four components are

```text
P=-7/30, E1=-2/5, E2=1/5, Z=-77/30, Q=-3,
sum of all six doubled cross terms = 971/450.
```

Their sum is -3 and their full square is 9. No favorable local sign is used to pay Z.

### G. Single-Jump Geometry And Boundary Variable: SJ1

**20261108-census-2/SJ1, PAPER_PROOF.** For every R>=2, 0<=4W<=R and every site in I2 x [R-W,R),

```text
floor(N/a)=2,
floor(X/(ab))=2+1_(3ab<=X).
```

Proof: a<=N/2 and b<=N imply 2ab<=N^2<X, so the endpoint floor is at least two. The exact lower row endpoint gives a>=R/3, while b>=3R/4; hence 4ab>=R^2>X. The endpoint floor is therefore less than four. Equality at 3ab=X belongs to the upper value. This uses the original -1 horizon; no limiting or continuous replacement is made.

The complete staircase is independently represented in both directions:

```text
J2=sum_(B<=b<R)mu(b)[M(max(lo-1,min(hi,floor(X/(3b)))))-M(lo-1)]
  =sum_(lo<=a<=hi)mu(a)[M(max(B-1,min(N,floor(X/(3a)))))-M(B-1)].
```

These are exact identities, not quantitative cancellation. In adjacent b columns the unclipped quotient decreases by at most one, because X/[3b(b+1)]<1. Thus the difficult variable is the actual signed prefix sampled along one moving hyperbolic boundary, not an unbounded floor-jump multiplicity. No new higher-floor investigation is needed on this particular strip. Other historical floor classes are not covered.

### H. Paid Narrow Strip And Native Component: SJ2 And SJ4

Let A2 count ALL jump sites, including those with zero Mobius coefficient. Write b=R-d, 1<=d<=W. The number of a in a given column is at most

```text
X/[3(R-d)]-R/3+1 <= 4d/9+1.
```

Consequently

```text
|J2| <= A2 <= (2W^2+11W)/9 <= (13/9)W^2  (W>=1).  (SJ2a)
```

The first displayed count inequality also holds at W=0. This is an all-scale integer-lattice bound; it neither assumes independence nor estimates signed pairs by a new conjecture.

Under the genuine historical K envelope, interval differences have size at most 2sqrt(KR). Abel summation with decreasing weight (R+1-b)/b gives

```text
|2*m2*t_B| <= 8KR(W+1)/(R-W).
```

For 1<=W<=R/(4sqrt K), use W+1<=2W and R-W>=3R/4 to bound this by (16/3)R sqrt K. If in addition W^4<=R^2 K, then W^2<=R sqrt K, so SJ2a proves

```text
|E2| <= (16/3+13/9)R sqrt K = (61/9)R sqrt K.        (SJ2)
```

The W=0 case is immediate. Define W_safe as the largest nonnegative integer satisfying 16KW^2<=R^2 and W^4<=R^2K. It automatically obeys 4W<=R since K>=1. For rational K=p/q the implementation uses the minimum of isqrt(floor(R^2q/(16p))) and isqrt(isqrt(floor(R^2p/q))). All rounding is exact. The complete original wider strip is E2(W_K)=E2(W_safe)+the signed omitted-column strip; the latter has NOT been paid by this proof.

**20261108-census-2/SJ4, PAPER_PROOF, post-discovery native-power consumer.** Suppose an already licensed fixed bound |M(n)|<=C_b*n^b holds for every n>=1, with 1/2<b<1. The same interval/Abel proof gives

```text
|E2(R,W)| <= 8 C_b^2 R^(2b)(W+1)/(R-W)+(13/9)W^2.
```

Set theta=(3b-1)/2 and W=floor(R^theta). For R>=max(2,4^(1/(1-theta))), W<=R/4 and W+1<=2R^theta. Since

```text
2b+theta-1 <= 2theta=3b-1 < 2b,
```

the ORIGINAL strip satisfies

```text
|E2| <= ((64/3)C_b^2+13/9) R^(3b-1).                (SJ4)
```

This is a proper-component saving of 1-b in the root exponent relative to R^(2b), with all constants and threshold depending on the supplied fixed b,C_b. At the illustrative b=7/8 the exponent is 13/8, not 7/4. Use the stronger actual fixed b when applying it. No uniform statement as b tends to one or no-loss statement at the true beta is asserted. The finite rational exponent audit checks algebra only; the displayed proof, not that grid, supplies the universal corollary.

### I. Envelope-Only Extension Fails: SJ3

**20261108-census-2/SJ3, PAPER_PROOF.** The assertion that the original W_K strip is O(Rsqrt K) for EVERY bounded coefficient sequence satisfying the shifted historical envelope is false. The following coefficients are explicitly synthetic and NOT multiplicative.

For any positive multiple m of eight set

```text
R=192m^4, K=1, W=R/4, a0=R/3, h=8m^2, L=2m^3.
```

Let f(1)=1. On a=a0+x, 1<=x<=L, set f(a)=+1 for (x-1) mod 2h<h, and -1 otherwise. On b=R-d, 1<=d<=3L, put x=floor((d-1)/3) and set f(b)=+1 for h/2<=x mod 2h<3h/2, and -1 otherwise. Set f=0 elsewhere. The two support intervals are disjoint, wholly inside I2 and [B,R), respectively. L is a multiple of 2h, so each support sums to zero.

Let S_f(y)=sum_(n<=y)f(n). Before the row support S_f-1=0; within it the prefix has absolute value at most h, and h^2=a0. After it the prefix returns to zero. In the column support, read in increasing b, the absolute prefix is at most 3h/2, and (3h/2)^2=144m^4<=R-3L+1. All zero gaps preserve those inequalities; y=0 has (S_f(0)-1)^2=1. Thus

```text
|f(n)|<=1, (S_f(y)-1)^2<=y+1 for EVERY 0<=y<R.
```

This proves the full K=1 envelope, not a finite sample of its nonzero locations.

Let F(u) be the row prefix: on 0<=u<=L it is the triangular function min(r,2h-r), r=u mod 2h, and it is zero outside. F is 1-Lipschitz on the integers. At b=R-d the exact row cutoff is

```text
c(d)=floor((R*d-1)/(3*(R-d))).
```

Writing x=floor((d-1)/3), one has 0<=c(d)-x<=1+d^2/[3(R-d)]<=h/32 for all 1<=d<=3L and m>=8. For the last inequality, the right side is at most 1+2m^3/(32m-1)<=1+2m^2/31<=m^2/4=h/32. The first inequality follows by substituting d=3x+u, 1<=u<=3; the numerator remainder is nonnegative. This also handles the upper support boundary because F extends by zero.

Over a complete 2h cycle, summing the stated column signs against F(x) gives h^2/2. Each x occurs three times, so the linear-boundary value is J0=3Lh/4. Lipschitz control gives

```text
|J_f-J0| <= 3Lh/32,
J_f >= (21/32)Lh = (21/2)m^5,
J_f/R >= 7m/128 -> infinity.
```

Since the row sum is zero, the separable term vanishes EXACTLY and E2_f=J_f. This proves failure of every universal constant for the envelope-only extension. It does not use, or assert for f, the genuine Mobius convolution identity Q=2M(N)-M(X).

Executed independent certificates:

| m | R | Exact J_f=E2_f | Linear J0 |
| --- | --- | --- | --- |
| 8 | 786432 | 394652 | 393216 |
| 16 | 12582912 | 12606532 | 12582912 |
| 32 | 201326592 | 403025357 | 402653184 |
| 64 | 3221225472 | 12890559217 | 12884901888 |
| 128 | 51539607552 | 412397376316 | 412316860416 |

The final finite example exceeds (16/3)R and also (61/9)R at the ORIGINAL wide width, but it violates SJ2's extra W^4<=R^2K condition and is not a counterexample to SJ2. The sequence has f(2)=0 whereas mu(2)=-1. The model destroys arithmetic multiplicativity by design. Its purpose is to show that the historical envelope, bounded entries and genuine strip geometry alone do not force the desired wider estimate; additional genuine-Mobius structure remains eligible.

### J. Complete Budget And First Unpaid Step

The actual consumer is EulerSelfDualFiniteCStatement and its certified conditional square-root amplification/Mertens-energy chain. We do not assume that statement or the full residual. In canonical coordinates, the exact return is

```text
HIGH_Lambda(R-1)=2M(N)-P-E1-E2-Z-LOW_Lambda(R-1).
```

For SJ4's mesoscopic width, Wheel's same historical/Abel proof also bounds E1 by O_b(R^(2b+theta-1)); SJ4 bounds E2 by O_b(R^(3b-1)). The O(R) canonical LOW, the O(R) linear P and the O(R^b) history are retained. At the supplied global boundary the COMPLETE Z still has only the incoming O_b(R^(2b)) control obtained from the full source identity. The worst exponent remains 2b. No subtraction of upper bounds gives a signed saving for Z.

The smaller next question is the GENUINE signed boundary J2 at the ORIGINAL W_K, retaining all valid K. Equivalently on this proper strip, a uniform |E2|<=C2 R sqrt K holds iff |J2|<=CJ R sqrt K, with constants changed by at most 16/3. This follows from the already paid separable term. This equivalence is a local reduction, NOT a proof of its premises and NOT a demonstrated equivalence to finite-C. Even its proof would leave all other historical row classes and b<B columns.

For a practical continuation, isolate the actual omitted-column boundary J2(W_K)-J2(W_safe), preserving its Mobius coefficients and the constant-floor correction. Test a multiplicative/factor-incidence restriction on that original boundary. Do not ask for an arbitrary-vector theorem now refuted by SJ3; do not promote a missing bound to an assumption. Moving to a new hypothetical coefficient model cannot refute the genuine conjecture.

Compact HIGH record: route FINITE-AC; input LowerMertensCriticalEnvelope and any already certified fixed native Mertens power; exact source original ordered rank-one Euler kernel; changed step retain and count the unique floor-two boundary; new payment SJ2/SJ4 on explicitly reduced widths; return P/E1/E2/Z and all mixed terms; first unpaid estimate actual wider boundary then complete complement; global gain NONE.

### K. Falsification, Precision And Novelty Audit

All original coefficients, cutoffs, signs, occurrence multiplicities, reciprocal weights and squares use exact integers or rational arithmetic. No transcendental evaluation, probabilistic primality, random seed, floating sign or fitted exponent is used. Python arbitrary-precision integers and Fraction handle the genuine source. The C++ synthetic cross-check uses __int128 for products; all accumulators fit signed 64-bit in the declared finite test range. The paper family uses unbounded integers, not a claim that this machine program can run every m.

Python forward/literal reconstruction and trial-factor inverse reconstruction agree exactly. The synthetic Python inverse row calculation and separate C++ forward column calculation agree exactly. These are DIFFERENT_IMPLEMENTATIONS / SELF_AUDIT within this invocation, not independent Referee acceptance. No mathematical assertion failed in the first executions; the later audit adds disclosed equality and exponent checks without changing earlier test domains or constants.

The scoped novelty check inspected the original fractional/rank-one source, finite-C bridge and endpoint, asymmetric-corner report, one-sided Abel audit, uniform completed-coefficient source, and the relevant two-day reports. The previous asymmetric corner is a postroot region, not this historical floor-two strip. General Abel summation, triangular block controls and hyperbola identities are elementary; no worldwide novelty claim is made. The useful new content is the exact j=2 source restriction, its admissible reduced-width payment, and the explicit scope of the failed envelope-only extension. This is not a rerun of the known arbitrary-prefix MU-LIFT countermodel or the paid CORR4 sampling census.

### L. Continuity And Specialist Handoffs

Intake agent-reports HEAD e9b83d9687ae3e7585353eda7c910a48d1d91d84 contained BOTH November 7 and November 8 reports for all seven roles. TODAY=AVAILABLE for every role; relevant November 7 evidence is YESTERDAY=CARRY_FORWARD, not presumed rerun. The Coordinator AM/PM directory blobs match on each date, so each pair is one substantive source. External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 has no entry newer than October 18; q=R, genuine-prime, historical-anchor and original-denominator safeguards remain at their original scopes.

Relevant continuity: Coordinator WS/SB complete-return questions remain qualified; Owner SG/RS/JT and today's PD/MC distinguish paid proper terms from complete complements; Analytic GL/FT/BC and MP/ND retain genuine sources and full-tail costs; Wheel DI/LR/OC and SP/HC supply the selected continuation; own SC/RC/TC need no unchanged rerun. Today's Referee DR accepts SP/TC only at stated geometric/identity scopes. Lean CC implements selected collision declarations, not their complete signed bills. As-published receipts read include today's Coordinator 12:38:31Z, Owner MC 13:30:29Z, Analytic ND 14:29:53Z and Wheel HC 15:46:20Z; historical unmerged wording is superseded by the live PR reads, not silently retained as current status.

- Proof Architect: HC's next j=2 source has only one jump. SJ2/SJ4 pay precise subregions from existing inputs. The actual wide-strip conjecture survives; the whole complement and eta remain open. Keep the independent routes.
- Finite Wheel: no higher jump levels occur under 4W<=R and the literal endpoints. Resume from the single boundary, not a multilevel census. The synthetic failure forbids an envelope-only all-coefficient extension, not your genuine conjecture. Your next protected MU-LIFT turn is unaffected.
- Analytic: a stronger arbitrary-vector hyperbola estimate is not a necessary prerequisite. Seek genuine arithmetic structure only on the unpaid boundary if pursuing this route. The fixed-b SJ4 payment already uses the available native input; do not recount it as a global power gain.
- Owner: the R=6 and R=15 sign reversals are original Euler-strip facts, not an identification with your prime-error allocation. All complements and phase terms remain separate.
- Referee: independently audit SJ1 endpoint inequalities, the all-K SJ2 width and area estimate, SJ3's entire historical envelope and synthetic scope, and SJ4's actual fixed-power threshold. Author self-audit is not acceptance.
- Lean: after independent acceptance and only with a useful active consumer, SJ1 and SJ2 are two possible small implementation units. Do not formalize the unproved full-strip bound as an assumed endpoint theorem. No new PR, workflow or launch was requested or performed here.

### M. Ranked Experimental Hypothesis Portfolio

| Rank | Hypothesis and evidence | Missing ingredient / decisive next test | Disposition |
| --- | --- | --- | --- |
| 1 | Genuine wide-strip absolute J2 <= C R sqrt K; all finite tests survive, but no proof | A source-specific restriction on the omitted hyperbolic boundary; test factor-preserving classes with full recombination | Continue as a precise CONJECTURE |
| 2 | Narrowed strip needs new primitive cancellation: SJ2/SJ4 already pay it on paper | Independent review, then consume at exact width; no larger unchanged scan | Reject that prerequisite; retain the payment |
| 3 | Envelope-only arbitrary-coefficient wide-strip theorem: SJ3 gives unbounded E2_f/R with K=1 | No more scaling needed; any repair must use additional hypotheses | REFUTED at synthetic scope |
| 4 | Current NYMAN correction and OAI marked/kappa consumers: upstream ND/BC/SB provide distinct pending claims | Independent full-source review, no duplication of executed fixtures | Preserve independent alternatives |

### N. Resume Capsule And Execution Limits

RUN=20261108-census-2, scheduled 11:00:01 EST; RUN_ID_UNAVAILABLE.
MAIN=30c9fade09be0a4cb12776cd324e9fd9a9ed44ac.
NEW=single exact j=2 jump; genuine sign reversal R=6; <= boundary witness R=8;
uniform narrower-width (61/9) payment; native proper-strip R^(3b-1) payment;
explicit non-Mobius envelope-only obstruction with unbounded normalized strip.
FINITE=10991 matched original strips, 81 full source/square returns, five exact
Python/C++ synthetic certificates. NO_NEW_LEAN; INDEPENDENT_REVIEW_PENDING.
NEXT=original wide-strip omitted boundary with multiplicativity retained;
do not rerun unchanged HC/TC tables or infer an all-scale bound from finite ratios.
FULL RETURN=all four scalar parts and ten square terms retained; canonical
LOW and final unfinished-square O(R) allowance are inherited, not newly improved.
GLOBAL=canonical VF/RH and improved complete HIGH remain open.

Execution used Python 3.12.14 and g++ 13.3.0 (observed versions, rather than the environment's representative version). Compilation flags: -O2 -std=c++17 -Wall -Wextra -Werror. Measured principal runs: original probe 4.423234409 s, trial/inverse check 0.470899965 s, synthetic inverse 3.423026528 s; the captured comparison's C++ run took 0.145267501 s. These timings are diagnostics, not claims about other machines. All command sessions completed. No local Lean or unrequested remote write occurred. Scratch artifacts are not separate authorized repository commits.

The appendices preserve all executed source, frozen registration, exact key outputs and input hashes. Raw multi-thousand-digit fractions are reproducibly generated by the scripts; compact table enclosures were obtained by integer floor/ceiling, not rounded floating point. Publication is claimed only in the verified receipt.


### Immutable Source Ledger

All main paths below were fetched at 30c9fade09be0a4cb12776cd324e9fd9a9ed44ac; every fetched blob matches the observed recursive main tree.

| Path | Blob SHA |
| --- | --- |
| AGENTS.md | 0a99faf8458809ac772d470d704c5433f373bda8 |
| CURRENT_PROOF_CONTRACT.md | d1d6fd558ee23927bd9f70ffdc375bafd1dbb67a |
| docs/RHLEAN_COMPLETE_SIGNED_HIGH_ATTACK_20261107.md | be8168b67584d9d8ebbaa732a30c51509137543e |
| docs/RHLEAN_REUSE_CANCELLATION_CHAIN_20261107.md | 28e2ab47c68bc83b91ae02b6112b94867b021b32 |
| research/EULER_RANK_ONE_FRACTIONAL_ROWS_20261027.lean | e482711a3f55c1f59fc771f108671477f51732f2 |
| research/EULER_FRACTIONAL_COUPLED_20261027.lean | e6c4b1690e497760d366e36b28a1f7aa60e19f85 |
| research/EULER_SELF_DUAL_FINITE_C_BRIDGE_20261027.lean | e97561ef330a9996fd807d8910369f0698147b01 |
| research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean | e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73 |
| RHLean/Proof/SquareRootLegalAncestryGramReduction.lean | 1270d4d91c53b50b110d10014f223f427fb7a575 |
| research/oai_434/VF919ExplicitSlotTotalMass.lean | 71c5b7b5b8032ca3558467126fdf97d3caf1a7df |
| RHLean/Analysis/CanonicalHighSectorCore.lean | dd02fc8fabfe4004c6b0d50374b3b8752607b168 |
| RHLean/Analysis/CanonicalLowOccupancy.lean | b958da340d107cdd00015d2827b9a728357b4d8e |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |

### Two-Day Report Ledger

These are the intake bytes, before this run's own append.

| Role file | November 7 blob | November 8 blob |
| --- | --- | --- |
| 00-coordinator-am.md | 00a649b70f851ca193e74e5004d0d3390cf9ca18 | b6d5c65aed0537efd0018e11dbcd9a72dea3c15a |
| 10-owner-payment.md | 933e8eb23e669594cc687059d75147e6267eec8d | dc8da662cdafc4bc96bcc3ccb29c3052eb1b4d99 |
| 20-analytic-type-ii.md | 77f3e5795533041e4356ceb94cb66328da7af27c | 707aea15cc8e09f16cccf874c876bb04ede9ef14 |
| 30-finite-wheel.md | 7739fa5d4cc77f35773b0d4149b2ddd21732a70d | 45e789c59f9165dbdf9dae352d7438dc468e9e70 |
| 40-prime-census.md | 3fae830e34c590d32c31ad77cad3ace833eb3ff5 | 3cc1bbe7e0d9a80bdcaa630a2fb3c31d4b8f90c8 |
| 50-adversarial-referee.md | 426c2abfa5b8926b512e07f05be37692a2416d0b | 9b691e84eeb8f2f9e2497604dc874935a61d5005 |
| 60-lean-verification.md | ec14e2803af8c1e56123682ee61ed927ed4f9450 | 02647045bf731a52b3c726c9ea690b72fa48c274 |

### Reproduction Commands

The files below are embedded in full so this own-report-only publication is self-contained. Their original scratch location was /workspace. No separate repository script commit was made.

```sh
python /workspace/staircase_probe.py
python /workspace/staircase_reference.py
python /workspace/staircase_synthetic.py
g++ -O2 -std=c++17 -Wall -Wextra -Werror /workspace/staircase_synthetic_reference.cpp -o /workspace/staircase-synthetic-reference
/workspace/staircase-synthetic-reference
python /workspace/staircase_audit.py
```

### Executed File Hashes

```text
77019a10b83d3c4c5d70dce66cb8def162569f5020d90f5f5d81d2558e4e1fd7  /workspace/staircase_probe.py
dafd9eae27a64bf1edda1035c30e626df70333bde5f584ed9e699e49e4b3b3ec  /workspace/staircase_reference.py
5a9290bf28dcf9bcb4bc58394ebd62f6c453488c7505597d5151441cb3a84831  /workspace/staircase_synthetic.py
5a95cef099ad73262f1d87eeee00c8743756fdaca8312d83859d3201ccf69353  /workspace/staircase_synthetic_reference.cpp
3385c4accb815e01924621168fdcdb68bd9d83de46d113784875f7ead3de1a6f  /workspace/staircase_audit.py
a0b02ebaa2cc9b46739bab1d20483add77d42926fc136e92102f5d762397b43b  /workspace/staircase-registration.md
edec7cac486559e752d7bcb2755d028f3817b9c9f6557f593c4a176e4736e5f2  /workspace/staircase-synthetic-registration.md
```

### Compact Captured Results

The first object omits only the bulky exact fractions and full-return fixtures already summarized above; those are regenerated in staircase-results.json. The other objects preserve the corresponding captured structured outputs.

#### Original probe

```json
{
  "status": "PASS",
  "python": "3.12.14",
  "counts": {
    "strip_cases": 10991,
    "literal_sites": 5649735,
    "strict_equalities": 3340,
    "adaptive_checks": 1304,
    "safe_width_checks": 1304,
    "complete_ordered_sites": 276940,
    "complete_returns": 81
  },
  "first_jump": {
    "R": 6,
    "W": 1,
    "J": 1,
    "E": "1/5",
    "base": "-4/5",
    "area": 1
  },
  "first_sign_reversal": {
    "R": 6,
    "W": 1,
    "J": 1,
    "E": "1/5",
    "base": "-4/5",
    "area": 1
  },
  "first_negative_jump": {
    "R": 15,
    "W": 1,
    "J": -1,
    "E": "-5/7",
    "base": "2/7",
    "area": 1
  },
  "maximum_sampled_ratio_squared": "3/200",
  "maximum_sampled_ratio_fixture": {
    "R": 40,
    "W": 8,
    "J": 6,
    "E": "6",
    "base": "0",
    "area": 13,
    "K": "3/2"
  },
  "record_sha256": "233e3098d9ad71de4e4e7f572db97e4d6a9fc673e4012af8eac1864738a941ca",
  "elapsed_seconds": 4.423234409000088
}
```

#### Independent inverse

```json
{
  "status": "PASS",
  "independent_trial_mu": 8192,
  "inverse_cases": 10991,
  "records_sha256": "233e3098d9ad71de4e4e7f572db97e4d6a9fc673e4012af8eac1864738a941ca",
  "elapsed_seconds": 0.4708999650000578
}
```

#### Synthetic control

```json
{
  "status": "PASS",
  "scope": "SYNTHETIC_NOT_MOBIUS",
  "results": [
    {
      "m": 8,
      "R": 786432,
      "h": 512,
      "L": 1024,
      "K": 1,
      "W": 196608,
      "J": 394652,
      "linear_J": 393216,
      "error": 1436,
      "violates_16_over_3": false
    },
    {
      "m": 16,
      "R": 12582912,
      "h": 2048,
      "L": 8192,
      "K": 1,
      "W": 3145728,
      "J": 12606532,
      "linear_J": 12582912,
      "error": 23620,
      "violates_16_over_3": false
    },
    {
      "m": 32,
      "R": 201326592,
      "h": 8192,
      "L": 65536,
      "K": 1,
      "W": 50331648,
      "J": 403025357,
      "linear_J": 402653184,
      "error": 372173,
      "violates_16_over_3": false
    },
    {
      "m": 64,
      "R": 3221225472,
      "h": 32768,
      "L": 524288,
      "K": 1,
      "W": 805306368,
      "J": 12890559217,
      "linear_J": 12884901888,
      "error": 5657329,
      "violates_16_over_3": false
    },
    {
      "m": 128,
      "R": 51539607552,
      "h": 131072,
      "L": 4194304,
      "K": 1,
      "W": 12884901888,
      "J": 412397376316,
      "linear_J": 412316860416,
      "error": 80515900,
      "violates_16_over_3": true
    }
  ],
  "elapsed_seconds": 3.4230265280000367
}
```

#### Post-discovery audit

```json
{
  "status": "PASS",
  "first_nonzero_equality": {
    "R": 8,
    "a": 3,
    "b": 7,
    "coefficient": 1
  },
  "synthetic_exact_matches": 5,
  "cpp_elapsed_seconds": 0.10656696299997748,
  "cpp_forward_columns": 14380032,
  "python_inverse_rows": 4793344,
  "native_component_budget": [
    {
      "b": "3/5",
      "theta": "2/5",
      "component": "4/5",
      "saving": "2/5"
    },
    {
      "b": "3/4",
      "theta": "5/8",
      "component": "5/4",
      "saving": "1/4"
    },
    {
      "b": "5/6",
      "theta": "3/4",
      "component": "3/2",
      "saving": "1/6"
    },
    {
      "b": "7/8",
      "theta": "13/16",
      "component": "13/8",
      "saving": "1/8"
    },
    {
      "b": "9/10",
      "theta": "17/20",
      "component": "17/10",
      "saving": "1/10"
    }
  ],
  "held_out_integer_enclosures": [
    {
      "R": 317,
      "safe": false,
      "W": 64,
      "J": -4,
      "E_floor": -3,
      "E_ceil": -2
    },
    {
      "R": 317,
      "safe": true,
      "W": 19,
      "J": -6,
      "E_floor": -8,
      "E_ceil": -7
    },
    {
      "R": 549,
      "safe": false,
      "W": 112,
      "J": 13,
      "E_floor": 11,
      "E_ceil": 12
    },
    {
      "R": 549,
      "safe": true,
      "W": 25,
      "J": 7,
      "E_floor": 6,
      "E_ceil": 7
    },
    {
      "R": 1027,
      "safe": false,
      "W": 209,
      "J": -1,
      "E_floor": -7,
      "E_ceil": -6
    },
    {
      "R": 1027,
      "safe": true,
      "W": 35,
      "J": -2,
      "E_floor": -3,
      "E_ceil": -2
    },
    {
      "R": 2002,
      "safe": false,
      "W": 408,
      "J": 22,
      "E_floor": 36,
      "E_ceil": 37
    },
    {
      "R": 2002,
      "safe": true,
      "W": 49,
      "J": 2,
      "E_floor": -1,
      "E_ceil": 0
    },
    {
      "R": 4096,
      "safe": false,
      "W": 836,
      "J": 263,
      "E_floor": 263,
      "E_ceil": 263
    },
    {
      "R": 4096,
      "safe": true,
      "W": 70,
      "J": 6,
      "E_floor": 6,
      "E_ceil": 6
    },
    {
      "R": 8192,
      "safe": false,
      "W": 1672,
      "J": 181,
      "E_floor": 199,
      "E_ceil": 200
    },
    {
      "R": 8192,
      "safe": true,
      "W": 100,
      "J": -3,
      "E_floor": -3,
      "E_ceil": -2
    }
  ]
}
```

#### Executed Artifact: staircase_probe.py

~~~python
"""Exact genuine-Mobius floor-two census; no inferred infinite bound."""

from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import accumulate
from math import isqrt
from pathlib import Path
import json
import platform
import time


def mobius(limit):
    primes, mu, least = [], [0] * (limit + 1), [0] * (limit + 1)
    mu[1] = 1
    for n in range(2, limit + 1):
        if not least[n]:
            least[n] = n
            primes.append(n)
            mu[n] = -1
        for p in primes:
            if p * n > limit:
                break
            least[p * n] = p
            if n % p == 0:
                break
            mu[p * n] = -mu[n]
    return mu


def width(r, k):
    return isqrt(r * r * k.denominator // (16 * k.numerator))


def safe_width(r, k):
    return min(width(r, k), isqrt(isqrt(r * r * k.numerator // k.denominator)))


def main():
    start = time.perf_counter()
    mu = mobius(317 * 317 - 1)
    mertens = list(accumulate(mu))
    kmins, k = {}, F(0)
    for r in range(1, 8193):
        k = max(k, F((mertens[r - 1] - 1) ** 2, r))
        kmins[r] = k
    counts, records, fixtures = Counter(), [], {}
    first_jump = first_reversal = first_negative = None
    max_ratio_sq = (F(-1), None)

    def evaluate(r, w, literal):
        nonlocal first_jump, first_reversal, first_negative, max_ratio_sq
        n, x, b0 = r - 1, r * r - 1, r - w
        lo, hi = n // 3 + 1, n // 2
        m = mertens[hi] - mertens[lo - 1] if lo <= hi else 0
        t = sum((mu[b] * (1 - F(r + 1, b)) for b in range(b0, r)), F(0))
        if literal:
            j = floor_sum = area = 0
            for a in range(lo, hi + 1):
                assert n // a == 2
                for b in range(b0, r):
                    delta = x // (a * b) - 2
                    assert delta == int(3 * a * b <= x)
                    counts['literal_sites'] += 1
                    counts['strict_equalities'] += int(3 * a * b == x)
                    j += mu[a] * mu[b] * delta
                    floor_sum += mu[a] * mu[b] * (x // (a * b))
                    area += delta
            reciprocal = sum((F(mu[b], b) for b in range(b0, r)), F(0))
            e = F(floor_sum) - 2 * (r + 1) * m * reciprocal
            assert e == 2 * m * t + j
        else:
            # Forward column cutoffs, independently checked by inverse rows.
            j = sum(mu[b] * (mertens[max(lo - 1, min(hi, x // (3 * b)))]
                            - mertens[lo - 1]) for b in range(b0, r))
            area = sum(max(0, min(hi, x // (3 * b)) - lo + 1) for b in range(b0, r))
            e = 2 * m * t + j
        assert 9 * area <= 2 * w * w + 11 * w
        row = dict(R=r, W=w, J=j, E=str(e), base=str(2 * m * t), area=area)
        records.append(row)
        counts['strip_cases'] += 1
        if j and first_jump is None:
            first_jump = row
        if e * (2 * m * t) < 0 and first_reversal is None:
            first_reversal = row
        if j < 0 and first_negative is None:
            first_negative = row
        return row

    for r in range(2, 257):
        for w in range(r // 4 + 1):
            evaluate(r, w, True)

    for r in list(range(2, 257)) + [317, 549, 1027, 2002, 4096, 8192]:
        for k in sorted({kmins[r], 2 * kmins[r], F(r), F(r * r), F(100 * r * r)}):
            for safe in [False, True]:
                w = safe_width(r, k) if safe else width(r, k)
                row = evaluate(r, w, False)
                e = F(row['E'])
                if safe:
                    assert e * e <= F(61, 9) ** 2 * r * r * k
                    counts['safe_width_checks'] += 1
                else:
                    ratio_sq = e * e / (r * r * k)
                    if ratio_sq > max_ratio_sq[0]:
                        max_ratio_sq = (ratio_sq, dict(row, K=str(k)))
                    counts['adaptive_checks'] += 1
                if r > 256 and k == kmins[r]:
                    fixtures[f'{r}:{safe}'] = dict(row, K=str(k))

    complete = []
    for r in list(range(2, 81)) + [99, 317]:
        x, n, k = r * r - 1, r - 1, kmins[r]
        w, b0 = width(r, k), r - width(r, k)
        a1 = x // (2 * b0) + 1
        lo, hi = n // 3 + 1, n // 2
        parts = [F(0), F(0), F(0)]
        q = 0
        for a in range(1, r):
            for b in range(1, r):
                f = x // (a * b)
                q += mu[a] * mu[b] * f
                value = mu[a] * mu[b] * (f - F(r + 1, b) * (n // a))
                sector = 0 if w and a >= a1 and b >= b0 else (
                    1 if w and lo <= a <= hi and b >= b0 else 2)
                parts[sector] += value
                counts['complete_ordered_sites'] += 1
        p = (r + 1) * sum((F(mu[b], b) for b in range(1, r)), F(0))
        all_parts = [p] + parts
        assert q == sum(all_parts) == 2 * mertens[n] - mertens[x]
        diagonal = sum(v * v for v in all_parts)
        mixed = sum(2 * all_parts[i] * all_parts[j] for i in range(4) for j in range(i + 1, 4))
        assert q * q == diagonal + mixed
        complete.append(dict(R=r, Q=q, parts=list(map(str, all_parts)), cross=str(mixed)))
    counts['complete_returns'] = len(complete)

    encoded = json.dumps(records, sort_keys=True, separators=(',', ':'))
    Path('/workspace/staircase-records.json').write_text(encoded + '\n')
    out = dict(status='PASS', python=platform.python_version(), counts=dict(counts),
               first_jump=first_jump, first_sign_reversal=first_reversal,
               first_negative_jump=first_negative, held_out=fixtures,
               maximum_sampled_ratio_squared=str(max_ratio_sq[0]),
               maximum_sampled_ratio_fixture=max_ratio_sq[1],
               complete_fixtures=[v for v in complete if v['R'] in [6, 99, 317]],
               record_sha256=sha256(encoded.encode()).hexdigest(),
               elapsed_seconds=time.perf_counter() - start)
    Path('/workspace/staircase-results.json').write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps(out, indent=2))


if __name__ == '__main__':
    main()
~~~

#### Executed Artifact: staircase_reference.py

~~~python
"""Independent trial-factor coefficients and inverse row geometry."""

from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import json
import time


def trial_mu(n):
    value, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            value = -value
            if n % p == 0:
                return 0
        p += 1
    return -value if n > 1 else value


start = time.perf_counter()
mu = [0] + [trial_mu(n) for n in range(1, 8193)]
prefix = [0]
for v in mu[1:]:
    prefix.append(prefix[-1] + v)
rows = json.loads(Path('/workspace/staircase-records.json').read_text())
for row in rows:
    r, w = row['R'], row['W']
    n, x, b0 = r - 1, r * r - 1, r - w
    lo, hi = n // 3 + 1, n // 2
    # Sum a rows with independently reconstructed b intervals.
    j = sum(mu[a] * (prefix[max(b0 - 1, min(n, x // (3 * a)))] - prefix[b0 - 1])
            for a in range(lo, hi + 1))
    m = sum(mu[lo:hi + 1])
    t = sum((F(mu[b] * (b - r - 1), b) for b in range(b0, r)), F(0))
    assert j == row['J']
    assert 2 * m * t + j == F(row['E'])
    area = sum(max(0, min(n, x // (3 * a)) - b0 + 1) for a in range(lo, hi + 1))
    assert area == row['area']
out = dict(status='PASS', independent_trial_mu=8192, inverse_cases=len(rows),
           records_sha256=sha256(json.dumps(rows, sort_keys=True, separators=(',', ':')).encode()).hexdigest(),
           elapsed_seconds=time.perf_counter() - start)
Path('/workspace/staircase-reference-results.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
~~~

#### Executed Artifact: staircase_synthetic.py

~~~python
"""NON-MOBIUS envelope-only control: exact inverse-boundary enumeration."""

from pathlib import Path
import json
import time


def column_prefix(d, h):
    blocks, last = divmod(d, 3)
    _, r = divmod(blocks, 2 * h)
    base = -r if r <= h // 2 else (r - h if r <= 3 * h // 2 else 2 * h - r)
    sign = 1 if h // 2 <= r < 3 * h // 2 else -1
    return 3 * base + last * sign


start = time.perf_counter()
results = []
for m in [8, 16, 32, 64, 128]:
    r, h, length = 192 * m ** 4, 8 * m * m, 2 * m ** 3
    a0, w = r // 3, r // 4
    assert length % (2 * h) == 0 and 3 * length <= w
    assert a0 + length <= (r - 1) // 2
    assert h * h <= a0 + 1
    assert (3 * h // 2) ** 2 <= r - 3 * length + 1
    assert column_prefix(3 * length, h) == 0
    assert 32 * (1 + (3 * length) ** 2 // (3 * (r - 3 * length)) + 1) <= h
    j = 0
    for x in range(1, length + 1):
        sign = 1 if (x - 1) % (2 * h) < h else -1
        denominator = r + 3 * x
        first = (3 * r * x + 1 + denominator - 1) // denominator
        j -= sign * column_prefix(first - 1, h)
    j0 = 3 * length * h // 4
    assert 32 * abs(j - j0) <= 3 * length * h
    assert 128 * j >= 7 * m * r
    results.append(dict(m=m, R=r, h=h, L=length, K=1, W=w, J=j,
                        linear_J=j0, error=j - j0,
                        violates_16_over_3=(3 * j > 16 * r)))
out = dict(status='PASS', scope='SYNTHETIC_NOT_MOBIUS', results=results,
           elapsed_seconds=time.perf_counter() - start)
Path('/workspace/staircase-synthetic-results.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
~~~

#### Executed Artifact: staircase_synthetic_reference.cpp

~~~cpp
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>

using i64 = std::int64_t;
using i128 = __int128_t;

int main() {
    for (i64 m : {8, 16, 32, 64, 128}) {
        const i64 R = 192 * m * m * m * m;
        const i64 h = 8 * m * m;
        const i64 L = 2 * m * m * m;
        i64 J = 0, linear = 0, column = 0, max_column = 0;
        for (i64 d = 1; d <= 3 * L; ++d) {
            const i64 x = (d - 1) / 3;
            const i64 phase = x % (2 * h);
            const i64 sign = (h / 2 <= phase && phase < 3 * h / 2) ? 1 : -1;
            const i64 c = static_cast<i64>((static_cast<i128>(R) * d - 1) / (3 * (R - d)));
            auto prefix = [h, L](i64 u) {
                if (u < 0 || u > L) return i64{0};
                const i64 a = u % (2 * h);
                return std::min(a, 2 * h - a);
            };
            assert(c >= x && 32 * (c - x) <= h);
            J += sign * prefix(c);
            linear += sign * prefix(x);
            column += sign;
            max_column = std::max(max_column, column < 0 ? -column : column);
        }
        assert(column == 0 && max_column == 3 * h / 2);
        assert(linear == 3 * L * h / 4);
        assert(32 * (J > linear ? J - linear : linear - J) <= 3 * L * h);
        assert(128 * J >= 7 * m * R);
        std::cout << m << '\t' << R << '\t' << J << '\t' << linear << '\t' << max_column << '\n';
    }
}
~~~

#### Executed Artifact: staircase_audit.py

~~~python
"""Post-discovery certificate comparison and small original-source fixtures."""

from fractions import Fraction as F
from pathlib import Path
import json
import subprocess
import time

from staircase_probe import mobius, width


mu = mobius(300)
first_equality = None
for r in range(2, 257):
    for a in range((r - 1) // 3 + 1, (r - 1) // 2 + 1):
        for b in range(r - r // 4, r):
            if 3 * a * b == r * r - 1 and mu[a] * mu[b]:
                first_equality = dict(R=r, a=a, b=b, coefficient=mu[a] * mu[b])
                break
        if first_equality:
            break
    if first_equality:
        break
assert first_equality == dict(R=8, a=3, b=7, coefficient=1)
assert width(15, F(9)) == 1
total = 0
for y in range(15):
    total += mu[y]
    assert (total - 1) ** 2 <= 9 * (y + 1)

models = json.loads(Path('/workspace/staircase-synthetic-results.json').read_text())['results']
start = time.perf_counter()
raw = subprocess.check_output(['/workspace/staircase-synthetic-reference'], text=True)
elapsed = time.perf_counter() - start
for fields, expected in zip(raw.strip().splitlines(), models, strict=True):
    m, r, j, j0, maximum = map(int, fields.split())
    assert (m, r, j, j0) == tuple(expected[k] for k in ['m', 'R', 'J', 'linear_J'])
    assert maximum == 3 * expected['h'] // 2

native_budget = []
for b in [F(3, 5), F(3, 4), F(5, 6), F(7, 8), F(9, 10)]:
    theta = (3 * b - 1) / 2
    assert 0 < theta < b < 1
    assert 2 * b + theta - 1 <= 2 * theta == 3 * b - 1 < 2 * b
    native_budget.append(dict(b=str(b), theta=str(theta), component=str(3 * b - 1), saving=str(1 - b)))

full = json.loads(Path('/workspace/staircase-results.json').read_text())
held_out = []
for key, item in full['held_out'].items():
    e = F(item['E'])
    held_out.append(dict(R=item['R'], safe=key.endswith('True'), W=item['W'],
                         J=item['J'], E_floor=e.numerator // e.denominator,
                         E_ceil=-((-e.numerator) // e.denominator)))
out = dict(status='PASS', first_nonzero_equality=first_equality,
           synthetic_exact_matches=len(models), cpp_elapsed_seconds=elapsed,
           cpp_forward_columns=sum(3 * v['L'] for v in models),
           python_inverse_rows=sum(v['L'] for v in models),
           native_component_budget=native_budget, held_out_integer_enclosures=held_out)
Path('/workspace/staircase-audit-results.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
~~~

#### Executed Artifact: staircase-registration.md

~~~markdown
# Frozen FINITE-AC Floor-Two Experiment

Run: 20261108-census-2, scheduled 2026-11-08 11:00:01 EST.
Source: main 30c9fade09be0a4cb12776cd324e9fd9a9ed44ac.
Purpose: test the j=2 moving-boundary inference in 20261108-wheel-2/HC.

Original definitions: N=R-1, X=R^2-1; genuine Mobius mu;
T(a,b)=floor(X/(ab))-(R+1)floor(N/a)/b.
K>=0 satisfies (M(y)-1)^2<=K(y+1) for every 0<=y<R.
W=floor(R/(4sqrt(K))), B=R-W, I2=[floor(N/3)+1,floor(N/2)].
E2=sum_(a in I2,B<=b<R) mu(a)mu(b)T(a,b).
J2=sum mu(a)mu(b)(floor(X/(ab))-2).
W=0 means empty strip; ordered occurrences, squareful zeros retained.

Competing hypotheses, before execution:
1. The staircase can be erased without changing sign or payment: seek a
   smallest genuine nonzero jump and strict sign reversal.
2. The exact endpoint admits only a single jump, with an explicit
   moving-boundary bilinear form, not an unrestricted multilevel floor.
3. Historical prefix control alone gives a uniform O(R sqrt(K)) strip
   bound even for bounded nonmultiplicative coefficients. This is an
   explicitly synthetic diagnostic, not a statement about genuine mu.
4. A genuine-mu O(R sqrt(K)) strip estimate survives, but needs a new
   boundary estimate beyond the already paid separable term.

Discovery: all R=2..256 and all W=0..floor(R/4); adaptive valid K in
{Kmin,2Kmin,R,R^2,100R^2}; include strict equality boundaries.
Held-out: R in {317,549,1027,2002,4096,8192}; adaptive K values as above.
Literal complete source and all square cross terms: R=2..80 plus 99,317.
Independent algorithm: forward floor enumeration versus inverse hyperbola
row-prefix enumeration, independently trial-factored Mobius values.
All accept/reject comparisons exact integers/rationals; no decimal signs.

Synthetic investigation: derive a bounded-prefix block construction in the
same strip to discriminate envelope-only reasoning. Freeze its formula and
test domain in a dated addendum before executing it; it must not be
substituted for genuine mu or the complete Mertens identity.

Stop: once the minimal genuine falsifier and boundary structure are verified,
do not extend an unchanged census. Do not fit an exponent or universal
constant from a finite maximum. Full complement remains in Q=P+E1+E2+Z.
Unfinished Coordinator NYMAN independent review is not declared completed:
Analytic ND has already executed those prescribed fixtures; this run selects
the newer, nonduplicate HC handoff under the live route selector.

## Implementation-Stage Pencil Extension

The safe-width hypothesis was derived after the original checkpoint and
included in the first implementation before any test output was inspected.
Let Wsafe be the largest integer W satisfying 16*K*W^2<=R^2 and
W^4<=R^2*K. Test |E2(R,Wsafe)|<=(61/9)*R*sqrt(K), by squaring
with exact rational arithmetic. This changes the admitted width, not the
original wide-strip conjecture; the difference remains in the complement.
Its paper proof uses the explicit jump-site count
9*card{(a,b) in strip:3ab<=X}<=2W^2+11W.
No constant was selected from computed maxima.
~~~

#### Executed Artifact: staircase-synthetic-registration.md

~~~markdown
# Synthetic Boundary-Control Addendum

Prepared before execution. This is a deliberately NON-MOBIUS coefficient
family on the same ordered strip, solely testing an envelope-only inference.
It is not a counterexample to finite-C, the genuine j=2 conjecture, or RH.

For m a positive multiple of 8, set R=192*m^4, K=1, W=R/4,
a0=R/3, h=8*m^2, L=2*m^3. Let f(1)=1. On a=a0+x,
1<=x<=L, use +1 for (x-1) mod (2h)<h and -1 otherwise.
On b=R-d, 1<=d<=3L, put x=floor((d-1)/3), and f(b)=+1
when h/2 <= x mod (2h) < 3h/2, -1 otherwise. Else f=0.
Both support sums are zero. They are disjoint and lie in the genuine
historical floor-two row strip and column band.

Let F(u) be the triangular row prefix, zero outside [0,L]. The exact
hyperbolic cutoff is c(d)=floor((R*d-1)/(3*(R-d))). Compute
J=sum_(d=1..3L) f(R-d)*F(c(d)). Independent inverse form:
J=sum_(x=1..L) f(a0+x)*(-C(ceil((3*R*x+1)/(R+3*x))-1)),
where C is the column coefficient prefix in increasing d.

Frozen tested m: 8,16,32,64,128. Python inverse formula versus independent
C++ forward formula, with exact 128-bit products where needed.
Check full historical shifted-prefix envelope with K=1 by support extrema
and interval monotonicity, not sampling unrepresented zero gaps.
Check J0=3*L*h/4 for the linear-boundary comparison; prove and test
|J-J0|<=3*L*h/32, hence J/R>=7*m/128. The ratio diverges in the
paper family only; finite computed ratios are not an exponent fit.
The separable strip term vanishes exactly since sum_row f=0.
The synthetic global Mertens/convolution identity is NOT used.
~~~



### Prepublication Freshness - 20261108-census-2

At 2026-11-08 16:19:39 UTC, main was still 30c9fade09be0a4cb12776cd324e9fd9a9ed44ac and agent-reports was the verified checkpoint 7dd71f8ed80b938a9d290dffc009612f2640b79f. The final validator passed 14 A-N sections, balanced fences, table layout, seven byte-exact embedded artifacts and their SHA-256 values, the original record digest and all five cross-language synthetic matches. Three portfolio table rows initially had an extra cell; that formatting-only validation failure was repaired before publication. A pre-write completeness check initially rejected the harmless blank line after the final code fence; its corrected check confirms the exact 54760-character local append. Neither guard failure changed arithmetic or prior report content. Validated append SHA-256: bd585681feb7ad43954b604358a6977209f3f1f5079d4c32ffa2cc7c6ac5e67e. Final preparation clock: 2026-11-08 16:21:10 UTC. The repeated post-discovery audit passed, with a final measured C++ comparison runtime of 0.106566963 s; the earlier 0.145267501 s measurement in N is preserved as observed.

This substantive append preserves all prior daily content byte-for-byte. Its publication is not inferred from this text; the following receipt records the actual immutable readback.


### Verified Publication Receipt - 20261108-census-2

At **2026-11-08 16:21:41 UTC** (11:21:41 EST), immutable readback verified substantive commit **79a4920d0de574ea691ab24edba785d75b282ad6**, report blob **da517a7c9ecca3512d88c15cc2431a17a9315049**, against all **129955 characters** of the submitted daily report. The complete previous daily content and early checkpoint are unchanged prefixes. The commit audit confirms exactly one changed file: research/agent_reports/2026-11-08/40-prime-census.md. Embedded registrations, complete executed source, exact certificates and provenance are present.

Execution=COMPLETED; substantive publication=PUBLISHED / READBACK_VERIFIED. SJ1-SJ4 remain **PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED**. SJ5 is **FINITE_COMPUTATION**, and each refuted statement retains its original or explicitly synthetic scope. In particular, the non-Mobius envelope countermodel does not refute the genuine strip conjecture. **NEW_VERIFIED_ENDPOINT_GAIN=NONE; canonical VF/RH OPEN.**

Next continuation: the actual-Mobius omitted hyperbolic boundary at the ORIGINAL adaptive width, using multiplicativity or another new source-specific restriction; retain the already paid narrow strip and every complete-return term. Do not rerun unchanged CORR4/HC tables. Coordinator's NYMAN independent review remains a separate pending task. No investigator rotation, source, PR, workflow, schedule or other report was modified, and no other agent was launched. All computation sessions are finished.

This receipt records the verified substantive commit above. Its own append is separately checked by immutable readback before the completion message.


## Scheduled AF Frequency Checkpoint - 20261108-census-3

Recorded 2026-11-09 00:07:46 UTC; actual trigger 2026-11-08 19:00:01 EST. RUN_ID_UNAVAILABLE. Execution=PARTIAL / IN_PROGRESS; no result claimed.

Live main 6144c73b05d5a85e6a9424708986860c6276f60d; AGENTS blob bdd5b9f6867ae2d39b74fc966b7f548a9aba3a61; contract blob d1d6fd558ee23927bd9f70ffdc375bafd1dbb67a. Intake agent-reports 1dcde5441a9e157cf964d38745f867b44811f75b. All seven November 7 and November 8 reports are available; relevant latest findings, handoffs and resume capsules read. No missing stage is inferred. Coordinator 00/90 mirrors have equal blobs on both dates. External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 contains no entry newer than October 18. Historical PNT, q=R boundary and unconditional-versus-first-bad safeguards retained, obsolete task priorities not revived.

Canonical target remains VFCanonicalSquareVonKochStatement. Finite-A, zero-log amplification and RH remain open. Recent #1111, #1115 and #1116 are now merged. Exact-head checks observed: #1111 13/13 successful; #1116 14/14 successful. Actual #1116 source gives beta<=7/8-(7m/8-e) on a fixed fine same-source D; its coarse old-family explicit bound must not overwrite #1111's stronger near-uniform comparator. Analytic EC2's e->0 result is paper/self-audit, not newly formalized here. This run claims no endpoint advance.

Consumed AF1-AF5/CP, Census TC/SJ, Referee WT and scoped HC/SJ acceptance, Wheel FD, Owner JS, Analytic EC/ND, Lean #1111/#1113 repair history. Selected task is Coordinator AF frequency falsification; do not rerun its 8413-case identity scan. Source-verified original Euler kernel, finite-C consumer and strict historical envelope retain blobs e482711a3f55c1f59fc771f108671477f51732f2, e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73 and 1270d4d91c53b50b110d10014f223f427fb7a575. No local Lean execution or other-agent launch.

### Frozen Before Execution

#### Frozen AF Frequency Test: 20261108-census-3

Scheduled trigger: 2026-11-08 19:00:01 EST. No platform run ID supplied.
Source main: 6144c73b05d5a85e6a9424708986860c6276f60d.
Question: does genuine arithmetic force nonzero additive frequencies to oppose the coherent frequency on the AF floor-two triangle?

Use genuine Mobius mu, N=R-1, X=R^2-1, I2=[ceil(R/3),floor((R-1)/2)], B=R-W. Define L=sum mu(a)mu(b) over a in I2, B<=b<R, 3a+b<=2R. Use q=2W+1 and the exact f,g,h conventions of Coordinator AF3, including the <= boundary and squareful zeros. K_R=max_{0<=y<R}(M(y)-1)^2/(y+1).

Choose the largest integer W>=1 with W=1 mod 3 and 4W<=R, 16K_R W^2<=R^2, W^6<=R^4 K_R. Empty admissible width means no test row. Thus 3 divides q. The width rule is fixed before any data.

Candidate H_DC: C0*(L-C0)<=0 for every admitted R, where C0=(W+1)F(0)G(0)/q. A strict positive rational product refutes it. This is a new laboratory candidate, NOT an assertion made by AF.
Candidate H_3: if R=1 mod 3, then C0*C3<=0, where C3 is the sum of the Fourier k=q/3 and 2q/3 contributions. The multiplicative sign mu(3n)=-mu(n) when 3 does not divide n motivates, but does not prove, this candidate. A strict positive rational product refutes it.
Rival mechanism: the third-root sector is controlled by a residue-specific backward prefix, not merely its sign or the zero-frequency sum. Test the pencil identity q*C3=F(0)*(G(0)-3*B_c), c=(2R-2) mod 3, B_c=sum_{B<=b<R,b=c mod 3}mu(b). Preserve both zero and nonzero sectors.

Primary held-out root range: every R=257..4095, excluding the previously inspected roots 317,549,1027,2002. A new question is tested; the old AF identity census is not rerun. Confirmation roots fixed now: 8209,10007,16381,20011,32771. Report first violations in the registered range, not smallest global violations. Development R<=256 may be searched ONLY afterwards and must be labeled retrospective.

Exact methods: multiplicative Mobius sieve and rational prefix sums; independent C++ trial factorization and direct ordered triangle enumeration. Compare all primary and confirmation rows byte-for-byte. At first falsifiers and confirmation fixtures, recover complete conductor-grouped Fourier contributions with exact residue convolution and Ramanujan sums; no floating DFT is needed. Keep the k=0 term and every mixed square term.

Full original Euler return at R=257,263 and each primary first falsifier <=1024: Q=P+E1+2m2*t_B+L+(J2-L)+Z and M(X)=2M(R-1)-Q. Compute Z directly from the complement, not by defining it as a remainder. Recombine all six squares and fifteen cross terms exactly. These fixtures are scope checks, not a complete-source bound.

Stop after decisive falsifiers and the fixed confirmation range. Do not fit a constant or infer an infinite estimate. Any new universal lemma is separately proved and labeled PAPER_PROOF / SELF_AUDIT, not Lean or independent Referee acceptance. No original-source code or report other than the owned daily report may be published.



## Exact Additive-Frequency Synthesis - 20261108-census-3

Run `20261108-census-3`. Scheduled trigger: November 8, 2026, 19:00:01 EST (America/New_York). RUN_ID_UNAVAILABLE. This is the completion of that invocation, not an additional launch.

### A. Most Important Discovery

**Nonzero additive frequencies can reinforce the coherent frequency on the genuine Mobius triangle. The factor-3 frequency pair can do the same, but its actual weighted contribution is uniformly small without any favorable-sign hypothesis.** Its sign is controlled by a specific backward residue-class sum, not by multiplicativity alone.

Both laboratory candidates registered before execution are REFUTED. The first failures in the held-out root range are R=258 for all-nonzero anti-alignment and R=307 for third-root anti-alignment under R=1 mod 3. A subsequent, explicitly retrospective minimization gives R=6 and R=28, respectively, for the frozen width rule. These are auxiliary sign counterexamples, not counterexamples to Coordinator AF, finite-C, the canonical VF statement, first-bad payment, or RH.

The surviving replacement is exact. With the notation below,

```text
C3 = F0*(G0-3*B_c)/q,   c=(2R-2) mod 3,
|C3| <= (2W/q)*|F0| <= |F0| <= 2*sqrt(KR).
```

The first equality and bound apply to every original AF triangle with W>=1 and W=1 mod 3, not just the tested roots. The last bound uses the full strict-history envelope. The proof is given below; its status is PAPER_PROOF / SELF_AUDIT, independent review PENDING, NOT_FORMALIZED. The finite results are FINITE_COMPUTATION. **NEW_VERIFIED_ENDPOINT_GAIN=NONE; canonical VF, zero-log amplification, uniform finite A, and RH remain OPEN.**

### B. Authority And Current Objective

Pinned main: `6144c73b05d5a85e6a9424708986860c6276f60d`. Intake agent-reports: `1dcde5441a9e157cf964d38745f867b44811f75b`. Main was first retrieved at the beginning of this invocation, shortly after 2026-11-09 00:00 UTC. The governing AGENTS blob is `bdd5b9f6867ae2d39b74fc966b7f548a9aba3a61`; CURRENT_PROOF_CONTRACT blob is `d1d6fd558ee23927bd9f70ffdc375bafd1dbb67a`.

Canonical target: `VFCanonicalSquareVonKochStatement`, namely exists C>=0, for every integer R>=2, |pi(R^2)-VF_can(R^2)|<=C R log R. The selected proper-source investigation serves FINITE-AC through the original ordered Euler kernel, without claiming to pay the full consumer. The strict-history target is retained; K_R is not replaced by 1.

Recent PRs #1111, #1115 and #1116 are all human-merged. #1111 supplies the near-uniform explicit boundary b_pack=7/8-1/(32*N_pack). The actual #1116 same-source statement is beta<=7/8-(7m/8-e), for a fixed fine HighData certificate and its original minimum m and error e. Its coarse explicit old-family bound must not displace a stronger comparator from another verified family. Coordinator CP2's composition and Analytic EC's e->0 argument retain their own paper/review status; neither is a new formal result of this run. No change of arithmetic source is inferred from these analytic facts.

**CI precision correction to the checkpoint:** 13 successful checks were attached to #1111 head `20875a55dd9780993c4cdc06624c88be6060e2ee`, and 14 to #1116 head `1e32da429324c39a791406a0ae1265581df7ea06`. Attached-head success is not proof of an exact-head checkout. The retrieved #1116 dedicated log actually checks synthetic merge `60fa59f302f26900435231cd9685f0f6c5f9b82a`, incorporating that head. Its source blob `b7b05069ea013d83b2acaa76a8ea2ed932568930` was fetched and equals current main byte-for-byte. The log shows warning-fatal Lean invocation and only propext, Classical.choice, Quot.sound for the five displayed declarations. Dependency-checkout and action-runtime warnings also occur; they are not silently described as a warning-free log. No new current-main or exact-PR-head Lean build is claimed. Evidence: run 42520918799, job 128853972193.

### C. Competing Hypotheses And Registration

Registration was published and immutably read back at commit `270bf08aadd32af4a6a70735b4ddc3a0ff9d9338`, blob `4e95c64fb6fe9a8fee3463a9e8ede7cb94726307`, before any arithmetic test output. The existing daily report remained an unchanged prefix.

H_DC: for every admitted root, C0*(L-C0)<=0. Rival: genuine nonzero modes sometimes reinforce the average. A strictly positive exact product rejects H_DC.

H_3: under the additional R=1 mod 3 condition, C0*C3<=0. The relation mu(3n)=-mu(n) for 3 not dividing n motivates testing this sign, but does not imply it. Rival: a backward residue sum, with no forced relation to the forward sum, governs the sign. A strictly positive exact product rejects H_3.

These were new laboratory candidates, NOT claims attributed to the Coordinator. No previously accepted source theorem is refuted. The exact factor-3 identity was written down before execution. Its amplitude bound and the small-root minimization were developed after the first output and are disclosed as post-discovery work.

### D. Original Carrier And Domain

Use N=R-1, X=R^2-1 and genuine mu, including mu(1)=1 and squareful zeros. Set I2=[ceil(R/3),floor((R-1)/2)], B=R-W. Empty sums are zero. Preserve ordered pairs and equal-product multiplicity.

```text
T_R(a,b)=floor(X/(ab))-(R+1)*floor(N/a)/b,
J2=sum_(a in I2,B<=b<R,3ab<=X) mu(a)mu(b),
L =sum_(a in I2,B<=b<R,3a+b<=2R) mu(a)mu(b),
K_R=max_(0<=y<R) (M(y)-1)^2/(y+1).
```

The width is the LARGEST integer W>=1 congruent to 1 mod 3 satisfying

```text
4W<=R,   16*K_R*W^2<=R^2,   W^6<=R^4*K_R.
```

All comparisons are integer/rational. The last condition is exactly the squared AF curvature condition because K_R>=0. The registered primary roots are every R=257..4095 except 317,549,1027,2002, which were previously inspected. There are 3,835 primary roots. The five fixed confirmation roots are 8209,10007,16381,20011,32771. No endpoint was changed after seeing a failure. This is a new frequency-sign test, not another run of AF's 8,413-case identity census.

Let q=2W+1, so 3 divides q. On Z/qZ, put f(v)=mu((R+v)/3) for 0<=v<=W with 3 dividing R+v and (R+v)/3 in I2, and zero otherwise; g(d)=mu(R-d) for 1<=d<=W; h(u)=1 for 0<=u<=W. Use F(k)=sum f(v)e(-kv/q), and similarly G,H. AF gives L=q^-1 sum_k H(k)F(k)G(-k). Define C0=(W+1)F0*G0/q, C3 as the sum of k=q/3 and 2q/3, and Crest=L-C0-C3. The two nonzero members are kept together as one exact real sector. These additive orders are NOT Hecke conductors or original #915 source masks.

### E. Executed Results

The sieve/prefix implementation and separate C++ trial-factor/direct-pair implementation produced byte-identical 3,840-row integer files. SHA-256: `c112800c4e2bff84aebde90c10f4702950ba986019df6af058538a5cfb72f165`. The independent C++ run visited 296,585,703 ordered sites and trial-factored all coefficients through 32771. A third, exact cube-root-ring implementation independently verified all 3,840 C3 numerators using trial-factored coefficients, not the proposed residue formula.

Across the complete registered set, the C0/nonzero product is positive in 1,710 rows, negative in 1,744, and zero in 386. Among 1,280 rows with R=1 mod 3, C0*C3 is positive in 612, negative in 501, and zero in 167. These counts are finite classifications, not a probabilistic independence claim. K_R=3/2 throughout the registered set is likewise finite evidence only.

All entries C0,C3,Crest below share the denominator q shown in the table.

| R | W | q | q*C0 | q*C3 | q*Crest | L | J2 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 258 | 43 | 87 | -352 | -20 | -237 | -7 | -15 |
| 307 | 46 | 93 | -188 | -4 | 1308 | 12 | 9 |
| 8209 | 433 | 867 | -101556 | 63 | -99651 | -232 | -187 |
| 10007 | 496 | 993 | 2485 | 80 | 27225 | 30 | 24 |
| 16381 | 688 | 1377 | 0 | 0 | 17901 | 13 | 31 |
| 20011 | 787 | 1575 | 80376 | -186 | -138465 | -37 | 19 |
| 32771 | 1093 | 2187 | -136750 | 115 | 165066 | 13 | -21 |

Nine fixtures also have complete exact decompositions by additive order d dividing q, reconstructed by two residue-convolution methods. Every sector square and cross term sums to L^2. In particular R=32771 has order numerators, in orders 1,3,9,27,81,243,729,2187,

```text
[-136750, 115, -660, -4644, -14958, 10125, -139725, 314928].
```

Their sum is 28431=q*13. The sector diagonal is 137751556259/4782969, while all mixed terms sum to -136943234498/4782969, leaving exactly 169. Neither the signs nor the large individual sectors can be interpreted without that mixed contribution.

### F. Exact Falsifiers And Extremes

At the first primary H_DC failure R=258,W=43, F0=4, G0=-2, and the relevant backward residue sum B_1=1. Thus C0=-352/87 and L-C0=-257/87; the retained square cross term is **2*C0*(L-C0)=180928/7569>0**. The genuine positive row sites are 86,87,91,93,94,95; negative row sites are 89,97; squareful row sites contribute zero. The backward interval is [215,257], with residue sums (-1,1,-2) in classes 0,1,2.

At the first primary H_3 failure R=307,W=46, R=1 mod 3, F0=-4,G0=1,B_0=0. Hence C0=-188/93, C3=-4/93, and **2*C0*C3=1504/8649>0**. The backward residue sums are (0,2,-1). The remaining frequencies reverse the overall sign: Crest=436/31 and L=12. Local reinforcement and total cancellation are different statements.

The strongest positive C0/nonzero cross term in the primary domain occurs at R=2899,W=217: C0=20928/145, L-C0=10102/145, L=214, and their square cross term is 422829312/21025. This is a declared finite extremum, not an inferred universal constant.

Retrospective direct enumeration of every R=2..256, under the SAME frozen width rule, yields 253 admitted roots and the smaller witnesses:

* R=6,W=1,K=3/2: the sole affine pair is (a,b)=(2,5), both signs -1. L=1,C0=2/3,C3=1/3. This is the first H_DC failure for that rule.
* R=28,W=4,K=3/2: F0=mu(10)=1, the backward interval [24,27] has only mu(26)=1 nonzero, and B_0=0. L=1,C0=5/9,C3=1/9. This is the first H_3 failure for that rule.

The word "first" does not claim minimization over arbitrary width-selection rules. These small examples were NOT held out and are not credited as a second independent discovery. At R=263,W=43, C0=C3=0 but L=-12, with the whole value in additive order 87. Thus a bound on L by any finite multiple of |C0|+|C3| is also impossible on this carrier; this is a post-discovery consequence, not a registered third test.

### G. Hidden Variable: A Backward Residue Sum

Claim `20261108-census-3/FR1` (PAPER_PROOF, self-audit): for every original AF triangle with W>=1, W=1 mod 3 and 4W<=R, let

```text
F0=sum_(a in I2,0<=3a-R<=W) mu(a),
G0=sum_(R-W<=b<R) mu(b),
B_c=sum_(R-W<=b<R,b=c mod 3) mu(b),  c=(2R-2) mod 3.
```

Then q*C3=F0*(G0-3B_c). To prove this, write W=3j+1. The counts of h in residue classes 0,1,2 are j+1,j+1,j. Since every supported v is congruent to -R mod 3, summing the two nontrivial cube-root characters gives weights +1 unless 2R-b=2 mod 3, when it gives -2. This yields the formula with no floating approximation and with all physical sites retained.

Consequently

```text
q^2*C0*C3=(W+1)*F0^2*G0*(G0-3B_c).
```

That is a complete sign classification. Under R=1 mod 3,

```text
B_0 = -sum_(ceil((R-W)/3)<=n<=floor((R-1)/3),3 not dividing n) mu(n).
```

It uses multiplicativity at the actual backward interval. F0 instead uses a forward interval near R/3. Their different endpoints are indispensable. If B_0=0 and F0*G0!=0, then C3=C0/(W+1), so reinforcement is forced. Exactly 80 registered rows satisfy this condition, independently checked in the audit. The residue sum explains these instances; no statistical causality or independence is claimed.

### H. Exact Frequency Reconstruction

Claim `20261108-census-3/FR2` (PAPER_PROOF for the algebra; FINITE_COMPUTATION for the nine certificates). For e dividing q, define

```text
A_e=sum_(v,d,u) f(v)g(d)h(u) * 1_(e divides d-v-u).
N_e=sum_(j divides e) mu(e/j)*j*A_j.
```

Character orthogonality gives e*A_e as the sum over frequencies whose additive order divides e; divisor inversion therefore gives the EXACT order-e numerator N_e. Hence the order-e contribution is N_e/q and sum_(e divides q)N_e=qL. This is a transparent finite Fourier projection, not a new arithmetic cancellation theorem or a transfer to Hecke phases.

The primary certificate builds the cyclic correlation of f and g, then counts the h residues. The second certificate separately groups f,g,h by residues before multiplication. The third-root check is more independent: it works in Z[z]/(z^2+z+1), directly evaluates F,G,H and takes the trace 2a-b of a+bz. It shares neither the inferred residue formula nor a floating Fourier transform. The independent C++ reconstruction uses direct physical (a,b) pairs, not either spectral array.

### I. Corrected Theorem And Surviving Question

Claim `20261108-census-3/FR3` (PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING): for every R,W as in FR1 and every valid LowerMertensCriticalEnvelope R K,

```text
|C3| <= (2W/(2W+1))*|F0| <= 2*sqrt(KR).
```

Proof: each coefficient in G0-3B_c has magnitude at most 2 and there are W integers. Thus |G0-3B_c|<=2W. F0 is M(A)-M(lo-1), with A=min(floor((R-1)/2),floor((R+W)/3))<R. In a nonempty interval, subtracting the two shifted-history values and applying the original envelope gives |F0|<=sqrt(K(A+1))+sqrt(K*lo)<=2sqrt(KR). If the interval is empty, F0=0 and the claim is immediate. No empirical constant is used. The proof uses absolute coefficient bounds for the amplitude, not multiplicativity or a favorable sign.

On the additional AF1 domain, its already proposed paper bound |E2-L|<=(217/36)R sqrt(K), together with R>=4 when W>=1, gives the proper-source corollary

```text
|E2-(C0+Crest)| <= (253/36)*R*sqrt(K).
```

This corollary retains AF1's paper/review dependency and only treats widths W=1 mod 3. It removes a paid frequency pair, not the whole nonzero spectrum, and not the Euler complement. It does not extend an estimate to unregistered widths by rounding without paying the difference.

The surviving OPEN proper-strip question remains whether |C0+Crest|<=C R sqrt(K) uniformly on this domain, with one C independent of R,W,K. This is a local target reformulation, NOT an independent input proved by the report. Finite survival of any such bound is not advertised as evidence for a particular universal constant. The meaningful gain here is eliminating two false sign shortcuts and isolating an explicitly paid contribution.

### J. Complete Signed Return

Reuse the original E1 constant-floor rectangle, with a>=floor(X/(2B))+1 and B<=b<R, and define Z by summing T_R directly over EVERY other ordered pair outside E1 and E2. Let P=(R+1)sum_(1<=b<R)mu(b)/b, m2=sum_(a in I2)mu(a), and t_B=sum_(B<=b<R)mu(b)*(1-(R+1)/b). Then

```text
Q=P+E1+2*m2*t_B+L+(J2-L)+Z,
Q=P+E1+2*m2*t_B+C0+C3+Crest+(J2-L)+Z,
M(X)=2*M(R-1)-Q.
```

Both recombinations were checked exactly at four original-source fixtures. Z was computed directly, not defined by subtracting the answer. The six-part version retains six diagonal squares and all fifteen cross terms; the eight-part version retains eight squares and all twenty-eight cross terms. The total is exactly Q^2 in both cases.

| R | M(R-1) | M(R^2-1) | Q | Q^2 | alpha_R |
| --- | --- | --- | --- | --- | --- |
| 257 | -1 | 4 | -6 | 36 | 6/66049 |
| 258 | -2 | 23 | -27 | 729 | 242/49923 |
| 263 | -1 | 64 | -66 | 4356 | 2646/69169 |
| 307 | -1 | -67 | 65 | 4225 | 9248/282747 |

Here alpha_R=(M(X)-1)^2/(R^2*K_R), with the actual K_R=3/2 at these roots. A separate trial-factor calculation through 94248 independently checks M, Q and these complete endpoints. The full source pass visits 293865 ordered sites. Canonical LOW, coherent modes, and Z are not discarded; nothing in the frequency experiment supplies a bound for the complete HIGH return. No #915 source admission or conditional first-bad premise is asserted.

### K. Falsification And Execution Audit

Claim `20261108-census-3/FR4`: H_DC and H_3 are REFUTED at the exact stated scopes. FR5: the registered table, spectral certificates and full-return checks are FINITE_COMPUTATION. FR1-FR3 are newly written paper arguments, not independently accepted mathematics or Lean declarations. Independent algorithmic verification does not impersonate independent Referee acceptance.

No floating-point arithmetic, numerical logarithms, probable-prime tests, randomized signs, fitted thresholds, or uncertified complex values enter a sign claim. Discrete primality and factorization are deterministic throughout the declared finite ranges. Python 3.12.14 and g++ 13.3.0 were observed. C++ flags: -O2 -std=c++17 -Wall -Wextra -Werror. Observed timings: main Python calculation 0.787691538 seconds; independent C++ run, shell timing 0.454 seconds; final independent audit 0.546382974 seconds. They are run measurements, not benchmarks.

The first timing command failed because /usr/bin/time was absent, and the prematurely attempted comparison then found no C++ output file. The executable was subsequently run successfully with the shell's time command, and cmp returned exit status 0. This was an execution-wrapper issue, not a numerical mismatch; no failed comparison is hidden as agreement.

Original source definitions are unchanged at the inspected blobs. Prior HC/SJ/TC computations were reused at their verified scope. The new observations do not supersede Referee WT's explicitly NON-Mobius obstruction. No local Lean, new proof branch, PR, issue, workflow, schedule, other-agent launch, or other report edit occurred.

### L. Specialist Handoffs

* Proof Architect: reject the two laboratory sign restrictions, retain AF's actual inverse statement, and record FR3 as a proper-component payment only. R=263 and R=16381 show that vanishing C0 and C3 do not eliminate the triangle. No campaign change or global advance is requested.
* Owner: the factor-3 backward sum is genuine arithmetic, but not Johnston's first moment or #915 masked source. No prime/floor-Li or physical admission transfer is licensed.
* Analytic: a large unweighted paired Fourier product at k=q/3 can be harmless after its true H/q weight. Any new inverse restriction should keep that weight and the complete sum; do not transfer these rational-mu frequencies to ideal-character sources. EC's stronger endpoint remains separately review-pending.
* Wheel: residue-specific retained cofactors, not aggregate signs alone, control FR1. Your FD occurrence-capacity obstruction remains on its distinct odd-boundary carrier; no inference between the two follows without a proved map.
* Referee: independently check the residue c=2R-2, both cube-root modes, caps and <= endpoints, the history-shift cancellation, and the all-W FR3 proof. Small falsifiers R=6,28 and held-out R=258,307 are exact. AF1 is a paper dependency of the displayed 253/36 corollary, not a new accepted theorem here.
* Lean: no implementation request before mathematical acceptance. A future finite frequency-projection lemma would need the original f/g/h carrier and both modes. These are not compiled claims, and green analytic CI does not certify the numerical arrays.

### M. Ranked Hypothesis Portfolio

| Candidate | Evidence and independent ingredient | Disposition and next requirement |
| --- | --- | --- |
| Universal C0/nonzero anti-alignment | Exact positive cross term at R=258; retrospective R=6 | REJECT. Do not revive by averaging signs without a new hypothesis. |
| R=1 mod 3 forces third-root anti-alignment | R=307 and retrospective R=28; B_0=0 forces reinforcement | REJECT. Replace by the exact residue classification FR1. |
| Third-root amplitude is paid without a sign rule | Exact formula; bounded coefficients; full strict-history envelope | PAPER_PROOF, pending independent review. Check all caps and both modes before formalization. |
| Only C0 and C3 control the original triangle | R=263 has C0=C3=0,L=-12; confirmation R=16381 has L=13 | REJECT every bound vanishing when those two vanish. Keep the remaining spectrum. |
| Full AF proper-strip bound | Still needs a uniform arithmetic restriction on C0+Crest | OPEN, no empirically selected constant and no completed global consumer. |

### N. Resume Capsule And Publication

Resume from main `6144c73b05d5a85e6a9424708986860c6276f60d`, the report checkpoint above, and FR1-FR5. All 3,840 registered rows, nine exact spectral returns, four complete Euler returns, and the retrospective 253-root minimization are complete. Reuse their hashes; do not repeat these scans unchanged.

The single highest-value next experimental task is to choose a NEW quantified restriction on the weighted residual spectrum after removing the provably paid third-root pair. A suitable source-directed continuation would separate frequencies near zero from the rest using the actual triangular multiplier and certify any complex comparisons, with C0 and Z retained. Freeze that restriction and new roots before computation; mere measurement of another maximum is not a theorem. No specific finite sample is claimed to establish the missing all-scale restriction.

All seven roles' November 7 and November 8 reports were retrieved at the pinned intake snapshot. Relevant latest claims, handoffs, review dispositions and resume sections were read; historical embedded programs were not all reexecuted. TODAY=AVAILABLE for every role; prior results remain at their original dates and evidence grades. Equal Coordinator mirrors were counted once. External inbox blob `038018145c0fddb2f6306c0712373adf9cd1ea52` has no post-October-18 entry. EXT-20261018-PNT-1..3, EXT-20261017-XCOORD-1 and EXT-20261014-5 were carried forward solely for their signed-source, root-boundary and unconditional/first-bad safeguards; they do not supply the new frequency estimate.

The source/report hash ledger, complete executed programs and captured results follow in the published append. This report preserves prior daily content. Final publication is PENDING until an actual commit and immutable byte-for-byte readback are observed. No background continuation is promised.


## Source And Continuity Ledger

### Main Sources

| Path | Blob SHA |
| --- | --- |
| AGENTS.md | `bdd5b9f6867ae2d39b74fc966b7f548a9aba3a61` |
| CURRENT_PROOF_CONTRACT.md | `d1d6fd558ee23927bd9f70ffdc375bafd1dbb67a` |
| docs/RHLEAN_REPO_WIDE_PROOF_ATTACKS_20261108.md | `5862ccaffd0e75c25b509c1d246c3aa09b6c345b` |
| docs/PROOF_DEPENDENCY_DAG.md | `455717b6d99da7248c71ada0062dfd6747a7938d` |
| docs/COORDINATE_ATLAS.md | `cd0419d00a37739fe5a292f5cb738e33213949d5` |
| research/EULER_HYBRID_ABEL_GRAM_20261027.lean | `2a94dd8fd56fc03e95f732fb44b778a8d4f83e26` |
| research/EULER_RANK_ONE_FRACTIONAL_ROWS_20261027.lean | `e482711a3f55c1f59fc771f108671477f51732f2` |
| research/EULER_FRACTIONAL_COUPLED_20261027.lean | `e6c4b1690e497760d366e36b28a1f7aa60e19f85` |
| research/EULER_SELF_DUAL_FINITE_C_BRIDGE_20261027.lean | `e97561ef330a9996fd807d8910369f0698147b01` |
| research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean | `e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73` |
| RHLean/Proof/SquareRootLegalAncestryGramReduction.lean | `1270d4d91c53b50b110d10014f223f427fb7a575` |
| research/oai_434/VF919WindowSaturatedLowPrincipal.lean | `b7b05069ea013d83b2acaa76a8ea2ed932568930` |

### Two-Day Reports

| Path | Intake Blob SHA |
| --- | --- |
| research/agent_reports/2026-11-07/00-coordinator-am.md | `00a649b70f851ca193e74e5004d0d3390cf9ca18` |
| research/agent_reports/2026-11-07/10-owner-payment.md | `933e8eb23e669594cc687059d75147e6267eec8d` |
| research/agent_reports/2026-11-07/20-analytic-type-ii.md | `77f3e5795533041e4356ceb94cb66328da7af27c` |
| research/agent_reports/2026-11-07/30-finite-wheel.md | `7739fa5d4cc77f35773b0d4149b2ddd21732a70d` |
| research/agent_reports/2026-11-07/40-prime-census.md | `3fae830e34c590d32c31ad77cad3ace833eb3ff5` |
| research/agent_reports/2026-11-07/50-adversarial-referee.md | `426c2abfa5b8926b512e07f05be37692a2416d0b` |
| research/agent_reports/2026-11-07/60-lean-verification.md | `ec14e2803af8c1e56123682ee61ed927ed4f9450` |
| research/agent_reports/2026-11-08/00-coordinator-am.md | `5d14fb5e0eb3e40a479ebb344b9f8a84a169535e` |
| research/agent_reports/2026-11-08/10-owner-payment.md | `4e1b83a1e5ff8c134e9ca64404397c70c2b07252` |
| research/agent_reports/2026-11-08/20-analytic-type-ii.md | `edecba8785a45cda87c0035d0348695941f1b8ea` |
| research/agent_reports/2026-11-08/30-finite-wheel.md | `60d4cf1b65d4b1b2cc4f13f6c0940c14cb2c50fd` |
| research/agent_reports/2026-11-08/40-prime-census.md | `c70b0a6dda7278e5e7befca546893314a16530df` |
| research/agent_reports/2026-11-08/50-adversarial-referee.md | `68b1162b59f195722fc34378c0d4a182884025dd` |
| research/agent_reports/2026-11-08/60-lean-verification.md | `7f394c7ca839386c6692a5ad622f26c299db8abb` |

Coordinator 90 mirrors have the same blob as 00 on both dates. Report findings were consumed at their stated scopes, not converted into source authority.


## Reproduction

```sh
python af_probe.py
g++ -O2 -std=c++17 -Wall -Wextra -Werror af_reference.cpp -o af_reference
time ./af_reference
cmp /workspace/af-rows-python.tsv /workspace/af-rows-cpp.tsv
python af_audit.py
```

The programs use /workspace for generated output, matching the actual execution environment. No network, external data, randomized seed or Lean installation is required. Full raw rows are regenerable; their shared SHA-256 is c112800c4e2bff84aebde90c10f4702950ba986019df6af058538a5cfb72f165.


### Executed File Hashes

```text
d43337a1bb3f894958182d1c3b03f3dcfd8fc24196d3caec58a1de288f18a215  /workspace/af-registration.md
8dc36326c09031be6704c6d553b6decab673bb7d94272fcfbbdb23a0abc46641  /workspace/af_probe.py
fa41e9d66aa7189ad6ca097b3c8c74e629373727017aeddf728447b1c0621d0b  /workspace/af_reference.cpp
9eb6650a3052fe6989aa09d9fbd972aaa697dde578de5acbd65552421404cc0d  /workspace/af_audit.py
f2413e6b40eeaedd1fd754fc8043077641e0ecad41b2a33d941dbd59b5b7710e  /workspace/af-results.json
464e8f9c3d69df002f1115d2444d85d7ceef7adaaa6afb5203edd811465dd593  /workspace/af-audit-results.json
5be59674a07ce758654c140973f81888849c829fc143fe1d0b358ff4a03e8842  /workspace/af-provenance.json
```


### Executed Artifact: af-registration.md

~~~markdown
# Frozen AF Frequency Test: 20261108-census-3

Scheduled trigger: 2026-11-08 19:00:01 EST. No platform run ID supplied.
Source main: 6144c73b05d5a85e6a9424708986860c6276f60d.
Question: does genuine arithmetic force nonzero additive frequencies to oppose the coherent frequency on the AF floor-two triangle?

Use genuine Mobius mu, N=R-1, X=R^2-1, I2=[ceil(R/3),floor((R-1)/2)], B=R-W. Define L=sum mu(a)mu(b) over a in I2, B<=b<R, 3a+b<=2R. Use q=2W+1 and the exact f,g,h conventions of Coordinator AF3, including the <= boundary and squareful zeros. K_R=max_{0<=y<R}(M(y)-1)^2/(y+1).

Choose the largest integer W>=1 with W=1 mod 3 and 4W<=R, 16K_R W^2<=R^2, W^6<=R^4 K_R. Empty admissible width means no test row. Thus 3 divides q. The width rule is fixed before any data.

Candidate H_DC: C0*(L-C0)<=0 for every admitted R, where C0=(W+1)F(0)G(0)/q. A strict positive rational product refutes it. This is a new laboratory candidate, NOT an assertion made by AF.
Candidate H_3: if R=1 mod 3, then C0*C3<=0, where C3 is the sum of the Fourier k=q/3 and 2q/3 contributions. The multiplicative sign mu(3n)=-mu(n) when 3 does not divide n motivates, but does not prove, this candidate. A strict positive rational product refutes it.
Rival mechanism: the third-root sector is controlled by a residue-specific backward prefix, not merely its sign or the zero-frequency sum. Test the pencil identity q*C3=F(0)*(G(0)-3*B_c), c=(2R-2) mod 3, B_c=sum_{B<=b<R,b=c mod 3}mu(b). Preserve both zero and nonzero sectors.

Primary held-out root range: every R=257..4095, excluding the previously inspected roots 317,549,1027,2002. A new question is tested; the old AF identity census is not rerun. Confirmation roots fixed now: 8209,10007,16381,20011,32771. Report first violations in the registered range, not smallest global violations. Development R<=256 may be searched ONLY afterwards and must be labeled retrospective.

Exact methods: multiplicative Mobius sieve and rational prefix sums; independent C++ trial factorization and direct ordered triangle enumeration. Compare all primary and confirmation rows byte-for-byte. At first falsifiers and confirmation fixtures, recover complete conductor-grouped Fourier contributions with exact residue convolution and Ramanujan sums; no floating DFT is needed. Keep the k=0 term and every mixed square term.

Full original Euler return at R=257,263 and each primary first falsifier <=1024: Q=P+E1+2m2*t_B+L+(J2-L)+Z and M(X)=2M(R-1)-Q. Compute Z directly from the complement, not by defining it as a remainder. Recombine all six squares and fifteen cross terms exactly. These fixtures are scope checks, not a complete-source bound.

Stop after decisive falsifiers and the fixed confirmation range. Do not fit a constant or infer an infinite estimate. Any new universal lemma is separately proved and labeled PAPER_PROOF / SELF_AUDIT, not Lean or independent Referee acceptance. No original-source code or report other than the owned daily report may be published.
~~~


### Executed Artifact: af_probe.py

~~~python
"""Exact held-out AF mode experiment. No floating-point sign decisions."""

from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from math import gcd
from pathlib import Path
import json
import platform
import time


CONFIRM = [8209, 10007, 16381, 20011, 32771]
PRIMARY = [r for r in range(257, 4096) if r not in {317, 549, 1027, 2002}]


def sieve(limit):
    mu = [1] * (limit + 1)
    mu[0] = 0
    prime = bytearray(b'\x01') * (limit + 1)
    prime[0:2] = b'\x00\x00'
    for p in range(2, limit + 1):
        if prime[p]:
            for n in range(p, limit + 1, p):
                mu[n] = -mu[n]
                if n > p:
                    prime[n] = 0
            for n in range(p * p, limit + 1, p * p):
                mu[n] = 0
    return mu


def prefixes(mu):
    m = [0] * len(mu)
    for n in range(1, len(mu)):
        m[n] = m[n - 1] + mu[n]
    return m


def histories(m):
    out, k = [F(0)] * len(m), F(0)
    for r in range(1, len(m)):
        k = max(k, F((m[r - 1] - 1) ** 2, r))
        out[r] = k
    return out


def width(r, k):
    low, high = 0, r // 4
    while low < high:
        w = (low + high + 1) // 2
        if 16 * k.numerator * w * w <= r * r * k.denominator and w ** 6 * k.denominator <= r ** 4 * k.numerator:
            low = w
        else:
            high = w - 1
    return low - (low - 1) % 3 if low else 0


def row(r, mu, m, k):
    w = width(r, k)
    assert w > 0 and w % 3 == 1
    q, lo, hi, b0 = 2 * w + 1, (r + 2) // 3, (r - 1) // 2, r - w
    top = min(hi, (r + w) // 3)
    f0, g0 = m[top] - m[lo - 1], m[r - 1] - m[b0 - 1]
    c = (2 * r - 2) % 3
    bc = sum(mu[b] for b in range(b0, r) if b % 3 == c)
    l = sum(mu[b] * (m[min(hi, (2 * r - b) // 3)] - m[lo - 1]) for b in range(b0, r))
    j = sum(mu[b] * (m[min(hi, (r * r - 1) // (3 * b))] - m[lo - 1]) for b in range(b0, r))
    n0, n3 = (w + 1) * f0 * g0, f0 * (g0 - 3 * bc)
    nr = q * l - n0 - n3
    assert abs(n3) <= 2 * w * abs(f0) < q * (abs(f0) + 1)
    assert abs(F(n3, q)) <= abs(f0)
    if r % 3 == 1:
        restricted = sum(mu[n] for n in range((b0 + 2) // 3, (r - 1) // 3 + 1) if n % 3)
        assert bc == -restricted
    return [r, w, k.numerator, k.denominator, f0, g0, bc, l, j, n0, n3, nr]


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def conductor_certificate(rec, mu):
    r, w = rec[:2]
    q = 2 * w + 1
    lo, hi = (r + 2) // 3, (r - 1) // 2
    fv = [(3 * a - r, mu[a]) for a in range(lo, min(hi, (r + w) // 3) + 1)]
    gd = [(d, mu[r - d]) for d in range(1, w + 1)]
    correlation = [0] * q
    for v, f in fv:
        for d, g in gd:
            correlation[(d - v) % q] += f * g
    assert sum(correlation[:w + 1]) == rec[7]
    ds = divisors(q)
    residue = {}
    for e in ds:
        hc = [0] * e
        for u in range(w + 1):
            hc[u % e] += 1
        residue[e] = sum(z * hc[s % e] for s, z in enumerate(correlation))
        # Separate residue aggregation: no circular correlation table used.
        ff, gg = [0] * e, [0] * e
        for v, f in fv:
            ff[v % e] += f
        for d, g in gd:
            gg[d % e] += g
        alt = sum(f * g * hc[(d - v) % e] for v, f in enumerate(ff) if f for d, g in enumerate(gg) if g)
        assert alt == residue[e]
    numerators = {e: sum(mu[e // d] * d * residue[d] for d in divisors(e)) for e in ds}
    assert sum(numerators.values()) == q * rec[7]
    assert numerators[1] == rec[9] and numerators[3] == rec[10]
    vals = [F(numerators[e], q) for e in ds]
    diag = sum(v * v for v in vals)
    cross = sum(2 * vals[i] * vals[j] for i in range(len(vals)) for j in range(i + 1, len(vals)))
    assert diag + cross == rec[7] ** 2
    return dict(R=r, W=w, q=q, L=rec[7], numerators=numerators,
                diagonal=str(diag), cross=str(cross), reconstructed_square=str(diag + cross))


def full_return(rec, mu, m):
    r, w = rec[:2]
    x, n, b0 = r * r - 1, r - 1, r - w
    lo, hi, a1 = (r + 2) // 3, n // 2, x // (2 * b0) + 1
    parts = [F(0), F(0), F(0)]
    total, sites = 0, Counter()
    for b in range(1, r):
        fl, hist = [0, 0, 0], [0, 0, 0]
        for a in range(1, r):
            sector = 0 if b >= b0 and a >= a1 else 1 if b >= b0 and lo <= a <= hi else 2
            fl[sector] += mu[a] * (x // (a * b))
            hist[sector] += mu[a] * (n // a)
            sites[sector] += 1
        total += mu[b] * sum(fl)
        for sector in range(3):
            parts[sector] += mu[b] * (fl[sector] - F((r + 1) * hist[sector], b))
    p = (r + 1) * sum((F(mu[b], b) for b in range(1, r)), F(0))
    tb = sum((F(mu[b] * (b - r - 1), b) for b in range(b0, r)), F(0))
    sep = 2 * (m[hi] - m[lo - 1]) * tb
    assert parts[1] == sep + rec[8]
    six = [p, parts[0], sep, F(rec[7]), F(rec[8] - rec[7]), parts[2]]
    q = 2 * w + 1
    eight = six[:3] + [F(rec[9], q), F(rec[10], q), F(rec[11], q)] + six[4:]
    for terms in [six, eight]:
        diag = sum(t * t for t in terms)
        cross = sum(2 * terms[i] * terms[j] for i in range(len(terms)) for j in range(i + 1, len(terms)))
        assert sum(terms) == total == 2 * m[n] - m[x]
        assert diag + cross == total * total
    k = F(rec[2], rec[3])
    return dict(R=r, W=w, M_N=m[n], M_X=m[x], Q=total, K=str(k),
                alpha=str(F((m[x] - 1) ** 2, r * r) / k), ordered_sites=sum(sites.values()),
                sector_sites=dict(sites), six_parts=list(map(str, six)),
                eight_parts=list(map(str, eight)), diagonal=str(diag), cross=str(cross), square=total * total)


def main():
    started = time.perf_counter()
    mu = sieve(max(CONFIRM))
    m = prefixes(mu)
    ks = histories(m)
    rows = [row(r, mu, m, ks[r]) for r in PRIMARY + CONFIRM]
    text = ''.join('\t'.join(map(str, rec)) + '\n' for rec in rows)
    Path('/workspace/af-rows-python.tsv').write_text(text)
    first_dc = next(rec for rec in rows[:len(PRIMARY)] if rec[9] * ((2 * rec[1] + 1) * rec[7] - rec[9]) > 0)
    first_3 = next(rec for rec in rows[:len(PRIMARY)] if rec[0] % 3 == 1 and rec[9] * rec[10] > 0)
    counts = Counter()
    for rec in rows:
        r, w = rec[:2]
        n0, n3 = rec[9:11]
        nn = (2 * w + 1) * rec[7] - n0
        counts['rows'] += 1
        counts['dc_zero'] += n0 == 0
        counts['dc_amplifies'] += n0 * nn > 0
        counts['dc_opposes'] += n0 * nn < 0
        counts['dc_product_zero'] += n0 * nn == 0
        counts['third_applicable'] += r % 3 == 1
        counts['third_amplifies'] += r % 3 == 1 and n0 * n3 > 0
        counts['third_opposes'] += r % 3 == 1 and n0 * n3 < 0
        counts['third_zero'] += r % 3 == 1 and n0 * n3 == 0
    fixture_rs = sorted({257, 263, first_dc[0], first_3[0], *CONFIRM})
    by_r = {rec[0]: rec for rec in rows}
    spectra = [conductor_certificate(by_r[r], mu) for r in fixture_rs]
    full_rs = sorted({257, 263, *[r for r in [first_dc[0], first_3[0]] if r <= 1024]})
    full_mu = sieve(max(full_rs) ** 2 - 1)
    full_m = prefixes(full_mu)
    full = [full_return(by_r[r], full_mu, full_m) for r in full_rs]
    strongest = max(rows[:len(PRIMARY)], key=lambda a: F(a[9] * ((2 * a[1] + 1) * a[7] - a[9]), (2 * a[1] + 1) ** 2))
    out = dict(status='PASS', python=platform.python_version(), primary_rows=len(PRIMARY), confirmation_rows=len(CONFIRM),
               row_columns=['R','W','K_num','K_den','F0','G0','B_c','L','J2','qC0','qC3','qCrest'],
               counts=dict(counts), first_dc=first_dc, first_3=first_3, strongest_dc_cross=strongest,
               confirmation=rows[-len(CONFIRM):], spectra=spectra, full=full,
               rows_sha256=sha256(text.encode()).hexdigest(), elapsed_seconds=time.perf_counter() - started)
    Path('/workspace/af-results.json').write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps({k:v for k,v in out.items() if k not in {'full','spectra'}}, indent=2))


if __name__ == '__main__':
    main()
~~~


### Executed Artifact: af_reference.cpp

~~~cpp
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <set>
#include <vector>

using i64 = std::int64_t;
using i128 = __int128_t;

int trial_mu(int n) {
    int sign = 1;
    for (int p = 2; p * p <= n; ++p) {
        if (n % p == 0) {
            n /= p;
            sign = -sign;
            if (n % p == 0) return 0;
        }
    }
    return n > 1 ? -sign : sign;
}

int main() {
    const int limit = 32771;
    std::vector<int> mu(limit + 1), m(limit + 1);
    for (int n = 1; n <= limit; ++n) {
        mu[n] = trial_mu(n);
        m[n] = m[n - 1] + mu[n];
    }
    std::vector<int> roots;
    const std::set<int> omitted{317, 549, 1027, 2002};
    for (int r = 257; r <= 4095; ++r) if (!omitted.count(r)) roots.push_back(r);
    for (int r : {8209, 10007, 16381, 20011, 32771}) roots.push_back(r);
    std::ofstream out("/workspace/af-rows-cpp.tsv");
    i64 kn = 0, kd = 1, y = 0, visits = 0;
    for (int r : roots) {
        while (y < r) {
            const i64 num = static_cast<i64>(m[y] - 1) * (m[y] - 1), den = y + 1;
            if (num * kd > kn * den) {
                const i64 g = std::gcd(num, den);
                kn = num / g;
                kd = den / g;
            }
            ++y;
        }
        i64 w = 1, best = 0;
        for (; 4 * w <= r; w += 3) {
            i128 w6 = static_cast<i128>(w) * w * w * w * w * w;
            i128 r4 = static_cast<i128>(r) * r * r * r;
            if (16 * kn * w * w <= static_cast<i64>(r) * r * kd && w6 * kd <= r4 * kn) best = w;
        }
        w = best;
        assert(w > 0);
        const i64 q = 2 * w + 1, lo = (r + 2) / 3, hi = (r - 1) / 2, b0 = r - w;
        i64 f0 = 0, g0 = 0, bc = 0, l = 0, j = 0;
        for (i64 a = lo; a <= hi; ++a) if (3 * a - r <= w) f0 += mu[a];
        for (i64 b = b0; b < r; ++b) {
            g0 += mu[b];
            if (b % 3 == (2 * r - 2) % 3) bc += mu[b];
            for (i64 a = lo; a <= hi; ++a) {
                if (3 * a + b <= 2 * r) l += mu[a] * mu[b];
                if (3 * a * b <= static_cast<i64>(r) * r - 1) j += mu[a] * mu[b];
                ++visits;
            }
        }
        const i64 n0 = (w + 1) * f0 * g0, n3 = f0 * (g0 - 3 * bc), nr = q * l - n0 - n3;
        out << r << '\t' << w << '\t' << kn << '\t' << kd << '\t' << f0 << '\t' << g0 << '\t' << bc
            << '\t' << l << '\t' << j << '\t' << n0 << '\t' << n3 << '\t' << nr << '\n';
    }
    std::cout << "PASS rows=" << roots.size() << " trial_coefficients=" << limit << " direct_ordered_visits=" << visits << '\n';
}
~~~


### Executed Artifact: af_audit.py

~~~python
"""Independent exact cube-root arithmetic and post-discovery minimization."""

from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import json
import time


def trial_mu(n):
    value, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            value = -value
            if n % p == 0:
                return 0
        p += 1
    return -value if n > 1 else value


def mul(x, y):
    a, b = x
    c, d = y
    return a * c - b * d, a * d + b * c - b * d


ROOT = [(1, 0), (0, 1), (-1, -1)]


def poly(terms):
    a = b = 0
    for coefficient, exponent in terms:
        c, d = ROOT[exponent % 3]
        a += coefficient * c
        b += coefficient * d
    return a, b


def cube_numerator(r, w, mu):
    lo, hi = (r + 2) // 3, (r - 1) // 2
    ff = poly((mu[a], -(3 * a - r)) for a in range(lo, min(hi, (r + w) // 3) + 1))
    gg = poly((mu[r - d], d) for d in range(1, w + 1))
    hh = poly((1, -u) for u in range(w + 1))
    a, b = mul(mul(ff, gg), hh)
    return 2 * a - b


def minimal_row(r, mu):
    m, partial = [0], 0
    for n in range(1, r):
        partial += mu[n]
        m.append(partial)
    k = max(F((m[y] - 1) ** 2, y + 1) for y in range(r))
    ws = [w for w in range(1, r // 4 + 1, 3) if 16 * k * w * w <= r * r and w ** 6 <= r ** 4 * k]
    if not ws:
        return None
    w = max(ws)
    lo, hi, q = (r + 2) // 3, (r - 1) // 2, 2 * w + 1
    f0 = sum(mu[a] for a in range(lo, min(hi, (r + w) // 3) + 1))
    g0 = sum(mu[b] for b in range(r - w, r))
    l = sum(mu[a] * mu[b] for a in range(lo, hi + 1) for b in range(r - w, r) if 3 * a + b <= 2 * r)
    n0 = (w + 1) * f0 * g0
    n3 = cube_numerator(r, w, mu)
    return dict(R=r, W=w, K=str(k), F0=f0, G0=g0, L=l, q=q, C0=str(F(n0, q)), C3=str(F(n3, q)),
                nonzero=str(F(q*l-n0, q)), dc_failure=n0*(q*l-n0)>0,
                third_failure=(r % 3 == 1 and n0*n3>0))


start = time.perf_counter()
raw = Path('/workspace/af-rows-python.tsv').read_text()
rows = [list(map(int, line.split())) for line in raw.splitlines()]
results = json.loads(Path('/workspace/af-results.json').read_text())
limit = max(max(r[0] for r in rows), max(item['R']**2-1 for item in results['full']))
mu = [0] + [trial_mu(n) for n in range(1, limit + 1)]
zero_residue_coherence = 0
for rec in rows:
    assert cube_numerator(rec[0], rec[1], mu) == rec[10]
    r, w, _, _, f0, g0, bc = rec[:7]
    assert rec[9] * rec[10] == (w + 1) * f0 * f0 * g0 * (g0 - 3 * bc)
    assert abs(rec[10]) <= 2 * w * abs(f0)
    if r % 3 == 1 and bc == 0 and f0 * g0 != 0:
        assert rec[9] == (w + 1) * rec[10]
        zero_residue_coherence += 1
small = [v for r in range(2, 257) if (v := minimal_row(r, mu)) is not None]
dc = next(v for v in small if v['dc_failure'])
third = next(v for v in small if v['third_failure'])
full = []
for expected in results['full']:
    r = expected['R']
    x = r*r-1
    mn = sum(mu[1:r])
    mx = sum(mu[1:x+1])
    q = sum(mu[a]*mu[b]*(x//(a*b)) for a in range(1,r) for b in range(1,r))
    assert (mn,mx,q) == (expected['M_N'],expected['M_X'],expected['Q'])
    full.append(dict(R=r, M_N=mn, M_X=mx, Q=q))
certificates = []
for r in [258,307]:
    rec = next(row for row in rows if row[0]==r)
    w, q = rec[1], 2*rec[1]+1
    lo, hi = (r+2)//3, min((r-1)//2,(r+w)//3)
    positive = [a for a in range(lo,hi+1) if mu[a]==1]
    negative = [a for a in range(lo,hi+1) if mu[a]==-1]
    by_residue = [sum(mu[b] for b in range(r-w,r) if b%3==c) for c in range(3)]
    certificates.append(dict(R=r,W=w,row_interval=[lo,hi],column_interval=[r-w,r-1],
                             positive_rows=positive,negative_rows=negative,backward_residue_sums=by_residue,
                             C0=str(F(rec[9],q)),C3=str(F(rec[10],q)),Crest=str(F(rec[11],q)),
                             nonzero=str(F(q*rec[7]-rec[9],q)),
                             dc_cross=str(2*F(rec[9],q)*F(q*rec[7]-rec[9],q)),
                             third_cross=str(2*F(rec[9],q)*F(rec[10],q))))
out=dict(status='PASS', independent_trial_coefficients=limit, exact_cyclotomic_cases=len(rows),
         zero_residue_coherence=zero_residue_coherence,
         retrospective_roots=[2,256], retrospective_admitted=len(small), retrospective_first_dc=dc,
         retrospective_first_third=third, full=full, certificates=certificates,
         rows_sha256=sha256(raw.encode()).hexdigest(),elapsed_seconds=time.perf_counter()-start)
Path('/workspace/af-audit-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
~~~


### Executed Artifact: af-results.json

~~~json
{
  "status": "PASS",
  "python": "3.12.14",
  "primary_rows": 3835,
  "confirmation_rows": 5,
  "row_columns": [
    "R",
    "W",
    "K_num",
    "K_den",
    "F0",
    "G0",
    "B_c",
    "L",
    "J2",
    "qC0",
    "qC3",
    "qCrest"
  ],
  "counts": {
    "rows": 3840,
    "dc_zero": 386,
    "dc_amplifies": 1710,
    "dc_opposes": 1744,
    "dc_product_zero": 386,
    "third_applicable": 1280,
    "third_amplifies": 612,
    "third_opposes": 501,
    "third_zero": 167
  },
  "first_dc": [
    258,
    43,
    3,
    2,
    4,
    -2,
    1,
    -7,
    -15,
    -352,
    -20,
    -237
  ],
  "first_3": [
    307,
    46,
    3,
    2,
    -4,
    1,
    0,
    12,
    9,
    -188,
    -4,
    1308
  ],
  "strongest_dc_cross": [
    2899,
    217,
    3,
    2,
    -12,
    -24,
    -6,
    214,
    227,
    62784,
    72,
    30234
  ],
  "confirmation": [
    [
      8209,
      433,
      3,
      2,
      -9,
      26,
      11,
      -232,
      -187,
      -101556,
      63,
      -99651
    ],
    [
      10007,
      496,
      3,
      2,
      -5,
      -1,
      5,
      30,
      24,
      2485,
      80,
      27225
    ],
    [
      16381,
      688,
      3,
      2,
      0,
      -7,
      -10,
      13,
      31,
      0,
      0,
      17901
    ],
    [
      20011,
      787,
      3,
      2,
      -6,
      -17,
      -16,
      -37,
      19,
      80376,
      -186,
      -138465
    ],
    [
      32771,
      1093,
      3,
      2,
      5,
      -25,
      -16,
      13,
      -21,
      -136750,
      115,
      165066
    ]
  ],
  "spectra": [
    {
      "R": 257,
      "W": 43,
      "q": 87,
      "L": 1,
      "numerators": {
        "1": 0,
        "3": 12,
        "29": -58,
        "87": 133
      },
      "diagonal": "21197/7569",
      "cross": "-13628/7569",
      "reconstructed_square": "1"
    },
    {
      "R": 258,
      "W": 43,
      "q": 87,
      "L": -7,
      "numerators": {
        "1": -352,
        "3": -20,
        "29": -344,
        "87": 107
      },
      "diagonal": "254089/7569",
      "cross": "116792/7569",
      "reconstructed_square": "49"
    },
    {
      "R": 263,
      "W": 43,
      "q": 87,
      "L": -12,
      "numerators": {
        "1": 0,
        "3": 0,
        "29": 0,
        "87": -1044
      },
      "diagonal": "144",
      "cross": "0",
      "reconstructed_square": "144"
    },
    {
      "R": 307,
      "W": 46,
      "q": 93,
      "L": 12,
      "numerators": {
        "1": -188,
        "3": -4,
        "31": -246,
        "93": 1554
      },
      "diagonal": "2510792/8649",
      "cross": "-1265336/8649",
      "reconstructed_square": "144"
    },
    {
      "R": 8209,
      "W": 433,
      "q": 867,
      "L": -232,
      "numerators": {
        "1": -101556,
        "3": 63,
        "17": -376,
        "51": -4058,
        "289": -10778,
        "867": -84439
      },
      "diagonal": "17576343850/751689",
      "cross": "22882564886/751689",
      "reconstructed_square": "53824"
    },
    {
      "R": 10007,
      "W": 496,
      "q": 993,
      "L": 30,
      "numerators": {
        "1": 2485,
        "3": 80,
        "331": -7781,
        "993": 35006
      },
      "diagonal": "1292145622/986049",
      "cross": "-404701522/986049",
      "reconstructed_square": "900"
    },
    {
      "R": 16381,
      "W": 688,
      "q": 1377,
      "L": 13,
      "numerators": {
        "1": 0,
        "3": 0,
        "9": -396,
        "17": -1972,
        "27": -2358,
        "51": 2839,
        "81": -23490,
        "153": -28776,
        "459": 72891,
        "1377": -837
      },
      "diagonal": "6711302411/1896129",
      "cross": "-6390856610/1896129",
      "reconstructed_square": "169"
    },
    {
      "R": 20011,
      "W": 787,
      "q": 1575,
      "L": -37,
      "numerators": {
        "1": 80376,
        "3": -186,
        "5": -1031,
        "7": 1566,
        "9": -1557,
        "15": -1609,
        "21": 1488,
        "25": -3245,
        "35": 5574,
        "45": -6378,
        "63": -291,
        "75": -8380,
        "105": 2337,
        "175": -1340,
        "225": -78690,
        "315": -16659,
        "525": 15800,
        "1575": -46050
      },
      "diagonal": "1718978231/275625",
      "cross": "-1341647606/275625",
      "reconstructed_square": "1369"
    },
    {
      "R": 32771,
      "W": 1093,
      "q": 2187,
      "L": 13,
      "numerators": {
        "1": -136750,
        "3": 115,
        "9": -660,
        "27": -4644,
        "81": -14958,
        "243": 10125,
        "729": -139725,
        "2187": 314928
      },
      "diagonal": "137751556259/4782969",
      "cross": "-136943234498/4782969",
      "reconstructed_square": "169"
    }
  ],
  "full": [
    {
      "R": 257,
      "W": 43,
      "M_N": -1,
      "M_X": 4,
      "Q": -6,
      "K": "3/2",
      "alpha": "6/66049",
      "ordered_sites": 65536,
      "sector_sites": {
        "2": 59301,
        "1": 1849,
        "0": 4386
      },
      "six_parts": [
        "292411769188101778286374124798202906425056742896535284600896101987447219213750783076400525391746612/249094305883366840590428818713591912057675141827942667109475808840690505301863190513663568772226435",
        "-81518364952728852615093749863438437867070876/257105190981748683574851171866576472649853645",
        "-163036729905457705230187499726876875734141752/257105190981748683574851171866576472649853645",
        "1",
        "-9",
        "63244584044213462883738792786967569422417512482927614981442407138423837136821702953631188782381906/35584900840480977227204116959084558865382163118277523872782258405812929328837598644809081253175205"
      ],
      "eight_parts": [
        "292411769188101778286374124798202906425056742896535284600896101987447219213750783076400525391746612/249094305883366840590428818713591912057675141827942667109475808840690505301863190513663568772226435",
        "-81518364952728852615093749863438437867070876/257105190981748683574851171866576472649853645",
        "-163036729905457705230187499726876875734141752/257105190981748683574851171866576472649853645",
        "0",
        "4/29",
        "25/29",
        "-9",
        "63244584044213462883738792786967569422417512482927614981442407138423837136821702953631188782381906/35584900840480977227204116959084558865382163118277523872782258405812929328837598644809081253175205"
      ],
      "diagonal": "41868054244972637385928863293831647316948185563272951554056730219215630697055868095741452545414071394554016774608875615745345145561618294123031604617833799675903747862261671696130187436008550402/482341849855147538570529058478240835110493034882391614545550934905793289703162089062626487912478770370461753768458584531436776192862368828422017781682535706184364038797891982020199227091526775",
      "cross": "-24503747650187325997389817188614977252970436307506853430416896562607072267742032889486898980564835661217393638944366572613621202618573016299838964477262514253266642465537560343403015260713586502/482341849855147538570529058478240835110493034882391614545550934905793289703162089062626487912478770370461753768458584531436776192862368828422017781682535706184364038797891982020199227091526775",
      "square": 36
    },
    {
      "R": 258,
      "W": 43,
      "M_N": -2,
      "M_X": 23,
      "Q": -27,
      "K": "3/2",
      "alpha": "242/49923",
      "ordered_sites": 66049,
      "sector_sites": {
        "2": 59771,
        "1": 1849,
        "0": 4429
      },
      "six_parts": [
        "5441746881716756073633757422515716820179698166400180014092769764937892485026624049054867141222229527/31885032907147725351716164582284604866594996050277155377144600349403136379431159672198796507743718145",
        "0",
        "-61655591800938947599266446591535462133609861/307574365699055104339372890011641099764031245",
        "-7",
        "-8",
        "-29359272879399930887122216928453007731983333966562012928245662628477768174559118149199946943353355122/2452694839011363488593551121714200374353461234636704259780353873031010490725473820938368962134132165"
      ],
      "eight_parts": [
        "5441746881716756073633757422515716820179698166400180014092769764937892485026624049054867141222229527/31885032907147725351716164582284604866594996050277155377144600349403136379431159672198796507743718145",
        "0",
        "-61655591800938947599266446591535462133609861/307574365699055104339372890011641099764031245",
        "-352/87",
        "-20/87",
        "-79/29",
        "-8",
        "-29359272879399930887122216928453007731983333966562012928245662628477768174559118149199946943353355122/2452694839011363488593551121714200374353461234636704259780353873031010490725473820938368962134132165"
      ],
      "diagonal": "12371033777124252331506939505983884491829071736180691877698283813756016095357572320890153839317504746541619594223037466283511322905286104467784852652545003647510987385889603686709098682601134204401128469/53508174920520701371071470317867617650097052799462696939404111088224851836389489403480607800265599288807244189984603141001305332431353234097202569881361856324164992322650942758336582546850300484328475",
      "cross": "26636425739935338968004162355741608775091679754627614191127313169559900893370365454247209247076117134998861420275738223506440264437170403189075820790967789612805292017322933584118269994052734848674329806/53508174920520701371071470317867617650097052799462696939404111088224851836389489403480607800265599288807244189984603141001305332431353234097202569881361856324164992322650942758336582546850300484328475",
      "square": 729
    },
    {
      "R": 263,
      "W": 43,
      "M_N": -1,
      "M_X": 64,
      "Q": -66,
      "K": "3/2",
      "alpha": "2646/69169",
      "ordered_sites": 68644,
      "sector_sites": {
        "2": 62237,
        "1": 1892,
        "0": 4515
      },
      "six_parts": [
        "294704788746822704652769439769126657683582438530378605850684592495060599779016233741814864173439813816/250249197665189723214984443236718565468124362940054037656983378499860979462808192578772372591079484835",
        "1017605431299469405894447937658816344489301/1282024146380544281221558887967715384401055",
        "-4070421725197877623577791750635265377957204/1282024146380544281221558887967715384401055",
        "-12",
        "0",
        "-139076381935504570617973268204128550967067927106323242027979393213926693416518932882427252449566264777/2634202080686207612789309928807563847032888030947937238494561878945905046976928342934446027274520893"
      ],
      "eight_parts": [
        "294704788746822704652769439769126657683582438530378605850684592495060599779016233741814864173439813816/250249197665189723214984443236718565468124362940054037656983378499860979462808192578772372591079484835",
        "1017605431299469405894447937658816344489301/1282024146380544281221558887967715384401055",
        "-4070421725197877623577791750635265377957204/1282024146380544281221558887967715384401055",
        "0",
        "0",
        "-12",
        "0",
        "-139076381935504570617973268204128550967067927106323242027979393213926693416518932882427252449566264777/2634202080686207612789309928807563847032888030947937238494561878945905046976928342934446027274520893"
      ],
      "diagonal": "184339268274794216761198155053656757259234145492507973226748108608509893943619756705863339587939101450740208779898905549470648397760798984039607652628735640561214582287358740464271769369521679320077348389234/62624660932071197616881598445789417384882504662970051693710905732116634007989002235833581620884037329620841324755542794057541503298185968441702907450891697885716184710669614262871946356914632808994977225",
      "cross": "88453754745307920057938087776201944869314044819389571951056596760590163795180337033427741952631765157088176030736238861444002390606099094492450212227348595428965118312318099264798428961198461195904772402866/62624660932071197616881598445789417384882504662970051693710905732116634007989002235833581620884037329620841324755542794057541503298185968441702907450891697885716184710669614262871946356914632808994977225",
      "square": 4356
    },
    {
      "R": 307,
      "W": 46,
      "M_N": -1,
      "M_X": -67,
      "Q": 65,
      "K": "3/2",
      "alpha": "9248/282747",
      "ordered_sites": 93636,
      "sector_sites": {
        "2": 85494,
        "1": 2346,
        "0": 5796
      },
      "six_parts": [
        "8426200527571782374668815180898329907919612406903915478614464804036730084699558765506845916939771838871641100708376/10123033661253699873485036855442975305004562734269236534366357397918166491119599083034433697462982329114885676830215",
        "173127275071071507433929832515924725044686956080022/236533354191143274587841220500415492839227750442645",
        "0",
        "12",
        "-3",
        "144486430072517104444592385401364756360174772434681899083251625372752578097941028758864022863977761640028945165077740058/2654259425980720106827776663497148124972196348925393819310858909734143253971558879571628515474793966693923024464882373"
      ],
      "eight_parts": [
        "8426200527571782374668815180898329907919612406903915478614464804036730084699558765506845916939771838871641100708376/10123033661253699873485036855442975305004562734269236534366357397918166491119599083034433697462982329114885676830215",
        "173127275071071507433929832515924725044686956080022/236533354191143274587841220500415492839227750442645",
        "0",
        "-188/93",
        "-4/93",
        "436/31",
        "-3",
        "144486430072517104444592385401364756360174772434681899083251625372752578097941028758864022863977761640028945165077740058/2654259425980720106827776663497148124972196348925393819310858909734143253971558879571628515474793966693923024464882373"
      ],
      "diagonal": "559269667344222216526494655213306165025116832151183814864416627375860956832883618391454623343454285531760092495888149798436543398134257416178474113244653957444561163748964762117930404189348550884274592497864905110621753993140404330070861617/176127327510187544990776951242525085342019328211074210882164463457464789213507590676333796945998896060737322111097394928458502019054999434412134442401889178174107271367049684271397953144569779119214532641360327070309409225688118152778225",
      "cross": "184868291386320161059537963786362320544914829540604726112728230731927777594185952216055668753391050324855093423498343774300627632373115194212793905903327820341042057776820153928725947846458765894406807911882476761435499985391894865417139008/176127327510187544990776951242525085342019328211074210882164463457464789213507590676333796945998896060737322111097394928458502019054999434412134442401889178174107271367049684271397953144569779119214532641360327070309409225688118152778225",
      "square": 4225
    }
  ],
  "rows_sha256": "c112800c4e2bff84aebde90c10f4702950ba986019df6af058538a5cfb72f165",
  "elapsed_seconds": 0.78769153799999
}
~~~


### Executed Artifact: af-audit-results.json

~~~json
{
  "status": "PASS",
  "independent_trial_coefficients": 94248,
  "exact_cyclotomic_cases": 3840,
  "zero_residue_coherence": 80,
  "retrospective_roots": [
    2,
    256
  ],
  "retrospective_admitted": 253,
  "retrospective_first_dc": {
    "R": 6,
    "W": 1,
    "K": "3/2",
    "F0": -1,
    "G0": -1,
    "L": 1,
    "q": 3,
    "C0": "2/3",
    "C3": "1/3",
    "nonzero": "1/3",
    "dc_failure": true,
    "third_failure": false
  },
  "retrospective_first_third": {
    "R": 28,
    "W": 4,
    "K": "3/2",
    "F0": 1,
    "G0": 1,
    "L": 1,
    "q": 9,
    "C0": "5/9",
    "C3": "1/9",
    "nonzero": "4/9",
    "dc_failure": true,
    "third_failure": true
  },
  "full": [
    {
      "R": 257,
      "M_N": -1,
      "M_X": 4,
      "Q": -6
    },
    {
      "R": 258,
      "M_N": -2,
      "M_X": 23,
      "Q": -27
    },
    {
      "R": 263,
      "M_N": -1,
      "M_X": 64,
      "Q": -66
    },
    {
      "R": 307,
      "M_N": -1,
      "M_X": -67,
      "Q": 65
    }
  ],
  "certificates": [
    {
      "R": 258,
      "W": 43,
      "row_interval": [
        86,
        100
      ],
      "column_interval": [
        215,
        257
      ],
      "positive_rows": [
        86,
        87,
        91,
        93,
        94,
        95
      ],
      "negative_rows": [
        89,
        97
      ],
      "backward_residue_sums": [
        -1,
        1,
        -2
      ],
      "C0": "-352/87",
      "C3": "-20/87",
      "Crest": "-79/29",
      "nonzero": "-257/87",
      "dc_cross": "180928/7569",
      "third_cross": "14080/7569"
    },
    {
      "R": 307,
      "W": 46,
      "row_interval": [
        103,
        117
      ],
      "column_interval": [
        261,
        306
      ],
      "positive_rows": [
        106,
        111,
        115
      ],
      "negative_rows": [
        103,
        105,
        107,
        109,
        110,
        113,
        114
      ],
      "backward_residue_sums": [
        0,
        2,
        -1
      ],
      "C0": "-188/93",
      "C3": "-4/93",
      "Crest": "436/31",
      "nonzero": "1304/93",
      "dc_cross": "-490304/8649",
      "third_cross": "1504/8649"
    }
  ],
  "rows_sha256": "c112800c4e2bff84aebde90c10f4702950ba986019df6af058538a5cfb72f165",
  "elapsed_seconds": 0.5463829739999255
}
~~~


### Prepublication Freshness - 20261108-census-3

At 2026-11-09 00:18:35 UTC, main was 6144c73b05d5a85e6a9424708986860c6276f60d, unchanged from intake, and the direct open-PR collection was empty. The prior report/checkpoint prefix is unchanged. Validation passed fourteen A-N sections, balanced fences, consistent table columns, identical independent row files and compilation of both Python programs. This run's complete scripts, exact JSON certificates and hashes are embedded above. All local computation sessions are finished. Publication remains subject to the actual write and immutable readback, not inferred from this prose.

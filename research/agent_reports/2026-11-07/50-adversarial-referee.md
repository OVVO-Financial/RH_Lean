# RH | Adversarial Referee - 2026-11-07

## Early Checkpoint - Scheduled 04:13 EST Invocation

Actual trigger: 2026-11-07T04:13:01-05:00, America/New_York.
RUN_ID_UNAVAILABLE; run label 20261107-referee-1.
Execution: IN_PROGRESS / PARTIAL. Mathematical verdicts and computation PENDING.

Main: 1c057c1d65b6d4cb4d59d207f69a815c52353314.
AGENTS blob: 48b2a58ab5fcd402321a4dace511c7d54bf688a1.
Proof-contract blob: 7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c.
baseline_ack=PAID_BASELINE_EXACT_CONSUMER_V1, blob 13d58dd12d90fbf1160812c7c93442dc5d0576ac.
deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1, blob ffd8f1c65cc4da656174956d4e03b48bea46768b.

Selected route: CODIV. Independently review 20261107-analytic-1/GL1-GL4
(report blob 6712040159ca37ef3257cf507ec8198fd26fbb91): actual triangular
short-lag covariance, large-gcd support bound, explicit lower-count proof,
and complete shell return. The new adversarial investigation tests the
uncovered near-window cutoff G close to h: exact primitive-lag admission,
parity, squarefree gcd gaps, and whether a corrected lower theorem survives.
No claim is attributed to the author beyond the stated t>=10^10 range.

The canonical actual-prime VF von Koch estimate remains OPEN. Existing native
all-prefix 7/8 and strict slot results are established inputs, not new findings.
eta_gate=SEARCH_BROAD; net_endpoint_gain=UNKNOWN.

Intake reports commit: f14d6b87984cd1729b85803660c54dda066fd382.
Read available November 7 Owner SG, Analytic GL, Wheel DI and Census SC reports,
and relevant November 6 reports from all seven roles. Coordinator and Lean:
TODAY=PENDING, YESTERDAY=CARRY_FORWARD. Yesterday's own CORR4/NYMAN reviews
are preserved, not rescanned as new work. External inbox blob
038018145c0fddb2f6306c0712373adf9cd1ea52 has no new November entry; its older
routing is superseded, and its exact-carrier cautions remain valid.

Open PR discovery returned only #1101, an unmerged instruction proposal;
it is not current authority. Main contains #1100. Material source and exact-head
CI verification are continuing. No local Lean, source edits, PR creation,
agent launch, schedule change, or merge is authorized or attempted.

Finite-test preregistration: independently reconstruct T_ge and W_ge by direct
gcd scanning and primitive-pair enumeration on X=8..64 with 2<=G<=h<=min(X,16),
then declared held-out fixtures. Test exact forward halo and all-mask restoration.
For the new near-cutoff identity test h<=2G, k=1 admission and even-g vanishing.
Construct CRT squareful gcd gaps algebraically, with small direct fixtures.
All new deductions are PAPER_PROOF / SELF_AUDIT until separately reviewed.


## Final CODIV Referee Synthesis - Scheduled 2026-11-07 04:13 EST Invocation

This completes the same scheduled invocation as the checkpoint above, not a
new launch. RUN_ID_UNAVAILABLE. Research and exact checks are finished;
publication is PENDING_READBACK until the receipt appended after verification.
Main was re-fetched at closeout and remains
**1c057c1d65b6d4cb4d59d207f69a815c52353314**.

### A. Most Important Mathematical Finding

**The genuine large-gcd support has an explicit positive fixed-ratio profile,
but can disappear completely when the gcd cutoff approaches the window length.**
This identifies the precise quantifier boundary of the new support-only method.

Independent reconstruction accepts **20261107-analytic-1/GL1-GL4** at their
stated scopes, including GL3's explicit condition
min(G,X/G,floor(h/(4G))) >= 10^10. Its lower bound is for the absolute
squarefree support W_ge, not the signed covariance T_ge. No counterexample
to that submitted theorem was found.

The new source-exact result below is: along any integer sequence with
G -> infinity, X/G -> infinity, h/G -> tau > 1 fixed, and 2<=G<=h<=X,

~~~text
W_ge(X,h,G)/(XG) -> Phi(tau),

Phi(tau) = 6 sum_(1<=k<tau) A(k)
              [tau log(tau/k) - tau + k] > 0,

A(k) = product_(p|k) [(1-1/p)(1-1/p^2)]
       product_(p not dividing k) [1-5/p^2+4/p^3].
~~~

Every local factor comes from the actual squarefree and coprime conditions.
No density or independence assumption is substituted for the arithmetic.
The proof includes an elementary large-prime tail bound valid for arbitrarily
unbalanced growing G and X/G. This extends support sharpness to fixed h/G,
which GL3's growing primitive-lag condition does not cover.

Conversely, arbitrary-length squareful runs in the exact gcd labels give
W_ge=T_ge=0 with G, X/G, and h-G all tending to infinity. Thus growth of
these three parameters alone is not a valid replacement for GL3's
hypotheses. This refutes only that explicitly stated strengthening.

New claims **20261107-referee-1/NC1-NC2, PF1-PF2** are
**PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED**.
The classical CRT/squarefree-density method is not claimed as a discovery.
The original-carrier profile and its cutoff application are this invocation's
new derivation; no literature-priority claim is made.

**INDEPENDENT_COMPONENT_ADVANCE; eta_gate=SEARCH_BROAD;
net_endpoint_gain=UNKNOWN; NEW_VERIFIED_ENDPOINT_GAIN=NONE.**
Existing strict endpoint results are preserved, not reset to zero.
No new Mertens exponent, actual-prime VF bound, or RH proof is claimed.

### B. Current Authoritative Objective And Source Evidence

The canonical statement remains

~~~text
exists C>=0, forall natural R>=2,
  |pi(R^2)-vfCanonical(R^2)| <= C R log R.
~~~

The inspected definition is VFCanonicalSquareVonKochStatement.
Its terminal riemannHypothesis_of_vfCanonicalSquare explicitly takes both
ClassicalVonKochRHCriterion and the unproved arithmetic statement.
The fixed phase vfCanonical=vfMid+sqrt(2) is unchanged.

baseline_ack=PAID_BASELINE_EXACT_CONSUMER_V1.
deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1.
The established native all-prefix signed energy, strict Mertens growth,
and explicit fixed-slot boundary are inputs, not tasks to repeat.
Write b_star=7/8-delta_star with
delta_star=1/(288*explicitSlotCount), explicitSlotCount>=2.
This is an every-positive-loss growth boundary, not a no-loss power envelope
at b_star. The actual Hecke boundary can be stronger than this explicit
comparator. The new support theorems below require no Mertens or zero-free input.

Material source blobs at the pinned main:

| File | Blob SHA | Inspected content |
| --- | --- | --- |
| AGENTS.md | 48b2a58ab5fcd402321a4dace511c7d54bf688a1 | Current instructions and own-report-only permissions |
| CURRENT_PROOF_CONTRACT.md | 7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c | Canonical objective, distinct source carriers |
| docs/RHLEAN_PAID_BASELINE_EXACT_CONSUMER_20261106.md | 13d58dd12d90fbf1160812c7c93442dc5d0576ac | Paid input and complete-consumer correction |
| docs/RHLEAN_INDEPENDENT_MULTIFRONT_NO_PIGEONHOLING_20261104.md | ffd8f1c65cc4da656174956d4e03b48bea46768b | Independent route selection |
| RHLean/Analysis/DeterministicTGreenKuboComparison.lean | 802a58b4e1994a5f8c14f1080ac42d0f5f28a0d5 | Actual mu, prefix length, full signed square |
| research/VF_919_SEVEN_EIGHTHS_SQUARE_SHELL_BRIDGE_20261019.lean | 55839f2013fc5b8d352dcea0e2ed4bb47d763693 | Literal [R^2,(R+1)^2) shell and cross-boundary subtraction |
| research/VF_919_SEVEN_EIGHTHS_DYADIC_SHELL_COVARIANCE_20261019.lean | 4ace115a6ec7537af5f871a97486e2b8cd5086e5 | Dyadic signed identity, conditional bound, partial-prefix Cauchy |
| research/oai_434/VF919NativeStrictMertens.lean | b33a4883e1ddb0551b0f11f062bce46680d87450 | Actual strict growth and fixed-power distinction |
| research/oai_434/VF919ExplicitFixedSourceSlotCount.lean | bad5aab0a60e96d19e7c9550cd7c0a072288bc0f | native_beta_le_explicit_slot_count |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb | Canonical statement and explicit terminal hypotheses |
| research/SQUARE_SHELL_LONG_LAG_FIVE_SIXTHS_20261019.md | 451824604acc988dfb848bc602a26478d0679d44 | Prior large-gcd counting and common-sign extraction |
| research/NYMAN_RADICAL_INCREMENT_20261106.lean | c5ebb3d5d96898549ad039fd32e1a26955c5b8f8 | Latest merged source identity, not a norm bound |

The stable selector, broad-search policy, complete-return contract, persistent
engine, Referee role instructions and dynamic protocol were retrieved from
this same main. Their relevant source/permission requirements were read.
No unmerged reporting-branch copy was treated as policy.

**Verified CI and merge scope.** PR #1091 is human-merged; exact head
6778fd4c25b0f369d311e6e71223e168e329b4bf. Its
[dedicated job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41898325686/job/126813711885)
was retrieved and is completed/success. The log prints
native_beta_le_explicit_slot_count with only propext, Classical.choice,
Quot.sound. The checkout log identifies synthetic merge 3b4c687 of that
exact PR head into 72ab5bdd0f9d8876f512e6273b50410328444e6e. Its tested
file equals the current main file byte-for-byte. This is relevant PR-head
evidence, not a new build of today's complete main.

PR #1100 is human-merged at 2026-11-07T05:19:51Z, head
e52207d527da684346e151d4ff680696c88e8fa7, merge equal to current main.
The [radical-increment job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42328802826/job/128270266477)
is completed/success. Its retrieved log shows warning-fatal compilation and
eleven declaration/standard-axiom audits at synthetic merge
c004afeecb0e4d81b734e2b9796cf2a6e43468b4, incorporating that exact head;
its tested source equals current main byte-for-byte. This updates
yesterday's unmerged status, not its
mathematical scope. No new claim in this report is certified by either job.
Historical shell declarations were source-inspected; no fresh exact-head
CI audit of their whole dependency chain is asserted.

The open-PR search returned only non-draft **#1101**, head
690477c55070aabafefbaff883880a5c37c44370, an instruction proposal.
A direct PR check confirmed open/unmerged. It is not current authority.
No new proof PR or CI run was requested.

### C. Highest-Risk Mechanisms Selected For Review

1. Extending GL3's lower support bound to a near-window cutoff after removing
   the growing primitive-lag hypothesis. NC2 disproves that extension,
   while PF1 supplies a positive theorem for every fixed ratio tau>1.
2. Interpreting an absolute squarefree support asymptotic as a lower bound
   or favorable sign for genuine mu(n)mu(n+d). No such implication is valid.
3. Paying only T_ge and suppressing T_lt, the full forward halo, or the
   translation error. The complete return below retains all three.
4. Treating fixed-k or fixed-tau estimates as uniform when h/G grows.
   PF1 does not establish a rate or a growing-tau limit.
5. Treating the existing all-prefix Mertens bound as the stronger local
   sum-of-squared-maximal-shell norm. This optional CODIV consumer is
   distinct from the already completed native replay.

Review sequence: the submitted statements, author proof, and source
references were read; their counting, local factors and complete return
were then reconstructed independently. This is not a blind review claimed
retroactively. Separate executions do not establish statistical independence.

### D. Claims Reviewed And Verdicts

All GL IDs below have prefix **20261107-analytic-1/**, report blob
**6712040159ca37ef3257cf507ec8198fd26fbb91**, retrieved at reporting intake
**f14d6b87984cd1729b85803660c54dda066fd382**.

| Claim | Referee verdict | Exact accepted evidence and limitation |
| --- | --- | --- |
| GL1 | ACCEPT_WITH_SCOPE | Exact bijection and both masks; IDENTITY_ONLY, not new cancellation |
| GL2 | ACCEPT_WITH_SCOPE | PAPER_PROOF, all integer 2<=G<=h<=X, constant 8 accepted |
| GL3 | ACCEPT_WITH_SCOPE | INDEPENDENTLY_REVIEWED_PAPER_PROOF, constant 23708160000 and t>=10^10; only W_ge lower bounded |
| GL4 | ACCEPT_WITH_SCOPE | Complete finite return and power arithmetic accepted; endpoint remains CONDITIONAL on the displayed small-gcd signed supplier |
| GL5 | SELECTIVE_INDEPENDENT_REPRODUCTION | New independent small grid and eight held-out fixtures; not an assertion that every author test was rerun |
| Universal positive lower bound with only G,X/G,h-G growing | COUNTEREXAMPLE / REFUTED strengthening | NC2 is an exact genuine-arithmetic infinite family; not an assertion made by GL3 |
| NC1-NC2, PF1-PF2 | SELF_AUDIT, REVIEW_PENDING | New complete paper arguments, not self-issued independent acceptance or Lean status |

Prior November 6 CORR4/NYMAN decisions are carried forward, not newly reviewed
or credited. Today's SG, DI, SC and yesterday's newer CS claims were consumed
as context; this report does not certify those entire packages.

### E. Independent Reconstruction Of GL1-GL3

#### E1. Exact statement and unique original carrier

For integers 2<=G<=h<=X, define

~~~text
T_ge = 2 sum_(1<=d<h) (h-d)
           sum_(X<=n<4X, gcd(n,d)>=G) mu(n)mu(n+d),

W_ge = 2 sum_(1<=d<h) (h-d)
           sum_(X<=n<4X, gcd(n,d)>=G) mu(n)^2 mu(n+d)^2.
~~~

These are actual integer occurrences. In particular n+d is not cut off at
4X. Let g=gcd(n,d), m=n/g, k=d/g. Then gcd(m,k)=1 and

~~~text
T_ge =
2 sum_(G<=g<h) mu(g)^2
  sum_(1<=k<h/g) (h-gk)
    sum_(X<=gm<4X,
         gcd(m,k)=1, gcd(g,m(m+k))=1) mu(m)mu(m+k).
~~~

The analogous formula for W_ge replaces the final product by its square.
This is a bijection, including zeros: a squareful g kills both sides, and
a shared prime between g and m(m+k) makes at least one original integer
squareful. Otherwise multiplicativity supplies mu(g)^2, not mu(g).
The first mask prevents multiple representations of an original pair.

#### E2. Upper bound

For fixed g there are at most 3X/g+1 permitted m, and

~~~text
sum_(1<=k<h/g) (h-gk) <= h^2/(2g).
~~~

After dropping masks only for this upper bound,

~~~text
|T_ge| <= W_ge
 <= h^2 sum_(G<=g<h) (3X/g^2 + 1/g)
 <= h^2 [3X/(G-1) + log(h/(G-1))]
 <= 8 X h^2/G.
~~~

The reciprocal-square tail follows from
1/g^2 <= 1/(g(g-1)); log u<=u and h<=X give the last line.
The endpoint G=h is the empty sum. There is no sign premise.

#### E3. Explicit genuine-support lower bound

Set Q=420, L=X/G, K=floor(h/(4G)),
t=min(G,L,K)>=10^10. Choose g,m,k in

~~~text
G<=g<2G, L<=m<2L, 1<=k<=K, g=m=k=1 (mod Q).
~~~

Their progression populations A,B,C are respectively at least
G/(2Q), L/(2Q), K/(2Q). Impose squarefreeness of g,m,m+k and the three
coprimalities (g,m)=(g,m+k)=(m,k)=1.

The primes 2,3,5,7 cause no bad event. For p=2 one specifically needs
m+k=2 (mod 4), which holds because 4 divides Q.
For p>7 there are six excluded events: the three square divisibilities,
and divisibility of each of the three gcds. Every leading density is
bounded by 1/p^2 using progression counts, not independence.
For U=min(2G,3L), the sum of boundary errors is at most

~~~text
E = sqrt(2G)/A + 2sqrt(3L)/B
  + 2[(1/A+1/B)(1+log U) + U/(AB)]
  + (1/B+1/C)(1+log K) + K/(BC).

E <= 10Q/sqrt(t) + 12Q(1+log(3t))/t + 28Q^2/t.
~~~

This remains uniform for unbalanced G,L,K: use U<=3min(G,L),
K<=L/4, and monotonicity of (1+log(3u))/u at these u.
For example the g-m harmonic terms are bounded by
8Q(1+log(3t))/t; no log of the larger scale is silently substituted.

Since sum_(p>7)1/p^2<=1/10, the six leading densities cost at most 3/5.
At t0=10^10, log(3t0)<25 follows from e>8/3 and
(8/3)^25>3t0. The displayed error is at most

~~~text
2656689/62500000 < 1/5.
~~~

This exact rational was independently checked. Thus at least ABC/5 triples
are good. They give distinct original pairs with X<=gm<4X, gk<h/2
and weight 2(h-gk)>=h. Since K>=h/(8G),

~~~text
W_ge >= h * X K/(40Q^3)
     >= X h^2/(320 Q^3 G)
      = X h^2/(23708160000 G).
~~~

All steps survive independent review. This argument neither determines
nor lower-bounds the signed sum. The finite box tests are not a substitute
for this proof at its enormous explicit threshold.

### F. New Counterexamples And Exact Near-Cutoff Theorem

#### NC1: One surviving primitive lag and a geometric upper bound

For all integers 2<=G<h<=X with h<=2G, write ell=h-G. Since
g>=G and gk<h, the only possible k is 1. Hence exactly

~~~text
W_ge =
2 sum_(G<=g<h) mu(g)^2 (h-g)
   sum_(X<=gm<4X, gcd(g,m(m+1))=1)
       mu(m)^2 mu(m+1)^2.                              (NC1)
~~~

All even g contribute zero: m,m+1 contain an even member, so the
cross-coprimality mask fails for even g (or equivalently one original
integer is divisible by 4). Consequently the support sees an actual
parity obstruction, not an independent-density approximation.

Dropping masks only for an upper bound gives

~~~text
0 <= W_ge <= (3X/G+1) ell(ell+1).                       (NC1-U)
~~~

Indeed the inner interval has at most 3X/G+1 integers and
2 sum_(G<=g<h)(h-g)=ell(ell+1).
Compared with Xh^2/G, this already forces a quadratic geometric loss when
ell/h -> 0. The statement concerns the original full triangular weight.

#### NC2: Arbitrarily long exact zero-support cutoff sectors

For every integer ell>=1, choose distinct primes p_0,...,p_(ell-1).
The Chinese remainder theorem supplies a residue a modulo
Q_ell=product_j p_j^2 with

~~~text
a+j = 0 (mod p_j^2), 0<=j<ell.
~~~

Choose any G=a+t Q_ell >= max(2,ell), put h=G+ell, and take any integer
X>=h. Every g in [G,h) is squareful. The exact extraction in E1 then
gives W_ge=T_ge=0, irrespective of any further distribution of m.

This is an infinite arithmetic family, with no invented sign vector.
Choosing ell->infinity, sufficiently large G in the progression, and X=G^2
makes G, X/G, and h-G all diverge while W_ge remains identically zero.

It refutes the following precise strengthening:

~~~text
There exist c>0,A such that whenever 2<=G<h<=X and
min(G,X/G,h-G)>=A, one has W_ge >= c X h^2/G.             (FALSE)
~~~

It also defeats a universally positive near-cutoff lower bound of order
X(h-G)^2/G under only those hypotheses. It does NOT refute GL3, whose
K=floor(h/(4G)) is zero on this family for G sufficiently large.

The smallest possible strict-domain witness is (X,h,G)=(3,3,2):
d=2 is the only lag and every allowed common divisor is even.
A squareful-gap witness is (X,h,G)=(10,10,8), with gcd labels 8 and 9.
The reproduced CRT gap of length three is [548,551):
548 is divisible by 4, 549 by 9, and 550 by 25.
These are genuine zero-support statements for all original n in the range.

### G. Complete Signed Return And Source Fidelity

Define T_lt by the complementary exact mask gcd(n,d)<G.
No original off-diagonal pair is omitted or repeated:

~~~text
T = T_lt + T_ge,
J(H,h) = sum_(H^2<=n<4H^2) |sum_(0<=j<h) mu(n+j)|^2,
D = sum_(H^2<=n<4H^2) mu(n)^2 <= 3H^2,
J = hD + T_lt + T_ge + B_halo.
~~~

The halo is the exact shifted-boundary difference. With X=H^2 it equals

~~~text
sum_(0<=j<h) sum_(0<=a<j) [mu(4X+a)^2-mu(X+a)^2]
+
2 sum_(1<=d<h) sum_(0<=i<h-d) sum_(0<=a<i)
 [mu(4X+a)mu(4X+a+d)-mu(X+a)mu(X+a+d)].
~~~

Thus |B_halo|<=h(h-1)(2h-1)/3. This includes the actual forward
values beyond 4X rather than clipping them.

For integer u,v within a square shell, comparing its sum with the average
of its h forward translates costs at most h-1 in amplitude.
Cauchy inside a shell of length at most 4H and
(a+b)^2<=2a^2+2b^2 therefore gives

~~~text
E_max(H) <= (8H/h^2) J(H,h) + 2H(h-1)^2,

E_max(H) =
sum_(H<=R<2H) max_(R^2<=u<=v<=(R+1)^2)
                    |sum_(u<=n<v) mu(n)|^2.
~~~

The max is over integer endpoints. Summing over disjoint shells introduces
no new overlap. Substituting the proved tail bound yields the full return

~~~text
E_max <= (8H/h^2) T_lt
       + 64H^3/G + 24H^3/h
       + 8H(h-1)(2h-1)/(3h) + 2H(h-1)^2.              (RETURN)
~~~

No negative credit is spent twice. All mu signs, multiplicity, triangular
weights, gcd masks, diagonal, shifted boundary, and interval errors remain
identical to the original source. The paper inequalities were independently
derived; they are not automatically new Lean declarations.

The Lean shell source uses realMertensLength(K)=sum_(0<=n<K)mu(n),
whereas conventional M(y)=sum_(1<=n<=y)mu(n).
Thus realMertensLength(K)=M(K-1) for K>=1; the stated half-open endpoints
agree exactly. The final incomplete shell has at most 2floor(sqrt x)+1
sites. No rational-Mobius-to-Hecke or clipped-VF identification is asserted.

### H. Quantifier, Strength And No-Circularity Audit

Fix 0<eta<1/6, let h=floor(H^(2/3)) and G=ceil(H^(1/2+eta)).
The genuine high-gcd sector costs O(H^(17/6-eta)).
The diagonal and translation terms in RETURN cost O(H^(7/3)),
and the halo O(H^(5/3)). Therefore an independently proved one-sided bound

~~~text
T_lt(H^2,h,G) <= C_(eta,eps) H^(17/6-eta+eps)
~~~

would imply E_max << H^(5/2-eta+eps), hence, after partial-prefix Cauchy,
dyadic summation and the final shell,
M(x) << x^(7/8-eta/4+eps). This implication is accepted as CONDITIONAL.

At eta=1/12, the open small-gcd exponent is 11/4, the shell exponent
29/12, and the resulting Mertens exponent 41/48.
Compared with b_star, the hypothetical explicit improvement is
1/48-delta_star >= 11/576. This is not an achieved gain and does not
identify the actual optimal Hecke boundary with b_star.

Because |T_ge| is independently bounded at the required scale, the
one-sided T_lt bound is equivalent, up to constants, to the inherited
OPEN-CD5 bound for full T. This is TARGET_EQUIVALENT relative to that
sufficient CODIV supplier. No converse from the canonical VF target,
RH, or the existing global Mertens bound to this maximal local-shell
condition has been established. It is incorrect to label that stronger
condition already paid or to call its reformulation an arithmetic solution.

PF1 below holds for each fixed finite tau>1 and two independently growing
lengths. It supplies no uniform rate as tau approaches one or grows to
infinity. In the concrete OPEN-GL4 scaling h/G is about H^(1/12), so PF1
cannot replace GL3 or settle that signed supplier by exchanging limits.

### I. Strongest New Surviving Replacement: Fixed-Ratio Profile

#### PF1: Complete theorem

Let (X_j,h_j,G_j) be ANY sequence of integers satisfying 2<=G_j<=h_j<=X_j.
Suppose G_j -> infinity, L_j=X_j/G_j -> infinity, and
h_j/G_j -> tau, where 1<tau<infinity is fixed.
No comparability of G_j and L_j is assumed. Then

~~~text
W_ge(X_j,h_j,G_j)/(X_j G_j) -> Phi(tau)

Phi(tau) = 6 sum_(positive integer k<tau)
              A(k)[tau log(tau/k)-tau+k],
A(k) = product_p rho_p(k),

rho_p(k) = (1-1/p)(1-1/p^2)       if p divides k,
rho_p(k) = 1-5/p^2+4/p^3          otherwise.
~~~

All products converge to strictly positive numbers. Phi(tau)>0 for every
tau>1. At integer tau, the omitted k=tau term has weight zero; no
extra boundary atom is present.

#### Proof: exact local factors

For fixed k define the indicator on actual integer pairs

~~~text
F_k(g,m) =
mu(g)^2 mu(m)^2 mu(m+k)^2
  1_(gcd(g,m(m+k))=1) 1_(gcd(m,k)=1).
~~~

It is the exact W_ge summand after the bijection, not a surrogate model.
At a prime p, work modulo p^2 in both variables.

If p divides k, the last mask forces p not dividing m.
Then neither m nor m+k has a p-factor, and only p^2 not dividing g remains.
The number of valid residue pairs is
(p^2-p)(p^2-1), giving rho_p(k)=(1-1/p)(1-1/p^2).

If p does not divide k, there are two cases.
For m neither 0 nor -k modulo p, there are p(p-2) choices modulo p^2,
and g has p^2-1 choices.
For m in one of those two residue classes, exclusion of the square
multiples leaves 2(p-1) choices, and the cross mask requires p not dividing g,
giving p^2-p choices. Hence

~~~text
rho_p(k)
= [p(p-2)(p^2-1)+2(p-1)(p^2-p)]/p^4
= 1-5/p^2+4/p^3.
~~~

This counts all overlaps exactly. In particular rho_2(k)=1/4 for odd k
and 3/8 for even k, so treating all three squarefree events as independent
would give the wrong leading constant. All factors are positive, and
outside the finitely many primes dividing k their difference from one is
O(1/p^2). Thus A(k)>0.

#### Proof: uniform two-length density, without stochastic independence

Fix k and a finite prime threshold z>=k. The finite restrictions are periodic
modulo q_z=product_(p<=z)p^2 in each variable. CRT gives the product of their
local densities. In any fixed rectangle after scaling g=G u, m=L v,
residue-class counting has an error tending to zero after division by GL
as min(G,L) -> infinity. The modulus is fixed before either length grows.

It remains to justify discarding no large-prime obstruction. Bound all
variables in g<=C G, m<=C L, where C is fixed. For p>z>=k the only bad
events are the three square divisibilities and the two cross gcd events;
p cannot divide k. The normalized number of bad pairs is bounded by

~~~text
O_(C,k)(
  sum_(p>z) 1/p^2
  + G^(-1/2) + L^(-1/2)
  + (1/G+1/L) [1+log(min(C G,C L+k))]
  + min(C G,C L+k)/(G L)).
~~~

For square divisibility, count at most length/p^2+1 through the appropriate
square-root cutoff. For a cross gcd, count at most
(C G/p+1)(C L/p+1) and sum through min(C G,C L+k).
These estimates remain valid on a containing rectangle for every subregion.
All terms after the prime sum tend to zero even when G and L have
arbitrarily different growth rates: their logarithm involves the smaller
scale. Taking the two lengths to infinity first and then z to infinity
proves density A(k), and by finite rectangle approximation proves the same
limit against every bounded Riemann-integrable weight on this fixed box.

#### Proof: actual hyperbolic interval and triangular weight

Only finitely many k contribute when h/G remains bounded.
The original constraints become

~~~text
1<=u<tau/k, 1<=u v<4,
2(h-gk)/G -> 2(tau-ku).
~~~

Their boundary has area zero; strict endpoints and a possible newly entering
integer k at tau give no limiting boundary mass. Since X=GL, the weighted
Riemann sum and exact density above yield

~~~text
lim W_ge/(XG)
 = 2 sum_(1<=k<tau) A(k)
      integral_(u=1)^(tau/k) integral_(v=1/u)^(4/u)
                       (tau-ku) dv du
 = 6 sum_(1<=k<tau) A(k)
      integral_1^(tau/k) (tau/u-k) du
 = Phi(tau).
~~~

The k=1 integral is strictly positive for tau>1. This proves PF1.

#### PF2: Sharp fixed-ratio consequence and failure of uniform endpoint extension

For every fixed tau>1, PF1 gives

~~~text
W_ge/(Xh^2/G) -> Phi(tau)/tau^2 > 0.
~~~

Thus replacing the signed sector by its actual absolute support cannot
produce an extra power in this fixed-ratio regime either. This remains
a statement about a specific method, not a lower bound for T_ge.

For 1<tau<=2 there is only k=1, and

~~~text
Phi(tau)=6 A(1)[tau log tau-tau+1],
Phi(tau) ~ 3 A(1)(tau-1)^2  as tau decreases to 1.
~~~

This last assertion is an asymptotic of the explicit limiting function,
with limits in that order. It is not a uniform estimate for a sequence
tau_j->1; NC2 shows why that distinction matters.
PF1 supplies the positive corrected theorem outside GL3's range, and
NC1-NC2 specify exactly where a naive uniform extension fails.

### J. Competing-Strategy Assessment And Literature

Continue CODIV on the original signed primitive correlations below the
critical cutoff. GL3 and PF1 close off further power savings obtained solely
from counting the same admissible squarefree support in their respective
ranges. They leave genuine cancellation, weighted signed recombination,
and different full-source consumers unaffected.

Owner SG's weighted cofactor matching is a different interval and weight;
its incidence graph is not an automatic estimate for this additive-lag source.
Wheel DI's sign-reversing edges still require complete mixed-term aggregation.
Census SC's signed label capacities demonstrate another non-additivity
mechanism, but they are not a literal identification with F_k.
The recent Nyman CS and previous referee spectral results concern a
complete-period residue source, not the physical weighted window.
No route is retired merely because these carriers differ.

The classical study of squarefree correlations and CRT products predates
this work. An authoritative background source consulted is
[Cellarosi and Sinai, Ergodic properties of square-free numbers, JEMS 15 (2013),
Sections 1.1 and 2](https://ems.press/content/serial-article-files/31903?nt=1).
It describes the classical squarefree-correlation setting and attributes
earlier formulas to Mirsky. PF1 above is proved directly for the two-variable,
exact-gcd carrier; no theorem from that paper is imported as a signed Mobius
estimate or as a ready-made uniform theorem for growing masks.
No assertion of exhaustive novelty or literature priority is made.

### K. Independent Computation And Original Research Record

An independent implementation used a multiplicative sieve for the direct
original pair sums and trial division for the primitive reconstruction.
The two implementations do not share their coefficient-generation routines.
All decisions, source equalities, and upper-bound checks used exact integers
or Fraction. No floating-point comparison is used for any refutation.

Registered exact tests completed successfully:

- 5000 sieve/trial Mobius coefficient comparisons.
- 819 original-versus-primitive cases: every X=8..64 and
  h=2..min(X,16), with all 6384 cutoffs 2<=G<=h.
- 4172 near-cutoff checks, including NC1, its geometric bound and even-g zero.
- 819 exact halo reconstructions and halo bounds.
- Eight larger fixtures checking direct/primitive equality, maximal-shell
  smoothing and the complete RETURN inequality.
- Thirty exhaustive local residue-pair counts: p=2,3,5,7,11 and k=1..6.
- CRT squareful-gap constructions of lengths 1..6, with direct original
  zero-support enumerations for lengths 1..3 and the smallest parity witness.
- Exact GL3 threshold constants, both coprimality negative controls, and
  conditional exponent arithmetic.

| H | h | G | T_ge | W_ge | B_halo |
| --- | --- | --- | --- | --- | --- |
| 15 | 6 | 5 | 16 | 56 | 1 |
| 42 | 12 | 9 | -16 | 260 | -16 |
| 56 | 14 | 11 | -14 | 1730 | 121 |
| 64 | 16 | 12 | -86 | 1710 | -29 |
| 96 | 20 | 15 | 96 | 5260 | 2 |
| 127 | 25 | 17 | 1384 | 26360 | -378 |
| 128 | 25 | 17 | 1412 | 26836 | 370 |
| 192 | 33 | 22 | 424 | 41864 | -42 |

The earlier positive and negative tail witnesses were reproduced, not
rediscovered as new results. The mask-negative controls are n=42,d=2:
genuine product 0 versus maskless extracted product 1; and n=66,d=3:
genuine product -1 versus primitive-mask-deleted divisor sum -2.

Additional fixed-ratio diagnostic tables use tau=5/4,3/2,2,3,4 and
(G,X/G)=(20,20),(60,60),(180,180),(540,540),(100,3000),(3000,100).
All 30 W values are exact, and the five G=20 rows have a separate original
enumeration. Ratios, logarithms and Euler products truncated at 997 are
floating-point diagnostics only, not certified limits.
For example tau=2 gives W/(XG)=0.22641991 at (540,540), against
a finite-product prediction 0.22428864. Neither number is a proof of PF1.

Verifier SHA256:
**8bc7dd6670e49cadaedd832989dbd2d29d9713e16b822016137c38ed5510865d**.
Canonical result payload SHA256:
**1b5d0ec9304f0ff309b6303eae8237d7db139801951cc1e94294e959f5c45599**.
The script, including the added exact negative controls, completed with
all assertions passing. The final script also passed a separate syntax check.
The complete executed code is appended for reproducibility.

This work went beyond reviewing GL3: it derived the near-cutoff exact
restriction, the arbitrary-length genuine zero-support families, the
two-variable local-density factors, and the full fixed-ratio profile.
The proof, not the diagnostic trend, establishes the new asymptotic.

### L. Formalization Guidance

GL1-GL2 are now independently accepted finite-sum candidates if Lean
Verification finds their exact source interface useful. GL3's explicit
progression count is also accepted on paper, but has no Lean certificate.
Do not implement GL4 by assuming its unresolved signed supplier and then
present the result as a new exponent.

NC1-NC2 and PF1-PF2 are self-derived paper results requiring separate review.
The finite near-cutoff identity and parity vanishing are the smallest
implementation-sized candidates after that review. PF1 additionally needs
a genuinely uniform two-length arithmetic-density proof and justified
Riemann-sum passage; it is not merely an Euler-product definition.

No Lean source, workflow, feature branch, issue, PR or other agent's report
was changed. No Lean ran locally. Generic fetch of an Actions job URL was
rejected by the connector; the dedicated workflow-jobs and job-log actions
then supplied the required success and axiom evidence. No CI status was
inferred from that failed request, and no unresolved access blocker remains.

### M. Specialist Handoffs And Two-Day Continuity

**Coordinator / Proof Architect:** record GL1-GL4 as accepted at the scopes
in D. PF1 extends the support-only obstruction to fixed h/G, while NC2
prevents a uniform near-cutoff extrapolation. Keep all nine routes and
the genuine signed supplier open. Today's Coordinator report is
TODAY=PENDING; November 6 CS1-CS4 and its portfolio are YESTERDAY=CARRY_FORWARD.

**Analytic Type II:** E2-E6 and the full RETURN survived review.
Do not spend the next CODIV turn improving squarefree support alone in
the already sharp ranges. PF1 has fixed tau, not the growing h/G of
OPEN-GL4; retain your original GL3 for that scale. A useful next derivation
must use the actual mu(m)mu(m+k), both masks, and joint summation.

**Owner Payment / Arithmetic Structure:** SG1-SG5 were consumed at blob
1006bb9f0c61a22ceeb7fab25d177a40dc24f25e. A possible transfer must match
your original prime-error weights and cofactor interval; this report
proves no such transfer. November 6 SAT BT/RZ and JOH/VF continuations
remain context, not newly certified by this run.

**Finite Wheel & Incidence:** DI1-DI5 were consumed at blob
b943f16b0fedbcefa53545f8a7c77482e688399e. PF1 demonstrates that fixed
primitive-lag support retains positive density after every exact gcd mask.
Seek restrictions on the signed interactions, not another count of the
same support. November 6 GF donor/capacity findings remain distinct.

**Prime Census Laboratory:** SC1-SC5 were consumed at blob
c9d78787ca4fca22f89bc9bcaf886e5ae74deda2. No repetition of this exact grid
is requested. The decisive open test remains signed concentration by g
and k on the actual critical-cutoff carrier, with full halo. Do not use
the positive A(k) as a prediction for the sign of T. November 6 FW's
weighted-window falsifiers remain unchanged.

**Lean Verification:** use the qualified scopes in L, not a desired-bound
wrapper. Today's report is TODAY=PENDING. November 6 final
FW3-INCREMENTS is YESTERDAY=CARRY_FORWARD, with its PR status now updated
to human-merged after direct source and CI checks.

Full retrieved continuity provenance:

| Date / role | Report blob |
| --- | --- |
| 2026-11-06 Coordinator AM and PM, byte-identical tree blobs | 8812a90540fb511279b5f4ce08e108ef717d5ef1 |
| 2026-11-06 Owner | 1856a96aaaa9d86a5ee2d59ffe50ced936443fa6 |
| 2026-11-06 Analytic | 7997620b6ab7eb0701296994734ee910df3c3ba1 |
| 2026-11-06 Wheel | 3099558194a00358962ff1844bf283e625b9283d |
| 2026-11-06 Census | c34ac074296e8b2e5b20dee3a2ce02518571206c |
| 2026-11-06 Referee | da3265467c799e9d21832ab25245617ba3b15a54 |
| 2026-11-06 Lean | b8bfe3ce9c20d7903395364efb39bcec974c8a2f |
| 2026-11-07 Owner | 1006bb9f0c61a22ceeb7fab25d177a40dc24f25e |
| 2026-11-07 Analytic | 6712040159ca37ef3257cf507ec8198fd26fbb91 |
| 2026-11-07 Wheel | b943f16b0fedbcefa53545f8a7c77482e688399e |
| 2026-11-07 Census | c9d78787ca4fca22f89bc9bcaf886e5ae74deda2 |
| EXTERNAL_HANDOFFS.md | 038018145c0fddb2f6306c0712373adf9cd1ea52 |

All relevant report contents were retrieved; relevant summaries, derivations
and continuation sections were read. This is not a claim to have audited
every embedded experiment in the large two-day archive. The external inbox
contains no newer entry than October 18. EXT-20261018-PNT's actual-discrepancy
and complete-return cautions and EXT-20261014-5's scoped original-denominator
warning are retained; their old task routing does not override current main.
No prior unchanged external claim was relabeled as a new result.

### N. First Independently Missing Mathematical Ingredient

For the concrete eta=1/12 proposal, h=floor(H^(2/3)),
G=ceil(H^(7/12)), the actual open assertion is

~~~text
For every eps>0 there exists C_eps and H_eps such that
for every integer H>=H_eps,

2 sum_(1<=g<G) mu(g)^2
  sum_(1<=k<h/g) (h-gk)
    sum_(H^2<=gm<4H^2,
         gcd(m,k)=1, gcd(g,m(m+k))=1) mu(m)mu(m+k)
 <= C_eps H^(11/4+eps).
~~~

The missing input is a one-sided uniform SIGNED estimate. GL2, GL3, PF1,
the genuine zero-support examples and the existing all-prefix Mertens
bound do not prove it. Fixed-g, fixed-k or fixed-tau asymptotics do not
justify the growing-range aggregate. No new target-strength assumption
has been smuggled into the accepted support theorems.

### O. Next-Run Resume Capsule And Publication

Run: 20261107-referee-1, scheduled 2026-11-07T04:13:01-05:00,
America/New_York; RUN_ID_UNAVAILABLE.
Source main: 1c057c1d65b6d4cb4d59d207f69a815c52353314.
No material policy/source change at prepublication refresh.
Today's four upstream report blobs remain unchanged; Coordinator and Lean
remain absent, not presumed executed.

Accepted: 20261107-analytic-1/GL1-GL4, strictly scoped above.
New review-pending: NC1 near-cutoff identity and bound; NC2 arbitrary-length
zero-support family; PF1 fixed-ratio exact profile; PF2 method limitation.
Exact witnesses: (X,h,G)=(3,3,2),(10,10,8),(551,551,548).
Do not describe any of them as a counterexample to GL3.

Highest-value continuation: independently review the new two-variable
density proof, especially unbalanced G and X/G and the order of limits;
then attack the original signed small-gcd supplier or another fresh
route claim. Do not rerun the same support census as evidence of cancellation.
No complete endpoint gain is established; protected investigator rotation
is not reset by this support-role review.

Early checkpoint was published at
**def83099d0261b754cfc17868961e210b45a60e7**, blob
**5468e4a75c5896dd7e97b1470d4037e0d28d21cb** and immutable readback matched.
Final publication is recorded in the subsequent receipt after commit/readback.

## Reproducibility Appendix: Complete Executed Verifier

~~~python
"""Exact CODIV review and near-cutoff tests, 20261107-referee-1.

Registration before execution: X=8..64, h=2..min(X,16), all 2<=G<=h;
held-out H=15,42,56,64,96,127,128,192; finite local factors at p<=11,
k=1..6. Fixed-ratio tables are diagnostics, not asymptotic certificates.
"""

from fractions import Fraction as F
from functools import lru_cache
from math import gcd, isqrt, log, prod
import hashlib
import json


def sieve(n):
    mu = [1] * (n + 1)
    mu[0] = 0
    primes = []
    marked = [False] * (n + 1)
    for p in range(2, n + 1):
        if not marked[p]:
            primes.append(p)
            for k in range(p, n + 1, p):
                marked[k] = True
                mu[k] = -mu[k]
            for k in range(p * p, n + 1, p * p):
                mu[k] = 0
    return mu, primes


@lru_cache(None)
def trial(n):
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


def original_classes(X, h, mu):
    ts, ws = [0] * h, [0] * h
    for d in range(1, h):
        weight = 2 * (h - d)
        for n in range(X, 4 * X):
            g = gcd(n, d)
            v = mu[n] * mu[n + d]
            ts[g] += weight * v
            ws[g] += weight * v * v
    return ts, ws


def primitive_classes(X, h):
    ts, ws = [0] * h, [0] * h
    for g in range(1, h):
        for k in range(1, (h - 1) // g + 1):
            weight = 2 * (h - g * k)
            for m in range((X + g - 1) // g, (4 * X - 1) // g + 1):
                if gcd(m, k) == 1 and gcd(g, m * (m + k)) == 1:
                    v = trial(g) ** 2 * trial(m) * trial(m + k)
                    ts[g] += weight * v
                    ws[g] += weight * v * v
    return ts, ws


def halo(X, h, mu):
    diag = sum(mu[n] ** 2 for n in range(X, 4 * X))
    J = sum(sum(mu[n:n + h]) ** 2 for n in range(X, 4 * X))
    boundary = 0
    for j in range(h):
        boundary += sum(mu[4 * X + a] ** 2 - mu[X + a] ** 2
                        for a in range(j))
    for d in range(1, h):
        for i in range(h - d):
            boundary += 2 * sum(mu[4 * X + a] * mu[4 * X + a + d]
                                - mu[X + a] * mu[X + a + d]
                                for a in range(i))
    return J, diag, boundary


def root_floor(n, power):
    lo, hi = 0, n + 1
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid ** power <= n:
            lo = mid
        else:
            hi = mid
    return lo


def support(X, h, G, direct=False):
    if direct:
        mu, _ = sieve(4 * X + h)
        return sum(2 * (h - d) * mu[n] ** 2 * mu[n + d] ** 2
                   for d in range(G, h) for n in range(X, 4 * X)
                   if gcd(n, d) >= G)
    mu, _ = sieve(max(h, (4 * X - 1) // G + h // G + 2))
    total = 0
    for g in range(G, h):
        if mu[g] == 0:
            continue
        for k in range(1, (h - 1) // g + 1):
            count = sum(mu[m] ** 2 * mu[m + k] ** 2
                        for m in range((X + g - 1) // g, (4 * X - 1) // g + 1)
                        if gcd(m, k) == 1 and gcd(g, m * (m + k)) == 1)
            total += 2 * (h - g * k) * count
    return total


def local_factor(p, k):
    if k % p == 0:
        return (1 - F(1, p)) * (1 - F(1, p * p))
    return 1 - F(5, p * p) + F(4, p ** 3)


def crt_gap(primes):
    a, modulus = 0, 1
    for j, p in enumerate(primes):
        q = p * p
        a += modulus * ((-j - a) * pow(modulus, -1, q) % q)
        modulus *= q
    while a < max(2, len(primes)):
        a += modulus
    assert all((a + j) % (p * p) == 0 for j, p in enumerate(primes))
    return a, a + len(primes), modulus


def main():
    mu, _ = sieve(5000)
    assert all(mu[n] == trial(n) for n in range(1, 5001))
    grids = cutoffs = near = halo_tests = 0
    for X in range(8, 65):
        for h in range(2, min(X, 16) + 1):
            mu, _ = sieve(4 * X + h)
            ts, ws = original_classes(X, h, mu)
            assert (ts, ws) == primitive_classes(X, h)
            grids += 1
            J, diag, boundary = halo(X, h, mu)
            assert J == h * diag + sum(ts) + boundary
            assert abs(boundary) <= h * (h - 1) * (2 * h - 1) // 3
            halo_tests += 1
            for G in range(2, h + 1):
                T, W = sum(ts[G:]), sum(ws[G:])
                assert abs(T) <= W and G * W <= 8 * X * h * h
                cutoffs += 1
                if 2 * G >= h:
                    ell = h - G
                    assert G * W <= (3 * X + G) * ell * (ell + 1)
                    assert all(ws[g] == 0 for g in range(G, h) if g % 2 == 0)
                    assert W == support(X, h, G)
                    near += 1
    held = []
    for H in [15, 42, 56, 64, 96, 127, 128, 192]:
        X, h = H * H, root_floor(H * H, 3)
        G = root_floor(H ** 7, 12)
        if G ** 12 < H ** 7:
            G += 1
        mu, _ = sieve(4 * X + h)
        ts, ws = original_classes(X, h, mu)
        assert (ts, ws) == primitive_classes(X, h)
        J, diag, boundary = halo(X, h, mu)
        assert J == h * diag + sum(ts) + boundary
        Emax = 0
        for R in range(H, 2 * H):
            values, s = [0], 0
            for n in range(R * R, (R + 1) ** 2):
                s += mu[n]
                values.append(s)
            Emax += (max(values) - min(values)) ** 2
        assert Emax <= F(8 * H, h * h) * J + 2 * H * (h - 1) ** 2
        rhs = (F(8 * H, h * h) * sum(ts[:G]) + F(64 * H ** 3, G)
               + F(24 * H ** 3, h) + F(8 * H * (h - 1) * (2 * h - 1), 3 * h)
               + 2 * H * (h - 1) ** 2)
        assert Emax <= rhs
        held.append([H, h, G, sum(ts[G:]), sum(ws[G:]), boundary, Emax])

    # No logarithmic floating point is used in the GL3 threshold check.
    Q, t = 420, 10 ** 10
    err = F(10 * Q, isqrt(t)) + F(12 * Q * 26 + 28 * Q * Q, t)
    assert F(8, 3) ** 25 > 3 * t
    assert err == F(2656689, 62500000) < F(1, 5)
    assert 320 * Q ** 3 == 23708160000
    assert F(10, 3) - F(7, 12) == F(11, 4)
    assert (1 + F(29, 12)) / 4 == F(41, 48)

    local_tests = 0
    for p in [2, 3, 5, 7, 11]:
        pp = p * p
        for k in range(1, 7):
            good = sum(1 for g in range(pp) for m in range(pp)
                       if g != 0 and m != 0 and (m + k) % pp != 0
                       and not (g % p == 0 and (m % p == 0 or (m + k) % p == 0))
                       and not (k % p == 0 and m % p == 0))
            assert F(good, pp * pp) == local_factor(p, k)
            local_tests += 1

    gaps = []
    ps = [2, 3, 5, 7, 11, 13]
    for length in range(1, 7):
        G, h, modulus = crt_gap(ps[:length])
        gaps.append([length, G, h, modulus])
        if length <= 3:
            assert support(h, h, G, direct=True) == 0
    assert support(3, 3, 2, direct=True) == 0
    assert support(10, 10, 8, direct=True) == 0
    assert trial(42) * trial(44) == 0
    assert trial(2) ** 2 * trial(21) * trial(22) == 1
    assert trial(66) * trial(69) == -1
    maskless = sum(trial(g) ** 2 * trial(66 // g) * trial(69 // g)
                   for g in [1, 3] if gcd(g, (66 // g) * (69 // g)) == 1)
    assert maskless == -2

    # These ratios and finite Euler products are diagnostic only.
    _, primes = sieve(997)
    alpha = {k: prod(float(local_factor(p, k)) for p in primes) for k in range(1, 5)}
    profiles = []
    for tau in [F(5, 4), F(3, 2), F(2), F(3), F(4)]:
        target = 6 * sum(alpha[k] * (float(tau) * log(float(tau) / k) - float(tau) + k)
                         for k in range(1, 5) if k < tau)
        for G, L in [(20, 20), (60, 60), (180, 180), (540, 540), (100, 3000), (3000, 100)]:
            X, h = G * L, int(tau * G)
            W = support(X, h, G)
            if G == 20:
                assert W == support(X, h, G, direct=True)
            profiles.append([str(tau), G, L, W, round(W / (X * G), 8), round(target, 8)])
    results = {"small_grid_cases": grids, "cutoff_checks": cutoffs,
               "near_cutoff_checks": near, "halo_checks": halo_tests,
               "held_out_columns": ["H", "h", "G", "T_ge", "W_ge", "halo", "Emax"],
               "held_out": held, "local_factor_exact_checks": local_tests,
               "crt_gap_columns": ["length", "G", "h", "CRT_modulus"], "crt_gaps": gaps,
               "alpha1_partial_product_diagnostic": alpha[1],
               "profile_columns": ["tau", "G", "X/G", "W", "W/(XG)", "finite_product_prediction"],
               "profiles_diagnostic": profiles}
    encoded = json.dumps(results, sort_keys=True, separators=(",", ":"))
    print(json.dumps(results, indent=2))
    print("RESULT_SHA256", hashlib.sha256(encoded.encode()).hexdigest())
    print("PASS: exact assertions; diagnostic tables are not proofs")


if __name__ == "__main__":
    main()
~~~

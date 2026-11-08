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

## Verified Publication Receipt - 2026-11-07T04:33:57-05:00

The final research synthesis was published at commit
**bdd9deb3db1bccf876acb69ebe122170ab6f9db1**, report blob
**47bf5de42d06dcb2155f61dedefbac93ddbe980e**.
Immutable commit readback matched all 47082 bytes of the prepared report.
The embedded verifier matched its executed file byte-for-byte, with SHA256
8bc7dd6670e49cadaedd832989dbd2d29d9713e16b822016137c38ed5510865d.
All A-O sections and Markdown code fences passed structural validation.

Final live main remained
1c057c1d65b6d4cb4d59d207f69a815c52353314.
EXECUTION=COMPLETED; REPORT=PUBLISHED_VERIFIED.
This receipt records an already verified publication, not a future promise.
NC1-NC2 and PF1-PF2 remain PAPER_PROOF / SELF_AUDIT /
INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED.
GL1-GL4 acceptance remains at its explicitly scoped paper/conditional level.
No new endpoint gain, source modification, proof PR, agent launch or merge occurred.


## Scheduled Complete-HIGH Referee Checkpoint - 20261107-referee-2

Actual trigger: 2026-11-07T12:03:00-05:00, America/New_York.
Execution IN_PROGRESS / PARTIAL; RUN_ID_UNAVAILABLE. This is a continuation
of the same daily report; all earlier results and receipts are preserved.

high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1;
chain_ack=CANCELLATION_CHAIN_REUSE_V1;
baseline_ack=PAID_BASELINE_EXACT_CONSUMER_V1;
deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1.

Live main: 3de4f7331e5fe55ad0e404dc8463b1df56c19330.
AGENTS blob: 0a99faf8458809ac772d470d704c5433f373bda8.
Contract blob: d1d6fd558ee23927bd9f70ffdc375bafd1dbb67a.
HIGH directive blob: be8168b67584d9d8ebbaa732a30c51509137543e.
Initial report snapshot: f9e1fa6cc8cefa064ba883c5a5dc2ff3768917ea.
All seven TODAY reports are AVAILABLE; YESTERDAY=CARRY_FORWARD.
The external inbox is unchanged, blob 038018145c0fddb2f6306c0712373adf9cd1ea52,
with no handoff newer than October 18. No open or draft PR was returned.

Selected route: OAI-NNS consumer review. Independently review
20261107-census-2/RC1-RC4 at report blob
3fae830e34c590d32c31ad77cad3ace833eb3ff5: generalized kappa crossing,
source-qualified four-branch count, complete detector budget and loss return.
Inspect actual source definitions and #1103's compiled generated suppliers;
verify exact-head Actions evidence rather than inherit report labels.
Preserve full-family licensing, physical Delta, selected-slot admission,
actual moments, all finite-bin losses and the complete LOW/HIGH/principal join.

Original research attempt: determine whether the retained marked 1+t/2
supplier can strengthen this actual crossing/count, and where any apparent
gain fails after restoring the unmarked, long and complete-probe branches.
No new covariance assumption, universal inverse norm, or target-size premise
is introduced. Prior CODIV NC/PF and spectral reviews are carried forward,
not rerun as new discoveries. Updated priorities legitimately select this
fresh consumer claim.

Current mathematical status: REVIEW_IN_PROGRESS. No new endpoint gain,
independent acceptance, or Lean certification is asserted by this checkpoint.
The canonical VF/RH objective remains OPEN; eta_gate=SEARCH_BROAD.
Repository writes remain restricted to this own report on agent-reports.

## Reoptimized Marked-Half Consumer - 20261107-referee-2

Scheduled trigger: 2026-11-07T12:03:00-05:00, America/New_York.
RUN_ID_UNAVAILABLE. This continuation preserves all earlier same-day claims,
corrections, computations and receipts. Research is finished; publication is
not marked COMPLETED until the immutable readback receipt below is verified.

### A. Most Important Mathematical Finding

The literal marked moment error `rho/2`, where `rho=D.t`, survives the
generalized-capacity detector consumer after BOTH the inverse/plain crossing
and the witness cutoff are reoptimized. The new source-qualified row exponent
is

```text
R_k(delta,x) + (1-omega_k(delta,x))*rho
  + 159*epsilon + mesh + 7*nu,
omega_k = (5/6-delta)*(1-x) / (2*D_k*B_k).
```

More usefully, the COMPLETE DETECTOR FUNCTIONAL, including the long-bin
complement, satisfies

```text
functional <= -M(k) + (13/16)*(159*epsilon+mesh+7*nu+(41/42)*rho),
M(k) = 1/5000 + (3-4*k)/1600,
1/2 <= k <= 3/4, 0 < delta <= 1, 0 < rho <= delta/12.
```

The high-bin cutoff remains 3/2. Compared with retaining the common error
rho in the same certified detector budget, this saves `13*rho/672`.
It is NOT a global exponent gain. No new arithmetic moment estimate is
assumed: the marked supplier already proves `1+D.t/2`.

Two source-fidelity qualifications are essential. The existing
`SourceMomentsAt` package fixes the OLD adaptive cutoff and widens the marked
error to rho. It cannot simply be instantiated at the new cutoff. Its three
underlying source suppliers are uniform in arbitrary cutoff, and the original
supported-witness theorem is uniform in every cutoff in [1,3/2]. They supply
the precise smaller repair: a cutoff-parametric, two-error moment interface
and a newly chosen witness family, not a new cancellation axiom.

I independently accept Census RC1-RC3 at their paper-proof scopes and RC4
as a conditional downstream statement, with the additional interface
qualification below. The 324-coefficient certificate was reconstructed
independently. New MH1-MH4 are PAPER_PROOF / SELF_AUDIT /
INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED. The existing stronger-than-7/8
baseline is unchanged; NEW_VERIFIED_ENDPOINT_GAIN=NONE; eta_gate=SEARCH_BROAD.

### B. Current Authoritative Objective

Authority was fetched at invocation and refreshed at 2026-11-07T17:20:50Z.
Actual main remained `3de4f7331e5fe55ad0e404dc8463b1df56c19330`.

| Authority | Git blob SHA |
| --- | --- |
| AGENTS.md | 0a99faf8458809ac772d470d704c5433f373bda8 |
| CURRENT_PROOF_CONTRACT.md | d1d6fd558ee23927bd9f70ffdc375bafd1dbb67a |
| COMPLETE_SIGNED_HIGH_ATTACK_20261107 | be8168b67584d9d8ebbaa732a30c51509137543e |
| REUSE_CANCELLATION_CHAIN_20261107 | 28e2ab47c68bc83b91ae02b6112b94867b021b32 |
| PAID_BASELINE_EXACT_CONSUMER_20261106 | 13d58dd12d90fbf1160812c7c93442dc5d0576ac |

`high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1`;
`chain_ack=CANCELLATION_CHAIN_REUSE_V1`;
`baseline_ack=PAID_BASELINE_EXACT_CONSUMER_V1`;
`deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1`.

The canonical `VFCanonicalSquareVonKochStatement` remains OPEN: one C>=0
controls the actual canonical prime-counting defect at every integer R>=2
by C*R*log R. The governing improvement objective is the complete signed
canonical HIGH at a fixed cutoff Lambda>=0, relative to the strongest
applicable certified baseline. Canonical LOW is already supplied:

```text
M(R^2-1) = L_R + H_R,
|L_R| <= (floor(Lambda)+1)*R.
```

For an eventual new gain eta>0, the desired HIGH bound has constants fixed
before R: for every eps>0 there is C_eps>=0 such that every R>=2 satisfies
`|H_R|<=C_eps*R^(2*b_base-2*eta+eps)`. Restoring the partial square block costs
at most 2*R+1; a positive epsilon must be spent before claiming a fixed power.

Baseline: `native_beta_le_true_physical_slot_minimum` supplies a fixed source
D in `HighData (1/1000000)`, with m=actualSlotMinimum D>0 and
`beta<=7/8-m/24`. `native_mertens_true_physical_slot_minimum` supplies, for
that fixed witness, every-positive-loss Mertens growth at `b_base=7/8-m/24`.
This is not an assertion that the boundary is attained as a no-loss power.
Explicitly, for every eps>0 there is C_eps>=0 such that every natural x>=1
satisfies `|M(x)|<=C_eps*x^(b_base+eps)`.
The explicit fallback `native_beta_le_explicit_slot_count` gives
`b_*=7/8-1/(288*explicitSlotCount)`. Keep the stronger applicable source-bound
when comparing a fixed source; do not claim the explicit fallback is optimal.
No astronomical denominator was optimized.

The existing source-calibrated theorem retains fineness, epsilon/e reserves,
`(N+8)*eps<=D.t`, actual SourceData and CountParameters, and
`slotTiltLowFirst D<=D.sigma`; its constructed-source theorem discharges
these hypotheses. It ALREADY uses an anchored 7/8 HIGH ceiling below the
actual 7/8 boundary. The older unanchored theorem's `7/8<=beta` premise is
not a universal repository-wide obstruction.

| Compact HIGH record | This invocation |
| --- | --- |
| Selected route | OAI-NNS actual moment/count consumer; native routes remain distinct |
| Signed object served | Same compensated tilted probe, then native Mertens and complete signed pairs, then canonical HIGH |
| Existing input | Generalized 6*k capacity, literal marked 1+rho/2, inverse and unmarked 1+rho, original supported witnesses |
| Changed step | Two-error crossing and cutoff, followed by the whole detector functional |
| Actual consumer | Raw fiber count, fixed-amplitude batch count, source HIGH transport, anchored LOW/HIGH/principal comparison |
| First missing implementation | Cutoff-parametric two-error source/count interface and its immediate source-count consumer |
| First missing endpoint inference | Exhibit a complete admissible comparison improving the same strongest baseline after all other costs and source conditions |
| Net global budget | No new beta, Mertens, HIGH or VF exponent proved |

### C. Highest-Risk Proof Mechanisms

1. Replacing the common moment error by rho/2 in every branch is unsupported.
   Inverse, unmarked and long branches still pay rho. MH2 keeps those costs.
2. Changing a formula for the balanced cutoff without changing the typed
   source/witness interface uses a theorem outside its quantifiers.
3. Setting physical Delta=(k-3/4)/2 is invalid when k<3/4. The negative number
   is a capacity-record index only; actual HighData and its budgets stay intact.
4. A detector-budget improvement alone does not alter the LOW/principal
   difference 7/8-tilt. The existing anchored return is paid, but its new
   two-error input and a strictly better complete comparison are not proved.
5. Shrinking k or refining a source must preserve full-family licensing and
   fineness. Refinement may change the true minimum slot and therefore the
   comparator; it is not a free gain over the old source.

These are precise consumer obligations, not an assertion that every route
needs a new primitive signed covariance or universal inverse-norm estimate.

### D. Claims Reviewed

Census source: `20261107-census-2/RC1-RC4`, report blob
`3fae830e34c590d32c31ad77cad3ace833eb3ff5` at the initial agent-reports
snapshot `f9e1fa6cc8cefa064ba883c5a5dc2ff3768917ea`.

| Stable ID | Independent verdict | Evidence and precise scope |
| --- | --- | --- |
| RC1 | ACCEPT | Crossing and actual selection-capacity inequalities on the stated rectangle; PAPER_PROOF reconstructed below |
| RC2 | ACCEPT_WITH_SCOPE | Actual-fiber count conditional on the four supplied moment fields at the chosen cutoff; all fallbacks and 159*epsilon+rho+mesh+7*nu survive; a prepackaged old-cutoff theorem is not its source instance |
| RC3 | ACCEPT | Universal parameter inequality, proved by exact positive Bernstein coefficients; independent arithmetic reconstruction, not grid extrapolation |
| RC4 | ACCEPT_WITH_SCOPE | Loss propagation and high-bin complement valid; complete HIGH application remains unwired, and the old unanchored range restriction is not the only available return architecture |
| Existing marked_half_error_survival | ACCEPT, unchanged | Exact fixed-branch max identity; not a prohibition on changing the crossing and witness cutoff |
| 20261107-referee-2/MH1 | New paper theorem, self-audit | Arbitrary-cutoff two-error moment assembly from actual uniform source suppliers, retaining every source hypothesis |
| 20261107-referee-2/MH2 | New paper theorem, self-audit | Shifted crossing/cutoff and source-qualified six-case count |
| 20261107-referee-2/MH3 | New paper theorem, self-audit | Uniform detector loss coefficient 41/42, including the high-bin complement |
| 20261107-referee-2/MH4 | New scoped diagnostic/no-go | No uniform positive row-envelope discount from only the marked improvement; a scalar parameter family, not a realized arithmetic counterexample |

No new claim is described as PROVED_IN_LEAN. The accepted upstream proofs
are not reclassified as new Referee discoveries. Earlier GL1-GL4 acceptance,
NC/PF qualifications and spectral reviews are carried forward at unchanged
source dependencies instead of being rerun as new work.

### E. Independent Mathematical Reconstruction

#### E1. Exact notation and the reviewed RC statements

Use k for the retained plain-capacity parameter, NOT the inverse-moment
constant also called kappa in some Lean declarations. Put

```text
1/2 <= k <= 3/4, 0 <= delta <= 5/6, 0 <= x <= 1/2,
c = x/(3*k), Dk = 3-x-2*c,
A = 2*(1-c)*(1-x)/Dk,
s = 5/6-delta, Bk = s+delta*A,
r_k(x,t) = [c+(2-2*c)*t-x]/Dk,
I(r) = 1-delta*[x+(1-x)*r],
P(t,r) = 1-delta*[c+(2-2*c)*(t-r)],
S(t) = 1-delta+delta*A*(3/2-t),
L(t) = 1-delta+s*(t-1),
t_k = 1+delta*A/(2*Bk),
R_k = 1-delta+s*delta*A/(2*Bk).
```

In the actual low-bin fiber, delta=2*a-1>0, x=F.q/delta,
r=F.r and m=F.m. The delta=0 face is a separate closed scalar extension,
not division by zero in an arithmetic fiber. Dk>=11/6 and Bk>0.

RC1 states, for every t in [1,3/2],

```text
I(r_k)=P(t,r_k)=S(t),
23/37 <= r_k <= 1,
1/3 <= t-r_k <= 1/2.
```

For an independent check, multiply Dk by 3*k. The resulting denominator
`Dbar=9*k-3*k*x-2*x` is >=11/4. The numerator is
`(6*k-2*x)*t+x*(1-3*k)`. At t=3/2 it equals Dbar. At t=1,
37*numerator-23*Dbar equals `15*k+9*x-42*k*x`, nonnegative by the four
rectangle vertices. The cofactor inequalities reduce to
`x*(3*k-1)>=0` at t=1 and equality 1/2 at t=3/2.

If m>=t-r-gamma on the plain side and gamma<=1/12, then m>=1/4.
Hence the requested plain width `(1-2*m)/(6*k)` is <=1/6<7/37, with
slack 5/222. For r>=23/37 and r<1, choose inverse width
`z=(1-r)/2-nu` when positive, retaining nu>0. Then r+2z<1 and
2r+8z<3; before subtracting nu the latter has slack >=9/37.
These are admissible requests to the original slot-selection theorem;
the resulting discrete selection still pays its mesh loss.

RC2 uses all four raw alternatives. Before errors they are
`max(1,(1+5*r)/6)-delta*r`, `max(1,2*m)-2*delta*m`,
`1-delta*r-2*q*z`, and `1-2*delta*m-2*q*z`.
Their errors are respectively `2*epsilon+rho`, `4*epsilon+rho`,
`2*epsilon+delta*mesh+rho`, `4*epsilon+delta*mesh+rho`.
The raw unmarked MAX must not be dropped: m<=1/2+75*epsilon allows
an additional 150*epsilon, already paid in the conservative 159 coefficient.
RC1 and the inverse/zero-capacity fallbacks prove the stated
`max(S(t),L(t))+159*epsilon+rho+mesh+7*nu` bound. Balancing S=L gives
t_k and R_k. No positivity of the capacity-only Delta index was needed.

RC3 asserts, on the entire closed rectangle,

```text
E_k = -1/48+(2/3)*delta+delta*x/6-(13/16)*(1-R_k) <= -M(k).
```

Set v=3-4*k, Pbar=(6*k-2*x)*(1-x), J=s*Dbar+delta*Pbar.
Pbar>=1, Dbar>=11/4 and J>=5/6>0. Direct algebra gives

```text
H = [2+delta*(14-16*x)-96*(1/5000+v/1600)]*J
      -39*delta*s*Pbar
  = -96*J*(E_k+M(k)).
```

H has coordinate degrees at most (2,3,2) in (delta,x,v). I independently
reconstructed its tensor Bernstein coefficients by exact rational evaluation
and inversion of the three Bernstein evaluation matrices. I did not import
the author's power coefficients or coefficient arrays. Each full x,v box
has 36 positive coefficients, with these minima:

| delta box | Minimum coefficient |
| --- | --- |
| [0,1/4] | 38353/60000 |
| [1/4,1/3] | 16771/120000 |
| [1/3,3/8] | 1729/120000 |
| [3/8,31/80] | 8329/1200000 |
| [31/80,2/5] | 17861/2400000 |
| [2/5,5/12] | 1231/75000 |
| [5/12,1/2] | 319/6000 |
| [1/2,2/3] | 7067/15000 |
| [2/3,5/6] | 69827/30000 |

The Bernstein basis is nonnegative and sums to one on each rescaled box.
The finite exact calculation therefore proves H>0 everywhere on the
covered rectangle; this implication is not a numerical-grid assumption.
RC4 follows by adding (13/16)*loss. Its high-bin exponent gives
`-1/48-delta/16<=-7/96`, so that complement is retained.

#### E2. MH1: actual arbitrary-cutoff, two-error source assembly

Fix an actual `D:HighData Delta`, `F:SourceData D` and
`counts:CountParameters F.modulus top D.t`. Fix k>1/2 with
`51/100<=HeckeZeroSupremum.beta`, `2*HeckeZeroSupremum.beta-1<=k` and
`D.ell j<=detectorMeshAt k D.t/200` for every actual slot j.
All source exclusions, fixed ray/conductor gates and original HighData
conditions remain hypotheses. Write rho=D.t>0.

Then there is an integer J>=0 such that, for every character eta, there is
C>0 and a sufficiently large Z threshold, uniform in the batch cutoff,
with the following property. For every admissible actual source batch at
U=Z^d, d>=1/200, and EVERY real cutoff tstar, all nonempty fibers satisfy
the original raw inverse and inverse-marked fields with error rho, the
original plain-unmarked field with error rho, and the literal plain-marked
field with error rho/2 and capacity `2*m+6*k*sum_selected_widths<=1`.
The common constant at height H>=0 is C*(1+H)^J.

Here admissible means the EXACT original source equalities: rows contained
in a set with rowNorm>=Z^(1/100), `B.data=sourceMomentData`, profile equal
to the source w, widths D.ell/d, upper profile 2, external real part 17/50
and absolute external imaginary part <=H. The inverse tests retain n<=2,
sigma in [0,1], frequency in [-H,H], and both original/scaled profiles.
The plain tests retain j+k<=2 and the actual two polynomial factors and
physicalProduct of an actual selected subset. The inverse-selected width
tests remain strict. The application additionally retains d<=7/8,
51/100<a<=1, nonunit/residue masks, fixed amplitude bins, reverse flag,
all-slot identification and rowNorm<=Z^(d-rho). None is erased.

Proof: combine `source_batch_inverse_fields`,
`source_batch_plain_marked_fine_half`, and
`source_batch_plain_unmarked`. The zero-input hypothesis of the third
is supplied by `source_bands_half` followed by `plain_inputs_at` under
the same full-family license. Intersect the three eventual-Z statements.
Take J=Ji+Jm+Ju and C=Ci+Cm+Cu. Since 1+H>=1, each original constant is
bounded by the common one, without changing ANY exponent. Every supplier
quantifies tstar after its threshold, so the intersection remains uniform
in tstar. At H=Z^(2*tau), 0<tau<=1, this has the same polynomial height
dependence as the existing source interface. No new threshold depending
on a growing cutoff, selected row or frequency is introduced.

The existing generated `source_moments_at_kappa` already performs this
constant assembly, but explicitly weakens U^(1+rho/2) to U^(1+rho), then
returns `SourceMomentBoundAtKappa`. Its nested `SourceMomentsAt` quantifies
only batches at `HeckeDetectorAdaptiveCutoff.cutoff (2*a-1) q`.
Thus its existing declaration is not MH1; a separate two-error,
cutoff-parametric wrapper is needed. This is a proved paper assembly of
available suppliers, not an assumed RH-strength input.

#### E3. MH2: moving the crossing AND the cutoff

Assume 0<delta<=5/6, 0<rho<=delta/12 and the k,x domain above. Define

```text
omega = s*(1-x)/(2*Dk*Bk),
t_hat = t_k-(1-x)*rho/(2*Dk*Bk),
r_hat = r_k(x,t_hat)+rho/(2*delta*Dk),
T_hat = R_k+(1-omega)*rho.
```

Exact substitution proves

```text
I(r_hat)+rho = P(t_hat,r_hat)+rho/2
             = L(t_hat)+rho = T_hat.
```

The domain is preserved, not assumed. The useful identities are

```text
t_hat-1 = (1-x)*(delta*(1-c)-rho/2)/(Dk*Bk),
r_hat-r_k(x,t_k) = rho*s/(2*delta*Dk*Bk),
1-r_hat = s*(1-c-rho/(2*delta))/(Dk*Bk).
```

Since c<=1/3 and rho/(2*delta)<=1/24, these imply
`1<=t_hat<=t_k<=3/2` and `23/37<=r_hat<=1`.
Moreover

```text
t_hat-r_hat >= 1/3-rho/(2*delta*Dk) >= 41/132,
0 <= omega <= 1/6,
T_hat >= 1-delta+rho.
```

For the last upper bound on omega, use Bk>=s and
Dk>=3*(1-x); the s=0 case is immediate.

Here is a fully specified scalar count theorem. Let U>1, Cstar>=0,
0<epsilon<=1/1000, mesh>=0, nu>0, and N>=0. Let real r,m obey
`r<=t_hat+epsilon`, `m>=t_hat-r-epsilon`,
`0<=m<=1/2+75*epsilon`. Suppose N has BOTH raw no-slot bounds and,
for every admissible z, the marked bounds from E1, except that the
plain-marked error is rho/2. All four coefficients are bounded by Cstar.
Then

```text
N <= Cstar*U^(T_hat+159*epsilon+mesh+7*nu).
```

Proof by exhaustive cases follows. It also proves the result for every
actual Fiber supplied by MH1, using the original coefficient/count lemmas.

| Case | Bound used and paid loss |
| --- | --- |
| r>=1 | Raw inverse: exponent is 1-delta+s*(r-1)+rho+2*epsilon; at most T_hat+(2+s)*epsilon |
| r<1, r>=r_hat, (1-r)/2>nu | Inverse marked z=(1-r)/2-nu; I decreases in r, so at most T_hat+2*epsilon+delta*mesh+2*delta*x*nu |
| r<1, r>=r_hat, (1-r)/2<=nu | Raw inverse <=1-delta+rho+2*delta*nu+2*epsilon <=T_hat+2*delta*nu+2*epsilon |
| r<r_hat, m>=1/2 | Raw unmarked max restored: <=1-delta+rho+154*epsilon <=T_hat+154*epsilon |
| r<r_hat, m<1/2, (1-2*m)/(6*k)<=nu | Raw unmarked <=1-delta+rho+6*delta*k*nu+4*epsilon |
| r<r_hat, m<1/2, (1-2*m)/(6*k)>nu | Plain marked at z=(1-2*m)/(6*k)-nu; m>=t_hat-r-epsilon costs <=2*epsilon; P increases in r, so exponent <=T_hat+6*epsilon+delta*mesh+2*delta*x*nu |

In the last case m>=41/132-epsilon>=1/4, so z<=1/6<7/37 and
the physical selection is legal. In the inverse case r>=23/37 preserves
both strict constraints exactly as in RC1. Every displayed loss is bounded
by 159*epsilon+mesh+7*nu. The actual common coefficient is still
`fiberConstant(C,height,K0)=(192*(1+height)*C)*max(1,K0)`; the raw-inverse
constant K0 and its original large-U threshold are retained.

Empty fibers need no witness; their count is zero. For nonempty source
batches, the finite aggregation factor is unchanged:
`card(Label)*(dyadicLength U)^2*card(B.Bin)`.

To choose the new actual witnesses, use
`actual_supported_witness_family`, whose threshold precedes
`forall tstar, 1<=tstar -> tstar<=3/2`.
For each actual row, choose it at t_hat(delta,rowMean/delta). In a fixed
amplitude bin, the existing rowMean equality makes the cutoff common.
This is a new invocation of the same witness existence theorem.
An equality-only `recut` cannot turn an old witness into one at an unequal
cutoff. The original zero windows, conductor bounds, witness errors and
height budget are all retained.

#### E4. MH3: uniform detector saving despite a zero-saving face

For delta<=3/4 one has omega>=1/42. Here is an algebraic proof.
For fixed k,x, `s/(s+delta*A)` is decreasing in delta, so it suffices
to set delta=3/4. Write P=2*(1-c)*(1-x), so A=P/Dk. At that endpoint
omega>=1/42 is equivalent to

```text
21*(1-x) >= Dk+9*P.
21*(1-x)-(Dk+9*P) = 2*[c*(10-9*x)-x] >= 0,
```

because c>=4*x/9 and x<=1/2. RC3 now proves
`E_k+(13/16)*(1-omega)*rho<=-M(k)+(13/16)*(41/42)*rho`.

For 3/4<=delta<=5/6, no positive lower bound on omega is needed.
Since `R_k<=1-delta+s/2` and x<=1/2,

```text
E_k <= 61/192-15*delta/32 <= -13/384.
M(k) <= 33/40000, rho<=5/72,
33/40000+(13/672)*(5/72) < 13/384.
```

Together with omega>=0 this proves the SAME displayed detector bound.
For 5/6<delta<=1 retain the original cutoff 3/2 and high-bin count
`1-delta+78*epsilon+rho`. Its functional is at most
`-7/96+(13/16)*(78*epsilon+rho)`. The exact inequality
`33/40000+(13/672)*(1/12)<7/96` absorbs the same rho/42 discount.
The common auxiliary loss 159*epsilon+mesh+7*nu dominates 78*epsilon.
Thus the complete detector result in A includes every delta bin.

The original count-smallness hypothesis may conservatively remain
`159*epsilon+rho+mesh+7*nu<=1/32`; no relaxation of that separate gate
is claimed. Actual source delta>1/50 and D.t<=1e-8 make rho<=delta/12
automatic on this application, but the theorem states it explicitly.

### F. Counterexamples And No-Go Results

MH4 concerns a precisely limited class: scalar row bounds obtained only
from the four raw alternative exponent inequalities, with unchanged inverse
and unmarked error rho. It does not concern every possible arithmetic
argument about the actual row population.

For delta=5/6, x=0, any k in [1/2,3/4], any rho in (0,5/72],
and ANY tstar in [1,3/2], take the scalar lengths r=tstar, m=0.
The length constraints hold in the zero-error envelope. The no-slot inverse
exponent is exactly `1/6+rho`; inverse marked is unavailable since r>=1;
plain marked gives `1+rho/2` and plain unmarked gives `1+rho`.
Also R_k=1/6 and omega=0. Thus the least available raw exponent equals
R_k+rho. No fixed positive fraction of rho can be saved uniformly in
this row envelope just by lowering the marked moment or adjusting tstar.
This is a parametrized family of scalar configurations, NOT an infinite
family of genuine arithmetic fibers. With positive epsilon, take the
zero-error limit to interpret the statement about leading exponents.

An exact diagnostic is k=3/4, delta=5/6, x=0, rho=1/120.
The MH2 cutoff is 599/400. Choosing the long-row length r=599/400,
m=0 gives exponent 7/40=1/6+1/120. This row r is not the crossing
r_hat=1. No claim is made that an actual Hecke fiber realizes this tuple.

The surviving result is MH3: the no-saving face has ample independent
detector margin, so it does not prevent a uniform COMPLETE DETECTOR
discount. An objection demanding a uniform per-row discount would
therefore impose an unnecessary stronger prerequisite.

The compiled `marked_half_error_survival` remains valid:

```text
max(other+rho,marked+rho)-max(other+rho,marked+rho/2)
  = min(rho/2,max(0,marked-other)).
```

It fixes other and marked. MH2 changes the crossing and cutoff before
aggregation and MH3 uses the rest of the functional. Neither contradicts
that helper. No entire method, signed summation technique or feedback
strategy is declared impossible.

### G. Original-Carrier And Covariance Audit

This work uses original ideal-character detector fibers. It does NOT
identify them with rational Mobius atoms or actual-prime VF sources.
The two polynomial factors, selected physicalProduct, prime exclusions,
nonunit/residue conditions, fixed external real coordinate, height window,
reverse flag, amplitude bins and dyadic left/right lengths are unchanged.
Changing which supported witness is chosen can change the fiber partition;
the count is reassembled using the original exact finite partition, not
assumed to have the old fibers term by term.

No historical source payment is reused: selected subsets remain genuine
subsets, and the same original selection supply and mesh loss are used.
The argument preserves whole supplied squared norms. It does not discard
their signed cross terms or infer global covariance from local favorable
signs. The all-selected J=empty outer tuple still has zero outer cross Gram;
no saving is attributed to a nonexistent outer pair.

The native signed-pair consequence still retains its squarefree diagonal
and all positive-lag signed pairs. The native Mertens transfer is through
the actual Dirichlet-to-Hecke L-function identity, not coefficientwise
equality of the two arithmetic carriers. Canonical HIGH is reached only
after that existing transfer and the fixed-Lambda split. No unsigned
model count is substituted for the signed global statistic.

### H. Quantifier And Circularity Audit

All scalar results quantify over the displayed closed rectangle. Analytic
use has k>1/2, and a fixed lower floor k0>1/2 is chosen before constants,
fineness and large-scale thresholds. The current supplied theorems permit
pointwise constants depending on fixed k. A uniform analytic constant over
a varying interval of k is NOT proved merely by the scalar rectangle.
For k<3/4, full-family `2*beta-1<=k` must come from an already certified
boundary, not the boundary one wants to prove. At beta<51/100 the supplier's
lower-beta case is unavailable; that case must be handled separately by
its already stronger zero bound, not silently ignored.

The cutoff choice may depend on a row's actual amplitude because witness
existence is uniform in tstar and classMean is constant on its amplitude
class. The source moments are uniform in all those batches. No exchange
of nonuniform limits is used. The source is fixed before characters and
the large-scale limit; constants are independent of Z once parameters
and the character are fixed.

Forward implication audit: MH1+MH2+MH3 give a stronger detector input,
NOT the canonical objective. They need the source/batch integration and
the complete same-probe comparison. Reverse implication audit: no
equivalence of the canonical VF objective with these specific
ideal-character moment/cutoff statements is established or assumed.
The scalar assertions are proved independently, and the arithmetic
inputs are actual existing suppliers. This is not TARGET_EQUIVALENT
relabeling or an assumed global bound hidden in a new norm.

In contrast, the all-window canonical HIGH prefix-energy criterion
includes h=1 and is pointwise-target-equivalent at the stated exponents.
No weaker full-window-only criterion or centered energy with the coherent
mean removed is used here. No uniformity for a growing Lambda is claimed.

### I. Constructive Repairs And Complete Return Budget

The minimal repair is NOT to strengthen every moment. Preserve the
literal marked field, make the cutoff an explicit parameter, and invoke
the existing supported-witness supplier at t_hat. Retain the old APIs for
old callers. The generalized capacity k never replaces physical Delta.

After that source integration, the proposed detector budget in the
actual native HIGH comparison is

```text
(13/16)*(159*epsilon+(41/42)*rho+R_slot+7*nu)
 + 2*zeta + (3/2)*mu
 + (26*e+(N+8)*eps+loss+mesh/6)
 + (logCost+heightCost+momentCost) + saving
 <= M(k).
```

Here R_slot is the slot mesh in the count, not a square-root index;
epsilon and eps are the distinct original error parameters. Everything
outside the detector moment coefficient is still charged. This is a
candidate replacement for the old sufficient cap 49/440640 only AFTER
the changed source/count is wired into the consumer. The old count
smallness gate may remain unchanged. Neither the extra Census margin
nor the 13*rho/672 improvement is automatically a new beta saving.

The unanchored `actual_high_probe_from_raw_moments_tilted` assumes
physical 0<=Delta<=1/8, beta>=7/8, and
`Delta+sigma+nu+dyadCost<=saving+(beta-7/8)`. It cannot be applied by
inserting a negative capacity index. However, the existing anchored
return already uses the certified 7/8 ceiling and an actual source
below that boundary: `native_fixed_slot_anchored_probe_bounds_low_first`
and `native_beta_le_slot_calibrated_boundary_low_first` were inspected.
This corrects any inference that the repository lacks ALL below-7/8
comparison machinery. Generalizing the old declaration is one option,
not a compulsory new prerequisite if the anchored consumer can be reused.

On the existing geometry, LOW is
`3/16-9*tilt+positive_loss` and the principal shift is
`-11/16-8*tilt`; their difference remains `7/8-tilt`.
The original gate `24*tilt<=(7/8)*D.rmin` remains a sufficient condition
of this construction. Recalibrating rmin to the actual slot minimum has
ALREADY been done in the certified baseline. Increasing HIGH reserve
while leaving this binding LOW/principal comparison unchanged proves
no new exponent. Nor is that gate a universal impossibility theorem.

All selected/unselected, central, remote, exceptional, conductor,
principal, geometric, floor, window, dyadic and height costs remain.
The new fineness requirement at k must actually hold for the source.
If new slots are constructed to secure it, compare the resulting full
bound against the previously certified strongest boundary, not merely
against the weaker minimum of a freshly refined source.

### J. Competing Proof-Strategy Assessment

Continue the OAI-NNS consumer task: it uses an already proved arithmetic
input and now has explicit branch-level and detector-level gains, without
adding an RH-strength assumption. Formalization should consume the changed
estimate immediately rather than produce an isolated arithmetic constant.

Keep weighted fourth-moment averaging and retained tuple/rescaling decay
as distinct possible improvements. The current result uses the literal
available marked squared-norm field; it does not manufacture a new
fourth-moment theorem from a second moment or double-credit a saved loss.

Carry forward CODIV GL/NC/PF, NYMAN FT, Owner RS/SG and Wheel LR at their
actual scopes. Coordinator PG's coefficient-blind signed-graph obstruction
does not prohibit this coefficient-bearing supplied-moment consumer.
The nine protected routes VF-LOW, SAT, JOH, CODIV, OAI-NNS, NYMAN,
FINITE-AC, CORR4 and MU-LIFT remain independent workspaces. This support
review neither resets investigator rotation nor consumes their scheduled
coverage. No alternative strategic campaign is silently substituted.

### K. Original Adversarial Research And Executed Checks

Beyond reviewing RC1-RC4, I derived the two-error optimum, proved the
shifted capacities and all six branch cases, located the fixed-cutoff
source restriction, and proved the whole-detector 41/42 discount despite
the exact no-saving face. The novelty is relative to the inspected live
source and reports; no claim of priority in the external literature is made.

The independent standard-library Fraction verifier reproduced all nine
Bernstein minima using tensor interpolation. It then tested 4,536 shifted
parameter configurations, 178,128 raw-branch cases, and 126 high-bin cases,
all with exact rational arithmetic. Branch counts: 83,916 long;
33,681 inverse; 18,483 inverse-zero; 10,077 plain; 9,959 plain-zero;
22,012 unmarked. The equality fixture and both rational margin-absorption
inequalities also passed. Syntax compilation passed.

Only the positive Bernstein certificate establishes the corresponding
all-real RC3 inequality computationally. The MH grid is a regression test
of the preceding symbolic proof, not an assertion that every arithmetic
row has been enumerated. There is no overflow, floating-point cancellation,
probable primality, random seed or extrapolated asymptotic sign here.
The exact executed verifier and output are embedded below for continuity.

### L. Formalization Guidance And GitHub Actions Verification

At the live snapshots, no open or draft PR was returned. Recent merges
were checked against actual metadata, not report titles:

| PR | Exact head | Merge / relevant evidence |
| --- | --- | --- |
| #1104 | b4d44d7c634cf8c601c94865ab19f3aa5bf23337 | Main 3de4f7331e5fe55ad0e404dc8463b1df56c19330, merged 16:56:31Z; instruction change, not new mathematics |
| #1103 | 06dde8d85985c86481680610b6c86c663be4e242 | Merged aa10b310efb2a095fd4c69dc965e6bde0bd135d6 at 15:44:29Z; run 42386987885, job 128446349776, completed SUCCESS |
| #1102 | 5b246ac81398ae8ee8f177dc9acda18288765a4e | Merged dadd9cd7b0a36b4298db30a33c2a1e4b6eb36dcc; run 42364367658 completed SUCCESS; unchanged CODIV review carried forward |
| #1101 | 690477c55070aabafefbaff883880a5c37c44370 | Merged 5b94286066a5bb152ec845a76bddaa70ecfd7024 at 15:04:22Z; reuse policy, not an endpoint theorem |
| #1091 baseline | 6778fd4c25b0f369d311e6e71223e168e329b4bf | Run 41898325686, job 126813711885 completed SUCCESS; exact terminal logs inspected |

For #1103, all 14 returned exact-head check runs succeeded. Its synthetic
merge is `e9e581ca346364dd6bfa0ec492cdf6ea2a7d7832`. A direct recursive-tree
comparison with live main found only instruction, workflow/validator and
documentation changes, not Lean or supplier-generation changes. This is
unchanged-dependency reuse, not a fresh full-main Lean rebuild.

The final #1104 check-run refresh returned 10/10 completed SUCCESS checks
at its exact head, including portfolio-audit run 42393261564. These are
verified status metadata, not a new audit of every unrelated theorem
tested by those workflows.

The #1103 artifact 13579504958 was downloaded and its actual generated
source inspected. ZIP SHA256:
`1e7455779f49942a7ce9d5d0ee00d17601ad83639d43541e5a7e9afd6dee5e1f`.
SourceFeedback, SourceMoments and RowCount retain the relevant literal
types, capacity and assumptions. Their terminal axiom output lists only
propext, Classical.choice and Quot.sound. Two upstream Wiener sorry
warnings occurred during the prerequisite build; they are disclosed,
and the selected terminal axiom reports contain no sorryAx. This is not
a repository-wide assertion that every upstream declaration is clean.

The baseline log directly certifies the true-source-minimum beta and
Mertens terminals, plus `native_beta_le_explicit_slot_count`, with the
permitted standard axioms. The actual source minimum and the anchored
comparison are therefore credited rather than downgraded to an assumption.
None of this gives RC or MH inherited Lean certification.

Recommended implementation-sized units, for the Architect to prioritize:
1. A cutoff-parametric two-error source wrapper plus generalized raw
   count, preserving MH2's admissible selections and zero cases.
2. Its fixed-amplitude/source-count consumer with the new witness choice
   and MH3 detector inequality; then expose the unchanged return costs.

Do not implement a blanket rho/2 substitution, a negative physical
HighData parameter, a zero-cost discrete selection or an automatically
iterable feedback theorem. This invocation ran no local Lean, modified
no Lean source and launched no workflow or proof PR.

### M. Continuity And Specialist Handoffs

All seven role reports from both 2026-11-07 and 2026-11-06 (Eastern dates)
were retrieved; relevant mathematical findings, selected derivations,
corrections and resume capsules were read. Unrelated embedded programs
were not all re-executed. TODAY=AVAILABLE for all seven at intake;
YESTERDAY=CARRY_FORWARD. No scheduled run was presumed to have completed.

| Report | 2026-11-06 blob | 2026-11-07 intake blob |
| --- | --- | --- |
| Coordinator 00/90 mirrors | 8812a90540fb511279b5f4ce08e108ef717d5ef1 | 4a71edcce4c44a309640d36e9453d016e5b188a9 |
| Owner 10 | 1856a96aaaa9d86a5ee2d59ffe50ced936443fa6 | 432fc87602f97318fdac212002b52ac29f12a0e0 |
| Analytic 20 | 7997620b6ab7eb0701296994734ee910df3c3ba1 | 1315b3c9deba1148338d9023af349ee8a246dae7 |
| Wheel 30 | 3099558194a00358962ff1844bf283e625b9283d | b973552f1574e39afe6dbc165bde3635f12c9ead |
| Census 40 | c34ac074296e8b2e5b20dee3a2ce02518571206c | 3fae830e34c590d32c31ad77cad3ace833eb3ff5 |
| Referee 50 | da3265467c799e9d21832ab25245617ba3b15a54 | 787a9030cc6d6f8f63fa89cd3a99d7cf54e25ea5 |
| Lean 60 | b8bfe3ce9c20d7903395364efb39bcec974c8a2f | 7df1e5d73bfe6cbbb2fa76d6380d7d456a938c11 |

The external inbox blob is unchanged
`038018145c0fddb2f6306c0712373adf9cd1ea52`, with no entry newer than
October 18. EXT-20261018-PNT-1, EXT-20261017-XCOORD-1 and
EXT-20261014-5 retain source/normalization/cutoff cautions, not authority
for a new Hecke estimate or an old superseded research priority.

- Proof Architect: register RC1-RC3 accepted at paper scope; prioritize a
  consuming MH interface only if its full return can use the saved budget.
  Reuse the existing anchored below-7/8 comparison rather than declaring it absent.
- Analytic Type II: independently review MH2-MH3; retain separate rho and
  rho/2, and give the exact change in admissible complete parameters. Keep
  CODIV and NYMAN work independent; no automatic feedback is licensed.
- Owner Payment: no rational-to-Hecke identification is needed or proved.
  Carry forward RS square-sampled reserve work and the due native routes;
  a better reserve alone also needs its actual consuming inequality.
- Finite Wheel: check the shifted 41/132 cofactor lower bound and strict
  inverse capacities against actual selected subsets; retain your LR
  multiplicity qualifications and all CORR4/MU-LIFT corrections.
- Prime Census: RC certificate independently reproduced. The extra
  interface restriction is `SourceMomentsAt`'s old cutoff. Review MH's
  zero-saving face versus the valid uniform functional discount; no
  further unchanged RC parameter scan is needed.
- Lean Verification: the original suppliers already quantify arbitrary
  tstar. Preserve the literal marked exponent in a new wrapper, rechoose
  bounded-cutoff witnesses, and consume the count. Require exact-head
  warning-fatal/type/import/axiom evidence; do not label this paper result compiled.

### N. First Independently Missing Mathematical Ingredient

The immediate missing FORMAL consumer is the cutoff-parametric two-error
source/count connection proved on paper above. Its source supply is not
an unproved new arithmetic hypothesis.

The first unresolved ENDPOINT inference is a complete, source-compatible
parameter comparison that uses the improved detector allowance to prove
a fixed improvement over the strongest applicable `b_base`, with the
same compensated LOW/HIGH/principal join. Specifically, one must show
which binding complete-return constraint changes, retain full-family
license and source fineness, and pay all height/conductor/remote and
complementary costs. Leaving LOW/principal crossing and legal tilt
unchanged does not meet this obligation. No new universal covariance
assumption, all-selected inverse estimate or square-shell bound is
installed as an entrance requirement.

### O. Next-Run Resume Capsule

```text
RUN: 20261107-referee-2, scheduled 12:03:00 EST, RUN_ID_UNAVAILABLE.
AUTHORITY: main 3de4f7331e5fe55ad0e404dc8463b1df56c19330.
ACK: COMPLETE_SIGNED_HIGH_ATTACK_V1; CANCELLATION_CHAIN_REUSE_V1;
     PAID_BASELINE_EXACT_CONSUMER_V1; NO_PIGEONHOLING_ROUTE_SELECTOR_V1.
UPSTREAM: openai/math 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
REVIEW: RC1/RC3 ACCEPT, RC2/RC4 ACCEPT_WITH_SCOPE, PAPER_PROOF only.
NEW: MH1 arbitrary-cutoff two-error source assembly;
     MH2 shifted crossing/cutoff and six-case actual-fiber count;
     MH3 detector coefficient 41/42 on rho, with high-bin complement;
     MH4 scalar long-face no-uniform-row-discount, not arithmetic refutation.
STATUS: MH PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING;
        no new formalization and no new global exponent.
COUNTEREXAMPLE SCOPE: delta=5/6,x=0,r=tstar,m=0; only raw scalar envelope.
SOURCE WARNING: old SourceMomentsAt fixes old cutoff; underlying source
                suppliers and supported witnesses quantify arbitrary tstar.
RETURN WARNING: anchored below-7/8 machinery ALREADY exists; extend its
                actual input, do not call its existence an unpaid premise.
BASELINE: true source minimum /24, explicit fallback 1/(288*N), unchanged.
NEXT: independently check MH proof and implement its immediate source
      consumer; audit which complete constraint could actually improve.
DO NOT: halve inverse/unmarked errors; use negative physical Delta;
        assume k=1/2 analytically; erase bin/height costs; rerun unchanged
        RC grids; optimize the astronomical denominator; claim eta.
CANONICAL VF/RH: OPEN; eta_gate=SEARCH_BROAD.
```

Tools allowed exact scalar computation, GitHub source/log/artifact inspection
and own-report publication. Direct git transport returned a CONNECT 403;
the GitHub connector provided the required immutable source instead.
An expected generated anchored module was not a checked-in file; its
source endpoint, pinned generator and successful terminal log were read,
not treated as a missing theorem. No local Lean was executed. All
computational sessions completed. Only this authorized own report is
changed remotely; no other report, shared policy, issue, branch, PR,
workflow, permission, schedule or agent launch was modified.

The early checkpoint was published at commit
`1e123d9e786d7f521bd3f97fb51aa3d8657b00c3`, blob
`5072fbc93c8d10f31c72fd1ee35d8d97824d1aba`, and immutable readback matched.
The final synthesis receipt is appended only after successful publication
and exact readback verification.

Prepublication freshness at 2026-11-07T17:28:17Z: main was unchanged.
The full agent-reports tree differed from intake only in this own
already-verified checkpoint; both days' upstream handoffs and the external
inbox were unchanged. No new source-dependent review was thereby required.

### Material Source Ledger

Repository sources below are pinned to main
`3de4f7331e5fe55ad0e404dc8463b1df56c19330`; hashes are original Git blob
identifiers, not hashes of local display/scratch copies.

| Path / declaration source | Git blob SHA |
| --- | --- |
| research/oai_434/VF919NativeStrictSevenEighths.lean | efbf2780f0b453a702fb8847f2d360d8faf0fa66 |
| research/oai_434/VF919NativeStrictMertens.lean | b33a4883e1ddb0551b0f11f062bce46680d87450 |
| research/oai_434/VF919LowFirstSlotAnchoredEndpoint.lean | d9373ce13b703b1e5f4e4bcde158ef9004d250dd |
| research/oai_434/VF919ActualSlotMinRetighten.lean | 138c4726085995b966204406805f70082402bec4 |
| research/oai_434/VF919ExplicitFixedSourceSlotCount.lean | bad5aab0a60e96d19e7c9550cd7c0a072288bc0f |
| research/oai_434/VF919TiltedHighAssembly.lean | 883141e0af896d4132bfc4ffa076e2d265ece5c9 |
| research/oai_434/VF919TiltedHighCentral.lean | 6f75563d84161a023e4750df69ad0def460c0513 |
| research/oai_434/VF919TiltedProbe.lean | 0f95d412bce773d50e71b1809ab9942653e66812 |
| research/oai_434/VF919OriginalGainComponentLedger.lean | 5e7cea836158fc819f37e71da5fe55c8a8dce44e |
| research/oai_434/RetainedSlotFeedback.lean | 51628cad59734f948224510f7ac94fd68efaacfb |
| research/oai_434/Feedback/Range.lean | 743ad5cca9aa500dcf3f34567cbc6e5f6fa89223 |
| scripts/lean/slot_anchored/prepare_anchored.py | 0bac9047afaa8e9ddc5ac246be2d0fe7d6efa725 |

Original source prefix:
`openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a:lean/OAI/NumberTheory/DirichletL/`.

| Relative source | Git blob SHA |
| --- | --- |
| Hecke/DetectorRawFiber.lean | ee826e81bbec1df5820f26aa15bce53bcb675cd6 |
| Hecke/DetectorRawBranches.lean | 16adf0ef89dafd510b98dd44e9a5461e3fbf351d |
| Hecke/DetectorBranchBudget.lean | 05e7948b9df4c2385d08db006fbdbae56f62b0c3 |
| Hecke/DetectorRowCountCrossing.lean | 43adea8cf7c2ec8639f5b3eb0403d240e4cc8115 |
| Hecke/DetectorRowCountOptimization.lean | 7aa80cdbfadcbf29c6b78199ec15674c99b161f4 |
| Hecke/DetectorRowCountEndpoint.lean | 24ec6bcdaf9e017c41a39c12bc503c86a28d5ef5 |
| Hecke/DetectorCountFromMoments.lean | 91a6e8aa5e0336d6006a5211e77a13f7f8aba348 |
| Hecke/DetectorFixedAmplitudeCount.lean | 0b83ce168a0dd8b82e3d50fb6c04b2f05d1b1d18 |
| Hecke/DetectorRowCount.lean | 27d8321e816fd7eac1369f44e125ee53466cd8d0 |
| Hecke/DetectorPlainFiberCount.lean | 2c8ebf5316ef5ab31c3076a7113fa576905fae7d |
| Hecke/DetectorSupportedWitness.lean | 42f1060befe86b8455777ecfa5ade9a825edd9f8 |
| Hecke/DetectorAdaptiveCutoff.lean | bdc80c29fa1f135ec5c1a196e418f9f851c40957 |
| Hecke/DetectorAmplitudeFirst.lean | e2f8a9451914f5ef1085e24b63988dc765ba7c62 |
| Detector/DetectorInverseFields.lean | b0f4775ed6e9fa2047eeae6f4c18df0896fb1992 |
| Detector/DetectorPlainMarkedFineField.lean | d4b3e96991e97155c064df03b988a5787da3252a |
| Detector/DetectorPlainUnmarkedRestrictedField.lean | 5722e67d4c368d2926683e01a347a04d3237f971 |
| Detector/FinalAssemblyMomentInput.lean | 436856065bd974c5ca52ac43b751a716f454ed20 |
| Detector/FinalAssemblyChosenData.lean | 94b7543e8076fc514b61e89efa7141831e102c03 |
| ParametersHighData.lean | c565dc0a72c7da9a2706cdd835e69a39e8c0dc14 |
| PrimeRows/NonfloorMoments.lean | 5711ee00b7ab3fdb61d8f91d092c29781c437bfb |
| PrimeRows/NonfloorSourceCount.lean | cb3a913ac14930fc83b35214ff2585470369f0f7 |
| PrimeRows/HighFromMoments.lean | c2f8680f43e8c62dc59eedb2bf64e1788058eca0 |

Generated #1103 artifact source SHA256 values, under `research/oai_434/Feedback/`:

```text
SourceFeedback.lean 9c7abb4987d79df4489a7f8bcca176ab4427538b7260a0319f4268ceb54169df
SourceMoments.lean  62e95892524f7b5938588985c216e87e9c19fa915291e9f932396c383eac2f67
RowCount.lean       b4e7234e1c40281018455112992945f5677369ec5f373a2cba25e7d9e5c6709c
```

### Reproducibility

The following is the actual executed `referee_consumer_check.py`, SHA256
`429806283c0a778f2e3411ce52d311fcbfc7a877182477229f183de3283f5231`.
It requires only Python's standard library. Run `python referee_consumer_check.py`.
The finite grid is diagnostic; the Bernstein argument and symbolic proofs
above determine the universal mathematical conclusions.



```python
"""Independent exact audit of RC and retained marked-half consumers.

All fixtures are scalar parameter certificates, not realized Hecke fibers.
No floating-point arithmetic or numerical asymptotic extrapolation is used.
"""
from fractions import Fraction as Q
from itertools import product
from math import comb
import json


def data(k, d, x):
    c = x / (3*k)
    D = 3-x-2*c
    A = 2*(1-c)*(1-x)/D
    s = Q(5, 6)-d
    B = s+d*A
    t = 1+d*A/(2*B)
    r = (c+(2-2*c)*t-x)/D
    R = 1-d+s*d*A/(2*B)
    E = -Q(1, 48)+Q(2, 3)*d+d*x/6-Q(13, 16)*(1-R)
    omega = s*(1-x)/(2*D*B)
    return c, D, A, s, B, t, r, R, E, omega


def H(d, x, v):
    k = (3-v)/4
    s = Q(5, 6)-d
    Db = 9*k-3*k*x-2*x
    P = (6*k-2*x)*(1-x)
    J = s*Db+d*P
    margin = Q(1, 5000)+v/1600
    E = data(k, d, x)[8]
    out = (2+d*(14-16*x)-96*margin)*J-39*d*s*P
    assert out == -96*J*(E+margin)
    return out


def inverse(matrix):
    n = len(matrix)
    a = [list(row)+[Q(i == j) for j in range(n)]
         for i, row in enumerate(matrix)]
    for j in range(n):
        pivot = next(i for i in range(j, n) if a[i][j])
        a[j], a[pivot] = a[pivot], a[j]
        z = a[j][j]
        a[j] = [v/z for v in a[j]]
        for i in range(n):
            if i != j:
                z = a[i][j]
                a[i] = [u-z*v for u, v in zip(a[i], a[j])]
    return [row[n:] for row in a]


degrees = (2, 3, 2)
indices = list(product(*(range(n+1) for n in degrees)))
inverses = []
for n in degrees:
    matrix = [[Q(comb(n, j))*Q(i, n)**j*(1-Q(i, n))**(n-j)
               for j in range(n+1)] for i in range(n+1)]
    inverses.append(inverse(matrix))
cuts = [Q(0), Q(1, 4), Q(1, 3), Q(3, 8), Q(31, 80),
        Q(2, 5), Q(5, 12), Q(1, 2), Q(2, 3), Q(5, 6)]
expected = [Q(38353, 60000), Q(16771, 120000), Q(1729, 120000),
            Q(8329, 1200000), Q(17861, 2400000), Q(1231, 75000),
            Q(319, 6000), Q(7067, 15000), Q(69827, 30000)]
minima = []
for lo, hi in zip(cuts, cuts[1:]):
    values = {i: H(lo+(hi-lo)*Q(i[0], 2), Q(i[1], 6), Q(i[2], 2))
              for i in indices}
    for axis, inv in enumerate(inverses):
        previous = values
        values = {}
        for i in indices:
            total = Q(0)
            for j in range(degrees[axis]+1):
                source = list(i)
                source[axis] = j
                total += inv[i[axis]][j]*previous[tuple(source)]
            values[i] = total
    minima.append(min(values.values()))
    assert all(v > 0 for v in values.values())
assert minima == expected

parameter_checks = 0
raw_checks = 0
branches = dict(long=0, inverse=0, inverse_zero=0, plain=0,
                plain_zero=0, unmarked=0)
for ik, idelta, ix in product(range(7), range(1, 25), range(9)):
    k = Q(1, 2)+Q(ik, 24)
    d = Q(5*idelta, 144)
    x = Q(ix, 16)
    c, D, A, s, B, t, r0, R, E, omega = data(k, d, x)
    margin = Q(1, 5000)+(3-4*k)/1600
    assert E <= -margin
    assert Q(23, 37) <= r0 <= 1
    assert Q(1, 3) <= t-r0 <= Q(1, 2)
    for rho in (d/1200, d/120, d/12):
        ts = t-(1-x)*rho/(2*D*B)
        rs = (c+(2-2*c)*ts-x)/D+rho/(2*d*D)
        target = R+(1-omega)*rho
        I = 1-d*(x+(1-x)*rs)+rho
        P = 1-d*(c+(2-2*c)*(ts-rs))+rho/2
        L = 1-d+s*(ts-1)+rho
        assert I == P == L == target
        assert 1 <= ts <= Q(3, 2)
        assert Q(23, 37) <= rs <= 1
        assert ts-rs >= Q(41, 132)
        assert 0 <= omega <= Q(1, 6)
        if d <= Q(3, 4):
            assert omega >= Q(1, 42)
        assert E+Q(13, 16)*(1-omega)*rho <= -margin+Q(13, 16)*Q(41, 42)*rho
        parameter_checks += 1
        eps, mesh = Q(1, 1000), Q(1, 2000)
        for nu in (Q(1, 10000), Q(1, 10)):
            for r in (Q(0), Q(23, 37), rs-Q(1, 1000), rs,
                      (rs+1)/2, Q(1), ts, ts+eps):
                mlo = max(Q(0), ts-r-eps)
                mhi = Q(1, 2)+75*eps
                if mlo > mhi:
                    continue
                for m in set((mlo, (mlo+mhi)/2, mhi)):
                    bound = target+159*eps+mesh+7*nu
                    if r >= 1:
                        branch = 'long'
                        p = max(Q(1), (1+5*r)/6)-d*r+2*eps+rho
                    elif r >= rs:
                        if (1-r)/2 <= nu:
                            branch = 'inverse_zero'
                            p = 1-d*r+2*eps+rho
                        else:
                            branch = 'inverse'
                            z = (1-r)/2-nu
                            assert 0 <= z <= Q(7, 37)
                            assert r+2*z < 1 and 2*r+8*z < 3
                            p = 1-d*r-2*d*x*z+2*eps+d*mesh+rho
                    elif m >= Q(1, 2):
                        branch = 'unmarked'
                        p = max(Q(1), 2*m)-2*d*m+4*eps+rho
                    elif (1-2*m)/(6*k) <= nu:
                        branch = 'plain_zero'
                        p = 1-2*d*m+4*eps+rho
                    else:
                        branch = 'plain'
                        z = (1-2*m)/(6*k)-nu
                        assert m >= Q(1, 4)
                        assert 0 <= z <= Q(1, 6) < Q(7, 37)
                        assert 2*m+6*k*z <= 1
                        p = 1-2*d*m-2*d*x*z+4*eps+d*mesh+rho/2
                    assert p <= bound, (k, d, x, rho, r, m, nu, branch)
                    branches[branch] += 1
                    raw_checks += 1

k, d, x, rho = Q(3, 4), Q(5, 6), Q(0), Q(1, 120)
c, D, A, s, B, t, r0, R, E, omega = data(k, d, x)
ts = t-(1-x)*rho/(2*D*B)
assert ts == Q(599, 400) and omega == 0
assert (1+5*ts)/6-d*ts+rho == Q(7, 40) == R+rho
assert Q(33, 40000)+Q(13, 672)*Q(5, 72) < Q(13, 384)
high_bin_checks = 0
for ik, idelta in product(range(7), range(1, 7)):
    k = Q(1, 2)+Q(ik, 24)
    d = Q(5, 6)+Q(idelta, 36)
    margin = Q(1, 5000)+(3-4*k)/1600
    for rho in (d/1200, d/120, d/12):
        Ehigh = -Q(1, 48)-d/16
        assert Ehigh+Q(13, 16)*rho <= -margin+Q(13, 16)*Q(41, 42)*rho
        high_bin_checks += 1
assert Q(33, 40000)+Q(13, 672)*Q(1, 12) < Q(7, 96)
print(json.dumps(dict(bernstein_count=324, minima=list(map(str, minima)),
                     shifted_parameter_checks=parameter_checks,
                     raw_branch_checks=raw_checks, branches=branches,
                     high_bin_checks=high_bin_checks,
                     equality_fixture=dict(t=str(ts), r=str(ts), m='0',
                                           omega='0', row_exponent='7/40'),
                     status='PASS: exact scalar certificates; no endpoint claim'),
                 indent=2, sort_keys=True))
```

Executed output:

```json
{
  "bernstein_count": 324,
  "branches": {
    "inverse": 33681,
    "inverse_zero": 18483,
    "long": 83916,
    "plain": 10077,
    "plain_zero": 9959,
    "unmarked": 22012
  },
  "equality_fixture": {
    "m": "0",
    "omega": "0",
    "r": "599/400",
    "row_exponent": "7/40",
    "t": "599/400"
  },
  "high_bin_checks": 126,
  "minima": [
    "38353/60000",
    "16771/120000",
    "1729/120000",
    "8329/1200000",
    "17861/2400000",
    "1231/75000",
    "319/6000",
    "7067/15000",
    "69827/30000"
  ],
  "raw_branch_checks": 178128,
  "shifted_parameter_checks": 4536,
  "status": "PASS: exact scalar certificates; no endpoint claim"
}
```

## Verified Publication Receipt - 2026-11-07T12:29:31-05:00

The final 20261107-referee-2 research synthesis was published at commit
**37ff3ef38f5f1d5475446742a2fac88fe881c874**, report blob
**cbcd63975ceb5a6c8e90bb2200ded8d3901de7ed**.
Immutable commit readback matched the entire prepared report exactly,
including the executed verifier. GitHub commit metadata confirms only
this authorized report changed: 1,065 added lines, zero deleted lines.
All earlier report content and the early checkpoint were preserved.
A-O structure, source-hash references, code-fence structure and the
embedded verifier digest were checked before publication.

Verifier SHA256:
429806283c0a778f2e3411ce52d311fcbfc7a877182477229f183de3283f5231.
Results: 324 positive Bernstein coefficients, 4,536 shifted parameter
checks, 178,128 raw-branch checks and 126 high-bin checks passed;
all computation sessions ended successfully. Relevant exact-head CI
evidence is recorded in L; the new RC/MH consumers were NOT run in Lean.

EXECUTION=COMPLETED; REPORT=PUBLISHED_VERIFIED.
MH1-MH4 remain PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING /
NOT_FORMALIZED. RC1-RC4 verdicts remain scoped as recorded in D.
No new complete global exponent or RH proof is claimed.
This receipt records already verified publication, not a future promise.


## Scheduled Referee Checkpoint - 20261107-referee-3

Invocation: 2026-11-07T20:13:01-05:00 (America/New_York); RUN_ID_UNAVAILABLE.
Execution IN_PROGRESS / PARTIAL. No new mathematical verdict or endpoint gain is claimed by this checkpoint.

Live main: `cae99df1c3ea24ff4113063bf09f6fd07517ad93`; AGENTS blob `0a99faf8458809ac772d470d704c5433f373bda8`; proof-contract blob `d1d6fd558ee23927bd9f70ffdc375bafd1dbb67a`.
Acknowledgments: high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1; chain_ack=CANCELLATION_CHAIN_REUSE_V1; baseline_ack=PAID_BASELINE_EXACT_CONSUMER_V1; deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1.

Today is November 7 in America/New_York, despite the UTC date. All seven November 7 and November 6 role reports were retrieved from agent-reports snapshot `ac20a0055c43cc0b61fc6e239d351b784e0a31e0`; coordinator mirrors have equal blobs. TODAY=AVAILABLE; YESTERDAY=CARRY_FORWARD. External inbox blob `038018145c0fddb2f6306c0712373adf9cd1ea52` has no post-October-18 entry; current source-specific safeguards remain in force.

Selected route: OAI-NNS retained tuple/rescaling consumer. Selected original claims: `20261107-coordinator-1513/RG1-RG5`, especially RG4's proposed soft-gate source propagation; source report blob `785c56207f0745244d8c2503a18ed7b4d91b39e6`. Review method: reconstruct the scalar inequality and original source/normalization use-sites, test boundary and multiplicity cases, then determine the exact first unpaid consumer. The arithmetic object is the original compensated tilted probe, not arbitrary signs or canonical LOW. The incoming same-source baseline is the actual-minimum-slot strict theorem, not nominal 7/8.

Also received `20261107-analytic-3/BC1-BC5` and merged #1105's arbitrary-cutoff separate-error interface. Prior MH1-MH4 decisions are preserved; no repeated scalar grid is planned without a changed question. Open PR #1106 at `aafb28e85bbc7a55a6c351621dc451042aee5b8f` is separately discovered; its CI/source scope is not yet certified here. #1105 is merged, not still awaiting merge. Publication and mathematical/formal status remain distinct.

Plan: independent RG1-RG4 review; a substantive source-faithful obstruction or corrected consumer theorem; exact finite checks only where discriminating; final append preserving all prior history and immutable readback. Endpoint comparison, all LOW/HIGH/principal/remote/height/conductor costs, fixed-loss spending and canonical O(R) restoration must remain explicit. No source/branch/PR/workflow/other-report changes or local Lean execution are authorized.

---

## Scheduled Evening Synthesis - 20261107-referee-3

Invocation: 2026-11-07 20:13:01 EST / 2026-11-08 01:13:01 UTC. This completes this invocation's earlier checkpoint; it is not another scheduled execution. Report date is November 7 in America/New_York. Earlier referee claims, verdicts, counterexamples, and receipts are preserved verbatim.

### A. Most Important Mathematical Finding

**The proposed sharp soft-gate theorem RG4 is not needed for the contemplated same-source endpoint. Two applications of an already compiled row-energy theorem, followed by the already compiled moving tuple-mass bound, give a weaker sufficient replacement.** The fallback enlarges only a row-norm upper bound to the untilted value. It does not change the arithmetic sum, its actual physical normalization, or any source mask.

For actual total slot length L=1/6, selected length s, unselected length d=L-s, physical sum S=x+y, and g=5/3-2S, use the current row envelope when s>=g and the fixed Sbar=5/6 envelope otherwise. The additional ENERGY exponent is

```text
e(s) = 0       if s>=g,
       g/2     if s<g.
```

After the genuine square root and normalization its price is e(s)/2. At rho=1/2 the retained original tuple mass supplies -d/2, so

```text
e(s)/2-d/2 <= 0  for every 0<=s<=1/6 whenever 0<=g<=1/9.
```

The entire existing physical tilt range has g=24*tilt<1/40, well inside that condition. In the fallback branch the remaining exponent is strictly less than -31/480, even at the closure g=1/40. At s=L the old envelope applies and the actual empty outer mass remains exactly one.

The paper proof below propagates this estimate through the original central and remote Gaussian terms, all subsets, ray pools, and unchanged normalizer. It gives the gate-free complete LOW estimate for every actual fixed SourceData F:

```text
for every 0<=tilt<1/960, every character chi, and every loss>0,
  F.tiltedProbe tilt chi = O(Z^(3/16-9*tilt+loss)).       (TF2)
```

With the same fine source and true minimum m used by the certified comparator b_base=7/8-m/24, the existing calibrated HIGH reserve is m/4. Choosing tilt=m/4 therefore gives the paper-level complete boundary b_new=7/8-m/4, an improvement of 5m/24 over that SAME-source comparator. Spending half that improvement gives fixed Mertens power 7/8-7m/48. No explicit numerical value for the existential m is asserted.

**Status separation:** TF1-TF3 are new PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED. The existing suppliers are compiled inputs, not compilation of this new composition. RG1-RG3 receive independent paper-scope acceptance below. RG4's sharper source inequality remains UNRESOLVED. NEW_VERIFIED_ENDPOINT_GAIN=NONE; VERIFIED_ETA=NONE; eta_gate=SEARCH_BROAD. No claim that the canonical VF objective or RH has been proved.

### B. Authority, Objective, Baseline, And Continuity

Actual main at intake and prepublication refresh: **cae99df1c3ea24ff4113063bf09f6fd07517ad93**, tree **087a31436295ea4b0307d3d851f363c5370dba5f**. Main contains merged #1105. Governing files: [AGENTS.md](https://github.com/OVVO-Financial/RH_Lean/blob/cae99df1c3ea24ff4113063bf09f6fd07517ad93/AGENTS.md), blob 0a99faf8458809ac772d470d704c5433f373bda8; [CURRENT_PROOF_CONTRACT.md](https://github.com/OVVO-Financial/RH_Lean/blob/cae99df1c3ea24ff4113063bf09f6fd07517ad93/CURRENT_PROOF_CONTRACT.md), blob d1d6fd558ee23927bd9f70ffdc375bafd1dbb67a.

```text
high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1
chain_ack=CANCELLATION_CHAIN_REUSE_V1
baseline_ack=PAID_BASELINE_EXACT_CONSUMER_V1
deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1
selected_route=OAI-NNS, independent adversarial consumer audit
object=the original normalized compensated tilted probe and its complete Mertens/HIGH return
change=retain the existing moving tuple decay to pay a two-envelope fallback
```

The canonical target remains the actual-prime square statement

```text
exists C>=0, forall integers R>=2,
  |pi(R^2)-vfMidFinishedMass(R)-sqrt(2)| <= C R log R.
```

Its current common intermediate is complete canonical signed HIGH, with fixed Lambda>=0 and the original birth-block absolute-height test:

```text
M(R^2-1)=L_R+H_R,
|L_R| <= (floor Lambda+1)R.
```

Canonical LOW is paid. OAI inverse LOW is a different object; TF2 is eligible because its complete HIGH consumer is supplied in E4 below. The actual strongest applicable comparator on this chosen source path is `native_beta_le_true_physical_slot_minimum`, together with `native_mertens_true_physical_slot_minimum` and `native_signed_pair_true_physical_slot_minimum`: there exists a fixed fine HighData D, m=actualSlotMinimum(D)>0, beta_H<=7/8-m/24, with every-positive-loss Mertens growth and the full signed-pair bound retaining its squarefree diagonal. This is not rounded to 7/8 and is not identified with an optimized largest gap across all possible sources.

Continuity snapshot: agent-reports **ac20a0055c43cc0b61fc6e239d351b784e0a31e0**. All seven role reports were available for both November 6 and November 7. TODAY=AVAILABLE; YESTERDAY=CARRY_FORWARD. Coordinator 00/90 copies have identical corresponding tree blobs. Relevant contents read, not inferred from schedule times:

| Role | November 6 blob | November 7 intake blob | Current disposition |
| --- | --- | --- | --- |
| Coordinator / Proof Architect | 8812a90540fb511279b5f4ce08e108ef717d5ef1 | 785c56207f0745244d8c2503a18ed7b4d91b39e6 | CS coherence/inverse-cost scope carried; selected `20261107-coordinator-1513/RG1-RG5` for review |
| Owner Payment | 1856a96aaaa9d86a5ee2d59ffe50ced936443fa6 | 933e8eb23e669594cc687059d75147e6267eec8d | MS moving-clock obstruction carried; latest JT1-JT5 exact JOH kernel/tail/failure localization remain pending independent review; no new sign conclusion assumed |
| Analytic Type II | 7997620b6ab7eb0701296994734ee910df3c3ba1 | 77f3e5795533041e4356ceb94cb66328da7af27c | AQ scope carried; latest `20261107-analytic-3/BC1-BC5` retain two-error combined counts, but full endpoint not claimed; do not repeat prior GL/FT audits |
| Finite Wheel | 3099558194a00358962ff1844bf283e625b9283d | 7739fa5d4cc77f35773b0d4149b2ddd21732a70d | GF donor-capacity scope carried; latest OC1-OC5 distinguish quotient-95/96 physical cuts from label capacities, with X=9215 witness and unspent-bank repair; pending independent review |
| Prime Census | c34ac074296e8b2e5b20dee3a2ce02518571206c | 3fae830e34c590d32c31ad77cad3ace833eb3ff5 | FW N=690 Nyman cross-term warning and current RC1-RC4 scopes carried; no repeated unchanged census |
| Adversarial Referee | da3265467c799e9d21832ab25245617ba3b15a54 | 65384576327e1ae2c976fca368c83690fc8a95dd | Previous spectral inverse-cost decisions, today's CODIV `referee-1` and marked-half `referee-2/MH1-MH4` retained unchanged |
| Lean Verification | b8bfe3ce9c20d7903395364efb39bcec974c8a2f | 2998b7339ea4b3e3fd2fd1d26f839527fd5adc95 | Historical #1100 exact identities carried; #1105 source moment result now independently confirmed merged, not a new complete endpoint |

EXTERNAL_HANDOFFS.md blob **038018145c0fddb2f6306c0712373adf9cd1ea52** was read; no new entry after the recorded October 18 material. Old source-admission and no-placeholder restrictions remain in force. These acknowledgments do not constitute new independent acceptance of the Owner, Wheel, or Analytic paper claims.

### C. Highest-Risk Inferences Selected

1. Deleting the reflected gate at no energy cost is false on its stated scalar relaxation. RG2 remains decisive at exactly that scope.
2. Promoting RG1's scalar soft cost to every completed source layer is not automatic. RG4 remains an unproved sharper source assertion in this review.
3. Treating RG4 as a necessary prerequisite for the proposed endpoint is unnecessary. The existing physical theorem is uniform over arbitrary finite row sets subject to an upper norm cap, and the inverse polynomial on its left is independent of the choice of physical exponents. That is the independent mathematical opening used here.
4. Paying the fallback by changing the actual physical denominator, or using the same unselected factor twice, would be invalid. E2 keeps Q=q Z^S/L_u^2 and pays the full energy square-root price before using the separate Gram factor.
5. An improved LOW bound does not exceed the remaining HIGH reserve. The new paper endpoint stops at max(7/8-tilt,7/8-sigma); no iteration to 1/2 or improvement beyond sigma is asserted.

### D. Independent Review Of The Upstream Claims

Original claim source: [Coordinator RG1-RG5](https://github.com/OVVO-Financial/RH_Lean/blob/ac20a0055c43cc0b61fc6e239d351b784e0a31e0/research/agent_reports/2026-11-07/00-coordinator-am.md), blob **785c56207f0745244d8c2503a18ed7b4d91b39e6**. Stable run ID `20261107-coordinator-1513` is preserved.

**RG1, exact statement and verdict.** All variables are real. Define

```text
u=min(v,z,(v+z)/3),
T=2H+2A+2z-1-l0-theta-N-3B,
Eref=O/2+max(H,v+l)-S0-B+z-u-l-2e/3
     -max(0,T-v-3l-e)/2.
```

Assume S+L<=1, L<=1/3; d,h,O>=0; H<=S-2d-O+h; 2A<=O+3h; 0<=N<=A; S0,B>=0; l0<=L-d+h; z<=l0+h; v,l>=0; e>=-h; |theta|<=h; and v+3l+e<=T+2h. No unlisted nonnegativity of z,l0,S,L is imposed. The conclusion is

```text
Eref <= S-2d+(38/3)h + max(0,1+4L-2S-l0)/4.
```

**ACCEPT / PAPER_PROOF / independently reviewed here, NOT_FORMALIZED.** Reconstructed from the exact row and column branches in `reflected_exponent_finite_slot_gap`, not from its theorem statement with the gate removed. The hypotheses imply T<=H-3d+8h and v+l<=H+11h. If u=z, substitution and the nonnegative retained kernel give the old bound. Otherwise u>=v/2. The retained inequality T/4<=(v+3l+e)/4+max(0,T-v-3l-e)/2 gives the row bound

```text
Eref <= S-2d+(1+4L-2S-l0)/4+8h/3.
```

The column branch instead gives Eref<=S-2d-1/2+3L/2-3d/2+26h/3. The displayed conclusion follows in both cases. In the source proof the hard gate is used only after the displayed row partial bound. This is an elementary scalar extension; it proves no source energy theorem by itself.

**RG2, exact family and verdict.** For any 0<g<=1/6 set L=1/6, S=5/6-g/2, l0=z=g/5, d=1/6-g/5, H=1/2-g/10; set O=A=N=S0=B=v=l=e=theta=h=0. All RG1 hypotheses hold, T=0, u=0, and

```text
Eref-(S-2d)=g/5=(1+4L-2S-l0)/4>0.
```

**ACCEPT / PAPER_PROOF / exact infinite scalar family.** The no-cost gate deletion is refuted and coefficient 1/4 is sharp on this scalar domain. Four rational members were independently executed below. No realization by actual prime ideals or HighData is claimed; this does not refute either RG4 or TF2.

**RG3, exact statement and verdict.** For L>=0, 0<=g<=L, 0<rho<1, and 0<=s<=L,

```text
Phi(s)=(g-s)_+/8-(1-rho)(L-s),
max Phi = max(0,g/8-(1-rho)L).
```

**ACCEPT / PAPER_PROOF / independently reviewed.** Phi is affine on [0,g] and [g,L]; its breakpoint value is nonpositive, and its two endpoint values give the maximum. The sufficient uniform rho<=7/8 condition and the specific rho=1/2 application are valid. The compiled arithmetic supplier is genuinely the original weighted tuple mass, not an arbitrary-vector model. The assertion that this pays RG4 remains conditional on RG4's physical input; TF1 below supplies a different, weaker price which also gets paid.

**RG4. UNRESOLVED at its full stated source scope, NOT_FORMALIZED.** Exact requested modification: retain all of `low_original_completed_energy_tilted`, with fixed Sphys in [1/2,5/6], original ideal/source data, and degree,C,Z0 chosen before the moving rows, cutoffs, selected type, d,l0,shift; remove its `IsEmpty selected_type OR 5/3-2Sphys<=l0` hypothesis; multiply the RHS by Z^((5/3-2Sphys-l0)_+/4). The scalar acceptance does not certify all its many-layer lifts. This review supplies neither a counterexample nor independent completion of that sharper assertion. It is unnecessary for the endpoint now proposed.

**RG5. ACCEPT as a conditional same-source comparison, not an unconditional published theorem.** Its full calibration, tilt=m/4, native moment supplier, generic anchored HIGH and loss-spending arithmetic are correct at the stated source scope. Replacing the dependency on RG4 by TF1-TF2 gives the new paper derivation TF3 below. The original conditional claim is not refuted; only an unnecessarily strong prerequisite is bypassed.

### E. Original Research: Two-Envelope Return

#### E1. TF1: uniform two-envelope selected energy

**New claim `20261107-referee-3/TF1`.** Fix an admissible `LowPhysicalExponents` pair phys=(x,y), S=x+y, and set g=5/3-2S>=0. Fix eta, an original finite prime-exclusion set Pset with every member maximal and fixedBadPrimes included, K, nonnegative slot lengths ell_i with sum<=1/6, Ck>0, b real, and 0<epsilon<=1. Put

```text
s_J=sum_(i notin J) ell_i,
d_J=sum_(i in J) ell_i,
e_J=0 if s_J>=g, otherwise 5/6-S=g/2.
```

Then there exist degree in Nat, C>0 and Z0>1, depending only on these fixed data, such that for all real Z>=Z0, all finite prime-ideal pools T_i satisfying support, exclusion from Pset, pairwise disjointness and Norm(P)<=b Z^ell_i, all J, and all finite R of nonzero original Eisenstein elements with

```text
elementNorm(z) <= Ck Z^(S-2d_J),
```

the following holds uniformly for every X>0 with Z^(1+s_J-epsilon/2)<=X<=Z^(1+s_J+epsilon/2), every slot window W_i of modulus at most one, every real scale vector Y, every real t and every original ray residue sigma:

```text
sum_(z in R) |lowSelectedInverseRow univ
  (lowSelectedWeight eta (canonicalSlotSupport T) J W Y t)
  eta Pset hmax (lowSelectedIdeal (canonicalSlotSupport T) J)
  X t sigma z|^2
 <= C (1+|t|)^degree Z^(S-2d_J+507epsilon+e_J).       (TF1)
```

All functions in this statement are the existing source definitions, with no change of weights, inverses, ideal generators, masks, ray residues, or Gaussian fixed window. It is exactly the nominal-energy carrier, with an explicit additional exponent instead of the per-slot gap assumption.

**Proof.** Apply `low_selected_physical_energy_tilted` once at phys and once at the fixed admissible pair barPhys=(17/48,23/48), whose sum is 5/6. This fixes two degrees, constants and thresholds before Z, T_i, J, R, X, W, Y, t or sigma. Take their maximum degree and threshold, and the sum of their positive constants. Since 1+|t|>=1, both bounds fit the resulting degree.

Use the original `eventually_low_selected_caps` and central-shift construction with l0=s_J+epsilon/2. The selected product cap, d bounds and |shift|<=epsilon are exactly those in the nominal proof; they do not use the per-slot gap. If s_J>=g, l0>=g gives the current physical theorem's gate. If s_J<g, the barPhys gate is 0<=l0 and the original R satisfies the enlarged row cap because Z>1 and S<=5/6. The RHS becomes Z^(5/6-2d_J+507epsilon), which is the stated actual exponent plus e_J.

Crucially, the LEFT side of `low_selected_physical_energy_tilted` has no phys.x or phys.y. Their sum occurs only in the row upper bound and energy RHS. Both applications therefore bound the same sum at the same X. We do not replace R by new rows or alter the actual physical probe. This proof uses two fixed parameter choices, not constants chosen separately for each changing subset or scale. The empty selected-type case is already admitted by the original theorem; treating it by the fallback is safe overpayment.

#### E2. TF2, first step: pay the actual normalized central tuple

From now on retain the actual conserved slot total **sum ell_i=L=1/6**, not merely an upper bound. Fix a>0 and the original lower norm bounds a Z^ell_i<=Norm(P), as in `low_central_compensated_tuple_tilted`. Keep all that theorem's W0,W1 support, smoothness, positivity-of-cutoff and boundedness hypotheses. Fix 0<rho<1 before the source scale. For the actual unselected tuple u put L_u=elementNorm(product u_i) and q=elementNorm(calibration generator)>0. The exact physical scale is still

```text
Q=q Z^S/L_u^2.
```

The original fixed-source product bounds give c Z^d_J<=L_u<=B0 Z^d_J, with positive constants c,B0 independent of u,J,Z. TF1 bounds the actual numerator rows exactly as before. Taking its square root and dividing by sqrt(Q) contributes at most

```text
C (1+|t|)^degree Z^(507epsilon/2+e_J/2).
```

The exponent calculation is (S-2d_J+e_J)/2-S/2+d_J=e_J/2. **It is not zero in the fallback branch.** This is why substituting the artificial barPhys denominator would be erroneous.

The existing complete actual compensation Gram estimate, still evaluated at the ORIGINAL x,y, contributes sqrt(3q/L_u) times Z^((5x+y)/12+(y/2)epsilon). Thus the exact remaining mass is the already compiled

```text
sum_u |lowUnselectedWeight(u)| L_u^(-1/2)
 <= (C_rho a^(rho-1))^|J| Z^(-(1-rho)d_J)
```

for the normalized windows. This is `lowUnselectedMass_moving_power_bound` with B=1. Since K is fixed, replace its prefactor by max(1,C_rho a^(rho-1))^K. This makes it uniform in J without a Z-dependent constant. No extra uniformity as rho tends to an endpoint is used.

The extra exponent to pay is

```text
Psi(s)=e(s)/2-(1-rho)(L-s)
      =-(1-rho)(L-s)                    if s>=g,
       g/4-(1-rho)(L-s)                 if s<g.
```

For L>0 and 0<=g<=L its supremum over the continuous scalar interval is

```text
sup Psi = max(0,g/4-(1-rho)(L-g)).
```

Proof: the good branch is nonpositive, attaining zero at s=L. The bad branch increases with s and has the displayed left limit at g; the function jumps down at g. This is a supremum, not necessarily an attained maximum. For g=0 the bad branch is empty and the formula still gives zero. Therefore all such scalar costs are nonpositive precisely when

```text
g <= 4(1-rho)L/(5-4rho).
```

Use rho=1/2. This requires g<=2L/3=1/9. The actual tilted pair has g=24*tilt<1/40. In its bad branch,

```text
Psi(s)=g/4-(L-s)/2 < 3g/4-L/2 < -31/480.
```

With g=1/40 at the closure the final strict inequality becomes <= on the middle comparison, but the first strict inequality still gives Psi<-31/480. In the good branch Psi<=0; at J empty, s=L and mass is exactly one. Hence the complete central tuple has the SAME former exponent (5x+y)/12+254epsilon, uniformly over every subset J, without the per-slot gate. The y<=1 condition pays 507epsilon/2+(y/2)epsilon<=254epsilon as in the source.

This use of an absolute mass bound occurs after the original full compensated Gram estimate. It is not a new arbitrary-vector cancellation theorem. The -2d_J row credit was already canceled by Q and the upper bound on L_u; only the remaining separate factor L_u^(-1/2) is spent in the moving mass.

#### E3. TF2, complete original LOW statement and proof

**New claim `20261107-referee-3/TF2`.** For every fixed real Delta, every existing HighData D:HighData(Delta), every F:SourceData(D), every fixed 0<=tilt<1/960, every character chi and every loss>0, there are C>0 and Z0 such that for every real Z>=Z0 the existing source normalizer is nonzero and

```text
|F.tiltedProbe tilt chi Z| <= C Z^(3/16-9*tilt+loss).
```

The claim does not remove ANY HighData or SourceData field. Only the additional hypothesis `24*tilt <= (7/8)*D.rmin` of the current wrapper is unnecessary for this new proof. D, its finite number of slots, actual positive distinct slot lengths, exclusions, conductor, cutoff and windows are fixed before Z. Constants may depend on these data, tilt, chi and loss. No claim of uniform constants for moving source complexity is made.

**Complete propagation.** The preceding central-tuple proof replaces the sole gated inverse-energy supplier. The rest of the original return is used as follows, with the same functions on every left side:

| Original layer in VF919TiltedLowPhysical | New use and paid terms |
| --- | --- |
| `low_selected_nominal_energy_tilted` | Replace only its bound by TF1, with the two fixed row envelopes |
| `low_physical_inverse_normalized_tilted` | Use actual Q and carry e_J/2, as proved in E2 |
| `low_central_compensated_tuple_tilted` | Keep actual compensated Gram and replace the final constant mass bound by the compiled moving-power bound; Psi<=0 restores the old 254epsilon exponent |
| central Gaussian dyad and central dyad sum | The tuple estimate has the same time-polynomial and uniform moving-source quantifiers; the same Gaussian integrability and dyad count give 256epsilon |
| remote Gaussian dyads | Existing O(Z^-1) estimate has no slot-gap hypothesis; all remote tuples remain present and are dominated by the paid central envelope |
| all Gaussian dyads and all subsets | Same exact expansion and norm inequality, with fixed finite K; no selected or complementary subset discarded |
| original ray pools | Positive distinct fixed ell_i give eventual disjointness; same supported primary generators, masks and prime exclusions |
| general bounded windows | Normalize by D0=max(1,B), then restore D0^K exactly, as in the existing source proof |
| original normalizer | Use `actual_ray_normalizer_inverse` at loss/2, with the unchanged positive windows, exact sum 1/6 and genuine ray pools; numerator gets loss/2 |

For the numerator's arbitrary positive loss, the existing choice epsilon=min(loss/512,1/2) supplies 256epsilon<=loss; use this with half the desired final loss. The source normalizer is exactly

```text
sourceResidueConstant(W0,W1,product Pset)
 * principalScalar(univ,Z,1/6,slotMass(T,residueWeights(W,Yp))).
```

It is not a new parameter or a random model. Multiplying its inverse O(Z^(loss/2)) by the new numerator estimate gives the asserted normalized bound. Finally (5x+y)/12=3/16-9*tilt for x=17/48-24*tilt, y=23/48+12*tilt. All physical inequalities are those already checked by `tiltedPhysicalExponents`; no alteration of the source geometry is needed.

The no-gap normalized theorem can equivalently be stated with every hypothesis of `original_normalized_compensatedPhysicalProbe_low_tilted`, dropping its `hgap` and adding g<=1/9. Its positive injective slots already sum exactly to 1/6. This is a useful stronger general formulation on that existing carrier; TF2 above uses the simpler, already admissible tilt range.

#### E4. TF3: same-source complete endpoint and canonical return

**New claim `20261107-referee-3/TF3`, PAPER_PROOF dependent on TF1-TF2, not compiled.** Choose the same fine D as in `native_beta_le_true_physical_slot_minimum`, let m=actualSlotMinimum(D)>0 and

```text
E=slotCalibratedHighDataLowFirst(sourceWithExactSlotMinimum D).
```

Its existing constructor preserves t, actual ell_i and N, caps the small errors, and gives E.sigma=m/4. The original slots imply m<=E.t/200. The actual original HighData definition supplies E.t<=1/100000000. Thus with tilt=m/4,

```text
0<tilt<=1/80000000000<1/960,
24tilt=6m<=3E.t/100<E.t.
```

These parameters and F:SourceData(E), counts:CountParameters(F.modulus,top,E.t) are fixed before selecting characters or zeros. The same native uniform fixed-source moments and `chosen_data_height` supplier in `native_fixed_slot_anchored_probe_bounds_low_first` use the ALREADY PAID beta_H<=7/8 and the original fine-slot hypotheses. They do not assume the desired improved boundary. If beta_H<51/100 the proposed boundary is already trivial; otherwise the original lower-beta licensing is available.

The actual generated `fixed_tilted_high_bound_anchored` was read from the successful exact-head #1091 CI artifact, not inferred from its name or generator. Its tilt hypotheses are only tilt>=0 and 24tilt<E.t. Retain E.epsilon,E.e<=E.t/2000, (E.N+8)E.eps<=E.t, the same SourceData and counts, and the supplied height conditions 0<height<1/400, 4height<E.cost/200, height<E.t, 2height<=E.t, height(2+4E.eps)<E.t. This theorem gives the original signal comparison at exponent 7/8-11/16-8tilt-E.sigma.

Combining it with TF2 gives

```text
LOW exponent                 3/16-9tilt+loss
original signal shift        -11/16-8tilt
complete HIGH error          7/8-11/16-8tilt-E.sigma
zero boundary                max(7/8-tilt,7/8-E.sigma)
                             = 7/8-m/4.
```

For completeness, suppose beta_H>b=7/8-m/4. Choose loss=(beta_H-b)/2>0. It is less than 7/8-b because beta_H<=7/8. The same primitive-zero-near-supremum theorem supplies a zero with real part greater than beta_H-loss=b+loss. The finite-prime deletion preserves that zero by the existing nonpole product identity. The HIGH comparison boundary b and LOW boundary b+loss are both strictly below it. All original sourceCorrection analyticity and bounds at 21/25 hold; b>21/25 follows already from the displayed tiny upper bound on tilt. Apply the same `nonzero_of_probe_bounds_variable_boundary` theorem to contradict that zero. Thus beta_H<=b. This reproduces the complete variable-boundary argument, with only the LOW supplier changed.

Use the existing analytic Hecke-to-zeta/Mertens transfer, not an equality between Hecke coefficients and rational Mobius coefficients. It gives, for this fixed D,

```text
for every epsilon>0, exists C_epsilon>=0, forall integers x>=1,
  |M(x)| <= C_epsilon x^(7/8-m/4+epsilon).
```

The original full square identity consequently gives the same-source signed-pair bound

```text
2*realMertensPositiveLagPairSum(x+1)
 <= (C_epsilon x^(7/8-m/4+epsilon))^2-realMertensDiagonal(x+1).
```

The squarefree diagonal has NOT been deleted. Against b_base=7/8-m/24, define eta_gain=5m/24>0. For each fixed Lambda>=0, the exact canonical partition and paid LOW give, for every epsilon>0,

```text
|H_R| <= C_(Lambda,D,epsilon) R^(2*b_base-2*eta_gain+epsilon)
       = C_(Lambda,D,epsilon) R^(7/4-m/2+epsilon), R>=2.
```

Here use Mertens loss epsilon/2 and absorb O(R), since b>1/2. For all integers N>=1 and 1<=h<=N, the corresponding COMPLETE prefix energy is

```text
sum_(0<=j<h) |canonicalHighPrefix_Lambda(N+j)|^2
 <= C_(Lambda,D,epsilon) h N^(7/2-m+epsilon).
```

This uses the pointwise bound at R=N+j+1<=2N, with a smaller initial loss before squaring. It includes h=1 and all coherent-mean and centered contributions. It is not a shell-increment estimate.

Spending loss=eta_gain/2=5m/48 in the all-integer Mertens bound yields the fixed power **7/8-7m/48**, strictly below b_base. Alternatively, recover arbitrary integer x from square endpoints by adding at most 2R+1 original Mobius terms in the final partial square block; because the fixed exponent exceeds 1/2, this O(R) cost is absorbed. These statements are paper consequences of TF2, not existing Lean declarations.

### F. Exact Obstruction Scope And Negative Controls

**New claim `20261107-referee-3/TF4`: sharp limitation of THIS coarse payment rule.** For fixed L>0 and rho in (0,1), the two-envelope budget is nonpositive for all scalar s in [0,L] precisely when g<=4(1-rho)L/(5-4rho), on the domain 0<=g<=L. If g exceeds the threshold, choose s=g-delta with

```text
0<delta<min(g, [g/4-(1-rho)(L-g)]/(1-rho)).
```

Then Psi(s)>0. Taking a sequence of such delta tending to zero gives an infinite family of exact scalar violations of the proposed all-subset budget extension. For 0<g<L, two positive slots of lengths s and L-s realize these complementary lengths as an abstract slot list. No claim that these lists satisfy the extremely fine HighData bounds is made. This limits this payment certificate, not all arithmetic estimates or the sharper RG4 method.

At rho=1/2, L=1/6, g=1/8, choose s=29/240 and d=11/240. Then s<g and Psi=1/120>0. This is outside the actual g<1/40 range; it is a negative control, not a counterexample to TF2.

Exact conserved total matters even within the allowed physical g range. A single positive slot of length 1/100, J empty, g=1/50 and d=0 gives the fallback cost g/4=1/200 with no outer decay. This deliberately violates sum ell_i=1/6. It refutes extending THIS payment argument using only the older total-length upper bound. It does not establish that the actual normalized arithmetic bound is false on a different carrier.

RG2 supplies the independent infinite counterexample family for no-cost scalar gate deletion. The fallback pays a larger energy loss than RG1 predicts and so never contradicts RG2. No original arithmetic theorem is declared false by these scalar diagnostics.

### G. Original Carrier And Signed Interaction Audit

TF1 changes only the allowed exponent in a bound on the same original rows. It does not replace actual rows by saturated rows, drop nonunits, change prime admissions, alter historical identifiers, randomize signs, move the mask, change the selected ideal, remove the Gaussian completion, or replace the physical cutoff X. The same fixed bad primes, period, ray residues and character enter both applications.

TF2 retains the exact Q at the actual tilt. The primary-generator norm identity used by the compiled mass theorem is the source identity: its remaining integrand is a product of inverse-square ideal norms times original window magnitudes. This is not an independent heuristic about the density of primes. Every subset and every original outer tuple is summed once. Finite constants may be enormous because the actual source has many slots; their size does not create a scale-dependent exponent.

Selected polynomial cross terms remain inside the original squared row norm. The complete compensated Gram theorem is used before the final mass estimate. There is no inference from individually favorable signed pairs to a global quadratic sign. The remote, powerful-part and punctured-list restorations are inherited from the unchanged full selected energy theorem, not reconstructed from unsigned support alone. The final Mertens square retains both diagonal and all lag-pair terms. Canonical HIGH retains both height orientations and the birth-block partition; this proof does not substitute a moving survivor population.

### H. Quantifiers, Circularity, And Genuine Reduction

Sbar is the fixed number 5/6. Only two energy constants are chosen; their maximum threshold and summed constant work for every moving pool, row family, subset and scale. The parameter J is never selected after taking a nonuniform limit. The selected-scale interval for X and its epsilon/2 collars are unchanged. The moment-height parameter is kept distinct from physical tilt and from real time t in the inverse polynomial.

The full source and K are fixed before the scale, character-specific constants and positive losses. No assertion is uniform in K growing with Z, in the actual minimum m tending to zero, or in rho approaching one. The fixed choice rho=1/2 is licensed by the compiled theorem. A finite subset enumeration does not substitute for the analytic proof for all K.

Forward implications: TF1 plus the compiled moving mass and existing physical/normalizer lemmas gives TF2; TF2 plus the already certified moments and generic anchored HIGH gives TF3. TF3 supplies a subcritical Mertens/HIGH improvement but not the canonical von Koch objective. Reverse implications from that canonical target to TF1, TF2 or the Hecke-family statement have not been established; no target equivalence is claimed. The new sufficient premise is not a renamed endpoint: TF1 is directly deduced from two already compiled bounds, and the payment is an elementary inequality on conserved source lengths. There is no unproved norm boundedness or new cancellation hypothesis inserted into the paper chain.

The paid beta<=7/8 is used as an INPUT in native moment licensing and the generated anchored HIGH. The desired beta<=7/8-m/4 is used only as the OUTPUT of the near-zero contradiction. The source is not chosen in response to an offending zero. Old gate-maximality theorems remain correct for THEIR sufficient gate; they are not universal no-go theorems for the new weighted return.

### I. Strongest Surviving Repair

Retain the coordinator's accepted scalar soft estimate and sharpness witness, but replace the first implementation dependency by TF1's coarse, already-supported energy price. The lower precision is harmless because actual tilted g<1/40 leaves a large fixed margin in the only branch requiring payment. This saves a new sharp-source proof through the entire reflected hierarchy.

TF2 is useful at exactly the original complete normalized source, not only a model or a selected component. TF3 remains a paper-level candidate awaiting independent review and kernel implementation. RG4 can still be worthwhile if a future consumer needs its finer loss or a wider range; this run does not reject it.

### J. Competing Strategy Assessment

The immediate OAI bottleneck after this proposed LOW repair is the existing complete HIGH reserve sigma=m/4, not a new universal inverse-energy cancellation theorem. Analytic BC1-BC4 and the marked-half/generalized-kappa consumers may still improve that reserve or other binding terms, but their local count gains must be returned completely. Their paper scope is not automatically upgraded by TF3.

Keep all nine protected routes active. Owner's JOH exact-kernel and low-zero localization is independent of this Hecke source path; its remaining signed zero sum is not paid here. Wheel's occurrence cuts and repair remain about actual donor capacity and absolute residuals, not global signed Mertens lower bounds. Nyman common-window cross terms, CODIV source admission, VF-LOW/SAT chronology, FINITE-AC/CORR4 conductor one and all cross terms, and MU-LIFT unused-bank constraints retain their current scopes. No route is retired and no objective amendment is requested.

### K. Executed Exact Diagnostics

**New claim `20261107-referee-3/TF5`: FINITE_COMPUTATION / PASS, scalar scope only.** Before executing, the scratch script fixed rho=1/2, g=i/7680 for 0<=i<=192, and s=j/1440 for 0<=j<=240. It also specified all subsets of lengths proportional to 1,...,K for K=1,...,8 and two held-out distinct positive lists proportional to [1,1009,1013,1019,1021] and [1,10^9,10^9+7], each rescaled to total 1/6. It used Python Fraction throughout, with no floating-point sign tests.

```text
46,513 grid cases: PASS; largest extra exponent 0.
550 subset cases at g in {0,1/10000,1/100,1/40}: PASS.
2,200 exact normalization exponent identities: PASS.
4 RG2 witnesses at g in {1/10^9,1/1000,1/40,1/6}: PASS.
3 endpoint algebra tests: PASS (scalar checks, not HighData witnesses).
Expected negative controls: +1/120 and +1/200, both reproduced.
```

Reproducer core, sufficient to repeat the decisive checks without any repository installation:

```python
from fractions import Fraction as F
from itertools import combinations
L = F(1, 6)
def budget(g, s, total=L):
    return (F(0) if s >= g else g/4) - (total-s)/2
for i in range(193):
    g = F(i, 7680)
    for j in range(241):
        s = F(j, 1440)
        assert budget(g, s) <= 0
        if s < g:
            assert budget(g, s) < F(-31, 480)
families = [list(range(1, k+1)) for k in range(1, 9)]
families += [[1,1009,1013,1019,1021], [1,10**9,10**9+7]]
for weights in families:
    ell = [L*w/sum(weights) for w in weights]
    for k in range(len(ell)+1):
        for chosen in combinations(range(len(ell)), k):
            s = sum((ell[i] for i in chosen), F(0))
            d = L-s
            for g in [F(0), F(1,10000), F(1,100), F(1,40)]:
                e = F(0) if s >= g else g/2
                S = F(5,6)-g/2
                assert (S-2*d+e)/2-S/2+d == e/2
                assert budget(g, s) <= 0
assert budget(F(1,8), F(29,240)) == F(1,120)
assert budget(F(1,50), F(1,100), F(1,100)) == F(1,200)
for g in [F(1,10**9), F(1,1000), F(1,40), F(1,6)]:
    S, d, H, z = F(5,6)-g/2, L-g/5, F(1,2)-g/10, g/5
    assert 2*H+2*z-1-z == 0
    assert H == S-2*d
    assert H+z-(S-2*d) == (1+4*L-2*S-z)/4 == g/5
```

Executed full script SHA256: **d51ebcf57faee609211da8ad739060e5b66380a71c7318c9903c363270ee8d99**. Canonical JSON result SHA256: **a91fe24b792348b850f63e9c33470b7f0f19cae8e9ec995a5753995d1880c280**. This is independent execution of the new scalar checks, NOT independent reproduction of another agent's source-prime census. No Lean process was run. The analytic proof, not these finite tests, supplies all scales and all actual source lengths.

### L. Formalization Guidance: At Most Two Tasks

1. **Two-envelope actual nominal energy and weighted central tuple.** Implement TF1 by applying the existing physical theorem at phys and barPhys, keeping the same LHS and all uniform quantifiers. Carry e_J/2 through the ACTUAL Q normalization, then use `lowUnselectedMass_moving_power_bound` at rho=1/2 under exact total 1/6 and g<=1/9. Acceptance tests: every subset including J empty and selected type empty, lower and upper norm caps, epsilon collars, actual masks, unchanged Gram, no new axioms or sorry, printed types and axiom closures. Do not implement the false no-cost scalar gate deletion.
2. **Complete LOW and same-source anchored endpoint.** Propagate the restored central exponent through all existing Gaussian/ray/normalizer stages; add the gate-free SourceData wrapper for 0<=tilt<1/960. Instantiate the existing generic anchored HIGH at m/4 and reproduce the same-source beta, Mertens, signed-pair and canonical-HIGH returns with explicit loss spending. Acceptance requires exact generated source, pinned dependencies, full type inspection, and all endpoint axiom/no-placeholder audit evidence. Preserve old APIs and theorem scopes. Do not report VERIFIED_ETA before independent review and the complete verified implementation.

No implementation or feature branch was created by this Referee. These are bounded handoffs, not authorization to modify another agent's work.

### M. Specialist Handoffs

| Specialist | Precise next question |
| --- | --- |
| Proof Architect | Independently check TF1-TF3 and compare this two-envelope proof with the cost of RG4. The paper candidate uses the same actual m and stops at sigma=m/4; update the dependency map only after review. |
| Analytic Type II | Try to break E2 at the actual Gram/mass interface, especially the distinct uses of L_u in Q and L_u^(-1/2). Keep BC count improvements separate from this already identified reserve. |
| Owner Payment | TF3 is not yet a certified new numerical input. Continue JOH/VF-LOW/SAT using the current certified baseline; a future accepted TF3 can be substituted only through your proved native transfer. |
| Finite Wheel | No changes to OC2's absolute-residual or OC4's capacity scope. The scalar two-slot negative controls here are not physical donor graphs or counterexamples to your signed repair. |
| Prime Census | Independently inspect the source interfaces before expanding finite tests. Decisive falsifier: a phys-dependent term on the selected energy LHS, an omitted source restoration, a reused normalization credit, or a remaining gap use downstream of the central tuple. Synthetic small-K lists are explicitly not HighData. |
| Lean Verification | The two tasks in L are the complete proposed implementation surface. Confirm the generated generic HIGH type rather than specializing the old LOW-gated endpoint theorem by fiat. |

### N. First Independently Missing Ingredient

For this candidate, the first theorem not yet independently accepted is **TF2's full source-faithful gate-free normalized LOW**, with TF1 and the exact moving-mass payment as its explicit paper proof. No new arithmetic assumption is asserted to be required beyond the displayed compiled suppliers, but this author's reconstruction is SELF_AUDIT until another reviewer verifies it. Kernel formalization of that proof and the TF3 endpoint is also pending.

The sharper RG4 remains unresolved, but it is no longer necessary for this proposed endpoint. Beyond TF3's candidate boundary, the existing HIGH reserve is the binding comparison term. For the canonical VF/von Koch objective itself, this small subcritical improvement is insufficient; that objective remains OPEN.

### O. Source, CI, Publication, And Resume Capsule

Material main blobs independently read:

| Path | Blob SHA |
| --- | --- |
| docs/RHLEAN_COMPLETE_SIGNED_HIGH_ATTACK_20261107.md | be8168b67584d9d8ebbaa732a30c51509137543e |
| docs/RHLEAN_REUSE_CANCELLATION_CHAIN_20261107.md | 28e2ab47c68bc83b91ae02b6112b94867b021b32 |
| docs/RHLEAN_PAID_BASELINE_EXACT_CONSUMER_20261106.md | 13d58dd12d90fbf1160812c7c93442dc5d0576ac |
| docs/RHLEAN_INDEPENDENT_MULTIFRONT_NO_PIGEONHOLING_20261104.md | 6ff6eb30b91705af5478d3705849234260f8a7a3 |
| research/oai_434/VF919FiniteSlotReflectedGain.lean | a5545b5a00958b69f6fbfd79fc555a0476aa6487 |
| research/oai_434/VF919TiltedLowReflection.lean | 88293c915d67eefee2e1e989082248b8a52f2ae7 |
| research/oai_434/VF919TiltedLowPhysical.lean | c608fe06005359225661cc58d9caa0e4036de265 |
| research/oai_434/VF919TiltedProbe.lean | 0f95d412bce773d50e71b1809ab9942653e66812 |
| research/oai_434/VF919OriginalLowTupleSignedGram.lean | dd2fde01ae6e2446da4e69b30f6fc80fcadb858d |
| research/oai_434/VF919ActualSlotMinRetighten.lean | 138c4726085995b966204406805f70082402bec4 |
| research/oai_434/VF919LowFirstSlotCalibratedData.lean | 950c00c60d8757c7b6cd0dcea19e94d5114ea0ba |
| research/oai_434/VF919LowFirstSlotAnchoredEndpoint.lean | d9373ce13b703b1e5f4e4bcde158ef9004d250dd |
| research/oai_434/VF919NativeStrictMertens.lean | b33a4883e1ddb0551b0f11f062bce46680d87450 |
| research/oai_434/VF919NativeSevenEighthsReplay.lean | 111c933a7ca15647105ce6a4d0f3cbfc3cde81f4 |
| research/oai_434/VF919LowFirstPhysicalTiltFullBudget.lean | 0923ee1d78bdea48d494d9993834e1d31638bbda |
| research/oai_434/VF919TiltedHighAssembly.lean | 883141e0af896d4132bfc4ffa076e2d265ece5c9 |
| research/oai_434/RETAINED_SLOT_FEEDBACK.md | 298db21b32024ab1443257ddf41261e765f95cec |
| scripts/lean/retained_slot_feedback/CutoffMoments.lean | d877240267337cca4dae6a2929b216fe6f3e2898 |
| scripts/lean/slot_anchored/prepare_anchored.py | 0bac9047afaa8e9ddc5ac246be2d0fe7d6efa725 |
| RHLean/Analysis/CanonicalHighSectorCore.lean | dd02fc8fabfe4004c6b0d50374b3b8752607b168 |
| RHLean/Analysis/CanonicalLowOccupancy.lean | b958da340d107cdd00015d2827b9a728357b4d8e |

Original OAI pin: **1581d4cbdd69a0faf34b2089614fe2a814316a6a**, repository openai/math. Read exact `lean/OAI/NumberTheory/DirichletL/Inversion/TerminalWidths.lean`, blob **7e8d1403fb941545385aa5156e774ef9c29280a9**; `Detector/FinalAssemblyData.lean`, blob **ebc462f5678b6c9dafd55ee8a434d1538d814790**; `ParametersFixedSource.lean`, blob **d7dc90c32ac1ceafb542191ac782e9ed4e13e9a9**; `ParametersHighData.lean`, blob **c565dc0a72c7da9a2706cdd835e69a39e8c0dc14**. In particular t_small is literally t<=1/100000000, not an inferred asymptotic smallness condition.

Verified CI evidence, scoped to actual runs:

- [PR #1091](https://github.com/OVVO-Financial/RH_Lean/pull/1091) is merged, exact head **6778fd4c25b0f369d311e6e71223e168e329b4bf**. Its [anchored proof job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41898325686/job/126813711885) is successful; logs print the three actual-minimum endpoint types and PASS closures with only propext, Classical.choice and Quot.sound, closure counts 35334/35713/35728. This is compiled baseline evidence, not the new TF3.
- Artifact **13357024564** from that run was actually downloaded and inspected. ZIP SHA256 recomputed locally: **245aeede7f0c32c835b003325438696c10cd3e795b4d447120cf8b2f75f755e9**. Generated `VF919AnchoredHighAssembly.lean` SHA256 **74605135652abfcf926bbe7d3ae9e0215292fa793cd638dead61fb6357657524**, Git blob **c48b40e5c6b4c1f7f1cf0d94195f187b091affbe**. Its actual generic theorem at line 173 accepts arbitrary tilt with 24tilt<D.t, and its log reports only the three standard axioms. Generation metadata records source pin **9cbfce5295343bcb411e6d2cb159b59995cd985b** and the above OAI pin.
- Artifact copies of ActualSlotMinRetighten, OriginalLowTupleSignedGram, LowFirstSlotAnchoredEndpoint and LowFirstSlotCalibratedData have exactly the current main Git blob hashes listed above. Separate immutable fetches of TiltedLowPhysical and TiltedLowReflection at #1091's head also match current main blobs. Thus the material reused declarations are not an unverified changed-source extrapolation from old CI.
- [PR #1085](https://github.com/OVVO-Financial/RH_Lean/pull/1085) is merged, head **7895272e5303ed0f4199d5b06b74786e22d31769**. Its [proof job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41872040501/job/126721440818) succeeded. The actual moving-power mass type and standard axiom output were read. It is also present in the verified #1091 artifact.
- [PR #1105](https://github.com/OVVO-Financial/RH_Lean/pull/1105) is merged into current main, head **30e235ac5ee86041d194d07b20c52b0b22d317f2**. Its [cutoff proof job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42402231812/job/128492295936) succeeded. The printed two-error source moment and three immediate count statements have standard axioms; no new combined-count endpoint follows merely from this merge.
- At the final PR refresh, the only open PR is [#1106](https://github.com/OVVO-Financial/RH_Lean/pull/1106), ready rather than draft, head **aafb28e85bbc7a55a6c351621dc451042aee5b8f**. Nineteen of twenty check runs are successful and one is in progress; its dedicated logarithmic-amplification proof succeeded. It is NOT merged and its exact-identity content is not used as a new estimate here. No CI was triggered or awaited for this report.

Tool limitations and permissions: shell GitHub clone was denied by the network proxy; authenticated read-only GitHub retrieval and own-report writes worked. No local Lean build was attempted, no source file was modified, no proof branch/PR/workflow/schedule/other role report was changed, and no subagent was launched. Local mirrors and rational diagnostics are scratch only. Existing compiled source and retrieved exact-head audit artifacts, not a fresh whole-repository build, support the formal input statuses.

Checkpoint publication was already verified at commit **a3cc177b6f96a04c108ddbdccc240d4f4d64d983**, report blob **f8464c2fa8a034bceb6b46c4868eab881d04c475**. Main remained unchanged at the final authority refresh; the reports branch then contained that checkpoint with all other intake handoffs unchanged. This synthesis's publication is not claimed complete until the immutable readback receipt below is added.

**Next-run capsule.** Preserve `20261107-referee-3/TF1-TF5`, accepted RG1-RG3 scopes, RG4=UNRESOLVED, conditional RG5 acceptance, and PAPER/SELF_AUDIT status of TF1-TF3. First inspect any independent review or implementation of the two-envelope LHS identity and actual-Q mass payment. Do not repeat unchanged scalar grids or claim certification from old #1091. If those proofs survive, audit the complete m/4 endpoint and all loss constants before marking a new certified gain. Any subsequent improvement must confront the remaining HIGH reserve, not reuse the same payment credit.

### Verified Publication Receipt - 20261107-referee-3

Verified at 2026-11-07 20:33:31 EST / 2026-11-08 01:33:31 UTC: synthesis commit **23d1e36d2a68af4381b002cbc75c214ea02512a8**, report blob **d722a7d329dc01439979befd134716a2c9a11d94**, was re-fetched by immutable commit and matched the intended full content exactly. Its commit changes only this own daily report, adding 492 lines and deleting zero. The entire preexisting report and verified early checkpoint are preserved byte-for-byte as a prefix. The 21 material main-file hash entries and all A-O report sections were checked before writing.

Execution/publication status: **COMPLETED / PUBLISHED / READBACK_VERIFIED** for this research synthesis. Mathematical status is separate and unchanged: RG1-RG3 accepted independently at paper/scalar scope; RG4 remains unresolved; TF1-TF3 are new paper proofs with self-audit only, independent review pending, and NOT_FORMALIZED; TF4 is the scoped scalar budget obstruction; TF5 is exact rational diagnostic computation. **NEW_VERIFIED_ENDPOINT_GAIN=NONE; VERIFIED_ETA=NONE.** The canonical VF objective remains OPEN. The receipt itself is a subsequent own-report-only append, with its final immutable readback checked before the user-facing completion message.

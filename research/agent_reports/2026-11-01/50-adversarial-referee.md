# RH_Lean agent daily report - 2026-11-01 / RH | Adversarial Referee

## Scheduled invocation checkpoint - 2026-11-01 04:15:50 EST (-0500)

**Status:** IN_PROGRESS / independent restricted-inversion audit completed; final proof capsule and publication readback pending.  
**Invocation:** RUN_ID_UNAVAILABLE; scheduled run invoked 2026-11-01 04:13 America/New_York.  
**Live main:** `5b232a4fa633fad5e73a9b7ebfb76572ecb1dbb0`.  
**deployment_ack:** first actual Referee consumption of policy/main `5b232a4f...`; selected `NEXT-REFEREE: restricted-inversion audit and actionable repair`; resumed claim `20261031-coordinator-3`.  
**Authority blobs:** `AGENTS.md` `9fa5e9519e2fb6dde22217aa2a18982dafef373a`; `CURRENT_PROOF_CONTRACT.md` `88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a`; selector `d05c327ae694ea54b599dab0a21032a056b521f1`; research engine `6fce99c61efb5b2a73c0cb1f1464f09b351fcd55`.  
**Material source blobs:** `EULER_FRACTIONAL_COUPLED_20261027.lean` `e6c4b1690e497760d366e36b28a1f7aa60e19f85`; `EULER_PRIME_RAY_SOURCE_ADMISSION_20261031.lean` `d164dccf992e24fe1c6378fefa75c03535ad5de8`; `EULER_PHYSICAL_COMPLETE_PACKET_20261030.lean` `8084af7fa50fb5b8361a64f05eb658f08b529ca7`.  
**eta_gate:** SEARCH_BROAD; net endpoint gain after complete return: UNKNOWN.

### Preliminary verdict

Claim `20261031-coordinator-3` splits.

- Equation (28), the fixed-seed restricted Mobius divisor identity, is mathematically correct.
- Equations (31)-(34) are correct at fixed squarefree seed after adding eventual-size quantifiers and explicitly sorting each distinct pair into the original `a<b<R` carrier.
- The proposed disjoint-seed globalization is not proved as written. Fixed-seed completion uses `gcd(m,s)=1`; the claimed disjoint primorial partition requires `gcd(m,P(z))=1`. These are different sums.
- Exact overlap witness: for `P(z)=6`, the same coefficient `a=6` occurs in the fixed-seed families as `(s,m)=(2,3),(3,2),(6,1)`, but only `(6,1)` belongs to the disjoint complete-small-prime-content partition.

The qualitative warning survives after repair: the correctly disjoint partition exactly reconstructs the full Mobius divisor sum and therefore supplies no global cancellation estimate by itself. The final report will state the corrected identity, growing-seed loss, exact verdict classes, and smallest Lean-ready lemma.

## Final synthesis - claims `20261101-referee-1,2` - 2026-11-01 04:17:01 EST (-0500)

**Status:** COMPLETED.  
**Evidence classes:** `PAPER_ACCEPTED_WITH_SCOPE`; `REVISE_WITH_EXACT_REPAIR`; `EXACT COUNTEREXAMPLE TO STATED GLOBALIZATION MECHANISM`; `PAPER_ACCEPTED_WITH_MINOR NORMALIZATION REPAIR`; `NO COMPLETE SOURCE BOUND`; `NO FIXED ETA GAIN`; `NO RH`.

### A. Authority, continuity, and formal status

The canonical objective remains
```text
exists C >= 0, forall R >= 2,
  |pi(R^2) - VF_can(R^2)| <= C R log R.
```
The nearer benchmark is a complete genuine sharp-shell estimate with one fixed positive exponent gain. Neither is proved.

At intake, today's Coordinator, Referee, and Lean files were `TODAY=PENDING`. Today's Owner, Analytic, Wheel, and Census reports were consumed at blobs `4604617532db0ab8b1e5d5da495f2e698e1aa575`, `411159fdab234c02f66df812c2eae2ef17487ace`, `38d69518d7e30769798637920cfcaecaa4e09c2a`, and `fca27fe912377722ad6acaaf193b4841284b67fb`. Yesterday's Coordinator and Referee were carried forward at blobs `6af6829827ecff25bac0dc2728f56a2a3eca049e` and `0d923f611ab8cb00f83f0dbd34605f447855c838`; the remaining October 31 continuity blobs are those recorded in today's upstream reports. External handoffs remain blob `038018145c0fddb2f6306c0712373adf9cd1ea52`, with no entry newer than October 18.

No open or draft PR was returned. PR #1062 is merged and its exact proof head `4309335c...` has 12/12 returned workflows successful. PR #1063 is merged; its first proof head had a workflow-script failure, while the corrected exact head `b2dcf5b4...` has all 12 returned workflows successful, including the dedicated source-admission, warning-fatal source audit, proof inventory, targeted iteration, and public-export runs. The current merge head itself returned no attached workflow or combined-status entries. The theorem on main proves only the `s=2` occurrence/sign bridge, not the general fixed-seed telescope.

### B. Claim `20261101-referee-1`: fixed-seed restricted inversion

For an integer `s>=2`, define
```text
Psi_s(A) = #{n <= A : every prime divisor of n divides s}.
```
Then for every `A>=1`,
```text
sum_(m<=A, gcd(m,s)=1) mu(m) floor(A/m) = Psi_s(A).       (R1)
```
This is **ACCEPT**. Reversing the finite sum gives, at each `n<=A`,
```text
sum_(m|n, gcd(m,s)=1) mu(m).
```
It is one exactly when `n` has no prime divisor outside `s`, and zero otherwise. If `r=omega(rad(s))`, unique prime-exponent coordinates give
```text
Psi_s(A) <= (1+floor(log_2 A))^r.                         (R2)
```

Now fix squarefree `s`, prime `R/2<q<R), `s<q), `X=R^2-1`,
```text
L_s=floor((R-1)/s),   A_s,q=floor(X/(s q)).
```
For `1<=m<=L_s`, `gcd(m,s)=1), one has `m<q`, hence `q` does not divide `sm), and
```text
mu(sm)mu(q) = -mu(s)mu(m).
```
The two positive factors `sm,q` are distinct and below `R`. Sorting them as
```text
a=min(sm,q), b=max(sm,q)
```
places the row in the literal `1<=a<b<R` carrier. Symmetry of product, floor, fractional remainder, and Mobius weight preserves the term. Within one fixed seed, the map `(m,q)` to this row is injective: `q` cannot divide `sm`, and a prime coordinate cannot be confused with a composite `sm`; the remaining prime-seed case is also unique because `q>s`.

Since `q<R`, `A_s,q>=L_s`. Since `q>R/2`,
```text
A_s,q < 2(L_s+1).
```
Thus every omitted completion index `L_s<m<=A_s,q` has `floor(A_s,q/m)=1`. Applying (R1) yields exactly
```text
T_R,s(q) = -2mu(s) [
  Psi_s(A_s,q)
  - sum_(L_s<m<=A_s,q, gcd(m,s)=1) mu(m)
].                                                            (R3)
```
This is **ACCEPT_WITH_SCOPE** as a fixed-seed original-row identity.

If `1<=U<=R/2` and `R-U<q<R`, then
```text
A_s,q-L_s
 <= 1 + ((R-1)(R+1-q))/(s q)
 <= 1 + 2(U+1)/s.                                             (R4)
```
Therefore
```text
|sum_q T_R,s(q)|
 <= 2U[(1+log_2 R)^omega(s)+1+2(U+1)/s].                      (R5)
```
For fixed `s`, fixed `0<alpha<3/8`, and all sufficiently large `R` so that `s<q`, `U=floor(R^alpha)>=1), and `U<=R/2), dyadic summation gives
```text
sum_(H<=R<2H) |sum_q T_R,s(q)|^2
 = O_s(H^(1+4alpha) polylog H)
 = O_s(H^(5/2-eta) polylog H),
eta=3/2-4alpha>0.                                             (R6)
```
This is a valid local fixed-seed energy saving. It is not a bound for the complete Euler source or the square shell.

### C. Exact failure in the disjoint-seed argument

The fixed-seed families are not disjoint. With `P=6`, the coefficient `a=6` appears as
```text
(s,m)=(2,3), (3,2), (6,1),
```
and each pair satisfies `gcd(m,s)=1`. This is an exact occurrence-reuse counterexample to summing the fixed-seed identities as a partition.

The distinction changes the principal. For `A=3`,
```text
sum_(m<=3, gcd(m,2)=1) mu(m)floor(3/m) = 3-1 = 2 = Psi_2(3),
```
whereas the disjoint `P=6` condition gives
```text
sum_(m<=3, gcd(m,6)=1) mu(m)floor(3/m) = 3 = Psi_6(3).
```
Thus `gcd(m,s)=1` cannot be silently replaced by `gcd(m,P)=1`.

The strongest correct repair is nevertheless an exact no-narrowing identity. Let `P` be squarefree. Every squarefree `a` has the unique decomposition
```text
s=gcd(a,P), s|P, a=sm, gcd(m,P)=1.
```
Zero Mobius coefficients may be added harmlessly. Hence for every `A>=1`,
```text
sum_(s|P) mu(s)
  sum_(m<=floor(A/s), gcd(m,P)=1)
    mu(m) floor(A/(sm))
 = sum_(a<=A) mu(a)floor(A/a)
 = 1.                                                         (R7)
```
For each fixed `s), the inner completed principal is
```text
Psi_P(floor(A/s)),
```
not `Psi_s`. Therefore (R7) is equivalently
```text
sum_(s|P) mu(s) Psi_P(floor(A/s)) = 1.                         (R8)
```

Verdict on the submitted globalization paragraph: **REVISE_WITH_EXACT_REPAIR**. Its stated derivation conflates overlapping fixed-seed completion with a disjoint primorial partition. Its qualitative conclusion survives: the correctly disjoint complete union is exactly full Mobius inversion, so it is identity-only and supplies no global estimate.

### D. Growing-seed constants and the surviving obstruction

Bound (R5) is uniform only after retaining
```text
(1+log_2 R)^omega(s).
```
If `s=s(R)`, this contributes
```text
exp(omega(s) log log R)
```
to amplitude and twice that logarithmic loss to energy. To retain merely a subpower loss, one needs at least
```text
omega(s) log log R = o(log R).                                (R9)
```
For a primorial `P(z)`, this is `pi(z)log log R=o(log R)`. Separately summing all `2^pi(z)` seed classes by triangle inequality adds another exponential seed-count loss and destroys the signed cancellation in (R8). At larger `z`, exact signed reassembly rather than componentwise absolute estimates is mandatory.

Thus the first genuinely missing theorem is not another fixed-seed identity. It is a uniform smooth/rough boundary estimate on the corrected disjoint carrier, with moving cutoffs, cross-seed signs, squareful rows, diagonal, principal, reciprocal-square, activation, complement, and endpoint restoration retained. No such theorem is established here.

### E. Claim `20261101-referee-2`: NYMAN follow-up review

Today's Analytic claim `20261101-analytic-1` was the next consequential ready claim from a different portfolio.

The exact interpolation identities (1), (4), and (5) are **ACCEPT_WITH_SCOPE**. They follow by expanding
```text
a_k(m)=m/k-floor(m/k)
```
and using the finite divisor identity
```text
sum_(k<=m) mu(k)floor(m/k)=1.
```
The first-tail lower bound (2), its RMS consequence (3), the fixed-damping coordinate obstruction (6), the finite-to-infinite certificate (7), the absolute-method loss (8), and the block lower bound (9) are also correct. The report correctly distinguishes the actual signed tail from the unusable absolute upper bound.

Equation (10) needs a minor exact repair. The inclusive interval
```text
ceil(N/2) <= m <= N
```
contains
```text
J_N=floor(N/2)+1
```
integers, not `floor(N/2)`. From (9) and `D_N(c)^2<=U_N`,
```text
sum_block |G_delta(m)-1-mA_N,delta|^2 <= N(N+1)U_N.
```
Since `N/J_N<=2`, the intended estimate is
```text
(1/J_N sum_block |...|^2)^(1/2)
 <= sqrt(2(N+1)U_N).                                          (R10)
```
With the submitted denominator `floor(N/2)`, the constant `2` is not justified for odd `N`; a coarser constant `3` would work. This off-by-one does not alter the qualitative NYMAN obstruction or the identified open signed-tail problem.

Verdict: **PAPER_ACCEPTED_WITH_MINOR_NORMALIZATION_REPAIR**. It proves no optimized-distance decay, no fixed eta, and no RH statement.

### F. No-circularity and complete-return verdict

- (R1)-(R6) introduce genuine finite divisor cancellation on a fixed original-row family; they are not target-equivalent.
- The same row can belong to several fixed-seed families. No global quadratic statistic may sum those families without a disjoint allocation and all resulting cross terms.
- The corrected disjoint union (R7) is an exact rearrangement of full Mobius inversion. Treating its boundary as already controlled would assume the missing arithmetic.
- The fixed-seed local eta is not a complete-return eta. All complementary Euler rows and the full endpoint consumer remain unpaid.
- The NYMAN identities isolate necessary bills for two explicit coefficient constructions. They do not constrain the optimized full basis without an independent approximation theorem.

### G. Lean-ready surviving theorem

The smallest nonduplicate formal target is (R1), stated for arbitrary natural `s,A`, with `Psi_s` defined by prime support. It is independent of the original Euler carrier and can be proved by a finite divisor-sum reversal. A second theorem may formalize (R3), but only after an explicit general-`s` source-admission/sorting theorem; merged #1063 certifies only `s=2`.

The corrected disjoint identity (R7) is also formalizable and useful as a no-double-counting regression. It must not be advertised as a source estimate.

### H. Routing check and resume capsule

- `eta_gate: SEARCH_BROAD`.
- `primary_route_and_original_carrier: restricted prime-ray completion / literal strict Euler factor-pair rows`.
- `actual_new_lemma_or_first_unresolved_inequality:` corrected disjoint identities (R7)-(R8), overlap witness `a=6`, growth condition (R9); unresolved uniform signed smooth/rough boundary after complete return.
- `independent_reviewer_and_formal_evidence:` this Referee paper audit; fixed-seed generalization not in Lean. Merged #1063 proves only the `s=2` row bridge at corrected green head.
- `net_endpoint_gain_after_complete_return: UNKNOWN`.
- Secondary portfolio review: NYMAN claim accepted after repair (R10); its joint signed-tail/full-basis decay remains open.
- Owner claim `20261101-owner-2` remains target-equivalent by its cited compiled exact restoration; no inference from residual `<21` to an exponent is accepted.
- Complete shell bound, strict Mertens exponent below `7/8`, canonical VF theorem, and RH remain OPEN.
- Next decisive Referee action: audit the first proposed growing-`P(z)` boundary theorem on the corrected disjoint carrier, or a complete signed NYMAN tail estimate if it becomes ready. Do not re-review the fixed-seed identity absent changed hypotheses.


## Scheduled continuation checkpoint - 2026-11-01 12:06 EST (-0500)

**Status:** IN_PROGRESS / exact mixed-kernel and scalar-threshold reconstruction completed; final scoped verdict and publication readback pending.  
**Invocation:** RUN_ID_UNAVAILABLE; scheduled invocation began 2026-11-01 12:03 America/New_York.  
**Live main:** `417cb62ee8ca65c82dd3aad1263c7529e94668eb` (human merge of PR #1068).  
**Selected task:** newer Coordinator assignment supersedes the already completed bootstrap review: independently audit claim `20261101-coordinator-1` and Wheel claim `20261101-wheel-1`.  
**Authority blobs:** `AGENTS.md` `9fa5e9519e2fb6dde22217aa2a18982dafef373a`; `CURRENT_PROOF_CONTRACT.md` `88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a`; selector `d05c327ae694ea54b599dab0a21032a056b521f1`; research engine `6fce99c61efb5b2a73c0cb1f1464f09b351fcd55`.  
**Material source blobs:** weighted common-clock coordinate `f0e2e672a1ed369d1dc6dacbe9024c65e986a3c8`; first-owner daughter Gram `b57a3e9030445262ec847ca0e20a60bc35ff127c`; CORR4 record/frame source `a4abeb13653076bedd8e1173c933ee3324bfea26`; physical transport `72d66f61b3eeb000117ecdac393572558bb7c378`; merged odd telescope `fbe472cca89f757c8f6f25e630a49847a2bd6ad0`.  
**Preliminary verdict:** (C1)-(C2) reconstruct the exact mixed product and its full fresh-prime owner partition, but prove no inequality. The `478/211` boundary is algebraically sharp under exactly the frame and record premises. The final section will record endpoint, diagonal, owner-range, null-fibre, and complete-return scope.


## Scheduled continuation final synthesis - claims `20261101-referee-3,4` - 2026-11-01 12:06 EST (-0500)

**Status:** COMPLETED.  
**Evidence classes:** `PAPER_ACCEPTED_WITH_SCOPE / EXACT IDENTITY`; `EXACT DIAGONAL RECONSTRUCTION`; `EXACT NULL-FIBRE COUNTEREXAMPLE`; `PAPER_ACCEPTED_WITH_SCOPE / SHARP SCALAR NO-GO`; `NO NEW SOURCE BOUND`; `NO COMPLETE ETA`; `NO RH`.

### I. Live authority, continuity, and formal state

The canonical objective remains
```text
exists C >= 0, forall R >= 2,
  |pi(R^2) - VF_can(R^2)| <= C R log R.
```
No complete positive gain, strict Mertens exponent below `7/8`, canonical VF theorem, or RH proof is established.

This continuation consumed the current November 1 Coordinator, Owner, Analytic, Wheel, Census, prior Referee, and Lean reports at blobs `c23d71084b9103d22e0ade268535dbcab18fc229`, `d57ca6c383884e0b2b9ef38809d589b60b355a42`, `97ebebec389bdafaa6c8e49afdde1b06f682779e`, `3c9752a5a580bcce27ca0af4b3281c1fbdac4dd8`, `b752c3393c6846b52abd11dd9ac40d9ccf6d1e99`, `01f2f9b84e28e985eef5a168bb86b944cca7924a`, and `a43d35c4534d3c1473e3fe9f910b481ec96e3429`. The October 31 continuity set was rechecked at blobs `6af6829827ecff25bac0dc2728f56a2a3eca049e`, `fdb9413fdd49588e1ad1c2348b4fabf4cff55b9c`, `574c544048e225475569c57f95ca1e47237ab733`, `5e62d4c536061564ceca0444a844f51b8886a7fd`, `46f6923fa188e5ed6036d6097b23360c32088fc0`, `0d923f611ab8cb00f83f0dbd34605f447855c838`, and `f81efcbb4a771e4b9a5b5ea713c0f1c5d4148d32`. External handoffs remain blob `038018145c0fddb2f6306c0712373adf9cd1ea52`, with no entry newer than October 18.

PR #1068 is now **MERGED** by a human. Its exact proof head `75d9cf05071502fad0fd76f7336c16f38b2faa33` has 12/12 returned PR workflows completed successfully, including dedicated run `41298543667`. The merge commit is live main `417cb62ee8ca65c82dd3aad1263c7529e94668eb`; the merge commit itself has no attached PR-triggered workflow runs or combined-status entries. Main source `research/ODD_MOBIUS_FLOOR_TELESCOPE_20261101.lean`, blob `fbe472cca89f757c8f6f25e630a49847a2bd6ad0`, proves the finite odd Möbius floor telescope and no truncated-tail or endpoint estimate. Open/draft PR refresh returned none.

### J. Claim `20261101-referee-3`: mixed common-clock owner decomposition

Set
```text
X = R^2 - 1,
h_R(n) = 1_[R <= n <= X],
W_R(n) = sum_(q in canonicalRoughLowQ2Owners R)
           1_[n <= floor(X/q^2)] / q.
```
The compiled common-clock theorem gives
```text
U_R = sum_(1<=n<=X) W_R(n) mu(n),
```
and the exact endpoint gap is
```text
G_R = M(X)-M(R-1)
    = sum_(1<=n<=X) h_R(n) mu(n).
```
Finite multiplication, not an estimate, gives
```text
G_R U_R
 = Dmix_R
 + sum_(1<=m<n<=X) K_R(m,n) mu(m)mu(n),                    (R11)

K_R(m,n)=h_R(m)W_R(n)+h_R(n)W_R(m),
Dmix_R=sum_(1<=n<=X) h_R(n)W_R(n)mu(n)^2.
```
The endpoint convention is correct: both source sums use the inclusive endpoint `X=R^2-1`, while `M(R-1)` removes exactly `n<R`.

The diagonal can be reconstructed more explicitly:
```text
Dmix_R
 = sum_(q in canonicalRoughLowQ2Owners R) (1/q)
     sum_(R<=n<=floor(X/q^2)) mu(n)^2 >= 0.                 (R12)
```
This term is not part of the off-diagonal owner fibres and cannot be dropped. Formula (R12) follows by substituting the literal `W_R` and exchanging finite sums. It is source-faithful but supplies no useful upper bound by itself.

For each prime `p<=X`, define
```text
J_R(p)=sum_(1<=m<n<=X, IsSquarefreePairFreshPrimeOwner p m n)
         K_R(m,n)mu(m)mu(n).
```
The compiled theorem `squarefreePairFreshPrimeOwnerExpansion_eq_pairWeight` applies to every `m<n<=X`. For a nonzero Möbius pair, both sites are squarefree and the owner is unique; for a zero pair, the expansion is still exactly zero. Multiplying by the owner-independent scalar `K_R(m,n)` and exchanging finite sums yields
```text
sum_(1<=m<n<=X) K_R(m,n)mu(m)mu(n)
 = sum_(p prime, p<=X) J_R(p).                               (R13)
```
Thus Coordinator equations (C1)-(C2) are **ACCEPT_WITH_SCOPE / EXACT IDENTITY**.

The scope is essential:

1. The owner range in (R13) is all fresh-prime owners through `X), not the low q-squared daughter-owner set.
2. `K_R>=0`, but the fibre sign is still the genuine sign of `mu(m)mu(n)`; no one-sided estimate follows.
3. The nonnegative diagonal (R12) remains separate.
4. A bound simply postulated on `sum_p J_R(p)` at the needed size could rehouse the original mixed-correlation problem. Independent incidence information is still required.
5. Neither (R11) nor (R13) restores owner two, renewal, terminal products, root correction, or the other complete physical populations.

### K. Null-fibre corollary

The main theorem `lowOwnerPhysicalAmplitude_zero_daughter_witness` gives
```text
rawQ2ChildCutoff 64 5 = 163,
lowOwnerRawMertensAmplitude 64 5 = 0,
farFourQ2OwnerSynthesisAtom 64 5 = -16.
```
This is a legal low owner: `5` is an odd prime below `64` and `5^2<64`, hence `5 in canonicalRoughLowQ2Owners 64`. Since raw daughter energy is the squared norm of the raw amplitude, it vanishes while the physical atom has squared norm `256`. Therefore, for every finite real `C`,
```text
|physicalAtom(R,q)|^2 <= C * rawQ2ChildEnergy(R,q)
```
is false as a universal legal-owner statement. Verdict: **EXACT COUNTEREXAMPLE TO DAUGHTER-ONLY POINTWISE TRANSPORT**. It does not refute aggregate signed compensation with the physical correction retained.

### L. Claim `20261101-referee-4`: sharp `478/211` scalar boundary

Let `b=211/900`. For real `G,U,E` and `lambda>=0), assume exactly
```text
U^2 <= bE,    E <= bG^2.                                    (R14)
```
Then `U^2<=b^2G^2`. From `(U+bG)^2>=0`,
```text
2GU >= -2bG^2.
```
Also `-lambda E >= -lambda bG^2`, so
```text
G^2+2GU-lambda E
 >= [1-b(2+lambda)]G^2.                                     (R15)
```
Equality is attained under (R14) at
```text
G=1, E=b, U=-b.
```
Consequently the coefficient of `G^2` is strictly positive exactly for
```text
0 <= lambda < 1/b-2 = 478/211.                              (R16)
```
This proves sharpness for the information in (R14), not realizability of the scalar extremizer by genuine Möbius data at infinitely many roots.

The specializations are correct:
```text
lambda=2:   coefficient 14/225,
lambda=9/4: coefficient 13/3600,
lambda=4:   coefficient -61/150.
```
Using the compiled mixed identity
```text
2M_mix=G^2+2GU-(D-P),
```
with `D<=3R^2` and `P>=0`, one obtains
```text
2M_mix-lambda E
 >= [1-b(2+lambda)]G^2-3R^2.                                (R17)
```
Thus Wheel claim `20261101-wheel-1` is **ACCEPT_WITH_SCOPE / SHARP SCALAR NO-GO**. Its phrase “complete returned inequality” is valid for the exact mixed bill and its two displayed diagonals only. It is not the complete CORR4 endpoint: the remaining physical owner-two, renewal, terminal, root-correction, and complementary terms are outside (R17).

The reported `R=2002` values are consistent with the adverse orientation and satisfy the record premise, but they are a finite regression rather than part of the proof. The no-go rules out obtaining a positive coefficient-four reserve solely from (R14). It does not rule out a genuine signed incidence theorem for the exact fibres (R13), joint absorption with omitted physical terms, or a Möbius-specific restriction excluding the scalar extremizer.

### M. No-circularity, surviving theorem, and next obstruction

- (R11)-(R13) are exact reindexings with a separately reconstructed diagonal. They do not reduce the quantitative difficulty until a new arithmetic restriction on the actual owner fibres is proved.
- (R15)-(R17) are sharp consequences of the frame and conditional record predicate. They are inverse restrictions, not forward mixed-tail estimates.
- The daughter-only pointwise route is refuted exactly at `R=64,q=5`; aggregate compensation survives as an open possibility.
- The strongest useful next statement must be one-sided and Möbius-specific on the complete expression
```text
Dmix_R + sum_(p<=X) J_R(p),
```
or on a jointly restored physical bill. A norm concentration statement that omits the diagonal or correction carrier cannot consume the mixed term.
- No complete-return eta follows. The gate remains `SEARCH_BROAD`.

### N. Routing check and resume capsule

- `eta_gate: SEARCH_BROAD`.
- `primary_route_and_original_carrier: CORR4 mixed common-clock endpoint/daughter product with all fresh-prime owners`.
- `actual_new_lemma_or_first_unresolved_inequality:` exact diagonal formula (R12), accepted owner partition (R13), sharp scalar no-go (R15)-(R17); unresolved Möbius-specific one-sided fibre/complete-physical estimate.
- `independent_reviewer_and_formal_evidence:` this paper audit; common-clock, fresh-owner, frame, diagonal, and null-fibre inputs are compiled on main at the blobs above. The combined mixed-owner identity and parameterized threshold are not Lean declarations.
- `net_endpoint_gain_after_complete_return: UNKNOWN`.
- PR #1068 is merged; exact proof-head CI is green, and its theorem remains structural only.
- Next decisive Referee action: audit a proposed Möbius-specific bound on `Dmix_R+sum_p J_R(p)` with the full owner range and correction carrier, or review Wheel claim `20261101-wheel-2` if no such bound is ready. Do not re-audit (R11)-(R17) absent changed hypotheses.
- Complete shell bound OPEN; strict Mertens exponent below `7/8` NOT PROVED; canonical VF theorem OPEN; RH OPEN.

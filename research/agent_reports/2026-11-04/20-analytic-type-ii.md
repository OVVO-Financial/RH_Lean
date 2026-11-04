# RH | Analytic Type II - 2026-11-04

**New paper result, independent review pending:** an explicit two-scale Nyman coefficient family has an exact polynomial-sized initial interval, a controlled transition layer, and an O(log(N)^(-2)) infinite tail beyond ceil(N^(3/2)), using the existing fixed sublinear Mertens input. The completed middle remains OPEN. No RH proof or new exponent is claimed.

## Early Research Checkpoint - 2026-11-04 01:08 EST (-0500)

**Status: PARTIAL / IN_PROGRESS.** Invocation: scheduled 2026-11-04T01:04:01-05:00; RUN_ID_UNAVAILABLE. No new theorem or endpoint gain is claimed at this checkpoint.

### A. Selected mathematical question

NYMAN is the protected route due after November 3 NYMAN / OAI-NNS / CODIV. Resume Coordinator C33-C35 and Referee NR6: change the actual low Mobius coefficients, retain their complete floor-defect return, and attempt a useful bound for the middle range. The first candidate is a flat-head logarithmic taper with distributed moment correction, compared against the previous fixed-low construction. The previously accepted remote-tail theorem will be reused, not rediscovered. All coefficient choices, head/middle/tail boundaries, and falsifiers will be fixed before finite checks.

### B. Current authority and original carrier

Actual main HEAD: 040980c16901af749202e9b0f91211c43909404a.
AGENTS blob: b878d396c387a57bd0b5165fecf10d15ef3732cd.
Source-first contract blob: b6980c30e63bb8c9ddfc8d6fa86a2bb401707fa6.
The canonical actual-prime VF square von Koch bound and RH remain OPEN.

NYMAN source: research/NYMAN_BEURLING_POSITIVE_RESIDUE_ATTACK_2026_10_15.md, blob b2775c892edffe920a101651eef6f3581c73c9d4. Actual basis a_k(m)=(m mod k)/k and weights 1/[m(m+1)] are unchanged. No identification with rational owner or OAI ideal-character sources is asserted.

### C. Continuity and source-first comparison

Retrieved November 3 Coordinator, Owner, own, Wheel, Census, Referee and Lean reports, plus today's Owner 20261104-owner-1 (blob 546f46832e12fdf80d32713d26978e63e1d7b7d5). Other November 4 upstream roles: TODAY=PENDING; YESTERDAY=CARRY_FORWARD, not fabricated completed stages. External inbox blob 038018145c0fddb2f6306c0712373adf9cd1ea52 has no entry newer than October 18; historical routing does not supersede current authority.

Source-first policy consumed. Latest Referee R9/R10 and Lean's independent paper qualification isolate J=empty, the ALL-selected packet, at original untilted geometry. Original LowSlotPolynomial/LowTupleGram were fetched at openai/math 1581d4cbdd69a0faf34b2089614fe2a814316a6a: blobs b1dcb5a1e51afad1d39ccd91fa58a764e39629ba and 710598c8bef4d1a1ec98aa7e68b00369962c3d17. The outer triangle is equality for that singleton carrier. New OAI signed gain remains OPEN; the due NYMAN turn is not displaced.

PR #1083 is MERGED, head 1ae84e2ff019b266114c100f43016eeec71144a9; 14 returned exact-head-associated check runs succeed. Dedicated run 41744927180 / job 126295407267 was retrieved. The genuine signed Gram is structural, not a nu estimate. No open/draft PR was returned. Formal-source status and new research status remain separate.

### D. Investigation and falsification plan

Compare at most two low-edit mechanisms, develop one, and preserve all middle and infinite-tail terms. Test exact coefficient moments, every-coordinate residual reconstruction, cutoff boundaries and the low-edit annihilator. A successful initial-range/tail bound is not full density. Any numerical experiment will be finite bookkeeping only, not an asymptotic proof.

### E-L. Pending completion

Derivation, quantitative comparison, complete source return, self-audit, specialist requests and final resume capsule will be appended in this same report. Independent review and any new Lean certification remain PENDING. Publication is recorded only after commit/readback. Own-report-only permissions; no proof branch, source edit, local Lean, schedule change, agent launch or merge.

---

## Final Research Synthesis - 20261104-analytic-1 - 2026-11-04 01:30 EST (-0500)

This is the final mathematical synthesis for the scheduled 01:04:01 EST invocation, not another launch. New mathematics: PAPER_PROOF / EXACT_IDENTITY / SELF_AUDIT; independent review PENDING; NOT_FORMALIZED. Finite checks are exact algebra, not asymptotic certification. Publication verification is recorded separately. No literature-novelty, new Mertens exponent, canonical VF estimate, or RH claim is made.

### A. Most Important Analytic Development

**A lawful low-coefficient change simultaneously gives an exact polynomial-sized initial interval and an O(log(N)^(-2)) infinite tail.** Unlike yesterday's construction, it does not keep the logarithmic Mobius coefficients fixed on that initial interval. The prime-power term cancels in an exact difference of two logarithmic approximants. Both distributed correction terms and both omitted-modulus sums remain in the full residual.

Fix 0<theta<1 and a genuine prefix envelope |M(x)|<=C x^b with 0<b<1, C>=1. For every sufficiently large N divisible by six, set H=floor(N^theta), ell=log(N/H), and T=ceil(N^(3/2)). The explicit coefficients in D satisfy

```text
r_(N,H)(m)=0                                       (1<=m<=H),
sum_(m>T) r_(N,H)(m)^2/[m(m+1)] = O_(b,C,theta)(log(N)^(-2)).
                                                               (P1)
```

There is also an independently bounded first-return layer: with t=floor(H^(4/5)), eventually

```text
sum_(H<m<=H+t) r_(N,H)(m)^2/[m(m+1)] <= ell^(-2).    (P2)
```

The exact head and P2 require no Mertens input. The remote-tail estimate uses only the displayed existing sublinear prefix input and the previously accepted rational-frequency tail theorem. The repository's `nativeReplay_mertens_growth`, with positive loss 1/16, supplies b=15/16. No new cancellation theorem for mu is smuggled into this application.

The **complete middle remains OPEN**. A fully displayed attempt to bound its first large part from the same prefix input yields only

```text
sum_(H<m<=N/2) r_(N,H)(m)^2/[m(m+1)]
 <= C^2 K_b^2 N H^(2b-2)/(2 ell^2),
K_b=(2-b)/(1-b)^2.                                  (P3)
```

For H=N^theta and b>=1/2, the right side has positive power 1-2theta(1-b). This is a failure of that upper-bound method to prove decay, NOT a lower bound or a refutation of the family. The new result combines exact initial interpolation with a quantitatively paid far tail and a paid transition layer; it does not solve density.

### B. Current Mathematical Objective And Authority

Actual main HEAD: **040980c16901af749202e9b0f91211c43909404a**. The canonical target is still the actual-prime statement

```text
exists C>=0, forall integer R>=2,
  |pi(R^2)-vfCanonical(R^2)| <= C R log R,
vfCanonical(x)=vfMid(x)+sqrt(2).
```

The original declaration [`VFCanonicalSquareVonKochStatement`](https://github.com/OVVO-Financial/RH_Lean/blob/040980c16901af749202e9b0f91211c43909404a/research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean) and its terminal consumer were inspected. The classical von Koch criterion remains an explicit interface argument on that consumer. This run uses the separate full-basis NYMAN route, not an asserted occurrence map to VF owners, square shells, or OAI ideals.

Registry connection: `MECH-NYMAN-FULL-BASIS-DECAY` supports the still-open `OPEN-NYMAN-DENSITY`; its external `LIT-BAEZ-DUARTE` consumer is not newly formalized here. P1/P2 are partial quantitative supporting results for that mechanism, not closure of either registry obligation. The [existing prefix input](https://github.com/OVVO-Financial/RH_Lean/blob/040980c16901af749202e9b0f91211c43909404a/research/oai_434/VF919NativeSevenEighthsReplay.lean) is `nativeReplay_mertens_growth`; no new Mertens converse hypothesis is supplied.

Material main/source blobs actually retrieved:

| Source | Blob SHA |
| --- | --- |
| AGENTS.md | b878d396c387a57bd0b5165fecf10d15ef3732cd |
| CURRENT_PROOF_CONTRACT.md | 63f7553bf6e5f2a16e37808116c643dc0dcc50e1 |
| docs/RHLEAN_NATIVE_SQUARE_CLOCK_AGENT_DIRECTIVE_20261029.md | 3cb817ab9aae51429858d5a98727e16dbd072d47 |
| docs/RHLEAN_BROAD_SEARCH_UNTIL_ETA_20261031.md | f5d754ce6b06d98643f30beeccb4bf7bd1f6242a |
| docs/RHLEAN_SOURCE_FAITHFUL_COMPLETE_RETURN_AGENT_CONTRACT_20261031.md | 4775ee5fd95f279beab08a75d1e17127078b19a6 |
| docs/RHLEAN_OAI_LOW_SOURCE_FIRST_AGENT_CONTRACT_20261103.md | b6980c30e63bb8c9ddfc8d6fa86a2bb401707fa6 |
| docs/RHLEAN_SEVEN_AGENT_RESEARCH_ENGINE_20261101.md | 495fa9ee2067ccf5db9dc3c48ffaaadcd6485aa4 |
| docs/RHLEAN_ALL_VECTOR_AGENT_PROMPTS_20261030.md | 6fa78bdecd4670075350f269f54e88618359e94d |
| docs/DYNAMIC_RESEARCH_AGENTS.md | ea90322f257a12dc694ca4a188fe4c5715880c79 |
| docs/RHLEAN_MULTIRUN_DAILY_AGENT_POLICY_20261031.md | 643cfd596116720a8e5b1efc07a6124b55d70946 |
| docs/RHLEAN_ALL_VECTOR_SYNTHESIS_AGENT_DIRECTIVE_20261030.md | 2b73da99c5f4b272e7d99c54b41d72220266b00d |
| docs/proof-obligations.json | 02bc2f408c709f7949f4bfcb06dadf5eff485b3d |
| research/NYMAN_BEURLING_POSITIVE_RESIDUE_ATTACK_2026_10_15.md | b2775c892edffe920a101651eef6f3581c73c9d4 |
| research/MERTENS_CONVERSE_IDENTIFICATION.lean | 768c8255850bf4074aff265c3fe17a1f5c43979b |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |
| research/oai_434/VF919NativeSevenEighthsReplay.lean | 111c933a7ca15647105ce6a4d0f3cbfc3cde81f4 |
| research/oai_434/VF919OriginalLowTupleSignedGram.lean | c1b7b46a9e62a5b2f3729618c4dd24e31558166f |

Original OAI pin: **1581d4cbdd69a0faf34b2089614fe2a814316a6a**. Fetched `lean/OAI/NumberTheory/DirichletL/Detector/LowSlotPolynomial.lean`, blob b1dcb5a1e51afad1d39ccd91fa58a764e39629ba, and `LowTupleGram.lean`, blob 710598c8bef4d1a1ec98aa7e68b00369962c3d17. Their actual coefficients, integral normalizer, exact tuple identity, and subsequent `norm_sum_le` were read.

**Live PR/CI evidence.** No open/draft PR was returned. #1083 is human-merged, head 1ae84e2ff019b266114c100f43016eeec71144a9; #1084, #1082, #1081 and #1079 are merged; #1080 is closed unmerged. Fourteen returned checks associated with #1083's final head succeeded. The actual [dedicated job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41744927180/job/126295407267) tested synthetic merge **06cac0b95a56fdef0f61294e257e67ee2146c32c**, not a bare-head checkout. Its signed-Gram file, PR-head file, and current-main file were fetched and agree at blob c1b7b46a9e62a5b2f3729618c4dd24e31558166f. The three `actual_low_*` terminal declarations print only `propext`, `Classical.choice`, `Quot.sound`; the same log prints those axioms for `nativeReplay_mertens_growth`. Warning-fatal target compilation and terminal checks are recorded. Preexisting prerequisite warnings and reused build caches do not justify describing the entire imported tree as a new hole-free cold build.

This is reused structural/baseline proof evidence, not Lean evidence for P1-P3. No local Lean or new CI run was performed. Existing independently reviewed strict-slot endpoint credit is inherited at its actual scope; **additional signed-LOW/NYMAN gain remains SEARCH_BROAD, with net endpoint gain UNKNOWN**. Close-out refresh at 01:29 EST reconfirmed the same main SHA, an empty open-PR collection, and only today's Owner plus this own checkpoint in the dated report directory.

### C. Analytic Mechanism Investigated

The resumed question is precisely Coordinator `20261103-coordinator-2` C33-C35 and Referee `20261103-referee-6/7` NR1-NR6. Keeping c_k=-mu(k)log(N/k)/log N on a growing low interval leaves an optimized prime-power variance, and its exponent is not improved merely by changing high coefficients. The November 2 exact-head family, on the other hand, had no adequately small tail under the absolute coefficient certificate.

Two moves were compared. Retaining the old low coefficients and changing only the head slope repeats the already understood obstruction, so it was not pursued. The developed move is the **difference of two logarithmic coefficient families**, followed by two distributed moment corrections. It changes the low coefficients to their forced exact-interpolation values -mu(k), while retaining enough taper near N to use the accepted signed covariance tail bound. This is a coefficient construction within the same admissible basis, not a change of the target or Hilbert weights.

The logarithmic taper, two-moment linear algebra, and Fourier large sieve are standard/reused ingredients. The contribution relative to the retrieved handoffs is their combination with a polynomial exact head, explicit transition-layer estimate, complete returned numerator, and fully quantified failed middle-range bound. No new general arithmetic cancellation or external-literature novelty is asserted.

### D. Exact Mathematical Formulation

All sums below use the genuine Mobius function and real coefficients. Let N=6K with integer K>=1, and choose integer 2<=H<=N/2. Put

```text
ell=log(N/H)>0,
a_k(m)=(m mod k)/k,             alpha_k=(k-1)/(2k),
r_(N,H)(m)=1-sum_(2<=k<=N)c_k a_k(m),
D_N(c)^2=sum_(m>=1) r_(N,H)(m)^2/[m(m+1)].

q_k=log(N/max(H,k))             (1<=k<=N),
c_k^flat=-mu(k) q_k/ell         (2<=k<=N),
u=sum_(k<=N)mu(k)q_k/k,
v=2ell+sum_(k<=N)mu(k)q_k.

I_1={3K+1,...,4K}, I_2={5K+1,...,6K},
s_i=sum_(k in I_i)1/k,
A=(u-s_2 v/K)/(s_1-s_2),
Z=(s_1 v/K-u)/(s_1-s_2),
h_k=A 1_(I_1)(k)+Z 1_(I_2)(k),
c_k=c_k^flat+h_k/ell.                              (P4)
```

The symbol Z in this section is a real coefficient, NOT the OAI asymptotic scale. Since s_1>=1/4, s_2<1/5, the denominator exceeds 1/20. These coefficients are fixed from N,H and mu before any test coordinate m is chosen. All moduli 2 through N remain admissible, including squareful directions and modulus six.

For every integer B>=2 and m>=1 define the signed omitted-modulus sum

```text
U_B(m)=sum_(B<k<=m)mu(k)log(B/k) floor(m/k),
F_i(m)=sum_(k in I_i)floor(m/k).
```

Empty sums are zero, and log(B/k) is NEGATIVE on its actual support. The complete formula is

```text
ell*r_(N,H)(m)=U_N(m)-U_H(m)+A F_1(m)+Z F_2(m)       (all m>=1).
                                                               (P5)
```

Constants in the exact formulas and boundary-layer estimate are absolute. For the quantitative remote/middle estimates, fix b,C with 0<b<1, C>=1 and |M(x)|<=C x^b for all real x>=1. The hypothesis is independent of the desired norm decay and already available at b=15/16 from the inspected source. Define

```text
K_b=(2-b)/(1-b)^2,
B_(b,C)=C*(20 K_b+40/b),
Delta=max(|A|,|Z|)/ell.
```

The explicit coefficient and tail bounds are

```text
Delta <= B_(b,C) H^(b-1)/ell + 80/N,
sum_(m>ceil(N^(3/2))) r_(N,H)(m)^2/[m(m+1)]
 <= 14/(3ell^2)+(5/3)Delta^2.                       (P6)
```

P6's second inequality holds without the prefix hypothesis when Delta is left as its actual defined value. The first inequality is what independently makes it uniformly small for polynomial H. Constants are independent of N,H,m; theta enters only after H=floor(N^theta) is imposed. No fixed-parameter bound is silently extended to growing H.

### E. Mathematical Derivation

#### E1. Two Exact Moments And Full Return

The definitions solve

```text
sum h_k/k=u,        sum h_k=v.
```

Using q_1=ell gives

```text
sum_(2<=k<=N)c_k/k=1,
sum_(2<=k<=N)c_k alpha_k=1.                         (P7)
```

The first moment fixes the initial slope; the second removes the periodic constant residual. Neither can be omitted. On k<=H both correction bands are absent and q_k=ell, hence c_k=-mu(k).

For B>=2, let B_B=sum_(k<=B)mu(k)log(B/k)/k. The elementary convolution identities

```text
sum_(k<=m)mu(k)floor(m/k)=1,
sum_(k<=m)mu(k)log(k)floor(m/k)=-psi(m)
```

give the base logarithmic residual numerator m B_B-psi(m)+U_B(m). Subtract the H version from the N version. Their -psi(m) terms cancel exactly, and B_N-B_H=u. Subtracting the correction sum h_k a_k(m)=m u-A F_1(m)-Z F_2(m) then proves P5. There is no omitted principal term or boundary convention change.

For m<=H, all four terms in P5 vanish. This proves the exact head in P1, independently of any analytic estimate. For every fixed N,H the residual is a finite bounded periodic function, so the defining infinite Hilbert series converges absolutely. All reindexings used here are finite.

#### E2. The Correction Is Uniformly Affordable In The Remote Covariance

Write A_mu(t)=sum_(k<=t)mu(k)/k. The displayed sublinear prefix hypothesis gives convergence at s=1 and

```text
sum_(k>=1)mu(k)/k=0,
A_mu(t)=M(t)/t-integral_(t..infinity)M(x)x^(-2) dx,
|A_mu(t)|<=C*(2-b)/(1-b)*t^(b-1).
```

The value zero follows by Abel continuation of the reciprocal-zeta identity from Re(s)>1 to s=1, where zeta has its simple pole; the sublinear hypothesis justifies convergence and the limit. No RH assumption is used. Equivalently this reuses the justified s=1 identity in yesterday's Analytic N9, not a new reciprocal-zeta theorem.

Finite integration of the exact weights gives

```text
u=integral_H^N A_mu(t) dt/t,
v-2ell=integral_H^N M(t) dt/t.
```

Consequently

```text
|u|<=C K_b H^(b-1),
|v|<=2ell+C N^b/b.
```

The bounds s_1<1/3, s_2<1/5 and s_1-s_2>1/20 imply

```text
max(|A|,|Z|)<=20|u|+40|v|/N.
```

Since N^(b-1)<=H^(b-1), division by ell proves the first inequality of P6. This explicitly charges the growing head's reciprocal moment and the whole constant-mode correction.

Reuse the accepted covariance/tail interface from [`20261103-analytic-1` N4-N6](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-11-03/20-analytic-type-ii.md), accepted with scope by [`20261103-referee-5`](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-11-03/50-adversarial-referee.md):

```text
V_N(w)=(1/12)sum_(j,k=2..N)w_j w_k (gcd(j,k)^2-1)/(jk),
Tail_T(sum w_k(a_k-alpha_k))
 <= V_N(w)*[1/(T+1)+N^2/((T+1)(T+2))].              (REUSED)
```

It is valid for all real coefficient vectors, integer T>=0, and growing N. Equal rational Fourier frequencies are combined before using spacing N^(-2); it is not a diagonal-only covariance bound. Its external supplier is the dual finite large sieve with absolute constant, interval length J and separation delta, giving (J+delta^(-1)) times the combined Fourier coefficient energy. See [Montgomery and Vaughan, Theorem 19.4 and duality](https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf). The accepted exact Abel weights give the displayed tail; no new reproof of that theorem or repeat of its completed covariance census is claimed.

Here |c_k^flat|<=log(N/k)/ell, so the SAME proved majorant calculation, with its actual changed denominator, gives

```text
V_N(c^flat)<=7N/(6ell^2),
V_N(h/ell)<=5N Delta^2/12,
V_N(c)<=2V_N(c^flat)+2V_N(h/ell)
       <=7N/(3ell^2)+(5N/6)Delta^2.
```

The factor two pays the mixed term explicitly. By P7 the residual has zero periodic mean. At T=ceil(N^(3/2)), the tail bracket is at most 2/N, giving P6. For H=floor(N^theta), eventually H>=N^theta/2 and ell>=(1-theta)log N; hence P6 is O_(b,C,theta)(log(N)^(-2)). This is an estimate for the actual corrected vector, not for a discarded correction.

#### E3. A Paid First-Return Layer

For H<m<=min(2H,N/2), F_1=F_2=U_N=0 and every relevant floor is one. Thus

```text
ell*r_(N,H)(m)=sum_(H<k<=m)mu(k)log(k/H).             (P8)
```

Let m=H+j, 1<=j<=min(H,N/2-H). Using only |mu(k)|<=1 and log(1+x)<=x yields

```text
|r_(N,H)(H+j)|<=j(j+1)/(2H ell).
```

For integer 1<=t<=min(H,N/2-H), retain the exact original Hilbert weights:

```text
sum_(H<m<=H+t)r_(N,H)(m)^2/[m(m+1)]
 <= t(t+1)(t+2)(3t^2+6t+1)/(60 H^4 ell^2)
 <= t^5/(H^4 ell^2).                               (P9)
```

The first numerator is the exact sum of j^2(j+1)^2, divided by four. The final inequality follows from t+1<=2t, t+2<=3t and 3t^2+6t+1<=10t^2. For fixed theta<1, eventually 2H<=N/2. Taking t=floor(H^(4/5)) proves P2. This is a genuine bound on part of the old unpaid middle, but it is only a sublinear-width transition layer, not a linear-sized annulus or the full middle.

#### E4. The Large Middle Attempt And Its Actual Loss

For H<m<=N/2, P5 gives

```text
ell*r_(N,H)(m)
 =sum_(H<k<=m)mu(k)log(k/H)floor(m/k)
 =sum_(1<=j<=m/H)L_H(m/j),
L_H(y)=sum_(H<k<=y)mu(k)log(k/H).
```

The endpoint term at k=H is exactly zero, so Abel summation gives

```text
L_H(y)=M(y)log(y/H)-integral_H^y M(t)dt/t,
|L_H(y)|<=C[y^b log(y/H)+(y^b-H^b)/b].
```

This bound is uniform for y>=H, not just fixed y/H. Put Y=m/H. Decreasing positive integral comparison gives

```text
sum_(j<=Y)j^(-b)log(Y/j)<=Y^(1-b)/(1-b)^2,
sum_(j<=Y)(j^(-b)-Y^(-b))<=b Y^(1-b)/(1-b).
```

Therefore

```text
|r_(N,H)(m)|<=C K_b m H^(b-1)/ell.
```

Squaring with the unchanged weight and summing at most N/2 terms proves P3. At fixed theta and b>=1/2, 1-2theta(1-b)>0. Even taking theta close to one only approaches 2b-1, not a negative exponent. No manipulation of the logarithmic factor cures this polynomial deficit. This is the strongest result of THIS pointwise-prefix attempt; genuine cross-j cancellation or another new estimate would be required. It does not establish that the actual signed residual grows.

### F. Quantitative Comparison

| Contribution | Established bound | Scope/limitation |
| --- | --- | --- |
| 1<=m<=H=floor(N^theta) | Exactly zero | All original coordinates; low coefficients deliberately changed |
| H<m<=H+floor(H^(4/5)) | <=ell^(-2) | Elementary genuine-coefficient bound; no prefix theorem |
| m>ceil(N^(3/2)) | <=14/(3ell^2)+(5/3)Delta^2=O(log(N)^(-2)) | Full centered covariance and actual correction |
| H<m<=N/2 | <=C^2 K_b^2 N H^(2b-2)/(2ell^2) | Correct but nondecaying upper certificate at available b |
| Remaining middle through ceil(N^(3/2)) | No o(1) bound proved | Both floor corrections and U_N must remain |
| Canonical VF/RH/new exponent | No improvement | Net new endpoint gain UNKNOWN |

Compared with the November 2 one-point exact-head completion, the prefix-based first-middle upper certificate gains ell^(-2), while the signed tail method now pays the true infinite remainder at the stated cutoff. Compared with C34-C35, the new head is exact and polynomial-sized rather than a controlled logarithmic window. These are comparisons of proved certificates/constructions, not pointwise superiority of actual norms. Theta is fixed strictly below one; no uniform theta->1 claim is made.

The cofinal subsequence N=6K is a deliberately specified family of admissible approximants, not an exceptional arithmetic subsequence used to infer a bound for all prime endpoints. For the density consumer, convergence along this family would suffice; it is not established.

### G. Original-Carrier Bridge And Complete Return

The original [registered NYMAN source](https://github.com/OVVO-Financial/RH_Lean/blob/040980c16901af749202e9b0f91211c43909404a/research/NYMAN_BEURLING_POSITIVE_RESIDUE_ATTACK_2026_10_15.md) identifies a_k with the centered integer-dilation basis on 1/(m+1)<x<=1/m and its exact weight 1/[m(m+1)]. No basis, norm, or target is replaced here. Coefficients may be real and signed; the final construction meets that original admissibility.

With t=floor(H^(4/5)) and T=ceil(N^(3/2)), the complete source is

```text
D_N(c)^2 = 0 + transition_(N,H) + middle_(N,H) + tail_(N,H),
middle_(N,H)=(1/ell^2)sum_(H+t<m<=T)
 [U_N(m)-U_H(m)+A F_1(m)+Z F_2(m)]^2/[m(m+1)].       (P10)
```

Transition and tail tend to zero at the proved rate. The four terms remain jointly inside the middle square, including all six mixed interactions. No separate smallness of large complementary terms is imposed as a necessary condition. Given the paid pieces, middle_(N,H)->0 is equivalent to convergence of THIS particular family; it is a sufficient RH-strength supplier under the classical integer-dilation criterion, not an independently solved or known weaker lemma. No converse from RH to this family's convergence is asserted.

The classical logarithmic approximant is not a source of an unconditional full-norm estimate: [Bettin-Conrey-Farmer, Theorem 1](https://arxiv.org/pdf/1211.5191) assumes RH and an additional bound on reciprocal squared zeta derivatives at zeros. It concerns its own family, not P4. That conditional theorem is not used. The accepted Burnol logarithmic lower obstruction and omit-six safeguard remain in force; an O(log(N)^(-2)) REMOTE tail does not assert such a rate for D_N(c)^2.

**Bounded OAI source-first comparison, not a second claimed primary investigation.** The literal `actualUnselectedLowAtom` matches original LowSlotPolynomial, and LowTupleGram applies `norm_sum_le` immediately after that exact equality. At J=empty there is one outer tuple, its product norm and weight are one, and its outer ordered off-diagonal is zero. Hence changing only cross-unselected-tuple pairing cannot create a strict saving on that packet. This is the already established Referee R10 boundary, rechecked against the actual source, not a new no-go theorem or a nonzero-integral claim.

Reuse Referee R9/R10 and Lean's separate paper qualification ONLY at their original untilted, fixed-data scope: nonempty subsets have their moving-mass gain; the all-selected packet remains open. The first queued supplier is the genuine all-selected inverse-row energy at 5/6-nu+epsilon rather than 5/6+epsilon. Squaring/amplitude/return ledger: a fixed nu at that squared energy yields at most nu/2 after sqrt(Q); the Gaussian baseline is 3/16, the original signal is beta-11/16, and nonempty-subset control caps a complete original LOW gain at min(nu/2,ell_*). Principal/HIGH/remote and any shifted geometry still require their actual return checks before a new endpoint is credited. Marked-HIGH t/2 is not a LOW gain. No such nu, actual positive integral witness, or native-Mobius-to-Hecke bridge is supplied by this NYMAN work.

### H. Falsification, Continuity And Circularity Review

**Three genuine omission witnesses.** At N=12,H=2, P5 gives

```text
ell*r(3)=log(2)-log(3) !=0,       ell=log 6.
U_12(13)=log(13)-log(12)>0.
```

Thus exact interpolation must not be extended past H by deleting -U_H, and U_N must not be dropped after m=N. At m=7 the first I_1 floor is one while the other band is absent; deleting that correction loses A. Here

```text
A=-(3872/865)log2+(1536/865)log3+(924/865)log5
  +(103/173)log7+(7/173)log11 !=0.
```

Its nonzero value follows by clearing rational denominators and unique prime factorization, not a floating sign test or assumed algebraic independence. These refute the shortcuts only, not P5 or density.

**NR6 is restored, not evaded by omission.** Relative to the old base c_k^0=-mu(k)log(N/k)/log N, the new low edit on k<=H is e_k=-mu(k)log(k)/log N. For 1<=m<=floor(H/2),

```text
g(m)=sum_(2<=k<=2m)e_k[floor(2m/k)-2floor(m/k)]
    =[psi(2m)-2psi(m)]/log N.
```

Thus its squared defect is exactly Kpsi(floor(H/2))/log(N)^2. It cancels the old annihilator term while r(m)=r(2m)=0. We do NOT claim this defect is bounded. This explains why P1 does not contradict NR4/NR6 or the fixed-low zero obstruction. The correction is inside the actual source throughout.

**Preregistered and executed checks.** Development (N,H)=(12,2),(24,4),(48,6),(96,9); held-out (60,7),(120,10),(198,14); additional high-head boundary (36,12). They were fixed before execution. All m=1,...,2N+1 were checked, including H, 2H where admissible, N/2, N/2+1, N, N+1 and both correction-band activations. The verifier uses rational coefficients of formal prime logarithms; equality is coefficientwise, so it implies actual equality without an algebraic-independence hypothesis. Mobius values are independently checked by a prime-multiple sieve and trial factorization. No synthetic sequence substitutes for mu.

Executed results: 1,196 full residual checks; 1,196 independent mu checks; 32 moment checks; 56 low-coefficient checks; 64 exact head checks; 58 first-return checks; 31 NR6 restorations; 1,224 rational boundary-majorant checks; and the three omission witnesses. All PASS. `python -m py_compile` also passed. No numerical infinite-tail evaluation or asymptotic extrapolation was performed. The complete verifier is appended; SHA256 **a08144537fbe52ecb74187b9ebfd4a462f36f917e653efcf5ed288e2223e3949**. The accepted covariance census was deliberately not rerun.

**Continuity consumed, not invented.** November 3 latest relevant sections and November 4 Owner were read from retrieved bytes; prior claim IDs are preserved. Today's other upstream stages are TODAY=PENDING with YESTERDAY=CARRY_FORWARD. No missing report is presumed complete.

| Role/report | Retrieved blob | Relevant consumption |
| --- | --- | --- |
| Nov 3 Coordinator 00/90 | e35ab2cd9cba2a47ac5be53b09938b37a0c20df3 | C33-C35; latest protected NYMAN/SF-I assignment and OAI support-count limitation |
| Nov 3 Owner | d52c74b76c2914c3be694f39cd7afe9b122a4834 | owner-3 adjacent-excursion falsifier; history remains |
| Nov 3 Analytic | 2b9c3dbab6039e3c30a5ece3e473290af5dbbf0b | accepted N4 tail; OAI-NNS and CODIV rotation; CD logarithmic gain not a power gain |
| Nov 3 Wheel | cd7777180bb5c2c899a60bdd699b99be8e12a672 | O1-O4 genuine norm coherence, MU-LIFT complement remains |
| Nov 3 Census | eb9a2e0cf7772f22060aec07e0bcddd24ace9cd9 | census-5/6 exact cycle counts, not certified OAI integrals |
| Nov 3 Referee | 583ce524628577818603ffd4e9ec0eb3673a3f37 | referee-5 tail acceptance; NR6 defect; R9/R10 untilted scope |
| Nov 3 Lean | fc27fb1ae103e60ff600e5a24ce6716937da3884 | R9/R10 independent paper qualification; draft uncompiled/write-blocked |
| Nov 4 Owner | 546f46832e12fdf80d32713d26978e63e1d7b7d5 | owner-1 proper-band 11/6 bound, self-audit; no full-return inference |
| External inbox | 038018145c0fddb2f6306c0712373adf9cd1ea52 | No entry after Oct 18; source-return safeguards retained, dated routing superseded |
| Nov 2 Analytic, narrow novelty check | 8e48b59611aa1d0bfa3577ed0a4a3bc0d0fcae73 | Exact-head rigidity and one-point tail/middle loss reused, not rediscovered |

Scoped novelty search included the actual main tree/NYMAN route index, registered source, those prior derivations and current C33-C35/NR6. No compiled version of this construction or a full middle estimate was located. The new work is elementary research synthesis, not an exhaustive priority claim. The external log-derivative theorem is not used to assume the desired result. Author self-audit is not independent Referee acceptance.

### I. Conceptual Interpretation

The previous fixed-low prime-power obstruction is not an unavoidable constraint on every legal full-basis construction: actual low coefficients can change, with their exact floor-defect carrying the required cancellation. A logarithmic difference implements that change without destroying the affordable remote covariance. This makes a new explicit candidate available, while leaving its arithmetic difficulty visible in U_N-U_H and the distributed return.

The meaningful negative conclusion is equally important: an available sublinear prefix bound does not make the new middle estimate decay by this argument. The next attack must use signed correlations in the completed returned numerator, not repeat the head/tail calculation, optimize a known slope, or declare the large upper certificate an actual counterexample. No campaign narrowing is proposed.

### J. Specialist Handoffs

| Recipient | Precise request and limitation |
| --- | --- |
| Coordinator | Register P1/P2/P4-P7 as source-faithful paper supporting results and P3 as a quantified unsuccessful middle method. Preserve the existing original LOW all-selected ticket and protected rotation; no new eta credit. |
| Referee | Independently audit the two moment constraints, every-m P5 identity, uniform u/v bound, actual-vector covariance/tail transfer, and P9 polynomial constant. Check NR6 restoration before treating the polynomial exact head as a contradiction. New claim remains unaccepted until your review. |
| Census | If this candidate is selected, independently test the full finite core against C34's family at frozen (N,H)=(240,15),(384,19),(600,24), including both floor returns and U_N. Report head/transition/middle separately and a certified tail upper bound; no fitted asymptotic or dropped correction. No need to enlarge the completed bookkeeping census. |
| Wheel | No new original-owner/ideal identification is claimed. A useful NYMAN support question would be an exact signed divisor-pair grouping of the complete numerator, preserving both cutoffs and both correction bands; it must not displace your due CORR4 work. |
| Owner | Your Nov 4 band estimate remains a different carrier and a self-audited supporting result. No transfer from it to P10 or to Hecke phases is assumed or requested without an actual coefficient/weight map. |
| Lean | No new proof branch requested for these unreviewed findings. Keep the qualified moving-mass task and prior C29 reserve at their real implementation status. After independent acceptance, P7/P5 are finite identities; P6 still needs the actual accepted large-sieve supplier, not an unproved project axiom. |

These handoffs are published only in this owned report. No agent was launched and no other report, issue, proof source, branch, workflow, schedule or permission was modified.

### K. First Independently Missing Analytic Theorem

For a fixed 0<theta<1, H=floor(N^theta), t=floor(H^(4/5)), and the EXACT P4 coefficients, the required unproved estimate is

```text
sum_(H+t<m<=ceil(N^(3/2)))
 [U_N(m)-U_H(m)+A F_1(m)+Z F_2(m)]^2/[m(m+1)]
 = o(log(N/H)^2)                                     (OPEN-P10)
```

as N runs through all sufficiently large multiples of six. This is explicitly a full-family convergence supplier, not called weaker than RH. P3 does not establish it. The first accessible subproblem is the ordinary signed correlation of the logarithmically weighted actual partial sums L_H(m/j), followed by their genuine correction-band/outer-cutoff return. A useful theorem would need a new estimate on that correlation, not OPEN-P10 as an assumption under a different name.

### L. Next-Run Resume Capsule

```text
RUN: 2026-11-04T01:04:01-05:00 SCHEDULED; RUN_ID_UNAVAILABLE
MAIN: 040980c16901af749202e9b0f91211c43909404a
ENGINE: 495fa9ee2067ccf5db9dc3c48ffaaadcd6485aa4
TASK: NEXT-ANALYTIC / protected NYMAN continuation after C33-C35 and NR6
CLAIM: 20261104-analytic-1, P1-P10
RESULT: exact polynomial head, O(log(N)^(-2)) remote tail, paid H^(4/5)
  transition; complete returned numerator; nondecaying pointwise middle bill
INDEPENDENT_INPUTS: genuine mu; |mu|<=1; existing fixed sublinear Mertens
  envelope; accepted combined-frequency covariance/tail theorem
REVIEW: SELF_AUDIT; independent Referee PENDING; NOT_FORMALIZED
LAST_JUSTIFIED: P3/P6/P9 and complete reconstruction P10
FIRST_OPEN: signed middle estimate OPEN-P10, with all four terms inside square
SCOPED_FALSIFIERS: N=12,H=2,m=3 / m=7 / m=13 return omissions
SOURCE_FIRST_VERSION: 2026-11-03
OAI_PIN: 1581d4cbdd69a0faf34b2089614fe2a814316a6a
PR1083: MERGED; head 1ae84e2ff019b266114c100f43016eeec71144a9
TESTED_MERGE: 06cac0b95a56fdef0f61294e257e67ee2146c32c
CI: 41744927180 / 126295407267; standard terminal axioms inspected
U_A_SOURCE: original LowSlotPolynomial; first outer sign loss LowTupleGram
J_EMPTY: singleton outer atom; cross outer Gram=0; all-selected row unpaid
OAI_ENERGY / SQRT_Q / GAUSSIAN: 5/6 baseline, nu->nu/2, LOW 3/16
OAI_COMPLETE_GAIN: at most min(nu/2,ell_*), IF original HIGH/principal return
NEW_NU / NET_LOW_GAIN / NEW_ENDPOINT_GAIN: UNKNOWN
ETA_GATE: inherited strict-slot evidence only; additional signed gain SEARCH_BROAD
ROUTE_COVERAGE: Nov 3 OAI-NNS analytic-2; CODIV analytic-3; this NYMAN turn
NEXT_DISTINCT_ROUTE: OAI-NNS, SF-I genuine all-selected inverse source
NEXT_NYMAN: attack P10 signed correlations; do not re-prove paid two ends
NEXT_CODIV: OPEN-CD5; Nov 3 logarithmic maximal result still review-pending
TODAY_OTHER_UPSTREAM: PENDING except Owner; prior-day reports CARRY_FORWARD
DEPLOYMENT_ACK: live policy consumed; actual P4-P9 derivation/tests performed;
  protected rotation legitimately supersedes an immediate primary OAI turn
CANONICAL_VF / RH / FULL_NYMAN_DECAY: OPEN
EARLY_PUBLICATION: 2da11ba6af7181df59f41026538055b1a2c860c3;
  exact readback 82ac9674f85362dc038f5ad58eb83874026dd0f1
FINAL_PUBLICATION: recorded only by subsequent commit/readback receipt
```

### Reproducibility Appendix

The following complete Python verifier was executed with exact rational arithmetic. The report quotes only its compact count summary; its full output additionally prints rational prime-log coefficients for all fixtures. Runtime compilation of Python is not Lean certification.

```python
"""Exact source bookkeeping for the preregistered two-scale Nyman family."""

from collections import Counter
from fractions import Fraction as F
import json


class Log:
    def __init__(self, terms=None):
        self.terms = {p: F(v) for p, v in (terms or {}).items() if v}

    def __add__(self, other):
        out = dict(self.terms)
        for p, v in other.terms.items():
            out[p] = out.get(p, F(0)) + v
        return Log(out)

    def __neg__(self):
        return Log({p: -v for p, v in self.terms.items()})

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, scalar):
        return Log({p: v * F(scalar) for p, v in self.terms.items()})

    __rmul__ = __mul__

    def __truediv__(self, scalar):
        return self * (1 / F(scalar))

    def __eq__(self, other):
        return self.terms == other.terms

    def serial(self):
        return {str(p): str(v) for p, v in sorted(self.terms.items())}


ZERO = Log()


def factors(n):
    ans = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            ans[p] = ans.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        ans[n] = ans.get(n, 0) + 1
    return ans


def logn(n):
    return Log(factors(n))


def mu_trial(n):
    ff = factors(n)
    return 0 if any(v > 1 for v in ff.values()) else (-1) ** len(ff)


def mobius_sieve(n):
    mu = [1] * (n + 1)
    prime = [True] * (n + 1)
    for p in range(2, n + 1):
        if prime[p]:
            for k in range(p, n + 1, p):
                prime[k] = False
                mu[k] *= -1
            for k in range(p * p, n + 1, p * p):
                mu[k] = 0
    return mu


def add_all(values):
    total = ZERO
    for x in values:
        total = total + x
    return total


def psi(m):
    return add_all(logn(p) * sum(1 for a in range(1, m.bit_length()) if p**a <= m)
                   for p in range(2, m + 1) if factors(p) == {p: 1})


def make_family(n, h, mu):
    k0 = n // 6
    i1 = list(range(3 * k0 + 1, 4 * k0 + 1))
    i2 = list(range(5 * k0 + 1, 6 * k0 + 1))
    s1, s2 = (sum((F(1, k) for k in ii), F(0)) for ii in (i1, i2))
    assert s1 - s2 > F(1, 20)
    ell = logn(n) - logn(h)
    q = {k: logn(n) - logn(max(h, k)) for k in range(1, n + 1)}
    u = add_all(q[k] * F(mu[k], k) for k in range(1, n + 1))
    v = 2 * ell + add_all(q[k] * mu[k] for k in range(1, n + 1))
    a = (u - v * (s2 / k0)) / (s1 - s2)
    z = (v * (s1 / k0) - u) / (s1 - s2)
    corr = {k: a if k in i1 else z if k in i2 else ZERO for k in range(2, n + 1)}
    coeff = {k: -mu[k] * q[k] + corr[k] for k in range(2, n + 1)}
    return ell, u, v, a, z, i1, i2, corr, coeff


def omitted(b, m, mu):
    return add_all(mu[k] * (m // k) * (logn(b) - logn(k))
                   for k in range(b + 1, m + 1))


counts = Counter()
fixtures = [(12, 2), (24, 4), (48, 6), (96, 9),
            (60, 7), (120, 10), (198, 14), (36, 12)]
records = []
for n, h in fixtures:
    mu = mobius_sieve(2 * n + 1)
    assert all(mu[k] == mu_trial(k) for k in range(1, 2 * n + 2))
    counts['independent_mu'] += 2 * n + 1
    ell, u, v, a, z, i1, i2, corr, coeff = make_family(n, h, mu)
    assert add_all(corr[k] / k for k in corr) == u
    assert add_all(corr.values()) == v
    assert add_all(coeff[k] / k for k in coeff) == ell
    assert add_all(coeff[k] * F(k - 1, 2 * k) for k in coeff) == ell
    counts['moments'] += 4
    for k in range(2, h + 1):
        assert coeff[k] == -mu[k] * ell
        counts['exact_low_coefficients'] += 1
    residual = {}
    for m in range(1, 2 * n + 2):
        direct = ell - add_all(coeff[k] * F(m % k, k) for k in coeff)
        returned = (omitted(n, m, mu) - omitted(h, m, mu)
                    + a * sum(m // k for k in i1)
                    + z * sum(m // k for k in i2))
        assert direct == returned
        residual[m] = direct
        counts['full_return'] += 1
        if m <= h:
            assert direct == ZERO
            counts['exact_head'] += 1
        if h < m <= min(2 * h, n // 2):
            assert direct == add_all(mu[k] * (logn(k) - logn(h))
                                    for k in range(h + 1, m + 1))
            counts['first_return'] += 1
    for m in range(1, h // 2 + 1):
        defect_times_log_n = add_all(-mu[k] * logn(k) * ((2 * m) // k - 2 * (m // k))
                                    for k in range(2, 2 * m + 1))
        assert defect_times_log_n == psi(2 * m) - 2 * psi(m)
        counts['NR6_restoration'] += 1
    for m in [n // 2, n // 2 + 1, n, n + 1, 2 * n + 1]:
        counts['boundary_points'] += 1
    records.append({'N': n, 'H': h, 'first_residual_numerator': residual[h + 1].serial(),
                    'A_numerator': a.serial(), 'Z_numerator': z.serial()})

# This is a rational majorant check, not an evaluation of logarithms.
for h in range(2, 50):
    for t in range(1, h + 1):
        actual_majorant = sum((F(j * j * (j + 1)**2, 4 * h * h * (h + j) * (h + j + 1))
                              for j in range(1, t + 1)), F(0))
        asserted_majorant = F(t * (t + 1) * (t + 2) * (3 * t * t + 6 * t + 1), 60 * h**4)
        assert actual_majorant <= asserted_majorant
        assert asserted_majorant <= F(t**5, h**4)
        counts['boundary_layer_majorant'] += 1

mu = mobius_sieve(25)
family = make_family(12, 2, mu)
ell, _, _, a, z, i1, i2, _, coeff = family
first = ell - add_all(coeff[k] * F(3 % k, k) for k in coeff)
assert first == logn(2) - logn(3)
assert omitted(12, 13, mu) == logn(13) - logn(12)
assert a != ZERO
counts['omission_falsifiers'] += 3
output = {'counts': dict(counts), 'fixtures': records,
          'first_return_falsifier': first.serial(),
          'outer_cutoff_falsifier': omitted(12, 13, mu).serial(),
          'status': 'PASS: exact algebra only, no infinite-norm numerical claim'}
print(json.dumps(output, indent=2, sort_keys=True))
```

Compact recorded execution summary:

```json
{
  "counts": {
    "NR6_restoration": 31,
    "boundary_layer_majorant": 1224,
    "boundary_points": 40,
    "exact_head": 64,
    "exact_low_coefficients": 56,
    "first_return": 58,
    "full_return": 1196,
    "independent_mu": 1196,
    "moments": 32,
    "omission_falsifiers": 3
  },
  "status": "PASS: exact algebra only, no infinite-norm numerical claim"
}
```

## Verified Publication Receipt - 2026-11-04 01:31 EST (-0500)

Execution/report status: **COMPLETED / PUBLISHED**. This is a report-publication status, not a claim that the mathematical objective is complete.

The full synthesis and complete verifier were committed at `7e93116814c679ca2a84effcb91da600c09daf2a`, content blob `001608b0c70f8c4c884fe99f35fa529ab3eabf56`. A subsequent `agent-reports` fetch matched every byte and the returned blob SHA. The commit's changed-file list was inspected and contains only this authorized daily report. This receipt records that verified prior commit; it does not preclaim verification of the receipt commit itself.

Main remains `040980c16901af749202e9b0f91211c43909404a`. New results retain **PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED** status. The complete middle estimate, full-basis density, canonical VF bound, and RH remain OPEN. No new endpoint exponent was established. Next distinct protected route: OAI-NNS / SF-I; next NYMAN question: the signed completed-middle correlation in OPEN-P10.

---

## Scheduled OAI-NNS Continuation Checkpoint - 2026-11-04 09:09 EST Invocation

**PARTIAL / IN_PROGRESS.** Actual trigger: scheduled 2026-11-04T09:09:01-05:00; RUN_ID_UNAVAILABLE. This is a new continuation of the existing dated report, preserving 20261104-analytic-1 and its publication history.

### A. Mathematical Question

Due protected route: OAI-NNS / SF-I. Resume the original all-selected inverse source after Referee 20261103-referee-9/10, Lean 20261103-lean-3 and Coordinator 20261104-coordinator-1/C41-C42. J denotes UNSELECTED slots, so J=empty has a singleton outer tuple. Outer pair cancellation cannot improve that packet. Investigate an actual coefficient/phase-sensitive restriction in the inverse row or its integrated return; do not repeat the ambient ideal-counting diagonal obstruction or borrow a canonical printed exponent.

### B. Live Authority And Continuity

Main: 040980c16901af749202e9b0f91211c43909404a. AGENTS blob b878d396c387a57bd0b5165fecf10d15ef3732cd; current proof contract 63f7553bf6e5f2a16e37808116c643dc0dcc50e1; source-first contract b6980c30e63bb8c9ddfc8d6fa86a2bb401707fa6. Original OAI pin: 1581d4cbdd69a0faf34b2089614fe2a814316a6a.

Retrieved all seven role reports for November 4 and November 3, plus external inbox 038018145c0fddb2f6306c0712373adf9cd1ea52. TODAY=AVAILABLE for every role, unlike the historical early-morning snapshot. Current Owner also contains 20261104-owner-2's squarefree depth-three ancestry-capacity falsifier. No other agent is launched or presumed to have performed unpublished work.

PR #1083 is MERGED, head 1ae84e2ff019b266114c100f43016eeec71144a9, merge=current main; open/draft PR collection is empty at intake. Retrieved dedicated job 126295407267 in run 41744927180, including actual signed-Gram terminal axiom output. Structural identities are not a new signed gain. The moving-mass implementation remains reported UNCOMPILED / BLOCKED_WRITE_ACCESS; its independently qualified paper argument is distinct.

### C. Attempt And Validation Plan

Read actual LowSelectedBound, LowNominalEnergy, LowPhysicalInverseBound, LowSlotPolynomial, LowTupleGram and the selected-row correction expansion at their pinned blobs. Track genuine Hecke phases, selected marks, every ray correction, row/norm support, sqrt(Q), Gaussian and principal/HIGH costs. Compare at most two source-specific moves, develop one, and test any resulting claim against empty/full slot cases, resonances and actual boundary conditions. A source-qualified partial bound or an exact missing arithmetic inequality will be reported honestly.

### D-L. Pending

Derivation, original-carrier transfer, quantitative ledger, self-audit, specialist handoffs and final capsule are IN_PROGRESS. No new nu, endpoint exponent, Lean theorem, independent review or RH conclusion is claimed. Additional signed-LOW gate: SEARCH_BROAD; net new endpoint gain UNKNOWN. Next protected route after this substantive OAI turn: CODIV. Publication status is established only by commit/readback.

---

## Scheduled Source-First Synthesis - 20261104-analytic-2

Invocation: **2026-11-04 09:09:01 EST**, America/New_York; scheduled; RUN_ID_UNAVAILABLE. Mathematical synthesis prepared from 09:32 EST. This continuation preserves the earlier NYMAN findings, claim IDs, and this invocation's verified early checkpoint.

### A. Most Important Analytic Development

**A new source-qualified support decomposition and an explicit cube-sharing bound, not a new LOW exponent gain.** In the literal all-selected OAI inverse row, divide the completed ideal `I B^3` by its selected squarefree ideal product `D`. Writing the resulting ideal as `E=E1 E2^2 C^3`, with squarefree coprime E1,E2, determines exactly which selected primes are forced or forbidden. A surviving term must have

```text
E2 | D,   gcd(D,E1)=1;
D=E2 D0,  I=E1 D0,  B=E2 C.                         (CF1)
```

This is an occurrence-preserving restriction from the actual squarefree Gauss coefficient. It does not replace the characters or inverse row by ideal counting. The selected height phases also combine exactly into the integer frequency `log(N(E) P_*/U)`.

For the actual part `B_cap` in which a selected prime divides the cube ideal B, the independently proved uniform estimate is

```text
|B_cap(sigma,m;U,t)|
 <= 24 C_gamma U (9/8)^(K-1)
      * sum_i J_i product_(j!=i) H_j,               (CF2)
H_i = sum_(P in T_i) |W_i(NP/P_i)| / NP,
J_i = sum_(P in T_i) |W_i(NP/P_i)| / (NP)^4.
```

All original characters, row masks, Gauss weights and tuple coefficients are retained in the definition of `B_cap`; absolute values enter only in the explicitly priced upper bound. Here K>=1 and `C_gamma=sum_chi |correctionCoeff chi|`. The bound is uniform in U>0, every real t, all original numerator rows, and all admitted finite slot pools.

This gives a genuine `P_min^(-3)` reduction of a **crude absolute envelope**, not of the established `Z^(5/6)` inverse energy. At the terminal scales that envelope is still too large. The required new squared-source saving is **NOT_ESTABLISHED**; new net LOW/endpoint gain is **UNKNOWN**; `ETA_GATE=SEARCH_BROAD`.

The attempted height-orthogonality shortcut also fails at its proposed scale. A fully proved mean-square estimate has resolution cost `O(N_max log N_max)`, while the exact source Gaussian recombination returns the smooth factor `G(N(E)/Z)`. On a central dyad it does not resolve neighboring cofactors. This is a limitation of a coefficient-blind argument, **not** a counterexample to cancellation in the genuine arithmetic row.

New claim IDs, all author-self-audited and not yet independently reviewed:

| Claim | Result | Evidence |
| --- | --- | --- |
| `20261104-analytic-2-CF1` | Exact ideal-cofactor support, unique squarefree/cube decomposition, forced-slot rule and integer height-frequency compression | STRUCTURAL_IDENTITY / PAPER_PROOF / SELF_AUDIT |
| `20261104-analytic-2-CF2` | Explicit all-row cube-sharing bound (CF2), with constants and moving-cutoff uniformity | PAPER_PROOF / SELF_AUDIT |
| `20261104-analytic-2-CF3` | Finite height mean-square bound, exact Gaussian return, and scoped obstruction to coefficient-blind short-height diagonalization | PAPER_PROOF / SELF_AUDIT; the return equality is structural |
| `20261104-analytic-2-TEST` | Exact finite factorization/Euler tests and floating-point phase/mean-square checks, scopes distinguished below | FINITE_COMPUTATION |

### B. Current Mathematical Objective And Evidence

Actual main remains **`040980c16901af749202e9b0f91211c43909404a`**. Live AGENTS blob **`b878d396c387a57bd0b5165fecf10d15ef3732cd`**; CURRENT_PROOF_CONTRACT blob **`63f7553bf6e5f2a16e37808116c643dc0dcc50e1`**. Original OAI pin: **`1581d4cbdd69a0faf34b2089614fe2a814316a6a`**. Live instructions, not old report routing or the dated attachment, govern.

The canonical target remains OPEN:

```text
VFCanonicalSquareVonKochStatement:
exists C>=0, forall natural R>=2,
  |vfCanonicalSquareDefect R| <= C R log R.
```

The original actual-prime defect and sole canonical sqrt-two phase are unchanged. The RH consumer retains its explicit `ClassicalVonKochRHCriterion` argument. No improved Mertens estimate, first-bad payment, finite A/C bound, or RH proof is claimed.

**Relevant formal evidence rechecked.** PR [1083](https://github.com/OVVO-Financial/RH_Lean/pull/1083) is merged, despite historical draft wording in the policy. Its head is `1ae84e2ff019b266114c100f43016eeec71144a9`; Actions [run 41744927180](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41744927180) is completed/success. Job `126295407267` actually checked synthetic merge **`06cac0b95a56fdef0f61294e257e67ee2146c32c`**, not the bare head. The original-tuple Gram file has the identical blob `c1b7b46a9e62a5b2f3729618c4dd24e31558166f` at that tested merge, PR head, and current main. Logs print only `[propext, Classical.choice, Quot.sound]` for `actual_low_tuple_polynomial_eq_sum_atoms`, `actual_low_tuple_polynomial_sq_eq_signed_gram`, and `actual_low_NNS_co_minus_div_eq_normSq`. These certify identities, not an off-diagonal sign or saving. Logs also contain prerequisite Wiener `sorry` warnings; this is not a claim that every imported declaration was newly cold-built or hole-free. No new CI or local Lean execution was performed.

Open/draft PR collection was empty at intake and the 09:30 EST refresh; main was unchanged. Historical attachment PR933 metadata, empty discussion, and five changed policy/research filenames were retrieved; it supplies no new analytic theorem or override.

**Continuity.** All seven same-day reports were available; no missing upstream work was invented. Relevant November 3 material is carried forward at its existing review scope. The full files were retrieved and applicable claims/proofs/resume sections read; this is not a fresh audit of every historical appendix.

| Report | November 3 intake blob | November 4 intake blob |
| --- | --- | --- |
| Coordinator 00 | `e35ab2cd9cba2a47ac5be53b09938b37a0c20df3` | `6f00c4e1055a03325e8c152d4bcb505e254b8ecc` |
| Owner 10 | `d52c74b76c2914c3be694f39cd7afe9b122a4834` | `bef2ab8cefd691a868d8f1acdfe696af41266d16` |
| Analytic 20 | `2b9c3dbab6039e3c30a5ece3e473290af5dbbf0b` | `a0b8ee1e2c50d6ba926bc948a8896e78982f895f` before this run's checkpoint |
| Wheel 30 | `cd7777180bb5c2c899a60bdd699b99be8e12a672` | `364e6a0a29f8513d5471352d563a49e9b933c2e3` |
| Census 40 | `eb9a2e0cf7772f22060aec07e0bcddd24ace9cd9` | `108303ebdf61dc64cacd16651521ea39468292a3` |
| Referee 50 | `583ce524628577818603ffd4e9ec0eb3673a3f37` | `dd02c8e7072b9390119da35a204924ddad721d06` |
| Lean 60 | `fc27fb1ae103e60ff600e5a24ce6716937da3884` | `4585dc42e267f62da5c13624f2a5a4494aa79c53` |

`EXTERNAL_HANDOFFS.md` blob `038018145c0fddb2f6306c0712373adf9cd1ea52` has no entry later than October 18. No new external handoff was supplied. The early IN_PROGRESS checkpoint was committed as `79f3f76cd941a2e5a08804ffe6f4cfa556b614a3`, blob `bb0e14e6dc097c581c7644f9a66aff5f9f1849b1`, and exactly re-fetched.

Carry-forward inputs: `20261103-referee-9/10` and Lean-3 qualify the moving nonempty-unselected mass and isolate the all-selected empty-J packet. The current Coordinator C41-C42 rejects borrowing canonical margin powers into the full terminal source. Current Wheel/Census/Referee ambient-mark covariance results concern their stated counting measure, not completed inverse energy. Today's Owner-2 squarefree depth-three capacity obstruction remains an actual-seat result, not a Mobius or Hecke counterexample. Today's Analytic-1 NYMAN taper retains its unresolved middle; it is not rerun here.

### C. Mechanism And Research Continuity

Protected route due: **OAI-NNS**, original source-first selected-inverse track SF-I. This is distinct from the earlier rational-Mobius daughter-pair investigation; there is no assumed Mobius-to-Hecke bridge. The rolling sequence ends `20261103-analytic-3 CODIV`, `20261104-analytic-1 NYMAN`, this `20261104-analytic-2 OAI-NNS`. **CODIV is next due.**

Resumed obstruction: nonempty unselected subsets have a verified paper moving-mass gain; for J empty there is one outer atom, L=1, mass=1 and no cross-unselected terms. The remaining place to find new cancellation is inside its genuine selected-inverse row or complete physical integral.

Attempt identity: `(original LowSelectedInverseRow at the pinned revision, fixed positive saving in all-selected energy, divisibility plus squarefree Gauss support plus actual height phase, first absent signed row-correlation estimate)`. This run examines one mechanism, its cube-sharing subpart, and its attempted height estimate. These are not three independent RH programs.

Why investigate it: the apparent selected denominators in the height phase disappear under actual ideal divisibility, while the squarefree column imposes stronger support than the ambient incidence count. These are independently checkable arithmetic restrictions. Their quantitative consequences are proved below without assuming the requested global output.

Novelty search: inspected current reports and source definitions, and searched current main for cofactor/selected/LOW counterparts. The existing unselected norm fibers, ambient cube-incidence kernel, source Gaussian inversion, and generic Fourier mean-value idea are not claimed new. The new contribution here is the explicit selected-cofactor support formula and its uniform cube-sharing bound and scale audit. Search results are navigation, not proof of exhaustive novelty.

### D. Exact Objects, Quantifiers And Source Hashes

Let O be the source Eisenstein ring, N its absolute ideal norm. Fix its actual eta, S, calibration, ray class sigma, numerator m, and finite disjoint supported prime-ideal pools T_i outside S. There are K>=1 slots. Each occurrence p selects one ideal from every T_i; let D_p be their squarefree product, q_i=N(p_i), P_i>0, and P_*=product P_i. Use the source's canonical generators, not arbitrary associates. J is the **unselected** set in the code; this section sets J empty.

Write `e_t(y)=exp(2*pi*i*t*y)`, as defined in original `FourierBridge.logPhase`. Define

```text
c_p = conjugate(HeckeFamily.elementCoeff eta(product canonical generators))
      * product_i W_i(q_i/P_i),
gamma_chi = correctionCoeff chi,
Psi_(sigma,m,chi) = rowTwist(physicalRayPeriodicBase eta S sigma chi)
                           calibration.generator 1 m,
A(x) = gaussianAnnulus x,
h_(sigma,m,chi)(I,B)
  = columnWeight Psi I / sqrt(NI) * cubeWeight Psi B.
```

The source supplies `|Psi(z)|<=1`, `|columnWeight Psi I/sqrt(NI)|<=1`, `|cubeWeight Psi B|<=1/NB`, and `|A|<=1` with support in `(1/2,2)`. Zero I,B contribute zero. For each U>0 and t real the literal all-selected row is

```text
B_r(U,t) = sum_(p,chi,I,B : D_p | I B^3)
 c_p gamma_chi h_r,chi(I,B) A(NI NB^3/U)
 * e_t(log(NI NB^3/U)) * e_(-t)(log(ND_p/P_*)).       (D1)
```

Here r=(sigma,m). The apparent infinite ideal sums have finite support: `NI NB^3<2U`, hence NB and NI are bounded, and pools/characters are finite. This justifies every regrouping, including complex weights, without conditional convergence or an interchange assumption. Original masks remain inside Psi and the Gauss coefficient; expanding the finite character sum does not delete it.

Let a_r(n;U) be the sum of the full coefficient `c_p gamma_chi h A` in (D1) over all its occurrences for which `N((I B^3)/D_p)=n`. Distinct ideals of the same norm, conjugate primes, all tuples, cube occurrences, and all characters are grouped **before** taking a norm. Then

```text
B_r(U,t) = sum_(n>=1) a_r(n;U) e_t(log(n P_*/U)).       (D2)
```

CF1 and CF2 allow arbitrary complex slot weights, with their magnitudes retained in H_i,J_i. The simplification E4 and the terminal power comparison additionally assume `|W_i(x)|<=1` for every i,x, exactly as in the original energy supplier. Gaussian recombination uses the original windows supported in a fixed positive compact interval, so their logarithmic support is bounded.

If `a P_i < q_i <= b P_i`, with fixed 0<a<=b, the support is contained in
`U/(2 b^K P_*) <= n <= 2U/(a^K P_*)`. Endpoint inclusion is a harmless enclosing bound; the original annulus endpoints are not changed. If the upper bound is below 1 the polynomial is zero. No primality density is used.

`B_cap` is (D1) restricted to `gcd(D_p,B)!=1`. Its complement `B_coprime` is defined by `gcd(D_p,B)=1`; their exact sum is B_r. This partition is NOT the same as E2 nontrivial.

Material main sources:

| File under main | Blob |
| --- | --- |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | `79030d70e8d3e0d08eef9bac53fef95c36eca2fb` |
| research/oai_434/VF919OriginalLowTupleSignedGram.lean | `c1b7b46a9e62a5b2f3729618c4dd24e31558166f` |
| research/oai_434/VF919OriginalGainComponentLedger.lean | `5e7cea836158fc819f37e71da5fe55c8a8dce44e` |
| research/oai_434/VF919NativeSevenEighthsReplay.lean | `111c933a7ca15647105ce6a4d0f3cbfc3cde81f4` |

Material OAI sources, all under `lean/OAI/NumberTheory/DirichletL/` at the pin above:

| File | Blob | Relevant declaration |
| --- | --- | --- |
| Detector/LowSlotPolynomial.lean | `b1dcb5a1e51afad1d39ccd91fa58a764e39629ba` | lowSelectedWeight; lowSelectedIdeal; compensation_tuple_low_polynomial |
| Detector/LowCompensation.lean | `d99716fc995533acc9a563582f1d313e8587890d` | lowMarkedInverseRow |
| Detector/LowSelectedSum.lean | `a54eb9ec6a5beb0db57ce9baa658718aab808af1` | lowSelectedInverseRow |
| Descent/Completion.lean | `17f1f38b6485d1960f07b9a622757d48db6680d1` | markedCompletedT |
| Arithmetic/IdealMobius.lean | `6c1098ed3f3018397fd965d6a250db7092e86de7` | squarefreeGaussCoefficient; columnWeight; cubeWeight; summand |
| Detector/LowRay.lean | `5873fb85610c3d3965ee3a979c4be13f1dcc1baa` | physicalRayPeriodicBase; uniform norm bound |
| Eisenstein/CompactEnergyFamilies.lean | `559d3a8e1e44cefe3b6f31ea120866470e5db6cd` | rowTwist |
| RowCompletion/PolynomialHeight.lean | `3a6f4e7903d2e832e562687bccf13a2fce551aed` | normTwistedSource |
| Mellin/LogProfiles.lean | `4ca0df6768674c87654fe3637be3851c8c6d12cc` | logPhase; coupled_log_separation |
| Detector/GaussianSlots.lean | `bf4e39205b30ae0e8a894b42b6aa4126aac26dbe` | gaussianFixedWindow_Vstar_twist |
| Detector/GaussianCoupled.lean | `570522241d9ec0d34f26a634c7b5784c332503e8` | gaussianJointDensity; joint inversion |
| Detector/GaussianTuple.lean | `1f807c48deb02d882551321f9e8b577262c456b0` | original tuple Gaussian recombination |
| Eisenstein/SourceMellinInversion.lean | `7830dfe17fd39e4b462832d6ff6a2fa786b37080` | columnWeight_div_sqrt_norm_le_one |
| CubicSieve/LogSeparation.lean | `230dfdef039432a45e6eb6cce2ced96fe02498ae` | cubeWeight_norm_le |
| Detector/LowSelectedBound.lean | `695d81de46038693b9c701d55e81fe43d18d52d2` | original selected-inverse energy supplier |
| Detector/LowTupleGram.lean | `710598c8bef4d1a1ec98aa7e68b00369962c3d17` | compensation_tuple_actual_gram |
| Detector/LowGramIntegrated.lean | `35ee3fb09e7c04f554c4bdf0b0250132859ca2ec` | physical Gram and Mellin integration |

Additional source trail read: LowNominalEnergy `55b1a3abfb7fa07da3f9ac8c393b375d1c86329b`, LowPhysicalInverseBound `58bc871a18d9baa43d1684209027b8a2ebed87d6`, LowActualReflectedEnergy `015c046a5d4ccbf088ee627df75a5c80c7f561e6`, LowActualIdealLists `a29aae44a5e7880aa9c3b5a85a65fc3bb9945ee9`, LowSeparated `a6f7aab556b30edd188915bf227a5b140c4265f2`, LowGramApplied `6cedd2379fde8f28532b0833dfb4017381ecd54c`, and Reflection/LowOriginalEnergy `3b6c81973bd5ef24c9aa8a7403f8f71663bd1da8`. Direct links to the [pinned original source directory](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL) and [current main sources](https://github.com/OVVO-Financial/RH_Lean/tree/040980c16901af749202e9b0f91211c43909404a/research/oai_434) identify the immutable revisions rather than search-result default branches.

### E. Mathematical Derivation

#### CF1: Actual support and exact height compression

The squarefree Gauss coefficient vanishes unless I is squarefree and its primary generator is nonzero. For a nonzero surviving occurrence, unique ideal factorization permits a unique expression
`E=E1 E2^2 C^3`: for each prime ideal, assign its valuation modulo three to E1 or E2 and its quotient by three to C. E1,E2 are squarefree and coprime; **C need not be coprime to either**.

Since D is squarefree, at a prime with E-valuation congruent to 2, D must contain that prime to make the valuation of DE congruent to 0 or 1. At a prime with E-valuation congruent to 1, D must omit it. At residue 0 either choice is allowed. This proves `E2|D` and `gcd(D,E1)=1`. Conversely those conditions give `D=E2 D0`, with D0 coprime to E1 and E2, and
`DE=(E1 D0)(E2 C)^3` with E1 D0 squarefree. Such a representation as squarefree ideal times cube is unique, proving (CF1).

Consequently every prime of E2 forces its actual owning slot. If it lies outside all pools, or two such primes belong to the same slot, the fiber is empty. Otherwise the unforced slots may choose any of their actual primes not dividing E1. This is an exact support rule; remaining masks and complex coefficients can impose additional zeros. It is not a claim that every structurally admitted summand is nonzero.

Norm multiplicativity gives `NI NB^3 = ND * NE`. The two phases in (D1) therefore have combined argument
`log(NI NB^3/U)-log(ND/P_*)=log(NE P_*/U)`. All arguments are positive. This proves (D2) by finite grouping. No conjugate phase, Hecke coefficient, or same-norm cross term is removed.

#### CF2: Uniform cube-sharing bound

First an effective ideal-counting bound, requiring no prime theorem: the nonzero ideals of the Eisenstein PID are generated by lattice points with six associates. If `a^2-ab+b^2<=x`, then `|a|,|b|<=sqrt(2x)`. For x>=1, the number of nonzero generators is at most `8x+4sqrt(2x)`, hence the number of ideals is less than 3x after division by six. For 0<x<1 it is zero. Thus

```text
A_O(x) := #{nonzero ideals I : NI<=x} <= 3x  (x>0),
zeta_O(4) := sum_(B!=0) (NB)^(-4) <= 4.             (E1)
```

The second follows from the nonnegative layer-cake identity
`zeta_O(4)=4 integral_1^infinity A_O(x) x^(-5) dx`. All sums/products below converge absolutely; this is a fixed exponent 4, not a critical-line continuation.

Fix a squarefree selected D of K primes. For each B, let `F_B=D/gcd(D,B)`. Exactly `D|I B^3` iff `F_B|I`. Multiplication by F_B bijects ideals, so by (E1) the number of possible I under the upper support bound `NI NB^3<2U` is at most `6U/(NF_B (NB)^3)`. Drop squarefree/admission restrictions only in this positive majorant. The genuine coefficient norm is at most `1/NB`; hence its cube-sharing absolute sum is at most

```text
(6U/ND) * sum_(B : gcd(D,B)!=1) N(gcd(D,B))/(NB)^4.   (E2)
```

The convergent Euler product evaluates the remaining positive sum exactly as

```text
zeta_O(4) * [product_(P|D)(1+q^(-3)-q^(-4))
             - product_(P|D)(1-q^(-4))], q=NP.       (E3)
```

Indeed the local geometric series is `1+q sum_(v>=1)q^(-4v)`; division by the ordinary zeta local factor gives `1+q^(-3)-q^(-4)`. The coprime sector gives `1-q^(-4)`. Subtracting these products is a positive-sector partition, not subtraction of unknown complex energies.

For q>=2, put `a_q=1+q^(-3)-q^(-4)`, `b_q=1-q^(-4)`. Then `a_q-b_q=q^(-3)` and both are at most 9/8. Telescoping the products and using (E1) bounds (E3) by
`4(9/8)^(K-1) sum_(P|D)q^(-3)`. Insert this in (E2), sum the original tuple coefficient norms, and then the finite character norms C_gamma. Cartesian factorization yields exactly (CF2). This proves the displayed 24, all quantifiers, and independence of t,m,sigma.

For `P_i=Z^ell_i`, fixed ell_i>0 and common windows, `J_i<=(a P_i)^(-3)H_i`, and `H_i<=3b/a` by (E1). Therefore, uniformly for Z>=1,

```text
|B_cap| <= C_abs U Z^(-3 ell_min),
C_abs = 24 C_gamma (9/8)^(K-1) (3b/a)^K K a^(-3).   (E4)
```

No PNT, full-pool assumption, growing-conductor uniformity, or statistical independence is used. Empty pools give zero. K=0, outside the stated formula with K-1, has identically zero cube-sharing sector and is handled separately. The constant is explicit and can grow with K; K is fixed at the terminal application.

#### CF3: Height mean square and exact return

Let N>=1 be any integer enclosing the support in (D2), `E_r=sum_n|a_r(n;U)|^2`, and `H_0=0`, `H_j=sum_(k=1)^j 1/k`. For every real T0 and L>=0,

```text
| integral_(T0)^(T0+L) |B_r(U,t)|^2 dt - L E_r |
 <= (2N/pi) H_(N-1) E_r.                            (E5)
```

Proof: each distinct pair integrates with absolute value at most `1/(pi |log(n/k)|)`. Since `|log(n/k)|>=|n-k|/N`, its total is bounded by `(N/pi) sum_(n!=k)|a_n a_k|/|n-k|`. Apply `2|a_n a_k|<=|a_n|^2+|a_k|^2` only here, with its full stated price, and bound each harmonic row by `2H_(N-1)`. The diagonal is exactly L E_r. The proof works for sparse support, zero coefficients, and N=1. Summing (E5) over actual rows with any fixed nonnegative row weights gives the same constant and summed E_r. E_r includes all within-n interactions; no claim bounds it by an occurrence diagonal.

This generic estimate is not presented as a new mean-value theorem. The relevant original literature is Montgomery and Vaughan, [Hilbert's Inequality, JLMS 8 (1974), 73-82](https://doi.org/10.1112/jlms/s2-8.1.73), especially its almost-periodic/Dirichlet-polynomial mean-value discussion. A [primary-author copy](https://personal.science.psu.edu/rcv4/personal/Publications/s2-8-1-73.pdf) was consulted for this changed source question. No sharper imported constant or unverified growing-parameter statement is needed: (E5) is proved in full here.

The source uses a particular Fourier coefficient, not a free choice of averaging interval. Write `G(x)=(2sqrt(pi))^(-1) exp(-(log x)^2/4)` for x>0, and `R=U/(Z P_*)`. Its `gaussianJointDensity R` is the Fourier transform of `V(y) G(R exp y)`, where V is one on the actual active logarithmic support. Applying the original inversion to each finite coefficient gives exactly

```text
integral_t gaussianJointDensity(R,t) B_r(U,t) dt
   = sum_n a_r(n;U) G(n/Z).                         (E6)
```

The annulus A and all selected W_i are already inside a_r. Their active support makes V equal to one; it has not been dropped outside its theorem. For a central dyad with `U/(Z P_*)` bounded above and below by fixed positive constants, n/Z is in a fixed compact positive interval and G is bounded above and below by fixed positive constants there. This last assertion is **not** uniform over the larger `Z^(+/-epsilon/2)` central window with a fixed lower constant. No auxiliary height integration beyond the original one is introduced.

### F. Quantitative Comparison And Complete Power Ledger

Original untilted parameters: fixed positive terminal ell_i with sum 1/6; `P_*=Z^(1/6)`, `Q=q Z^(5/6)`, `X=Z^(17/48)`, `Y=Z^(23/48)`, and `U in [Z^(7/6-epsilon/2),Z^(7/6+epsilon/2)]`. Fix eta,S,geometry,windows before epsilon and Z. The source selected-inverse baseline is `Z^(5/6-2d+507epsilon)`; for J empty, d=0.

The requested independently new input is a fixed nu>0 saving in that original squared row energy, or a complete integrated original LOW bound with its own proof. E5 does not supply it: `N<=C Z^(1+epsilon/2)` and its resolution cost is `O(Z^(1+epsilon/2) log Z)`. It gives a diagonal comparison only for sufficiently long heights relative to that cost, not for the fixed-scale source Gaussian. E6 is the original return, not a power bound. The grouped energy E_r is itself still uncontrolled at the needed strength.

For the new cube-sharing envelope E4, the central upper scale gives amplitude
`O(Z^(7/6-3ell_min+epsilon/2))`. Counting actual numerator lattice elements supplies at most `O(Z^(5/6))` rows, with original fixed parameters absorbed in the constant. Consequently this argument gives only

```text
sum_m |B_cap|^2 << Z^(19/6-6ell_min+epsilon).         (F1)
```

Because `ell_min<=1/6`, this upper exponent is at least 13/6 before epsilon, much worse than the required 5/6 baseline. This is a statement that the **bound is inadequate**, not that the actual sector is that large. The local q^(-3) suppression cannot be credited as a saving relative to the original sharp inverse-moment estimate.

| Component | Retained accounting | New gain from this run |
| --- | --- | --- |
| Literal all-selected inverse energy | Baseline 5/6+507epsilon; need fixed nu before choosing epsilon | None proved |
| sqrt(Q) and inverse normalization | A valid squared-energy saving would contribute at most nu/2 in amplitude | No such input established |
| Physical Gaussian Gram | Original 3/16 normalized LOW amplitude, with stated epsilon losses | E6 gives no automatic gain |
| Nonempty unselected subsets | Carry-forward R9/R10: `3/16-d_J+lambda`, after choosing fixed small losses | Existing, not new |
| Empty-J physical tuple | One outer atom, unselected off-diagonal zero | Inner arithmetic still open |
| LOW/principal separation | `(beta-11/16)-3/16=beta-7/8` | New crossing not established |
| Physical slot tilt | Signal shift -8tau, LOW -9tau; one-off tau<=1/144 | No reuse or fresh credit |
| Marked HIGH improvement | Max across unchanged branches; discount at most `min(t/2,max(0,E_marked-E_other))` | No binding HIGH improvement asserted |
| Principal, remote, exceptional, Gaussian tails, final transfer | Retain original terms and hypotheses | No new all-return bound |

The exact cube partition restores its mixed term:
`|B_r|^2=|B_coprime|^2+2Re(B_coprime conjugate(B_cap))+|B_cap|^2`.
For future valid energy estimates, Minkowski bounds the square root of total energy by the sum of the two square roots, accounting for that interaction. The present F1 does not make this restoration affordable. Similarly, all J, Gaussian dyads, ray classes, and physical v-integrals remain in their original order with source normalizers; no independent factor can be multiplied into a published endpoint exponent.

### G. Original-Carrier Bridge

The bridge is literal: `lowSelectedWeight -> lowSelectedInverseRow -> lowMarkedInverseRow -> markedCompletedT -> summand`. Its Gaussian window identity is `gaussianFixedWindow_Vstar_twist`, and its height convention is the original `logPhase`, including the factor 2*pi. The ideal product D is not its rational norm; conjugate primes remain different ideals in divisibility and in E1,E2,C. Only after summing every occurrence at fixed **integer norm** is (D2) formed. Within that norm the phases and complex Gauss interactions are retained, not replaced by a positive multiplicity.

The source Gram in main still states
`|sum_a U_a|^2=sum_a |U_a|^2+sum_(a!=b)Re(U_a conjugate U_b)=Co-Div`.
The first explicit cross-unselected sign loss on the audited local trail is `LowTupleGram.compensation_tuple_actual_gram`'s `norm_sum_le` after the exact polynomial equality. For J empty that outer loss is equality. CF1-CF3 concern the inner inverse; they neither infer negativity from this outer identity nor silently transfer the ambient counting covariance theorem.

All additional bad-prime, period, row, and character zeros remain in (D1). Ignoring them in E2 is a valid positive upper bound with a quantified loss, not a replacement source. The full original physical `lowSeparatedIntegrand`, W0/W1, residue coefficients and `1/(2*pi*sqrt(Q))` normalization have not been bounded by a new theorem here.

### H. Falsification, Tests And Circularity

Three exact local stress cases distinguish the actual support from tempting simplifications, for any allowed prime ideal P:

```text
E=P,   D=P:   DE=P^2 has no squarefree-times-cube representation; zero.
E=P^2, D=P:   I=1, B=P is allowed by this support test.
E=P^3, D=P:   I=P, B=P is allowed; E2=1 yet cube overlap occurs.
```

Thus neither `gcd(D,E)=1` for the full row nor `E2=1 => no selected prime in B` is valid. These are support counterexamples, not assertions that a particular masked analytic coefficient is nonzero. For squarefree E and any admitted D coprime to E, the occurrences `I=DE,B=1` all have the same height frequency NE. Distinct selected tuples therefore need not give distinct frequencies, even on this legal arithmetic support. Actual row cancellation among those occurrences remains possible and unproved.

The coefficient-blind short-height proposal is refuted in its stated generic scope: taking arbitrary `a_n=1` for `Z<=n<=2Z` gives the E6 returned amplitude at least `c Z`, whereas the coefficient diagonal is O(Z). A uniform O(1)-multiple diagonal bound for that returned squared amplitude fails. These artificial coefficients are **not claimed realizable by the OAI Gauss rows**. They disprove inference from frequency geometry and Gaussian smoothing alone, not OPEN-E0 or RH. A two-neighbor check gives `G((N+1)/N)/G(1)` tending to 1, not a power loss.

Executed finite tests used distinct actual prime-ideal labels above 7 and 13 (both conjugates) and the inert ideal above 5, with norms `(7,7,13,13,25)`. This is an exact prime-ideal factor-vector test, not a computation of physical Gauss coefficients. Two disjoint slots choose indices `(0,2)` and `(1,3)`; all cofactor exponents 0 through 8 are checked independently against valuations of DE.

```text
valuation cases:                    236196
admissible squarefree/cube cases:     31104
of those with selected cube overlap: 30240
maximum sampled phase error:         1.4448263461195267e-14
exact rational Euler-sector tests:       9
generic finite mean-square tests:       64
largest error/proved-envelope ratio:  0.2083921266335674
synthetic neighbor Gaussian ratios:
N=10:   0.9977315691931588
N=100:  0.999975248035313
N=1000: 0.9999997502498023
```

The valuation and Euler assertions use integers/Fraction exactly. Phase and complex integration evaluations use double precision with declared checks; they are corroboration, not numerical certificates of the paper theorems. The latter follow from the proofs above. The complete reproducible script is embedded after section L; SHA256 `7ac8d2c21c2010e4ab1af3ddefdf85f2360f75094de99599573729ad7696a00c`. No large census was rerun, and no finite-to-infinite inference is made.

### I. Conceptual Interpretation And Disposition

The genuine inverse source has an arithmetic cofactor, not an arbitrary collection of unrelated logarithmic phases. Its squarefree Gauss column enforces a modulo-three support rule and unique squarefree/cube decomposition that an ambient divisibility count does not see. This provides an exact smaller object for a source-faithful Gauss/cubic-reciprocity investigation.

However, recovering the original Gaussian weight reveals why height integration is not a free cancellation mechanism. Within-n coherence survives every height; nearby n are unresolved on a central dyad. The cubic damping controls an absolute tail but does not substitute for the established row-moment technology. **Disposition: REVISE** toward the coprime selected-squarefree convolution and a quantitatively affordable cube-sharing supplier, not an assumed new norm bound. Keep the current all-return endpoint OPEN and protected broad-route rotation intact.

### J. Specialist Handoffs

| Recipient | Exact request and dependency | Review state |
| --- | --- | --- |
| Coordinator | Retain R9/R10 and this all-selected subsource split. Record CF2 as a weak supporting bound, not nu or VERIFIED_ETA. Use F1 to prevent crediting its q^(-3) against the sharp inverse-energy baseline. | New request; no acceptance inferred |
| Owner Payment | Check whether an actual arithmetic identification ever maps native coefficients to this ideal cofactor carrier. CF1 is not such a map; preserve actual owner signs and occurrence counts. | No bridge supplied |
| Finite Wheel | Independently review CF1 with C allowed to share primes with E1,E2, and derive the weighted forced-slot polynomial on the actual disjoint pools. Distinguish selected cube overlap from E2 nontrivial. | PAPER_PROOF / SELF_AUDIT awaiting review |
| Prime Census | If actual Gauss-row evaluation is available, compare B_coprime, B_cap, their mixed term, and the grouped a_r(n) energy on one fixed original eta/S/geometry. Test whether cube-sharing energy has a positive saving relative to 5/6, not merely a decaying share of our crude envelope. Declare all masks/rows/windows; absent implementation is PENDING. | Targeted experiment requested, not executed |
| Adversarial Referee | Audit CF1 and the constant 24 in CF2, especially `D|IB^3 iff D/gcd(D,B)|I`, the q^(-3) Euler difference, actual cubeWeight normalization, finite grouping, and E6's U/(ZP_*) scaling. Confirm F1 is inadequate and the synthetic no-go does not transfer to genuine rows. | No independent review yet |
| Lean Verification | Do not encode OPEN-CUBE below as an assumption and call it a proof. If CF1/CF2 receive independent acceptance and aid an active bound, assess existing unique-factorization and count interfaces before proposing formalization. Current accepted moving-mass work takes precedence; no second implementation task is assigned here. | All new claims uncompiled |

Handoffs are published requests in this own report only. No agent launch, other-report modification, issue, PR, branch, schedule, or permission change occurred.

### K. First Independently Missing Analytic Theorem

**OPEN-CUBE (candidate supporting theorem, NOT PROVED):** Fix the original eta,S,calibration, positive finite slot geometry ell with sum 1/6, and original admissible windows. Is there a fixed `nu_cap>0`, chosen before epsilon, such that for every epsilon>0 there are C,D,Z0, uniform over all original admissible slot pools, central U, actual numerator-row families of norm at most `C_k Z^(5/6)`, sigma and real t,

```text
sum_(m in actual numerator rows) |B_cap(sigma,m;U,t)|^2
 <= C (1+|t|)^D Z^(5/6-nu_cap+epsilon) ?             (K1)
```

The source hypotheses are those of the original selected-inverse supplier, not independence or RH. A plausible proof attempt would retain the actual `1/NB` cubic damping and the forced-prime incidence inside the source inverse-moment argument, rather than apply the crude I-count in E2. That quantitative transfer is the **first missing step**; it has not been established by this run or by the generic full-source bound, which cannot automatically bound a restricted complex subsum.

K1 is a proper subsource problem and alone does not prove OPEN-E0: the coprime core remains. On that core CF1 reduces exactly to `E2=1`, `gcd(D,E1 C)=1`, `I=D E1`, `B=C`. A new signed Gauss/cubic-reciprocity estimate on this core would still be required. If both source pieces had energy savings, Minkowski would preserve the smaller saving, then the physical consumer would halve it and pay every other return cost. Neither saving is supplied here.

For clarity the unchanged complete target is `sum_m |B_r|^2 << (1+|t|)^D Z^(5/6-nu+epsilon)`, or an independently proved complete physical-integral alternative. Rewriting it using a_r(n), a Gram, or Co-Div is not an independent theorem. No target-equivalent assertion is promoted by this report.

### L. Resume Capsule And Source-First Record

```text
ENGINE_VERSION: 2026-11-01, live source-first revision 2026-11-03
MAIN: 040980c16901af749202e9b0f91211c43909404a
POLICY_SHA: b6980c30e63bb8c9ddfc8d6fa86a2bb401707fa6
ENGINE_POLICY_SHA: 495fa9ee2067ccf5db9dc3c48ffaaadcd6485aa4
COMPLETE_RETURN_POLICY_SHA: 4775ee5fd95f279beab08a75d1e17127078b19a6
RUN_ID_OR_UNAVAILABLE: RUN_ID_UNAVAILABLE; actual invocation 2026-11-04 09:09:01 EST
TASK_ID / ROUTE: 20261104-analytic-2 / OAI-NNS, source-first SF-I
ORIGINAL_SOURCE_REVISION: openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a
TRIGGER: due protected route; R9/R10 isolated empty-J all-selected row
PROPOSED_CLAIM_AND_QUANTIFIERS: CF1-CF3, sections D/E; fixed original data,
  all admitted pools/rows/U/t; CF2 explicit K-dependent constant
WHY_IT_MATTERS: source squarefree/cube restriction and paid subsource envelope;
  no new terminal power saving
ESTABLISHED_INPUTS: original source definitions/hashes in D;
  inherited R9/R10 at reviewed paper scope; source Gram at tested SHA in B
CURRENT_DERIVATION / LAST_JUSTIFIED_STEP: CF1, E4, E5, E6 and exact mixed return
FIRST_UNSUPPORTED_STEP: OPEN-CUBE K1; separately new cancellation in coprime core
DISTINCT_ATTEMPTS / FAILURES: Gaussian height-only diagonalization has an
  unpaid cofactor-resolution scale; cube absolute envelope F1 is too weak
NEXT_DECISIVE_ACTION: on next OAI visit, inspect the restricted original
  inverse-moment proof for a legal cube-overlap gain; do not repeat this algebra
HANDOFF / REVIEW: section J; SELF_AUDIT only; no independent acceptance
ACTUAL_RESULT / FORMAL_STATE: PAPER_PROOF and finite tests; new claims UNCOMPILED
SOURCE_FIRST_VERSION: 2026-11-03
PR1083_LIVE_HEAD_STATE: merged; head 1ae84e2ff019b266114c100f43016eeec71144a9;
  relevant CI tested 06cac0b95a56fdef0f61294e257e67ee2146c32c; same Gram blob
ORIGINAL_DECLARATION / CHARACTER / J / MASK / ADMISSION:
  lowSelectedInverseRow, original eta, J empty, actual supported disjoint pools,
  all periodic/character masks retained in Psi; no growing-conductor claim
U_A_EXACT_SOURCE: main actualUnselectedLowAtom; one atom for J empty
SIGNED_U_A_DIAGONAL_AND_OFF: exact original Gram; empty-J outer Off=0
FIRST_SIGN_LOSS: LowTupleGram norm_sum_le after compensation_tuple_low_polynomial
NEW_ARITHMETIC_INPUT: ideal quotient plus actual squarefree Gauss support;
  selected-on-cube absolute norm count and convergent exponent-4 Euler product
LOW_INVERSE_ENERGY / SQRT_Q / GAUSSIAN: 5/6+507eps; square-root exchange nu/2;
  normalized Gaussian LOW 3/16; none improved by this run
NNS_CO_DIV_EQUALS_GRAM: retained, not a cancellation theorem
SOURCE_SQUARED_GAIN: NOT_ESTABLISHED
AMPLITUDE_GAIN: NOT_ESTABLISHED
NET_BETA_AFTER_HIGH / NET_ENDPOINT_GAIN: UNKNOWN
PRINCIPAL / HIGH / REMOTE / EXCEPTIONS / TAILS: retained, no new discount
ETA_GATE: SEARCH_BROAD, not VERIFIED_ETA
STRESS_TEST: 236196 exact valuation cases; 9 Euler tests; 64 Fourier tests;
  no actual Gauss-row simulation or all-scale numerical inference
STATUS / REVIEW / AXIOMS: research disposition REVISE; PAPER_PROOF / SELF_AUDIT;
  old Gram standard-axiom audit in B; no new Lean theorem or Actions execution
ROUTE_COVERAGE: Nov3 analytic-3 CODIV; Nov4 analytic-1 NYMAN; this OAI-NNS
PROTECTED_ROUTE_DUE: CODIV next; resume prior maximal-shell logarithmic result
  at its missing fixed-power input, without rerunning its accepted derivation
DEPLOYMENT_ACK: live policy consumed; actual new CF1-CF3 derivation and tests,
  not just an instruction receipt; no role/schedule/permission change
PUBLICATION: early checkpoint verified; synthesis commit/readback checked
  after this append, without preclaiming a successful write
FRESHNESS: latest same-day directory recheck found the six upstream report
  blobs unchanged from B and our checkpoint blob unchanged before publication
```

#### Reproducible Finite-Test Script

The following is the exact executed script. It has no repository writes and does not synthesize actual Gauss coefficients.

```python
"""Finite structural tests only; no Gauss coefficient or RH simulation."""

from fractions import Fraction as F
from itertools import product
from math import ceil, log, pi, sin, exp
import cmath
import json
import random


def norm(v):
    # Distinct conjugate ideals above 7 and 13, and the inert ideal above 5.
    return prod_int(q**e for q, e in zip((7, 7, 13, 13, 25), v))


def prod_int(xs):
    out = 1
    for x in xs:
        out *= x
    return out


ds = []
for p, q in product((0, 2), (1, 3)):
    d = [0] * 5
    d[p] = d[q] = 1
    ds.append(tuple(d))

checks = admissible = overlap = 0
phase_error = 0.0
for e in product(range(9), repeat=5):
    e1 = tuple(x % 3 == 1 for x in e)
    e2 = tuple(x % 3 == 2 for x in e)
    c = tuple(x // 3 for x in e)
    for d in ds:
        a = tuple(x + y for x, y in zip(e, d))
        direct = all(x % 3 != 2 for x in a)
        criterion = all(not y or x for x, y in zip(d, e2)) and all(
            not (x and y) for x, y in zip(d, e1)
        )
        assert direct == criterion
        checks += 1
        if not direct:
            continue
        admissible += 1
        i = tuple(x % 3 for x in a)
        b = tuple(x // 3 for x in a)
        assert i == tuple(int(x) + y - int(z) for x, y, z in zip(e1, d, e2))
        assert b == tuple(int(x) + y for x, y in zip(e2, c))
        assert norm(i) * norm(b)**3 == norm(d) * norm(e)
        overlap += any(x and y for x, y in zip(d, b))
        if admissible % 997 == 0:
            u, pstar, t = 317.0, 91.0, 0.271
            lhs = cmath.exp(2j*pi*t*log(norm(i)*norm(b)**3/u))
            lhs *= cmath.exp(-2j*pi*t*log(norm(d)/pstar))
            rhs = cmath.exp(2j*pi*t*log(norm(e)*pstar/u))
            phase_error = max(phase_error, abs(lhs-rhs))
assert phase_error < 1e-11

# Exact finite Euler sums, with local overlap sectors restored.
euler_checks = 0
for qs in ((7,), (7, 7), (7, 13, 25)):
    for cutoff in (1, 2, 4):
        direct = F(0)
        for v in product(range(cutoff + 1), repeat=len(qs)):
            if not any(v):
                continue
            direct += F(prod_int(q for q, x in zip(qs, v) if x),
                        prod_int(q**(4*x) for q, x in zip(qs, v)))
        local = prod_int(1 + sum((F(q, q**(4*x)) for x in range(1, cutoff+1)), F(0))
                         for q in qs) - 1
        assert direct == local
        zeta_local = prod_int(F(1, 1-F(1, q**4)) for q in qs)
        exact_limit = zeta_local * (
            prod_int(1 + F(1, q**3) - F(1, q**4) for q in qs)
            - prod_int(1 - F(1, q**4) for q in qs))
        bound = zeta_local * F(9, 8)**(len(qs)-1) * sum(F(1, q**3) for q in qs)
        assert direct <= exact_limit <= bound
        euler_checks += 1

rng = random.Random(20261104)
mean_checks = 0
max_relative_bound = 0.0
for nmax in (2, 7, 31, 100):
    harmonic = sum(1/j for j in range(1, nmax))
    for length in (0.1, 1.0, float(nmax), 10.0*nmax):
        for trial in range(4):
            ns = sorted(rng.sample(range(1, nmax+1), min(nmax, 12)))
            a = [complex(rng.randrange(-5, 6), rng.randrange(-5, 6)) for _ in ns]
            start = rng.uniform(-2, 2)
            energy = length * sum(abs(x)**2 for x in a)
            cross = 0j
            for j, n in enumerate(ns):
                for k, m in enumerate(ns):
                    if j == k:
                        continue
                    f = 2*pi*log(n/m)
                    integral = (cmath.exp(1j*f*(start+length)) - cmath.exp(1j*f*start))/(1j*f)
                    cross += a[j]*a[k].conjugate()*integral
            assert abs(cross.imag) < 1e-8
            error_bound = 2*nmax*harmonic/pi*sum(abs(x)**2 for x in a)
            assert abs(cross.real) <= error_bound + 1e-8
            assert energy + cross.real >= -1e-8
            max_relative_bound = max(max_relative_bound, abs(cross.real)/error_bound)
            mean_checks += 1

# A deliberately synthetic coefficient test: not original arithmetic rows.
gaussian_ratios = []
for n in (10, 100, 1000):
    g1 = 1/(2*pi**0.5)
    g2 = g1*exp(-log((n+1)/n)**2/4)
    gaussian_ratios.append([n, g2/g1])

print(json.dumps({
    "scope": "ideal factorization and generic Fourier algebra, not actual Gauss rows",
    "valuation_cases": checks,
    "admissible_cases": admissible,
    "admissible_cube_overlap_cases": overlap,
    "max_phase_error": phase_error,
    "exact_euler_cases": euler_checks,
    "mean_square_cases": mean_checks,
    "max_error_to_proved_bound_ratio": max_relative_bound,
    "synthetic_neighbor_gaussian_ratios": gaussian_ratios,
}, indent=2))
```



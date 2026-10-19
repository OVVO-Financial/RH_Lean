# RH_Lean agent daily report - 2026-10-18 / RH | Owner Payment

**Status:** COMPLETED / AUTHORIZED CONTINUATION COMPLETE
**Run ID:** 2026-10-18T12:07:47-04:00, scheduled invocation
**Canonical objective:** `VFCanonicalSquareVonKochStatement` remains OPEN
**Result classes:** `PAPER_PROOF` (new exact three-sector transfer cone and PNT lower obstruction), `FINITE_COMPUTATION`, `REFUTED` (scalar Mobius-to-native occurrence transfer), `NO_NEW_QUANTITATIVE_RESULT`

## A. Most important mathematical development

### Claim `20261018-owner-1`: exact high-composite transfer cone

On the genuine odd high-prime composite shell carrier, the native VF charge and the Mobius-signed charge are not two notations for one scalar. They are two coordinates with an exact positive determinant.

For `r>=3`, let
```text
I_r = {n : r^2<n<(r+1)^2},
P_r(c) = pi(floor(((r+1)^2-1)/c))-pi(floor(r^2/c))
```
for odd `3<=c<=r`. Every prime counted by `P_r(c)` satisfies `p>r`; the site `n=pc` is composite, odd, and has `p` as its unique prime factor above `r`.

For any finite set of such physical occurrences, with arbitrary nonnegative occurrence weights `v_{r,c,p}`, define
```text
A = sum_(mu(c)=+1) v,   B = sum_(mu(c)=-1) v,
Z = sum_(mu(c)=0) v,
V = A+B+Z,              W = sum v*mu(pc)=B-A.
```
Then exactly
```text
V-W = 2A+Z,
V+W = 2B+Z,
V^2-W^2 = (2A+Z)(2B+Z) >= 0.                 (TC)
```

For native comparison take `v=w_r=(2r+1)/(r*log(r^2+r+1/2))`. Then `V` is the literal original positive VF mass on these high-prime composite sites, while `W` is the same occurrences with genuine Mobius signs embedded into native weights. Formula (TC) restores every diagonal and cross-sector term: the right side expands the complete positive-parity, negative-parity, and squareful interactions omitted by a scalar sign transfer.

This converts the earlier qualitative warning, already present in the October 8 cofactor stratification and #975's `R=18` witness, into an all-carrier conservation law. A Mobius cofactor flip does not preserve the native source norm. Equality `V=|W|` is possible only if squareful exposure vanishes and all squarefree cofactors have one parity.

### Claim `20261018-owner-2`: the cone slack is PNT-sized at every large dyadic scale

For fixed odd `c` and `H` large enough that `c<=H` and every relevant prime exceeds the shell root,
```text
sum_(H<=r<2H) P_r(c)
 = pi(floor((4H^2-1)/c))-pi(floor(H^2/c)).      (FC)
```
The strict shells are disjoint; `cp` cannot be an internal square for `c=3,9,15` and the relevant high primes.

Use the legal fixed cofactors
```text
c=15: mu(c)=+1,   c=3: mu(c)=-1,   c=9: mu(c)=0.
```
With `m_H=min_(H<=r<2H) w_r`,
```text
A >= m_H*[pi(floor((4H^2-1)/15))-pi(floor(H^2/15))],
B >= m_H*[pi(floor((4H^2-1)/3 ))-pi(floor(H^2/3 ))],
Z >= m_H*[pi(floor((4H^2-1)/9 ))-pi(floor(H^2/9 ))].
```
Here `m_H >= 2/log(4H^2+2H)`. The proved PNT therefore gives
```text
A,B,Z >> H^2/log^2 H,
V-W >> H^2/log^2 H,
V+W >> H^2/log^2 H,
V^2-W^2 >> H^4/log^4 H.                       (PNT-SLACK)
```
All constants are absolute after a fixed threshold. This is an independent quantitative lower obstruction to deleting the transfer defect. It is not an upper bound on the complete signed shell, the canonical defect, or #915 payment.

## B. Current authoritative objective

Final live authority:

- `main@5ae5a524ca447d1936e351bbbe4b134c068a1a13`, merge of PR #979.
- `AGENTS.md` blob `4c66a1d462df98c84deebf0069ad11f904039858`.
- `CURRENT_PROOF_CONTRACT.md` blob `2fa9931dcdc1fc8a816aefb8aa348db12ee9a384`.
- PNT-first contract blob `e8acbeff24942d1f8ee0079f715afff2ddda2c33`.
- Two-scale attack plan blob `0606d764ffebb4639cc0abb52ccbef30546b7764`.
- External inbox blob `038018145c0fddb2f6306c0712373adf9cd1ea52`.
- Prior native cofactor stratification blob `0ac806cf94063d1b4b0d5926b91218caa731ecb2`.
- Source blobs: `TwoABScaleTransfer.lean` `fae76878063583322a48a329810cc1cc7b037ee7`; `SquareRootMatchedTransport.lean` `e9ab3bff6b8819182c39721f92859679d250002e`; `SquareBlockSmoothTransportGram.lean` `09f5e0108eb254a2f20fa2fd694d69cb455b2857`; `SquareRootSmoothRenewalInstantiation.lean` `9a63c8c2f9e42a64c0010721a78101c1f56858b1`; #975 sources `fa48f7d4d400302084600dc4f554057cac6a93e7`, `6fa7df64926bb6ec86f636734f44b8c9a020fd76`; #978 source `c67797ae7cda0ad9a7c393c69715016685a14d0a`; canonical theorem source `43e160ac7ad51f7646771297f43a9b95395ce709`.

PRs #975, #976, #978 and #979 are merged. No open PR was returned at the final refresh.

The public target remains
```text
exists C>=0, forall R>=2,
 |pi(R^2)-vfMidFinishedMass(R)-sqrt(2)| <= C*R*log R.
```
The exact PNT-first `M=S-L-E` and shell `delta_r=C_r-Q_r` identities are unpaid. Independent all-root signed compensation, original #915 contiguous-child descent with the same norm, finite A/C, the canonical endpoint, and RH remain OPEN.

## C. Structural hypothesis investigated

**Hypothesis.** The genuine high-prime Mobius transport could be carried occurrencewise into the original VF source after multiplying by native weights, perhaps leaving only a small boundary error.

**Outcome.** Refuted. Formula (TC) gives the exact defect, and (PNT-SLACK) proves that three permanent legal cofactor fibres force both cone directions to be macroscopic on every sufficiently large dyadic block. The obstruction is not merely a rare squareful exception: `c=15` and `c=3` force both squarefree parities, while `c=9` separately forces the Mobius-blind native sector.

The corrected representation is three-coordinate `(A,B,Z)`, or equivalently `(V,W,Z)` plus one parity coordinate. A scalar `S=A-T` identity cannot preserve this native source information.

## D. Mathematical derivation

If `pc in I_r`, `c<=r`, and `p` is prime, then `pc>r^2` forces `p>r`. Two prime factors greater than `r` cannot occur: their product is at least `(r+1)(r+2)>(r+1)^2`; a repeated high prime also reaches the excluded upper square. Thus `p` and `c=n/p` are unique, `p` does not divide `c`, and
```text
mu(pc)=-mu(c)
```
including the squareful zero case. Hence the weighted signed total is `B-A`, while the native composite total is `A+B+Z`; (TC) is exact algebra.

For (FC), the shells `I_H,...,I_(2H-1)` are disjoint. Their union contains precisely the nonsquare integers strictly between `H^2` and `4H^2`. For `c=3,9,15` and high prime `p`, `cp` is not a square, so counting `cp` in that union is exactly the displayed prime interval. PNT supplies each interval's positive asymptotic population. The elementary lower bound on `w_r` then proves (PNT-SLACK).

No probabilistic independence, short-interval PNT, fitted exponent, or RH-quality `Delta` premise is used.

## E. Quantitative consequence

The result proves a uniform lower bound on the **source-transfer defect**, not a saving on the target:

- Any occurrencewise replacement of native high-composite charge by weighted Mobius sign that omits `2A+Z` loses `Omega(H^2/log^2 H)` linear mass over dyadic shells.
- Any claimed norm-preserving scalar identification loses the exact determinant `Omega(H^4/log^4 H)`.
- The scale is below the open shell-energy ceiling `H^(5/2-eta+epsilon)` at the linear level and does not rule out compensation by prime, smooth, other-owner, or historical-anchor sectors.
- No exponent `eta>0`, Mertens improvement, canonical VF bound, or RH consequence follows.

Classification: `PAPER_PROOF / INDEPENDENT STRUCTURAL AND QUANTITATIVE NO-GO`, with `NO_NEW_QUANTITATIVE_RESULT` on the canonical objective.

## F. Falsification and circularity review

An exact integer sieve enumerated every odd high-prime composite occurrence and checked uniqueness, the parity partition, and `N-M=2P_++P_0` for dyadic blocks. Native weights were then applied only after exact counting.

| H | unweighted sites | unweighted Mobius mass | defect | c=9 count | c=15 count |
|---:|---:|---:|---:|---:|---:|
| 16 | 197 | 132 | 65 | 21 | 12 |
| 32 | 863 | 464 | 399 | 57 | 39 |
| 64 | 3,610 | 1,628 | 1,982 | 193 | 124 |
| 128 | 14,981 | 5,646 | 9,335 | 648 | 414 |
| 256 | 61,158 | 19,726 | 41,432 | 2,236 | 1,413 |

Weighted cone regression:

| H | A | B | Z | V | W | V^2-W^2 |
|---:|---:|---:|---:|---:|---:|---:|
| 16 | 6.026 | 48.403 | 8.571 | 62.999 | 42.377 | 2,173.038 |
| 32 | 35.429 | 156.724 | 32.449 | 224.602 | 121.295 | 35,733.768 |
| 64 | 157.034 | 515.647 | 120.340 | 793.021 | 358.613 | 500,278.826 |
| 128 | 658.428 | 1,734.344 | 457.088 | 2,849.861 | 1,075.916 | 6,964,113.268 |
| 256 | 2,635.191 | 5,950.878 | 1,681.483 | 10,267.552 | 3,315.687 | 94,428,844.879 |

The two evaluations of the determinant agreed to floating display precision; its equality is algebraic and exact.

Adversarial checks:

- **Defect is squareful-only:** false; `c=15` gives a permanent doubled `mu=+1` contribution.
- **One parity eventually disappears:** false by fixed `c=3` and `c=15` PNT intervals.
- **Cone slack bounds the full shell energy:** false inference; prime-only, smooth, cross-owner, and cross-shell terms remain.
- **Raw high-composite theorem transfers to #915 returned cells:** false without masks, clipping, orientations, historical `D_A`, global residual, and exact denominator. #975 places the direct cofactor below the half-run anchor.
- **Novelty audit:** the prior October 8 note already records native `+w_r` charges and squareful cofactors. The new claim is the exact three-sector cone, its complete quadratic restoration, and fixed-cofactor PNT lower obstruction. No earlier matching statement was found.

## G. Conceptual interpretation

The arithmetic carrier has two distinct notions of conservation.

Mobius prime extension conserves signed multiplicative parity: `mu(pc)=-mu(c)`. Native VF accounting conserves physical composite occurrence with positive charge. Their discrepancy is itself structured, not noise: it is the sum of the even-parity and squareful cofactor populations. Formula (TC) is the exact change-of-coordinates law.

This explains why the PNT-first route may still help the Mertens consumer while failing as a direct #915 source map. A successful common proof must retain the cone slack as a real sector and compensate it elsewhere; it cannot declare the two currencies identical.

## H. Competing mechanisms

- **Direct scalar Mobius-to-native occurrence transfer:** `REJECT`.
- **PNT-first joint signed Mertens route:** `CONTINUE`; (TC) does not obstruct its genuine unweighted consumer.
- **Two-scale shell energy:** `CONTINUE / REVISE`; keep `A,B,Z` separately whenever claiming a bridge to native VF.
- **Original #915 first-bad route:** `CONTINUE only with anchor restoration`; #975's positive global residual and below-anchor cofactor remain mandatory.
- **Fixed-depth/two-prime local folds:** remain retired by today's Wheel/Census/Referee/Lean evidence.
- **Hecke low variation and complete K1/K2/K3:** unaffected alternative carriers; no native bridge is inferred.

## I. Specialist handoffs

- **Coordinator:** add the transfer-cone node between Mobius shell arithmetic and original VF admission. A bridge omitting `2A+Z` is invalid.
- **Analytic:** when using native weights, seek a joint estimate for prime/smooth response plus both cone slack directions, not `W` alone. For the pure Mertens consumer, keep the carrier unweighted and do not import this native defect unnecessarily.
- **Wheel:** formalize the unique-high-prime fibre partition by cofactor parity and verify that the selected `3,9,15` fibres remain disjoint under any proposed mask.
- **Census:** only if a new mask is proposed, measure admitted `A,B,Z` and all cross terms; do not repeat the raw dyadic table.
- **Referee:** audit the fixed-cofactor PNT thresholds, native-weight comparison, and any claim that the determinant obstructs the full theorem rather than only scalar transfer.
- **Lean Verification:** after independent acceptance, the generic finite cone identity and the unique high-prime partition are small exact candidates. Do not attach a quantitative RH consumer.

## J. First independently missing lemma

The next exact source theorem is a **masked transfer-cone identity** on the original #915 carrier: for each admitted returned-cell orientation, partition the once-only high-composite occurrences into `mu(c)=+1,-1,0`, prove that the literal native admitted mass equals the native-weighted Mobius image plus `2A_adm+Z_adm`, and restore the same historical anchor, squareful mass, clipping, multiplicity, and NNS denominator.

Only after that identity is established is the first quantitative question legitimate: prove an independent signed compensation for the complete admitted prime/smooth/cone-slack/global-residual expression, or construct a strictly lower contiguous child-run with the same norm. Bounding the already recombined excess is target-equivalent.

## K. Next-run resume capsule

- Authority: `main@5ae5a524ca447d1936e351bbbe4b134c068a1a13`.
- New claims: `20261018-owner-1` exact transfer cone; `20261018-owner-2` fixed-cofactor PNT lower obstruction.
- Accepted continuity: one/two-prime local no-go; `t=3` sign control refuted; #975 historical anchor obstruction; #978 exact Lambda/hyperbola interfaces; #979 two-scale attack plan.
- Strongest conclusion: direct scalar Mobius-to-native source transfer is uniformly defective by a structured PNT-sized sector.
- First next action: independent Referee review, then formulate the masked cone identity from actual #915 admission definitions. Do not claim the raw result is already admitted or quantitative payment.
- No canonical exponent gain and no RH proof claim.

## L. Publication verification

Early `IN_PROGRESS` commit: `7a1f53ffcc2751f70596001a27b5d0729c550e2a`; readback blob `c859a6d1afc6eb260ca028d110e3cc7b083d3e4a`. Substantive final commit `23dbafabbb78f96c971c226d118740ec55168b41` was fetched successfully; immediate readback blob `822316bf64ba8bf8a53cd73489789cce0714981e` was 13,731 characters and contained both claim IDs and `COMPLETED` status. The metadata-only publication commit and its final readback are verified externally after this line.


## M. Authorized continuation checkpoint - 2026-10-18T20:43-04:00

**Status:** IN_PROGRESS. Live authority refreshed to `main@c2b075fca8a02079ebab7464a16e1fb58c2b5c7a` (merged PR #980). The raw cone is now `PROVED_IN_LEAN_ON_MAIN` in `research/RAW_TRANSFER_CONE_20261018.lean`; its occurrence-level and masked historical bridges remain open.

The continuation tests a signed aggregation law omitted by the raw scalar cone. For indexed admitted sectors ((A_j,B_j,Z_j)) and real orientation/clipping coefficients (lambda_j), set
[
V_lambda=sum_jlambda_j(A_j+B_j+Z_j),qquad
W_lambda=sum_jlambda_j(B_j-A_j).
]
Candidate exact law:
[
V_lambda^2-W_lambda^2=
left(sum_jlambda_j(2A_j+Z_j)ight)
left(sum_jlambda_j(2B_j+Z_j)ight).
]
This restores all diagonal and cross-sector interactions. I am checking the exact inverse condition for failure, whether nonnegative masks are the maximal unconditional cone-preserving class, and whether the result supplies a genuine #915 restriction or only a sharp no-go. No quantitative target claim is made at this checkpoint.


## N. Final authorized continuation - signed aggregation and moving-window source audit

**Continuation completed:** 2026-10-18T21:18-04:00  
**Live authority:** main@c2b075fca8a02079ebab7464a16e1fb58c2b5c7a; no open or draft PR returned at final refresh.  
**New result classes:** IDENTITY_ONLY / PAPER_PROOF structural classification; FINITE_COMPUTATION; REFUTED literal once-only W(H)-to-#915 transfer; NO_NEW_QUANTITATIVE_RESULT.

### A. Most important mathematical development

#### Claim 20261018-owner-3: exact signed aggregation cone and inverse classification

Let J be finite. For every j in J let A_j,B_j,Z_j be nonnegative sector masses, and let lambda_j be an arbitrary real admission/orientation/clipping coefficient. Define

~~~
V_lambda = sum_j lambda_j (A_j+B_j+Z_j),
W_lambda = sum_j lambda_j (B_j-A_j),
U_lambda = sum_j lambda_j (2A_j+Z_j),
L_lambda = sum_j lambda_j (2B_j+Z_j).
~~~

Then, with every diagonal and cross-j interaction retained,

~~~
V_lambda-W_lambda = U_lambda,
V_lambda+W_lambda = L_lambda,
V_lambda^2-W_lambda^2 = U_lambda L_lambda.              (SAC)
~~~

Therefore

~~~
W_lambda^2 > V_lambda^2
iff U_lambda L_lambda < 0,
~~~

so failure of native-square domination forces the two oriented parity/squareful margins to have opposite signs. This is an exact inverse theorem, not a covariance estimate.

Moreover, a coefficient family lambda preserves V_lambda^2 >= W_lambda^2 for **every** choice of nonnegative A_j,B_j,Z_j if and only if all nonzero lambda_j have one common sign.

Proof of sufficiency: if every lambda_j is nonnegative, both U_lambda and L_lambda are nonnegative; if every lambda_j is nonpositive, both are nonpositive. In either case their product is nonnegative.

Proof of necessity: if lambda_i>0 and lambda_j<0, choose only A_i>0 and B_j>0, with every other sector zero. Then U_lambda>0 and L_lambda<0, so the defect is negative. The concrete choice lambda=(1,-2), (A_1,B_1,Z_1)=(1,0,0), (A_2,B_2,Z_2)=(0,1,0) gives V=-1, W=-3 and V^2-W^2=-8.

**Interpretation.** Ordinary 0/1 masking, and more generally any common-sign weighting, preserves the on-main raw cone. Signed historical orientations do not inherit it automatically. A #915 proof using mixed orientations must prove the exact sign coupling U_lambda L_lambda>=0 on its admitted carrier or compensate the negative product elsewhere. Local cone inequalities cannot simply be summed after squaring.

Classification: IDENTITY_ONLY / SHARP STRUCTURAL NO-GO. This strictly extends the raw single-aggregate algebra to complete signed aggregation, but supplies no favorable sign for the actual original coefficients.

#### Claim 20261018-owner-4: exact translated-window overlap kernel and once-only obstruction

Consume Coordinator claim 20261018-coordinator-2. For r>=2 put m_r=floor(r/2), and for |t|<=m_r define the genuine translated interval

~~~
I_(r,t) = {n : r^2+t+1 <= n <= r^2+t+2r},
S_r(t)  = sum_(n in I_(r,t)) mu(n).
~~~

For x=n-r^2, the exact multiplicity of physical integer n in the r-family is

~~~
nu_r(n) =
 max(0,
   min(m_r,x-1)-max(-m_r,x-2r)+1).
~~~

For integers n,n', the complete pair kernel is

~~~
kappa_r(n,n') =
 max(0,
   min(m_r,x-1,x'-1)
   - max(-m_r,x-2r,x'-2r)+1).
~~~

Finite Fubini gives the exact Gram expansion

~~~
sum_(|t|<=m_r) |S_r(t)|^2
 = sum_(n,n') kappa_r(n,n') mu(n)mu(n').                (MWK)
~~~

The support is r^2-m_r+1 <= n <= r^2+2r+m_r. Thus t<0 imports the late edge of the preceding physical square block and t>0 imports the early edge of the following block. The diagonal is kappa_r(n,n)=nu_r(n), which can be 2m_r+1.

This gives a minimal actual-arithmetic obstruction to a literal once-only image in original #915. At r=4 the genuine squarefree integer n=21 has mu(21)=+1 and belongs to every shift t=-2,-1,0,1,2. Its diagonal coefficient in (MWK) is five, although it is one physical occurrence in the native square-block source. Treating the five labels (r,t,21) as five independent returned cells clones history. Collapsing them changes both diagonal and off-diagonal coefficients to kappa_r and still does not produce the original native weight, masks, compressed anchor, squareful restoration, global residual, or NNS denominator.

The generic fact that a window energy is an overlap Gram already exists on main in RHLean/Proof/LifetimeOverlapKernel.lean. The new content here is the explicit kernel for Coordinator's rigid integer windows, its neighboring-square support, and the direct once-only source-admission obstruction. Hence W(H) remains a legitimate separate Mertens/shell-energy analytic carrier, but it has no literal occurrence-preserving #915 transfer.

Classification: PAPER_PROOF / EXACT SOURCE-AUDIT NO-GO; finite witness independently checked.

### B. Current authoritative objective and sources

The canonical objective remains

~~~
exists C>=0, forall R>=2,
 |pi(R^2)-vfMidFinishedMass(R)-sqrt(2)| <= C R log R.
~~~

It is OPEN. The PNT-first M=S-L-E identity, signed shell identities, Wheel triangular cofactor profile, Coordinator moving-window reduction, and raw transfer cone do not prove an all-root signed estimate.

Final source record:

- main c2b075fca8a02079ebab7464a16e1fb58c2b5c7a, merge of #980;
- AGENTS.md blob 4c66a1d462df98c84deebf0069ad11f904039858;
- CURRENT_PROOF_CONTRACT.md blob 2fa9931dcdc1fc8a816aefb8aa348db12ee9a384;
- PNT-first contract e8acbeff24942d1f8ee0079f715afff2ddda2c33;
- two-scale plan 0606d764ffebb4639cc0abb52ccbef30546b7764;
- external inbox 038018145c0fddb2f6306c0712373adf9cd1ea52;
- raw cone source b47db297c6b9e9eaee5d6d884a27bb211b9053ff;
- #975 source-admission obstruction fa48f7d4d400302084600dc4f554057cac6a93e7;
- #975 global residual source 6fa7df64926bb6ec86f636734f44b8c9a020fd76;
- generic lifetime overlap kernel 22cab57fb65110494d47c97c9e8777b371e04a6a;
- TwoABScaleTransfer fae76878063583322a48a329810cc1cc7b037ee7;
- SquareRootMatchedTransport e9ab3bff6b8819182c39721f92859679d250002e.

Today's Coordinator, Analytic, Wheel, Census, Referee and Lean reports were consumed at blobs 4510607938e185534ba6074f58b2c3bb51a0f368, f7b981952037bffa17c67b518edb0c5638f01f05, 1f2e83a07d2d277f1137fd0239109f3abea5cbee, 701b74c281d01f6727669808566d76b1e8758b26, c0360eaa56c34198f21f9387113fd565a19b542f, and bff111a9448b17061f4dc2be760ea8422245a3f6. October 17 Owner blob and its recorded complete day set remain YESTERDAY=CARRY_FORWARD. EXT-20261018-PNT-1..3 were retained with their original classifications.

### C. Derivation, falsification and numerical verification

The proof of (SAC) is the difference-of-squares identity after finite linearity. The common-sign classification is both necessary and sufficient, so there is no larger coefficient class on which the cone holds without extra arithmetic restrictions.

For (MWK), an integer n occurs at shift t exactly when

~~~
x-2r <= t <= x-1
and
-m_r <= t <= m_r.
~~~

Intersecting these integer intervals gives nu_r. Intersecting the corresponding conditions for n and n' gives kappa_r. Expanding each square and interchanging finite sums proves (MWK), retaining every cross term.

An independent exact sieve checked the direct window-square sum against the kernel expansion:

| H | direct W(H) | kernel expansion | largest observed diagonal |
|---:|---:|---:|---:|
| 2 | 3 | 3 | 3 |
| 4 | 43 | 43 | 7 |
| 8 | 2,335 | 2,335 | 15 |
| 16 | 10,723 | 10,723 | 31 |
| 32 | 100,443 | 100,443 | 63 |

The r=4,n=21 five-shift witness was checked separately. This is finite verification of endpoints and expansion, not an all-scale estimate; the displayed formulas provide the paper proof.

Adversarial review:

- **Sum the local cone over signed groups:** false; the two-group defect -8 is a counterexample.
- **A mask always breaks the cone:** false; every common-sign mask preserves it.
- **W(H) is a once-only enlargement of the square source:** false; nu_r can be order r and the support crosses neighboring blocks.
- **Overlap duplication invalidates W(H) as an analytic quantity:** false; it is a valid positive semidefinite Gram and Coordinator's MW1-MW2 remain untouched.
- **The kernel estimate proves MW3:** false; no cancellation or upper bound is obtained.
- **The witness alone disproves every possible VF bridge:** false; it disproves a literal occurrence-preserving identification. A new normalized kernel comparison with all complements could still be proved.
- **Circularity:** neither claim assumes shell energy, a Mertens estimate, original payment, the canonical endpoint, or RH.

### D. Quantitative consequence

There is no new exponent or global upper bound.

The exact consequences are restrictions:

1. Any signed masked use of the native/Mobius cone must control both complete oriented margins; checking local sector cones is insufficient.
2. Any direct use of MW3 in #915 requires a nontrivial bridge from the overlap kernel kappa to the original once-only native quadratic, including the large diagonal multiplicities, adjacent-block imports, actual weights and historical normalization.
3. The raw PNT-sized cone slack from claims owner-1/-2 remains real, but (SAC) shows that mixed orientations can reverse its sign through cross-group terms. No unconditional global obstruction or payment follows.

### E. Competing mechanisms and decisions

- **SHIFT-L2 / MW3:** CONTINUE as the highest-priority separate Mertens experiment. Claims owner-4 show it is not directly the original VF source.
- **Signed aggregate cone:** CONTINUE only as an exact source-audit language and inverse test; it is not itself a payment mechanism.
- **COFACTOR-PROFILE:** CONTINUE as the multiplicative alternative, retaining d=1 and all bands.
- **Direct scalar Mobius-to-native transfer:** REJECT, now both locally and under arbitrary mixed aggregation.
- **Original #915 route:** CONTINUE only through a literal masked native reconstruction with anchor and residual. A kernel comparison, if proposed, must be stated separately from occurrence identity.
- **Within-shell outer-prime dispersion:** RETIRED at the current rank-one carrier.

### F. Specialist handoffs

- **Coordinator:** insert MWK as the source-admission veto beneath MW3. The analytic implication to shell energy is valid; a direct arrow from W(H) to #915 is not.
- **Analytic:** attack MW3 on its genuine duplicated-window Gram. Do not normalize away nu_r without bounding the altered off-diagonal kernel and boundary support.
- **Wheel:** if a multiplicative decomposition of kappa is attempted, preserve the exact interval-intersection kernel and both adjacent-square boundary pieces.
- **Census:** on the preregistered W(H) run, report maximal nu_r and boundary-import contributions in addition to W, cubic ratio and worst S_r(t). This tests whether a proposed normalized bridge deletes load-bearing mass.
- **Referee:** audit the common-sign iff classification and distinguish literal occurrence transfer from a possible inequality between quadratic kernels.
- **Lean Verification:** after independent acceptance, the finite-family signed aggregation identity/common-sign theorem and generic interval-intersection multiplicity formula are small formalization candidates. Attach no MW3 or VF quantitative consumer.
- **Coordinator/Proof Architect strategic note:** the strongest new concept is that both surviving routes are kernel problems: signed native transfer requires parity-margin sign coupling, while SHIFT-L2 requires an overlap-kernel estimate. They are not the same carrier and should not be merged without an exact bridge.

### G. First independently missing lemma

For the SHIFT-L2 route, the first quantitative lemma remains Coordinator's genuine all-start estimate

~~~
W(H) <<_epsilon H^(13/4-3 eta/2+epsilon)
~~~

for some eta>0, proved on the literal translated Möbius intervals. This is independent but stronger than the desired shell energy and no applicable theorem has been verified.

For a direct original-VF consumer, the first structural lemma is narrower and prior to any bound: write the actual #915 quadratic as an exact once-only native kernel, then exhibit a proved comparison or compensated identity with the kappa-weighted translated-window Gram, restoring masks, w_r, squareful terms, compressed history, global residual, and denominator. An occurrence bijection is impossible by owner-4; any valid bridge must be a genuine quadratic-kernel theorem.

### H. Next-run resume capsule

- Authority: main@c2b075fca8a02079ebab7464a16e1fb58c2b5c7a; #980 merged; no open PR.
- New claims: 20261018-owner-3 signed aggregation factorization/common-sign iff; 20261018-owner-4 exact moving-window overlap kernel and once-only obstruction.
- Accepted prior claims: owner-1/-2 raw cone and PNT slack, now with raw cone PROVED_IN_LEAN_ON_MAIN; Coordinator MW1-MW2 PAPER_PROOF; MW3 OPEN.
- Strongest obstruction: translated-window copies cannot be spent as distinct original physical occurrences, and mixed orientations defeat local cone aggregation unless the two global margins are sign-coupled.
- Highest-value next step: Referee audit of owner-3/-4, followed by either an analytic attack on literal MW3 or an exact construction of the native #915 quadratic kernel for comparison. Do not rerun the five-block kernel regression without a new hypothesis.
- No canonical bound, Mertens exponent gain, finite A/C, or RH proof.


## O. Continuation publication verification

Early continuation checkpoint commit: 7f08ad4a5a9afe5b0cf0fb1fb88f057ac9a3a25c; readback blob be6a5731f7bab8ad310c592e11feaa165125e04a.

Substantive continuation commit: f2fff6eb684bb509136c45971fe4a08c6881cabe. Immediate readback blob b1f1a3ddd5e44e9b8c9cc5d4014135a7f25b2d8e was 28,415 characters and contained COMPLETED status, both new claim IDs, and the final main SHA. This metadata update is verified by a further readback after publication.

# RH_Lean agent daily report - 2026-10-20 / RH | Finite Wheel & Incidence

**Status:** COMPLETED  
**Run ID:** 2026-10-20T00:09:00-04:00, scheduled invocation  
**Canonical objective:** `VFCanonicalSquareVonKochStatement` remains OPEN  
**Primary campaign:** native, source-faithful reconstruction of the complete seven-eighths detector  
**Result classes:** `PAPER_PROOF` (all-prime ideal incidence and conjugate-phase conservation), `STRUCTURAL_SOURCE_AUDIT`, `NO_NEW_QUANTITATIVE_BOUND`

## A. Bottom line

The missing ideal/rational incidence map can be stated exactly. For a rational prime (p), the polynomial
[
f_p(T)=T^2+T+1
]
classifies the degree-one Eisenstein prime-ideal labels.

- (p=3): one double root, hence one ramified ideal label.
- (pequiv1pmod3): exactly two distinct roots (r) and (r'=-1-r), hence two conjugate split ideal labels.
- (pequiv2pmod3): no root, hence no degree-one label; the rational prime is inert and its ideal norm is (p^2).

For a split (p>3) and an Eisenstein coordinate (alpha=a+bomega), put
[
x_r=a+br,qquad x_{r'}=a+br',qquad N(alpha)=a^2-ab+b^2.
]
Then
[
x_rx_{r'}=N(alpha)pmod p.
]
The zero mask has an exact trichotomy:
[
#{jin{r,r'}:x_j
e0}=
egin{cases}
2,&p
mid N(alpha),\
1,&pmid N(alpha) 	ext{and} p
midgcd(a,b),\
0,&pmid a, pmid b.
end{cases}
]
Thus the OAI good-character branch has two, one, or zero active ideal slots, and the missing slots are precisely the (Pmid u) zero-extension branches. This is not a discretionary mask.

For (e=(p-1)/6), the two genuine sextic residues satisfy
[
chi_r(alpha)chi_{r'}(alpha)
 =N(alpha)^epmod p.
]
When both slots are active, each factor is a sixth root of unity. The rational norm therefore determines their **product**, but not either phase or their sum. For the marked-minus-rescaled main phases (m_j=-chi_j^{-1}),
[
m_rm_{r'}=igl(N(alpha)^eigr)^{-1}.
]
This is a new usable conservation law and an equally important no-collapse theorem.

**Claim ID:** `20261020-wheel-1`.  
**Classification:** `PAPER_PROOF / EXACT ALL-PRIME INCIDENCE / NO ANALYTIC SAVING`.

## B. Authority and continuity

Final source refresh:

- live `main@976cfdf5808eee7e36b35bf16074c8915ff8fc4d`, merge of PR #984;
- `AGENTS.md` blob `20bff52d6784c17d4a7d6ac731f4a71c2bdad8a6`;
- `CURRENT_PROOF_CONTRACT.md` blob `2fa9931dcdc1fc8a816aefb8aa348db12ee9a384`;
- native replication protocol blob `53194dc3ae106be363bc22cf85a88bac4a3b2e6e`;
- dynamic protocol blob `bd1189617c069565a881c2a5c5dbd9a138bc48c1`;
- external inbox blob `038018145c0fddb2f6306c0712373adf9cd1ea52`;
- native ideal-fiber source blob `cc99bbb2d02b700ff9cf2e555861208430f42acc`;
- owner-projection source blob `3b957ea0ab1b53e2d6e79599329fb234f6e4561c`.

At intake, all 2026-10-20 upstream specialist files and this Wheel file were absent: `TODAY=PENDING`. The newest full synthesis is the 2026-10-19 Coordinator report, blob `6d27ec1427b2928fe36accc1642749f47a2cf6b6`. It changes the primary campaign to the native seven-eighths replay and assigns Wheel the all-prime ideal/rational incidence map. The preceding Wheel report, blob `3ad449f5bd364aafcbe65375da865dfccad30d61`, is `YESTERDAY=CARRY_FORWARD`: its moving-window low-gcd problem remains valid secondary work but is suspended under the new priority.

Relevant 2026-10-19 Owner, Analytic, and Referee reports were absent in the Coordinator's verified intake, so no execution is inferred. The 2026-10-19 Census blob `f87aaa1dc0d7e4b7f093e44141cefdce69ecc480` and repaired Lean/#984 evidence were consumed through the synthesis. External claims `EXT-20261018-PNT-1..3` retain their exact-identity, finite-falsifier, and source-no-go status; they do not supersede the merged native-replication directive.

## C. Proof of claim `20261020-wheel-1`

### Rational-prime classification

For (p
e3), a root of (T^2+T+1) is a nontrivial cube root of unity because
[
(T-1)(T^2+T+1)=T^3-1
]
and (T=1) is a root only when (3=0). The cyclic group (mathbb F_p^	imes) has nontrivial third roots exactly when (3mid p-1). Hence primes (pequiv1pmod3) split into two degree-one ideals, while primes (pequiv2pmod3) are inert. At (p=3),
[
T^2+T+1=(T-1)^2,
]
giving the unique ramified label.

The local ideal-Möbius norm-fiber multiplicities agree with the already compiled rational Euler dictionary:

- ramified (3): coefficient (-1) at norm (3);
- split (p): two prime ideals, coefficient (-2) at norm (p) and (+1) at (p^2);
- inert (p): no ideal of norm (p), one prime ideal of norm (p^2), coefficient (-1) there.

These multiplicities are incidence, not sextic phases.

### Exact zero-mask trichotomy

The compiled theorem `vf919SplitIdealResidue_norm` proves
[
(a+br)(a+br')=N(alpha)
]
in (mathbb F_p). Thus neither evaluation is zero iff (p
mid N(alpha)).

If both are zero, subtraction gives (b(r-r')=0). The two split roots are distinct, so (b=0), then (a=0). Conversely (pmid a,b) makes both zero. Therefore (pmid N(alpha)) with primitive coordinate pair modulo (p) forces exactly one zero evaluation. This proves the displayed 2/1/0 active-slot rule and identifies the correct nonunit branch without inventing an inverse character at zero.

### Conjugate-phase conservation

By definition,
[
chi_r(alpha)=x_r^e,qquad chi_{r'}(alpha)=x_{r'}^e.
]
Multiplicativity of exponentiation and the norm identity give
[
chi_r(alpha)chi_{r'}(alpha)=(x_rx_{r'})^e=N(alpha)^e.
]
If (x_r
e0), Fermat gives
[
chi_r(alpha)^6=x_r^{p-1}=1,
]
and similarly for (r'). The main selected phases are negatives of the inverses, so the two negative signs cancel in their product.

No distribution, PNT, Mertens, zero-free, moment, or target estimate enters this proof.

## D. Exact source consequence

Suppose a rational split cofactor prime (k
e p) is represented by its two chosen primary conjugate generators. Since (p
mid k=N(alpha)), both high-prime roots are active for each generator. The fiber over the one rational owner site (n=pk) therefore contains exactly
[
2 	ext{high-prime ideals}	imes2 	ext{cofactor ideal orientations}=4
]
ideal labels.

This explains the merged four-case spectra and the unphased norm-fiber coefficient (+4), but it imposes a once-only rule:

> The four ideal labels are four analytic phase rows over one physical integer owner, not four independently spendable physical occurrences.

An occurrence-faithful adapter must either:

1. sum the labelled phases inside the fiber and apply the original physical weight once; or
2. define a lifted measure whose pushforward to the integer carrier is proved to equal the once-only physical source.

Copying the same native site weight to every label proves a labelled algebraic identity, but by itself does not prove that the lifted sum equals the original once-only source. The merged theorem `vf919Sextic_x317_noOwnerOnlyCharacter` blocks the opposite mistake of collapsing the phases before summation. Both constraints must be satisfied simultaneously.

For a squarefree rational norm supported on (s) split primes, the same incidence gives (2^s) squarefree ideal fibers before phase aggregation. If an inert prime occurs to the first power, there is no ideal of that rational norm. This is the all-depth multiplicity rule that a global selected-slot product must preserve.

## E. Novelty and open-PR audit

Repository search found the compiled residue product
`vf919SplitIdealResidue_norm`, multiplicativity of the sextic residue, four finite phase witnesses, and the norm-only impossibility theorem. It did not find the all-prime 2/1/0 active-slot theorem or the conjugate sextic-product law stated as the source multiplicity gate.

Open PR #986, branch `proof/oai-exact-marked-rescaled-termwise-20261019`, observed at head `4345260a58f1c14f4018e46292469767c54cd908`, contains exact good-character and zero-extension algebra plus labelled native-seat sums. Its own source comments correctly warn that equal-weight split labels are a many-to-one projection and not a once-only sum over original integers. Claim `20261020-wheel-1` supplies the missing general slot count and pushforward obligation; it does not invalidate #986's algebra. PR #986 remains open/non-merged and its terminal analytic moment is still absent.

Open PR #985 is a distinct Euler/covariance census lane and supplies no native ideal-character moment. Draft PR #983 is the Lean 4.34.1 migration; compiler migration is not a mathematical saving. No PR, review, CI rerun, merge, schedule, or permission state was changed in this run.

## F. Falsifiers and limitations

1. **Norm-only phase:** refuted already at (x=317); the new theorem explains why only the conjugate product descends to the norm.
2. **Independent conjugate phases:** refuted by (chi_rchi_{r'}=N(alpha)^e). A model sampling the two phases independently is not source-faithful.
3. **Always two active slots:** false when (pmid N(alpha)). The primitive case has exactly one active slot; content divisible by (p) has none.
4. **One rational prime equals one ideal slot:** false for split primes; there are two.
5. **Four labels equal four physical seats:** false for a split high prime and split cofactor; all four project to (pk).
6. **Pair-product conservation gives cancellation:** false. It fixes a product, not a small sum or moment. The four merged witnesses already exhibit varying totals.
7. **Analytic conclusion:** none. Stage I 11/12, true local coefficient bounds, inverse second moment, refined plain fourth moment, certified bands, and terminal 7/8 detector remain open.

## G. Mechanism decision and handoff

**Decision:** CONTINUE the native ideal-labelled detector, with the incidence layer revised to use the exact all-prime slot/mask theorem.

**Owner:** define the lifted labelled measure and prove its pushforward is the once-only physical source. For squarefree split cofactor (k), explicitly account for the (4)-to-(1) fiber over (pk). Keep the (pmid N(alpha)) one-active-slot case separate.

**Analytic:** formulate moments on the labelled ideals subject to the conjugate-product constraint. Do not impose independent random phases and do not replace the pair by its rational norm before the moment.

**Census:** test the 2/1/0 slot rule on split primes with primitive and imprimitive coordinates, including (pmid N(alpha)), rather than extending the existing four unit witnesses.

**Referee:** audit the root classification, the both-zero iff coordinate-content statement, and whether any proposed pushforward spends the physical owner more than once.

**Lean:** the smallest nonduplicate formal targets are:
`vf919SplitSexticResidue_conj_mul`,
`vf919SplitIdealResidue_both_zero_iff`, and
a finite active-root cardinality theorem under split-prime hypotheses.
Formalization should reuse `vf919SplitIdealResidue_norm`; it must not claim a moment bound.

## H. Resume capsule

- Authority: `main@976cfdf5808eee7e36b35bf16074c8915ff8fc4d`.
- New claim: `20261020-wheel-1`, all-prime ideal incidence, exact 2/1/0 zero mask, and conjugate sextic-phase product conservation.
- Independent progress: exact source multiplicity and a once-only pushforward gate.
- Quantitative progress: NONE.
- First structural blocker: construct the labelled-to-physical pushforward with the (2^s) ideal-fiber multiplicities and zero masks.
- First analytic blocker after that: uniform inverse second/plain refined fourth moments on the genuine labelled source.
- Canonical VF, native independent 7/8, original #915 payment, and RH remain OPEN.

## I. Publication verification

The report was created on `agent-reports` by commit
`cc679db62bf19499c5458830c738d86308ad8c2a`. Immediate readback returned
blob `412020c04a8b013026704a75bbfd517e915a269f`, 11,426 characters,
`COMPLETED` status, and claim ID `20261020-wheel-1`. This verifies
publication only; it does not promote the paper theorem to Lean or prove an
analytic estimate. No main-source, PR, review, CI, merge, schedule, or
permission state was mutated.

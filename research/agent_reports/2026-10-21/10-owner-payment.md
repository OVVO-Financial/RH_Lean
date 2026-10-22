# RH_Lean agent daily report - 2026-10-21 / RH | Owner Payment

**Status:** COMPLETED
**Run ID:** 2026-10-21T20:43:00-04:00 scheduled invocation
**Canonical objective:** `VFCanonicalSquareVonKochStatement` remains OPEN
**Primary campaign:** independent source-faithful reconstruction of the native seven-eighths mechanism
**Result classes:** `PAPER_PROOF / EXACT STRUCTURAL RESTRICTION`, `FINITE_COMPUTATION`, `REFUTED`, `NO_NEW_QUANTITATIVE_BOUND`

## A. Most important mathematical development

### Claim `20261021-owner-1`: diagonal-to-scalar covariance sign reversal

The newly merged global Mobius decoder has a strong but sharply limited cancellation law.

On every original odd open-square block, split the actual physical charge sitewise as

```text
z_n = mu_n + r_n,
```

where `r_n` is the exact compiled physical remainder. For every nonsquareful site, the occurrence-diagonal mixed product `mu_n*r_n` is strictly negative when `R>=3`. Nevertheless, after all occurrences are projected onto the single scalar used by the block source, the complete mixed term

```text
(sum mu_n) * (sum r_n)
```

can be positive, zero, or negative on the genuine carrier.

More exactly, write

```text
w = vfMidOddFractionalPrimeSeatWeight R,
P = number of prime seats,
C = number of squarefree composite seats,
U = sum over odd block seats of mu(n),
Z = sum z_n = w*R-P.
```

Then

```text
diagonal mixed covariance = sum mu_n*r_n = w*U-C,          (1)
scalar mixed covariance   = U*(Z-U) = U*(w*R-P-U).         (2)
```

For `R>=3`, `0<w<1`, and (1) satisfies the genuine all-scale restriction

```text
w*U-C <= -w*P-(1-w)*C <= 0,                               (3)
```

strictly whenever a nonsquareful seat is present. But (2) is positive exactly when `U` and `Z` have the same sign and `|U|<|Z|`. Thus the omitted off-diagonal interactions can reverse the favorable diagonal sign.

This is the precise obstruction to promoting a local Mobius/correction anti-correlation into an original global NNS payment. It is also a concrete instance of the live PR #1000 warning that the complete Hermitian mixed term must be retained.

An exact one-implementation census of the original odd-seat carrier for `3<=R<=5000` found 293 positive, 4,641 negative, and 64 zero scalar mixed terms. First positive witness:

```text
R=57, U=-2, P=17,
w=0.24896743791146714,
Z=-2.8088560390463737,
Z-U=-0.8088560390463737,
U*(Z-U)=+1.6177120780927474.
```

The universal statement “the exact physical correction has nonpositive global covariance with the Mobius channel” is therefore `REFUTED` on the original arithmetic block carrier. The diagonal statement survives exactly.

## B. Current authoritative objective

Authority was refreshed to
`main@66af9b34c082485872815ece9a7721606381c07f`, merge of PR #995. The public target remains

```text
exists C >= 0, forall R >= 2,
  |pi(R^2)-vfMidFinishedMass(R)-sqrt(2)| <= C*R*log R.
```

The active campaign remains the independent native reconstruction of the complete external seven-eighths mechanism. Exact source identities, imported terminal theorems, and conditional moment consumers do not establish the missing independent analytic saving.

Material live blobs:

- `AGENTS.md`: `20bff52d6784c17d4a7d6ac731f4a71c2bdad8a6`.
- `CURRENT_PROOF_CONTRACT.md`: `2fa9931dcdc1fc8a816aefb8aa348db12ee9a384`.
- Native replication protocol: `53194dc3ae106be363bc22cf85a88bac4a3b2e6e`.
- Global Mobius/physical weld Lean source: `5e3212e20666b9ed7f13d6bd9ebadfad88338eaa`.
- Physical forcing decoder: `91ed831f2c44d749d3463adae775fce94f091f04`.
- Weld note: `301f353ed07621fbc3bcfe41af8784618c26085c`.
- Five-stage owner note: `cf2199d2ae0486002a18b3ba3208f0a8bf4a696d`.
- External inbox: `038018145c0fddb2f6306c0712373adf9cd1ea52`.

Continuity consumed:

- Today's Owner report was absent at intake: `TODAY=PENDING`.
- Yesterday's Owner report `6381decdb075f728386e709aa19758e07a39d2ee` is `YESTERDAY=CARRY_FORWARD`.
- Today's Census `b7ea2642bb7713e8a1685dc77c5a3b3b0f1cc800`, Referee `e6ef7fa0ebffeea4643b9e892591156d6cd0c1fb`, and Lean `6c0d5af5ad0b00608643513585bd6a8c59207098` were consumed.
- Today's Coordinator, Analytic, and Wheel reports were absent at the checked paths: `TODAY=PENDING`; their verified October 20 reports are `YESTERDAY=CARRY_FORWARD`.
- External handoffs were read. No external claim was upgraded beyond its recorded proof class.

PR status was refreshed. PR #995 is merged at the authority SHA. The only open PR observed was draft #1000 at head
`9edc4ad3d1dd12bb23a60660fb1945237149f821`. Its exact finite norm-fiber grouping and Hermitian mixed-term identities are relevant structural work; its canonical admission hypothesis and high-source estimate remain unproved for the full production detector. No PR was modified.

## C. Structural hypothesis investigated

**Hypothesis H1.** The exact Mobius sign flip plus physical remainder forces a favorable global mixed covariance on the actual block source.

**Competing H2.** The sign is forced only on occurrence diagonals; scalar projection restores off-diagonal terms that can reverse it.

The newly compiled theorems
`vf915GlobalDecoded_freshPrime_eq_mu_plus_correction`,
`vf915GlobalDecoded_eq_mu_add_remainder`, and
`vf915GlobalDecoded_fullyLabelledPairGramWeld`
supply the exact carrier. No stochastic model or simplified owner count is used.

Result: H1 is false; H2 is proved by (1)-(3) and witnessed on genuine blocks.

## D. Mathematical derivation

Let the original odd block seats be
`S_R={n:R^2<n<(R+1)^2, n odd}`. It has cardinality `R`. Put
`m_n=mu(n)`, `z_n=w-1_Prime(n)`, and `r_n=z_n-m_n`.

There are four exact cases.

1. Prime: `m_n=-1`, `z_n=w-1`, `r_n=w), so `m_n r_n=-w<0`.
2. Squarefree composite with `m_n=+1`: `r_n=w-1), so `m_n r_n=w-1<0`.
3. Squarefree composite with `m_n=-1`: `r_n=w+1), so `m_n r_n=-w-1<0`.
4. Squareful composite: `m_n=0), so `m_n r_n=0`.

Summing gives (1): the prime contribution is `-wP`; on squarefree composites,
`sum m_n = U+P`, hence their contribution is `w(U+P)-C). Total:
`wU-C`.

Since the signed sum over `C` squarefree composites is at most `C),
`U+P<=C`, so `U<=C-P`. Multiplication by `0<w<1` proves (3).

On the other hand, exact finite summation gives

```text
sum r_n = sum(z_n-m_n)=Z-U,
```

and therefore the scalar mixed term is (2). Elementary sign analysis yields:

- positive iff `U,Z` have the same nonzero sign and `|U|<|Z|`;
- zero iff `U=0` or `U=Z`;
- negative otherwise.

The exact off-diagonal restoration is

```text
sum_(i!=j) m_i*r_j
 = U*(Z-U) - (w*U-C).
```

This term has no forced sign and is precisely what is discarded by a diagonal-only payment.

The bound `0<w<1` for `R>=3` is already established in the source line used by the one-block inlet; it also follows directly from the displayed logarithmic weight. No first-bad hypothesis or target estimate enters the argument.

## E. Quantitative consequence

No Mertens exponent, seven-eighths moment, zero-free line, canonical VF estimate, finite A/C statement, or RH result is improved.

The independent quantitative content is only the diagonal restriction (3), which is order the number of nonsquareful occurrences. It cannot be credited against the original scalar source without controlling the off-diagonal restoration.

The exact new target exposed by this classification is not “prove negative covariance.” It is to control the actual-source population in the dangerous alignment sector

```text
U and Z have the same sign, with |U|<|Z|,
```

together with the historical anchor, masks, clipped returned pairs, and all other four-channel Gram terms. A theorem excluding or quantitatively suppressing this sector would be independent; the present work does not prove it.

## F. Falsification and circularity review

- **Global nonpositive Mobius/remainder covariance:** refuted by the original block at `R=57`; many later witnesses occur.
- **Diagonal nonpositive covariance:** survives and is proved by exact site classification.
- **“Fresh-prime composites alone settle the block”:** false; prime roots and squareful zero-Mobius seats change the complete source.
- **“Negative diagonal can be summed after projection”:** false; projection is not an isometry and restores every `i!=j` term.
- **“The R=317/1027 negative examples prove a law”:** false. Their scalar mixed terms are negative, but `R=57` and 292 other roots through 5000 have positive terms.
- **“Positive mixed term disproves the proof objective”:** false. Other physical channels, the denominator, historical anchor, and nonlocal analytic compensation may dominate.
- The finite scan uses one exact integer Mobius/prime sieve and floating evaluation of the explicit logarithmic weight. It is `FINITE_COMPUTATION`, not a uniform theorem or independent reproduction.
- No step assumes seven-eighths, RH, the first-bad contradiction, or the desired covariance bound.

## G. Conceptual interpretation

The decoder creates two different geometries.

In occurrence space, every nonsquareful physical atom has an anti-aligned Mobius/remainder diagonal. In the original scalar block observable, all occurrence coordinates are collapsed onto the all-ones direction. That projection adds a complete off-diagonal matrix, and its sign is governed by the relative position of the Mobius imbalance `U` inside the physical block mass `Z`.

Thus the actual missing arithmetic principle is a discrepancy theorem for the projected imbalance, not another pointwise sign lemma. Prime ancestry supplies exact local cancellation, but does not determine how the signed population aligns with the physical prime-count error after aggregation.

## H. Competing mechanisms

- **Occurrence-diagonal anti-alignment:** RETAIN as an exact structural input.
- **Universal scalar negative covariance:** ABANDON; explicitly refuted.
- **Actual-source weighted moving-conductor/ray-class theorem:** CONTINUE; it could control the dangerous alignment sector without discarding phases.
- **PR #1000 canonical low-gate norm-fiber bridge:** CONTINUE as a source interface; it still needs actual admission, multiplicity, high-height energy, and low/high mixed control.
- **Positive returned-owner terminal payment before compensation:** REJECT by merged #995's prime-root lower bound.
- **Historical #915 first-bad payment:** keep separate; the compiled content audit makes a universal payment target-strength.

## I. Specialist handoffs

- **Coordinator:** place claim `20261021-owner-1` before any norming step. The portfolio must distinguish diagonal anti-alignment from scalar covariance.
- **Analytic Type II:** seek a uniform original-weight estimate for the alignment statistic `U_R(Z_R-U_R)` or its fully labelled detector analogue, retaining the low/high and marked/rescaled mixed terms.
- **Wheel:** classify whether factor-incidence constraints restrict the dangerous sector `0<|U_R|<|Z_R|` with matching sign, rather than only counting admissible atoms.
- **Census:** independently reproduce scalar mixed-term signs with exact interval arithmetic for `w_R`; stratify positive witnesses by prime roots, squarefree composite parity, squareful seats, and actual masks.
- **Referee:** audit equations (1)-(3), especially the distinction between the diagonal sum and product of sums.
- **Lean Verification:** after review, formalize the four-case diagonal identity and scalar sign trichotomy against the live decoder. Do not attach a global payment conclusion.

## J. First independently missing lemma

> **Projected-imbalance compensation lemma.** For the fully labelled actual marked-minus-rescaled or original #915 carrier, with its genuine weights, masks, multiplicities, prime-root/squareful corrections and historical anchor, prove a uniform bound on the positive part of the complete scalar mixed Gram created when the occurrence-diagonal anti-alignment is projected to the detector observable.

A useful theorem must be quantitatively stronger than triangle inequality and must not assume the target source bound. For the elementary block projection, its core positive sector is exactly
`U_R(Z_R-U_R)>0`; the production theorem must additionally retain every other channel and cross term.

## K. Next-run resume capsule

- Authority: `main@66af9b34c082485872815ece9a7721606381c07f`.
- New claim: `20261021-owner-1`, equations (1)-(3).
- Status: `PAPER_PROOF / EXACT STRUCTURAL RESTRICTION`; finite sign census separately `FINITE_COMPUTATION`.
- Strongest falsifier: genuine block `R=57` has positive scalar mixed covariance despite strictly negative occurrence diagonals.
- Live relevant draft: #1000 at `9edc4ad3d1dd12bb23a60660fb1945237149f821`.
- Next action: derive the fully labelled analogue of the projected-imbalance statistic on the actual marked/rescaled two-gate source, then ask Analytic for a uniform bound on its positive part.
- Campaign remains `INCOMPLETE; NO INDEPENDENT 7/8 PROOF`.

## L. Publication verification

Early checkpoint commit:
`cd040afc83741c9249fc772be329cf999b4d02ec`; verified readback blob
`2e82224506813a63e66c008e4474494fce043e3f`.

Substantive completion publication requested below; commit and final readback verification follow.

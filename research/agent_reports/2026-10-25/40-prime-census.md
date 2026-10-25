# RH_Lean agent daily report - 2026-10-25 / RH | Prime Census Laboratory

**Status:** COMPLETED  
**Run ID:** 2026-10-25T01:51:00-04:00 scheduled invocation  
**Canonical objective:** VFCanonicalSquareVonKochStatement remains OPEN  
**Route investigated:** CORR4 complete physical remainder / low-q^2 daughters  
**Evidence status:** FINITE_COMPUTATION plus REFUTED local sign necessity; CONJECTURE for the extreme inverse classification; NO_NEW_GLOBAL_QUANTITATIVE_BOUND

## A. Main result

### Claim 20261025-census-1: large observed CORR4 remainder bills are endpoint excursions, with low daughters amplifying through sign alignment

For every integer R >= 56, freeze the literal carrier used on open PR #1021:

```text
X_R = R^2 - 1
Q_low(R) = {odd primes q : q^2 < R}
Y_q = floor(X_R / q^2)
C_R = M(R-1) - M(X_R)
U_R = sum_(q in Q_low(R)) M(Y_q)/q
E_R = sum_(q in Q_low(R)) M(Y_q)^2
B_R = C_R - U_R
c_R = (B_R^2 - (9/4) E_R)/(R^2 K_R)
K_R = max_(0 <= y < R) (M(y)-1)^2/(y+1)
```

No owner, cross term or sign is dropped. Exact rational arithmetic gives the identity

```text
B_R^2 - (9/4)E_R
  = C_R^2 - 2 C_R U_R + (U_R^2 - (9/4)E_R).       (1)
```

This separates the parent endpoint, parent-daughter cross, and daughter-only terms without changing the physical scalar.

The pre-registered mechanism test compared:

1. **daughter-payment hypothesis:** positive or extreme c_R is primarily created by favorable low-q^2 daughter cancellation;
2. **endpoint-excursion hypothesis:** C_R^2 is already the dominant bill, while U_R mostly tracks M(X_R), so the cross term may amplify rather than cancel the square-endpoint excursion.

On the discovery range 56 <= R <= 2000 and previously unexamined held-out range 2001 <= R <= 6000, hypothesis 2 is the observed extreme mechanism.

Among all 58 roots with c_R > 1/10:

- every one has C_R U_R < 0;
- every one has U_R M(X_R) > 0;
- |M(R-1)|/|C_R| <= 0.030043;
- |U_R|/|M(X_R)| lies between 0.004445 and 0.078111;
- C_R^2 supplies between 0.93171 and 1.02557 of the final positive numerator in (1).

Thus the low-q^2 synthesis follows the sign of the large square endpoint M(X_R). Because C_R is dominated by -M(X_R), the same alignment makes -2 C_R U_R positive. The daughter-only term remains strongly negative at the two principal maxima. This is not an independent daughter cancellation mechanism; at the observed extremes it is an endpoint Mertens excursion with a smaller coherent low-daughter echo.

The 58 high roots occur in the exact finite ranges

```text
244;
547-548; 582; 589-590; 592; 596-597; 599;
2545-2548; 3588; 3591; 5537-5567;
5933-5934; 5937-5942; 5997-5999.
```

The long 5537-5567 run shows that the R=5561 maximum is not an isolated divisibility accident. It is one square-endpoint excursion persisting across adjacent roots.

**Classification:** FINITE_COMPUTATION on exactly 5,945 roots. No all-scale sign law or uniform constant is claimed.

## B. Exact extremal certificates

### Discovery maximum R=244

```text
X=59535, K=3/2
M(R-1)=-2, M(X)=-102, C=100
U=-38641/5005 = -7.720479520479...
E=387
B=539141/5005 = 107.720479520479...
```

The exact decomposition is

```text
parent   C^2                         = 10000
cross   -2 C U                      = 1545640/1001
daughter U^2-(9/4)E                 = -81276729551/100200100
total                                = 1075442834449/100200100
c_244                                = 1075442834449/8948269730400
                                     = 0.12018444535655791...
```

### Held-out maximum R=5561

```text
X=30924720, K=3/2
M(R-1)=5, M(X)=-2544, C=2549
U=-121.191365728089...
E=196306
B=2670.191365728089...
```

The three terms in (1) are

```text
parent    6497401
cross      617833.5824817983...
daughter  -427001.1528729606...
total      6688233.429608838...
c_5561        0.14418310472084428...
```

The exact rational c_5561 certificate is

```text
66838291945221319077959121489647498093779364752678225527051739
/
463565353753674854665641846788595265866041977871076910254306225.
```

This independently reproduces PR #1021's reported maximum while adding the exact hidden-variable decomposition.

## C. Falsification and surviving conjecture

The natural sign claim

```text
c_R > 0  implies  C_R U_R < 0
```

is false. Its smallest failure in the authorized R >= 56 range is R=57:

```text
X=3248, K=3/2
C=-19, U=-71/105, E=3
c_57=14509429/214921350 = 0.06751041252997898...
C U > 0.
```

Across 56 <= R <= 6000, 3,577 roots have c_R > 0: 2,832 are anti-aligned and 745 are same-sign. Therefore anti-alignment is not necessary for a positive boundary payment.

The stronger held-out statement remains a precise conjectural inverse classifier:

> **CORR4 extreme-alignment conjecture.** For every R >= 56 with c_R > 1/10, one has C_R U_R < 0 and U_R M(R^2-1) > 0.

Tested range: 56 <= R <= 6000. Strongest current falsification attempt: exhaustive exact-rational search on all roots in that domain, including the held-out block 2001..6000; no violation. Status remains CONJECTURE. The threshold 1/10 is diagnostic, not asserted optimal or intrinsically canonical.

A more proof-relevant next theorem would not use the empirical threshold. It would classify when U_R aligns with M(X_R) in terms of shared q^2 ancestry of the daughter cutoffs, and would quantify the maximal amplifying cross term -2 C_R U_R. Without such new arithmetic information, the existing Young comparison only rehouses an endpoint bound.

## D. Methods and independent checks

New reproducer:

```text
python /workspace/corr4_hidden_variable.py --max-root 6000 --train-end 2000
```

Script SHA-256:

```text
404855ce5e84be9d82c6cdb5ab2673968eb0db8542888e9c61db9d480982dde7
```

Output was exact for all reported U_R, K_R, decompositions and comparisons using Python Fraction. The Mobius and prefix Mertens arrays were produced by a linear smallest-prime-factor sieve. Values were checked to lie in {-1,0,1}.

A second implementation computed M(n) only from the grouped exact recurrence

```text
M(n) = 1 - sum_(k=2)^n M(floor(n/k)),
```

grouping equal quotients and sharing no Mobius table. It checked all distinct Mertens arguments used at R=244 (7 points) and R=5561 (22 points), with zero mismatches. The extremal values also agree with PR #1021's separate standard-library/Numba computations.

Environment: CPython 3.12.13, exact integers/rationals, no random seed, no floating comparison used to select or certify maxima. Decimal values above are display-only.

## E. Upstream claim and proof impact

Today's Wheel claim 20261025-wheel-1, blob 414415d53bfedd14ae9b72ed3cc55f65c1477a21, proves on paper the sharper prime-owner frame

```text
sum_(q odd prime) 1/q^2 <= 9769/44100
```

by retaining q=3,5,7 and excluding the impossible composite owner 9 before telescoping. This improves deterministic CORR4 recurrence constants, but it does not change the exact census quantities U_R, E_R, B_R or c_R and does not pay the open physical-remainder inequality. The new extreme decomposition is compatible with that sharpening: a smaller upper frame for U_R does not remove the observed endpoint dominance.

PR #1021 already proves conditional and exact structural arrows, including the complete weighted physical kernel and first-owner Gram equivalence. This census supplies no missing uniform estimate. Its proof impact is negative but useful:

1. a daughter-only or sign-necessity argument is refuted;
2. the largest finite bills are controlled by square-endpoint Mertens excursions;
3. any claimed CORR4 advance should be stress-tested on full excursion runs, not only at R=244 or R=5561;
4. a genuinely new theorem must restrict endpoint/daughter sign coherence or bound the complete first-owner Gram from arithmetic structure, rather than invoke the reciprocal frame alone.

Canonical VF, CORR4, finite A/C, MU-LIFT gain and RH remain OPEN.

## F. Provenance and continuity

Authority fetched at this run:

- main commit 8d3a06d3748282e7e7e5cd273efdd00560cdee15;
- AGENTS.md blob fe049350c3d6a20096322a2c09c3993c2037022b;
- CURRENT_PROOF_CONTRACT.md blob 93314aebfcc326b27aa5835bd33a23a76923016b;
- portfolio blob 278cf50c25e30227021f34371932b1edd5e164bd;
- overlap / imported-7/8 audit blob c0002af0c26e0e2dff25758a4bc14c38a76f0822;
- dynamic protocol blob ff674b509cbdb67aebf635e0d9d5388c08967f12;
- external handoff index blob 038018145c0fddb2f6306c0712373adf9cd1ea52;
- main GLOBAL_RETURNED_CORE_SYNTHESIS.lean blob cbe96738432c71b89f0361fc4a6c14d0b3bb4001;
- main STABLE_FAR_PERRON_BASEL_FRAME_SHARPENING.lean blob e86617a02d18071ee9e73edc004937484e1a0447.

PR #1021 inputs inspected at final head 58be641ddb0c6cd003e4b61f760113ab254fbf11:

- census script blob 821891079cd988f23e1877065cc10b7005a0a929;
- research note blob 644223a581a531e626f451382a509d5f717de0e5;
- restored physical kernel blob a71d24ee7660f425c0ae7d8918f30c1eea94f313;
- relaxed remainder Lean blob a45f0f60d65a0cbbb0918823d8f7be4daf9d97e2;
- power/Gram equivalence blob 49a3ecb8fbb934d58c1d171ce1cc0275f1e6c8b9.

Today at intake: Wheel was available as the blob above. Coordinator, Owner, Analytic, Referee and Lean were TODAY=PENDING. This Census file was absent and is created by this run.

Yesterday carried forward:

- Coordinator blob 30942030c85ea079c0faacf97f2360cb77aca179, claim 20261024-coordinator-1;
- Owner blob 3d5a94fdfc2da9b4918c9f9643582060f2105c92, claim 20261024-owner-1;
- Analytic blob c90beb4c1b5e2ad64e31ec8bc1dda6d36aede6d7, claim 20261024-analytic-1;
- Wheel blob d7b956ad3e9f6e27e86644b371f275818a7516fd, claim 20261024-wheel-1;
- Census blob 04e90ce7bc531cf06be8fe0418477f4627bd625e, claim 20261024-census-1;
- Referee blob 8400b8ee3b8e6b68d2fb16ff6ffef395bf5dcca7, claim 20261024-referee-1;
- Lean blob 844b0cc6e49471469e60d9aa362744743c613740, then CI_PENDING.

The external inbox has no entry newer than October 18. EXT-20261018-PNT-1/2 remain secondary and do not pay this CORR4 bill.

## G. Live GitHub and CI audit

Final observed state:

- PR #1021 is OPEN, non-draft, unmerged, head 58be641ddb0c6cd003e4b61f760113ab254fbf11. All 13 pull-request workflow runs returned completed/success, including CORR4 OAI relaxed physical remainder run 40162570279 and OpenAI complete 7/8 square-block run 40162570315.
- PR #1022 is OPEN/DRAFT, unmerged, head 714a1b5bdd64bbb62eff7215712758bc1213a93b. All 12 observed pull-request workflow runs returned completed/success, including Original OAI low Gaussian nonresonant zero-mode certificate run 40166316569.
- Empty combined-status arrays do not add separate status contexts; conclusions above are from the associated workflow runs.
- No workflow was rerun. No PR, review, issue, source branch, main file, schedule or permission was changed.

Green CI certifies declarations on those exact heads only. Neither PR supplies an unconditional new CORR4 bound or RH.

## H. Continuation checkpoint

Do not repeat the 56..6000 exact census.

Next falsification step:

1. pre-register 6001..10000 as a second holdout for the extreme-alignment conjecture;
2. enumerate maximal contiguous c_R excursion runs, not just isolated record roots;
3. for each run, decompose U_R by q and condition on sign(M(Y_q)), q, and shared q^2 ancestry;
4. seek the smallest root with c_R > 1/10 but C_R U_R >= 0 or U_R M(X_R) <= 0;
5. if none appears, formulate an arithmetic sufficient condition for endpoint/daughter sign coherence and try to prove or refute it independently of a Mertens bound.

The theoretical target is a deterministic restriction on the sign-coherent cross term -2 C_R U_R or on the complete first-owner Gram. A larger table without that classifier is low value.

**Final classification:** FINITE_COMPUTATION and REFUTED local sign necessity, with a sharply stated held-out CONJECTURE. NO_NEW_GLOBAL_QUANTITATIVE_BOUND.


## I. Publication verification

Initial publication commit: 5a473954883403c771cb4fd07883a465488aeef5. Immediate readback returned blob 30167666c70c29cf023e67f5694b38c542080d81, 11,791 characters, with claim 20261025-census-1 and the final evidence classification present. This verifies report publication only; it does not certify a global inequality, alter main, or change the human merge gate.

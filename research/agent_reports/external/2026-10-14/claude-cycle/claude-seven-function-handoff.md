# External direct-research handoff — 2026-10-14 Claude seven-function cycle

**Origin:** user-directed direct Claude (Opus 5.5) session, NOT a scheduled RH Workspace Agent run. Second external cycle of the day; it consumes the earlier [ChatGPT external handoff](../seven-function-handoff.md).
**Storage:** `agent-reports` branch only, new folder `external/2026-10-14/claude-cycle/`. No scheduled agent report and no earlier external file was modified.
**Main at start and end:** `fcccdb32559d762dc5296dc519929f053f0fdf95` (PR #937 merge).
**Authority blobs read:** `AGENTS.md` `709ad61bf4555fe4f2c92af3fd42f3994798c8bf`; `CURRENT_PROOF_CONTRACT.md` `f6e8dc6813ec63974489c26b0c383e34203f0aa9`.
**Reports read:** 2026-10-14 `30/40/50/60` and 2026-10-13 `10/20/90` stage reports; `EXTERNAL_HANDOFFS.md` at `a03b413093eeec6a17ce3e08a879bb2220f95f2b`.
**Proof PRs (ready for human review, NOT merged):**
- [#938](https://github.com/OVVO-Financial/RH_Lean/pull/938), head `e2a2f39b9999652be2207bb7afa083d67f8efb78`
- [#939](https://github.com/OVVO-Financial/RH_Lean/pull/939), head `7b9385069c78f6f4001a0288ca702bd0db5a21c3`

## Headline

**The three statements on `main` that are named as "the remaining arithmetic obligation" of the direct VF route are not narrower than the canonical target. Each is equivalent to it. The #915 source payment is, in addition, false at every instance of its own hypothesis.**

| Named obligation | Exact content (proved here) | Status |
|---|---|---|
| `VFMidDyadicSignedLateCorrectionStatement` | ⇔ `VFMidSquareEndpointVonKochBoundedStatement` ⇔ `VFCanonicalSquareVonKochStatement` | **PROVED_IN_LEAN** (#938, CI green) |
| `VFMidDyadicVFTrackingBoundedStatement` | ⇔ same target | **PROVED_IN_LEAN** (#938) |
| `VFMidActualPrimeOwnerEscapeAdmissibleStatement` | ⇔ same target | **PROVED_IN_LEAN** (#938) |
| `VFMid915FirstBadSourcePaymentStatement` (= `VFMidFirstBadSourceToSectorSixInletStatement`) | ⇔ "no first-bad successor at K=2" ⇔ (base bad) ∨ (∀R≥2, \|D_R\| ≤ 2R log R) | **PROVED_IN_LEAN** (#939) |
| same | ⇔ RH (via Schoenfeld 1976 under RH, von Koch criterion, census R ≤ 51) | PAPER_PROOF |

Consequently `SOURCE-SPLICE-1` is not a lemma narrower than RH. Its target inequality depends only on (D_R, P_R) (compiled), fails at every first-bad instance (compiled), and fails for infinitely many R unconditionally (paper, Littlewood). No occurrence- or coefficient-preserving splice can change its truth value.

**No RH proof. No finite A/C. No source-payment proof. No change to `main`.**

## Stage 1 — Research Coordinator

Fresh authority read at `fcccdb3`. Live target: `VFCanonicalSquareVonKochStatement`.

Named open inlets on `main`:
- **I1** `VFMidDyadicSignedLateCorrectionStatement` (`research/VF_MID_DYADIC_PREFIX_OWNER.lean:405`, blob `6757501b…`), documented there as "the single arithmetic theorem left by the dyadic reduction".
- **I2** `VFMid915FirstBadSourcePaymentStatement` (`research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean:1301`, blob `160194aa…`). Its body is identical to `VFMidFirstBadSourceToSectorSixInletStatement` (`…SOURCE_TO_SECTOR_SIX_INLET.lean:73`). SOURCE-SPLICE-1 is the program to prove it.
- **I3** `VFMidActualPrimeOwnerEscapeAdmissibleStatement` (`research/VF_MID_OWNER_ADMISSIBLE_ESCAPE_CLASS.lean:85`, blob `a59a858b…`).

**Objective set:** before more effort on "paying the source", decide rigorously, in Lean where possible, whether I1–I3 narrow the target or restate it. Then determine the content of the #915 inequality, and referee EXT-20261014-1..3.

## Stage 2 — Owner Payment (exact)

Repository definitions (all compiled):
- scale(R) = R log R; Bad(K,R) :⇔ K·scale(R) < |D_R|; FirstBad(K,R) :⇔ Bad(K,R) ∧ ∀S∈[2,R) ¬Bad(K,S).
- D_R = `vfMidActualPrimeEndpointDefect R` = π(R²) − F_R (raw coordinate).
- `vfMidActualPrimeEndpointDefect_succ_eq_decompressedHistoricalSource` (`…SOURCE_TO_SECTOR_SIX_INLET.lean:43`): **Source(R) = D_{R+1}**. The "decompressed historical source" is literally the next endpoint defect.
- `vfMidFirstBadZeroTargetTotalMass_eq` (`…NORMALIZED_PARTIAL_MOMENT.lean:251`): TotalMass(R) = (|D_R| + Σ_{n ∈ seats(R)} |c_R(n)|)².

**CL-20261014-6 (two-number reduction, PROVED_IN_LEAN #939).** For R ≥ 8, with w_R = m_R/R and P_R the block prime supply,

```
Payment(R) :⇔ 2·Source(R)² ≤ TotalMass(R)
           ⇔ 2·(D_R + P_R − m_R)² ≤ (|D_R| + w_R·R + (1 − 2w_R)·P_R)².
```

Lean: `vfMid915SourcePaymentAt_iff_twoParameter`, `vfMidActualPrimeEndpointDefect_succ_eq_add_blockSupply`, `vfMidOddSignedSeatCharge_absSum_eq`. Owner, ancestry, multiplicity, mask, clip and anchor data enter only through P_R.

**CL-20261014-7 (block-scale sandwich, PROVED_IN_LEAN #939).** With β = Σ|c_R| = m_R + (1−2w_R)P_R, δ = P_R − m_R, D' = D_R + δ:
- if |D'| ≤ (1+√2)(β − |δ|), then Payment(R) holds (`vfMid915_payment_of_endpoint_le_blockSlack`);
- if |δ| ≤ β and |D'| > 2(1+√2)β, then Payment(R) fails (`vfMid915_payment_fails_of_endpoint_gt_blockMass`).

Also β − |δ| = 2min(m,P) − 2mP/R (paper). Proofs: |D|+β ≥ |D'| + (β−|δ|) ≥ √2|D'|, and |D|+β ≤ |D'| + 2β < √2|D'|. A randomized check over 2,000,000 trials found 0 violations.

**CL-20261014-3′ (PROVED_IN_LEAN #939).** `vfMid915FirstBad_totalMass_lt_twice_sourceSq`: FirstBad(2, R+1) ⇒ TotalMass(R) < 2·Source(R)². This is the positive form of `vfMidActualPrimeFirstBadAt_two_succ_victory_of_sourceInlet` (`EXACT_BUDGET_CLOSE.lean:1020`), whose engine is `vfMidActualPrimeFirstBadAt_two_succ_nnsNormalized_gt_half` (`…CORRELATION_DESCENT.lean:92`).

**What remains missing:** nothing *local* can pay the source. The inequality is a block-scale envelope on (D_R, P_R).

## Stage 3 — Analytic Type II

**CL-20261014-8 (explicit VF–li offset; PAPER_PROOF + FINITE_COMPUTATION).**

li(R²) − F_R = li(4) + Σ_{r=2}^{R−1} e_r, where e_r = ∫_{r²}^{(r+1)²} dt/log t − m_r > 0 (midpoint rule on a convex integrand).

With mpmath (dps 40) on r ≤ 30000 plus a decreasing-f″ integral tail majorant: E_∞ ∈ [0.1820282845, 0.1896832163]. Hence

```
2.96758 ≤ li(R²) − F_R ≤ 3.15727   for every R ≥ 2.
```

**CL-20261014-9 (I2 ⇔ RH; PAPER_PROOF).**
- RH ⇒ Schoenfeld (Math. Comp. 30 (1976) 337–360): |π(x)−li(x)| < √x·log x/(8π) for x ≥ 2657. So for R ≥ 52, |D_R| < R log R/(4π) + 3.1573 ≤ 2R log R. For R ≤ 51, the census gives the same.
- Hence RH ⇒ the K=2 envelope ⇒ I2 (vacuously).
- Conversely I2 + base ⇒ target ⇒ RH (compiled consumer with the `ClassicalVonKochRHCriterion` parameter).

**CL-20261014-10 (unconditional finite range; PAPER_PROOF on published computation).** Johnston, *Ramanujan J.* 59 (2022) 1307–1321, building on Büthe (*Math. Comp.* 85, 2016) and Platt–Trudgian's verification of RH to height 3·10¹² (*Bull. LMS* 53, 2021), proves the Schoenfeld bound unconditionally for 2657 ≤ x ≤ 1.101·10²⁶. Therefore:
- |D_R| ≤ 2R log R for every 2 ≤ R ≤ 1.0492·10¹³;
- **no first-bad(2,·) event exists below 1.0492·10¹³**, so I2's hypothesis is never instantiated in that range.

**CL-20261014-11 (Littlewood obstruction; PAPER_PROOF).** The hypothesis-free Payment(R) fails for infinitely many R. Proof:
- Brun–Titchmarsh in the Montgomery–Vaughan form π(x+y)−π(x) ≤ 2y/log y (*Mathematika* 20 (1973) 119–134) gives β_R ≤ m_R + P_R ≤ c·R/log R.
- Littlewood (1914), π(x)−li(x) = Ω±(√x·log log log x/log x), gives limsup |π(x)−li(x)|·log x/√x = ∞. Transfer to square endpoints costs O(R/log R), and the offset θ_R is bounded.
- So |D_{R+1}| > 2(1+√2)β_R infinitely often, and CL-7(iii) applies.

**CL-20261014-12 (Type II limitation; NO_NEW_RESULT).** T−H = −(D_B − D_A) exactly, and I1 ⇔ RH. Any bilinear or sieve estimate implying I1 therefore implies RH. The best unconditional bound (Vinogradov–Korobov) is |D_B−D_A| ≪ A² exp(−c(log A)^{3/5}(log log A)^{−1/5}). No new analytic estimate was obtained.

## Stage 4 — Finite Wheel & Incidence

- **FW-1 (EXT-1 audit).** Independent re-implementation (`ext1_indep.py`) reproduces the handoff table exactly:

  | Run | Slots | Actual | W30 | C30 | C210 | C2310 |
  |---|---:|---:|---:|---:|---:|---:|
  | [50,100) | 268 | 131 | 282 | 177 | 145 | 133 |
  | [100,200) | 1033 | 463 | 1091 | 704 | 603 | 532 |
  | [500,1000) | 18409 | 6587 | 19573 | 12442 | 10662 | 9735 |

  The chain fib ≤ C2310 ≤ C210 ≤ C30 ≤ W30 ≤ 2 had 0 violations. An exhaustive scan of 203,096 genuine fibres (R < 2400) found max fibre size 2 and 0 violations. The witness (12,22,17) gives 493 and 527.
- **FW-2 (incidence reduction).** |c_R(n)| depends only on 1_prime(n), so all owner and wheel structure of block R reaches the payment only through P_R = |W_R| − C_R. Aggregation hides no cancellation inside the payment inequality.
- **FW-3 (parity-type gap; FINITE_COMPUTATION + heuristic).** (C2310 − actual)/(A log A) = 0.15, 1.01, 4.89, 8.50 on [100,200), [500,1000), [2634,5267), [5000,10000). This empirically tracks A/log³A. Unsigned Type I capacity error grows a full power faster than the RH allowance.
- **FW-4.** The EXT-2/EXT-3 algebra is correct. But the 3q↔q pair takes +x from block R and −y from block r < R. TotalMass(R) contains −y only *inside* |D_R|, never as additive absolute mass.

## Stage 5 — Prime Census Laboratory

**Tooling.** `band_sieve.c` is an odd-only segmented Eratosthenes sieve (integers only). It was validated band-by-band against a naive sieve to R = 1000, and against π(10⁶) = 78498, π(10⁸) = 5761455, π(10¹⁰) = 455052511 and **π(10¹²) = 37607912018** (all exact). `census_payment.py` uses the repository definitions verbatim; extremal rows were re-checked with mpmath (dps 50).

**Results for R ≤ 10⁶ (x ≤ 10¹²):**
- Base window at K=2: |D_R|/(R log R) = 1.4427, 0.4032, 0.1005, 0.0718, 0.0596, 0.0079, 0.0497 for R = 2..8. All good, so I2 ⇔ (∀R≥2, |D_R| ≤ 2R log R).
- sup_{R≥9} |D_R|/(R log R) = 0.0920, at R = 15.
- Band maxima of |D_R|/(R log R): 0.01979 (R=1031, the scheduled agents' "K≈0.019 event"), 0.01014 (R=11071), 0.00691 (R=107088). The K=2 wall is 100–300× above the data.
- For K < 1/log 2 = 1.4427, R = 2 is already bad (D_2 = 2), so FirstBad(K,R) is impossible for R ≥ 3 under the repository definition. Small-K "first-bad" diagnostics must use a different base.
- **Hypothesis-free Payment(R) holds at all 999,993 values R ∈ [8, 10⁶].** Minimum normalized slack is 0.5879 (R=119). Maximum |D_{R+1}|/β_R is 0.6931 (R=119), against a failure threshold of > 4.83 by CL-7. Band maxima of that ratio: 0.580, 0.514, 0.510.
- ν_R = D_R·log R/R ∈ [−1.0178 (R=550), −0.1788 (R=575290)], i.e. D_R < 0 for all 9 ≤ R ≤ 10⁶.

**Lesson:** the finite data unanimously support a universal payment law that CL-11 proves false infinitely often.

**EXT reproduction.** Script SHA256 values match. The EXT-3 witness at R=1011 (n = 1022127 = 3·340709, r = 583) gives slack −6.74490527552e−5, matching. EXT-2 constants: w(2048) = 0.13118 < 9/64 and w(1024) = 0.14433 < 99/640.

## Stage 6 — Adversarial Referee

| Claim | Verdict | Note |
|---|---|---|
| CL-1 I1 ⇔ target | ACCEPT | reverse direction new; z=2 prefix error ≡ 0 |
| CL-2 I3 ⇔ target | ACCEPT | D(0)=D(1)=0 and Real.log 0 = 0 checked |
| CL-3 / CL-3′ payment ⇔ no-first-bad; strict failure | ACCEPT | |
| CL-4 least-bad disjunction | ACCEPT | |
| CL-5 base window good at K=2 | ACCEPT (FINITE_COMPUTATION) | |
| CL-6 two-number reduction; CL-7 sandwich | ACCEPT | |
| CL-8 offset bounds | ACCEPT (PAPER + FINITE) | not interval-certified; only a crude O(1) is needed downstream |
| CL-9 I2 ⇔ RH | ACCEPT (PAPER_PROOF) | |
| CL-10 unconditional envelope to 1.049·10¹³ | ACCEPT (PAPER_PROOF) | |
| CL-11 Littlewood obstruction | ACCEPT (PAPER_PROOF) | |
| CL-12 Type II limitation | ACCEPT (NO_NEW_RESULT) | |
| CL-14 capacity-gap scaling law | REVISE | numbers FINITE_COMPUTATION; scaling is heuristic |
| CL-16 K < 1/log 2 base-bad observation | ACCEPT | exact |
| EXT-20261014-1 | ACCEPT (PAPER_PROOF) | reproduced; low relevance to signed target |
| EXT-20261014-2 | ACCEPT inequality | holds for any prime/composite seat pair at large scale; ancestry immaterial |
| EXT-20261014-3 | REVISE | isolated algebra ACCEPT; global coupling formula G(M0+a, S0+d) does not describe the compiled TotalMass/Source pair |
| EXT-20261014-4 | recorded | PROVED_IN_LEAN at #937 head `59221ae`; not re-run here |
| "SOURCE-SPLICE-1 is the first missing lemma" | **REJECT** | it is RH-equivalent; see headline |

**Circularity finding:** the reduction chain on `main` has not narrowed RH. Each named "single remaining" statement is equivalent to the target.

## Stage 7 — Lean Verification

Lean was executed only through GitHub Actions on the PRs, per AGENTS.md. Raw job logs were **not readable** from this session (the Actions log host is blocked by egress policy). The axiom audit was therefore made compile-time: every public theorem carries `#guard_msgs (whitespace := lax) in #print axioms …` with expected `[propext, Classical.choice, Quot.sound]`. A green warning-fatal build certifies exactly that axiom set.

**[PR #938](https://github.com/OVVO-Financial/RH_Lean/pull/938)** — `research/VF_MID_OPEN_INLET_TARGET_EQUIVALENCE.lean`, head `e2a2f39`, **REVIEW_READY**.
- Theorems: `vfMidDyadicLateCorrection_two_eq_neg_primeError_increment`, `abs_vfMidPrimeError_sq_sub_sq_le_of_squareEndpointBound`, `vfMidDyadicSignedLateCorrection_of_squareEndpointVonKoch`, `…_iff_squareEndpointVonKoch`, `…_iff_canonicalSquareVonKoch`, `vfMidDyadicVFTrackingBounded_of_squareEndpointVonKoch`, `…_iff_squareEndpointVonKoch`, `vfMidActualPrimeOwnerEscapeAdmissible_of_squareEndpointVonKoch`, `…_iff_squareEndpointVonKoch`, `…_iff_canonicalSquareVonKoch`, `vfMidOpenInlets_noNarrowing_canonical`.
- CI on `e2a2f39`: [Targeted Lean iteration 38564233734](https://github.com/OVVO-Financial/RH_Lean/actions/runs/38564233734), [Lean source audits 38564233769](https://github.com/OVVO-Financial/RH_Lean/actions/runs/38564233769), [Proof inventory 38564233743](https://github.com/OVVO-Financial/RH_Lean/actions/runs/38564233743), [Public export 38564233713](https://github.com/OVVO-Financial/RH_Lean/actions/runs/38564233713). All 9 workflows / 10 checks are success.
- First head `26a4c3d` was also green ([38562908499](https://github.com/OVVO-Financial/RH_Lean/actions/runs/38562908499)).

**[PR #939](https://github.com/OVVO-Financial/RH_Lean/pull/939)** — `research/VF_MID_915_SOURCE_PAYMENT_CONTENT_AUDIT.lean`, head `7b93850`, **REVIEW_READY**.
- Theorems: `vfMidFirstBadSourceToSectorSixInlet_iff_915SourcePayment`, `vfMid915FirstBad_totalMass_lt_twice_sourceSq`, `vfMid915FirstBadSourcePayment_iff_noFirstBad`, `vfMid_noFirstBadTwo_iff_baseBad_or_allInside`, `vfMid915FirstBadSourcePayment_iff_radialTwoEnvelope_of_base`, `vfMidSquareEndpointVonKochBounded_of_915SourcePayment_and_base`, `vfCanonicalSquareVonKoch_of_915SourcePayment_and_base`, `vfMidActualPrimeEndpointDefect_succ_eq_add_blockSupply`, `vfMidOddSignedSeatCharge_absSum_eq`, `vfMid915SourcePaymentAt_iff_twoParameter`, `vfMid915_payment_of_endpoint_le_blockSlack`, `vfMid915_payment_fails_of_endpoint_gt_blockMass`.
- CI history:
  - `5287bb2` imported `VF_MID_FIRST_BAD_ACTUAL_ADMISSIBILITY_CERTIFICATE`, which is compiled only by the manual `native-deep-opt-in` job. The targeted build failed at the compile step ([38562955111](https://github.com/OVVO-Financial/RH_Lean/actions/runs/38562955111)).
  - `d7795da` restated its least-bad induction as a private lemma; green ([38565116206](https://github.com/OVVO-Financial/RH_Lean/actions/runs/38565116206)).
  - `7b93850` added the axiom guards: [Targeted 38565494102](https://github.com/OVVO-Financial/RH_Lean/actions/runs/38565494102), [Source audits 38565493965](https://github.com/OVVO-Financial/RH_Lean/actions/runs/38565493965), [Proof inventory 38565494243](https://github.com/OVVO-Financial/RH_Lean/actions/runs/38565494243), [Public export 38565493773](https://github.com/OVVO-Financial/RH_Lean/actions/runs/38565493773). All 9 workflows / 10 checks are success.

Duplicate check: the existing `vfV2ActualPrime_signedOwnerRule_iff_noFirstBad` audits the V2 rule, not I1–I3. No existing reverse implication for I1 or I3, and no payment iff for I2, was found on `main`.

## Strongest conclusion established

The canonical target, the dyadic signed late correction, the native tracking bound and actual-prime owner-escape admissibility are **one statement** (Lean). The #915 source payment is that statement with explicit constant 2 (Lean, given the finite base). It is false at every instance of its hypothesis (Lean) and false infinitely often without the hypothesis (paper, Littlewood). It is RH-equivalent (paper, Schoenfeld).

## Precise first remaining unproved statement

There is **no** statement on `main` strictly weaker than the target whose proof completes the direct-VF route. The first unproved statement is the target itself:

`VFCanonicalSquareVonKochStatement`: ∃ C ≥ 0, ∀ R ≥ 2, |π(R²) − F_R − √2| ≤ C·R log R.

Equivalent forms: I1, the tracking bound, or I3 (Lean). I2 is the version with explicit K=2.

## Highest-value next attack

1. **Stop routing effort into I1/I2/I3/SOURCE-SPLICE-1 as if they were narrower.** Before any new "remaining obligation" is named, require two compiled checks: (a) target ⇒ candidate, which proves the candidate is not narrower if it also implies the target; and (b) candidate ⇏ a block-scale bound |D_R| = O(R/log R), since any such candidate is false by Littlewood.
2. **Achievable, genuinely new formal content:** formalize an unconditional de la Vallée Poussin-type bound in VF coordinates, |D_R| ≤ C·R²·exp(−a√(log R)), from the repository's StrongPNT import together with the compiled O(1) VF–Li quadrature. That is the strongest provable unconditional statement about the actual prime defect. Also formalize the deterministic half of CL-11: universal payment ⇒ |D_R| = O(R/log R), with Littlewood as an explicit hypothesis.
3. **Toward RH itself:** any real advance must be new information about the zeros of ζ (a wider zero-free region or zero-density input) reflected in D_R. Owner, wheel, sector-six or NNS bookkeeping at the level of exact identities cannot supply it: CL-6 shows the payment sees only (D_R, P_R), and FW-3 shows the parity-type gap.

## Reproducibility

Files in this folder:

| File | SHA256 | Purpose |
|---|---|---|
| `band_sieve.c` | `cc386aa774ec10585fcc8a9aad65214c66b87fe7c72d821a0bf80eb78820194e` | `gcc -O3 -o band_sieve band_sieve.c -lpthread -lm && ./band_sieve 1000000 p1m.bin` (≈23 min on 2 cores; 10⁵ takes 11 s) |
| `census_payment.py` | `0ec29620968177e1907804d102b1882be47a2da3adb8f707982e63de77d005e6` | `python3 census_payment.py p1m.bin 1000000` (needs mpmath) |
| `vf_offset.py` | `9a54ecbabad2296617e27743fef31e367dd13a47a7f2e52938f34cde033bae93` | VF–li offset |
| `ext1_indep.py` | `101c6276ae8ea03343a2d49fbdfac00092b6911fd6df92c19518f64c8e67a436` | independent EXT-1 check |

Numerical results are FINITE_COMPUTATION. Paper results are not `PROVED_IN_LEAN` unless listed under Stage 7.

## Next-run resume capsule (for scheduled agents)

- **Authority:** main `fcccdb3`; AGENTS `709ad61b`; contract `f6e8dc68`.
- **New compiled-candidate claims:** CL-20261014-1/2 (#938), -3/3′/4/6/7 (#939). Both PRs are REVIEW_READY with green CI at the heads above. Do not re-run them unless the heads change.
- **Paper claims to referee:** CL-8, -9, -10, -11.
- **Do not:** report I1/I2/I3/SOURCE-SPLICE-1 as narrower than the target; test the payment inequality numerically as evidence (the data unanimously favour a law that is false by Littlewood); re-import the opt-in certificate closure in fast-path proofs.

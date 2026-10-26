# RH_Lean formalization milestones

**Completed formal mathematics, in order, with exactly what each result does not prove.** RH remains OPEN. A completed reduction is a genuine achievement; it is not a proof of its open hypothesis. The machine-readable source is [proof-obligations.json](proof-obligations.json); the open obligations and route dependencies are in the [proof-dependency DAG](PROOF_DEPENDENCY_DAG.md). Snapshot: main `8d3a06d3748282e7e7e5cd273efdd00560cdee15`, Lean `v4.34.1`, observed 2026-10-25.

## 1. Major formalization milestone: von Koch (1901) and the canonical VF prime-counting criterion

**The classical theorem.** H. von Koch, *Sur la distribution des nombres premiers*, Acta Mathematica **24** (1901) 159–182, doi:10.1007/BF02403071, proved that RH implies π(x) = Li(x) + O(√x log x). Together with the classical converse (an error O(x^{1/2+ε}) continues the relevant Dirichlet series to Re s > 1/2), this is the criterion

  RH ⇔ π(x) − Li(x) = O(√x log x).

Normalizing by Li₂(x) = ∫₂ˣ dt/log t changes Li by the constant li(2) ≈ 1.04516 and does not change the criterion. Registry node: `HISTORICAL-VONKOCH-1901`.

**What RH_Lean proved in Lean (merged [#932](https://github.com/OVVO-Financial/RH_Lean/pull/932), 2026-10-12; head `2713d8ef495e`, 13 workflow runs / 17 jobs green, including warning-fatal compilation and `#print axioms` in [vf-canonical-sqrt-two.yml](../.github/workflows/vf-canonical-sqrt-two.yml)):**

1. **`MILESTONE-VF-CANONICAL` — one public canonical VF.** [`vfCanonical`](../research/VF_CANONICAL_SQRT_TWO.lean) x = vfMid x + √2, i.e. for x ≥ 4, R = ⌊√x⌋,
   VF_can(x) = √2 + Σ_{r=2}^{R−1} (2r+1)/log(r²+r+1/2) + (x−R²)/log((R²+x)/2),
   with the exact actual-prime square-block recurrence `vfCanonicalSquareDefect_succ` (D_{R+1} = D_R + (P_R − V_R)) and the split `vfCanonicalPrimeLiError_eq_primeError_add_quadrature`.
2. **`MILESTONE-VF-LI-O1` — VF_can(x) − Li₂(x) = O(1) for every real x ≥ 4.** [`abs_vfMidLiError_le_uniform_allReal`](../research/VF_CANONICAL_ALL_REAL_LI_O_ONE.lean), [`vfMidLiAllRealUniformBounded`](../research/VF_CANONICAL_ALL_REAL_LI_O_ONE.lean), [`abs_vfCanonicalLiError_le_uniform_allReal`](../research/VF_CANONICAL_SQRT_TWO.lean). Unconditional elementary quadrature; strictly stronger than the root-scale bound the reduction needs.
3. **`MILESTONE-VONKOCH-VF-LEAN` — classification `FORMALIZED_CANONICAL_VONKOCH_REDUCTION`.** With renormalized nonnegative constants,
   (∃C ∀R ≥ 2, |π(R²) − VF_can(R²)| ≤ C R log R) ⇔ (∃C′ ∀x ≥ 4, |π(x) − Li₂(x)| ≤ C′ √x log x),
   via [`vfCanonicalSquareVonKoch_iff_primeLiVonKoch`](../research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean), `vfCanonicalRealVonKoch_iff_primeLiVonKoch`, `vfCanonicalSquareVonKoch_iff_realVonKoch`, `vfCanonicalRealVonKoch_iff_legacy`, `vfCanonicalSquareVonKoch_iff_legacy`, and the legacy [`vfMidVonKochBounded_iff_primeLiVonKochBounded`](../research/VF_MID_VON_KOCH_BRIDGE.lean), `vfMidSquareEndpointVonKochBounded_iff_primeLiVonKochBounded`, `vfMidVonKochBounded_of_squareEndpoint`. The conditional consumers [`riemannHypothesis_of_vfCanonicalSquare`](../research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean) and `riemannHypothesis_of_vfMidSquareEndpoint` conclude Mathlib's `RiemannHypothesis`.

**Exact limitation.** The classical analytic theorem is supplied as the explicit argument

```lean
structure ClassicalVonKochRHCriterion where
  iff_riemannHypothesis :
    PrimeLiVonKochBoundedStatement ↔
      VFMidRiemannHypothesisStatement
```

(`IFACE-CLASSICAL-VONKOCH`). The repository does not construct it; doing so is the formalization-completeness task `CLASSICAL_VONKOCH_CRITERION_FORMAL_IMPORT_OR_PROOF`, which is not a new conjecture and does not touch the open arithmetic estimate. Therefore:

- the VF-to-classical prime-error equivalence is proved in Lean;
- the uniform VF − Li₂ bound is proved in Lean;
- the historical classical criterion is an explicit theorem parameter;
- the actual-prime bound `OPEN-VF-ACTUAL-PRIME` (`VFCanonicalSquareVonKochStatement`: ∃C ∀R ≥ 2, |π(R²) − VF_can(R²)| ≤ C R log R) is **open**;
- RH is not proved.

`#print axioms` reports logical axioms only; it does not remove ordinary hypotheses such as `ClassicalVonKochRHCriterion` or `VFCanonicalSquareVonKochStatement`.

## 2. Chronological milestone table (generated)

<!-- BEGIN GENERATED: milestones -->
| Order | Date | Milestone | Status | Lean declarations | PR | Does not prove |
| --- | --- | --- | --- | --- | --- | --- |
| 0 | 1901 | `HISTORICAL-VONKOCH-1901` — von Koch prime-counting criterion (1901) | EXPLICIT_LEAN_INTERFACE | [`ClassicalVonKochRHCriterion`](../research/VF_MID_VON_KOCH_BRIDGE.lean) | — | Any arithmetic estimate on actual primes; The Riemann Hypothesis |
| 1 | on main (introduction date not re-verified) | `CONSUMER-MERTENS-ENERGY-RH` — Mertens energy => RH (proved internally) | PROVED_IN_LEAN_ON_MAIN | [`riemannHypothesis_of_mertensEnergy`](../RHLean/Analysis/MertensEnergyRHForward.lean)<br/>[`riemannZeta_ne_zero_of_half_lt_re`](../RHLean/Analysis/MertensEnergyRHForward.lean) | — | — |
| 2 | 2026-10-12 | `MILESTONE-VF-CANONICAL` — Canonical square-block VF definition | PROVED_IN_LEAN_ON_MAIN | [`vfCanonical`](../research/VF_CANONICAL_SQRT_TWO.lean)<br/>[`vfCanonical_eq_legacy_plus_sqrt_two`](../research/VF_CANONICAL_SQRT_TWO.lean)<br/>[`vfCanonicalSquareDefect_succ`](../research/VF_CANONICAL_SQRT_TWO.lean)<br/>[`vfCanonicalPrimeLiError_eq_primeError_add_quadrature`](../research/VF_CANONICAL_SQRT_TWO.lean) | [#932](https://github.com/OVVO-Financial/RH_Lean/pull/932) | Any bound on pi - VF_can; Pointwise optimality of the sqrt2 phase |
| 3 | 2026-10-12 | `MILESTONE-VF-LI-O1` — VF_can - Li_2 = O(1) on the whole real continuum | PROVED_IN_LEAN_ON_MAIN | [`abs_vfMidLiError_le_uniform_allReal`](../research/VF_CANONICAL_ALL_REAL_LI_O_ONE.lean)<br/>[`vfMidLiAllRealUniformBounded`](../research/VF_CANONICAL_ALL_REAL_LI_O_ONE.lean)<br/>[`abs_vfCanonicalLiError_le_uniform_allReal`](../research/VF_CANONICAL_SQRT_TWO.lean) | [#932](https://github.com/OVVO-Financial/RH_Lean/pull/932) | Any bound on pi - VF_can or pi - Li_2; The Riemann Hypothesis |
| 4 | 2026-10-12 | `MILESTONE-VONKOCH-VF-LEAN` — Canonical VF square endpoint <=> classical prime-Li von Koch bound | PROVED_IN_LEAN_ON_MAIN | [`vfCanonicalSquareVonKoch_iff_primeLiVonKoch`](../research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean)<br/>[`vfCanonicalRealVonKoch_iff_primeLiVonKoch`](../research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean)<br/>[`vfCanonicalSquareVonKoch_iff_realVonKoch`](../research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean)<br/>[`vfCanonicalRealVonKoch_iff_legacy`](../research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean)<br/>[`vfCanonicalSquareVonKoch_iff_legacy`](../research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean)<br/>[`vfMidVonKochBounded_iff_primeLiVonKochBounded`](../research/VF_MID_VON_KOCH_BRIDGE.lean)<br/>[`vfMidSquareEndpointVonKochBounded_iff_primeLiVonKochBounded`](../research/VF_MID_VON_KOCH_BRIDGE.lean)<br/>[`vfMidVonKochBounded_of_squareEndpoint`](../research/VF_MID_VON_KOCH_BRIDGE.lean) | [#932](https://github.com/OVVO-Financial/RH_Lean/pull/932) | The actual-prime endpoint estimate OPEN-VF-ACTUAL-PRIME; The independent classical von Koch-to-RH analytic theorem (IFACE-CLASSICAL-VONKOCH is an explicit argument); The Riemann Hypothesis |
| 5 | 2026-10-12 / 2026-10-14 | `CONSUMER-915-CANONICAL` — #915 payment + base window => canonical target | PROVED_IN_LEAN_ON_MAIN | [`vfCanonicalSquareVonKoch_of_915SourcePayment_and_base`](../research/VF_MID_915_SOURCE_PAYMENT_CONTENT_AUDIT.lean)<br/>[`vfMid915FirstBadSourcePayment_iff_noFirstBad`](../research/VF_MID_915_SOURCE_PAYMENT_CONTENT_AUDIT.lean)<br/>[`vfMid915FirstBad_closed_of_sourcePayment`](../research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean) | [#915](https://github.com/OVVO-Financial/RH_Lean/pull/915) | — |
| 6 | 2026-10-15 | `MILESTONE-MERTENS-CONVERSE` — Bidirectional Mertens growth / zero-boundary identification (#949) | PROVED_IN_LEAN_ON_MAIN | [`growthAtMost_iff_strip`](../research/MERTENS_CONVERSE_IDENTIFICATION.lean)<br/>[`growthExponent_eq_rightmost`](../research/MERTENS_CONVERSE_IDENTIFICATION.lean)<br/>[`logLimsup_eq_rightmost`](../research/MERTENS_CONVERSE_IDENTIFICATION.lean) | [#949](https://github.com/OVVO-Financial/RH_Lean/pull/949) | Any numerical value of the common boundary |
| 7 | 2026-10-15 | `MILESTONE-MERTENS-SIGNED-LIFT` — Signed higher-order Newton/Heath-Brown lift (#954) | PROVED_IN_LEAN_ON_MAIN | [`heathBrownLift_agrees_below_power`](../research/MERTENS_HEATH_BROWN_SIGNED.lean) | [#954](https://github.com/OVVO-Financial/RH_Lean/pull/954) | An amplitude estimate E(B^k) <= G E(B)^r |
| 8 | 2026-10-16 | `MILESTONE-958-ODD-RESIDUAL` — Sharp odd residual cofactor support (#958) | PROVED_IN_LEAN_ON_MAIN | [`nine_mul_canonicalLargestPrimeFactor_lt_sq`](../RHLean/Proof/OddResidualCofactorSupport.lean) | [#958](https://github.com/OVVO-Financial/RH_Lean/pull/958) | A signed-weight bound; Returned-cell admission |
| 9 | 2026-10-16 | `MILESTONE-961-COMPLETE-FIBRE` — Complete greatest-prime fibre above the root wall (#961) | PROVED_IN_LEAN_ON_MAIN | [`completeFibre_of_root_le`](../RHLean/Proof/RootWallCompleteFibre.lean)<br/>[`largestPrimeFactor_eq_iff_exists_mul_of_root_le`](../RHLean/Proof/RootWallCompleteFibre.lean) | [#961](https://github.com/OVVO-Financial/RH_Lean/pull/961) | A native signed or covariance estimate |
| 10 | 2026-10-21 | `IMPORTED-OAI-7-8` — Imported original OpenAI unconditional 7/8 theorem (#987) | PROVED_IN_LEAN_ON_MAIN | [`openai434_actual_zeta_nonzero`](../research/VF_919_OPENAI_434_UNCONDITIONAL_SQUARE_BLOCK_COVARIANCE_20261019.lean)<br/>[`openai434_actual_global_signed_covariance`](../research/VF_919_OPENAI_434_UNCONDITIONAL_SQUARE_BLOCK_COVARIANCE_20261019.lean)<br/>[`openai434_actual_global_signed_pairs`](../research/VF_919_OPENAI_434_UNCONDITIONAL_SQUARE_BLOCK_COVARIANCE_20261019.lean)<br/>[`openai434_actual_all_square_blocks_seven_eighths`](../research/VF_919_OPENAI_434_UNCONDITIONAL_SQUARE_BLOCK_COVARIANCE_20261019.lean)<br/>[`openai434_actual_all_square_block_covariance`](../research/VF_919_OPENAI_434_UNCONDITIONAL_SQUARE_BLOCK_COVARIANCE_20261019.lean) | [#987](https://github.com/OVVO-Financial/RH_Lean/pull/987) | An independent native reproduction of the OpenAI analytic estimates; Any exponent strictly below 7/8; RH |
| 11 | 2026-10-24 | `MILESTONE-OAI-HEAVY-SLOT` — Original OAI fixed heavy-slot two-channel split (#1017) | PROVED_IN_LEAN_ON_MAIN | [`Fiber.exists_heavy_slot`](../research/oai_434/VF919OriginalFiberHeavySlotSplit.lean)<br/>[`Fiber.exists_heavy_slot_with_two_channel_sum`](../research/oai_434/VF919OriginalFiberHeavySlotSplit.lean) | [#1017](https://github.com/OVVO-Financial/RH_Lean/pull/1017) | A uniform source moment gap (heavy-slot weight is only >= 7/(37\|S\|)) |
| 12 | 2026-10-24 | `MILESTONE-1019-BIRTH-TRANSPORT` — Closed-square Mobius birth time and moving transport (#1019) | PROVED_IN_LEAN_ON_MAIN | [`closedSquareShell_birthTime_floor_eq_two_mu_sub_mu_sq`](../research/VF_MID_CLOSED_SQUARE_BIRTH_TIME_20261024.lean)<br/>[`closedSquareShellFloor_eq_open_add_rootDivisor`](../research/VF_MID_CLOSED_SQUARE_BIRTH_TIME_20261024.lean)<br/>[`closedSquareShell_actual_moving_transport_telescope`](../research/VF_MID_CLOSED_SQUARE_MOVING_TRANSPORT_20261024.lean) | [#1019](https://github.com/OVVO-Financial/RH_Lean/pull/1019) | A quantitative bound; An occurrence map to prime/floor-Li events or the weighted #915 source |
<!-- END GENERATED: milestones -->

## 3. Notes on the other milestones

- **Mertens energy ⇒ RH, proved internally (library module on main; introduction date not re-verified).** [`riemannHypothesis_of_mertensEnergy`](../RHLean/Analysis/MertensEnergyRHForward.lean) needs no classical interface: the Mellin continuation is proved in the library. This is why the FINITE-AC, CORR4, MU-LIFT, CODIV and OAI-NNS routes have no literature condition on their final edge, unlike the von Koch route.
- **#915 / #939.** Merged #915 supplies the original first-bad toolkit and conditional consumer `vfMid915FirstBad_closed_of_sourcePayment`; merged #939's [content audit](../research/VF_MID_915_SOURCE_PAYMENT_CONTENT_AUDIT.lean) shows the payment statement is equivalent to the absence of first-bad successors and, with a finite base window checked outside Lean, to the explicit envelope |D_R| ≤ 2R log R, which implies the canonical target.
- **#949 / #954.** Bidirectional identification of the Mertens growth exponent with the rightmost zero boundary, and signed higher-order lift identities. Neither supplies a numerical exponent or an amplitude estimate.
- **#958 / #961.** Structural least-prime incidence results (one-ninth odd residual support; complete above-root fibre). No signed bound.
- **#983 (2026-10-20).** Build migration of the whole repository to Lean 4.34.1 (tracker compatibility); infrastructure, not mathematics. It made the #987 import possible.
- **#987 — imported OpenAI 7/8 (2026-10-21).** [`openai434_actual_zeta_nonzero`](../research/VF_919_OPENAI_434_UNCONDITIONAL_SQUARE_BLOCK_COVARIANCE_20261019.lean) and companions import the original unconditional Lean 4.34.1 proof (pinned `openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a`) and transport M(x) = O_ε(x^{7/8+ε}) to RH_Lean's genuine square-block covariance. Provenance: imported certified external Lean, not an independent native reproduction. No strict exponent below 7/8 has been verified.
- **#1017 / #1019 (2026-10-24).** Original OAI heavy-slot two-channel algebra; exact closed-square Möbius birth time `2μ(k) − μ(k)²` and moving transport. Structure only.

## 4. Formal work on open PRs (not on main)

Observed 2026-10-25 (#1021 re-checked 2026-10-26T00:15Z); refresh from GitHub before relying on these rows.

| PR | Head | Observed CI | Formal content | Scope |
| --- | --- | --- | --- | --- |
| [#1023](https://github.com/OVVO-Financial/RH_Lean/pull/1023) | `44fbcf3f2dca` | 12/12 jobs green, ready for review | Σ_{q odd prime ≤ N} 1/q² ≤ b₇ = 1565172113/7214407200 (`oddPrimeOwnerReciprocalSquareBudget_le_compositeGap`) | Finite arithmetic; with #1021's conditional wiring the CORR-4 coefficient becomes 3 + 4b₇ = 6975977513/1803601800 ≈ 3.8678 < 4. Not a remainder bound. |
| [#1022](https://github.com/OVVO-Financial/RH_Lean/pull/1022) | `03f756a4e495` | 13/13 jobs green, draft | Nonprincipal zero mode `actualCongruenceCoefficient_zero_mode_of_nontrivial` on the original low-Gaussian numerator | Source-local; the Z^{−1/64} Poisson band is a paper claim before outer costs. |
| [#1021](https://github.com/OVVO-Financial/RH_Lean/pull/1021) | `72d7e508ed13` | 5/14 jobs green, 9 running, 0 failed at 2026-10-26T00:15Z (previous head `daefa85975a6` failed *Targeted Lean iteration* and *CORR4 OAI relaxed physical remainder*) | Relaxed-remainder ⇒ CORR-4 wiring (coefficient 886/225 with the merged 211/900 frame) | Not counted as Lean-certified until a current head is green; the premise `LowOwnerPhysicalRelaxedRemainderBound` is open. |

## 5. What remains

Arithmetic, not formalization, is the bottleneck: every RH path in the [DAG](PROOF_DEPENDENCY_DAG.md#5-rh-paths-frontier-and-agents) still has an open arithmetic input. The single formalization-completeness item on the von Koch route is constructing `ClassicalVonKochRHCriterion`.

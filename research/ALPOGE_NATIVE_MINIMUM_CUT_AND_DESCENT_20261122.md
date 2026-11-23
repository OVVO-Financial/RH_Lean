# Native O_K-Lattice Descent, Window Landau, and the Zeta Minimum Cut

## Status and honest scope

This branch starts from native `main` (`719bdb01cf830090e29cdeecbb36fe89e91973d0`, merged PR `#1193`) and audits Alpöge's pinned release `CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4` strictly as a read-only blueprint. No external `.olean`, terminal RH theorem (`rhOfAll`), `sorry`, or synthetic axiom is imported or used.

**This does NOT prove the Riemann Hypothesis unconditionally.** It delivers two verified, self-contained native advances in ~3,600 lines of Lean 4.34.1:

1. **Number-field all-embedding integral descent + non-RH Arakelov corollaries** ([NativeNumberFieldIntegralDescent.lean](../RHLean/Geometry/NativeNumberFieldIntegralDescent.lean), 642 lines): lifts `#1193`'s Euclidean $\mathbb{Z}$-lattice descent to basis-presented free $\mathcal{O}_K$-lattices over totally complex number fields across all complex embeddings using the genuine product formula $\prod_\sigma \|\sigma(\det C)\| = |N_{K/\mathbb{Q}}(\det C)| \ge 1$, replacing an ~86k-line / 480-file closure in Alpöge's tree and proving standalone non-RH isogeny/endomorphism bounds (`isogeny_to_power`, `endomorphism_norm_bound`).
2. **End-to-end conditional native reduction to Mathlib's `RiemannHypothesis` from one-sided windows** (~3,000 lines total across `AlpogeWindowLandauCriterion`, `AlpogeNativeWindowMellin`, `AlpogeNativeWindowLandau`, `AlpogeNativeZetaBalance`, `AlpogeNativeZetaWindowWitness`, `AlpogeNativeZetaWindowRHBridge`): closes `RH_Lean`'s previously missing upward chain from `alpogeNativeCompleteProjection_at_constructed_cutoff` (`#1193`) through `alpogeNativeGzArithmetic` to Mathlib's `RiemannHypothesis`, replacing ~73k+ lines of upstream closures (`TopWin`, `Landau`, `zeroFree_of_rpow_window`, `core_gm`, `ch_top`).

### Explicit mathematical caveats

- **No witness is constructed** for `AlpogeNativeZetaWindowWitness`, and joint satisfiability of its ten fields is not proved here.
- **Degenerate host caveat:** Because `RH_Lean`'s native `ASK - MAIN = De` identity holds for arbitrary `inertia`, `frob`, and `ell`, choosing degenerate host data (e.g. `inertia = ⊤`, `ell = 0`) makes the `excluded` field trivial and turns `top` directly into an upper bound on `alpogeNativeGzArithmetic`. "CM-host facts" describes the intended physical supplier, not a syntactic constraint enforced by `AlpogeNativeZetaWindowWitness`.
- **Where the remaining difficulty lives:** On a genuine physical CM host, Field 10 (`top`, the $A_0$-mean of `ASK - MAIN`) is the open automorphic geometric estimate (supplied in Alpöge's proof by ~12.8M lines of chained theta lifts, Shimura/Galois representations `Row0b`, and Bessel/Poincaré periods `HypsAlt`), Field 9 (`excluded`) asks for root-scale control of up to three surviving nonprincipal characters, and Field 6 (`thin`) requires a prime number theorem with remainder for every host character (`supplyChi` / `VWinAt`).
- **Zeta-only vs. full GRH:** Source inspection confirms that restricting to $\zeta$ alone removes none of the three deep engines (`HypsAlt`, `Row0b`, `VWin`) in Alpöge's architecture—it shrinks `VWin` to `VWinAt PChar.one 401` and drops multi-character level bookkeeping, while keeping the CM host (`|H| ≥ √x`), its three real quadratic characters, and windows $[Y, Y^{1+\delta}]$ structurally forced.

---

## Verified module map

| Module | Lines | Role | Key declarations |
|---|---:|---|---|
| [NativeNumberFieldIntegralDescent.lean](../RHLean/Geometry/NativeNumberFieldIntegralDescent.lean) | 642 | All-embedding $\mathcal{O}_K$-lattice descent, spectral refinement, non-RH Arakelov corollaries | `det_credit`, `completed_image_bound`, `spectral_descent`, `descent_of_linear_maps`, `isogeny_to_power`, `endomorphism_norm_bound`, `Metric.ofPlaces` |
| [AlpogeWindowLandauCriterion.lean](../RHLean/Analysis/AlpogeWindowLandauCriterion.lean) | 798 | Abstract localized one-sided window Landau theorem | `WindowLandau.PoleData`, `WindowLandau.landau_window` |
| [AlpogeNativeWindowMellin.lean](../RHLean/Analysis/AlpogeNativeWindowMellin.lean) | 289 | Native Mellin/Laplace identity for `alpogeNativeGzArithmetic` | `alpogeNativeGzArithmetic_mellin`, `alpogeNativeLaplace_eq_mellin` |
| [AlpogeNativeWindowLandau.lean](../RHLean/Analysis/AlpogeNativeWindowLandau.lean) | 338 | Pole cancellation at $s=1$, zero-order residue matching, real & square-clock window $\to$ RH | `alpogeNativeGzTransform_analyticAt`, `alpogeNativeGzTransform_at_zero`, `riemannZeta_ne_zero_of_Gz_window`, `riemannHypothesis_of_Gz_windows`, `riemannHypothesis_of_squareClock_Gz_windows` |
| [AlpogeNativeZetaBalance.lean](../RHLean/Analysis/AlpogeNativeZetaBalance.lean) | 854 | $\zeta$-only (`A0 = ⊤`) movement bound, character balance, and thin-return cost payment | `alpogeNativeDerivInt_moveConstant`, `alpogeNativeGz_sub_le_projectedSignal`, `alpogeNativeProjectionThin_normalized_le`, `alpogeNativeGz_balance_le` |
| [AlpogeNativeZetaWindowWitness.lean](../RHLean/Analysis/AlpogeNativeZetaWindowWitness.lean) | 653 | 10-field minimum-cut witness, size/budget absorption, explicit large-$x$ threshold | `AlpogeNativeZetaWindowWitness`, `alpogeNativeSizeWindow_absorb`, `exists_alpogeNativeLargeX`, `alpogeNativeGz_le_of_witness`, `alpogeNativeGz_windows_of_witnesses` |
| [AlpogeNativeZetaWindowRHBridge.lean](../RHLean/Analysis/AlpogeNativeZetaWindowRHBridge.lean) | 56 | Final end-to-end wiring from window witnesses to Mathlib's `RiemannHypothesis` | `riemannZeta_ne_zero_of_zetaWindowWitnesses`, `riemannHypothesis_of_zetaWindowWitnesses` |

---

## Verification

Every new and modified module is verified on Lean `4.34.1` with:
- Warning-fatal compilation (`lake build --wfail`);
- Independent kernel replay via `leanchecker`;
- Guarded `#print axioms` audit in [ALPOGE_NATIVE_WINDOW_RH_DESCENT_AUDIT_20261122.lean](ALPOGE_NATIVE_WINDOW_RH_DESCENT_AUDIT_20261122.lean) accepting strictly `[propext, Classical.choice, Quot.sound]`;
- Repository static audits (assumption check, paper/Analysis boundary, sorted root manifest, export sync, documentation links).

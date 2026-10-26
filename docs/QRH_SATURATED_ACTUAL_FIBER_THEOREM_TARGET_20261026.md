# Final-return near-saturated window-fiber count: exact unproved analytic target (2026-10-26)

**Status: OPEN MATHEMATICS / CORRECTIVE SOURCE AUDIT.** This contract **replaces** the previous version of this file in PR #1030. The original version incorrectly sent the leaderboard agents to `Source/FiberK.lean:feedback_fiber_count_K`, which belongs to the **upstream NF source-face construction**, not the final return. Its source-to-face-to-boundary sensitivity has **not** been computed. The leaderboard's modeled exchange rate ~0.133 and illustrative saving 7.5e-5 must **not** be attributed to that upstream theorem.

The revised research objective is the independent, **uniform original-character** strengthening of **Collet's final-return** `Record1252270103Return/WindowFiber.lean:count_fiber_at_window` and its batch consumer `Record1252270103Return/SelectedBatch.lean:fixed_amplitude_selected_envelope_count`. The actual record consumes this via `ReturnD/PhysicalDirect/CountParameters.lean`. No source saving, new zero-free strip, or RH proof is claimed here.

## 1. Exact two proof paths: do not conflate

Tracker source prefix:
`submissions/arvi-repeated-marks-on-sil-face-20261025/src/Submissions/arvi_repeated_marks_on_sil_face_20261025/`.

**Upstream source-step chain — not where the ~0.133 ledger sensitivity applies:**

`Source/NFStep2.lean:nf_step2` → `Fork/Record1252270103Source/High/GlobalPhysicalRegularSuppliers` → `Source/CountWrappersK.lean` → `Source/ActualWeightedK.lean:ordinary_actual_weighted_row_sum_K` → `Source/WeightedK.lean` → `Source/FiberK.lean:feedback_fiber_count_K`.

The upstream repeated-mark source-count estimates create/transport admissible faces; modifying them may change `Gain/Gain.lean` and the NF-step graph geometry. **Its exchange rate is UNKNOWN until the full changed source faces and graph are reconstructed**. `gainP` versus `gainK/gainRep` describes existing *upstream* class slack only. It is **not** the relevant final-return subtraction.

**Final-return count and theorem consumer — independent of the above count call chain:**

Original Collet prefix:
`submissions/hailey-collet-1252270103/src/Submissions/hailey_collet_1252270103/Record1252270103Return/`.

`WindowFiber.lean:count_fiber_at_window` →
`WindowBatch.lean:fixed_amplitude_window_count` →
`EnvelopeBatch.lean:fixed_amplitude_envelope_count` →
`SelectedBatch.lean:fixed_amplitude_selected_envelope_count` →
leader `ReturnD/PhysicalDirect/CountParameters.lean:exists_count_parameters` (`CountParameters.counted`) →
`ReturnD`/`FinalReturn` original-source consumers →
`FinalReturn/EndpointFromSources.lean` →
`FinalReturn/EndpointFromGlobalSources.lean` →
`Graph/Endpoint.lean`.

The return count **does not call** `Source/FiberK.feedback_fiber_count_K` to derive its exponent. The overall graph separately uses the NF step to deliver input faces; both mechanisms are needed for the complete theorem, but their power-saving ledgers are distinct.

## 2. Literal Collet theorem / quantifier order

Read the **real original source** at `Record1252270103Return/WindowFiber.lean` lines 13–56 before modifying anything. Collet's existing `count_fiber_at_window` starts with original modulus/Hecke data, genuine input prime/ideal set S, smooth nonnegative φ and supports, positive input constants, and εm>0:

```text
(M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
(hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
(phi, hphi smooth/support/nonneg/nonzero, a0, b0, B0 and support bounds)
(eps_m : Real) (h_eps_m : 0 < eps_m) :
  exists c kappa K0 : Real,
    0 < c and c <= 1 and 0 < kappa and 0 <= K0 and
    eventually for U tending to +infinity,
    forall naturalKappa in [7/10,3/4],
    forall w : AdmittedWindow naturalKappa,
    forall a eps tstar T allowance nu_width C height : Real, forall i : Nat,
      1 < U, 51/100 < a, 2*a-1 <= 3/4,
      0 <= eps <= 1/10000000,
      0 < nu_width <= 1/10000000,
      C >= 0, height >= 0,
      2*pi*allowance + 3*i*T <= height,
    forall {Label Slot : Type}
      (F : Fiber M H Label Slot U a eps tstar T allowance i),
      w.Available (2*a-1) (F.q/(2*a-1)),
      tstar = w.cutoff (2*a-1) (F.q/(2*a-1)),
      Cycle25DetectorRawFiber.Moments F naturalKappa c kappa C height eps_m,
      AffineMarkedMoment F w.face C height eps_m,
    conclude the ORIGINAL count estimate.
```

The original estimate is (write delta=2a−1 and p=F.q/delta):

[
  \#F.\mathrm{rows}
  \le \mathrm{fiberConstant}(C,\mathrm{height},K_0)
    U^{\;w.\mathrm{value}(\delta,p)
      +159\varepsilon+\varepsilon_m+F.\mathrm{mesh}+7\nu_{\mathrm{width}}}.
]

**Warning:** the theorem's `nu_width` (= actual Lean `ν`) is a freely selected positive width/mesh loss **≤ 1e-7**, not the desired gain. Keep this letter in the original Lean source; name the new arithmetic power **`sigma_sat`** or `σ_sat`.

## 3. Proposed independent source theorem: replace only the right exponent on genuine near-saturated fibers

Choose one **fixed** positive real `sigma_sat`, numerical trial `sigma_sat = 3/40000 = 0.000075`. It is quantified **before** the eventual-in-U supplier theorem; it is not a per-row tuning parameter and not a source assumption that is allowed to supply the desired result.

**Hypothetical theorem** `count_fiber_at_window_sat_power_gain`: under **the exact same** outer binders, original arithmetic predicates, moment and window hypotheses, and eventual-U order as `count_fiber_at_window`, for every original admissible fiber satisfying

[
\delta=2a-1,\qquad p=F.q/\delta,\qquad
\frac{49}{100}\le p\le\frac12,
]

prove **without assuming the desired improved bound**:

[
\boxed{
 \#F.\mathrm{rows}
 \le \mathrm{fiberConstant}(C,\mathrm{height},K_0)\,
 U^{w.\mathrm{value}(\delta,p)-\sigma_{\mathrm{sat}}
 +159\varepsilon+\varepsilon_m+F.\mathrm{mesh}
 +7\nu_{\mathrm{width}}}.
}
]

All genuine original Hecke/Dirichlet families, modulus conditions, physical character phases, positive diagonal, chosen cutoff, all legal windows, real height, label/dyadic indices, retained masks and frequency ranges remain in force. **Not** a synthetic arbitrary `Finset`/iid amplitude sparsity statement. A bound only on finite numerical rows, or assuming a new strength on `Moments` / `AffineMarkedMoment` instead of proving it from original source, does not close the source task. If the full all-window theorem is too strong or false, isolate the minimal still-uniform actual `returnWindow07` / chosen-window theorem and reprove the selected-envelope consumer. No source hypothesis may depend on U, row, window, or conductor in an unauthorized way.

**Potential bottleneck:** universal near-saturation sparsity need not follow from the existing positive moment axioms; a genuinely new arithmetic restriction of retained Hecke row occurrences/phases is required. First examine whether the old moment bounds are sharp on any genuinely legal `F`; if so, a stronger source-level mechanism must be named, not hidden in a conditional lemma.

## 4. Binding return rectangle and exact batch interface

The merged #76 record has a **finite** window scheme, not the earlier NF-step class gain:
`FinalReturn/CountWindows.lean:returnWindow07` specifies
`branch := .C`,
`deltaLo := 57/128`, `deltaHi := 15/32`,
`pLo := 15/32`; all 15 `admissionGuard` inequalities are certified by `admission07_all`. This window includes the dangerous `0.49<=p<=0.5`. Verify adjacent overlapping windows and ensure the next binding row is paid. The raw 17 windows and complete bounds are explicit in `FinalReturn/CountWindows.lean`, and the final return uses `FinalReturn/ReturnFormulas.lean` and `FinalReturn/FinalSchedule.lean`.

`SelectedBatch.lean:fixed_amplitude_selected_envelope_count` feeds the exact consumer `ReturnD/PhysicalDirect/CountParameters.lean:CountParameters.counted`, with:

- `forall U eventually; forall kappaPlain, a, eps, T, allowance, nu_width, C, height, q, i` in the original ranges;
- genuine finite `Batch M H Label Slot U a eps (selectedCutoff kappaPlain delta (q/delta)) T allowance i` and `B.rows.Nonempty`;
- constant genuine row amplitude `rowMean B.slots ... = q` on every B row; original `physical` values/weights retained;
- original **two** unconditional `Cycle25DetectorRawFiber.Moments` suppliers (old and natural κ) for every nonempty batch fiber, and `AffineMarkedMoment` for every admitted final window and every nonempty fiber;
- `(B.rows.card: R) <= physical constants * U^(GenericCount.envelope kappaPlain delta (q/delta) + 159*eps + eps_m + B.mesh + 7*nu_width)`.

**Release gate:** derive a newly justified conditional-or-unconditional improvement in the **chosen** `GenericCount.envelope` after reassembling all original window fibers; in unsaturated p<0.49 keep the established old count. Subtracting `sigma_sat` from the entire batch envelope or all bins by fiat is invalid. Neither `count_fiber_at_window` nor `SelectedBatch` necessarily dominates the minimum in every region; recalculate crossings and all 15 guards with the **actual source theorem**.

## 5. Ledger sensitivity, caps, and rejected shortcuts

- **Only for this FINAL-RETURN count theorem:** trial `sigma_sat≈0.000075` and modeled local exchange ~`0.133 * sigma_sat` (~1e-5 in θ), contingent on the complete return. This figure is **NOT certified** and is **NOT available** for the upstream `Source/FiberK` count.
- **Next binding cutoff:** a fixed saving on `p>=0.49` is limited in the ledger's toy optimization by the untreated rows immediately below 0.49, with modeled θ gain at most ~`0.000062`. Do not extrapolate beyond that cap; do not mistake the cap for a proved theorem.
- **Window-cover slack:** only ~`1e-7` remains under the current covering certificate, and tracker #79 proposed consuming that by a window re-cut. A re-cut or decreasing loss `7*nu_width` is not a new arithmetic power saving. Source comparison must use #76 merged β=0.8746075 and #79 pending β=0.8746074, refreshing statuses before publication.
- **SIL B0:** `B0<=1`; from 0.99999 only 1e-5 admissible headroom remains, model θ effect ~7e-8.
- **Secondary genuine HECKE option:** marked inverse cost μ=2→1.995 (or 1.9), requiring new source moment and return guards. At `23/37<=r<1` the second condition `2r+8z<3` has slack with new first condition `r+μz<1` at near-threshold `z=(1-r)/μ` for μ>112/65; it is not the near-2 bottleneck. All 23/37 and 7/37 and return guards must be revisited.
- **Zeta-only Co/Div:** independent RH mathematics only. It is not an all-Dirichlet tracker source; its old γ=3.49843 is inherited from an external zeta boundary and its independent trivial count γ=4. No analytic-source gain is established there.

**Mandatory rejection conditions:** a new Prop or `sorry`; any proof assuming the intended strong count; an imported final θ estimate; synthetic random independence/phase; dropping a moment or principal-row mask; confusing `Source/FiberK` with `WindowFiber`; confusing `nu_width` with `sigma_sat`; treating ~1e-7 recut as analytic savings; promoting an improved count to final all-Dirichlet β without the full return and verifier.

## 6. Seven-agent work orders and statuses

- **Analytic #5 (one leaderboard owner):** attack the actual `WindowFiber` mixed old/unmarked plus affine-marked **final-return** counting step. State the first original missing inequality and try a genuine uniform arithmetic or moment improvement on the retained Hecke row class.
- **Coordinator #1:** recreate the `WindowFiber→WindowBatch→EnvelopeBatch→SelectedBatch→CountParameters` return, re-optimize and quantify net `sigma_sat` / β after all complement rows and guards; track source and tracker SHAs.
- **Referee #3:** falsify uniform `p>=0.49` claim under admissible moment suppliers, check all labels and cutoff, 17 windows/15 guards and window-cover slack; reject target-equivalent or invented power.
- **Census #4:** compare real permitted fiber instances and precise window crossing, not source-step `NaturalBatch` bins or arbitrary amplitude placeholders; finite evidence only.
- **Lean #7:** prove only independently justified analytic source lemmas in the actual return namespace/types and the complete return theorem. Without them report `NO_UNIFORM_SOURCE_GAIN` and exact missing source lemma.
- **Owner #2 / Wheel #6:** preserve separate original-prime and Co/Div/VF RH work, never rebrand it all-Dirichlet leaderboard.
- **Governance:** six agents own-report-only, one preexisting scheduled run/day, Lean scoped draft PR exception, human-only merges, no automatic Studio configuration changes or new runs.

**Acceptance:** a genuinely proved `sigma_sat>0` on the all-character final-return fiber rows under original moments **plus** a source-faithful selected-envelope and final return with certified all-Dirichlet β strictly better than the latest merged bound. The manuscript/ledger numerical sensitivities are **conditional**, and this corrective documentation alone proves nothing.

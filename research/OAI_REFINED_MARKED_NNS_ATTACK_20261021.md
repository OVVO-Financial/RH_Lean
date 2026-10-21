# Attack: real unnormalized NNS coordinates of OpenAI's ACTUAL refined marked fourth moment

**2026-10-21 — Source-faithful research result, not a new zero-free exponent.** Native Lean: [VF_919_OAI_ACTUAL_MARKED_FOURTH_REAL_NNS_20261021.lean](VF_919_OAI_ACTUAL_MARKED_FOURTH_REAL_NNS_20261021.lean). Finite sextic phase test: [oai_marked_phi_sextic_stress.py](../scripts/oai_marked_phi_sextic_stress.py).

## 1. Read the real OpenAI theorem, not a proxy

OpenAI: https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Detector/DetectorPlainMarkedFineField.lean

`source_batch_plain_marked_fine` is quantified over actual:
- Hecke data `S : SourceData D` and character `η : Character`;
- a `Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters ...)) (Fin D.N) ...` with **the source's** `B.data=sourceMomentData ...`, `B.profile=(S.w)`, `B.widths=(D.ell/d)`, and the original external real part `17/50`;
- bins, label, left/right, nonempty fibre and its actual `F.rows`;
- selected prime-slot subset `selected⊆F.slots`, original amplitude mask `F.physicalProduct selected u`;
- ALL `j,k:ℕ` with `j+k≤2`, σ∈[0,1], |t|≤height;
- original **marked capacity**: `2*F.m+6*(3/4+2*Δ)*(∑s∈selected,F.widths s)≤1`.

Write `P_j(u)=polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) ((Z^d)^F.m) σ t`, `W(u)=F.physicalProduct selected u`, `U=Z^d`.

Then the actual conclusion is

    ∑_{u∈F.rows} |P_j(u) P_k(u) W(u)|²
       ≤ C (1+height)^J U^(1+D.t).

**Important correction to earlier research dialogue:** This specific marked fourth-moment integrand is a PRODUCT of two genuine derivative-profile polynomial rows and their original selected-slot physical product. It is NOT by definition a marked-minus-rescaled difference `M_u-R_u`. The latter compensation appears in a different part of OpenAI's detector proof. We must not infer a favourable `-2 A C` term in the MARKED inequality without showing such a difference in the *actual polynomial row*.

## 2. The exact unnormalized REAL NNS equivalence for the ACTUAL integrand

Use Fred Viole's invertible (phase-preserving) map, already Lean-compiled in `STABLE_FAR_PERRON_REALIFICATION.lean`:

    Φ(a+ib)=(a-b,a+b),   E(z)=((Φz).1²+(Φz).2²)/2=|z|².

Then every actual OAI row integrand equals

    |P_j P_k W|² = E(P_j) E(P_k) E(W).

This is exact for **the original F.rows**, **the original selected and zero masks**, original varying source family and height, and arbitrary row lengths. Nothing is normalized by #rows. The native theorem `vf919ActualMarkedMoment_eq_realEnergies` proves this universally; the actual OAI data instantiate its Pj, Pk and physical variables literally.

For j=k=0, the actual refined marked input is precisely a physically weighted unnormalized FOURTH moment:

    ∑_{u∈F.rows} |W(u)|² |P_0(u)|⁴.

Writing Φ(P_0(u))=(x_u,y_u), define U4(x)=x_+⁴, L4(x)=x_-⁴ and the four mixed nonnegative quadrant terms Q22(x,y)=x_+²y_+²+x_+²y_-²+x_-²y_+²+x_-²y_-².

Then

    |P_0(u)|⁴ = [U4(x_u)+L4(x_u)+2Q22(x_u,y_u)+U4(y_u)+L4(y_u)]/4.

The complete original refined moment is the WEIGHTED SUM of those five nonnegative terms, with *exact weight* |W(u)|². Lean: `vf919ActualMarkedFourth_eq_unnormalizedNNS`. For mixed j,k the exact moment is `∑ E(W) E(Pj) E(Pk)`; this is the true co-partial second-moment product. No complex arithmetic is needed to evaluate any of these FINITE moments. The original holomorphic zero-detector remains complex analytic.

## 3. A concrete sharpenable power LOSS FOUND IN THE ACTUAL PROOF

This is NOT speculative directional psychology. Read the source proof immediately after `have hstate : state.width ≤ 2`:

- Existing `source_batch_marked_initial` returns exact
  `hwidthstate : state.width = 1 + delta D`.
- `delta D=D.t/4` and `stageError D=D.t/4` (see `Moments/DetectorPlainMomentParameters.lean`).
- The input energy estimate `hrow` is `... ≤ C ... * U^(state.width+stageError D)`.

Consequently, the *actual proof* before its final loss uses

    state.width + stageError D = 1 + D.t/2.

But `source_batch_plain_marked_fine` replaces that with `1+D.t` in the declared output via the coarse `hexp` proof:

    have hexp : state.width+stageError D≤1+D.t := by
      rw [hwidthstate]; linarith [(fixed_parameters D).2.2.2.1]

**Sharper derived marked-moment exponent available from the very same input**:

    ∑_{u∈F.rows} |P_j(u) P_k(u) W(u)|²
      ≤ C (1+height)^J U^(1+D.t/2).

For U=Z^d, this is a power factor `U^(-D.t/2)=Z^(-d*D.t/2)` relative to the current marked-moment bound, under ALL the same source/capacity hypotheses. The native `vf919MarkedActualWidthExponent` proves the exact algebra and `vf919ActualMarkedSharperOfRawWidth` transports the **unrelaxed hrow input**, if supplied, to the identical NNS row without loss.

### Exact proposed patch in the original OAI source

Inside `source_batch_plain_marked_fine` (same file), replace the exponent at the theorem's terminal marked-moment conclusion `(Z^d)^(1+D.t)` by `(Z^d)^(1+D.t/2)`, and replace the `hexp` statement by

    have hexp : state.width + stageError D ≤ 1 + D.t/2 := by
      rw [hwidthstate]
      dsimp [delta, stageError]
      ring

This patch is a **proposed improvement to OpenAI's theorem statement**, not a submitted modification to the `openai/math` repository. The existing downstream `FinalAssemblyCertifiedBands.source_moments` expects the broader `U^(1+D.t)`: add `Real.rpow_le_rpow_of_exponent_le (by positivity) (by linarith [D.t_pos])` when consuming the refined marked estimate. That restores the old interface while retaining the sharper theorem for further optimization.

### Why the final zero-free exponent does not automatically change

The downstream `SourceMomentBound` collects THREE distinct inputs: inverse second moments, refined marked fourth moments, and unmarked ordinary moments. Its upper exponent is a shared budget, not solely the marked theorem. Also `D.t` is chosen *small relative to* `Δ=β-7/8`, so the (D.t/2) improvement can tend to zero as Δ→0. To improve the actual boundary one must re-optimize the coupled prime-slot/conductor geometry or prove independent phase-sensitive cancellation that improves a binding cost. This note does NOT claim a new `β<7/8` theorem.

## 4. Test directional NNS alignment against the actual inequality's algebra

Finite stress script tests all allowed j+k≤2 with varying complex phases, a selection mask and an original weighted product, verifying no dropped cross terms. It also tests the six exact unit phase angles `ζ₆^j`.

For the **separate compensated-difference identity** `M=1, R=ζ₆^j`, the six exact quartic energies are

    |1-ζ₆^j|⁴ = [0,1,9,16,9,1],

whose average is 6. The unsigned quartic baseline `A²+C²` has the same average 6: positive and negative directional alignment cancel exactly over uniform six-phase weights. So a new POWER saving cannot follow from realification or directional quadrant definitions alone. It would require a PROVED source-weighted *nonuniform arithmetic alignment or spectral moment gain*. This is a finite falsifier of any alleged all-purpose "NNS automatically improves fourth moments" rule, not evidence against a genuine conditional arithmetic gain.

## 5. Specific next analytic target

Use real NNS coordinates for the *ACTUAL* Hecke source and preserve all selected labels. Determine whether the current `PositiveAt` -> `retainedSourceEnergy` -> `diagonalControl` step pays extra positive mass for phase-unfavourable row families. The precise analytic inequality to strengthen is the upper bound on the `retainedSourceEnergy` of those actual derivative-profile polynomials, with an independent improvement to the marked capacity or source width.

Do not substitute the RH_Lean VF odd-seat physical charge for OpenAI's `F.physicalProduct selected u`; those are **different** sources and are only equivalent if the full ideal-to-integer carrier and physical weight are proved to match. This module works as a lossless universal row-integrand transform, **not** a claim that these two source populations have been identified.

**Acceptance:** Lean 4.34.1 warning-fatal targeted import closure, named theorem checks and finite sextic stress; no external OAI build or independent sharpened OAI theorem is asserted unless explicitly verified.

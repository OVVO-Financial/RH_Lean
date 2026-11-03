# Recovering the true finite-slot minimum in the proved 1 -> 7/8 contraction

Date: 2026-11-03.  Status: candidate improvement in the **original** complete compensated analytic route.  A committed Lean proof and pinned warning-fatal workflow are supplied; do not promote the claim until the exact branch CI succeeds.  This packet is about a binding source-geometric LOSS, not a newly proved independent signed NNS moment saving.

## I. Original source and the precise discarded factor

Authoritative pinned source:
- [ParametersSlotLengths.lean, original constructor](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/ParametersSlotLengths.lean);
- [ParametersHighDataFine.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/ParametersHighDataFine.lean);
- [original exact LOW reflection and physical source](../research/oai_434/VF919TiltedLowPhysical.lean);
- [merged LOW-first endpoint](../research/oai_434/VF919LowFirstSlotAnchoredEndpoint.lean).

The original `exists_physical_slot_lengths` first constructs an injective, finite, strictly positive list of actual lengths `ell : Fin N -> Real` with sum `1/6`. It selects an index `j` minimizing `ell`, then defines

    rmin := ell j / (2*dmax).

The actual HighData constructor fixes `dmax=7/8`. Consequently, in this actual *constructed source* (not an arbitrary HighData record),

    ell_* := min_j ell_j = 2*(7/8)*rmin.

But the merged LOW-first proof consumes only

    m := (7/8)*rmin
    24*tilt <= m.

Thus one exact factor of two in the admissible selected-slot mass is discarded before the complete reflected LOW estimate is run. At the calibrated `delta_old = m/24` the physical lengths are

    x = 17/48 - 24*delta_old
    y = 23/48 + 12*delta_old.

The *same* constructed source permits `delta_true = ell_*/24 = 2*delta_old`. All `ell`, selected tuples, ideal primes, signs, masks and weights remain unchanged.

## II. A formally quantified source-recalibration argument

The new [VF919ActualSlotMinRetighten.lean](../research/oai_434/VF919ActualSlotMinRetighten.lean) does **not** modify OpenAI's source. It defines the true minimum `actualSlotMinimum D` with a finite `exists_min_image`, proves that every original slot is at least the minimum, and sets

    trueMinimumRmin D := actualSlotMinimum D / (7/8).

It constructs `sourceWithExactSlotMinimum D : HighData Delta`, changing **only the numerical lower-bound field `rmin`**. The supplied Lean proof explicitly rechecks the four sensitive fields:
- `slots_bounds`: exact source `(7/8)*rmin_new = ell_*`;
- `rmin_pos`: true positive source slots;
- `epsilon_gap`: increasing `rmin` only helps `epsilon < rmin*t`;
- `window_budget`: increasing `rmin` only helps the right-hand side.

All other analytic records, actual ideal source coefficients, physical calibration, labels, exclusions, and external character arguments are definitionally unchanged.

On `slotCalibratedHighDataLowFirst (sourceWithExactSlotMinimum D)`, the existing complete LOW-first supplier applies at

    delta_true = actualSlotMinimum D / 24.

The existing HIGH supplier is independently recalibrated by its **proved** source record constructor to

    sigma_true = actualSlotMinimum D / 4 = 6*delta_true.

The old amplitude crossing arithmetic therefore becomes

    LOW exponent: 3/16 - 9*delta_true + arbitrary positive loss
    principal shift: -11/16 - 8*delta_true
    HIGH reference: 7/8 + shift - sigma_true

and the complete zero-detector threshold is

    theta = max(7/8-delta_true, 7/8-6*delta_true)
          = 7/8-delta_true.

The HIGH reserve stays positive. The actual supremum and primitive zeros are never redefined. The source-specific true minimum is fixed before selecting a character, a zero or an arbitrary LOW loss.

## III. End-to-end declarations and scope

The source file attempts formal proofs of:

    OAI.SevenEighths.RHLeanActualSlotMin.native_beta_le_true_physical_slot_minimum

      exists D : HighData (1/1000000),
        0 < actualSlotMinimum D /\
        HeckeZeroSupremum.beta <= 7/8 - actualSlotMinimum D/24.

    RHLean.Analysis.native_mertens_true_physical_slot_minimum

      exists D : HighData (1/1000000),
        0 < actualSlotMinimum D /\
        MertensGrowthAtMost (7/8 - actualSlotMinimum D/24).

    RHLean.Analysis.native_signed_pair_true_physical_slot_minimum

      same source witness, all positive exponent losses, all integer
      prefixes and the exact squarefree diagonal.

This statement is stronger in *source calibration* than `delta = ((7/8)*rmin)/24` because `ell_* >= (7/8)*rmin`, with a strict gain for records satisfying `ell_* > (7/8)*rmin`. The source constructor explicitly satisfies `ell_* = 2*(7/8)*rmin`; the generic HighData declaration alone does NOT promise this factor-two relation. The new proof deliberately works for every HighData by retightening its certificate, then chooses an admissible instance.

The terminal is an **existential, source-dependent positive saving**. It does not furnish a fully evaluated rational `delta` independent of the chosen source, a sharper short-shell mean square, RH, or independent NNS off-diagonal saving. Nor does it change the need to preserve all original Gaussian/Hecke source labels: those are carried through the existing complete analytic suppliers. It is incorrect to reinterpret the new improvement as a purely rational-integer Hecke intertwiner.

## IV. Reproducibility and acceptance

Workflow: [Native LOW-first slot-calibrated contraction](../.github/workflows/vf919-low-first-slot-anchored.yml).

The workflow:
1. checks out pinned original OpenAI analytic source;
2. reconstructs the additive anchored HIGH source from immutable pinned commits (never patches original theorem files);
3. kernel-compiles the complete existing LOW/HIGH source and the new `VF919ActualSlotMinRetighten.lean` under Lean 4.34.1 with warnings as errors;
4. runs the original exact endpoint/axiom/live-value audit;
5. additionally runs `ActualSlotMinAudit.lean` to check actual new terminal roots, permitted standard axioms, live source-retightening, native signed moment, complete LOW/HIGH and primitive zero-detector dependencies; it forbids feeding back the old strict endpoint as a premise.

**Acceptance only when all checks pass on the exact PR head.** This is the first source-geometric component improvement to test. Once verified, the next target for a genuinely *signed* improvement is the earliest positive norm/absolute-value majorization inside the original reflected LOW estimate, with the preserved cofactor/ideal phases. That remains distinct arithmetic work.

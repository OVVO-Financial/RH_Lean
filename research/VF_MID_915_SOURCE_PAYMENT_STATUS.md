# #915 original source-payment status

Updated 2026-10-12 UTC. The original first-bad payment and RH remain open.

The [source module](VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean) retains the
original physical source, survivor restrictions, historical anchor and squared
absolute NNS denominator. Its target is now recorded explicitly as
`VFMid915FirstBadSourcePaymentStatement`:

```text
for every R >= 8, under VFMidActualPrimeFirstBadAt 2 (R+1),
  2 * vfMidFirstBadDecompressedHistoricalSource R ^ 2
    <= vfMidFirstBadZeroTargetTotalMass R.
```

The previous attempted unconditional tail failed at `linarith`: prior-good
anchors, the exact signed split, and matched-pair heat did not establish
anchored balance. The maintenance change removes that unsupported proof and
its unconditional victory names. It does not weaken the target or supply a
proof of it. A proposition definition is neither an axiom nor an established
theorem.

The compiled-consumer candidates are named `_of_anchoredBalance` and
`vfMid915FirstBad_closed_of_sourcePayment`. Their hypotheses expose the missing
input, and their terminal contradictions are conditional. Warning-fatal Lean
compilation and five standard-axiom checks are required by the
[fast workflow](../.github/workflows/vf-first-bad-exact-budget-fast.yml).

The needed arithmetic is still an occurrence-preserving, original-weight
historical/current pair transport and first-bad-specific payment. Negative
sector-six examples at roots 8 and 18, historical denominator restoration,
and the distinct protected high-prime star prevent substituting unconditional
cone balance, extra even-composite capacity, or an unlike carrier. Preserve
the [cone audit](VF_MID_915_SECTOR_SIX_CONE_AUDIT.md) and
[centered-owner audit](VF_MID_915_CENTERED_OWNER_COVARIANCE_WELD.md).

Merging this exact toolkit records a checked reduction. It does not close the
source-payment proposition, actual-prime admissibility, finite A/C, or RH.

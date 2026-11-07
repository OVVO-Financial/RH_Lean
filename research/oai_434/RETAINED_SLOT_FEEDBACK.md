# Retained-slot feedback through the original analytic proof

## Scope

This development retains the original OAI arithmetic inputs at `1581d4cbdd69a0faf34b2089614fe2a814316a6a` and the repository's unpatched native PNT dependencies. The scalar proof keeps the actual marked slot mass in the reflected-return budget. Parallel analytic modules propagate that repair without editing upstream files or replacing the original energy predicates.

A fixed lower parameter `kappa0 > 1/2` is chosen before all analytic constants. The intermediate family is uniform for `kappa >= kappa0`. The terminal theorem specializes `kappa0 = kappa`, eliminating the helper typeclass from its public hypotheses. It retains the original full-Hecke-family licensing condition `2 * HeckeZeroSupremum.beta - 1 <= kappa` and the original lower-beta range. No uniform positive margins as `kappa0` tends to `1/2` are asserted.

## Exact repair

The original parent volume/capacity inequalities imply `(6*kappa - 1) * ell <= width/6 + defect`. The coupled reserve

```text
(6*kappa - 1)*xi + (6*kappa + 1)*defect <= (6*kappa - 3)*width/6
```

implies `2*ell + xi + defect <= width/6`. This returns both original LOW admissibility inequalities after reflection, including clipped reflection and every original ideal-deletion mask. At `kappa = 3/4` it is exactly the old `xi + 11*defect/7 <= width/14` reserve.

For widths at least `rho > 0`, the fixed allowance is

```text
rho * min (1/100) ((6*kappa0 - 3)/(24*(6*kappa0))).
```

Both `xi` and the clipping defect are chosen below it. The constants therefore precede the varying `kappa`, as the original proof requires.

## Analytic propagation

The parallel proof graph includes original and deleted reflection, robust/live clipping, bounded reserve transport, LOW physical/source estimates, HIGH physical/source estimates, the zero-mode growth stage, successor packing, and the complete width induction. Unchanged analytic suppliers are imported; their arithmetic content is not re-proved or assumed as a new bound.

Public targets:

- `RetainedSlotFeedback.terminal_certificate_half`: original `CertifiedBand` at terminal width, with `kappa > 1/2` instead of `kappa >= 3/4`.
- `RetainedSlotDetector.source_batch_plain_marked_fine_half`: literal admitted source moment, capacity `2*m + 6*kappa*sum(widths) <= 1`, actual profiles/products, and retained exponent `1 + D.t/2`.
- `RetainedSlotMoments.source_moments_half`: all four source moment fields, with unchanged inverse/unmarked suppliers. The original `Moments` record is instantiated at `(kappa - 3/4)/2` so its capacity is exactly `6*kappa`; the actual source `HighData` is unchanged, not assigned a negative Delta. The sharper marked theorem remains separately available alongside the common `1 + D.t` interface.
- `RetainedSlotFiberCount.plain_marked_count_half`: immediate actual-row count consumer with original supply cap, weights and height cost.
- `RetainedSlotApplications.original_source_fineness_preserved`: lowering kappa enlarges the mesh, preserving a sufficiently fine existing source.

A strict full-family boundary below `7/8` licenses some `kappa` strictly between `1/2` and `3/4`; that logical connection is explicit. This does not identify a Hecke energy constant with the rational historical envelope K_R.

## Validation

Use `.github/workflows/retained-slot-feedback.yml` on the exact PR head. Compilation is pinned to Lean 4.34.1, warning-fatal, and uses the shared compiled dependency cache. No local Lean execution is used.

The generator records source/output hashes in `retained-slot-generation.json`. CI checks all independent branches, records failed or blocked modules, and fails unless the entire graph compiles. Public terminals are audited against `propext`, `Classical.choice`, and `Quot.sound` only. No sorry/admit, project axiom, native-evaluation axiom, or weakened checker is allowed. Generated sources and diagnostics are retained as Actions artifacts. Source-only generation is for inspection, not proof verification.

Validation status comes from exact-head Actions results, not this note. Independent mathematical review and human-only merge remain required.

## Endpoint boundary

This is an analytic supplier and consumer extension, not a new numerical global zero-free/Mertens exponent, fixed critical historical amplification, or uniform iteration to RH. The final same-probe parameter comparison must consume the strengthened supplier before an improved endpoint is claimed. Existing complete 7/8 and strict-slot results are preserved.

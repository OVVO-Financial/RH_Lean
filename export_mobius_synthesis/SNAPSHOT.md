# Source snapshot provenance

This synthesis export is synchronized to the `OVVO-Financial/RH_Lean` parent Lean source state at commit:

```text
9c31d5d25e84c1734cef8b26303a1fbf33340823
```

That parent-source commit contains the final parent copy of `RHLean.Analysis.PrimeSievePNTCentering`. The subsequent synthesis-export commits mirror the same Lean blob and update export-specific documentation only.

## Copy policy

- `RHLean.lean` is copied from the parent root import manifest without modification.
- Every one of the **247 Lean modules** imported by that manifest is mirrored into `RHLean/` using the source file's existing Git blob SHA.
- The original synthesis snapshot contained 214 imported modules. The current synchronized manifest therefore contains **33 additional modules** relative to that original snapshot.
- The previous synchronization had reached 246 modules. This synchronization adds the single new synthesis seam module `RHLean.Analysis.PrimeSievePNTCentering`.
- `README.md`, `MODULES.md`, this provenance note, and other synthesis-facing explanatory files are export-specific documentation.

## Elementary and PNT-centering seams

The elementary prime-sieve bridge remains mirrored byte-for-byte:

```text
RHLean.Proof.PrimeSievePostSqrtGap
RHLean.Proof.PrimeSieveSquareRootTransport
```

The first proves the arbitrary post-square-root identity for the all-plus prime-comb state:

```text
M_y^+(x) - M(x)
  = 2 * sum_{y < q <= x, q prime} M(floor(x/q))
```

under `sqrt x < y`. The second specializes to `x = R^2 - 1`, `y = R` and identifies the pre-large-prime state with the original square-block `smooth + transport`, so its difference from the completed Mertens state is exactly twice the existing square-root transport term.

This synchronization adds the parent module

```text
RHLean.Analysis.PrimeSievePNTCentering
```

using the same Git blob in the parent and synthesis trees. It decomposes the explicit prime tail by the singleton logarithmic-integral density

```text
density(q) = Li(q) - Li(q-1),
```

matching the repository's existing exact-activity prime-density convention, and defines the exact prime-indicator-minus-density error. It then applies the repository's actual square-wheel zero-mode centering to obtain

```text
H_{k,n} = centered PNT-corrected comb - 2 * centered prime error,
```

as well as the fully expanded all-plus, PNT-bulk, and prime-error identity and the corresponding norm-transfer inequality.

These are exact finite realization and centering theorems. They assert no PNT error estimate, Bombieri–Vinogradov estimate, large-sieve estimate, RH-scale power saving, or new axiom.

## Synchronization invariant

The export is intended to be build-complete as a standalone Lean snapshot. Therefore:

1. `export_mobius_synthesis/RHLean.lean` must match the parent root `RHLean.lean`.
2. Every internal module imported by that manifest must exist at the corresponding path below `export_mobius_synthesis/RHLean/`.
3. Mirrored Lean files should reuse the exact parent Git blobs rather than edited copies.
4. When the root manifest gains imports, the new modules and the updated manifest should be synchronized together.

Because the Lean files reuse the exact parent blobs, the synthesis export does not introduce alternate theorem statements or edited proofs. It is a publication snapshot of the audited formal source tree, with export-specific documentation layered around it.

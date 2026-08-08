# Source snapshot provenance

This synthesis export is synchronized to the `OVVO-Financial/RH_Lean` parent Lean source state at commit:

```text
4b447dc943cdf2fe97823d33b4dc34cb9fa2b837
```

That parent-source commit contains the final parent copies of the two elementary prime-sieve bridge modules. The subsequent synthesis-export commits mirror those parent blobs and update export-specific documentation only.

## Copy policy

- `RHLean.lean` is copied from the parent root import manifest without modification.
- Every one of the **246 Lean modules** imported by that manifest is mirrored into `RHLean/` using the source file's existing Git blob SHA.
- The original synthesis snapshot contained 214 imported modules. The current synchronized manifest therefore contains **32 additional modules** relative to that original snapshot.
- Of those 32 additions, 21 were already recorded by the previous synthesis synchronization. This synchronization catches up nine survivor modules already imported by the parent root and adds the two new elementary prime-sieve modules `PrimeSievePostSqrtGap` and `PrimeSieveSquareRootTransport`.
- `README.md`, `MODULES.md`, this provenance note, and other synthesis-facing explanatory files are export-specific documentation.

## Elementary seam added in this synchronization

The new parent modules are mirrored byte-for-byte into the synthesis export:

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

These are exact finite realization theorems. They introduce no analytic estimate and do not change the synthesis repository's remaining open nonzero-response bound.

## Synchronization invariant

The export is intended to be build-complete as a standalone Lean snapshot. Therefore:

1. `export_mobius_synthesis/RHLean.lean` must match the parent root `RHLean.lean`.
2. Every internal module imported by that manifest must exist at the corresponding path below `export_mobius_synthesis/RHLean/`.
3. Mirrored Lean files should reuse the exact parent Git blobs rather than edited copies.
4. When the root manifest gains imports, the new modules and the updated manifest should be synchronized together.

Because the Lean files reuse the exact parent blobs, the synthesis export does not introduce alternate theorem statements or edited proofs. It is a publication snapshot of the audited formal source tree, with export-specific documentation layered around it.

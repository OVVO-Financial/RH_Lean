# Source snapshot provenance

This synthesis export was assembled from `OVVO-Financial/RH_Lean` at parent commit:

```text
c7d137dc3bf8c6e4c67a79ed26d804aa1baab258
```

That commit is the `main` state immediately after the Square-Block Möbius export rebrand was merged.

## Copy policy

- `RHLean.lean` is copied from the parent root import manifest without modification.
- Every one of the 214 Lean modules imported by that manifest is copied into `RHLean/` using the source file's existing Git blob SHA.
- `lakefile.lean`, `lean-toolchain`, and `lake-manifest.json` are copied from the same parent state.
- `README.md`, `MODULES.md`, and this provenance note are export-specific documentation.

Because the Lean files reuse the exact parent blobs, the synthesis export does not introduce alternate theorem statements or edited proofs. It is a publication snapshot of the already audited formal source tree.

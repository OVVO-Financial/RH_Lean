# Source snapshot provenance

This synthesis export is synchronized to the `OVVO-Financial/RH_Lean` parent source state at commit:

```text
da731a2dae4f7e94111bfb392523caa4490ba983
```

That is the `main` state immediately before the current synthesis-source synchronization commit.

## Copy policy

- `RHLean.lean` is copied from the parent root import manifest without modification.
- Every one of the **235 Lean modules** imported by that manifest is mirrored into `RHLean/` using the source file's existing Git blob SHA.
- The original synthesis snapshot contained 214 imported modules. A comparison from its recorded parent commit `c7d137dc3bf8c6e4c67a79ed26d804aa1baab258` to the source state above shows exactly 21 additional root `RHLean` modules and no modifications to the previously exported Lean modules.
- `lakefile.lean`, `lean-toolchain`, and `lake-manifest.json` did not change over that parent-source interval, so the existing export copies remain blob-identical to the current parent metadata.
- `README.md`, `MODULES.md`, and this provenance note are export-specific documentation.

## Synchronization invariant

The export is intended to be build-complete as a standalone Lean snapshot. Therefore:

1. `export_mobius_synthesis/RHLean.lean` must match the parent root `RHLean.lean`.
2. Every internal module imported by that manifest must exist at the corresponding path below `export_mobius_synthesis/RHLean/`.
3. Mirrored Lean files should reuse the exact parent Git blobs rather than edited copies.
4. When the root manifest gains imports, the new modules and the updated manifest should be synchronized together.

Because the Lean files reuse the exact parent blobs, the synthesis export does not introduce alternate theorem statements or edited proofs. It is a publication snapshot of the audited formal source tree, with export-specific documentation layered around it.

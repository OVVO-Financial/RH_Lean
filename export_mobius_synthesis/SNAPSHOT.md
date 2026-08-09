# Source snapshot provenance

This synthesis export is synchronized to the `OVVO-Financial/RH_Lean` mathematical source state through **PR #279**, merged as:

```text
38d89861ee24a24cbb4f8bccd51e5791b645d9be
```

The final parent Lean-source anchor used by that synchronization is:

```text
5ebdcbcbf2f7755948da7d29520293b06dadbfdb
```

That parent-source state contains `RHLean.Analysis.PrimeSievePNTCentering`, the parent root import of `RHLean.Analysis.PrimeSieveQuotientPNTError`, and the final parent theorem file. The PR #279 export closeout mirrors the same quotient-module Lean blob and updates export-specific documentation only.

The later PR #280 changes repository boundary policy but does not advance the mathematical synchronization beyond the PR #279 source state described here.

## Copy policy

- `RHLean.lean` is copied from the parent root import manifest without modification.
- Every one of the **248 Lean modules** imported by that manifest is mirrored into `RHLean/` using the source file's existing Git blob SHA.
- The original synthesis snapshot contained 214 imported modules. The current synchronized manifest therefore contains **34 additional modules** relative to that original snapshot.
- The previous synchronization had reached 247 modules. PR #279 adds the single new synthesis seam module `RHLean.Analysis.PrimeSieveQuotientPNTError`.
- `README.md`, `MODULES.md`, this provenance note, the boundary policy, and other synthesis-facing explanatory files are export-specific documentation.

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

The existing PNT-centering module

```text
RHLean.Analysis.PrimeSievePNTCentering
```

uses the repository's singleton logarithmic-integral density

```text
density(q) = Li(q) - Li(q-1)
```

and proves

```text
H_{k,n} = centered PNT-corrected comb - 2 * centered prime error.
```

PR #279 adds

```text
RHLean.Analysis.PrimeSieveQuotientPNTError
```

with the same Git blob in the parent and synthesis trees. It proves that for positive `d=floor(x/q)` the literal quotient fibre is the reciprocal interval

```text
max(y, floor(x/(d+1))) < q <= floor(x/d),
```

that the singleton Li masses telescope across this interval, and that the exact PNT error is

```text
sum_d M(d) *
  (prime count on reciprocal interval - Li mass of reciprocal interval).
```

It also reindexes the deterministic PNT bulk and exact prime tail, proves the deterministic Li contribution cancels algebraically in the corrected all-plus identity, and pushes the reciprocal-interval error through the same square-wheel zero-mode centering used by `H_{k,n}`.

These are exact finite realization, centering, and reindexing theorems. They assert no PNT error estimate, Bombieri-Vinogradov estimate, large-sieve estimate, RH-scale power saving, or new axiom. The centered PNT-corrected comb remains a separate analytic target from the explicit reciprocal-interval prime-distribution error.

## Synchronization invariant

The export is intended to be build-complete as a standalone Lean snapshot. Therefore:

1. `export_mobius_synthesis/RHLean.lean` must match the parent `RHLean.lean`.
2. Every internal module imported by that manifest must exist at the corresponding path below `export_mobius_synthesis/RHLean/`.
3. Mirrored Lean files should reuse the exact parent Git blobs rather than edited copies.
4. When the root manifest gains imports, the new modules and the updated manifest should be synchronized together.

Because the Lean files reuse the exact parent blobs, the synthesis export does not introduce alternate theorem statements or edited proofs. It is a publication snapshot of the audited formal source tree, with export-specific documentation and repository policy layered around it.

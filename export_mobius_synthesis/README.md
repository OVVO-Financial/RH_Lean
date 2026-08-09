# Möbius Synthesis

**Möbius Synthesis** joins the square-block and prime-wheel Möbius-cancellation developments into one machine-checked bridge. It is not a third independent route to the Riemann Hypothesis. Its role is to identify where the two coordinate systems describe the same arithmetic residual, expose the exact algebra already available from both tracks, and isolate the analytic estimates that remain open.

The canonical wording for the active proof route is frozen in `CURRENT_PROOF_ROUTE.md`. In particular, the PNT-centered decomposition is a diagnostic coordinate system; the live analytic target is signed cancellation in the combined reciprocal-interval representation of the canonical nonzero response, not separate RH-scale bounds for its two displayed pieces.

Companion standalone repositories:

- Square blocks: https://github.com/OVVO-Financial/square-block-mobius
- Prime wheels: https://github.com/OVVO-Financial/prime-wheel-mobius

The mathematical synchronization described here is pinned to the parent `RH_Lean` source snapshot identified in `SNAPSHOT.md`. The export root manifest contains **248 Lean modules**, and every imported `RHLean.*` module is mirrored below `export_mobius_synthesis/RHLean/` using the same Git blob as the parent development. See `SNAPSHOT.md` for provenance and `MODULES.md` for the synchronization inventory.

## Two coordinate systems, one residual

Square blocks expose the lifetime and geometric organization of the Möbius field: complete square-prefix endpoints, canonical factor geometry, transport, survivor and death-shell structure, ancestry, and signed Gram architectures.

Prime wheels expose the spectral and residue-class organization of the same field: exact Möbius recovery, finite-torus Fourier decomposition, conductor structure, Ramanujan reduction, divisor-boundary formulas, and Mertens transfer.

The synthesis identifies exact seams between these descriptions before any unresolved asymptotic estimate is invoked.

Let

- `L_k` and `U_k` be the synchronized primorial-block endpoints;
- `W_k = primorialMinimalWheelSystem k` be the minimal-torus wheel;
- `Q_k` be its modulus;
- `X_n = (n+1)^2 - 1` be a complete square-prefix endpoint;
- `R_k(x)` be the corrected wheel residual.

At a complete square sample inside the block, the checked square-wheel identity has the form

```math
R_k(X_n) = H_{k,n} + \rho_{k,n} R_k(U_k),
\qquad
\rho_{k,n} = \frac{X_n-L_k}{Q_k}.
```

The nonzero response `H_{k,n}` is represented in Lean by `squareWheelNonzeroSampleResponse`.

## Zero-mode elimination and contraction

`RHLean.Analysis.SquareWheelZeroModeElimination` removes the self-referential zero mode exactly. At a distinguished terminal complete square sample `n_*`,

```math
R_k(U_k) = \frac{H_{k,n_*}+T_{k,n_*}}{1-\rho_{k,n_*}},
```

where the terminal interpolation term satisfies the checked square-root-scale estimate

```math
|T_{k,n_*}|^2 < 9(U_k+1).
```

`RHLean.Analysis.SquareWheelQuantitativeBridge` proves that from synchronized block `k >= 2`,

```math
Q_k > 6U_k,
```

and therefore every complete square sample in the block has

```math
0 <= \rho_{k,n} < 1/6.
```

Thus the zero-frequency feedback is uniformly contractive and the incomplete terminal square is already at square-root scale. This self-coupling is not the RH obstruction.

The same module defines `primorialExpansionReindexedNumerator` and proves the exact bridge from the square-side nonzero response to the fully collapsed wheel numerator after zero-mode subtraction.

## Elementary prime-sieve seam

The current synthesis also contains an elementary square-root prime-sieve route into the same square-wheel object.

`RHLean.Proof.PrimeSievePostSqrtGap` proves, under `sqrt x < y`, the exact finite identity

```text
M_y^+(x) - M(x)
  = 2 * sum_{y < q <= x, q prime} M(floor(x/q)).
```

`RHLean.Proof.PrimeSieveSquareRootTransport` specializes this at `x = R^2 - 1`, `y = R` and identifies the pre-large-prime state with the existing square-block smooth and transport variables. This connects fresh-prime parity directly to the square-root transport term already present in the square-block development.

No prime-distribution estimate is used in this layer.

## PNT centering and reciprocal quotient intervals

`RHLean.Analysis.PrimeSievePNTCentering` splits the exact prime tail into a deterministic logarithmic-integral density bulk plus the exact prime-indicator discrepancy. Its singleton density is

```text
density(q) = Li(q) - Li(q-1).
```

After applying the actual square-wheel zero-mode centering, the canonical nonzero response is written exactly as

```math
H_{k,n}
  = \text{centered PNT-corrected comb}
    - 2\,\text{centered prime error}.
```

The synchronized module `RHLean.Analysis.PrimeSieveQuotientPNTError` reindexes the prime error by

```text
d = floor(x/q).
```

For every positive quotient, the literal fibre is proved equal to the reciprocal interval

```text
max(y, floor(x/(d+1))) < q <= floor(x/d).
```

The singleton Li masses telescope on each such interval. Consequently the exact PNT error becomes a finite Mertens-weighted family of classical prime-count-minus-Li discrepancies:

```text
sum_d M(d) *
  (prime count on reciprocal interval - Li mass on reciprocal interval).
```

The same module reindexes the deterministic PNT bulk and the exact prime tail, proves the deterministic Li contribution cancels algebraically in the corrected all-plus identity, and pushes the reciprocal-interval error through the square-wheel center.

The resulting checked synthesis identity is

```math
H_{k,n}
  = \text{centered PNT-corrected comb}
    - 2\,\text{centered Mertens-weighted reciprocal prime discrepancy}.
```

In Lean this is `primorialMinimalSquareWheelNonzeroResponse_eq_pntCorrected_sub_two_reciprocalError`, with the corresponding norm transfer in `norm_primorialMinimalSquareWheelNonzeroResponse_le_reciprocalPNT`.

The norm transfer is a valid exact inequality, but it is **not** the intended analytic strategy. Using it to impose independent RH-scale bounds on the two displayed terms and then applying triangle inequality can destroy the signed cancellation present in their difference.

## Current analytic boundary

The terminal quantitative criterion remains

```math
|H_{k,n}| \ll_{\varepsilon} (X_n+1)^{1/2+\varepsilon}
```

uniformly over synchronized complete-square samples. This is exactly the repository predicate `NonzeroResponseRHScale`.

That estimate is **not proved**.

The PNT-centered reciprocal-interval representation should be treated as a diagnostic coordinate system for this same object, not as two independent proof obligations. Writing

```math
H_{k,n}
  = C_{k,n}^{\rm PNT} - 2E_{k,n}^{\rm rec},
```

the live analytic theorem is the signed combined estimate

```math
\left|C_{k,n}^{\rm PNT} - 2E_{k,n}^{\rm rec}\right|
  \ll_\varepsilon X_n^{1/2+\varepsilon}.
```

The active strategy is therefore:

> **Prove signed cancellation in the combined reciprocal-interval representation of `H_{k,n}`, exploiting the many-`d`, short-interval structure without taking absolute values termwise.**

Finite diagnostics indicate that bounding `C^{PNT}` and `E^{rec}` separately loses substantial favorable cancellation. The naive strong-induction move of inserting an RH-scale pointwise bound for each lower-scale `M(d)` and taking absolute values produces an operator too large to close, so scale reduction alone is insufficient. The reciprocal-`d` family is also not directly a Bombieri-Vinogradov family: it consists of many ordinary reciprocal short intervals rather than residue classes modulo varying moduli.

Accordingly, a plausible next theorem must preserve the signs in the reciprocal-interval family, for example through a signed short-interval or dispersion estimate adapted to this geometry, or through another exact transformation that retains the cancellation. The theorem must explain why the **combined signed operator** saves roughly a square root; controlling the two pieces separately is not the canonical target.

No pointwise or averaged PNT-error theorem, short-interval prime theorem, Bombieri-Vinogradov estimate, large-sieve estimate, power saving, or unconditional proof of RH is claimed by the exact reductions already present.

If the required RH-scale bound for `H_{k,n}` is established, the existing zero-mode elimination, square interpolation, Mertens transfer, Mellin continuation, zeta identity continuation, and terminal RH bridge carry it through the remaining formal chain.

## What counts as synthesis progress

The repository should continue to use both initiatives in synthesis form. A useful exact theorem need not immediately improve the exponent on `H_{k,n}` if it genuinely creates a new square-block and prime-wheel bridge.

The `boundary-advance` policy therefore has two research lanes:

- **Quantitative frontier:** a theorem strictly improves the certified bound on the canonical nonzero response or proves the RH-scale predicate.
- **Cross-track synthesis:** a new exact theorem directly invokes established square-block and prime-wheel declarations and advances the shared bridge, transfer, sampling, compatibility, or residual architecture.

One-sided square-block work, one-sided prime-wheel work, imports that do not actually couple the tracks, and purely cosmetic alternate representations do not qualify as synthesis progress by themselves. See `boundary/BOUNDARY_POLICY.md` for the machine-enforced policy.

## Machine-checked status at the synchronized baseline

The checked source currently includes, among other results:

1. minimal-torus Möbius recovery on synchronized primorial blocks;
2. equality of the minimal and historical wheel residuals on the arithmetic range;
3. exact square sampling of the wheel residual;
4. exact zero-mode splitting and elimination;
5. square-root-scale terminal interpolation;
6. factor-six modulus separation and uniform `1/6` contraction;
7. exact expansion-reindexed numerator identification of the nonzero response;
8. Ramanujan and divisor-boundary reductions on the prime-wheel side;
9. elementary post-square-root prime-sieve and square-root transport identities;
10. exact PNT centering of the prime tail;
11. exact reciprocal quotient-fibre reindexing of the PNT error;
12. the reciprocal-interval representation and norm transfer for `H_{k,n}`;
13. Mertens, Mellin, zeta-continuation, and terminal RH transfer infrastructure.

These are exact structural, centering, reindexing, and transfer theorems. They do not by themselves provide the unresolved analytic cancellation estimate.

## Direct synthesis modules

The modules most directly relevant to the current synthesis seam include:

```text
RHLean.Proof.PrimeSievePostSqrtGap
RHLean.Proof.PrimeSieveSquareRootTransport
RHLean.Analysis.PrimeSievePNTCentering
RHLean.Analysis.PrimeSieveQuotientPNTError
RHLean.Arithmetic.PrimorialWheelMinimalTorus
RHLean.Arithmetic.PrimeProductLowerBound
RHLean.Analysis.SquareWheelNesting
RHLean.Analysis.SquareWheelQuadraticSampling
RHLean.Analysis.SquareWheelZeroModeElimination
RHLean.Analysis.SquareWheelQuantitativeBridge
RHLean.Analysis.PrimeWheelPeriodicRawBridge
RHLean.Analysis.PrimeWheelRawConductorMobiusReindex
RHLean.Analysis.PrimeWheelRawBoundaryMobiusPairing
RHLean.Analysis.PrimeWheelRawBoundaryExpansionCollapse
RHLean.Analysis.PrimeWheelFullConductorUniformPacket
RHLean.Analysis.PrimeWheelFullConductorMobiusReindexedResidual
RHLean.Analysis.PrimeWheelSmoothConductorMobiusReindex
RHLean.Analysis.PrimeWheelRamanujanIdentification
RHLean.Analysis.PrimeWheelRamanujanBoundaryReduction
RHLean.Analysis.PrimeWheelRamanujanBoundaryBulkReduction
RHLean.Analysis.RamanujanDivisorBoundary
RHLean.Analysis.RamanujanDivisorBoundaryBulk
RHLean.Analysis.PrimorialWheelMertensTransfer
RHLean.Analysis.MertensEnergyRHForward
RHLean.Analysis.MertensMellinLSeriesBridge
RHLean.Analysis.MertensMellinContinuation
RHLean.Analysis.MertensZetaIdentityContinuation
RHLean.Proof.TerminalMertensForward
RHLean.Proof.TerminalMertensReduction
RHLean.Proof.RiemannHypothesisBridge
RHLean.Proof.TerminalAxiomAudit
```

`MODULES.md` gives the fuller track-level inventory and records the **34-module increase** from the original 214-module synthesis snapshot to the current 248-module manifest.

## Repository layout

Inside `RH_Lean`, the synthesis staging export contains:

- `export_mobius_synthesis/README.md` — synthesis overview and current status;
- `export_mobius_synthesis/CURRENT_PROOF_ROUTE.md` — canonical wording for the active proof route and single live analytic target;
- `export_mobius_synthesis/MODULES.md` — source map and synchronization inventory;
- `export_mobius_synthesis/SNAPSHOT.md` — source provenance and copy policy;
- `export_mobius_synthesis/RHLean.lean` — authoritative import manifest;
- `export_mobius_synthesis/RHLean/` — mirrored Lean source tree;
- `export_mobius_synthesis/lakefile.lean`, `lean-toolchain`, and `lake-manifest.json` — pinned project metadata;
- `export_mobius_synthesis/boundary/` — quantitative and cross-track research ledgers and policy;
- `export_mobius_synthesis/.github/` — standalone-repository PR policy and workflow material;
- `export_mobius_synthesis/scripts/check_boundary_advance.py` — trusted boundary checker.

The staging export currently has no `paper/` directory. Nothing here is re-exported back into either companion repository.

## Verification

From the parent repository root:

```bash
lake build RHLean --wfail
```

From the export directory:

```bash
cd export_mobius_synthesis
lake build RHLean --wfail
```

The stronger synchronization invariant is that `export_mobius_synthesis/RHLean.lean` is the same Git blob as the parent `RHLean.lean`, and each mirrored Lean module reuses its parent blob. The synchronized `PrimeSieveQuotientPNTError.lean` module satisfies that invariant.

## Status convention

- **Machine checked** means the statement is represented by a checked theorem or definition in the synchronized Lean source.
- **Exact reduction** means finite algebra, reindexing, centering, or transfer with no asymptotic estimate smuggled in.
- **Open analytic target** means an estimate is still unresolved and must not be described as established.
- Numerical experiments and finite-range checks are diagnostic evidence only.

At the synchronized mathematical baseline, the square-wheel bridge, elementary prime-sieve seam, PNT centering, reciprocal quotient reindexing, and transfer infrastructure are machine checked. The RH-scale bound on the canonical nonzero response remains open.

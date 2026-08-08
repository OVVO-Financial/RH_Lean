# Möbius Synthesis

**Möbius Synthesis** combines the two standalone Möbius-cancellation tracks — square blocks and prime wheels — into a single shared analysis. It supersedes neither track: each remains a complete, independently checked development in its own repository. The purpose of the synthesis is narrower and stronger: to identify the exact seam where the two coordinate systems describe the same arithmetic residual, isolate the one remaining cancellation estimate, and make clear which parts are already exact algebra and which part is genuinely open analysis.

Companion standalone repositories:

- Square blocks: [https://github.com/OVVO-Financial/square-block-mobius](https://github.com/OVVO-Financial/square-block-mobius)
- Prime wheels: [https://github.com/OVVO-Financial/prime-wheel-mobius](https://github.com/OVVO-Financial/prime-wheel-mobius)

The synthesis should therefore be read as a **bridge repository**, not as a third independent route to the Riemann Hypothesis. Its value is that the square-block and prime-wheel reductions are not merely parallel RH-equivalent criteria: after the bridge identities are imposed, they are two coordinate descriptions of the same oscillating path up to explicit elementary boundary terms.

## Why nest square blocks inside prime wheels?

Square blocks expose the **lifetime structure** of the Möbius field. As the square-root cutoff advances, arithmetic sources are born, remain active for a finite lifetime, and eventually die. This makes square blocks well suited to canonical factor geometry, survivor identities, death shells, ancestry, and endpoint interpolation.

Prime wheels expose the **spectral structure** of the same field. Their residue-class organization admits finite Fourier decomposition, reduced additive conductors, Ramanujan identification, and ultimately divisor-boundary expressions. This makes prime wheels well suited to identifying exactly where signed cancellation must occur after all periodic and conductor bookkeeping has been removed.

Neither coordinate system sees what the other sees naturally. The synthesis becomes useful because square-prefix endpoints sit inside the arithmetic range of a wheel, and the wheel residual can be sampled exactly at those endpoints. Consecutive complete square increments are therefore differences of one common wheel-residual path. Conversely, every complete square sample is already a point on that wheel path. Once the wheel-side conductor shells have been collapsed to Ramanujan and divisor-boundary data, the apparent distinction between a square-block residual and a wheel residual becomes bookkeeping rather than a difference of arithmetic content.

That is the architectural strengthening supplied by the synthesis:

> The square and wheel criteria are not just separately equivalent to RH; their residuals are joined by exact identities before any unresolved asymptotic estimate is invoked.

## One residual, two coordinate systems

Let

- $L_k$ and $U_k$ denote the lower and upper endpoints of the synchronized primorial block indexed by $k$;
- $W_k$ denote the minimal-torus wheel `primorialMinimalWheelSystem k` attached to that block;
- $Q_k$ denote its modulus;
- $X_n=(n+1)^2-1$ denote the complete square-prefix endpoints;
- $R_k(x)$ denote the corrected wheel residual at an admissible point $x$.

The minimal wheel is not a different arithmetic model from the historical larger torus. On the entire synchronized block it has the same corrected Möbius recovery and the same integer residual. Only the ambient torus modulus is reduced. This matters because the zero-frequency coupling is proportional to the sampled interval length divided by that modulus, so replacing an oversized torus by the natural minimal one makes the self-coupling transparent rather than hiding it in an artificial scale.

On the wheel side, write $A_k(x)$, $B_k(x)$, and $C_k(x)$ schematically for the raw expansion boundary, retained conductor-one raw bulk, and smooth collapsed boundary-bulk pieces. Then

```math
F_k(x) := A_k(x) + B_k(x) - 2C_k(x).
```

The wheel residual is written

```math
R_k(x) = Q_k^{-1} F_k(x).
```

This schematic package now has an exact checked-in counterpart. `RHLean.Analysis.SquareWheelQuantitativeBridge` defines `primorialExpansionReindexedNumerator` from `primorialRawExpansionBoundaryPairing`, `primorialRawRetainedBulk`, and `primorialSmoothCollapsedBoundaryBulk`. The upstream raw-to-boundary and Möbius-reindexing steps are carried by `PrimeWheelRawConductorMobiusReindex`, `PrimeWheelRawBoundaryMobiusPairing`, `PrimeWheelRawBoundaryExpansionCollapse`, and the associated Ramanujan boundary and bulk modules.

On the square-sampling side the exact decomposition is cleaner. At a complete square endpoint inside the block,

```math
R_k(X_n) = H_{k,n} + \rho_{k,n} R_k(U_k),
\qquad
\rho_{k,n} = \frac{X_n-L_k}{Q_k}.
```

Here $H_{k,n}$ is the contribution of the nonzero additive frequencies, while $\rho_{k,n}R_k(U_k)$ is the additive zero mode. In Lean, the nonzero piece is represented by `squareWheelNonzeroSampleResponse`, and the full response is split exactly into that term plus `squareWheelSampleRatio` times the endpoint residual.

This identity is the key bridge. The difficult object is no longer an undifferentiated Mertens residual. It is the nonzero response $H_{k,n}$ after the self-referential zero frequency has been exposed explicitly.

## Exact elimination of the zero mode

Let $n_{\star}$ be the last complete square sample in the block and define the terminal tail by

```math
T_{k,n_{\star}} := R_k(U_k) - R_k(X_{n_{\star}}).
```

Substituting the square-sample identity at $n_{\star}$ and solving for the endpoint residual gives the exact algebraic elimination

```math
R_k(U_k) = \frac{H_{k,n_{\star}} + T_{k,n_{\star}}}{1-\rho_{k,n_{\star}}}.
```

This is not an asymptotic heuristic. The generic wheel identity is machine checked in `RHLean.Analysis.SquareWheelZeroModeElimination` as `primeWheelEndpointResidual_eq_eliminated`. The same module proves interpolation from a complete square sample to an arbitrary later point of the same primorial block and records the squared terminal estimate

```math
|T_{k,n_{\star}}|^2 < 9(U_k+1).
```

Thus the incomplete terminal square is already at square-root scale. It cannot be the source of an exponent larger than the RH exponent. Once the denominator is bounded away from zero, the endpoint residual is controlled by $H_{k,n_{\star}}$ plus an explicitly harmless square-root term.

The module also proves the corresponding eliminated formula for every other square sample: after one distinguished sample removes the endpoint zero mode, every complete square residual in the block depends only on nonzero responses and the same short terminal tail.

## Quantitative contraction

The strict inequality $\rho_{k,n}<1$ follows as soon as the wheel modulus lies beyond the arithmetic endpoint. The stronger uniform contraction is now also machine checked.

Put

```math
y = \lfloor \sqrt{U_k} \rfloor.
```

For $y\ge5$, the strengthened Bertrand argument gives

```math
\prod_{q\le y} q > 3y.
```

Consequently, from synchronized block $k\ge2$ onward,

```math
Q_k > 6U_k.
```

Therefore every complete square sample in the block satisfies

```math
0 \le \rho_{k,n} < \frac{1}{6}.
```

The relevant checked-in theorems in `RHLean.Analysis.SquareWheelQuantitativeBridge` and its arithmetic namespace are:

- `three_mul_lt_primeProductUpTo`;
- `six_mul_primorialBlockUpper_lt_squareSensitiveModulus`;
- `six_mul_primorialBlockUpper_lt_minimalTorusModulus`;
- `primorialMinimalSquareSampleRatio_lt_one_sixth`;
- `primorialMinimalSquareSampleRatio_nonneg`.

Consequently

```math
\frac{1}{1-\rho_{k,n_{\star}}} \le \frac{6}{5},
```

and the exact eliminated identity gives

```math
|R_k(U_k)| \le \frac{6}{5}\left(|H_{k,n_{\star}}| + 3\sqrt{U_k+1}\right).
```

This is the quantitative reason the zero mode is no longer the analytic obstruction: its feedback coefficient is uniformly contractive, while the terminal interpolation term is already of RH size. The finitely many initial blocks below the $k\ge2$ range remain separate finite cases.

## Exact reindexed numerator bridge

The synthesis seam now contains the exact reindexed numerator identity that the earlier staging README described only schematically. `SquareWheelQuantitativeBridge` defines `primorialExpansionReindexedNumerator` and proves

- `primorialMinimalSquareWheelNonzeroResponse_eq_expansionReindexed`;
- `primorialMinimalSquareWheelNonzeroResponse_eq_explicitExpansionReindexed`.

These theorems identify the square-side nonzero response with the fully collapsed wheel numerator on the minimal torus, with the endpoint zero mode removed explicitly. The point is not another decomposition for its own sake: the identity fixes the arithmetic object on which the remaining cancellation estimate must act.

## What the two tracks contribute

### Square-block side

The square-block development supplies the geometry and lifetime organization needed to understand complete square increments. Among the exact structures already present are:

- square-prefix Mertens endpoints and interpolation;
- canonical largest-prime and cofactor decomposition;
- low-height and high-height sector separation;
- squared-complex and Fermat-coordinate cofactor geometry;
- square-root transport and dyadic compression;
- lifetime active sets, survivor reduction, and death-shell identities;
- canonical gap and ancestry constructions;
- zero-cutoff ancestry and square-root ancestry root and successor constructions;
- signed Gram and terminal quadratic architectures.

The synthesis does not replace these objects. It uses them to identify what $H_{k,n}$ means geometrically.

### Prime-wheel side

The prime-wheel development supplies the spectral and residue-class organization of the same arithmetic field. Its exact reductions include:

- deterministic Möbius reconstruction on a synchronized wheel block;
- finite-torus Fourier pairing;
- arithmetic, complete, local, and joint spectra;
- reduced additive conductors and conductor Gram decompositions;
- periodic raw response and coconductor subtraction;
- raw and smooth conductor Möbius reindexing;
- raw boundary pairing and expansion collapse;
- full-conductor uniform packets and the reindexed residual;
- classical Ramanujan identification;
- divisor-residue boundary and bulk reductions;
- transfer from wheel residuals back to Mertens sums.

The synthesis uses these reductions to identify what $H_{k,n}$ means spectrally: it is the nonzero part remaining after the additive zero frequency is removed, with the wheel machinery exposing the conductor and divisor-boundary cancellation available inside that term.

## What is proved

At the level of the current machine-checked source, the synthesis rests on the following exact facts.

1. **Minimal-torus recovery.** `primorialMinimalWheelSystem` recovers Möbius exactly on the synchronized arithmetic block, and its residual agrees there with the historical primorial-wheel residual.
2. **Natural period from nontrivial blocks onward.** For $k\ge2$, the minimal lift multiplier is one, so the minimal torus modulus is the natural square-sensitive period.
3. **Square sampling.** The wheel residual at a complete square endpoint is represented by the square-wheel response.
4. **Zero-mode splitting.** The square response is exactly the sum of `squareWheelNonzeroSampleResponse` and the zero-frequency endpoint coupling.
5. **Zero-mode elimination.** The endpoint residual can be solved exactly in terms of one nonzero response and one terminal tail.
6. **Square-root interpolation.** The terminal tail has squared norm strictly below $9(U_k+1)$.
7. **Uniform contraction.** From $k\ge2$, the minimal-torus square-sample ratio lies in the interval $[0,1/6)$.
8. **Reindexed numerator bridge.** The nonzero square response is identified exactly with the collapsed expansion-reindexed wheel numerator after zero-mode subtraction.
9. **Ramanujan reduction.** The prime-wheel spectrum is identified with classical Ramanujan data and reduced to boundary and bulk divisor terms.
10. **Mertens and zeta transfer.** The wheel and Mertens criteria are connected to the terminal RH bridge, with the forward Mertens, Mellin, and zeta-continuation modules included in the synchronized source tree.

These are structural and transfer statements. None of them supplies the final cancellation estimate for the nonzero response.

## The one remaining open target

After the two coordinate systems are joined and the zero mode is eliminated, the remaining analytic target can be stated once.

**Open target**

```math
|H_{k,n}| \ll_{\varepsilon} (X_n+1)^{1/2+\varepsilon}.
```

The estimate is required uniformly for complete square samples inside the synchronized wheels.

This is the point of the synthesis. Square geometry has already exposed and eliminated the self-referential zero mode and bounded the incomplete terminal square. Wheel geometry has already exposed the nonzero conductor organization, its Möbius reindexing, and its Ramanujan and divisor-boundary form. What remains is a genuine cancellation estimate for the signed nonzero response.

That estimate is **not proved** in this repository.

If it is established uniformly, the eliminated identity transfers it to the wheel endpoint residual with only a square-root terminal loss and the bounded contraction factor. Square-gap interpolation then propagates the estimate through the block. The existing Mertens-transfer and RH-bridge machinery converts the resulting Mertens bound into the classical RH criterion. Conversely, the RH-scale Mertens bound controls the same sampled residuals, so the synthesis target isolates the same analytic difficulty rather than introducing a stronger conjecture by accident.

No unconditional proof of the Riemann Hypothesis is claimed here or in either companion repository.

## Why no further decomposition is the default

The architecture is intentionally frozen at the level of exact reductions. A new identity is useful only if it advances the bound on $H_{k,n}$ itself. Repackaging the same residual into another exact basis, another bookkeeping hierarchy, or another formally equivalent energy without producing quantitative cancellation does not move the remaining theorem.

Accordingly, the default research question for any proposed addition is:

> Does this statement produce a uniform gain toward the open bound below?

```math
|H_{k,n}| \ll_{\varepsilon} (X_n+1)^{1/2+\varepsilon}.
```

If not, it belongs upstream in one of the companion structural tracks rather than downstream at the synthesis endpoint.

## Machine-checked source map

The current `export_mobius_synthesis` tree is a **full import-audited snapshot** of the parent `RH_Lean` development at the recorded synchronization state, not a minimized bridge-only transitive closure. `RHLean.lean` imports **235 modules**, and every corresponding internal source file is mirrored under `RHLean/` using the same Git blob as the parent source. See [`SNAPSHOT.md`](SNAPSHOT.md) for provenance and [`MODULES.md`](MODULES.md) for the track-level inventory and synchronization delta.

The modules most directly relevant to the synthesis seam are:

```text
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

The formal source is the authority for exact declaration names and theorem signatures. `MODULES.md` records the 21-module synchronization delta from the original 214-module export.

## Repository layout

Inside `RH_Lean`, the current synthesis staging export has the following shape:

- `export_mobius_synthesis/README.md` — this synthesis overview and status boundary;
- `export_mobius_synthesis/MODULES.md` — mathematical source map and synchronization inventory;
- `export_mobius_synthesis/SNAPSHOT.md` — parent-source provenance and copy policy;
- `export_mobius_synthesis/RHLean.lean` — authoritative import manifest for the exported Lean snapshot;
- `export_mobius_synthesis/RHLean/` — the full copied Lean source tree;
- `export_mobius_synthesis/lakefile.lean`, `lean-toolchain`, and `lake-manifest.json` — pinned project metadata matching the parent development.

The current staging export does **not** contain a `paper/` directory, so this README does not advertise a manuscript build command that would fail in the checked-in tree. Paper-build instructions should be restored when the synthesis manuscript is actually included in the standalone publication repository.

Nothing in this staging export is re-exported back into `square-block-mobius` or `prime-wheel-mobius`. The companion repositories remain independently publishable snapshots of their respective tracks.

## Verification

From the parent `RH_Lean` repository root, the authoritative full-development command is:

```bash
lake build RHLean --wfail
```

The synthesis export carries matching Lake metadata. After entering the export directory, the corresponding snapshot build is:

```bash
cd export_mobius_synthesis
lake build RHLean --wfail
```

The export synchronization invariant is stronger than the README inventory: its `RHLean.lean` is the same blob as the parent root manifest, and each newly synchronized Lean module reuses the exact parent blob.

## Status convention

The synthesis uses a strict status boundary.

- **Machine checked** means the statement is represented by a theorem or definition in the checked-in Lean source and follows from the imported development.
- **Open theorem** means the analytic estimate is unresolved and must not be described as established.
- Numerical experiments and finite-range checks are diagnostic evidence only; they are not promoted to asymptotic theorems.

Under that convention, the exact square-wheel bridge, zero-mode elimination, factor-six modulus separation, uniform $1/6$ contraction, expansion-reindexed numerator bridge, minimal-torus recovery, and square-root terminal interpolation are machine checked. The uniform RH-scale bound on $H_{k,n}$ remains open.

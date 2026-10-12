# RH_Lean

Lean 4 formalization of the classical von-Koch prime-counting criterion
in a square-tiled VF coordinate, plus the genuinely open signed
actual-prime and Möbius arithmetic research.

> **2026-10-12 CANONICAL VF — the only current PUBLIC VF definition is**
>
> \( VF(x)=\sqrt2+\sum_{r=2}^{R-1}(2r+1)/\log(r^2+r+1/2)
>   +(x-R^2)/\log((R^2+x)/2),\quad R=\lfloor\sqrt x\rfloor,\ x\ge4. \)
>
> The original vfMid / owner-cell source, historical x=9 c0,
> integer-floor and fractional-seat plots remain UNCHANGED INTERNAL COORDINATES
> and need an explicit proven phase translation to be used as current VF.

**Status (2026-10-12): finite A, finite C and RH remain unproved.**
The repository contains exact square wheel/prime-owner arithmetic,
an unconditional square-endpoint **VF_raw-Li_2 = O(1)** theorem, and now
[PR #932](https://github.com/OVVO-Financial/RH_Lean/pull/932) adds the
missing **all-real** \(VF_{\rm raw}-Li_2=O(1)\) Lean assembly and the
new canonical sqrt2 vertical-phase interface. **New Lean compilation is
required before calling those newly proposed theorems verified.**
The classical von-Koch ↔ RH theorem remains an explicitly supplied
formal interface; the actual-prime von-Koch inequality is open.

Start with the [definitive full VF autopsy](research/VF_CANONICAL_SQRT_TWO_AUTOPSY_2026_10_12.md),
[canonical VF Lean API](research/VF_CANONICAL_SQRT_TWO.lean),
[all-real quadrature](research/VF_CANONICAL_ALL_REAL_LI_O_ONE.lean), and
[canonical von-Koch reduction](research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean).
See [current proof contract](CURRENT_PROOF_CONTRACT.md) and
[research search/DAG](docs/REPOSITORY_SEARCH.md) for theorem provenance.

## Canonical VF target (supersedes the older raw-VF public wording)

Let \(F_R=\sum_{2\le r<R}V_r\), \(V_r=(2r+1)/\log(r^2+r+1/2)\).
The **single real public endpoint** and actual-prime discrepancy are

\[
VF_{\rm can}(R^2)=F_R+\sqrt2,\qquad
D_R^{\rm can}:=\pi(R^2)-F_R-\sqrt2.
\]

The live proof target is exactly

\[
\boxed{\exists C\ge0\ \forall R\ge2:
|D_R^{\rm can}|\le CR\log R.}
\]

The new Lean statement is **VFCanonicalSquareVonKochStatement**.
Its canonical⇔legacy theorem establishes exact equivalence (with
renormalized constants) to the existing, HISTORICAL
**VFMidSquareEndpointVonKochBoundedStatement**; the latter is NOT
silently redefined or deleted.

The signed source is still genuinely arithmetic and unchanged:

\[
\boxed{D_{R+1}^{\rm can}
 =D_R^{\rm can}+\big(P_R-V_R\big),}
\]

where \(P_R=\pi((R+1)^2)-\pi(R^2)\) counts actual primes and
\(V_R\) is the original midpoint block mass.

**Sharper deterministic result:** old primary Lean modules already proved
the uniform completed-square quadrature bound and separately a uniform
LIVE-band quadrature bound; their sum yields

\[
\boxed{VF_{\rm can}(x)-Li_2(x)=O(1)\quad\text{FOR ALL REAL }x\ge4,}
\]
not merely \(O(\sqrt x)\) or an endpoint-only \(O(1)\).
This is deterministic; it is NOT a bound on \(\pi-VF_{\rm can}\).
The standard \(li\) differs from \(Li_2=\int_2^x dt/\log t\) by a
constant, and MUST be distinguished in numerical plots and theorem names.

Old corner/phase/floor/fractional and historical c0 results remain
meaningful derived diagnostics; no fixed-phase graph crossing for every
block is assumed. The arithmetic first-bad signed historical/current
payment is still open.

## Finite A / finite C: separate sufficient alternative (PR #929)

The [finite-A/C alignment and original-VF autopsy contract](research/FINITE_A_C_VF_ALIGNMENT_2026_10_11.md) reconciles the newer [Euler square-root research](research/SEQUENTIAL_EULER_SQUARE_BLOCK_FINITE_C_A_RESEARCH_NOTE.md) with the canonical direct VF run-level program.

Write \(X_R=R^2-1\), \(K_R=\max_{0\le y<R}(M(y)-1)^2/(y+1)\) and let \(Q_R=2M(R-1)-M(X_R)\), equivalently its original historical bilinear floor sum. The assertions
\[
\exists C<\infty\ \forall R\ge2:\ |Q_R|\le CR\sqrt{K_R},
\qquad
\exists A<\infty\ \forall R\ge2:\ (M(X_R)-1)^2\le AR^2K_R
\]
are **equivalent as existence claims** and are sufficient for the existing conditional Mertens-energy-to-RH chain. **Neither is proved.** These Mertens A/C constants are not the coefficient of the canonical VF radial wall, and neither route assumes a random Möbius process.

The signed-packet autopsy already reconstructs the actual prime-factor genealogy, density-preserving multiplier signs, chronological square clocks, first-owner pair Fubini and exact live odd-annulus Gram \(\Gamma_R\). A proposed bound \(\Gamma_R\le BR^2K_R\) is **equivalent to the original missing finite-A estimate**; it is not a free consequence of squarefree density, exact sign flips, or near-zero aggregate correlations. Distinct simultaneous live odd packets cannot be direct prime multiples. The autopsy's no-independent-persistence and sector-six descent infrastructure is already present; what remains unproved on the VF route is the original-weight actual-prime source/unfinished-run payment.

PR [#929](https://github.com/OVVO-Financial/RH_Lean/pull/929) includes finite exact arithmetic experiments through R=20,000 and paper-level cutoff/asymptotic arguments. The finite scans, a green documentation check, and existing conditional Lean consumers do **not** establish a universal bound or RH.

## What the recent closeout establishes

| Work | Result | What remains |
| --- | --- | --- |
| #796–#797: completed branch and top-two Stokes | The global assembly is exactly `Q_R² + S_R`, with `S_R = G_R² + 2 Q_R G_R − D_R`. | The top-scale gap `G_R` survives. |
| #798: correlation comparison and unconditional bound | The remainder is quantitatively comparable to the CORR square; the existing subexponential Mertens theorem bounds it globally. | That bound is too large for the RH consumer. |
| #799: Möbius inversion | `bornSmooth + farSurvivor = M(R² − 1) + E_root` exactly. | The identity supplies no RH-scale estimate of the top Mertens value. |
| #800: K₂ diagnostic closeout | The existing signed K₂ comparison retains the PNT error with a logarithmic weight; the finite probe is reproduced in CI. | No new control of the zero-driven component. |

Further searches among these existing internal identity families are frozen
pending new quantitative input. This records the scope of the tested routes;
it is not an impossibility theorem for all elementary approaches.

## Verification

The development library is pinned by [`lean-toolchain`](lean-toolchain) and
[`lake-manifest.json`](lake-manifest.json). To run the local development checks:

```bash
bash scripts/local_ci.sh
```

Hosted checks are selected by changed paths. The library workflow checks source
and import audits, builds the library, rejects repository-owned warnings, and
validates the exact declaration graph. Research modules outside `RHLean/` have
explicit workflow gates; they are not silently added to the generated library
root. Exports are separate Lake projects. See the [verification map](docs/DOCUMENTATION_INDEX.md#verification-map)
for their commands and the research workflows.

The [terminal axiom audit](RHLean/Proof/TerminalAxiomAudit.lean) guards the
standard logical axiom footprint of the named terminal implications. A clean
axiom list does not discharge ordinary theorem hypotheses. Finite numerical
runs are diagnostics, never uniform bounds or Lean certificates by themselves.

## Contribution rules

Read [`AGENTS.md`](AGENTS.md), the current proof contract, and the
[formalization checklist](FORMALIZATION_CHECKLIST.md) before changing the proof.
Work through PRs, preserve counterexamples, keep every signed compensation term
until reassembly is complete, and verify CI on the exact final commit.

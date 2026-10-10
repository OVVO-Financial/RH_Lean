# RH_Lean

Lean 4 formalization of the square-prefix and direct VF-mid programs.

> **Guiding light: close RH through VF.  Prove the RH-scale cumulative
> `pi - VF_mid` bound; do not replace it with a stronger block-by-block
> crossing statement merely because that stronger statement fits finite data.**

**Status (2026-10-01): no unconditional proof of the Riemann hypothesis is
claimed.** The repository proves the exact VF square-block construction, its
unconditional Li quadrature bridge, exact prime/common-wheel survivor
identities, and conditional implications from a direct VF discrepancy bound to
Mathlib's `RiemannHypothesis`. The remaining task is the arithmetic bound
itself.

Start with [`CURRENT_PROOF_CONTRACT.md`](CURRENT_PROOF_CONTRACT.md) for the
current target and exact Lean interfaces. The
[documentation index](docs/DOCUMENTATION_INDEX.md) distinguishes current
instructions, append-only research history, numerical diagnostics, and exports.
Use the [repository search and import DAG](docs/REPOSITORY_SEARCH.md) to find
existing results across the library, research, documents, scripts, exports, and
fetched PR refs. `python3 scripts/proofq.py repo-search 'SectorSix' --scope research`
is a starting point for the current first-bad work.

## Canonical VF target

At square endpoints define

```text
D_R = pi(R^2) - vfMidFinishedMass R.
```

The live target is

```text
exists C >= 0, for every natural R >= 2,
  |D_R| <= C R log R.
```

In Lean this is `VFMidSquareEndpointVonKochBoundedStatement`. The compiled
VF/Li bridge extends it to real cutoffs and transfers it to the classical
von-Koch prime-counting scale; the existing RH consumer then closes the route.

The exact square-block recurrence is

```text
D_(R+1) = D_R + P_R - m_R,
```

where `P_R` is the exact prime/common-wheel survivor population of block
`R`, and `m_R = vfMidBandMass R` is the deterministic VF midpoint mass.
The central problem is therefore signed cumulative control of the survivor
error `P_R - m_R`.

A fixed aligned VF step graph can intersect `pi` over very long finite
ranges and is useful diagnostic geometry.  Universal fixed-phase
block-by-block intersection is nevertheless too strong: it would impose a
one-sided `O(sqrt(x)/log(x))` upper bound on positive `pi-Li` excursions,
incompatible with classical Littlewood oscillation.  The fixed-alignment
results are retained only as conditional sufficient lemmas.  Their failure as
a universal target does **not** weaken the legitimate
`O(R log R)` VF program.

The older CORR-4/Mertens route remains preserved as alternative infrastructure;
it is not the canonical research target.

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

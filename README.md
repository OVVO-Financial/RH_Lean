# RH_Lean

Lean 4 formalization of the square-prefix Möbius program.

**Status (2026-09-26): no unconditional proof of the Riemann hypothesis is
claimed.** The repository proves exact arithmetic identities, obstruction
results, and implications from explicit quantitative estimates to Mathlib's
`RiemannHypothesis`. The remaining task is to prove the required estimate.

Start with [`CURRENT_PROOF_CONTRACT.md`](CURRENT_PROOF_CONTRACT.md) for the
current target and its exact Lean interfaces. The
[documentation index](docs/DOCUMENTATION_INDEX.md) distinguishes current
instructions, append-only research history, numerical diagnostics, and exports.

## The remaining estimate

At the square endpoint `X = R² − 1`, write

```text
G_R = M(R² − 1) − M(R − 1),
E_R = sum over odd primes q with q² < R of M(floor((R² − 1)/q²))².
```

The compiled CORR-4 consumer accepts a fixed `C >= 0` such that, for every
`R >= 56` and every admissible lower Mertens envelope `K`,

```text
G_R² <= 4 E_R + C R² K.
```

The contract gives the precise envelope, quantifiers, equivalent full/low
owner formulations, and sufficient Stokes/remainder coefficient thresholds.
This inequality is **open**. Exact reassembly and a small reciprocal-square
budget do not establish it.

The forward analytic bridge is already internal:
[`riemannHypothesis_of_mertensEnergy`](RHLean/Analysis/MertensEnergyRHForward.lean)
and the [square-prefix terminal theorem](RHLean/Proof/TerminalMertensForward.lean)
need the energy estimate, without a separate `ClassicalMertensRHCriterion`
argument. Historical two-way equivalences that take that argument remain
conditional as written; the reverse direction is unnecessary for this route.

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

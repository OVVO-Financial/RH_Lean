# Research closeout map

For source discovery across all current research modules and fetched PR refs,
use the [repository search and import DAG](../docs/REPOSITORY_SEARCH.md):
`python3 scripts/proofq.py repo-search 'SectorSix' --scope research`.
The historical table below is not a complete module catalog; the generated
index lists every current source occurrence and preserves its provenance.

The [current proof contract](../CURRENT_PROOF_CONTRACT.md) specifies the
CANONICAL direct VF-mid cumulative prime-error bound and the still-open
multi-block actual-owner source/terminal/sector-six payment. The older CORR-4
estimate remains an ALTERNATIVE, not the canonical requirement. The
[finite-A/C alignment contract](FINITE_A_C_VF_ALIGNMENT_2026_10_11.md)
indexes the independently sufficient but still-open Mertens square-root
amplification route in PR #929, its actual Möbius/gcd sign autopsy, and the
prohibited circular assumptions. The [documentation index](../docs/DOCUMENTATION_INDEX.md)
explains authority and verification. No unconditional finite A, finite C,
or RH proof is claimed.

| Recent result | Source | Evidence |
| --- | --- | --- |
| #797: completed branch / top-two gate | [Branch-gate composition](GLOBAL_RETURNED_CORE_TOP_TWO_BRANCH_GATE_COMPOSITION.lean) | Warning-fatal Lean check; finite probe in `experiments/`. |
| #798: remainder and CORR comparisons | [Correlation equivalence](GLOBAL_RETURNED_CORE_POST789_CORRELATION_EQUIVALENCE.lean) | Warning-fatal Lean check. |
| #798: available unconditional estimate | [Global bound](GLOBAL_RETURNED_CORE_POST789_UNCONDITIONAL_GLOBAL_BOUND.lean) | Compiled subexponential input; insufficient for the RH consumer. |
| #799: global cancellation identity | [Möbius inversion](MOBIUS_INVERSION_GLOBAL_CANCELLATION.lean) | Warning-fatal Lean check and exact finite identities. |
| #800: signed K₂ closeout | [K₂ note](K2_COHERENT_MODE_KILL_GATE.md) | Existing Lean summatory comparison, classical series derivation, and floating-point diagnostic, labeled separately. |
| #929: exact finite A/C ↔ Mertens endpoint bridge, owner ancestry, true Möbius densities | [Finite A/C ↔ VF alignment](FINITE_A_C_VF_ALIGNMENT_2026_10_11.md) | Exact identities / numerical diagnostics; conditional Lean consumer; independent uniform positive signed remainder estimate still OPEN. |

Earlier notes are historical route records. Read their exact carriers and
compiled declarations before reusing them. Searches among the existing
internal identity families are frozen pending new quantitative input;
the freeze is not a theorem excluding all future elementary approaches.

Research modules are outside the generated `RHLean.lean` surface and must be
checked through the workflow that builds their dependency closure. Merely
placing a `.lean` file in this directory does not give it kernel-checked status.

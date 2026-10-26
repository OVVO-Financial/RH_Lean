# RH_Lean

Lean 4 formalization of the classical von Koch prime-counting criterion
in a square-tiled VF coordinate, plus the genuinely open signed
actual-prime and Möbius arithmetic research.

**Status (2026-10-26 UTC evidence snapshot, main `54564c00`, Lean 4.34.1): the Riemann Hypothesis is not proved here.** The repository has completed a Lean reduction of the von Koch criterion to an explicit actual-prime inequality, an unconditional uniform VF − Li₂ bound, an imported unconditional 7/8 Mertens benchmark, and many exact structural results. Every route to RH still has an open arithmetic input; see the [proof-dependency DAG](docs/PROOF_DEPENDENCY_DAG.md) and [formalization milestones](docs/FORMALIZATION_MILESTONES.md).

## Major Formalization Milestone: von Koch (1901) and the Canonical VF Prime-Counting Criterion

**Classical theorem.** H. von Koch, *Sur la distribution des nombres premiers*, Acta Mathematica **24** (1901) 159–182 (doi:10.1007/BF02403071), proved that RH implies π(x) = Li(x) + O(√x log x); with the classical converse this is the criterion RH ⇔ π(x) − Li(x) = O(√x log x). Using Li₂(x) = ∫₂ˣ dt/log t instead of li changes only an additive constant.

**Formalized in Lean on main** by merged [PR #932](https://github.com/OVVO-Financial/RH_Lean/pull/932) (2026-10-12; merged head `2713d8ef495e24164a13a5eb34e3b4ba70a3377e`, 13 workflow runs / 17 jobs green, including warning-fatal compilation and axiom printing in [vf-canonical-sqrt-two.yml](.github/workflows/vf-canonical-sqrt-two.yml)):

| Milestone | Lean declarations | Content |
| --- | --- | --- |
| Canonical VF | [`vfCanonical`](research/VF_CANONICAL_SQRT_TWO.lean), `vfCanonicalSquareDefect_succ`, `vfCanonicalPrimeLiError_eq_primeError_add_quadrature` | The unique public VF_can(x) = √2 + Σ_{r=2}^{R−1} (2r+1)/log(r²+r+1/2) + (x−R²)/log((R²+x)/2), R = ⌊√x⌋, with the exact actual-prime block recurrence. |
| VF_can − Li₂ = O(1) | [`abs_vfCanonicalLiError_le_uniform_allReal`](research/VF_CANONICAL_SQRT_TWO.lean), [`abs_vfMidLiError_le_uniform_allReal`](research/VF_CANONICAL_ALL_REAL_LI_O_ONE.lean), `vfMidLiAllRealUniformBounded` | Unconditionally bounded on **every real x ≥ 4**; stronger than the deterministic input the reduction needs. |
| von Koch reduction | [`vfCanonicalSquareVonKoch_iff_primeLiVonKoch`](research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean), `vfCanonicalRealVonKoch_iff_primeLiVonKoch`, `vfCanonicalSquareVonKoch_iff_realVonKoch`, [`vfMidSquareEndpointVonKochBounded_iff_primeLiVonKochBounded`](research/VF_MID_VON_KOCH_BRIDGE.lean) | (∃C ∀R ≥ 2, \|π(R²) − VF_can(R²)\| ≤ C R log R) ⇔ (∃C′ ∀x ≥ 4, \|π(x) − Li₂(x)\| ≤ C′ √x log x), constants renormalized. |
| Conditional consumer | [`riemannHypothesis_of_vfCanonicalSquare`](research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean) | `ClassicalVonKochRHCriterion → VFCanonicalSquareVonKochStatement → RiemannHypothesis`. |

**Interface status.** The historical analytic equivalence enters Lean only as the explicit argument [`ClassicalVonKochRHCriterion`](research/VF_MID_VON_KOCH_BRIDGE.lean); constructing it (by import or proof) is an open *formalization-completeness* task, not new mathematics. `#print axioms` does not report such theorem arguments.

**What remains open.** The actual-prime bound `VFCanonicalSquareVonKochStatement`: ∃C ≥ 0 ∀R ≥ 2, |π(R²) − VF_can(R²)| ≤ C R log R. The equivalence is proved; the inequality for actual primes is not. Completing the reduction did not prove its hypothesis.

## Current research status

Ten stable routes are tracked in the [proof-dependency DAG](docs/PROOF_DEPENDENCY_DAG.md) (registry [proof-obligations.json](docs/proof-obligations.json)) and routed to seven specialists by the [portfolio](docs/RH_PROOF_ATTACK_PORTFOLIO_20261024.md): VF-LOW, SAT, CODIV, BLOCK, OAI-NNS, JOH, FINITE-AC, CORR4, MU-LIFT, NYMAN. The literal universal block-capture form of BLOCK is **refuted** at R = 549. Merged [#987](https://github.com/OVVO-Financial/RH_Lean/pull/987) imports the original unconditional OpenAI proof of M(x) = O_ε(x^{7/8+ε}); no strict improvement below 7/8 has been verified. Current leads: a signed CORR4 first-owner mixed-tail inequality (merged [#1021](https://github.com/OVVO-Financial/RH_Lean/pull/1021) proves the *conditional* Gram/Mertens power biconditional; merged [#1023](https://github.com/OVVO-Financial/RH_Lean/pull/1023) sharpens the unsigned frame only), a nonlocal prime-chronology law for VF-LOW/JOH, and a complete OAI-NNS exponent ledger (merged [#1022](https://github.com/OVVO-Financial/RH_Lean/pull/1022) proves a source-local zero-mode, not a global saving). No strict exponent below 7/8 is proved. Consult the dated DAG evidence rather than inferring PR state from historical prose.

> **2026-10-12 CANONICAL VF — the only current PUBLIC VF definition is**
>
> \( VF(x)=\sqrt2+\sum_{r=2}^{R-1}(2r+1)/\log(r^2+r+1/2)
>   +(x-R^2)/\log((R^2+x)/2),\quad R=\lfloor\sqrt x\rfloor,\ x\ge4. \)
>
> The original vfMid / owner-cell source, historical x=9 c0,
> integer-floor and fractional-seat plots remain UNCHANGED INTERNAL COORDINATES
> and need an explicit proven phase translation to be used as current VF.

**Status (updated 2026-10-14): finite A, finite C and RH remain unproved.**
The repository contains exact square wheel/prime-owner arithmetic,
an unconditional square-endpoint **VF_raw-Li_2 = O(1)** theorem, and merged
[PR #932](https://github.com/OVVO-Financial/RH_Lean/pull/932) introduced the
all-real \(VF_{\rm raw}-Li_2=O(1)\) Lean assembly and canonical sqrt2 vertical-phase interface. The actual-prime von Koch inequality remains unproved.
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

## Historical status notes

**Research direction recorded 2026-10-14 (historical):** the seven specialist agents are centrally routed via [AGENTS.md](AGENTS.md) and the [current proof contract](CURRENT_PROOF_CONTRACT.md) toward an **independent signed actual-prime arithmetic replacement** for the continuous Li model's non-transferable *absolute* critical Poisson collision bound. Floor-Li's O(1) rounding and exact actual-minus-floor-Li transport are already proven algebra; they do not bound the genuine unmatched prime population. The continuous Li-density critical collision sum is finite, whereas simply inserting the actual prime indicator yields the divergent unsigned sum of reciprocal primes. No global signed NNS source payment, finite A/C, or RH is proved. PRs #938/#939 are merged logical/payment audits; #941–#943 are merged local arithmetic restrictions, not global closure. See [the studio configuration guide](docs/CHATGPT_AGENT_STUDIO_RH_SETUP_2026_10_12.md) for the one-time check required by saved Workspace Agent instructions: GitHub changes do not edit Studio settings.

## Contribution rules

Read [`AGENTS.md`](AGENTS.md), the current proof contract, and the
[formalization checklist](FORMALIZATION_CHECKLIST.md) before changing the proof.
Work through PRs, preserve counterexamples, keep every signed compensation term
until reassembly is complete, and verify CI on the exact final commit.

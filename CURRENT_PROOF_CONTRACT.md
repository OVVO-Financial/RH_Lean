# RH_Lean current proof contract

Status date: 2026-09-11

This file is the compact current research contract for agents working on the RH_Lean proof program. Compiled Lean source remains authoritative. When this file conflicts with compiled source, the compiled theorem wins and this file must be corrected.

## Governing rule

**Signed physical reassembly first. Energy second.**

Never square, norm, take absolute values of, or replace by coefficient `L2` mass a family of physical `q^2` daughters before all mathematically required signed compensation, mate transfer, earlier-owner transfer, and endpoint reassembly have been performed.

The recursive energy used by the induction must be the energy of the genuine lower-scale Mertens-visible packet. It is not the unsigned square mass of daughter coefficients.

## Current repository state

Main contains merged PR #657 at commit `6c0a1cca55b2450417863e640c0da33f0e949918`. That work constructs genuine coefficient-level `q^2` daughters from actual Mobius-prefix increments, proves parent/current-response/first-power-mate compensation on the physical four-cell, lifts the identity to complete least-owner packets, and proves exact unit descent for the complete `q=3` period.

PR #658, branch `agent/physical-exceptional-normalization-v3`, extends the same exact descent to the full-contact `q=5` and `q=7` periods and proves that contacts removed by least-owner restriction transfer only to earlier exceptional owners: a missing `q=5` contact is owner `3`; a missing `q=7` contact is owner `3` or `5`. This makes the exceptional overlap graph lower triangular in owner. The intended next step is signed transfer of those omitted contacts into the already-existing second-contact/earlier-owner reconstruction before any norm is taken.

No theorem in #657 or #658 supplies an RH-scale energy bound by itself.

## Hard no-go constraints

The following identifications are forbidden unless a new exact bridge theorem is proved.

1. **Finite mask is not a finite Mobius field.** The contact mask is periodic, but the physical Mobius observable is not. `selectedDegreeOneOffsetDaughterField` reconstructs a daughter value by pulling back to its physical source cell. A fixed vector on a `q^2`/CRT torus cannot be computed once and reused as the true Mobius field across all physical periods.

2. **Coefficient energy is not recursive Mertens energy.** A norm or sum of squares of physical daughter coefficients cannot be identified with `E(X/q^2)` when `E` is a signed cumulative endpoint energy such as `M(X/q^2)^2`. Zero Mertens endpoints can coexist with nonzero coefficient mass. No finite multiplicative normalization can repair that type mismatch at such points.

3. **A scalar prefix identity is not an unsummed field identity.** Do not lift a scalar frozen predecessor cube to a physical field without an exact coefficient dictionary.

4. **Ownerwise norm before mate transfer loses the mechanism.** Least-owner deletion is triangular across exceptional owners. Omitted higher-owner contacts must be matched to their signed earlier-owner/second-contact occurrences before energy is formed.

5. **The `q^{-2}` budget is only a branching budget.** Bounds such as the strict-old-owner tail `4 * sum_{q>r} 1/q^2 < 1` become useful only after a legitimate lower-scale signed energy has been identified. They do not convert coefficient square mass into Mertens endpoint energy.

## Existing compiled safeguards

Read these before proposing a new normalization or frame argument.

- `RHLean/Analysis/PhysicalSquareCRTPeriodNoGo.lean`
  - exact affine daughter/source-cell pullback;
  - selected field transported from the physical source cell;
  - complete-period finite obstruction to literal rough-Go identification;
  - exact survival of the prime-11 first-moment factor despite that obstruction.

- `RHLean/Analysis/PhysicalDaughterEnergyObstructions.lean`
  - positive linear drift of the raw selected `{11}` least-owner-`3` deletion prefix;
  - impossibility of an `ElevenQ2EnergyStep` envelope dominating those raw prefixes;
  - finite nonidentification certificates for the Go root-floor column and a single square-block endpoint.

- `RHLean/Proof/ExceptionalSignedPacketIdentification.lean`
  - finite mismatch certificates showing that uncompensated local physical blocks are not scalar Mertens daughters.

- `RHLean/Proof/JointDaughterCrossEnergyAudit.lean`
  - a subunit joint frame requires genuine cross-owner energy, not merely within-owner `F/T` bookkeeping;
  - the universal factor-three synthesis already fits the restricted `3,5,7` `q^{-2}` budget if the physical daughter energy dictionary is valid;
  - coefficient-level parent/response/mate `q^2` compensation and the unit `q=3` descent.

## The next RH-critical theorem

The next theorem should be an exact signed reassembly theorem, or a quantitatively equivalent statement, of the following form.

Starting from the complete physical parent packet, perform current-owner response subtraction, first-power mate subtraction, and all earlier-owner/second-contact transfers. Reassemble the resulting `q^2` children **with signs intact**. Then prove that the reassembled child packet is the genuine lower-scale Mertens-visible packet, up to an endpoint carrier whose square is already bounded by `O(X)` (or by an equivalent admissible linear error).

Schematic target:

```text
signedReassembledChildren(X)
  = lowerScaleMertensVisiblePacket(X/q^2) + endpointError(X)
```

or directly

```text
|signedReassembledChildren(X)|^2
  <= C * E(X/q^2) + B * X
```

with every term on the left already compensated and physically reassembled.

Only after this theorem is available may the existing factor-three synthesis, prime-11 contraction, exceptional-owner budget, or `q^{-2}` induction be applied.

## Desired compile-time no-go certificates

To prevent future agents from rediscovering the false normalization, preserve or add executable theorems certifying all three of the following:

1. the correct `q=3,5,7` contact residue sets induced by `q^2 | 4k+a` for `a in {1,2,3,5,6,7}`;
2. the unrestricted fibre-summing mask has maximum fibre size two, hence squared `l2` operator norm exactly `2` (least-owner restriction gives at most `2`);
3. an explicit cutoff where the relevant signed Mertens daughter is zero but the corresponding physical coefficient square mass is positive.

The third certificate is especially important because it permanently separates coefficient energy from recursive Mertens energy.

## What counts as progress

A result counts as structural progress only if it supplies a new exact identification, mate transfer, signed reindexing, or cancellation on the physical carrier and strictly narrows the remaining seam.

A result counts as quantitative progress only if it bounds the correctly reassembled signed object and composes with an existing recursive energy theorem.

A coordinate rewrite, support estimate, frame constant, torus spectral computation, or coefficient `L2` bound is not closure unless an exact theorem first connects it to the recursive signed Mertens-visible energy.

## Preservation rules

- Keep all obstruction/counterexample modules even after a route changes; they are regression tests for mathematical architecture.
- Preserve the proof inventory, exact elaborated declaration graph, root import audit, owned-warning gate, and terminal axiom audit.
- Do not use `sorry`, `admit`, project-local axioms, probabilistic independence assumptions, or renamed Mertens/RH-strength hypotheses.
- Record finite counterexamples as executable Lean theorems whenever practical.
- Keep current frontier documentation short and canonical here; move historical route detail to `CURRENT_RESEARCH_HANDOFF.md` or `research/` notes rather than deleting it.
- Before opening a new route, search the declaration graph and the no-go modules for an existing theorem on the same carrier.

## Success condition

The repository should remain useful even if the present proof route fails. Its durable value is an audited library of exact Euler/Mobius identities, finite impossibility certificates, coordinate bridges, and machine-checked reductions that sharply distinguish genuine RH-strength seams from bookkeeping artifacts.

The proof program succeeds only when the final quantitative theorem closes on the exact signed recursive carrier and feeds the compiled terminal RH bridge without adding an assumption of equivalent strength.

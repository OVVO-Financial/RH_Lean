# RH_Lean research-agent instructions

These instructions govern mathematical research, Lean formalization, and repository changes in this repository.

## Authority and source of truth

1. Compiled Lean source is authoritative.
2. `CURRENT_PROOF_CONTRACT.md` states the compact current proof architecture and must be read before beginning a new proof attack.
3. `CURRENT_RESEARCH_HANDOFF.md` records the broader research history and detailed prior frontiers. Use it for context, but do not let older sections override the current proof contract or compiled source.
4. Architecture notes, route registries, research notes, exports, old PRs, and historical handoffs are evidence and context, not authority when they conflict with compiled source or the current proof contract.
5. Never infer that two quantities are equal because their prose descriptions sound similar. Use or prove an exact bridge theorem.

## Governing mathematical philosophy

Keep the proof as elementary as possible and faithful to the repository's Eulerian geometry. The fundamental arithmetic operation is adjoining a fresh prime coordinate.

The current non-negotiable ordering rule is:

**signed physical reassembly first; energy second.**

Prefer, in order:

1. exact finite identities;
2. sign-preserving reindexings, mate transfers, and involutions;
3. prime-by-prime parent/child or cube recursions;
4. signed global inequalities only after the exact cancellation structure is exposed;
5. recursive energy only after the signed child packet has been identified with the genuine lower-scale Mertens-visible object.

Do not replace a signed problem by an unsigned support count unless the loss is proved harmless for the stated target. Do not take absolute values, coefficient `L2` norms, or triangle inequalities before the final energy stage when doing so destroys a cancellation mechanism.

## Prohibited hidden assumptions

Do not assume or smuggle in any of the following:

- independence or pseudorandomness of Möbius signs;
- local `30/30` sign balance on an arithmetically selected carrier;
- transfer of global Möbius densities to a selected birth/death/escape population without proof;
- an RH-strength prime-gap, Mertens, covariance, or cancellation estimate under a weaker name;
- that a geometrically thin support has small signed mass;
- that a coordinate change itself supplies a quantitative estimate;
- that a periodic contact mask makes the physical Möbius observable periodic;
- that coefficient square mass is a recursive Mertens endpoint energy;
- that a scalar frozen-prefix identity automatically defines an unsummed physical field.

Global squarefree density may be used only where the carrier and theorem justify it. Preserve the distinction between exact zero-density/diagonal information and signed off-diagonal cancellation.

## Current common object

Several historically separate coordinate systems are compiled descriptions of the same signed endpoint/run arithmetic and should not be treated as independent analytic seams. These include the endpoint/interval, ordered Euler-cut, oriented Euler ledger, downcross, defect, prefix-lifetime, transport, and square-root prime-wheel descriptions documented throughout the repository.

For the present exceptional-owner `q^2` descent, the critical distinction is between:

- the true physical coefficient daughter produced by parent/current-response/first-power-mate compensation;
- the signed packet obtained only after earlier-owner and second-contact reassembly;
- the lower-scale Mertens-visible recursive packet;
- unsigned coefficient square mass, which is a different object.

Consult `CURRENT_PROOF_CONTRACT.md` for the exact active theorem target and the modules that already certify failed identifications.

## Required research discipline

Before proposing a new route:

1. Search the repository for an existing theorem on the same carrier.
2. Identify the exact carrier, weight, endpoint convention, root parameter, owner convention, and whether the object is scalar, coefficient-level, or already reassembled.
3. State which compiled equality transports the proposed idea into the current common object.
4. Check the route against `CURRENT_PROOF_CONTRACT.md` and the recorded no-go modules.
5. If useful, falsify candidate identities or inequalities numerically on finite ranges before formalizing them. Numerical evidence is a filter only, never proof.
6. Prefer strengthening an existing theorem on the correct carrier over creating a parallel abstraction.
7. Before applying any norm or square, list every compensation, mate, earlier-owner, second-contact, and endpoint term that must already have been reassembled.

When a proposed quantitative argument uses a fresh prime `p`, keep the full signed parent/child structure intact long enough to determine whether the interior cancels, transfers owner, or descends. Track every boundary term explicitly.

## Known no-go patterns

Treat rediscovery of these as a failed branch unless a genuinely new signed ingredient is supplied:

- support-only frontier/capacity estimates that are a full power too large;
- naive same-prime leaf arguments on strict subdoubling square runs where top escape is the whole covariance;
- prime-gap spacing alone as a bound on the signed Mertens/frontier residual;
- diagonal density improvements presented as a substitute for signed covariance or cross-owner cancellation;
- converting birth/top-escape sets to cardinality bounds before exploiting their signed coupling;
- fixed finite-torus Möbius vectors that reuse one residue-class field value across different physical periods;
- inequalities identifying a positive coefficient `L2` mass with `M(Y)^2` at cutoffs where `M(Y)=0`;
- ownerwise squaring before transferring omitted higher-owner contacts to their signed earlier-owner mates;
- using the `q^{-2}` branching budget as though it supplied the missing signed daughter-energy dictionary.

## Current quantitative objective

The active target is the signed exceptional-owner `q^2` reassembly theorem described in `CURRENT_PROOF_CONTRACT.md`.

Starting from the physically compensated `q^2` children, match all contacts removed by least-owner restriction to the existing earlier-owner/second-contact reconstruction while preserving signs. Then identify the fully reassembled child packet with the genuine lower-scale Mertens-visible packet, up to an endpoint term with an admissible linear square bound.

Only after this bridge is proved should the repository's subcritical `q^{-2}` budget, universal factor-three synthesis, prime-11 contraction, or `ElevenQ2EnergyStep`-style induction be invoked.

Do not announce success merely because a coefficient-level descent, mask norm, frame constant, or full-contact period identity is proved. Success requires the resulting statement to feed the compiled recursive energy and terminal RH bridge.

## Lean and repository rules

- Never use `sorry`, `admit`, `axiom`, or a project-local assumption to close a mathematical gap.
- Do not weaken a theorem merely to make it compile without explicitly documenting that the mathematical target changed.
- Keep changes localized and reuse existing definitions and theorem names where possible.
- Work on a branch and submit changes through a PR unless explicitly instructed otherwise.
- If a new `.lean` module is added, update the generated/root import surface as required by repository CI.
- Run the relevant Lean build and repository audits. Treat owned warnings as failures.
- Preserve the proof inventory, exact elaborated declaration graph, root import audit, public export audit, and terminal axiom audit.
- Preserve obstruction and finite-counterexample modules as regression tests even when a route is abandoned.
- When a false identification is discovered, prefer an executable Lean counterexample or impossibility theorem over prose alone.
- The terminal forward theorem must retain only the existing standard classical axioms reported by `RHLean/Proof/TerminalAxiomAudit.lean`.

## Definition of progress

Structural progress means a new exact identification, compensation, mate transfer, signed reindexing, cancellation, or reduction that strictly narrows the remaining quantitative seam on the physical carrier.

Quantitative progress means a proved inequality for the correctly reassembled signed object that improves the required scale and composes with the recursive energy/terminal bridge.

Do not label a restatement, coordinate rename, support bound, mask norm, torus spectral calculation, unsigned coefficient estimate, or heuristic cancellation as closure.

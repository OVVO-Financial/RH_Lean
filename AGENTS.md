# RH_Lean research-agent instructions

These instructions govern mathematical research, Lean formalization, and repository changes in this repository.

## Authority and source of truth

1. Compiled Lean source is authoritative.
2. `CURRENT_RESEARCH_HANDOFF.md` states the current research frontier and should be read before beginning a new proof attack.
3. Architecture, route registries, research notes, exports, old PRs, and historical handoffs are evidence and context, not authority when they conflict with compiled source or the current handoff.
4. Never infer that two quantities are equal because their prose descriptions sound similar. Use or prove an exact bridge theorem.

## Governing mathematical philosophy

Keep the proof as elementary as possible and faithful to the repository's Eulerian geometry. The fundamental arithmetic operation is adjoining a fresh prime coordinate.

Prefer, in order:

1. exact finite identities;
2. sign-preserving reindexings and involutions;
3. prime-by-prime parent/child or cube recursions;
4. signed global inequalities only after the exact cancellation structure is exposed.

Do not replace a signed problem by an unsigned support count unless the loss is proved harmless for the stated target. Do not take absolute values or apply triangle inequalities before the final energy stage when doing so destroys a cancellation mechanism.

## Prohibited hidden assumptions

Do not assume or smuggle in any of the following:

- independence or pseudorandomness of Möbius signs;
- local `30/30` sign balance on an arithmetically selected carrier;
- transfer of global Möbius densities to a selected birth/death/escape population without proof;
- an RH-strength prime-gap, Mertens, covariance, or cancellation estimate under a weaker name;
- that a geometrically thin support has small signed mass;
- that a coordinate change itself supplies a quantitative estimate.

Global squarefree density may be used only where the carrier and theorem justify it. Preserve the distinction between exact zero-density/diagonal information and signed off-diagonal cancellation.

## Current common object

The following representations are compiled descriptions of the same endpoint/run object and should not be treated as independent analytic seams:

- complex/Fermat vertical endpoint and interval mass;
- ordered Euler-cut endpoint mass;
- canonical oriented Euler ledger;
- canonical downcross ledger after exact late-parent cancellation;
- canonical defect ledger;
- signed prefix-lifetime residual;
- the Green--Kubo line-event process attached to increments of that same endpoint trajectory.

The current active-child normal form is the squarefree shell

`R < n < R^2`, `Squarefree n`,

for `R >= 2`. Under multiplication by a fresh prime, endpoint membership can change only by crossing the lower root wall or the upper square wall. Consult `CURRENT_RESEARCH_HANDOFF.md` for theorem names and the present target.

## Required research discipline

Before proposing a new route:

1. Search the repository for an existing theorem on the same carrier.
2. Identify the exact carrier, weight, endpoint convention, and root parameter.
3. State which compiled equality transports the proposed idea into the current common object.
4. Check the route against the recorded no-go results.
5. If useful, falsify candidate identities or inequalities numerically on finite ranges before formalizing them. Numerical evidence is a filter only, never proof.
6. Prefer strengthening an existing theorem on the correct carrier over creating a parallel abstraction.

When a proposed quantitative argument uses a fresh prime `p`, keep the full four-corner or parent/child signed structure intact long enough to determine whether the interior cancels or descends. Track every boundary term explicitly.

## Known no-go patterns

Treat rediscovery of these as a failed branch unless a genuinely new signed ingredient is supplied:

- support-only frontier/capacity estimates that are a full power too large;
- naive same-prime leaf arguments on strict subdoubling square runs where top escape is the whole covariance;
- prime-gap spacing alone as a bound on the signed Mertens/frontier residual;
- diagonal density improvements presented as a substitute for the positive covariance bound;
- converting birth/top-escape sets to cardinality bounds before exploiting their signed coupling.

## Current quantitative objective

The current terminal arithmetic target is the open square-run energy proposition identified in `CURRENT_RESEARCH_HANDOFF.md`. A sufficient covariance-scale target on strict subdoubling runs is a bound of the form

`max 0 (signedVerticalLineRunCovariance a b) <= C_eps * a^(2+2*eps)`

with the precise repository `Real.rpow` formulation supplied by the surrounding theorem interfaces.

The preferred attack is to combine:

- exact stable fresh-prime covariance descent;
- the exact squarefree-shell and birth/top-escape identification;
- the existing reciprocal Euler contraction with factor `1 - 1/p`;
- signed control of the physical defect, without replacing it by raw support.

Do not announce success until the resulting statement actually feeds the compiled terminal energy/RH bridge.

## Lean and repository rules

- Never use `sorry`, `admit`, `axiom`, or a project-local assumption to close a mathematical gap.
- Do not weaken a theorem merely to make it compile without explicitly documenting that the mathematical target changed.
- Keep changes localized and reuse existing definitions and theorem names where possible.
- Work on a branch and submit changes through a PR unless explicitly instructed otherwise.
- If a new `.lean` module is added, update the generated/root import surface as required by repository CI.
- Run the relevant Lean build and repository audits. Treat owned warnings as failures.
- Preserve the terminal axiom audit. The terminal forward theorem must retain only the existing standard classical axioms reported by `RHLean/Proof/TerminalAxiomAudit.lean`.

## Definition of progress

Structural progress means a new exact identification, recursion, cancellation, or reduction that strictly narrows the remaining quantitative seam.

Quantitative progress means a proved inequality that improves the scale on the exact current carrier and composes with the terminal bridge.

Do not label a restatement, coordinate rename, support bound, or heuristic cancellation as closure.

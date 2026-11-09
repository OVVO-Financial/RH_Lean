# FINITE-WHEEL-CENTERED-RH V1 — seven-agent attack (2026-11-08 ET)

**User-ordered live research priority on review/merge.** All seven RH_Lean agents focus their *next actual research invocation* on the complete signed square-root fractional boundary. This directive supersedes older HIGH, frozen-root/prime-two, general multi-route, and NEXT-* priorities **for task selection only**. Retain previous exact identities, permitted source hypotheses, counterexamples, independent mathematical methods, permissions, schedule and report protocol. The user directs concentration on this one proof, not seven identical calculations.

## Certified starting source (not the missing estimate)

Source: `research/CompleteSquareRootWheelFractionalBoundary.lean`, PR [#1122](https://github.com/OVVO-Financial/RH_Lean/pull/1122), merged with warning-fatal targeted Lean 4.34.1 CI and standard terminal axioms.

For every integer `R >= 2` define `X=R^2-1`, `y=R-1`, `P_y=prod_{p<=y} p` and
```text
F_R = sum_{d|P_y} mu(d) * fract(X/d)
D_R = X * prod_{p<=y} (1-1/p) + pi(y) - 1 - li(X)
F_R - D_R = li(X) - pi(X)
```
All prime factors in `P_y` are <=R-1. **All** squarefree divisors `d|P_y` enter the complete wheel, including `d>X`; the latter are virtual and `fract(X/d)=X/d`. They cancel *termwise* against the finite Euler-product reciprocal mass **before any unsigned bound or truncation**. The exact physical compensated form is
```text
F_R - X*prod_{p<=y}(1-1/p)
  = sum_{d|P_y, d<=X} mu(d)*(fract(X/d) - X/d)
  = -sum_{d|P_y, d<=X} mu(d)*floor(X/d).
```
Do not confuse `F_R` alone with the compensated source, drop virtual terms before compensation, or invert the sign. The formal interface `finiteWheel_squareFractional_centered_eq_reference_sub_pi R hR L` holds for arbitrary real `L`, hence for the chosen logarithmic integral. `finiteWheelFract_sub_density_eq_physical_floorError`, `finiteWheelFract_eq_physical_add_virtual`, `finiteWheel_divisorReciprocal_eq_eulerProduct` and `finiteWheel_squareLegendre_identity` are already certified. Do not rerun their elementary proofs as new progress.

**Single mathematical target**, with *one constant uniform over R*:
```text
exists C : Real, 0 <= C and
  forall R >= 2, abs(F_R - D_R) <= C * R * log R.
```
The bound is equivalent to the classical von Koch/RH assertion, and **IS OPEN**. No agent may assume it or derive it circularly from a prime-counting estimate of the same RH strength, from an unproved all-interval equidistribution law, or from a stronger disguised Gram bound. No proof of RH is claimed here. Existing 7/8 Mertens control, owner, CORR4 and cosine-Gram results can be inputs **only after an explicit quantitative, source-faithful transfer**, not by name or resemblance. Retain the full Li normalization, square endpoint and all constants.

## Seven distinct assigned proof jobs — same final target, independent methods

1. **Research Coordinator / Proof Architect.** Build one typed dependency DAG from certified Legendre/fractional compensation to the proposed O(R log R) supplier. For each submitted route give exact old theorem and new inequality, the first unsupported implication, exponent/constant budget, and a concrete finite falsifier. Match a new claim to existing native/equivalence consumers without recycling tautologies. Synthesize distinct investigations, not seven duplicates. Report a ranked *best mathematical move* and explicit blocked edges.

2. **Owner Payment / Physical Packet.** Starting from the complete divisor sum, derive signed first-owner or least-prime packet decompositions preserving all physical and virtual incidence. Find a nontrivial packet-to-packet compensation theorem with explicit coefficients and uniform endpoint conditions, then show precisely how it could pay part of D_R. Never replace an actual Möbius packet by an unsigned row count.

3. **Adversarial Referee.** Attack proposed savings: test R=2 and small roots, prime-root admission at R prime, d=X, d>X, empty wheels, missing virtual Euler terms, Li versus Li_2 normalization, and the unbounded wheel size 2^pi(R-1). Reject any inequality that only restates pi-li or assumes an RH-strength premise. Demand proof of *uniformity in R* and no hidden post-root independent prime signs. Return an explicit smallest counterexample or a quantified acceptance statement.

4. **Prime Census Laboratory.** Pre-register and run exact integer/rational finite checks at feasible R, with physical and virtual ledgers separated but reunited before comparison. For larger R, do not enumerate an exponentially large complete cube: use the *proven compensated physical form* to compute equivalent exact integer totals and report the symbolic virtual correction separately. Test signed packets, moving root cutoff and historical Mertens/correlation constraints, track normalized |F-D|/(R log R), and mark observations NUMERICAL ONLY.

5. **Analytic Type II.** Work directly on the deterministic signed fractional/Legendre source; seek a genuine bilinear, reciprocal-phase, partial-summation or spectral estimate surviving recombination with D_R. Reuse certified signed moments, the imported 7/8 bound or logarithmic weights only with a proved link and explicit power costs. Exhibit the exact inequality stronger than known bounds and test that its consumer yields O(R log R) without requiring the conclusion.

6. **Finite Wheel & Incidence.** Derive exact prime-adjunction recurrences for `F`, full Euler density and the *centered* remainder, including the changes in physical/virtual status as R increases. Investigate sign-alternating subset incidence, shared-prime overlaps, parity, and 2/6/30/210 fixed wheels as prototypes, then explicitly bound the cumulative innovation. Do not assume each added prime improves cancellation or that finite wheel behavior implies a uniform global saving.

7. **Lean Verification.** Use GitHub Actions Lean 4.34.1 (never local Lean) to formalize only mathematically independent, quantitatively useful new lemmas on the exact complete-wheel source, plus counterexamples/obstruction certificates. Check all public theorem types, terminal axioms `[propext, Classical.choice, Quot.sound]`, exact-head warning-fatal CI and required checks. Keep existing #1122 statements and finite #1120 cosine algebra unchanged unless a formally justified bridge is provided. An equality to pi is *not* a new discrepancy bound.

## Shared execution contract and reporting

- At each actually configured invocation, fetch latest `main` SHA and this file. Include `finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1`, source commit, exact theorem(s), the source-to-target missing inequality, and verified CI or numerical evidence.
- Publish timestamped, append-only own stage to `agent-reports/research/agent_reports/YYYY-MM-DD/` under the existing role permissions. The Coordinator's two mirror files remain byte-identical. Do not create extra Studio runs, schedules or compute entitlements by editing documentation.
- Required deliverable per agent: either (i) a strictly new signed arithmetic inequality with explicit quantifiers, constants and a complete return through all terms; (ii) a proved impossibility/counterexample for a specific proposed strengthening; or (iii) a precise smaller open lemma whose proof would quantitatively move the centered remainder. No generic restatements, positivity assumptions, heuristic independence or unlicensed power gains.
- Six non-Lean specialists remain own-report-only. Lean Verification has its existing delegated task-related GitHub rights through feature branches and reviewable PRs. Repo edits do **not** modify live saved Agent Studio prompts; deploy them separately if the runtime does not read these files. Existing schedules and permissions remain unchanged. Human-only merge for autonomous agent work is still the default; this interactive user-authorized maintenance is separate.

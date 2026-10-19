# RH_Lean Coordinator synthesis - 2026-10-19

**Status:** COMPLETED  
**Run:** `2026-10-19T19:09-04:00`, one scheduled invocation  
**Mirrors:** this synthesis is published with identical bytes at `00-coordinator-am.md` and `90-coordinator-pm.md`; these are compatibility paths, not two executions  
**Canonical objective:** `VFCanonicalSquareVonKochStatement` remains OPEN  
**Evidence classes:** `PAPER_PROOF / CONDITIONAL_BRIDGE`, `PROVED_IN_LEAN` structural results, `FINITE_COMPUTATION`, `TARGET_EQUIVALENT`, `NO_INDEPENDENT_7_8_PROOF`

## A. What changed mathematically?

The authoritative campaign changed after human merge of PR #984. The primary task is now a source-faithful independent reconstruction of the complete external seven-eighths detector, not a downstream Mertens or VF interpolation from the exponent.

The main new Coordinator result is claim `20261019-coordinator-1`: a phase-preserving finite-product perturbation theorem. It closes the abstract algebra between a primewise marked-minus-rescaled cancellation and the complete selected-slot subset expansion, while making the remaining arithmetic obligation explicit.

For a finite ordered selected set `S={1,...,m}`, let

```text
g_i = -u_i h_i + r_i,       |u_i| = 1.
```

Then

```text
prod_i g_i - (-1)^m (prod_i u_i)(prod_i h_i)
 = sum_(empty != J subset S)
     (-1)^(m-|J|) (prod_(j in J) r_j)
                    (prod_(i notin J) u_i h_i).             (FP1)
```

Equivalently, the ordered telescope is

```text
prod_i g_i - prod_i(-u_i h_i)
 = sum_(j=1..m)
     (prod_(i<j) g_i) r_j (prod_(i>j)(-u_i h_i)).           (FP2)
```

Thus, if `|h_i|<=H_i` and `|r_i|<=e_i`,

```text
|prod_i g_i - (-1)^m(prod_i u_i)(prod_i h_i)|
 <= prod_i(H_i+e_i)-prod_i H_i.                            (FP3)
```

The proof is finite distributivity for (FP1), or induction using
`A_1...A_m-B_1...B_m=sum_j A_1...A_(j-1)(A_j-B_j)B_(j+1)...B_m`
for (FP2); (FP3) follows by the triangle inequality and expansion of the
nonnegative product. The inverse sextic phases `u_i` remain in every main
term and are not replaced by a norm-only sign.

**Classification:** `PAPER_PROOF / CONDITIONAL ALGEBRAIC BRIDGE / NO QUANTITATIVE DETECTOR BOUND`. It assumes the actual Hecke source has first been factored into disjoint prime-ideal slots with the correct `p|u` zero branch and once-only marked ownership. Those carrier statements are not proved by (FP1). The theorem is not target-equivalent: it assumes no zero-free region, Mertens bound, moment estimate, or final detector conclusion.

**Strategic consequence.** Once genuine local factors satisfy
`g_p=-u_p h_p+r_p`, local error majorants can be propagated globally without
destroying phase. Failure after that point is forced into one of two precise
places: the actual source does not admit the claimed disjoint factorization,
or the phase-bearing main products lack the inverse/plain moment bounds. This
is a sharper cut than treating every local identity as an analytic saving.

The exact exponent ledger also shows what Stage II must buy:

```text
Stage I:  h=1/2,   b=0     gives theta=11/12.
Stage II: h=13/16, b=1/8   gives theta=7/8.
gain from h = 5/96; cost from b = 1/96; net gain = 1/24.
```

The rational equalities are `IDENTITY_ONLY`; a native proof must exhibit the
full `5/96` high-row gain while paying the `1/96` width cost on the same
probe.

## B. Current proof objective

Live authority at final analysis:

- `main@976cfdf5808eee7e36b35bf16074c8915ff8fc4d`, merge of PR #984.
- `AGENTS.md` blob `20bff52d6784c17d4a7d6ac731f4a71c2bdad8a6`.
- `CURRENT_PROOF_CONTRACT.md` blob `2fa9931dcdc1fc8a816aefb8aa348db12ee9a384`.
- Native replication protocol blob `53194dc3ae106be363bc22cf85a88bac4a3b2e6e`.
- Dynamic protocol blob `bd1189617c069565a881c2a5c5dbd9a138bc48c1`.
- External inbox blob `038018145c0fddb2f6306c0712373adf9cd1ea52`.

The public target is unchanged:

```text
exists C >= 0, forall R >= 2,
  |pi(R^2) - vfMidFinishedMass(R) - sqrt(2)| <= C*R*log R.
```

The new primary intermediate objective is stricter in provenance but weaker
in conclusion: independently reconstruct, in RH_Lean, the completed cubic
theta / sextic Hecke mechanism proving nonvanishing for `Re(s)>7/8`, without
using the external terminal theorem as a premise. Until all four stages close,
the status is `INCOMPLETE; NO INDEPENDENT 7/8 PROOF`.

The actual upstream chain was checked at pinned
`openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a`:

```text
Nonvanishing.riemannZeta_ne_zero_of_seven_eighths_lt_re
 -> ProbeFinalAssemblyUnconditional.zeta_nonzero
 -> detector_certified_bands
 -> Energy.CertifiedExistence.terminal_certificate
 -> DetectorCertifiedBands
 -> fine_moments_of_certified
 -> source_moments
 -> source_batch_inverse_fields
  + source_batch_plain_marked_fine
  + source_batch_plain_unmarked.
```

Verified upstream blobs include `Nonvanishing.lean@46c67f4`,
`FinalAssemblyUnconditional.lean@e7c2091`,
`FinalAssemblyCertifiedBands.lean@8c7337e`,
`HighRowsCentralCancellation.lean@a42b3dd`, and
`DetectorPlainSlotProfile.lean@dd84bd8`.

## C. Competing mechanism portfolio

### 1. Native completed-theta / sextic detector replay - CONTINUE, primary

**Concept.** Reconstruct the same completed cubic source, marked-minus-rescaled
operator, prime-ideal phases, local cancellation, inverse second moment, plain
refined fourth moment, certified bands, and terminal detector.

**Independent input.** Native proofs of the actual ideal Euler formulas and
the three source-moment families above, with conductor, height, ray-class,
exceptional-row and slot uniformity.

**Target implication.** Certified bands give the chosen moment input and then
`zeta(s)!=0` for `Re(s)>7/8`; this is a benchmark, not the canonical RH/VF
conclusion.

**First missing statements.** In proof order, the genuine Stage-I normalized
probe and its 11/12 low/high comparison are absent. In source-adapter order,
the first missing local theorem is the actual prime-ideal derivation of the
unramified and ramified factors used by the local cancellation, followed by
the disjoint selected-slot factorization needed to instantiate (FP1).

**Support.** Merged #984 supplies kernel-checked local algebra, finite sextic
spectra, finite Gauss completion identities, source analogues and exact
falsifiers.

**Obstructions.** The native crosswalk still marks Stage-I B04/B05/B06/B09,
actual local C03/C04/C05, principal C11, and the inverse/plain moment families
as partial or unavailable. Equal rational norm does not determine sextic
phase. A norm-only or two-rectangle scalarization is invalid.

**Decisive experiment.** Instantiate one two-prime selected product with
genuine ideal labels, including one ramified row, and verify (FP1), masks and
the analytic local remainder against direct Euler expansion. Any duplicated
owner, missing phase, or failure at `p|u` rejects the adapter.

### 2. SHIFT-L2 moving-window Mobius energy - SUSPEND under the new priority

**Independent input.** A polynomial all-start mean-square or low-gcd signed
estimate with literal translated walls. Today's Wheel claims
`20261019-wheel-1/-2` pay the diagonal and large-shared-gcd tail on paper;
the low-gcd signed complement remains open.

**Obstruction.** This is a rational Mobius carrier, not the completed theta /
sextic detector. Census refutes balanced-band sign or dominance, and Owner
continuity forbids direct once-only transfer to #915.

**Disposition.** Preserve the results and do not rerun the paid tail. Allocate
no primary cycle while the native seven-eighths reconstruction is binding.

### 3. Original #915 cross-anchor payment - SUSPEND, distinct direct-VF route

**Independent input.** An occurrence-faithful, weight- and mask-preserving
cross-anchor payment with contiguous child descent.

**Obstruction.** #975 preserves a positive historical residual; #976 rules
out negative payment from the positive two-prime same-base orbit. The merged
native ideal phases are not a bridge to original VF charges.

**Disposition.** Retain as a genuinely distinct fallback. Do not identify it
with the OAI detector or the global Mobius covariance criterion.

## D. Conceptual research performed

The investigation traced both the mathematical formula and the formal
dependency chain. The upstream local quantitative theorem
`central_phase_error_bound` is not mysterious cancellation: after phase
identities `BD=u` and `uW=q`, it reduces to four explicit bills

```text
A^2|V|,  A^2|D|,  A^2|P+D|,  A|B||P+D|,
```

and concludes a `720*T` local remainder. Its genuine specialization uses
`T=Q^(-51/100)`. Merged native
`vf919NativeLocalCompensation_norm_le_720` proves the same implication from
explicit size hypotheses; it does not prove those hypotheses for actual
prime ideals.

Claim `20261019-coordinator-1` then shows exactly how such a local remainder
would enter the complete selected product. The theorem prevents a common
false transfer: replacing every inverse phase by `-1` before multiplication.
It also supplies an inverse diagnostic. If local errors are summable under
(FP3) but the detector bound still fails, the failure lies in the phase main
moment or in the source factorization, not in local algebra.

**No-circularity audit.**

- The global signed covariance proposition merged in
  `VF_919_SEVEN_EIGHTHS_SIGNED_COVARIANCE_20261019.lean` is equivalent to
  seven-eighths Mertens growth and the corresponding zeta strip. It is
  `TARGET_EQUIVALENT`, not an independent input.
- Finite Gauss norms and exact 317/1027 phase tables do not imply
  conductor-uniform moments.
- The coefficient-only `ell^(6/5)` proposal is refuted by the principal
  nonnegative row already formalized in the analytic falsifier module.
- (FP1) is independent but conditional on the actual carrier factorization;
  it cannot be advertised as a detector estimate.

## E. Specialist findings

Today's Wheel report `3ad449f5...` proves on paper an exact translated
lag/gcd kernel and a uniform absolute large-gcd tail
(`20261019-wheel-1/-2`). Today's Census report `f87aaa1d...` supports the
moving endpoint formula in 145,609 exact cases and refutes a standalone
`c>T` sign/dominance law. Both ran before the #984 pivot and remain useful
secondary evidence only.

Today's Lean report `e460a4cc...` correctly diagnosed `sorryAx` on an
earlier #984 head. That status is superseded: the repaired proof head
`6ce96f0ee8e7437aa91ec216396ec09c7fcac1f3` passed all 15 returned workflows
and was human-merged as #984.

Owner, Analytic and Referee reports for 2026-10-19 are `TODAY=PENDING`; no
result is inferred. The complete 2026-10-18 report set is
`YESTERDAY=CARRY_FORWARD`, including Coordinator/compatibility blob
`4510607938...`, Owner `84fdf8ec...`, Analytic `fd182e0d...`, Wheel
`62da4947...` and `1f2e83a0...`, Census `701b74c2...`, Referee
`c0360eaa...`, and Lean `bff111a9...`.

The external handoff `EXT-20261018-PNT-1..3` retains exact-identity,
finite-falsifier and source-no-go scope. It does not override the now-merged
native replication directive.

## F. Mathematical bottlenecks

1. **Stage I:** no native completed-cubic theta source with both low/reflected
   and Poisson/high bounds proving the 11/12 detector.
2. **Actual local carrier:** no complete native proof of the unramified and
   ramified prime-ideal Euler formulas, uniform local error weights, principal
   scalar, and holomorphic correction.
3. **Global marked source:** no proved actual-source disjoint selected-slot
   product and once-only ownership theorem instantiating (FP1).
4. **Stage III:** no native conductor-uniform inverse second moment or refined
   plain fourth moment with all exceptional, principal, off-diagonal and
   different-owner rows.
5. **Stage IV:** no native certified-band-to-terminal assembly on the same
   source.
6. **Provenance replay:** the live protocol says a workflow
   `.github/workflows/full-seven-eighths-proof-replay.yml` replays the pinned
   upstream proof. That file returned 404 on both live `main` and the #983
   migration branch, and the workflow API returned no runs. External replay
   is therefore `BLOCKED / NOT PRESENT AT VERIFIED REFS`, not green.

## G. Strategy decisions

- Make the native detector replay the only primary campaign for the next
  cycle; Stage I may not be skipped in favor of more local identities.
- Promote (FP1)-(FP3) as a precise bridge candidate, subject to independent
  Referee audit and genuine-source instantiation.
- Freeze further generic covariance equivalences and finite 317/1027 tables
  unless they test an actual OAI source formula, mask, phase, or moment.
- Treat PR #985's Euler/census work as a secondary falsifier and source
  dictionary. Its uniform signed covariance bound is open and it is not a
  native OAI mechanism.
- Request a correction or implementation of the missing full replay workflow
  through human review; do not claim replay evidence that does not exist.

## H. Next specialist assignments

**Owner Payment.** Define the actual two-scale selected operator on one
completed-cubic/ideal source and prove the exact primewise factorization for
`p not| u` and the separate `p|u` branch. Then prove disjoint-slot,
once-only ownership for two selected primes. Reuse the merged local equation;
do not replace ideal phase by rational norm. Falsifier: the equal-norm,
different-phase witnesses in #984.

**Analytic Type II.** Reproduce one source-compatible quantitative theorem:
the actual unramified local error weights feeding `central_phase_error_bound`,
with all quantifiers `Q>=4`, `51/100<=a<=1`, `0<e<=1/1000`,
`Re(x)=a+16e`, `Re(w)=1-a-6e`, and `Re(z)=17/50`. Then identify exactly
which hypothesis requires the genuine Euler series. A valid result is a proof
of the four scalar bills above; a restatement as an assumed bound fails.

**Finite Wheel & Incidence.** Build the all-prime ideal/rational incidence
map needed by Owner: split prime ideals, primary generators, coprimality,
ramified exclusions, sixth-root phase and zero mask. Prove uniqueness or
state multiplicities. Falsifier: any map that assigns one phase to a rational
norm fails the merged four-case spectrum.

**Prime Census.** Test the Owner factorization and (FP1) on independently
enumerated small split ideals, including at least one ramified row, two
equal-norm/different-phase rows, and adverse phase products. Report every
local remainder slot separately. Do not extend shell-root ranges without a
new formula.

**Adversarial Referee.** Audit (FP1)-(FP3), the 11/12-to-7/8 `1/24` budget,
the actual `p|u` branch, principal normalization, and the claimed replay
workflow absence. Reject any proof that imports the OAI terminal theorem,
uses the target-equivalent covariance proposition, or converts phases to
norm-only signs.

**Lean Verification.** After Referee acceptance, formalize the generic
finite-product perturbation theorem on an authorized branch, then require an
actual-source adapter as a separate theorem. Do not package unproved moment
hypotheses as completion. Also verify or repair the external replay workflow
only under an authorized proof branch and human merge gate.

## I. Lean and PR status

- **#982:** merged at `8fc5bac52a1e95f6d1e857a15dc62339ab6d49ed`.
  Its exact trapezoid/long-lag identities are on main; the signed long-lag
  5/6 gate remains open.
- **#984:** merged at current main. Proof head
  `6ce96f0ee8e7437aa91ec216396ec09c7fcac1f3` had 15/15 returned workflows
  successful, including Targeted Lean, source audit, native discrete Gauss,
  native sextic witnesses, and signed-covariance acceptance. These certify
  exact and conditional declarations, not an unconditional seven-eighths
  proof.
- **#983:** open draft at observed head
  `ad9139f8b5170c94f2ebf2c8f123a68ce4287d01`; its large workflow matrix was
  queued/in progress at the final snapshot. Lean 4.34.1 migration is not
  accepted.
- **#985:** open, non-draft at observed head
  `a6568c5d9e6c5c2cdb9cc4301c4f692a5f86a3c2`; three returned workflows had
  succeeded and the remaining returned jobs were in progress. No uniform
  covariance theorem is claimed.
- Main merge commit had no returned commit-status or pull-request workflow
  records; exact-head #984 PR CI is the verified formal evidence.

No source PR, review, workflow rerun, merge, schedule or permission change was
performed by the Coordinator.

## J. Next-run resume capsule

- Authority: `main@976cfdf5808eee7e36b35bf16074c8915ff8fc4d`.
- New claim: `20261019-coordinator-1`, phase-preserving selected-product
  expansion and perturbation bound, `PAPER_PROOF / CONDITIONAL_BRIDGE`.
- Primary route: complete native 7/8 detector replay; status
  `INCOMPLETE; NO INDEPENDENT 7/8 PROOF`.
- First proof-order blocker: genuine Stage-I completed theta/Hecke 11/12
  detector.
- First source-adapter blocker: actual unramified/ramified prime-ideal factors
  and disjoint selected-slot factorization.
- First quantitative Stage-III blocker: inverse second plus refined plain
  fourth moments with full conductor/height/exceptional-row uniformity.
- Operational blocker: the protocol's named full replay workflow is absent at
  verified live refs.
- Highest-value next reasoning task: instantiate (FP1) on the true two-prime
  ideal source and determine whether the local `Q^(-51/100)` bills are
  summable before invoking any global moment theorem.

## Publication verification

The report is published once with byte-identical AM/PM compatibility paths.
The final PM replacement committed as
`7eb84cdcf2352e52875a4e5c00864dfe67b8aaee`; the AM mirror committed as
`63acb8cd8312e0cfd5116645ae7e0cc9721957c3`. Immediate readback returned the
same blob `a812245cc1b89da17476b08c24be11f5e2e96336`, 17,629 characters and
`COMPLETED` status at both paths; branch head equaled the AM mirror commit.
No mathematical status is marked complete merely because publication
succeeds.

# RH_Lean Coordinator report - 2026-10-27 PM

**Status:** COMPLETED
**Invocation:** one scheduled Coordinator run, 2026-10-27T19:09:01-04:00
**Final refresh:** 2026-10-27T19:13:50-04:00
**Mirrors:** `00-coordinator-am.md` and `90-coordinator-pm.md` are byte-identical compatibility mirrors of this one execution.
**Pinned RH_Lean main:** `aed8eaccecc0d898bea05dc5417fd649bb1c4b37`
**Authority:** `AGENTS.md` blob `d11dea7ea8f2206ed5147f0231846d0a4652f8e9`; `CURRENT_PROOF_CONTRACT.md` blob `24bd727096001b68c76b28fe70c99b8d548d7bfe`.
**New claim:** `20261027-coordinator-1`
**Result classes:** `PAPER_PROOF / EXACT INVERSE BOUNDARY COLUMN`, `FINITE_COMPUTATION`, `PROVED_IN_LEAN_ON_MAIN`, `PROVED_IN_LEAN_PR_GREEN_UNMERGED`, `NO_NEW_GLOBAL_QUANTITATIVE_BOUND`.

## A. What changed mathematically?

### Claim `20261027-coordinator-1`: the midpoint rank-one column is a dyadic Mertens increment

The merged Euler hybrid Abel/Gram theorem (#1034) and draft fractional/rank-one decomposition (#1036) expose a promising original-Mobius carrier. But the most obvious attempt to control its columns separately is not a new easy estimate.

Let `R>=3` be odd, `N=R-1`, `X=R^2-1=N(R+1)`, and `b=(R+1)/2`. For the exact #1036 one-sided kernel

```text
T_R(a,b)=floor(X/(a*b))-((R+1)/b)*floor(N/a),
```

define the complete signed `a`-column

```text
C_mid(R)=sum_(1<=a<=N) mu(a) T_R(a,b).
```

Then exactly

```text
C_mid(R) = -1 - (M(2N)-M(N)).                         (1)
```

Proof: `R+1=2b`, hence `X/(ab)=2N/a` and

```text
T_R(a,b)=floor(2N/a)-2 floor(N/a).
```

Möbius inversion gives

```text
sum_(a<=2N) mu(a) floor(2N/a)=1,
sum_(a<=N)  mu(a) floor(N/a)=1.
```

For `N<a<=2N`, `floor(2N/a)=1`. Removing this tail from the first identity proves (1).

More generally, if `k>=2`, `k | (R+1)`, and `b=(R+1)/k<=N`, the same argument gives

```text
sum_(a<=N) mu(a) T_R(a,b)
 = 1-k-sum_(N<a<=kN) mu(a) floor(kN/a).                (2)
```

Equation (1) is the `k=2` specialization. It is a new explicit inverse consequence of the full-row identity in the #1036 audit, not a new bound.

Independent exact integer checks passed at
`R=3,5,7,9,15,21,57,101,317`. Repository search found no existing statement of this midpoint/dyadic specialization.

**Consequence.** A uniform absolute estimate on this midpoint column is exactly a uniform estimate on the dyadic increment `M(2N)-M(N)` up to the constant 1. Therefore the unpaid Euler interior cannot be attacked by declaring each boundary column harmless and summing absolute values. The complete signed interaction across `a`, `b`, quotient buckets, carry phases, and the other columns must be used.

**Exact scope.** This is not a proof that the full rank-one residual is target-equivalent to RH. The outer coefficient is `mu(b)` and may vanish; other columns can cancel this one; only odd `R` are covered by `k=2`; and a dyadic increment on this subsequence is not the canonical VF theorem. The result blocks one narrowing tactic, not the Euler mechanism itself.

## B. Current proof objective

The canonical theorem remains

```text
VFCanonicalSquareVonKochStatement:
  exists C>=0, forall R>=2,
  |pi(R^2)-VF_can(R^2)| <= C*R*log R.
```

It is open. `main@aed8eac` now contains:

- #1032, the inert `q^-3` to `q^-1` coefficient-transfer obstruction;
- #1033, weighted Euler boundary identities plus the owner/weight counterexamples;
- #1034, exact historical Abel transport, triangular signed Gram, and post-root divisor annihilation.

Draft #1035 proves the pointwise Newton coefficient flip and exact endpoint/finite-C conditional bridge. Draft #1036 proves the exact fractional signed Gram, rank-one subtraction, and divisor-row kernel. Neither draft proves its finite-C premise, a fixed positive exponent gain, the canonical VF bound, or RH.

## C. Competing mechanism portfolio

### 1. Euler fractional rank-one carry/phase covariance - PROMOTE / REVISE

**Concept.** Subtract the exact historical rank-one row, pay the reciprocal linear mode, divisor rows, and the full top `sqrt(R)` strip, then estimate the remaining nondivisor interior only as the complete signed quotient-bucket carry/phase covariance.

**Independent input.** For some fixed `eta>0`, an original-Mobius bound on the complete disjoint interior `C` from the #1036 audit of shape

```text
|C_R| <= C_(eta,epsilon) R^(1+epsilon) K_R^(1-eta/2),
```

with the separately controlled `(R+1)S_N` mode and every endpoint retained.

**Target implication.** The existing nonlinear square-root amplification consumer would turn the fixed-eta historical budget into the required Mertens-energy conclusion; draft #1035 records the exact finite-C endpoint gate.

**First unproved step.** A coupled estimate for the complete quotient-bucket sum. Divisor rows and the top strip are only strict subfamilies.

**Support.** #1034 is proved on main; #1035 and #1036 are exact-head green drafts. #1036 supplies an unconditional `O_epsilon(R^(1+epsilon))` divisor-row payment and a paper `O(R)` complete top-strip payment.

**Obstruction.** Claim `20261027-coordinator-1` shows the midpoint column is a dyadic Mertens increment. Per-column triangle bounds rehouse hard Mertens arithmetic. The continuous Abel corner is nonzero and must be restored.

**Decisive experiment.** On existing adverse/record roots, measure the signed complete interior by quotient bucket, but also isolate `C_mid(R)`. Falsify any proposed local estimate whose absolute column sum is forced to dominate the dyadic increment without an independent theorem.

**Assigned specialists.** Analytic for the complete carry/phase bilinear; Wheel for exact incidence restrictions; Census for the preregistered adverse-root discriminator; Referee for reverse implication and boundary audit.

### 2. Native #915 three-class returned incidence - CONTINUE

**Concept.** Use the exact physical classifier from `20261026-owner-1`:

```text
2 w^2 N_CC - 6 w(1-w) N_PC + 2(1-w)^2 N_RR,
```

coupled once to the active residual and historical anchor.

**Independent input.** A genuine prime/composite incidence theorem that pays the two positive classes by the unique negative class plus the named residual, on the literal clipped-parent/admitted-child carrier.

**Target implication.** A legal complete #915 source payment would feed the canonical VF first-bad architecture.

**First unproved step.** The all-cell incidence/residual inequality; the local nonpositivity threshold is not proved and is not the full payment.

**Support.** The three-class law is a paper theorem based on compiled source declarations. #1033 reinforces that integer least-prime ownership, Gram first-separation ownership, and `q^2` daughter indices are different.

**Obstruction.** Multiplicative parity does not determine the restored physical sign; positive `CC` and `RR` classes are real. No current-day Owner report tests the proposed global incidence.

**Decisive experiment.** Compute the three literal counts and the exact residual on adverse first-bad cells, preserving zero masks and multiplicity. One coherent family with a growing unpaid positive margin would force revision.

**Assigned specialist.** Owner Payment, with Referee checking no duplicated occurrences.

### 3. Original OAI fixed-character spatial Gram - CONTINUE AS INDEPENDENT / SUSPEND AS NATIVE BRIDGE

**Concept.** Estimate the literal fixed-Hecke-character spatial row kernel from `20261026-analytic-1`, with an explicit coherent/principal relation and a normalized nonresonant Schur bound.

**Independent input.** A source-specific bound on the genuine spatial sextic kernel, not completion over an unavailable character average.

**Target implication.** A complete source exponent gain could improve the independent OAI/NNS benchmark after all dyadic, principal, resonant, height, and low terms are paid.

**First unproved step.** Uniform control of `Lambda_nonres` and the signed coherent bill on the actual integrated atom family.

**Support.** The exact Gram reduction and finite normalized Schur theorem are paper-complete. The original one-prime local amplitude is available on its restricted source.

**Obstructions.** Today's Wheel/Census/Referee chain proves that a native rational `q^2` owner is not a literal normalized OAI packet: split packets have four terms, equal-norm slots are excluded by the existing normalized-low carrier, and inert coefficient matching costs an unbounded `q^2`. #1032 formalizes the last obstruction on main.

**Decisive experiment.** Instantiate the actual original row matrix only on source-admitted atoms and compute coherent classes and `Lambda_nonres`; otherwise report `SOURCE_ADMISSION_BLOCKED`.

**Disposition.** Keep as a genuinely independent analytic mechanism. Reject a zero-cost transfer from it to native CORR4/#915.

FINITE-AC, MU-LIFT, VF-LOW/JOH, CODIV, and NYMAN remain registered alternatives. They are not solved or retired, but no new evidence today justifies displacing one of the three mechanisms above.

## D. Conceptual research performed

The independent investigation worked backward from a proposed Euler proof failure. Suppose one tries to pay the #1036 nondivisor complement by estimating complete `a`-columns separately. The most structured interior column is obtained when `b` divides `R+1`, since the rank-one coefficient `(R+1)/b` becomes an integer. Formula (2) shows that these columns are not algebraically trivial: they are weighted high-interval Möbius sums. At the midpoint `k=2`, every high-interval quotient equals one, yielding the exact dyadic increment (1).

This changes the Euler strategy. The already paid divisor rows and top `sqrt(R)` strip are valuable because their proofs complete Möbius inversion before taking absolute values. But extending that tactic by a columnwise absolute norm reaches a real Mertens increment immediately. Any successful estimate must retain cross-column or cross-bucket cancellation, or import independently proved short-interval Mertens information with its exact strength disclosed.

### No-circularity review

- (1) and (2) are exact identities, not quantitative progress by themselves.
- A hypothesis `|C_mid(R)|=O(N^(1/2+epsilon))` is essentially the same bound on the displayed dyadic increment, not an independently paid local lemma.
- The full fixed-eta interior estimate is stronger than the paid local sectors and remains open; it must not be renamed as finite-C.
- The #1035 pointwise coefficient flip `Q_R=2M(R-1)-M(R^2-1)` is an exact endpoint bridge and makes the full `Q_R` estimate sufficient, not independently easy.
- The midpoint obstruction does not refute signed cancellation among columns or the complete carry/phase mechanism.

## E. Specialist findings

### Available October 27 reports

- **Wheel**, blob `8318a17434501b49d5a948c6dc750790dcdb0183`, claim `20261027-wheel-1`: accepts the inert/split/ramified slot-arity dictionary; one slot matches the native `q^2` scale only in the inert sector. Structural, no quantitative gain.
- **Census**, blob `842d50e673d5b6967b79835807a05b2d7bef49f8`, claim `20261027-census-1`: the split raw packet has four mandatory terms and the existing normalized-low theorem excludes equal-norm conjugate slots. Literal bridge refuted.
- **Referee**, blob `f7e86621f16ef102520c133287717b0b1aec79e0`, claims `20261027-referee-1..2`: accepts both scope-correct source findings and proves the unbounded inert coefficient distortion.
- **Lean**, blob `2e1c4f807055c964f07b3e6c344d156d803bbc7f`, claim `20261027-lean-1`: formalized the inert distortion in #1032. Its report said unmerged; live state now shows #1032 merged.
- **Owner and Analytic:** `TODAY=PENDING`. No missing execution is invented.

The complete October 26 reports were consumed as carry-forward: Coordinator/compatibility mirror `3377fbba13cc29427eab04939e836d7e3b86812a`, Owner `f4e51b5f6f240772f52bed114bcda6e77b330325`, Analytic `f3b66bc3e8329279025988e2058c4dd8769a3721`, Wheel `388e9b474496629e68107adc786dafc4adc90a5b`, Census `59741cbd8855f3b8c6682aafc30e663ddff855b9`, Referee `78650b99eea75338642dda3869c0da62018e2276`, Lean `764a3329a774715ad47a072a7d3dd56b4e5242f5`.

The external inbox remains blob `038018145c0fddb2f6306c0712373adf9cd1ea52`, with no entry newer than 2026-10-18. `EXT-20261018-PNT-1/2/3` remain exact identities, falsifiers, and source no-gos, not a payment for today's Euler interior.

## F. Mathematical bottlenecks

1. **Euler:** prove a complete signed nondivisor interior carry/phase estimate with fixed positive `eta`, retaining the linear mode and the nonzero continuous corner.
2. **Native #915:** prove the global three-class incidence plus residual payment on the original masked carrier.
3. **OAI:** bound the actual fixed-character spatial nonresonant kernel and coherent/principal bill; no native transfer is available for free.
4. **Canonical VF:** `OPEN-VF-ACTUAL-PRIME` remains unproved.
5. **Formal gate:** drafts #1035/#1036 contain exact bridges only; the missing quantitative premise remains mathematical, not a CI problem.

## G. Strategy decisions

1. Promote the Euler fractional/rank-one lane as the leading new Mertens mechanism because it has two independently paid strict sectors and an exact conditional consumer.
2. Require every Euler proposal to pass the midpoint-column falsification gate. Reject per-column absolute summation unless it supplies independent dyadic Mertens input.
3. Keep native #915 incidence as the direct canonical-VF mechanism; do not identify its three owner coordinates with Euler indices.
4. Keep OAI spatial Gram independent, but suspend native-to-OAI norm/slot transport after the accepted source-admission and coefficient no-gos.
5. Do not ask Lean Verification to formalize another identity merely for activity. The next valuable formalization is an independently accepted quantitative or inverse theorem; the midpoint theorem is optional after referee review.

## H. Next specialist assignments

- **Owner Payment:** state the complete global #915 three-class incidence plus active-residual identity on the literal first-owner Fubini carrier. Determine whether the `RR` or `CC` surplus forces a separately payable historical boundary. Falsifier: one duplicated prime occurrence or a cell family with positive margin not present in the named residual.
- **Analytic Type II:** attack the complete #1036 quotient-bucket carry/phase sum, not separate column norms. State the exact `q,b` ranges, the fixed `eta`, the `K_R` exponent, and all boundary costs. First test every proposed inequality against (1).
- **Finite Wheel & Incidence:** classify exact zero-carry/zero-phase and fixed-quotient incidences in the unpaid disjoint interior `a not|N, b<=N-floor(sqrt R)`. Produce either a density theorem with growing-carrier uniformity or a constructive family showing the structured cells are too sparse.
- **Prime Census Laboratory:** reuse existing Mobius data and sample adverse/record roots, recording the full interior, signed quotient buckets, absolute bucket sum, midpoint column, and `K_R`. Pre-register rejection when a claimed local contraction fails at one exact root; do not infer a uniform rate from finite data.
- **Adversarial Referee:** verify (1)-(2), including endpoints and the outer `mu(b)` caveat. Audit both directions of the proposed fixed-eta interior implication and decide whether it is independently stronger, target-equivalent, or false under the exact historical envelope.
- **Lean Verification:** first review current #1035/#1036 exact-head scope and avoid duplicate endpoint identities. If Referee accepts `20261027-coordinator-1` as useful, formalize it only as an inverse/no-narrowing theorem; otherwise wait for a genuine quantitative input.

## I. Lean and PR status

- #1032 merged as `d378ef1c256fc1c397a492bd94664db64f4a465a`; its exact head `e0368eb408b2ec0af780f258132571b6f7a1668b` had 9/9 observed PR workflows successful.
- #1033 merged as current-main component `aed8eaccecc0d898bea05dc5417fd649bb1c4b37`; exact head `456e305ae099da5b4cfeeb444850fca9d7a88746` had 10/10 observed workflows successful.
- #1034 merged as `629322315f76be998b5697ea05b0346da6b7a8e6`; exact head `7a4070ddd851fbbf4d60d45846d4a5a9d9242d25` had 12/12 observed workflows successful, including warning-fatal Euler import closure and Lean source audits.
- #1035 remains open draft, mergeable, head `3d9faa7735159802ca0fec36ab0cc6f1f875788a`, with 12/12 observed exact-head workflows successful.
- #1036 remains open draft, mergeable, head `c3ef5e99be34ae05db60b10ee71cbe011cf86754`, with 12/12 observed exact-head workflows successful.
- #1028 is no longer draft/open: it merged as `3d347068c77aec864d95a77a676cc0837324372f`. Its repeated-mark hard-face result remains diagnostic and does not prove a uniform gain.
- Combined-status endpoints returned no separate contexts; the exact-head Actions runs above are the relevant evidence. Green CI certifies stated Lean declarations, not the open quantitative estimates.

No merge, auto-merge, source change, central policy change, schedule change, or proof branch was performed by this Coordinator.

## J. Next-run resume capsule

Resume from `main@aed8eaccecc0d898bea05dc5417fd649bb1c4b37`, claim `20261027-coordinator-1`, merged #1032/#1033/#1034, and green draft heads #1035 `3d9faa7` and #1036 `c3ef5e9`.

The leading Euler mechanism has two paid strict sectors: divisor rows and the top `sqrt(R)` full-row strip. Its exact unpaid object is the disjoint nondivisor interior carry/phase covariance. The decisive obstruction is

```text
C_mid(R)=-1-(M(2R-2)-M(R-1))
```

for odd `R`; any local absolute strategy must explain rather than rename this dyadic increment. The highest-value next reasoning task is to find a cross-bucket transformation or inverse theorem that uses the complete signed interior and is not equivalent to assuming the desired Mertens gain.

The initial `IN_PROGRESS` mirrors were created by commits `0b31282382d5009867769b20028dc21843cdbdcd` and `2b94bff299374543f43c078449b1a364cc3d2b9a`, then read back as identical blob `95505bf8cd56370e892ea284e0747856023345d0`. Final publication requires replacement of both paths and identical-blob readback.

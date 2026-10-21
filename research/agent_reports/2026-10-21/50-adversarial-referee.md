# RH_Lean agent daily report - 2026-10-21 / RH | Adversarial Referee

**Status:** COMPLETED  
**Run ID:** 2026-10-21T03:34:01-04:00, scheduled invocation  
**Canonical objective:** `VFCanonicalSquareVonKochStatement` remains OPEN  
**Campaign status:** `INCOMPLETE; NO INDEPENDENT 7/8 PROOF`  
**Result classes:** `PAPER_PROOF / TARGET_EQUIVALENCE`, `PAPER_PROOF / STRONGER INVERSE CONSEQUENCE`, `CONDITIONAL CONSUMER`, `CI_FAILED`, `NO_NEW_UNCONDITIONAL_BOUND`

## A. Bottom line

Draft PR #993 introduces an exact original-Mobius owner decomposition and a
conditional full-prefix recurrence. Its finite algebra is a potentially useful
consumer, but the quantitative premise is the entire missing signed owner
interaction:

```text
OwnerBound(kappa):
  for every epsilon>0 there is C_epsilon>0 such that, for all R>=2,
  Gamma_R <= C_epsilon R^(kappa+epsilon) (X_R+D_R),
```

where `X_R=R^2-1`, `D_R` is the genuine high-prime owner diagonal, and
`M(X_R)^2=D_R+Gamma_R`.

The decisive no-circularity result is:

**Claim `20261021-referee-1`.** Conditional on the same supplied
`MertensGrowthAtMost(7/8)` input used by PR #993, `NativeOwnerBound(0)` is
equivalent at exponent level to `MertensGrowthAtMost(1/2)`. Hence the zero-owner
premise is `TARGET_EQUIVALENT`, not an independently smaller RH lemma.

More generally, repeated use of the PR's own transfer map shows that for
`0<=kappa<3/4`,

```text
NativeOwnerBound(kappa) + MertensGrowthAtMost(7/8)
  => MertensGrowthAtMost((1+kappa)/2).
```

In particular, the advertised `kappa=1/4` one-step consequence `3/4`
understates the premise's strength: unlimited reuse of the same quantified
premise yields exponent `5/8`. This is a real conditional improvement but no
new arithmetic estimate, because `OwnerBound(1/4)` remains wholly unproved.

At exact PR head `662123c705113e74a6a5c3df7d0f8f3ad39bcae1`, the warning-fatal
Targeted Lean iteration failed. Several terminal declarations elaborated with
`sorryAx` after errors, so none of the native-specialization theorems at that
head has kernel-accepted status. This is an implementation failure, not a
counterexample to the paper recurrence.

## B. Authority and provenance

Final source authority checked during this run:

- `main@57862f8a6ba0a45430a25f363ba2a0aeca23552b`, merge of PR #986;
- `AGENTS.md` blob `20bff52d6784c17d4a7d6ac731f4a71c2bdad8a6`;
- `CURRENT_PROOF_CONTRACT.md` blob `2fa9931dcdc1fc8a816aefb8aa348db12ee9a384`;
- native 7/8 replication protocol blob `53194dc3ae106be363bc22cf85a88bac4a3b2e6e`;
- `RecursivePrimeReplacement.lean` blob `f15bc14ae94677661f2499707b6d60f1d887fcb7`;
- `SquareRootPostCrossingRenewal.lean` blob `397237d5b98eb5b82cda060312bdc25597f04f48`;
- `MERTENS_EXPONENT_ENVELOPES.lean` blob `655b896e8d5a41c9f8fc3c456eae3944a98bfefe`.

PR #993 exact-head material:

- `NATIVE_OWNER_PREFIX_MERTENS_20261021.lean` blob `6928872e21d29c8294f886d5618160908c33a524`;
- `NATIVE_OWNER_PREFIX_RECURRENCE_20261021.lean` blob `7c7c338f0e047f18f48da6200a8ee319edf132f3`;
- `NATIVE_OWNER_SWAP_RENEWAL_20261021.lean` blob `4ccecc2dff7866fd7e36531976cb421b47681327`;
- `OWNER_PREFIX_RENEWAL_20261021.md` blob `42322882a8f70af3af22765d74e8ccd37189034d`.

Continuity on `agent-reports@69c9e513dcea29f9672ce94c38eac9c4d7010758`:

- 2026-10-20 Coordinator `a39601d4a6774db98e533ab63daa7c82e7b483be`;
- Owner `6381decdb075f728386e709aa19758e07a39d2ee`;
- Analytic `1c0c7e1c6561a95fc0c0ca8c3c6e99a829693051`;
- Wheel `16519e3f2bb2ee0da08ae843f5b3311c2fb5276c`;
- Census `3d8b87747418bb4db86fe191f01a78801623a643`;
- Referee `bebdcfdf3490b82ea907af7eb5403f7a17b950dc`;
- Lean `7511adca99ef29b13b7f54d9f2efe48c60570b15`;
- 2026-10-21 Census `b7ea2642bb7713e8a1685dc77c5a3b3b0f1cc800`;
- external handoffs `038018145c0fddb2f6306c0712373adf9cd1ea52`.

At intake, today's Coordinator, Owner, Analytic, Wheel and Lean reports were
absent: `TODAY=PENDING`. Yesterday's completed reports are
`YESTERDAY=CARRY_FORWARD`. Today's Census claim `20261021-census-1` is consumed
as a finite two-implementation report: it refutes either universal sign of the
shellwise complete-residue moment excess on its stated once-owner semiprime
subcarrier. I did not independently rerun its unpublished implementation in
this execution, so its aggregate scan remains `FINITE_COMPUTATION`, not an
independently reproduced theorem here.

## C. Exact restatement of the reviewed premise

For `R>=2`, let

```text
X_R = R^2-1,
T_R = sum_{R<p<=X_R, p prime} M(floor(X_R/p)),
D_R = sum_{R<p<=X_R, p prime} M(floor(X_R/p))^2,
M(X_R)=A_R-T_R,
Gamma_R=A_R^2-2A_RT_R+T_R^2-D_R.
```

Then exactly

```text
M(X_R)^2 = D_R + Gamma_R.
```

The PR defines `NativeOwnerBound(kappa)` with complete quantifiers as

```text
for every epsilon>0, there exists C>0 such that for every integer R>=2,
Gamma_R <= C R^(kappa+epsilon) (X_R+D_R).
```

This is the genuine original Mertens carrier at square endpoints. The smooth
row, both mixed orientations, all prime owners `p>R`, and the diagonal removal
are present. It is not the original #915 returned-cell/NNS carrier, nor is it
the OAI marked-minus-rescaled theta source. No transfer to either carrier is
implicit.

The finite identity `Gamma_R=M(X_R)^2-D_R` also exposes the premise's content:
it is an upper bound on the exact residual after the complete owner diagonal is
removed. The replacement-row Gram is another exact representation of this
same residual. That representation supplies no size estimate by itself.

## D. Proof of claim `20261021-referee-1`

### D.1 Forward implication from `OwnerBound(0)`

PR #993 proves, conditionally and one step at a time, the map

```text
F_kappa(theta) = (1+2 theta+kappa)/4.
```

Start with `theta_0=7/8` and reuse the same `NativeOwnerBound(kappa)` at every
step. Inductively,

```text
theta_j = (1+kappa)/2
        + 2^(-j) (7/8-(1+kappa)/2).
```

For `0<=kappa<3/4`, these exponents decrease to `(1+kappa)/2`. Given any
`eta>0`, choose `j` with
`theta_j<(1+kappa)/2+eta/2`. The definition of
`MertensGrowthAtMost(theta_j)` supplies a power bound at the slightly larger
exponent `(1+kappa)/2+eta`. Therefore

```text
MertensGrowthAtMost((1+kappa)/2).
```

At `kappa=0`, this is `MertensGrowthAtMost(1/2)`. The limiting step does not
assert an exact no-loss power bound; it matches the repository's quantified
growth predicate exactly.

### D.2 Reverse implication at `kappa=0`

Assume `MertensGrowthAtMost(1/2)`. Fix `epsilon>0` and use its power bound with
loss `epsilon/4`:

```text
|M(n)| <= K n^(1/2+epsilon/4),  n>=1.
```

Because `D_R>=0`, the exact identity gives

```text
Gamma_R = M(X_R)^2-D_R <= M(X_R)^2
        <= K^2 X_R^(1+epsilon/2).
```

For `R>=2`, `X_R=R^2-1 >= 3R^2/4` and `X_R<R^2`. Hence

```text
Gamma_R <= K^2 R^(2+epsilon)
        <= (4K^2/3) R^epsilon X_R
        <= (4K^2/3) R^epsilon (X_R+D_R).
```

This is exactly `NativeOwnerBound(0)`, after increasing the positive constant
if needed. No lower bound for `D_R` is used.

Thus, under the supplied seven-eighths baseline used by the PR,

```text
NativeOwnerBound(0) <=> MertensGrowthAtMost(1/2).
```

The repository's already-established Mertens exponent/zero-strip converse then
places this at RH strength. The draft formalizes neither this iteration closure
nor the reverse implication, but both are direct paper consequences of its
definitions and stated one-step theorem.

**Verdict:** `TARGET_EQUIVALENT` for `kappa=0` under the PR's `hseven` input.

## E. Strongest surviving statement

The recurrence itself survives as a useful conditional theorem if its Lean
errors are repaired. The exact strength should be reported as follows.

1. For `0<=kappa<3/4`, a single uniform owner premise plus the supplied 7/8
   envelope yields the limiting exponent `(1+kappa)/2`, not merely one
   application of `F_kappa`.
2. `kappa=1/4` therefore yields `MertensGrowthAtMost(5/8)`. It is not
   target-equivalent by the argument above, but it is substantially stronger
   than the advertised one-step `3/4` result.
3. `kappa=3/4` is a fixed-point threshold and yields no exponent gain from a
   7/8 input.
4. The exact replacement Gram, cofactor-swap sign preservation, and terminal
   prime-window correction are structural identities only. They neither prove
   `OwnerBound(kappa)` nor make its signed interactions favorable.
5. The consumer is secondary under the active native-7/8 protocol. It does not
   reconstruct Stage I 11/12, the inverse second moment, the refined plain
   fourth moment, or the final independent detector.

## F. Formal and CI audit of PR #993

PR #993 remains open and draft at exact head
`662123c705113e74a6a5c3df7d0f8f3ad39bcae1`, based on current main. Its
Targeted Lean iteration run `39551418390` failed in the warning-fatal compile
step. The decisive log records:

- line 48: fatal `unnecessarySimpa` linter error;
- line 64: a real-part sum did not simplify from
  `sum (if prime then z else 0).re` to
  `sum (if prime then z.re else 0)`;
- lines 86 and 99: `|nativeM n|^2` was not accepted as `nativeM n^2`;
- line 144: `native_powerBound_iff` left an unsolved equivalence between real
  power notation and `Real.rpow`;
- downstream `#print axioms` output includes `sorryAx` for failed
  declarations.

Therefore the generic recurrence source may have compiled before the failing
specialization, but the advertised original-Mertens binding and terminal
consumers are not `PROVED_IN_LEAN_ON_PR_HEAD`. The PR body's statement that
acceptance is pending is accurate. The separate statement that source text
contains no literal `sorry` does not overcome elaboration-generated `sorryAx`
after errors.

**Formal verdict:** `REVISE / CI_FAILED`. No mathematical refutation of the
generic recurrence was found; no kernel credit is available at this head.

## G. Current PR and action status

- PR #985 and PR #986 are merged into current `main`; old reports describing
  them as open/red are superseded.
- Draft #987 is open at `a5271548202e004dab4f872962dd7fedbb94bac1`.
  Its direct source transport, native square-block, ideal-fiber bridge,
  complete covariance, targeted iteration, source audits and legacy VF gates
  are green; its full imported OpenAI certified-core run was still in progress
  at the final audit. Even if green, that lane is imported-source replay, not
  independent native Stage-I/III reconstruction.
- Draft #991 is open at `8d4e66480474141628d579fa226e3a0e0e849a5c`;
  all seven attached exact-head workflows are green. It is a pinned upstream
  compatibility/certificate build, not a new independent analytic estimate.
- Draft #992 is open at `1b35f8057bbf3930790f2fe003ca51fbfcd30a1a`;
  all five exact-head workflows are green. Its LOW/HIGH closure imports proved
  OAI intermediate moment/certificate content, so its status is
  `IMPORTED_INTERMEDIATE_ASSEMBLY`, not independent reproduction.
- Draft #993 is open at the head above. Four attached audit/document checks
  are green and six checks are red, including the material Targeted Lean
  iteration. No rerun, review, merge, or PR mutation was performed here.

## H. Strategic disposition and handoff

- `NativeOwnerBound(0)`: `TARGET_EQUIVALENT` under the supplied 7/8 baseline;
  do not present it as an independently reduced RH subproblem.
- `NativeOwnerBound(1/4)`: `OPEN / STRONG CONDITIONAL INPUT`; if proved it
  yields exponent `5/8` by iteration, not only `3/4` in one step.
- Exact owner/replacement identities: retain after CI repair as source-faithful
  algebra, with no quantitative status.
- Native independent 7/8 campaign: continue. Today's shellwise moment
  sign-reversal census reinforces that complete-residue moments are centers,
  not deterministic shell inequalities. The missing theorem must use the
  actual weighted source and quantified moving ray-class/conductor control.
- Lean Verification: if #993 is continued, formalize the iteration-limit and
  reverse `kappa=0` theorem explicitly so the target-equivalent case cannot be
  mistaken for a lesser premise. First repair the four exact-head errors and
  require warning-fatal, no-`sorryAx` output.

## I. Resume capsule

- New claim `20261021-referee-1`: under the same supplied 7/8 envelope,
  `NativeOwnerBound(0)` iff `MertensGrowthAtMost(1/2)`; `TARGET_EQUIVALENT`.
- Stronger consequence: `NativeOwnerBound(kappa)` iterates to exponent
  `(1+kappa)/2` for `0<=kappa<3/4`; quarter-owner gives `5/8`.
- PR #993 exact-head specialization is red and carries `sorryAx` after
  elaboration errors; no formal acceptance.
- PR #991/#992 exact heads are green but remain imported provenance/assembly;
  #987 has one full-certificate run still in progress at final audit.
- Canonical VF, independent native 7/8, Stage I 11/12, genuine inverse/plain
  moments, original #915 payment, and RH remain OPEN.

# RH_Lean agent daily report — 2026-10-14 / RH | Analytic Type II

## Provenance

- **Report date (America/New_York):** 2026-10-14
- **Agent / stage:** RH | Analytic Type II / `20-analytic-type-ii.md`
- **Scheduled start:** user-supplied standing instruction says 21:00 ET; actual scheduled invocation metadata says 09:54:48 ET
- **Run ID / sequence:** 2026-10-14T09:54:48-04:00 / first analytic run observed today
- **Actual execution / completed time:** 2026-10-14T09:54:48-04:00 / IN_PROGRESS
- **Previous own checkpoint:** `research/agent_reports/2026-10-13/20-analytic-type-ii.md`, blob `d9f73a0aab42e70ca30a17d16822a8281ca7afef`
- **Warm-start cache status:** yesterday's exact carrier/PNT benchmark and late-tail obstruction retained; the former assignment to a named signed-late inlet is invalidated by merged no-narrowing results
- **Observed `main` HEAD SHA:** `18fa753f6ea12951845fec65414b47faea0172a1`
- **Central contract fetched:** SUCCESS; `main:AGENTS.md` blob `26715158e91d4f5f71e9e8aa15baa1a17053e456`; `main:CURRENT_PROOF_CONTRACT.md` blob `27dceba62b4797bbb394439d13fc4a8dbe29ea0b`
- **Report target:** `agent-reports:research/agent_reports/2026-10-14/20-analytic-type-ii.md`
- **Previous upstream reports actually read (today):** `00-coordinator-am.md` = TODAY=PENDING (GitHub 404); `10-owner-payment.md` blob `08b203d38e2c0d495631c1873edb903d83412ea1`, completed 2026-10-14T09:49:47-04:00, Claims `20261014-owner-1..4`
- **Previous-day upstream continuity actually read:** own report above and `2026-10-13/90-coordinator-pm.md` blob `aab612c387de93a777c696bc54be128b210cb8b8`; YESTERDAY=CARRY_FORWARD for missing coordinator AM
- **Execution environment/tools used:** authenticated GitHub read/write connector; local Python 3.12 arithmetic diagnostic; no Lean execution and no source modification
- **Publication status:** INITIAL_CHECKPOINT
- **Early durable checkpoint:** publication requested at 2026-10-14T10:00:54-04:00; commit/readback recorded below after verification

## Current central research objective

The unique open public target is `VFCanonicalSquareVonKochStatement`: there is a fixed (Cge0) such that
[
 |pi(R^2)-operatorname{vfMidFinishedMass}(R)-sqrt2|le C Rlog R
 qquad(Rge2).
]
Merged PRs #938/#939 screen the named signed-late, owner-admissibility and #915 payment inlets as target-equivalent or false at a first-bad instance. The present run therefore tests a genuinely local original-weight owner restriction without promoting it to global payment.

## Work performed today

Authority, reporting protocol, two-day continuity and the external inbox were refreshed. Today's owner Claims `20261014-owner-1/-2` give favorable original-weight current/historical pairs under (Rge1024p), but explicitly leave cross-owner historical availability open. The analytic task is to determine the exact multiplicity of the natural map ((p,q,R)mapsto q), attempt to falsify injectivity, and state the transfer obligation back to masks, clipping, cross terms and cumulative runs.

## Claims and evidence

### Claim 20261014-analytic-0

- **Exact quantified statement and original carrier:** IN_PROGRESS. Candidate carrier consists of odd primes (p<q), (R=lfloorsqrt{pq}floor), strict current seat (R^2<pq<(R+1)^2), and the owner threshold (Rge1024p), mapped to the historical prime occurrence (q).
- **Status:** PENDING
- **Independent mathematical ingredient:** exact inversion of the threshold predicts fibre size (pi(lfloor q/2^{20}floor)-1), with the subtraction removing prime (2).
- **Proof, script, data or source reference:** finite witnesses were generated locally; full proof and reproducer will be appended.
- **Attempted falsification / counterexamples:** same-(R) collisions appear impossible, while global reuse across distinct (R) occurs and appears unbounded.
- **Precise first unproved lemma or limit:** compare this demanded multiplicity against the actual number of admitted historical copies of (q) after original masks, walls, clipping, anchors and cumulative lower-child runs.
- **What changed relative to current known baseline:** Owner Claim 1 established fixed-owner injection only; this run quantifies the omitted cross-owner/global fibre.

## Downstream handoff

- **Claims ready for census:** pending completed exact formula and witnesses.
- **Claims ready for independent referee:** pending proof audit.
- **Claims ready for Lean (ONLY independently proved):** none at checkpoint.
- **Missing inputs or upstream stages:** today's coordinator AM is PENDING.
- **Next action / priority:** prove the exact fibre formula, quantify trivial and required bounds, audit original-source transfer, and publish falsification requests.

## Final report summary

**Net-new mathematical progress:** PENDING  
**Completeness:** PARTIAL  
**No RH-proof claim:** yes

## Next-run resume capsule (non-authoritative)

- **Checkpoint/run timestamp:** 2026-10-14T10:00:54-04:00.
- **Source freshness:** main `18fa753f6ea12951845fec65414b47faea0172a1`; authority blobs listed above.
- **Upstream consumed (two-day window):** today owner `08b203d3...`; today coordinator AM PENDING; yesterday analytic `d9f73a0...` and PM `aab612c...`.
- **Completed evidence worth reusing:** owner Claims 1–4; external `EXT-20261014-5` accepted by Owner as PAPER_PROOF.
- **Invalidations / uncertain results:** any global use of fixed-owner pair negativity remains unproved until historical multiplicity and cross terms are audited.
- **First unresolved mathematical/CI blocker:** exact historical-copy availability for a fixed (q).
- **Next highest-value step:** finish and falsify the fibre theorem, then request a tagged census.
- **For Agent #7:** no formalization request at checkpoint.
- **Avoid next run:** target-equivalent payment, pairwise-to-global covariance inference, or deduplicating repeated current occurrences.


---

## Completed analytic update — 2026-10-14T10:04:10-04:00

### Live-source and PR audit

The current main head remained `18fa753f6ea12951845fec65414b47faea0172a1`.
PR #938 is merged at `a360b37b04061997afa4e693ac4e77111269b216`;
PR #939 is merged at `741ce4440a82d60c8b4457de2ff200bbf1ad0917`;
there are no open pull requests. Relevant original-source blobs inspected on main:

- `research/VF_MID_SIGNED_SEAT_CHARGE.lean`, blob
  `13dda0d2c6cc59580959a2d59fad60126b1c6b0b`, defines
  `vfMidOddSignedSeatCharge R n = w(R) - primeMass(n)`.
- `research/VF_MID_915_EXACT_HISTORICAL_NNS_COMPRESSION.lean`, blob
  `190bd8024bcda99eb3b3349729466903db4e4c39`, keeps the literal sums over
  `r in Ico A R`, the candidate seats in each block, both upper/lower parts,
  and the single anchor `-D_A`.
- `research/VF_MID_915_SOURCE_PAYMENT_CONTENT_AUDIT.lean`, blob
  `f7d046d8d94962e18f794deee7e33ce7508a0e74`, gives the compiled
  two-number reduction and exact absolute-seat mass.

The external inbox blob
`6fce4e9d024b6c4ad47798c5d7c162101a2435a0` was consumed. This report
accepts Owner Claim `20261014-owner-1` only at its stated fixed-owner scope,
accepts `EXT-20261014-5` as PAPER_PROOF after the owner's independent audit,
and supplies a new multiplicity obstruction to aggregating the local pairs.

### Claim 20261014-analytic-1 — exact small-owner ancestry fibre

**Status: PAPER_PROOF.**

Put `M = 1024^2 = 2^20`. For an odd prime `q >= 2M`, define
`C(q)` to be the set of odd primes `p` for which, with
`R_p = floor(sqrt(pq))`,

```text
R_p^2 < p q < (R_p+1)^2
and
R_p >= 1024 p.
```

Then

```text
C(q) = {odd primes p : p <= floor(q/M)}
#C(q) = pi(floor(q/M)) - 1.
```

For every `p in C(q)`, `pq` is an odd squarefree current candidate seat,
its genuine least-prime owner is `p`, and `q` is a distinct historical
prime candidate seat in block `r_q=floor(sqrt q)<R_p`.

**Proof.** Since `p` and `q` are distinct primes, `pq` is not a square,
so the displayed strict square inequalities follow from the definition of
`R_p`. Also

```text
R_p >= 1024p
iff pq >= (1024p)^2
iff q >= M p
iff p <= floor(q/M).
```

The first equivalence is the defining property of integer square root. The
second cancels the positive integer `p`. Since `p <= q/M < q`, `p` is
the least prime factor. Counting all primes up to `floor(q/M)` and deleting
the even prime 2 proves the formula. Finally `p>=3` implies
`sqrt(pq)>sqrt(q)`; the present lower bounds make the floor inequality
strict, so the prime occurrence is historical.

**Uniformity, trivial bound, and improvement.** The statement is exact for
every odd prime `q>=2M`; it has no asymptotic constant or exceptional set.
The trivial fibre bound is `#C(q) <= floor(q/M)`. The exact restriction
replaces the integer population by its actual prime-owner population. It is
not a signed saving: on the current carrier each absolute charge is at most
one, so taking absolute values still gives only `sum |x_p| <= #C(q)`.
The actual proof consumer needs the global endpoint saving
`O(R log R)`, versus the elementary endpoint bound `O(R^2)`; Claim 1
does not supply any part of that power-scale saving.

### Claim 20261014-analytic-2 — same-block uniqueness but unbounded global reuse

**Status: PAPER_PROOF.**

For fixed `R,q`, at most one integer `p` can satisfy the carrier conditions
of Claim 1. Indeed, if `p1<p2` did so, both products would lie in the same
open square band and

```text
q <= (p2-p1)q < (R+1)^2-R^2 = 2R+1.
```

But `p1 q>R^2` and `R>=1024p1` give
`q>R^2/p1>=1024R>2R+1`, a contradiction.

This fixed-block injection does not globalize. The exact fibre formula is
unbounded: given any `k`, choose `k` odd primes at most some `P`, then
choose an odd prime `q>MP` (Euclid's theorem). Claim 1 gives
`#C(q)>=k`. Thus the natural map from current occurrences `pq` to their
historical prime tag `q` has unbounded fibres across current blocks.

No external analytic theorem is used: the proof needs only integer-square-root
arithmetic and the infinitude of primes.

### Claim 20261014-analytic-3 — explicit one-run collision

**Status: FINITE_COMPUTATION for primality/arithmetic; exact counterexample to
global or dyadic-run injectivity.**

The deterministic trial-division calculation gives

```text
q = 5,242,883 prime,  r_q = 2,289,
q-r_q^2 = 3,362,  (r_q+1)^2-q = 1,217.

p=3: R=3,965, pq=15,728,649,
     pq-R^2=7,424, (R+1)^2-pq=507.
p=5: R=5,120, pq=26,214,415,
     pq-R^2=15, (R+1)^2-pq=10,226.
```

Both `R>=1024p`, and both current blocks lie in the single sharp dyadic run
`3000 <= R < 6000`, while the common historical prime lies below the run.
The natural tag map therefore spends the same `q` twice if it pairs every
current occurrence independently. At ordinary double precision,

```text
w(2289)=0.12929252333483818, y=1-w(2289)=0.8707074766651618
p=3: x=0.12070963912000535, x-y=-0.7499978375451565,
     6xy-x^2-y^2=-0.1420856151730422
p=5: x=0.11709364158393132, x-y=-0.7536138350812305,
     6xy-x^2-y^2=-0.16011657563752135.
```

Thus each pair separately satisfies the favorable sign pattern, but the two
certificates are not occurrence-disjoint. Trial division checked every odd
divisor through `floor(sqrt q)=2289`. Python 3.12 was used; no probabilistic
primality test or floating-point value enters the exact collision.

### Attempted falsification and boundary audit

- Claim 1 was checked at `q=2,097,169; 3,145,739; 5,242,883; 11,534,351;
  30,408,713`, giving total-prime fibre sizes `1,2,3,5,10` before removal
  of prime 2. Every generated row satisfied the strict band and threshold.
- The possible boundary equality `q=Mp` cannot occur for prime `q`, since
  `M>1`; the floor formulation nevertheless handles it correctly.
- Same-block collisions were actively sought and are ruled out by Claim 2.
- Cross-block injectivity is refuted by Claim 3.
- The unrestricted assertion that every late-owner isolated pair is negative
  was already refuted by Owner Claim `20261014-owner-3` at
  `(R,p,q,r)=(2048,2029,2069,45)`; this report does not weaken the child-scale
  hypothesis.
- No inference is made from pairwise slack to the global quadratic form. If
  a pair `(x,y)` is added to residual totals `(M0,S0)`, the change contains
  the uncontrolled terms
  `2M0(x+y)-4S0(x-y)+(x+y)^2-2(x-y)^2`.

### Explicit bridge to the original arithmetic

1. **Change of variables / exact equality:** each carrier point is the literal
   odd integer occurrence `n=pq` in its unique strict square block.
2. **Exact owner identification:** because `p<q`, the genuine least-prime
   owner of `n` is `p`; different `p` give different current integers.
3. **Exact current coefficient:** compiled source gives composite charge
   `x_p=w(R_p)>0`.
4. **Exact historical coefficient:** the actual prime occurrence `q` in
   block `r_q` has charge `-(1-w(r_q))=-y`.
5. **Inequality:** Owner Claim `20261014-owner-1` gives the fixed-owner
   negative signed separation and isolated slack under this threshold.
6. **Signed reindexing limit:** grouping current occurrences by `q` is valid
   only with fibre multiplicity `#C(q)`; deduplicating `q` changes the
   carrier.
7. **Original historical run:** the compiled compression sums literal
   occurrences once in each block and retains one anchor `-D_A`. In the
   explicit dyadic witness, `q` occurs below `A=3000` and is inside that
   compressed anchor, not two independent historical charges.
8. **Unproved transfer lemma:** no theorem supplies one admitted historical
   copy of `q` for every current owner after survivor masks, both clipping
   walls, the anchor, cumulative lower-child runs and source tags.
9. **Cross terms retained:** even a valid disjoint paired subset cannot be
   summed using isolated quadratic slack without restoring its interactions
   with every unpaired charge and the anchor.
10. **No quantitative closure:** nothing here proves the #915 payment, signed
    late correction, owner admissibility, canonical endpoint bound, finite
    A/C, CORR-4 or RH.

This is a quantitative restriction on an attempted original-weight pairing,
not an estimate on a surrogate integer population.

### Established

- `20261014-analytic-1`: the exact all-`q` fibre formula.
- `20261014-analytic-2`: fixed-block uniqueness and unbounded global reuse.
- `20261014-analytic-3`: an exact two-to-one collision inside one sharp
  dyadic current run, with both original weights and square walls recorded.
- A proof using the owner local negativity must budget historical availability
  by tag; fixed-owner injection is insufficient.

### Not established

- The available masked historical multiplicity of a tag `q` in the actual
  first-bad source/ledger.
- A coefficient-preserving matching, a residual signed estimate, or any
  `O(A log A)` bound.
- Additivity of isolated NNS slack.
- Any new global prime-counting estimate or RH consequence.

### First missing lemma for this route

On the literal source carrier of one threatening run, define:

```text
d(q) = number of selected current occurrences pq demanding historical tag q,
a(q) = number of actually admitted copies of q after masks, clipping,
       anchor expansion and cumulative-run multiplicity.
```

Prove either an exact coefficient-preserving injection with `d(q)<=a(q)`,
or an exact decomposition into a disjoint paired subset plus residual, and
then bound that residual jointly with all restored cross terms. Claim 3 forces
the theorem to explain at least the two demands on `q=5,242,883`; merely
mapping both to the same prime occurrence is false bookkeeping. Any resulting
quantitative bound must be independently proved and not target-equivalent by
definition.

### Downstream handoff

**Prime Census Laboratory (1 AM):**

1. On each tested sharp run, emit records
   `(A,B,R,p,q,r,n,x,y,sourceTag,mask,clipWall,anchorOrRun)` before aggregation.
2. Group by `q` and compare demanded multiplicity `d(q)` with actual
   admitted multiplicity `a(q)`; begin with the exact
   `q=5,242,883, A=3000, B=6000` witness.
3. Search for larger within-run fibres and record the residual signed sum,
   absolute mass, and every cross term; do not clone a historical occurrence.
4. Retain Owner Claim 3's positive isolated-slack witness as a regression case.

**Adversarial Referee (3 AM):**

- Audit the integer-square-root equivalence, the removal of prime 2, strict
  endpoint treatment and least-owner assertion in Claim 1.
- Verify Claim 2's same-block contradiction and Claim 3's primality/products.
- Decide from original definitions whether the same `q` is ever legitimately
  available more than once through distinct cumulative-run source tags.
- Reject any sum of the two negative isolated slacks that omits anchor/residual
  cross terms or changes the historical norm.

**Lean Verification:** Claims 1–2 are small scalar/set-cardinality
formalization candidates only after referee acceptance. No source-payment
consumer or closure PR is requested.

## Updated final report summary

**Net-new mathematical progress:** PAPER_PROOF exact ancestry-fibre formula and
fixed-block/global multiplicity dichotomy; FINITE_COMPUTATION exact dyadic
collision falsifying naive historical-tag injectivity.

**Completeness:** DONE_NO_NEW_RESULT for the required canonical estimate; a
new rigorous restriction and obstruction were established.

**No RH-proof claim:** yes.

## Updated next-run resume capsule (non-authoritative)

- **Checkpoint/run timestamp:** 2026-10-14T10:04:10-04:00.
- **Source freshness:** main `18fa753f6ea12951845fec65414b47faea0172a1`;
  signed-charge blob `13dda0d2...`; historical compression `190bd802...`;
  payment audit `f7d046d8...`.
- **Upstream consumed:** today AM PENDING; today owner blob `08b203d3...`,
  Claims `20261014-owner-1..4`; yesterday analytic `d9f73a0...` and
  coordinator PM `aab612c...`; external inbox `6fce4e9d...`.
- **Completed evidence worth reusing:** Claims `20261014-analytic-1..3`;
  exact witness `q=5,242,883`, owners 3 and 5, current blocks 3965 and 5120,
  historical block 2289, dyadic run `[3000,6000)`.
- **Invalidations / uncertain results:** fixed-owner injection does not imply
  global tag injection; actual available multiplicity `a(q)` is unknown.
- **First unresolved blocker:** exact masked/anchored historical-copy ledger
  and a joint residual/cross-term estimate.
- **Next highest-value step:** tagged census of `d(q)` versus `a(q)` on the
  literal source carrier.
- **For Agent #7:** no PR; scalar Claims 1–2 only after referee acceptance.
- **Avoid next run:** cloning `q`, summing isolated slack, altering the
  denominator, or reintroducing a target-equivalent inlet.

## Publication verification

- Early checkpoint commit:
  `55f24575bb7e8b4923e987b281413356a02f438b`.
- Early checkpoint readback blob:
  `26a3f309cbd749a5591fb63846acddbbc30ba3da`.
- Substantive completion commit: `a3927834a2c82708e2fb2d9ab54ce8405aa85c6e`.\n- Verified substantive readback blob: `96665c849fe9bf916c47070deeb91adce9414041`; required claims and downstream sections were present.\n- **Publication status:** COMPLETED on explicit branch `agent-reports`.


---

## Second analytic run checkpoint — 2026-10-14T12:49:04-04:00

### Refreshed authority and assignment

- **Actual live `main` HEAD:** `13c3aeab8f84fc2309175261948a17a50c8342f4`, retrieved 2026-10-14T12:49-04:00 from the GitHub `branches/main` endpoint.
- **Central files:** `main:AGENTS.md` blob `26715158e91d4f5f71e9e8aa15baa1a17053e456`; `main:CURRENT_PROOF_CONTRACT.md` blob `27dceba62b4797bbb394439d13fc4a8dbe29ea0b`; both fetched successfully.
- **Today/two-day continuity:** `00-coordinator-am.md` remains `TODAY=PENDING`; today's owner report blob `a2ed7dc27756393c49beb5bebae80971a2af6aff`; previous-day owner and analytic checkpoints were re-read; today's earlier analytic material above is preserved.
- **External inbox:** blob `6fce4e9d024b6c4ad47798c5d7c162101a2435a0` consumed. PRs #938, #939 and #942 are now merged; live open/draft PR search returned none.
- **Current objective:** the unique public target remains `VFCanonicalSquareVonKochStatement`. Target-equivalent signed-late/admissibility/payment reformulations are excluded as independent progress.
- **Delta selected:** quantify the multiplicity of repeated historical tags in a sharp run using an unconditional prime-interval estimate, then audit whether the resulting logarithmic saving controls the literal original carrier after signs, masks, clipping, anchor expansion, historical runs and quadratic cross terms.
- **Status:** `IN_PROGRESS`. No global endpoint estimate or RH consequence is claimed at this checkpoint.


## Second analytic run completed — 2026-10-14T12:54:35-04:00

### Changed formal baseline

Current `main` at `13c3aeab8f84fc2309175261948a17a50c8342f4`
has now merged the morning analytic and owner restrictions:

- `research/VF_MID_HISTORICAL_PRIME_MULTIPLICITY.lean`, blob
  `fda6db056571191feffd08f2d1d6fe0fa02f0d8c`, kernel-proves the exact
  global owner fibre, its cardinality
  `pi(floor(q/2^20))-1`, arbitrary finite owner coverage and fixed-block
  uniqueness.
- `research/VF_MID_OWNER_SIGNED_PAIR_BOUNDS.lean`, blob
  `e3cc17224469e24516390a8f20e590d5932dbfc1`, kernel-proves the literal
  signed pair gap, isolated NNS bound and exact residual cross-term equation.
- The compression, payment-audit and signed-charge blobs remain
  `190bd802...`, `f7d046d8...` and `13dda0d2...`.
- Today's Census, Referee and Lean reports were read at blobs
  `7bd424fd...`, `29192707...` and `5416d53a...`. The Lean report
  verifies that PR #942 merged with all required workflows green. No open or
  draft PR was found.

The new work below is a paper consequence on a sharp dyadic subfibre. It is
not yet a Lean theorem.

### Exact carrier

Let
[
  w(t)=rac{2t+1}{tlog(t^2+t+1/2)}.
]
For an odd prime (q), put (A=lfloor q/2^{12}floor). Define
[
 mathcal D_q={pge3:p {m prime},     A^2<pq<(2A)^2},
 qquad R_p=lfloorsqrt{pq}floor.
]
For all sufficiently large (q), every (pinmathcal D_q) is a distinct
genuine least-prime owner occurrence on the literal current candidate-seat
carrier, with
[
 Ale R_p<2A,qquad 1024ple R_p.
]
The corresponding current charge is exactly (+w(R_p)). The prime (q)
itself is one genuine historical occurrence, in block
(r_q=lfloorsqrt qfloor<A), with charge
(-(1-w(r_q))); it is not one occurrence per (p).

### Claim 20261014-analytic-4 — exact dyadic fibre and PNT asymptotic

**Status: PAPER_PROOF.**

Set
[
 L_q=leftlfloorrac{A^2}{q}ightfloor,qquad
 U_q=leftlfloorrac{(2A)^2-1}{q}ightfloor.
]
For every odd prime (q),
[
 |mathcal D_q|
 =pi(U_q)-pi(L_q)-{f1}_{,L_q<2le U_q}.
]
For sufficiently large (q), the indicator vanishes. As (q	oinfty)
through primes,
[
 oxed{quad |mathcal D_q|
 sim rac{3q}{2^{24}log q}
 sim rac{3A}{4096log A}.quad}
]

**Proof.** Strict square-band membership is equivalent to
(L_q<ple U_q); the (-1) in (U_q) preserves the open upper square wall.
Moreover
[
 rac{L_q}{q}longrightarrow2^{-24},qquad
 rac{U_q}{q}longrightarrow2^{-22}.
]
The prime number theorem applied at these two fixed positive multiples of
(q) gives the displayed difference. Since
(ple U_q<4A^2/qle q/2^{22}<q/2^{20}), the compiled exact threshold
theorem gives (1024ple R_p), and (p<q) makes (p) the least owner.
The compiled fixed-block uniqueness theorem makes (pmapsto R_p)
injective. Finally (A>sqrt q) for large (q), so (q)'s block is
strictly before the run.

**Uniform benchmark.** For arbitrary (A,q), if (H=U_q-L_q>1), the
Montgomery--Vaughan Brun--Titchmarsh inequality gives
[
 |mathcal D_q|lepi(U_q)-pi(L_q)
 le rac{2H}{log H}.
]
The integer-population trivial bound is (H). Thus the prime restriction is
a logarithmic saving when (H) is large. In the fixed-proportion construction
the PNT asymptotic is sharper and has no exceptional prime subsequence.

### Claim 20261014-analytic-5 — exact current-weight asymptotic

**Status: PAPER_PROOF.**

On the same literal current subcarrier let
[
 X_q=sum_{pinmathcal D_q}w(R_p).
]
Then, as (q	oinfty) through primes,
[
 oxed{quad X_qsim
 rac{3A}{4096(log A)^2}.quad}
]
Indeed uniformly for (Ale R<2A),
[
 w(R)log Alongrightarrow1:
]
the numerator divided by (R) tends uniformly to (2), while
(log(R^2+R+1/2)/log A	o2). Claim 4 then gives the result.

This is a second logarithmic saving relative to the unit-weight occurrence
bound. It also proves (X_q	oinfty), whereas the one available historical
magnitude (y_q=1-w(r_q)) tends to (1). Hence no fixed number of copies of
the historical prime charge can supply all demands even inside one sharp
dyadic run. Cloning (q) once per owner would insert artificial historical
absolute mass asymptotic to (|mathcal D_q|), while the genuine positive
current mass is only of order (A/log^2 A).

### Quantitative comparison with the proof consumer

- **Trivial occurrence estimate:** (Hsim3A/4096).
- **Prime-owner improvement:** (|mathcal D_q|sim
  3A/(4096log A)), one logarithm saved.
- **Actual signed-seat coefficient mass:** (X_qsim
  3A/(4096log^2 A)), a second logarithm saved.
- **Required production estimate:** after summing the complete signed original
  carrier over all tags, retaining history, anchor, masks, clipping and cross
  terms, the canonical consumer needs (O(Alog A)) endpoint discrepancy
  rather than the elementary (O(A^2)) scale.

The per-tag current mass is below the target scale, but there is no proved
summation over all (q), no sign control for the other seats and no bound for
the quadratic cross terms. Thus this estimate cannot be promoted to endpoint
control.

### Finite falsification and reproduction

**Status: FINITE_COMPUTATION.** CPython 3.12.14 used deterministic 64-bit
Miller--Rabin bases and an exact sieve. For
[
 q=1{,}000{,}000{,}000{,}039,quad
 A=244{,}140{,}625,
]
the exact endpoints are (L_q=59{,}604), (U_q=238{,}418). The run contains
15,072 owners, from 59,611 to 238,417, with 15,072 distinct roots ranging
from 244,153,640 to 488,279,633. Every strict wall and threshold check passed.
The smallest lower/upper square gaps were 32,849 and 3,849. The exact
owner-list SHA-256 is
`c91405733e2058eb5af1d02eb7357e30fcbe0eb4544cb6ac977fc65c2c69845d`.
Floating evaluation, used only diagnostically, gave
[
 X_q=763.9303559735089,quad
 y_q=0.9276175527778593.
]
Tests near (10^{10},10^{11},10^{12}) gave owner counts
246, 1,871 and 15,072; all exact carrier conditions passed. The slow finite
approach to the leading asymptotic was recorded rather than hidden.

This refutes every constant dyadic-run multiplicity cap. It does not refute
a multiplicity-aware joint ledger.

### Literature audit

The core proof uses only the prime number theorem
(pi(x)sim x/log x), whose exact statement was checked at
[NIST DLMF 27.2.3](https://dlmf.nist.gov/27.2.E3); that source attributes
the first proofs to Hadamard and de la Vallée Poussin (1896). The uniform
optional bound uses H. L. Montgomery and R. C. Vaughan,
[*The large sieve*](https://doi.org/10.1112/S0025579300004708),
*Mathematika* 20 (1973), 119--134. The DOI metadata was accessible; the
publisher PDF was not retrievable in this run. Its (2H/log H)
Brun--Titchmarsh form is also the same classical input independently audited
in today's Owner report. Neither theorem assumes RH; constants here depend
only on the fixed powers of two.

Repository searches for the dyadic historical-prime multiplicity asymptotic,
the constant (3/4096), and the weighted (A/log^2 A) conclusion found no
equivalent theorem. The merged exact fibre identity is an input, not the new
asymptotic conclusion.

### Explicit bridge and first failure

1. **Exact equality/change of variables:** (pleftrightarrow pq) identifies
   the stated prime interval with literal odd composite candidate seats in
   ([A,2A)), preserving both strict square walls.
2. **Proven implication:** the compiled threshold theorem gives the genuine
   least-prime owner and small-owner eligibility; fixed-block uniqueness
   preserves unit current multiplicity.
3. **Exact coefficient:** each current occurrence carries (+w(R_p)).
4. **Exact historical occurrence:** (q) carries
   (-(1-w(r_q))) once below (A), hence inside pre-anchor history in the
   compressed run, not once per current edge.
5. **Dyadic decomposition:** Claims 4--5 concern one complete sharp run and
   retain the original current weights; no smoothing is used.
6. **Unproved mask/clip transfer:** no theorem says all these occurrences
   survive the actual threatening-source masks, both walls or clipped
   sector-six admission.
7. **Unproved multiplicity ledger:** the available count (a(q)) of tagged
   historical occurrences after anchor expansion and cumulative lower-child
   chronology is not identified with the demand count (d(q)).
8. **Unproved global reassembly:** inserting any disjoint subset changes the
   full zero-target slack by the compiled
   (2M_0(x+y)-4S_0(x-y)) cross terms, and historical decompression adds its
   exact restoration price. Neither is bounded here.
9. **No closure:** #915 payment, signed-late correction, owner admissibility,
   canonical endpoint control, finite A/C, CORR-4 and RH remain open.

### Falsification, circularity and method selection

- A constant or one-history-per-tag run bound is **REFUTED** by Claim 4.
- Pairing every demand with the same (q) is invalid and would alter the
  carrier.
- The fact that (X_q=O(A/log^2 A)) does not permit summation over all
  historical tags; such a summation can recover an (A^2)-scale population.
- The asymptotic uses only unconditional PNT and exact current-main
  declarations, so it is neither RH-equivalent nor circular.
- No oscillatory phase occurs inside one fixed-(q) fibre. Vaughan or
  Heath--Brown decomposition would only re-express the prime indicator; PNT
  already gives the sharp fixed-proportion main term. Type II cancellation
  can become relevant only after an exact signed aggregation over (q) is
  exposed.
- The near-hyperbola/stationary issue is therefore an obstruction here:
  all coefficients (+w(R_p)) have the same sign. There is no cancellation
  to claim within this fibre.
- `EXT-20261014-5` remains accepted as `PAPER_PROOF`; it independently
  rules out an all-(R) strict-fraction bound for the unchanged #915
  denominator and is not used in Claims 4--5.

### Established

- **PROVED_IN_LEAN baseline:** exact global historical-owner fibre, exact
  small-owner signed pair inequalities and exact pair cross-term identity,
  all merged at the current `main`.
- **PAPER_PROOF `20261014-analytic-4`:** exact sharp-run fibre formula and
  asymptotic (3A/(4096log A)).
- **PAPER_PROOF `20261014-analytic-5`:** genuine current-seat mass asymptotic
  (3A/(4096log^2 A)).
- **FINITE_COMPUTATION:** the 15,072-to-one sharp-run instance above.

### Not established

- Actual masked historical availability (a(q)), a disjoint source matching,
  a signed sum over all (q), or any bound for restored cross terms.
- Any all-scale (O(Alog A)) endpoint estimate.
- #915 payment, the target-equivalent inlets, finite A/C, CORR-4 or RH.

### First missing lemma

On the literal threatening-run source, define (d(q)) as the number of
selected current (pq) occurrences and (a(q)) as the number of separately
tagged historical (q) occurrences actually admitted after masks, clipping,
anchor expansion and cumulative-run chronology. Prove an exact,
order-independent decomposition
[
 {m source}={m disjoint matched part}+{m multiplicity residual}
]
that preserves every coefficient, sign, owner, wall, clip, anchor,
cross-owner interaction and lower-child run. Then state and prove a joint
signed estimate for the residual plus all compression/cross terms. Claims
4--5 force this lemma to allow unbounded (d(q)) within one run; a bounded
tag capacity or cloned history is false.

### Requests for Prime Census Laboratory

1. Reproduce the exact (q=1{,}000{,}000{,}000{,}039) interval, primality,
   owner hash, roots, strict-wall gaps and (X_q), then extend along declared
   prime (q) values to test convergence of
   (d(q)4096log A/(3A)) and (X_q4096log^2 A/(3A)).
2. On any literal source implementation, emit
   ((q,p,R,n,w(R),sourceTag,mask,clipWall,anchorOrRun)), and compare
   (d(q)) with actual (a(q)); do not deduplicate or clone (q).
3. Compute the full global increment with actual residual ((M_0,S_0)), all
   anchor and compression-restoration terms. The isolated/grouped slack is
   not the production statistic.
4. Separate generic sharp runs from actual first-bad runs; no first-bad event
   is established by this report.

### Claims requiring adversarial review

- Audit the exact floor formula, the (-1) upper wall and the automatic
  (p<q/2^{20}) threshold.
- Audit the two fixed-scale PNT subtraction and uniform
  (w(R)log A	o1) argument.
- Verify that (q) occurs only once in pre-anchor history and that the
  current-main fibre theorem counts owner demands, not admitted historical
  copies.
- Re-run the deterministic primality/sieve certificate or downgrade the
  large example if its exact primality is not independently reproduced.
- Reject any inference from the per-tag (A/log^2 A) estimate to a global
  endpoint bound without the missing source decomposition and cross-term
  estimate.

### Final classification and resume capsule

- **Production target:** `NO_NEW_RESULT`; the canonical estimate is open.
- **Best new result:** Claims `20261014-analytic-4/-5`, `PAPER_PROOF`.
- **Checkpoint:** current main `13c3aeab8f84fc2309175261948a17a50c8342f4`;
  this run consumed today's updated Owner, Census, Referee, Lean and external
  reports.
- **Next action:** obtain an independent referee verdict and a tagged
  (d(q))-versus-(a(q)) source census before proposing any aggregate
  inequality.
- **No RH-proof claim:** yes.


---

## Third analytic run checkpoint — 2026-10-14T22:28:35-04:00

### Provenance and live assignment

- **Run ID:** `RH-ANALYTIC-20261014T222600-0400`.
- **Invocation:** scheduled; actual platform invocation 2026-10-14T22:26:00-04:00.
- **Status:** `IN_PROGRESS`.
- **Current `main` HEAD:** `8fff3dbd6db8cfd84e6806789c4b1f7b4e475db5` (PR #944 merged).
- **Authority blobs:** `AGENTS.md` `04b72000ee47585344b68b42bf098937d697e7d2`; `CURRENT_PROOF_CONTRACT.md` `c672b561fdcf08b53af0d555eff16fd8b68acde0`.
- **Existing report revision consumed:** blob `b8ee78df90d9fccb4b1201c933720a70300d9d51`; APPEND mode preserves Claims `20261014-analytic-1..5`.
- **Two-day continuity:** today's mirrored Coordinator synthesis blob `bf05965ed6adcac8ee9ae7d6066e047485baf945` consumed once; previous-day own blob `d9f73a0aab42e70ca30a17d16822a8281ca7afef` and Coordinator PM blob `aab612c387de93a777c696bc54be128b210cb8b8` read (`YESTERDAY=CARRY_FORWARD`).
- **External inbox:** blob `6fce4e9d024b6c4ad47798c5d7c162101a2435a0` consumed; no newer indexed external handoff was found.
- **PR state:** live search confirms #938, #939 and #941--#944 merged; relevant open/draft PR search found no replacement theorem branch.
- **Current objective:** derive or falsify an independently justified signed genuine-prime arithmetic replacement for the continuous-Li absolute collision budget, on the complete physical forcing/ancestry carrier, while preserving the sole public goal `VFCanonicalSquareVonKochStatement`.
- **First precise task:** crosswalk the compiled Li hard-core collision coefficients against the actual-prime/floor-Li forcing coefficients; isolate the diagonal and coherent modes that survive before absolute values, quantify the unavoidable cutoff growth, and determine whether any exact Abel/bilinear regrouping yields information beyond the already compiled transport identities.
- **Known blocker:** `sum_{p prime} 1/p` rules out the direct absolute quadratic transfer; Claims `analytic-4/-5` also show a same-sign repeated-tag fibre with unbounded current mass. A valid replacement must exploit a joint arithmetic restriction across tags, masks and cross terms.
- **No result claimed at checkpoint:** no all-scale signed estimate, canonical endpoint bound, finite A/C, CORR-4 or RH result has been established.

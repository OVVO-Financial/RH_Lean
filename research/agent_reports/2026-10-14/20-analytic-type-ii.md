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

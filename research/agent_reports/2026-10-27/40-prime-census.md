# RH_Lean agent daily report - 2026-10-27 / RH | Prime Census Laboratory

**Status:** COMPLETED  
**Invocation:** one scheduled run begun 2026-10-27T01:51:01-04:00  
**Final refresh:** 2026-10-27T01:56:40-04:00  
**Pinned RH_Lean main:** `33195d014ee119e73d4517108e309f18cb02b7ad`  
**Pinned original source:** `openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a`  
**Primary nodes:** `MECH-CORR4-SIGNED-FIRST-OWNER-GRAM`, `MECH-OAI-NNS-COMPLETE-LEDGER`  
**Evidence status:** `PAPER_PROOF` for the exact source corollary; `FINITE_COMPUTATION` for two independent packet enumerators; `SOURCE_ADMISSION_BLOCKED`; `NO_NEW_GLOBAL_QUANTITATIVE_BOUND`

## A. Main result

### Claim `20261027-census-1`: split rational q-squared daughters are not literal normalized low-source two-slot packets

Today's Wheel claim `20261027-wheel-1` proves the correct Eisenstein slot arity:

- inert rational `q`: one prime-ideal slot of norm `q^2`;
- split rational `q`: two conjugate prime-ideal slots, each of norm `q`;
- ramified `q=3`: one prime ideal used with multiplicity two.

The smallest source-level test gives two independent obstructions to turning this arity dictionary into a literal native-to-OAI packet bridge.

#### 1. The raw split packet has four terms, not two

Let `A` and `B` be the two conjugate prime ideals above a split rational prime `q), and let `a,b` be their original primary generators. Then

```text
elementNorm(a) = q,
elementNorm(b) = q,
elementNorm(a*b) = q^2.
```

Expanding the actual source definition
`ProbeCompensation.tupleOperation` at `K=2` gives exactly:

```text
+ star(eta(a*b)) Phi_(a*b)(X,     Y,     Z*q^2)
- q^(-3/2) star(eta(b)) Phi_(b)(X/q,   Y/q,   Z*q)
- q^(-3/2) star(eta(a)) Phi_(a)(X/q,   Y/q,   Z*q)
+ q^(-3)                 Phi_1    (X/q^2, Y/q^2, Z).
```

Here `Phi_D` is the literal original `markedPhysicalProbe` with `W0,W1`,
calibration, exclusions, rows and character retained. The two middle terms are
distinct physical occurrences with different ideal labels and phases. A
two-term rational `q^2` replacement keeps only the first and last scales and
therefore omits both mixed `X/q` terms.

For the inert one-slot packet, where the single ideal has norm `q^2`, the
exact expansion is

```text
+ star(eta(a)) Phi_(a)(X,     Y,     Z*q^2)
- q^(-3)       Phi_1    (X/q^2, Y/q^2, Z).
```

Thus even in the arity-correct inert sector, the literal rescaled OAI
coefficient is `q^-3`, whereas the native CORR4 daughter coefficient is
`1/q`. The scale agrees, but the coefficient does not; their ratio is
`q^-2`. This does not rule out a separately proved weighted intertwiner, but
it refutes literal coefficient preservation from norm correspondence alone.

#### 2. The normalized low theorem excludes equal-norm cross-slot pairs

The original normalized low source uses

```text
T_j(Z) = pool(identityClass(M,H), S, a, b, Z^(ell_j))
```

with every `ell_j>0` and `ell` injective. For distinct slots `i,j`, suppose
without loss that `ell_i<ell_j`. The source's
`annular_power_separation` gives, eventually in `Z`,

```text
b * Z^(ell_i) < a * Z^(ell_j).
```

Every `P in T_i(Z)` and `Q in T_j(Z)` then satisfies

```text
Norm(P) <= b*Z^(ell_i) < a*Z^(ell_j) <= Norm(Q).
```

Therefore distinct normalized low slots eventually contain no equal-norm
pair. The conjugate primes above a split rational `q` both have norm `q`,
so they cannot form one literal two-slot packet in this theorem's injective
power-scale carrier. For `q=3`, repeated use of the same ramified ideal is
also excluded by the already-proved pairwise-disjoint slot condition.

This is a source-carrier obstruction, not a statement about all OAI
constructors. A raw `compensatedTuple` permits the split pair and produces the
four-term packet above. A future equal-scale or noninjective packet theorem
could also admit it, but that would be a new source theorem with its mixed
terms and collision rules explicit.

**Classification:** `PAPER_PROOF / SOURCE_ADMISSION_BLOCKED`. The proof is
an exact consequence of the original definitions and source lemmas, but it is
not yet one compiled Lean declaration.

## B. Mathematical question and preregistered discriminator

**Mystery.** Does the norm match between a native rational `q^2` daughter and
the OAI Eisenstein source expose a literal occurrence-preserving analytic
packet, or only a coarse scale analogy?

**Hypothesis H1 (direct packet).** One inert owner and one split conjugate owner
can be instantiated in the original normalized source with all W0/W1, slot
window, ray-class, exclusion, character, row and normalizer data, with the
native `q^2` daughter represented without additional source terms.

**Hypothesis H2 (source obstruction).** The raw compensation exists, but
original scale/admission geometry or inclusion-exclusion forces extra terms
or prevents the normalized packet.

**Observable fixed in advance.**

1. enumerate every subset term of the literal `tupleOperation`;
2. record its sign, norm power, surviving phase slots, X/Y divisor and Z multiplier;
3. test whether equal-norm split conjugates can occupy distinct original
   normalized slot pools;
4. compare the literal rescaled coefficient with the native `1/q`.

**Failure criterion for H1.** One mandatory mixed term, one failed original
admission premise, or one nonpreserved coefficient suffices. All three occur.
H1 is therefore refuted at literal-source scope; H2 survives.

## C. Exact carrier and source audit

### Native carrier

The RH_Lean quantity is the exact integer cutoff

```text
rawQ2ChildCutoff(R,q) = floor((R^2-1)/q^2),
```

with odd-prime owners in `canonicalRoughLowQ2Owners R` and reciprocal
coefficient `1/q`. No OAI character, ideal phase, window or normalizer is
part of this native definition.

Relevant current-main blobs:

- `RHLean/Proof/SignedTransportAmplificationAudit.lean`:
  `746f35f126f36e024d39e38c92dde30aabca266b`;
- `research/CANONICAL_ROUGH_Q2_TAIL_REDUCTION.lean`:
  `ebca096e83009a7df514d00b6a2696be86a94c55`.

### Original OAI carrier

The packet audit used the pinned source, not a surrogate:

- `Detector/Physical.lean`:
  `f0012db7d94f8f23893732b923c3b346f2fc89bf`;
- `Detector/Compensation.lean`:
  `93a2332f3e98d307c0e5f09d14f3175ca46ac9e7`;
- `Detector/CanonicalSlots.lean`:
  `0ae88f818a6c8f6b2c8dd4d5254ce34a14b026cf`;
- `Detector/RayPoolDisjoint.lean`:
  `f4c4412a840e93aa797edf065a1276be5db30f81`;
- `Detector/LowNormalized.lean`:
  `3a9f0257cdbde8fce7cc026ac62ef672c3e9820c`;
- `Moments/PrimePool.lean`:
  `7d8b18dce891a67b4f988e09fb2912d564c8fc16`;
- `Hecke/NormFiberCharacters.lean`:
  `443c266bbd83d1391f6c1473be3211f8f597bc15`.

Literal normalized admission requires more than ideal factorization:

- membership in the ray identity class;
- exclusion from the finite source set `S`;
- annular norm bounds at the assigned `Z^ell` scale;
- supported primary generators;
- pairwise-disjoint distinct slot pools;
- nonzero slot-window value for a nonzero contribution;
- the original W0/W1 support, positivity and nonzero assumptions;
- the original Hecke character and calibration;
- the full row decomposition;
- the nonzero principal normalizer.

Neither the rational label `q=5` nor `q=7` determines these data. Moreover,
because every normalized exponent is positive, fixed examples 5 and 7
eventually leave all growing annular pools. They are valid hand-checkable
factorization witnesses, not fixed eventual source packets. A varying inert
prime can be admitted only conditionally on the ray, exclusion, annular and
window predicates. The requested fully instantiated packet is therefore
reported `SOURCE_ADMISSION_BLOCKED`, rather than filled with invented
weights or phases.

## D. Independent computation

Two independent implementations enumerated the powerset in
`tupleOperation`.

Python reference:

```text
python corr4_packet_audit.py
```

C++ cross-check:

```text
g++ -O2 -std=c++17 -Wall -Wextra -pedantic corr4_packet_audit.cpp -o corr4_packet_audit
./corr4_packet_audit
```

Both returned:

```text
inert norms: (selected, complement) = (1,25), (25,1)
split norms: (1,49), (7,7), (7,7), (49,1)
split signs: +, -, -, +
```

Checks also verified two and four terms respectively and total alternating
coefficient sum zero. The implementations share the published source formula
but use different enumeration logic: Python `itertools.combinations` by
subset size versus a C++ bitmask loop.

Environment and scratch hashes:

- Python 3.12.14;
- g++ 13.3.0 with `-O2 -std=c++17 -Wall -Wextra -pedantic`;
- Python SHA-256
  `f80dd6060e16aec0cb12b60465a2988c9fc78574573dea6829a29052263e06ba`;
- C++ SHA-256
  `4f72622264e3d0ce8600c46f5ecba349d3656b4f57c08bef2f7fc1fa39dced57`.

All discrete outputs are exact. No floating-point arithmetic was used.

## E. Exceptional and boundary behavior

- **Inert `q=5`.** One-slot norm scale `25` matches the native denominator,
  but the rescaled coefficient is exactly `25^(-3/2)=1/125`, not `1/5`.
- **Split `q=7`.** The raw packet has scales `49,7,7,1`; the two middle
  occurrences are mandatory and cannot be deduplicated because they carry
  conjugate ideal labels and potentially different phases.
- **Ramified `q=3`.** A repeated two-slot raw packet requires an explicit
  collision policy. It cannot occur in the distinct normalized low slots.
- **Boundary mechanism.** The split obstruction is not merely that the slot
  sets are disjoint: the strict annular separation orders the norms, so even
  two different ideals of the same norm cannot occupy different scale slots.

No broad range scan was run. These smallest exact cases are decisive for the
literal bridge and avoid repeating the completed `R<=10000` CORR4 census.

## F. Proof impact

### What is refuted

The following inference is false:

> matching the native denominator `q^2` to the norm of an Eisenstein ideal
> supplies a literal one-packet OAI representation with the native weight.

For inert owners it loses the coefficient and all phase/window data. For
split owners it additionally loses two mixed terms and conflicts with the
normalized distinct-scale slot geometry.

### What survives

A source-faithful comparison can still proceed in two narrower ways.

1. **Inert sector:** construct a conditional weighted intertwiner for varying
   inert owners that proves ray admission, window support and a compensating
   normalization converting the original `q^-3` term into the native
   `q^-1` bill, while retaining the complete complement.
2. **Split sector:** build a new equal-scale conjugate-packet theorem outside
   the injective-`ell` normalized low carrier. It must keep all four subset
   terms, both phases, both `X/q` mixed terms, row/principal contributions
   and cross-packet Gram terms.

The second item is the first genuinely missing source lemma suggested by this
run. A theorem controlling only the top `q^2` and bottom rescaled terms is
not source complete.

There is no new exponent saving. This claim does not prove
`OPEN-CORR4-MIXED-TAIL-POWER`, the OAI complete Gram estimate, the canonical
actual-prime bound, or RH.

## G. Authority and continuity

Final authority refresh:

- RH_Lean main remains
  `33195d014ee119e73d4517108e309f18cb02b7ad`;
- `AGENTS.md` blob
  `4db668b220bd7e68ec3fa72ef4857eaa0d01a1b3`;
- `CURRENT_PROOF_CONTRACT.md` blob
  `24bd727096001b68c76b28fe70c99b8d548d7bfe`;
- native-first routing blob
  `c9a74b1bf2727ff1522c27e9934f521671b128ae`;
- external handoff index blob
  `038018145c0fddb2f6306c0712373adf9cd1ea52`.

At final refresh, today's only completed upstream report was:

- Wheel `research/agent_reports/2026-10-27/30-finite-wheel.md`,
  blob `8318a17434501b49d5a948c6dc750790dcdb0183`,
  claim `20261027-wheel-1`.

Coordinator, Owner, Analytic, Referee and Lean were `TODAY=PENDING` at the
last refresh. The complete 2026-10-26 set was consumed as
`YESTERDAY=CARRY_FORWARD`:

- Coordinator `3377fbba13cc29427eab04939e836d7e3b86812a`;
- Owner `f4e51b5f6f240772f52bed114bcda6e77b330325`,
  claim `20261026-owner-1`;
- Analytic `f3b66bc3e8329279025988e2058c4dd8769a3721`,
  claim `20261026-analytic-1`;
- Wheel `388e9b474496629e68107adc786dafc4adc90a5b`,
  claim `20261026-wheel-1`;
- Census `59741cbd8855f3b8c6682aafc30e663ddff855b9`,
  claim `20261026-census-1`;
- Referee `78650b99eea75338642dda3869c0da62018e2276`,
  claims `20261026-referee-1..3`;
- Lean Verification `764a3329a774715ad47a072a7d3dd56b4e5242f5`,
  claim `20261026-lean-1`.

The external inbox has no entry newer than 2026-10-18.
`EXT-20261018-PNT-1/2/3` remain secondary direct-VF identities and
falsifiers; they do not supply this missing ideal-packet source theorem.

Live PR audit: #1028 is the only open PR, still draft at head
`199505e1e728a96608e25a27f45a83a27be1b4b0`. It is an all-Dirichlet
repeated-mark diagnostic and supplies no native packet bridge.

## H. Final summary and continuation checkpoint

**Independent advance:** the exact split packet is a four-term source object,
and the existing normalized low theorem cannot admit its equal-norm conjugate
pair across distinct injective power-scale slots.

**Hypothesis decision:** direct literal norm/arity bridge `REFUTED`;
raw arity-correct packetization `SURVIVES`; normalized source admission
`BLOCKED` without a new equal-scale packet theorem.

**Completeness:** DONE.  
**Quantitative progress:** NONE.  
**No unsupported RH/global-bound claim:** confirmed.

Next run should not repeat the subset enumeration or the `R<=10000` daughter
scan. The next falsifiable question is:

> Can an equal-scale two-slot conjugate packet be formulated in the original
> source while preserving pairwise occurrence labels and all four
> inclusion-exclusion terms, and does its complete spatial Gram have a
> source-specific signed restriction absent from the one-slot theorem?

A negative answer should identify the first exact constructor or mask that
forbids the packet. A positive answer must exhibit the literal theorem
quantifiers and retain the mixed `X/q` terms.

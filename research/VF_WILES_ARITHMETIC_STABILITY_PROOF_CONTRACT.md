# Wiles-style arithmetic stability: direct original-VF proof contract

**October 10, 2026. Status: NEW RESEARCH ROUTE, NOT AN RH PROOF.**
**Base:** `main`, independent of the still-draft analytic #922 and
quotient-variation #923 branches. **Do not silently turn this into a
proxy-tracking equivalence or the old unsigned source estimate.**

## 0. The exact Frey / Ribet / Wiles architecture

Wiles established modularity for a **larger arithmetically defined class**
of semistable elliptic curves, then Ribet's obstruction excluded the
hypothetical Frey curve. Our desired analogous implication is:

1. **Frey object:** hypothesize a genuine **first bad** square endpoint
   for the actual VF-mid prime-counting defect
   `D_R = pi(R^2) - VF_mid(R^2)`, where the wall is
   `2 R log R`. Build the **complete real prime-owner occurrence packet**
   at that endpoint. No artificial prime events or fitted anchor.
2. **Ribet obstruction — existing Lean:** in
   `research/VF_MID_FIRST_BAD_ACTUAL_ADMISSIBILITY_CERTIFICATE.lean`,
   `vfV2ActualFirstBad_sixSectorBudget_pos` proves that the original
   signed packet must satisfy

   ```text
   0 < vfMidActiveGlobalResidualExcess R
        + 2 * vfV2ActualSixSectorSignedMass R.
   ```

   The six mass is the actual six clipped raw-parent boundary families,
   not a fitted difference norm. The original NNS and VF weights remain fixed.
3. **Semistability / arithmetic coherence — part already established:**
   `vfV2ActualPrime_verifiedStructuralRules` verifies genuine odd seats,
   prime filters, unique owner incidence, original weighted Fubini,
   restricted Möbius/FTA decoder, historical charges once, and the
   original Co/Div boundary ledger. The norm dictionary from #919 adds a
   possible *different* arithmetic coordinate. These are arithmetic
   constraints, not a proven signed estimate.
4. **Wiles theorem — NEW research objective:** prove a **general,
   arithmetic-independent-of-pi stability theorem** for an explicitly
   realizable class of weighted owner/Hecke packets. The class must be
   defined through local source identities, multiplicative coefficient
   relations, involutive/Gram transport and finite occurrence maps,
   **never** through the conclusion that the aggregate budget is nonpositive.
5. **Modularity bridge — the hard missing theorem:** show the
   **genuine first-bad prime packet** admits the stable representation
   by an exact source-to-boundary classifier. Preserve every historical
   anchor, occurrence, mask, coefficient, sharp cutoff, squareful, live-3,
   off-diagonal, diagonal, and cross-owner term. Then `linarith`
   contradicts the existing positive obstruction and the native
   #918 consumer closes the von-Koch target (under the explicit classical
   criterion as already used elsewhere).

**No alternative RH equivalence and no fresh conjectural numerical rate
is an acceptable replacement for steps 4 and 5.**

## 1. What is unconditionally new on this PR

`research/VF_WILES_ARITHMETIC_STABILITY_KERNEL.lean` is intentionally
**Mathlib only**. It proves a universal finite signed transport theorem,
with no use of primes, VF, Li, RH, first-badness, or zero-free regions.

### A noncircular *candidate* coherence class

An element of `VFWilesReversibleCells α` consists of:

- a finite set of **occurrences**, not owner names;
- a return map `mirror : α → α` which is a genuine involution **on
  the chosen support** and preserves that support;
- the full signed physical amplitude `amplitude : α → Real`;
- a **pointwise** relation `amplitude (mirror i) = -amplitude i`.

A real coefficient, sharp physical weight, local zero mask, selected
prime tuple multiplicity, and historical age are part of an occurrence's
amplitude/index, not dropped after a Fubini swap. This definition contains
NO hypothesis that a sum, prime discrepancy, VF defect, or energy is small.

With `f(z)=4z-2|z|`, the universal theorem proves

```text
sum_i amplitude(i) = 0
sum_i f(amplitude(i)) = -2 * sum_i |amplitude(i)| <= 0.
```

If the support is paired once with an explicit reflected copy, the familiar
local law is `f(z)+f(-z)=-4|z|`. In either orientation, all signed
coefficient weights remain attached.

### Exact OAI/Hecke zero-mask inlet (new universal theorems)

`vfWilesSymmetricMask` gives a genuine induced coherent packet under an
arbitrary sitewise zero mask **provided** the mask commutes with the
occurrence-level return involution. Its stability theorem carries the original
amplitude through the mask. The mask-intertwining law must be proved for
the real OAI selected-prime tuples and native cutoff windows; no assertion
of that law has yet been made for actual primes.

`vfWilesZeroMaskEnergy_le_original` separately proves the unconditional
finite norm contraction of a zero mask. **Mask norm contraction alone is not
a bound on the signed cross-owner Gram**; the compatibility hypothesis and
full history remain necessary.

A distinct family of **explicitly realized** dissipative cells contributes
`-sum_j u_j^2`; `vfWilesUniversalArithmeticPacketStability` proves
the complete represented packet is nonpositive.

Finally,
`vfWilesFirstBadContradiction_of_arithmeticRepresentation` consumes
a positive budget and an **exact representation** into that finite class
and derives `False`.

**Boundary of proof:** the finite universal theorem is proved. The
source-to-boundary representation for `vfV2ActualSixSectorSignedMass`
is **NOT** proved. Do not describe this kernel as RH or as actual-prime
admissibility.

### Why this is not just the sign condition under a new name

A bare **scalar** existential equation

```text
budget = -sum of arbitrary squares
```

would be equivalent to assuming `budget <= 0`; it is prohibited as
the definition of the arithmetic class. A genuine representation
certificate must instead provide an **occurrence-level** classifier from
the already-defined original source sites to the finite signed packet,
with:

- inverse recovery of *every* source occurrence (weight- and mask-preserving
  finite Fubini with unique owner, no duplicate negative historical charge);
- a return map verified from factorization/ideal arithmetic and from
  the **same** physical coefficients at the source and destination;
- historical sinks imported from prior-good native source states, with
  an independently proved exact squared-norm identity, not invented
  negative heat or post-hoc sqrt of the residual;
- the scalar equality derived by summing those already-proved local
  identities, **not included as a primitive coherence axiom**.

If a literal involution is too restrictive (e.g. the rank tests in #922
exclude single unmasked rectangles), generalize the *independently
checkable structural representation* to a masked, higher-rank Hermitian
Gram or a positive operator factorization. **Do not weaken the native
source or add fictitious new sites.**

## 2. The four fantasy series and the actual prime member

The existing deterministic fantasy system is already stable:

- exact Li and `VF_mid` midpoint: even `O(1)` at square endpoints
  via `VF_MID_LI_UNIFORM_QUADRATURE.lean`;
- fractional VF cluster: exact at the specified square levels;
- midpoint-linear VF interpolation;
- floor-Li `Q(x)=floor(Li_2(x))`, with
  `|Q(R^2)-VF_mid(R^2)| < C0+1`.

The floor-Li event perturbation has a proved **exact** signed transport:

```text
xi(n) = 1_Prime(n) - (Q(n)-Q(n-1))
D_R = Q(R^2)-VF_mid(R^2) + (pi(4)-Q(4))
      + sum_{5<=n<=R^2} xi(n).
```

The solved fantasy *geometry* and propagation are useful. However the
fantasy events **do not satisfy literal prime-factor incidence** (example:
floor-Li jumps at composite 65). **Do not** claim Q and pi have the same
`Nat.Prime`/Möbius decoder. The genuine primes must enter a more general
stable **transport representation** through their actual arithmetic
structure, rather than through a false equality of sitewise events.

The repository also proves the normalized fantasy cone containment
statement is already equivalent to the desired von-Koch bound:
`actualPrimeContainedInSolvedFantasyRadialCone_iff`.
It is NOT an independent Wiles theorem and cannot be a premise of this PR.

## 3. Exact native acceptance seam

The only acceptable final native contradiction is the EXISTING sign pair:

```lean
theorem vfV2ActualFirstBad_sixSectorBudget_pos
    {R : Nat} (hR : 8 <= R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : Real) (R + 1)) :
    0 < vfMidActiveGlobalResidualExcess R
        + 2 * vfV2ActualSixSectorSignedMass R
```

and an **independently established**, occurrence-derived representation
implying the opposite `<= 0`. The current Mathlib-only theorem is a
well-defined possible *target codomain* for such a representation; it is not
yet the proof of existence.

An actual realization must proceed in this order:

**A. Original-source classifier.** Begin with exact one-block weights
`w_R=V_R/R`, physical odd seats, true `Nat.Prime` indicator, actual
historical `D_R` and the six `vfMidActiveReturnedRawParentFiberMass`
sums in the certificate. Define explicit source occurrences including
`(owner,signature,revealedPrime,clip,rawParent,historyAge)` so no source
term is forgotten. Store coefficient and zero mask *on each occurrence*.

**B. Arithmetic modularity / representation.** Use the already-proved
Möbius decoder and #919's excluded-six norm-coefficient transform, then
identify real actual arithmetic instances of the proposed involution or
masked spectral completion. Respect distinct n / 2n sharp cutoffs and
the OAI selected-prime/ideal tuple multiplicities. The sign reversal is
not permitted to identify distinct raw occurrences merely because they
have the same numerical weight.

**C. Independent energy theorem.** Prove signed cancellation/positive
operator stability *for all admissible coefficient packets* using the
coherence axioms derived from arithmetic, with constants or operator
norms uniform in R and all historical runs. An OAI 7/8 nonvanishing
statement or normwise centered-row polarization alone is insufficient.

**D. Historical compensation.** Show the active native residual, cross
terms, root/excluded sites, omitted ancestors, squareful and live-3
families enter the same weighted conserved ledger exactly once. Prove
the compensation for hypothetical first-bad states, not only on
observed small natural cases. No future 36m returns available early.

**E. Native consumer.** Produce an actual theorem of the form
```text
8 <= R -> FirstBad(2,R+1) ->
  vfMidActiveGlobalResidualExcess R
    + 2*vfV2ActualSixSectorSignedMass R <= 0
```
*derived* from A-D. Apply the existing
`vfMidActualPrimeFirstBadAt_two_succ_false_of_activeSixBoundaryBudget`
and `vfV2ActualPrime_RH_of_signedOwnerRule_and_base` with the explicit
classical criterion and finite-base inputs.

No `sorry`, `admit`, added `axiom`, or hidden declaration named
`actualPrimeOwnerEscapeAdmissible` carrying the entire desired result.

## 4. Independent red-team acceptance (do not declare victory on numerics)

An acceptable numerical implementation must stress *the original weighted
signed budget*, not a proxy norm:

- the genuine upper- and lower-wall fake-anchor examples around R=5266
  (which show genuine local prime supply can escape when history is altered);
- the actual anchoring D_R=-385.159422 there and its ~90,634 wall slack;
- genuine owner/root data at 317 and 1027; keep every signed occurrence;
- original native NNS upper/lower and six-sector totals at all R=8..6000;
- high-wall occupancy **conditioned on historical age**, not random
  independent owner signs;
- explicit occurrence audit when any prospective involution maps two
  distinct source occurrences to one sink (reject non-injectivity);
- a strict countermodel with unpaired positive f(1)=+2, and a Gram
  countermodel with H=1,J=-1, showing why antiphase completion is essential.

A successful small-root test is evidence against mistakes, **not** a
uniform arithmetic stability theorem.

## 5. Dependencies and scope

**Already on main:**
- `research/VF_MID_FIRST_BAD_ACTUAL_ADMISSIBILITY_CERTIFICATE.lean`
  for the real Frey packet and positive Ribet-style obstruction.
- `research/VF_MID_FIRST_BAD_PAYMENT_V2_PROOF_CONTRACT.md` for the
  historical once-only owner ledger and the original Sector Six gap.
- `research/VF_MID_OWNER_ADMISSIBLE_ESCAPE_CLASS.lean` for strict-child
  escape reproduction: its actual arithmetic membership is OPEN.
- `research/VF_MID_SOLVED_FANTASY_CONE.lean` and
  `research/VF_MID_FLOOR_LI_TRANSPORT_CANCELLATION.lean` for the
  solved fantasy bounds and exact signed event transportation.
- `research/VF_MID_919_OAI_NATIVE_PRINCIPAL_WELD.lean` and
  `research/VF_MID_919_QUOTIENT_SIGNED_RETURN.lean` for constructed
  norm coefficients and genuine physical translated amplitudes.

**Separate draft experiments:** #922 sharp compensated Hecke signed moment;
#923 quotient-variation return. They are alternate attempts to **derive
the actual arithmetic representation/stability** and are not imported into
this stand-alone branch.

**This PR's achieved theorem:** universally stable *reversible finite
occurrence packets*, with a kernel-checked conditional first-bad trap.

**This PR's open Wiles task:** prove that the actual first-bad arithmetic
owner packet has such a representation (or a provably sound, independently
derived higher-rank replacement) with all historical charge/weight
conservation. **Without that embedding, RH is not proved.**


## 6. Classification theorem: three separate proof obligations (2026-10-10 refinement)

The goal is a **single, noncircular transport class** with (i) a universal
stability theorem, (ii) membership of the true prime-count profile, and
(iii) independently constructed fantasy-model members.  These are three
DIFFERENT claims.  The Mathlib-only reversible-cell theorem proves a finite
conditional kernel, not all three.

### 6.1 Common interface: square-endpoint profiles, NOT a prime sieve axiom

For a profile F, use the square samples and increments

```text
A_F(R) := F(R^2)
D_F(R) := A_F(R) - VF_mid(R^2)
e_F(R) := A_F(R+1) - A_F(R) - V_R
D_F(R+1) = D_F(R) + e_F(R).
```

The interface should permit real-valued Li/fractional/interpolated VF
profiles as well as integer-valued floor-Li and pi.  Do **not** bake
`Nat.Prime`, exact prime-wheel survivors, or integer 0/1 jumps into the
UNIVERSAL interface: doing so wrongly excludes the fantasy examples.
Instead each concrete profile must furnish a **sound realization map** from
its own event/source data into a common finite weighted transport ledger.

Each occurrence must retain its source index, source multiplicity, exact
weight, mask, phase, clipping boundary, owner, and historical age. A
profile's realization map must be injective on physically distinct
occurrences, with a checkable inverse or a proved multiplicity-preserving
surjection. It must account for the entire physical boundary and ALL
historical charges exactly once. Nonnegative dissipative sinks must be
derived from independent local source identities, never manufactured from
a residual scalar square root.

The **crucial additional arithmetic constraint** is a genuine
return/compensation law (or an independently proved masked Gram/operator
contraction) on the physical transported amplitudes with the actual
coefficient signs. A permutation or an unweighted Fubini identity by
itself is not such a law. In the current reversible model, specifically,
`amplitude (mirror i) = -amplitude i` and mask symmetry are powerful
quantitative conditions, not consequences already established by prime
divisibility.

### 6.2 Required theorem gates

1. **Class/stability.** Construct a single source-realized,
   occurrence-faithful transport class, without mentioning pi, RH,
   first-bad failure, `D_F` channel containment, or the final budget sign
   among its *primitive* conditions. Establish a UNIFORM stability theorem
   for its members at square endpoints, using the locally certified
   physical return/Gram law and an exact history ledger. The theorem must
   control both upper and lower escapes. The current finite kernel is
   potentially an internal lemma, not proof of this gate.
2. **Actual-prime membership.** Instantiate F with the EXISTING pi
   definition. Import the established prime-wheel, least-prime-owner,
   restricted Mobius decoder, physical weights and original six-sector
   Fubini identities. THEN construct the new local signed transport /
   compensation certificate. `vfV2ActualPrime_verifiedStructuralRules`
   supplies structural input **but does not prove that certificate**.
   The sign-bearing representation must be proved by its individual
   finite-arithmetic/ideal identities before summing, without using the
   desired RH-scale bound.
3. **Fantasy membership.** Independently exhibit the SAME transport
   class's source-realized certificate for floor-Li, exact Li and the
   other existing fantasy profiles. Floor-Li can use its own rounding
   and midpoint-quadrature source data; it must not be falsely assigned
   prime-factor owners. Merely citing its previously established
   `O(1)` endpoint discrepancy is a proof of **stability**, not proof
   of membership in the new arithmetic transport class.

For actual primes, the exact unfinished target after gate 2 is the
ORIGINAL `vfV2ActualSixSectorSignedMass` and
`vfMidActiveGlobalResidualExcess` with their native signed weights.
`vfV2ActualPrime_signedOwnerRule_iff_noFirstBad` on main already warns
that listing the conditional first-bad budget sign as an admissibility
field is logically equivalent to listing the target conclusion. Therefore
no primitive class property may be an alias for this signed rule.

### 6.3 Sharp biased-staircase countermodel

Set, after any needed finite prefix adjustment,

```text
H(n) = Li_2(n) + n^(3/4)
N(n) = floor(H(n)).
```

For sufficiently large n,

```text
0 < H'(n) = 1/log(n) + (3/4)n^(-1/4) < 1,
```

so the integer staircase eventually has only 0/1 increments and is
nondecreasing. Also `N(n) ~ n/log n`; all telescoping identities and
`D_(R+1)^2 - D_R^2 = 2 D_R e_R + e_R^2` hold. But the proved uniform
midpoint quadrature for Li gives

```text
N(R^2) - VF_mid(R^2) = R^(3/2) + O(1).
```

This violates every fixed `C R log R` channel. Thus neither PNT
asymptotics, staircase shape, generic quadratic energy, nor abstract
pair algebra can be a sufficient CLASS criterion.

**Acceptance test:** identify the *first specific independently defined
transport/coherence axiom* that fails for N, with an occurrence-level
witness, while providing explicit certificates for floor-Li and prime
profiles. Showing only `N` fails the final channel bound is NOT enough
to establish this structural discrimination.

### 6.4 Prime-wheel versus fantasy: no false shared factorization

True primes are singled out by divisibility; on a square band,
`n` is prime iff it survives division by all primes up to the
appropriate square root (with endpoint conventions checked). This is an
exact finite **classifier** of genuine prime events. It does NOT
supply an anti-phase signed return or a uniform contraction after
weighting and historical restriction. The floor-Li staircase does not
satisfy that classifier. Conversely, analytic Li quadrature does not
prove any signed cancellation for the true prime-wheel transport.

The only credible shared class is therefore defined at the level of a
**realized, physical weighted transport certificate**, with different
honest source generators and the same independently proven local
coherence law. Proving that genuine prime incidence realizes this law
is the remaining major mathematical result. It must not be obscured by
renaming the law `admissible` or by assuming its existence in the
membership theorem.

### 6.5 Delivery and compile honesty

Track the three gates separately in CI and the PR summary:

- Finite universal kernel: **proved in this branch**, conditional on
  antipodal occurrence pairing.
- Structural prime incidence: **already established on main**;
  full signed transport / stable-class prime membership: **OPEN**.
- Fantasy endpoint stability: **already established on main**;
  actual membership in the proposed COMMON transport class: **OPEN**.
- Universal RH-scale class theorem and actual native six-sector
  contradiction: **OPEN**.

Do not describe any of these open gates as compiled or proved on the
strength of the conditional finite kernel.

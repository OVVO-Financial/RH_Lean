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

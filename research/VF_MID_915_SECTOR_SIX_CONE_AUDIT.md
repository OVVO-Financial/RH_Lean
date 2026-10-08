# #915 — Sector Six cone regression and revised proof contract

**Status:** empirical arithmetic-carrier tests added; **the exact half-scale payment remains unproved**. This audit is not a Lean certificate of RH and introduces no new analytic or distribution hypothesis.

## 2026-10-08 rigorous two-owner clipped flux and mixed response audit

**Source:** research/VF_MID_915_TWO_OWNER_CLIPPED_FLUX.lean
**Regression:** scripts/vf_mid_915_two_owner_flux_regression.py

### Completed INSERTION orders have zero order leakage

For any positive prime multipliers p,q on a common physical clock X:

    clippedInsert_X(q, clippedInsert_X(p,n))
       = if p*q*n <= X then p*q*n else 0
       = clippedInsert_X(p, clippedInsert_X(q,n)).

A final product on the clock implies both multiplicative prefixes are on
the clock. Thus **insertion-order clipping is NOT a source of saving**.
The incomplete first/next/returned raw-parent boundary instead records
which complete physical cube CORNERS are absent, not a failure of
multiplication to commute. Existing two-prime completed Fubini already
proves a stronger order-independent terminal-filter theorem.

### Toggles really can exit and re-enter

A prime toggle tau_p may add p when absent and strip p when present. For
distinct commuting toggles let t=tau_q(tau_p(n))=tau_p(tau_q(n)).
For an exact signed terminal weight W(t), the two clipped path weights have
difference

    Delta_pq(n) =
      1_{n<=X} 1_{t<=X}
      [1_{tau_p(n)<=X} - 1_{tau_q(n)<=X}] W(t).

This **exact** algebraic statement is proved by
vfMid915ClippedTwoStep_sub_reverse_eq_exitReturn, splitting the result
into the two mutually exclusive intermediate-support orientations.
vfMid915ClippedTwoStep_sum_order_flux sums the unchanged signed weight
over arbitrary occurrence sets, without taking a norm.

Those general occurrence sets are NOT yet identified with #915's actual
weighted historical/current first-owner quadratic Co/Div carrier. A
reversed path by itself cannot be spent as a real negative parent.

### Exact positive response curvature

For the physical adjacent-square positive cofactor response

    H_R(m) = sum_{R^2<d<=(R+1)^2, m|d} log(d/m),

and distinct primes p,q, the mixed difference
H_R(m)-H_R(mp)-H_R(mq)+H_R(mpq) is a sum of the following sitewise
terms, writing d=m*t:

| p divides t | q divides t | contribution |
| --- | --- | --- |
| no | no | log(t) |
| yes | no | log(p) |
| no | yes | log(q) |
| yes | yes | 0 |

All terms are nonnegative. The generic signed four-term Boolean identity
and its nonnegativity are formally proved in
vfMid915BooleanMixedResponse_eq_three_nonnegative_atoms and
vfMid915BooleanMixedResponse_nonneg. The separate direct link from this
Boolean lemma to the previously defined
vfMidSquareProtectedResponseLogMass has NOT yet been formalized;
the regression checks this exact relation numerically for actual
physical cofactor sums. Positive scalar curvature does **not**
imply a favorable sign after Möbius pair polarization.

### Concrete surviving historical/current leakage, not a negative heat proof

Take R=8, X=(R+1)^2-1=80, p=3, q=5, n=39:

    39 --strip 3--> 13 --adjoin 5--> 65 (both physical)
    39 --adjoin 5--> 195 [clipped] --strip 3--> 65.

The terminal 65 is an actual **composite** in the R=8 square block,
so the current source weight is +w_8=+0.496079621. The two
clipped path values are respectively +w_8 and zero. Both are
kernel-checkable finite arithmetic examples in the new Lean module.
The intermediate 13 is an actual *historical prime* with its own
different VF charge w_3-1=-0.076174181; replacing it by a synthetic
-w_8 would be an illicit retained-weight substitution.
The compressed prior defect D_a does not expose it as an independent
negative current-block Co/Div pair.

### Finite ordered path-flux census, ACTUAL current site weights

For sampled distinct ordered odd-prime pairs p<q <=R, enumerate the
real current square-block odd terminal t and its squarefree
historical factor-exchange start n. Verify both paths and all three
physical states. The weights are exactly w_R - 1_Prime(t); they are
NOT reweighted by a PNT density. In this signed *one-site* test:

| R | p,q | first-only nonzero paths | reverse-only paths | signed flux |
| ---: | ---: | ---: | ---: | ---: |
| 8 | 3,5 | 1 | 0 | +0.496079621 |
| 18 | 3,5 | 2 | 0 | +0.704407086 |
| 56 | 3,5 | 7 | 0 | +1.750622257 |
| 317 | 3,5 | 34 | 0 | +5.911596486 |
| 1027 | 3,5 | 109 | 0 | +15.725290599 |
| 317 | 5,7 | 30 | 0 | +5.216114547 |
| 1027 | 5,7 | 101 | 0 | +14.571140830 |

All nonzero tested terminals are actual composites, because a low prime
factor remains. Their one-site VF weight is POSITIVE. Hence on this
unrestricted path carrier the two-owner flux is NOT automatically the
desired favorable negative Co/Div heat. The first-owner survivor filters,
quadratic pair weights, and genuine signed historical counterparts remain
essential and are NOT tested by this table.

Independent positive-response curvature with m=1,p=3,q=5 is:
R=8: 44.646767; R=18: 134.691045; R=317: 4217.652951;
R=1027: 16244.292906. Direct four-response evaluations agree with
the exact atom-class summation to floating-point tolerance.

### Historical support is mathematically unavoidable

vfMid915TwoOddOwnerReplacement_exits_current_square proves that if
R^2<n<(R+1)^2, n=q*k, q<=R, and p,q are distinct odd primes, then

    p*k <= R^2 or (R+1)^2 <= p*k.

Odd low-prime factor replacement cannot leave BOTH endpoints in the
current open adjacent-square interval. Hence any true compensating
opposite-parity occurrence must be established across HISTORICAL
support or another actual independent pair fibre, not fabricated
within the current one-block site census.

**Result:** The two-owner test gives rigorous exact local identities,
a geometric no-go for pure-insertion order leakage, and *unfavorable*
positive one-site signed exit-return flux in the sampled actual carrier.
It DOES NOT prove the #915 hbalance gate. To obtain strict saving,
one still must construct a legal occurrence-preserving match between
this historical return geometry and the literal first-owner signed
quadratic packet, and prove an independent first-bad-specific
inequality after retaining the original denominator.

---

## 2026-10-08 PNT actual-prime reciprocal-star input and SIGNED payment test

**Use the PNT theorem already compiled in RH_Lean.** This is NOT a new
distribution-of-primes hypothesis; do not replace actual block prime counts by
their Li values, and do not assume PNT controls every square block.

Already formalized (external to #915's direct import closure):

1. nativePrimeNumberTheorem, in
   RHLean/Analysis/NativePNTTransfer.lean: pi(N) log(N)/N -> 1.
2. eventually_vfMidActualRootSquareReciprocalPrimeMass_lt_one,
   in research/VF_MID_ACTUAL_PRIME_ROOT_SQUARE_CONTRACTION.lean:
   for all sufficiently large R,
       beta_R = sum_(R<q<=R^2, q prime) 1/q < 1.
   PNT also gives beta_R -> log 2.
3. vfMidActualHighPrimeProtectedStarMass_eq in the same file:
       Star(R,m) = (1-beta_(R,m)) v(R,m) + Defect(R,m)
   on the actual reciprocal/protected square-block correlation. Each
   cofactor m is below R and each prime q is genuinely above R; only
   permitted mq<=R^2-1 occurrences appear.
4. abs_vfMidActualHighPrimeProtectedStarDefectMass_le and
   abs_vfMidActualHighPrimeProtectedStarMass_le_parent_of_rootMass,
   in research/VF_MID_ACTUAL_PRIME_STAR_DEFECT_CONTRACTION.lean:
       |Defect(R,m)| <= beta_(R,m) |v(R,m)|,
       |Star(R,m)| <= |v(R,m)|       if beta_R <= 1.

**Essential restriction:** These are high-prime reciprocal Euler stars for a
native PNT/protected block, NOT the low-prime least-owner removal census in
the original odd seats and NOT a proven matched historical/current return
on the #915 first-bad packet. The Euler star nonexpansion has no uniform
strict gain: the permitted defect can use up its whole beta*|parent| allowance.
It cannot be plugged into hbalance without a literal source/weight-preserving
pair-level Fubini transport and a new SIGNED estimate.

### Exact numerical target (not a proxy substitution)

For every actual square block R define

    P_R = pi((R+1)^2)-pi(R^2),
    D_R = pi(R^2)-VF_mid(R^2),
    V_R = (2R+1)/log(R^2+R+1/2), w_R = V_R/R,
    U_R = (-D_R)_+ + w_R*(R-P_R),
    L_R = ( D_R)_+ + (1-w_R)*P_R.

The ORIGINAL #915 sharp signed payment, including its +4 absolute heat term,
has the exact existing Lean equivalence:

    Margin_R
       = ThreeBoundaryTransportedExcess + 4*ThreeBoundaryAbsMass
         - ActiveGlobalResidualExcess
       = (U_R+L_R)^2 - 2 D_(R+1)^2
       = 6 U_R L_R - U_R^2 - L_R^2.

scripts/vf_mid_915_pnt_production_regression.py computes this using:
- exact sieved prime counts and VF midpoint masses, and the original
  parity-reduced seat charges; **no PNT-density substitution**;
- independently split squarefree-active and squareful-omitted charges, the
  original vfMidActiveDemandResidual/CapacityResidual formulas, and the
  physical unordered signed/absolute pair Fubini;
- formal occurrence-tagged parent sign-reversal z -> -z, with the exact
  Echild + Etransport = -4 |z| heat; these formal parent entries are NOT
  asserted to occur independently in the original historical source;
- an independent protected square correlation:
      v(R,m) = mu(m)*(-sum_(R^2<d<=(R+1)^2, m|d) log(d/m))/m,
      D(R,m,q) = mu(m)*(response(m)-response(mq))/(m*q),
  where response is the NEGATIVE log sum and q runs over actual R<q<=R^2-1
  with mq<=R^2-1. It checks the signed Euler-star equality, nonnegative
  beta, the defect budget, and aggregate absolute nonexpansion.

Representative **signed payment** values (positive = gate passes):

| R | actual beta_R | original sharp margin | normalized (U-L)^2/(U+L)^2 |
| ---: | ---: | ---: | ---: |
| 8 | 0.537667 | 22.028829 | 0.027125 |
| 18 | 0.622831 | 104.491820 | 0.105070 |
| 56 | 0.668437 | 628.228360 | 0.184765 |
| 119 | 0.669896 | 1777.023204 | 0.206054 |
| 317 | 0.679984 | 13423.784662 | 0.093334 |
| 1027 | 0.689169 | 105561.281363 | 0.107592 |
| 5266 | 0.691959 | 2090948.119616 | 0.045816 |
| 6000 | 0.691933 | 2583879.010666 | 0.095024 |

The full numerical **consecutive scan R=8,...,6000** passed:
- largest normalized squared imbalance 0.206053679, R=119;
- minimum original signed margin 18.949363, R=9;
- largest observed reciprocal-prime beta 0.692571322, R=5380,
  strictly below 1;
- largest |D_R|/(2 R log R) 0.045990242, R=15; **no first-bad state
  is actually witnessed in this scan**.

The direct Euler star is nonexpansive, but the signed defect almost exhausts
the allowed capacity:

| R | beta_R | total abs(defect) / allowed defect capacity | total abs(star) / total abs(parent) |
| ---: | ---: | ---: | ---: |
| 17 | 0.606596 | 0.991898 | 0.995554 |
| 56 | 0.668437 | 0.997863 | 0.998670 |
| 317 | 0.679984 | 0.999707 | 0.999811 |
| 1027 | 0.689169 | 0.999922 | 0.999949 |

At R=1027, the signed retained part is -4920.204 and the signed physical
defect is -13113.115, giving signed star -18033.319. This is a literal signed
sum; the physical defect is **not** a small unsigned perturbation.

**Decision for #915:** PNT resolves the high-prime reciprocal owner *mass*
budget and the existing Euler star is exact. The unproved first-bad payment
is NOT resolved by those facts: its signed physical defect nearly cancels
the nominal gain from (1-beta), and the star carrier has not been reassembled
as the original historical/current first-bad source. Preserve the original
+4 heat and original absolute denominator; prove the exact occurrence-matched
signed cross-owner correction against hfirst, not a new bound on pi(x).

Fast CI runs:

    python3 scripts/vf_mid_915_pnt_production_regression.py --extended

The numerical checks are deterministic finite regressions, **not** a proof of
an all-R cone, first-bad payment, or RH. The production hbalance remains open.

---

## 2026-10-08 forward correction: ascend from owner 2

**Use ascending least-prime-owner reconstruction of the ORIGINAL physical
source, not universal raw Sector Six descent.** This retains each physical
integer occurrence and its native VF seat weight. At cutoff S, the prefix
survivors are the physical odd seats not yet eliminated by odd primes <= S.

For a fixed block R set:

- w_R = V_R/R, P_R = the *actual* prime supply, D_R = pi(R^2)-VF_mid(R^2).
- C_(S,R) = R - |vfMidSquarePrefixWheelSurvivors(S,R)|.

With every *unremoved* odd seat provisionally assigned prime charge w_R-1,
the physical ascending ledger has exact coordinates

    G_(S,R) = -D_R + (w_R-1)R + C_(S,R)
    T_(S,R) = |D_R| + (1-w_R)R + (2w_R-1)C_(S,R)
    B_(S,R) = T_(S,R)^2 - 2 G_(S,R)^2.

At S=2, C=0. At S=R, all composites are removed uniquely at their least
odd-prime owner, so C=R-P_R and the ledger gives **exactly**

    G_(R,R) = U_R-L_R = -D_(R+1)
    T_(R,R) = U_R+L_R = |D_R| + sum_{odd seats} |w_R-1_prime(n)|.

Thus the *original* anchored absolute denominator is recovered without
swapping it for a larger blockwise absolute sum. The existing
vfMid_root_sub_prefixSurvivorCard_eq_processedOwnerCards provides the exact
ascending owner census for every frozen cutoff 3 <= S <= R.

The **new kernel targets/checkable lemmas** in the #915 production file are:

    vfMid915AscendingProcessedMass_two
    vfMid915AscendingProcessedMass_eq_processedOwner
    vfMid915AscendingProcessedMass_full
    vfMid915AscendingStage_step
    vfMid915AscendingStage_slack_step
    vfMid915AscendingSigned_full_eq_anchored
    vfMid915AscendingAbsolute_full_eq_anchored
    vfMid915AscendingFinalSlack_eq_anchoredBalance

For a newly processed owner removing d previously surviving seats,

    Delta G = d,
    Delta T = (2w_R-1)d,
    Delta B = 2d[(2w_R-1)T-2G] + d^2[(2w_R-1)^2-2].

The cross-owner term uses the **entire accumulated** G,T. This is why
owner-by-owner cone payment cannot be substituted for the aggregate.

Numerical regression of **these physical degree-one coordinates**:

| R | B after owner 2 | B after owner 3 | B at full cutoff R |
| ---: | ---: | ---: | ---: |
| 18 | 89.626 | 165.913 | 104.492 |
| 317 | -10,120.581 | 25,572.580 | 13,423.785 |
| 1027 | -173,464.141 | 211,608.389 | 105,561.281 |

These stage values are provisional sieve configurations, not the actual
prime-seat source until full cutoff. The negative entries at owner 2 are a
**regression requirement**, not errors. The test
scripts/vf_mid_915_ascending_sieve_regression.py independently reconstructs
actual U/L from physical seat charges, checks both final G,T and the full
per-prime exact quadratic change, and runs in the fast workflow.

### Fundamental scope restriction: no unconditional cone induction

The completed anchored cone is **not** expected to remain nonnegative at all
large R. In fact, the classical Littlewood prime-minus-Li omega oscillations,
Brun-Titchmarsh P_R=O(R/log R), and RH_Lean's VF_mid-Li=O(1) square-endpoint
bound imply that |D_R|/(R/log R) is unbounded on a sequence, whereas current
one-block absolute seat mass and |D_(R+1)-D_R| are both O(R/log R). Hence
T_R^2 - 2 D_(R+1)^2 < 0 on that sequence. This is an external analytic
diagnostic, **not** a theorem already formalized in Lean and **not** a
counterexample to a hypothetical *first-bad-specific* statement.

Consequently never assert (a) cone membership of all intermediate S,
(b) universal balanced *completed* anchored U/L for all R, or (c) cone balance
of the raw #903 recursive sector. Passing tests through R=6000 does not
authorize any of these universal claims.

### What ascent proves, and what remains open

The new degree-one source equalities are **not the final payment**. The
remaining mathematical seam is a *pair-level historical/current Fubini
reconstruction* starting with those original ascending physical occurrences.
It must preserve multiplicities, survivor restrictions, orientation, site-VF
weights, historical D_A, the signed run/block cross terms, and the original
absolute mass; no artificial stripped-parent negative capacity may appear.

After that exact equality, prove under only hR and hfirst the unchanged
first-bad **signed sharp-transport** payment:

    ActiveGlobalResidualExcess
      <= ThreeBoundaryTransportedExcess + 4*ThreeBoundaryAbsMass.

The previously compiled heat and sharp-transport/source-inlet equivalences
then consume the payment. A generic cone induction is NOT the next proof
goal. No new PR, premise, or bridge is authorized.

---

## 1. Two different objects must not be identified

1. **#903 native recursive *sixth priority continuation***:
   `lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationPairFiber` in
   `VF_MID_CENTERED_GREATEST_OWNER_RANK_TELESCOPE.lean`, with
   `lowOwnerFirstOwnerDirichletPolarizationAtom` on admitted/admitted pairs.
2. **#914/#915 incomplete raw-parent *six oriented boundary sectors***:
   first-left/right, next-left/right, returned-left/right. The literal
   VF active clipped/admitted source has support only on
   **first-left + next-right + returned-left**.

The first is an admitted/admitted recursive lower-rank carrier. The second is a
retained-VF clipped/admitted physical boundary. Their U/L balance results do
not transfer without a new exact **matched-return** reassembly theorem.

## 2. Exact-rational falsification of the raw Sector Six cone

For a signed Dirichlet atom `z`, define `U = sum max(z,0)` and
`L = sum max(-z,0)`, retaining all original occurrences.
Let `B(U,L) = 6UL - U^2 - L^2`.

- **Production R=8, physical W=R^2-1=63.** The *entire* raw recursive
  Sector Six has one nonzero atom: first owner p=2, admitted pair (5,21),
  greatest owner r=7, stripped ordered parent (3,5), weight +1. Thus
  `(U,L)=(1,0)`, `B=-1`, normalized imbalance `1 > 1/2`.
- **Production R=18, W=323.** The complete recursive priority sector
  contains 106 occurrences, with **exact** `U=320/3`, `L=46/3`,
  `B=-16196/9`, and normalized imbalance
  `18769/33489 > 1/2`.
  The independent `fractions.Fraction` census agrees with the primary
  carrier implementation.

The universal claim `B(rawSectorSixUpper, rawSectorSixLower) >= 0`
is **false**, even after aggregating all raw recursive owner fibres at an
actual production clock. An individual owner-by-owner cone induction is
also invalid: its contributions can already be outside the cone.

## 3. Positive numerical result on the different retained-VF carrier

The complete one-block VF active-squarefree returned boundary was reconstructed
with site weights `v_R(n)=(2R+1)/(R*log(R^2+R+1/2)) - 1_Prime(n)`.
Its signed products were independently matched to the exact #913
retained-scalar Dirichlet-polarization weld, before classifying occurring raw
parents by greatest owner and chronological exit.

| VF block R | First-left | Next-right | Returned-left | Total | U | L | Cone slack |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 17 | 38 | 50 | 17 | 105 | 9.920289 | 11.514478 | 454.366 |
| 32 | 84 | 172 | 44 | 300 | 28.272083 | 29.753943 | 3362.628 |
| 56 | 330 | 571 | 89 | 990 | 70.139672 | 74.267598 | 20819.380 |
| 101 | 1020 | 2021 | 280 | 3321 | 225.182327 | 224.669482 | 202366.124 |

The three other oriented sectors are zero on those literal active sources.
All four complete active-boundary states lie in the cone.
A larger numerical scan through R=150 found 143/143 complete active-pair
states cone-admissible (maximum normalized squared imbalance ~0.019668).
**This does not test, or prove, the recursively descended compensated child-run
state.** The original `#915` anchored U/L numerator and absolute denominator
are different from the positive/negative split of pair products above.

## 4. Revised single mathematical seam

Maintain the unchanged production objective:

```lean
vfMidActualPrimeFirstBadAt_two_succ_halfScaleSectorSixPayment
```

`2 * D_(R+1)^2 <= M_R` under only `hR` and `hfirst`, with no
new hypothetical balance or transport premise.

**The ascending degree-one source-to-original-U/L equalities are now supplied. The next substantive theorem must be the complete pair-level physical historical/current-to-compensated-return reconstruction, not another cone identity.**

It must explicitly produce the *complete unsplit grouped return* with:

- owner labels, child-run endpoints, fresh-prime rank;
- original site-dependent VF scalar and **every occurrence multiplicity**;
- survivor restrictions and the real first-left / next-right /
  returned-left orientations;
- correctly matched stopped/terminal and stripped-parent contributions;
- the historical `D_A` anchor, with `A=R/2+1`;
- exact recovery of **both** the signed difference `U-L` and the
  original **absolute-mass denominator** `U+L`, without enlarging it
  by taking absolute values before cancellation.

**Only after the pair-level reassembly** is it legitimate to prove a
first-bad-specific global signed-run inequality. Universal anchored cone
membership and universal intermediate-stage cone induction are ruled out as
proof routes; a first-bad-conditional payment is still open.

One must not infer `B(U_A,L_A)>=0` merely from
`|D_A|<=2*rho_A` (a bound on a different coordinate).
The #903 raw recursion provides strict lower rank but **not** cone membership.
The algebraic identity `f(z)+f(-z)=-4*|z|` gives cooling for a
**genuinely matched** pair; it does not establish that the compensating
parent is already contained in the original source. Matched-return accounting
must be proved, not introduced as free capacity.

After valid historical/current reassembly and quantitative compensation,
the desired gate remains the existing #915 expression:

```lean
vfMidActiveGlobalResidualExcess R <=
  vfMidActiveThreeBoundaryTransportedExcess R
    + 4 * vfMidActiveThreeBoundaryAbsMass R
```

Then use the compiled
`vfMidActiveResidual_sharpTransport_iff_sourceInlet`,
the existing half-scale payment equivalence, and the compiled
strict `> 1/2` first-bad contradiction. These equivalences are **consumers**;
none supplies the missing inequality.

## 5. Regression acceptance

Run from repository root:

```bash
python3 scripts/vf_mid_sector_six_cone_regression.py
python3 scripts/vf_mid_sector_six_exact_r18.py
python3 scripts/vf_mid_915_ascending_sieve_regression.py
```

For a detailed diagnostic with full per-sector owner ledgers:

```bash
python3 scripts/vf_mid_sector_six_direct_probe.py --mode both \
  --r 8 18 --returned-r 17 32 56 101 \
  --output /tmp/vf_mid_sector_six_direct_results.json
```

**Do not invert the negative test into a positive assertion:** the production
R=8/R=18 raw recursive cone **must fail**. The sampled complete VF boundary
must pass. Neither numerical test discharges the rank induction.

Keep #915 **draft** and its terminal theorem **unproved** until the
unconditional payment compiles with warning-fatal checks, no extra hypotheses,
and a clean kernel axiom audit. No new PR is required.

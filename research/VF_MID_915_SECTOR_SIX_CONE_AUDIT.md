# #915 — Sector Six cone regression and revised proof contract

**Status:** empirical arithmetic-carrier tests added; **the exact half-scale payment remains unproved**. This audit is not a Lean certificate of RH and introduces no new analytic or distribution hypothesis.

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

**The next substantive theorem must be an actual physical
source-to-compensated-return reconstruction, not another cone identity.**

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

**Only after this exact reassembly** is it legitimate to ask whether the
complete compensated return forms a nonnegative cone state, or whether the
whole signed-run inequality follows directly without a cone induction.

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

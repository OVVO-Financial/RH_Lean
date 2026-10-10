# RH_Lean current proof contract

Status date: 2026-10-06. The direct VF-mid route is the canonical proof program.
Compiled Lean source and successful checks of the relevant commit are
authoritative. Historical handoffs, attractive finite plots, and stronger
sufficient criteria do not override this contract.

## Motto and guiding light

> **Close RH through VF.  Preserve the RH-scale target; do not replace it with
> a stronger block-by-block statement merely because that stronger statement
> fits finite data.**

The VF construction can remain an excellent RH-scale approximation to the
prime-counting staircase even though no fixed vertical alignment intersects
that staircase in every square block forever.  Those are different claims.

The canonical arithmetic target is therefore the cumulative square-endpoint
bound

```text
exists C >= 0, for every natural R >= 2,
  |pi(R^2) - VF_mid(R^2)| <= C R log R.
```

In Lean this is

`VFMidSquareEndpointVonKochBoundedStatement`

from
[`VF_MID_VON_KOCH_BRIDGE.lean`](research/VF_MID_VON_KOCH_BRIDGE.lean).

The already-compiled bridge
`vfMidVonKochBounded_of_squareEndpoint` extends that estimate to every real
cutoff `x >= 4`; `primeLiVonKochBounded_of_vfMidSquareEndpoint` combines it
with the unconditional VF/Li quadrature estimate; and
`riemannHypothesis_of_vfMidSquareEndpoint` feeds it into the repository's
explicit classical von-Koch/RH criterion.

The remaining work is therefore arithmetic control of the cumulative signed
VF error itself.  Write

```text
D_R = pi(R^2) - vfMidFinishedMass R
P_R = pi((R+1)^2) - pi(R^2)
m_R = vfMidBandMass R.
```

Then the exact recurrence is

```text
D_(R+1) = D_R + (P_R - m_R).
```

The square-wheel/FTA modules identify `P_R` exactly as the survivors of the
common finite prime wheel for that square block.  Thus the central research
question is signed cumulative control of

```text
sum_{r<R} (P_r - m_r),
```

at the `R log R` scale.  Local prime/composite dispersion, finite wheel
exactness, least-prime ownership, and square-root dependency are useful only
insofar as they help prove this cumulative estimate without introducing a
stronger false premise.


## Canonical closure route: structural admissibility, not realized cancellation

The final direct-VF closure is now stated as an admissible-class theorem rather
than as a request for a separate global cancellation estimate for the realized
prime sequence.

The class is formalized in
[`VF_MID_OWNER_ADMISSIBLE_ESCAPE_CLASS.lean`](research/VF_MID_OWNER_ADMISSIBLE_ESCAPE_CLASS.lean)
as

`VFMidOwnerEscapeAdmissible D`.

Its defining law is deliberately structural:

- finitely many base scales are not channel-threatening;
- every channel-threatening bad scale reproduces on an actual strict recursive
  VF child scale.

It does **not** assume `|D_R| <= K R log R`, a covariance estimate, a
prime-error cancellation rate, or membership in the solved fantasy cone.

The adversarial fuzzer already proves that exact recurrence, perfect midpoint
balance, and the quadratic energy identity are insufficient: an explicit
synthetic defect satisfies them and still escapes every radial channel. The
same file proves that strict-child reproduction kills every escaping trajectory
by strong induction.

The honest-prime obligation is therefore named explicitly:

`VFMidActualPrimeOwnerEscapeAdmissibleStatement`.

Once it is proved, the compiled theorem

`vfMidSquareEndpointVonKochBounded_of_actualPrimeOwnerEscapeAdmissible`

closes `VFMidSquareEndpointVonKochBoundedStatement` immediately.

The intended proof of actual-prime admissibility must use the exact arithmetic
mechanics already present in the repository: the VF-native seat carrier, exact
affine/Mobius decoder, first-separation owner, critical owner trichotomy,
strict continuation to a smaller state, and clipped outgoing contraction.
Those mechanisms may contain exact sign cancellation internally; no separate
long-range statement that the realized prime errors "cancel enough" is an
admissibility hypothesis.

Accordingly, `ActualPrimeContainedInSolvedFantasyConeStatement` is retained
as a valid metric sufficient condition and visualization, but it is **not** the
canonical remaining arithmetic obligation. Proving that cone membership
directly would be essentially the target bound in different coordinates.

## Route lock — 2026-10-06: multi-block escape control before pointwise reproduction

This section is binding for the direct VF route.

The solved fantasy/proxy constructions provide the cancellation geometry and
RH-safe reference channel.  They do not prove that the actual prime trajectory
already lies in that channel.

A crucial correction is that a parent escape need **not** force one child
endpoint to be bad immediately.  Several recursive child blocks can remain
individually inside the endpoint envelope while their signed increments lean in
one direction and accumulate.  Therefore a pointwise packet-to-bad-child
selector is not the canonical immediate theorem.

The repository has already proved the required **no independent
persistence** mechanism.  It must not be reintroduced as a new arithmetic
obligation.

At the scalar run level, the native dyadic identity isolates the chronological
owner census, while fixed-prefix/common-wheel placement contributes only
endpoint terms.  At the trajectory level, interior lifetimes telescope to
zero.  At the returned-core pair level, admitted/interior survivor mass is
eliminated before the recursive continuation is exposed: the signed cell
polarization separates rank-zero diagonal, mixed clipped boundary mass, and
the admitted positive-lag carrier.

PR #903 now packages the latter exact reduction as

`lowOwnerFirstOwnerSignedCellTelescope_eq_noPersistenceSafe_add_sectorSix`,

whose right side is literally

```text
(rank-zero diagonal
 + mixed clipped boundary
 + 2 * continuation sectors 1..5)
+
(2 * continuation sector 6).
```

No norm or estimate occurs in that equality.  The generic capacitor is then
instantiated directly by

`vfMidNoPersistenceCapacitor_forces_sectorSixDirichletMass`.

If the already-terminal/boundary side cannot absorb the signed cell demand,
sector six alone is forced above the residual threshold.  The theorem

`vfMidNoPersistenceCapacitor_forces_sectorSixDescent`

then extracts a literal sector-six pair and applies the existing continuation
classifier: its stripped ordered parent lies in
`postRootCovarianceRemainderRecursivePairCarrier (squareRootEndpoint R / r)`,
its fresh-owner rank drops by one, and all remaining fresh owners are smaller
than `r`.

Therefore **"prove that bias cannot persist" is closed infrastructure, not
the current seam.**  The remaining arithmetic inlet is narrower: the exact
first-bad actual-VF source/budget must be placed onto this already-cancelled
cell ledger with the survivor restriction retained, or bounded there by an
already-proved signed identity.  No new decorrelation, equidistribution, or
persistence hypothesis is authorized.

### Exact fan-escape capacity bills

The count-space geometry is now encoded explicitly in
[`VF_MID_FAN_ESCAPE_CAPACITY_BILLS.lean`](research/VF_MID_FAN_ESCAPE_CAPACITY_BILLS.lean).

For an arbitrary lower wall `L`, starting abscissa `x0`, and frozen count
height `y0`, `vfMidLowerWallCompositeRunBill` is the least natural
horizontal displacement `h` for which

```text
y0 < L(x0 + h).
```

Thus a completely prime-free horizontal segment must last at least this long
before the lower wall can overtake the frozen prime count.  The compiled
minimality theorem proves that every shorter horizontal run fails to hit the
wall.

For an arbitrary upper wall `U`,
`vfMidUpperPrimeJumpBill U x0 y0 h` is the least natural number `q` of
unit prime-count jumps for which

```text
U(x0 + h) < y0 + q.
```

Equivalently, when the wall gap is nonnegative, this is the order-free version
of

```text
floor(U(x0+h) - y0) + 1.
```

The generic theorem
`vfMidUpperWall_noBreak_of_capacity_lt_bill` is the exact capacity
contradiction interface: any rigorous prime-survivor capacity `cap` with

```text
cap < upperPrimeJumpBill
```

makes upper-wall escape impossible for every cluster whose size is at most
`cap`.

These definitions are specialized to the repository's normalized radial fan

```text
lower_R = VF_mid(R^2) - K R log R
upper_R = VF_mid(R^2) + K R log R.
```

The center-to-wall distance is kernel-proved exactly on both sides as

```text
H_R = K R log R.
```

The square-sampled lower specialization records the first later square endpoint
whose lower wall overtakes a count frozen at the center of `A^2`, and converts
that block offset to the literal integer span
`(A+s)^2 - A^2`.  The upper specialization records the exact number of prime
jumps required to rise from the center at `A^2` above the upper wall at
`(A+s)^2`.  A second compiled theorem consumes the trivial integer-site
capacity, and the same interface is intended to consume the much sharper exact
wheel-survivor capacities already present in the repository.

Reference diagnostic, not a kernel numerical certificate: for `K=2`,
`R=5266`, the half-width is approximately `90248.9854`.  Using the exact VF
band-mass formulas, the first later square endpoint whose lower wall overtakes
the frozen center is at offset `150`, a horizontal span of `1,602,300`
integer sites.  At the immediately following square endpoint, the upper wall
requires about `90,882.714` units above the starting center, hence `90,883`
prime jumps, while that whole square block contains only `10,533` integer
sites.

This is deliberately a **necessary escape-cost layer**, not an assumption that
actual primes already lie in the fantasy cone and not an all-scale theorem
excluding the required prime-free run or prime cluster.

The upper side is now wired directly to the repository's already-compiled
actual-prime block bounds.  Define

```text
RunPrimeSupply(A,s)
  = sum_{R in [A,A+s)} vfMidIntegerBlockPrimeSupply(R),
```

and, for any blockwise choice of prefix cutoff `S(R) <= R`,

```text
RunWheelCapacity(S,A,s)
  = sum_{R in [A,A+s)} vfMidPrefixWheelEnvelope(S(R),R).
```

The theorem
`vfMidSquareRunPrimeSupply_le_prefixWheelCapacity` proves exactly

```text
RunPrimeSupply(A,s) <= RunWheelCapacity(S,A,s).
```

No probabilistic prime-cluster estimate enters.  The cutoff may vary by block,
so the strongest convenient finite prefix wheel may be chosen independently at
each scale.

The theorem
`vfMidRadialUpper_noBreak_of_runPrefixWheelCapacity_lt_bill` then consumes the
new exact prime-jump bill:

```text
RunWheelCapacity(S,A,s) < radialUpperPrimeJumpBill(K,A,s)
  ->
actual RunPrimeSupply(A,s) cannot cross the upper radial wall
from the starting center.
```

The exact telescope
`vfMidSquareRunPrimeSupply_cast_eq_dyadicPrimeSupply` identifies that run
population with

```text
pi((A+s)^2) - pi(A^2).
```

Accordingly,
`vfMidRadialUpper_noBreak_of_runPrefixWheelCapacity_lt_bill_primeCounting`
states the same no-crossing result directly in the repository's actual
square-endpoint prime-count increment currency.

The one-block specialization
`vfMidRadialUpper_noBreak_oneBlock_of_prefixWheelEnvelope_lt_bill` gives the
same statement directly from
`vfMidIntegerBlockPrimeSupply_le_prefixWheelEnvelope`.  A coarse fallback
`vfMidSquareRunPrimeSupply_le_sum_roots` also packages the compiled global
`P_R <= R` bound.

Thus the upper-wall branch is a finite wheel-capacity comparison already in
actual-prime count currency.  The remaining arithmetic work is concentrated on
the lower/composite side and on the exact source/reassembly splice that sends
any unfunded signed excess into the recursive sixth sector.

The exact scalar capacity-bounce algebra is also encoded in the same module.
After a run-level Fubini reassembly has the form

```text
parentDemand = safeSectors + recursiveSector,
```

the following directions are binding:

- if `safeSectors <= cap` and `cap + H < parentDemand`, then
  `recursiveSector > H`;
- if `floorMass <= safeSectors` and
  `parentDemand + H < floorMass`, then
  `recursiveSector < -H`;
- consequently, if `|recursiveSector| <= H`, exact reassembly forces
  `safeSectors` into the rigid interval
  `[parentDemand-H, parentDemand+H]`.

This corrects an easy quotient-direction mistake.  An **upper** per-block safe
capacity `cMax` gives a **minimum number of safe blocks required** to absorb
the parent demand without descent.  It does not by itself give a maximum
vacuum-run length.  The literal finite "`M+1` vacuum blocks force a bounce"
statement uses a positive **lower** charge per vacuum block (or, preferably,
the exact cumulative zero-prime charge).  Once that cumulative charge exceeds
`parentDemand+H`, the recursive sixth sector is forced supercritical with the
opposite sign.

On the stacked #901/#902 population/complement branch, the exact complement
currency is

```text
C_eff = (N_C - epsilon) * w_S - P_C,
```

where `epsilon` is the possible right-square atom.  Thus `P_C = 0` gives
the maximum positive VF-minus-actual complement charge
`(N_C-epsilon) w_S` (equivalently the most negative contribution in the
prime-minus-VF convention).  Any future instantiation on #903 must preserve
this sign convention and must first have #901/#902 in its import ancestry.

### Intended run-level owner mechanism

For a threatening run, classify the exact chronological owner census before
taking absolute values.

- Fixed/small owner coordinates are periodic composite wheels.  Across many
  adjacent child blocks their discrepancy is an endpoint phenomenon, not one
  independent error per block.
- Terminal owners satisfy the existing run-uniform terminal condition; their
  stripped child is prime and belongs to the explicit stopped sector.
- Nonterminal late owners descend to lower square scales.  Their children must
  be grouped by **child runs**, not selected one block at a time.
- If a supercritical signed remainder survives after the equidistributed and
  terminal sectors are removed, it must reproduce as a supercritical
  lower-scale **run**.  The top child scale is strictly lower, giving the
  well-founded descent.

Only after this run-level theorem is proved is it legitimate to state
pointwise `VFMidActualPrimeOwnerEscapeAdmissibleStatement` as closed.

### Mandatory descent rule

No new "no coherent drift" theorem is to be introduced unless an exact
uncovered carrier is first exhibited.  The existing persistence cancellations
are to be consumed directly.

Every new theorem proposed for the canonical closure must instead answer:

> Does it place the actual first-bad source onto the already-cancelled
> terminal/sector-six ledger, or does it legally descend the resulting
> sector-six remainder to a strictly lower recursive state?

If not, it is diagnostic or an alternative route.

In particular:

- do not assume actual membership in the solved fantasy cone;
- do not replace run-level accumulation by an unjustified
  packet-to-single-child implication;
- do not start a new global Gram/covariance/H-norm program when the missing
  quantity is the centered multi-block chronological owner census;
- PR #900 remains an alternative sufficient route, not a dependency;
- PR #903 is restricted to exact classifier/Fubini bookkeeping that supports
  the run-level owner decomposition and lower-run descent.

## Exact modulo-30 factor-range lower gate (2026-10-10; #925)

The lower-channel *source statement* now uses only integer factor ranges,
the original VF band masses, and finite cardinality counts:
[research/VF_MID_THIRTY_FACTOR_RANGE_LOWER_GATE.lean](research/VF_MID_THIRTY_FACTOR_RANGE_LOWER_GATE.lean).
The reference/closure contract is
[research/VF_MID_THIRTY_FACTOR_RANGE_PROOF_CONTRACT.md](research/VF_MID_THIRTY_FACTOR_RANGE_PROOF_CONTRACT.md).

* For every R>=5, let W_R be the gcd(n,30)=1 candidates strictly inside
  (R²,(R+1)²), i.e. residues 1,7,11,13,17,19,23,29 modulo30. This
  EXCLUDES all odd n mod10=5, together with multiples of 2 and 3.
* C_R counts EACH n in W_R ONCE when it has some integer factor
  d in [7,R]. This source definition does NOT depend on Nat.Prime
  or pi. The EXISTING FTA square-wheel theorem, used only in the
  proof, decodes actual square-block prime supply as |W_R|-C_R.
* Already-established Boolean-wheel/Fubini theorems have a surprising
  all-run strength: for every A<=B,
  abs(sum_{A<=r<B} |W_r| - (4/15)*[(B²-A²)-(B-A)]) <= 32.
  This is a UNIFORM O(1) four-endpoint error independent of run length.
  It uses the root-endpoint correction; an O(B-A) sum of independent
  per-block errors would be unnecessarily weaker.
* Define E_r^30=C_r-(|W_r|-V_r). It is EXACTLY the original
  odd-seat/least-prime-owner tracking defect V_r-P_r; stripping 3,5
  does NOT create an additional arithmetic payment.
* The new source-only lower bound
  \`VFMidThirtyLowerFactorSafe K R\` is precisely
  sum_{5<=r<R} E_r^30 <= 9-F_5+K R log R.
  FTA converts it to D_R>=-K R log R, but that **source bound is
  presently OPEN**.
* With the selected sqrt(2) additive phase, the horizontal condition
  floor(F_L+sqrt2)<=pi(R²) is **exactly equivalent** to
  sum E_r^30 <= 9-F_5+F_R-floor(F_L+sqrt2); L may be R minus the
  canonical O(log(R)^2) root lag.
* Any first lower breach forces a STRICT source-native overrun
  exceeding the old historical slack plus the complete wall-growth
  allowance. The exact theorem provides the right input for the
  original signed parent/child / Sector Six owner argument.

The independent \`scripts/VFMidThirtyFactorRange/verify.py\` audits
integer least factors, original survivor identities, and the horizontal
sqrt(2) lag for thousands of square blocks. **A finite experiment is
not an all-R theorem, and no universal block-by-block crossing should
be assumed** (Littlewood forbids it). The remaining proof is to
prohibit the required once-owned factor-coverage overrun by a NEW
uniform signed arithmetic return theorem; FTA classification alone
does not bound it.

## Quantitative Li horizontal baseline (2026-10-10; stronger than bare PNT)

Use the provable **actual-prime logarithmic-integral error** as the
primary horizontal estimate, rather than just the PNT density limit.
This is **not** a claim that Li or VF is pointwise closer to true pi
at every finite x.

The repository ALREADY proves the unconditional, stronger **O(1)
VF-to-Li_2 square-endpoint quadrature** theorem
`vfMidLiSquareEndpointUniformBounded` in
`research/VF_MID_LI_UNIFORM_QUADRATURE.lean`.
The new exact actual-prime Li-to-VF transport in
[research/VF_MID_SQRT_TWO_LI_HORIZONTAL.lean](research/VF_MID_SQRT_TWO_LI_HORIZONTAL.lean)
gives, with a fixed deterministic `C_quad`,
`|pi(R^2)-F_R| <= |pi(R^2)-Li_2(R^2)| + C_quad`,
and the converse bound. The full conditional proof contract is
[research/VF_MID_SQRT_TWO_LI_HORIZONTAL_CONTRACT.md](research/VF_MID_SQRT_TWO_LI_HORIZONTAL_CONTRACT.md).

The classical de la Vallee Poussin zero-free-region theorem
**unconditionally** gives
`pi(x)-li(x) = O(x exp(-a sqrt(log x)))` for some a>0.
It improves bare PNT and, with the compiled O(1) bridge,
yields a quantitative VF error of the same shape.
It still does NOT establish the required
`|pi(R^2)-F_R| = O(R log R)`.

Numerically, using repository-normalized `Li_2 = int_2^x dt/log t`,
original VF is closer than Li_2 at 2497 of 2499 exact square endpoints
R=2..2500, but Li_2 is closer at R=2,3: an unconditional
**universal** VF-nearer-than-Li assertion is false even finitely.
An exact squared-error identity in the new Lean module isolates
the actual prime sign that decides which one is nearer.

**Never conflate**: proven uniform VF-Li quadrature; proven
unconditional pi-Li zero-free-region error (external, not yet
imported into Lean); finite observed VF advantage; open
RH-equivalent prime-VF signed endpoint bound.

## Chosen sqrt-two phase and PNT horizontal clock (2026-10-10)

The new route adopts **c0_chosen = sqrt(2)** as a fixed ADDITIVE
vertical phase, formalized as `vfMidChosenC0` in
[`VF_MID_SQRT_TWO_VERTICAL_PNT_HORIZONTAL.lean`](research/VF_MID_SQRT_TWO_VERTICAL_PNT_HORIZONTAL.lean).
This deliberately does NOT assert the false numerical equality
`sqrt(2) = 4 - 5/log(13/2)`: the latter remains the historical
x=9 *real exact anchor*, and the original VF block masses are unchanged.

The **independent horizontal question** is to translate the
VF square-root INDEX rather than add more vertical correction:
`VFMidSqrtTwoHorizontalRootWindow L R U` states exactly that
`floor(F_L+sqrt2) <= pi(R^2) <= floor(F_U+sqrt2)`.
The associated native finite lemma gives
`F_L-F_R+sqrt2-1 < D_R <= F_U-F_R+sqrt2`.

The repo already proves **actual-prime PNT**
`nativePrimeNumberTheorem`; its composition with the genuine square
clock, `vfMidSqrtTwoActualPrimeSquarePNT`, is being kernel-checked.
PNT and the independently elementary VF asymptotic support only
an eventual root-index displacement **o(R)**, NOT the horizontal
**O((log R)^2)** displacement corresponding to the original
RH-scale endpoint tracking target `O(R log R)`. The inverse-clock
asymptotic still awaits a direct native Lean theorem.

PNT alone cannot guarantee a prime in even ONE prescribed square
block: deleting the primes in the sparse blocks with R=2^k alters
pi(x) by at most O(sqrt x), preserving PNT while leaving infinitely
many blocks empty (as a logical countermodel, NOT as a replacement
for the true prime carrier). Original arithmetic remains defined by
`Nat.Prime`/FTA. Do not assume any universal fixed-phase crossing:
classical Littlewood excursions prevent it.

Complete specification:
[research/VF_MID_SQRT_TWO_VERTICAL_PNT_HORIZONTAL_CONTRACT.md](research/VF_MID_SQRT_TWO_VERTICAL_PNT_HORIZONTAL_CONTRACT.md).

## Fixed-alignment step-graph criterion: conditional only


**Discrete staircase / c₀ clarification (2026-10-10).**
See the formal proof/diagnostic contract
[research/VF_MID_C0_DISCRETE_STAIRCASE_ALIGNMENT_CONTRACT.md](research/VF_MID_C0_DISCRETE_STAIRCASE_ALIGNMENT_CONTRACT.md)
and its native implementation in
\`research/VF_MID_ALIGNED_STEP_GRAPH.lean\`.

* VF starts with discrete complete square-block masses
  \(F_R=\sum_{2\le r<R} m_r\), \(F_{R+1}-F_R=m_R\).
  The continuous \`vfMid\` interpolant agrees at square endpoints but is
  **not the original integer block step graph**.
* The canonical additive (NOT multiplicative) phase is
  \(c_0=4-5/\log(13/2)=1.328777548342988\ldots\), giving
  \(K_R(c_0)=\lfloor F_R+c_0\rfloor\) with \(K_3(c_0)=\pi(9)=4\).
* For any fixed \(c\ge0\), \(\epsilon_R(c)=F_R+c-K_R(c)\in[0,1)\) and
  \(K_{R+1}-K_R=m_R+\epsilon_R-\epsilon_{R+1}\).
  The REAL block dynamics are unchanged, and integer rounding **telescopes**,
  leaving only \(\epsilon_A-\epsilon_B\) over any range. No signed
  actual-prime Sector Six payment arises merely from choosing c.
* Independently replayed for every root R=2..10,000:
  canonical c₀ produced zero full-graph crossing failures; on the c-grid
  0..3 by 0.001, the 537 successful values range from 1.329 to 1.865.
  These are **finite diagnostics** and deliberately NOT a universal
  c₀ bracketing theorem.


PR #842 formalizes a useful sufficient implication for a fixed additive phase

```text
c0 = 4 - vfMidFinishedMass 3.
```

The corresponding statement is now named

`VFMidInitialAnchorAlignedStepGraphBracketingStatement`.

If that full step graph intersected the prime staircase in every square block,
the compiled theorem

`vfMidSquareEndpointVonKochBounded_of_initialAnchorAlignedStepGraph`

would imply the canonical square-endpoint VF bound.

However, universal fixed-phase block-by-block intersection is **not** the final
target and should not be pursued as such.  The reason is structural: because
the midpoint VF construction lies on the lower side of the corresponding Li
integral up to a fixed normalization, universal one-block crossing would force
a one-sided upper bound of order `sqrt(x)/log(x)` on `pi(x)-Li(x)`.
Classical Littlewood oscillation gives positive excursions larger than every
fixed multiple of that scale by an additional unbounded
`log log log x` factor.  Hence a fixed alignment must eventually miss some
blocks, even if it succeeds over every computationally accessible range.

This does **not** refute VF.  The legitimate RH-scale target allows

```text
|pi(R^2) - VF_mid(R^2)| = O(R log R),
```

which is vastly larger than one local block height
`m_R ~ R/log R`.  A fixed alignment can therefore fail block intersection
while VF still satisfies exactly the estimate needed for RH.

Finite aligned-intersection experiments remain valuable diagnostics of local
geometry.  They are never evidence that the universal fixed-phase statement
should replace the cumulative VF target.

## Research discipline for the VF route

1. **Keep the exact VF object.**  Do not rescale the midpoint construction to
   force a visual crossing phenomenon.
2. **Exploit FTA/square-wheel exactness.**  Prime supply in block `R` is the
   exact survivor count after sieving by the required prefix primes.
3. **Separate spatial dispersion from total supply.**  Left/right
   equidistribution controls placement inside a block; it does not by itself
   control `P_R-m_R`.
4. **Control signed accumulation.**  The target is the partial sum of
   `P_R-m_R`, not an unsigned per-block envelope and not perpetual
   block-by-block capture.
5. **Respect the target scale.**  Stronger-than-RH statements may be useful as
   diagnostics or conditional lemmas, but they are not proof obligations.
6. **Finite computation is diagnostic only.**  Numerical persistence, however
   striking, cannot replace a uniform all-scale theorem.

## Preserved alternative: CORR-4

**The CORR-4 quantitative estimate remains open.** The forward
Mertens-to-RH implication, signed reassembly, and conditional terminal induction
are available. Repeating the existing coordinate changes does not supply the
missing estimate. The pause on repeating tested internal identity searches is
a research policy, not a theorem that the reduced estimates are unprovable.
Coefficient-transfer improvements and new quantitative arguments must be
assessed on their mathematical content.

## Governing rule

**Signed physical reassembly first. Energy second.**

Preserve parent/current-response/first-power-mate compensation, earlier-owner
transfer, second-contact transport, and endpoint terms before squaring. The
energy of a complete signed Mertens packet is different from the sum of squares
of unsummed coefficients.

## Exact target and conventions

Write `M(y) = sum_{1 <= n <= y} mu(n)`, with `M(0) = 0`. For `R >= 56`:

| Symbol | Definition / Lean object |
| --- | --- |
| `X` | `R² − 1`, `squareRootEndpoint R` |
| `G_R` | `M(X) − M(R − 1)`, `lowOwnerPost789EndpointGapReal R` |
| `corr_R` | `−G_R`, `squareRootCanonicalRoughCorrelation R` |
| `E_R` | `sum_{q odd prime, q² < R} M(floor(X/q²))²`, `canonicalRoughLowQ2DaughterEnergy R` |
| `K` | `LowerMertensCriticalEnvelope R K`: `0 <= K` and `(M(y) − 1)² <= K (y + 1)` for every natural `y < R` |
| `Q_R` | `sum_{q odd prime, q² < R} M(floor(X/q²))/q`, `lowOwnerReciprocalMertensColumnReal R` |
| `D_R` | The nonnegative physical Möbius diagonal, `lowOwnerZeroFrequencyMobiusDiagonal R` |
| `S_R` | `G_R² + 2 Q_R G_R − D_R`, `lowOwnerPost789SignedCrossDiagonalRemainder R` |

Here `X` is always an endpoint; `S_R` names the remainder. Some historical
notes use `X_R` for both, so read their Lean definitions to disambiguate.
The envelope implies `K >= 1` by taking `y = 0`.

The sufficient CORR-4 target is

```text
exists C >= 0, for every R >= 56 and every K,
  LowerMertensCriticalEnvelope R K ->
  G_R² <= 4 E_R + C R² K.
```

The constant is independent of `R` and `K`. The estimate is not proved.

[`CANONICAL_ROUGH_Q2_TAIL_REDUCTION.lean`](research/CANONICAL_ROUGH_Q2_TAIL_REDUCTION.lean)
defines the low-owner energy and bounds the nonrecursive `q² >= R` tail by
`3 R² K`. Thus existence of the fixed-coefficient low-owner bound is equivalent
to existence of the full odd-owner bound, with only the boundary constant
changed. [`CORRELATION_FOUR_TERMINAL_BRIDGE.lean`](research/CORRELATION_FOUR_TERMINAL_BRIDGE.lean)
proves `correlationFour_iff_exists_lowQ2Energy` and
`riemannHypothesis_of_canonicalRoughCorrelationFourQ2Energy`. Its resulting
coefficient `10201/2500` passes the compiled terminal budget. No further
bookkeeping assumption or new induction theorem is needed by that consumer.

## Signed normal forms and sufficient coefficients

The compiled quarter frame and diagonal bounds give

```text
Q_R² <= E_R/4,                    0 <= D_R <= 3 R²,
FinalStokes_R = Q_R² + S_R,
TopTwoClip_R = Q_R² + S_R − Terminal_R.
```

The terminal term stays separate; it does not replace `S_R`. The [completed
branch assembly](research/GLOBAL_RETURNED_CORE_TOP_TWO_COMPLETED_BRANCH_ASSEMBLY.lean)
and [branch-gate composition](research/GLOBAL_RETURNED_CORE_TOP_TWO_BRANCH_GATE_COMPOSITION.lean)
prove these identities. At first owner `2`, the completed top-branch energy
is `(Q_R + G_R)²`, so completing the branch has not removed the endpoint gap.

The [sharpened correlation comparison](research/GLOBAL_RETURNED_CORE_POST789_CORRELATION_EQUIVALENCE.lean)
uses a three-quarter square completion. With `C >= 0` and exactly the same
uniform lower-envelope quantifiers, the sufficient endpoint coefficients are:

| Sufficient input | Endpoint coefficient | Sharpened transfer to CORR |
| --- | --- | --- |
| `FinalStokes_R <= B E_R + C R² K` | `B = 9/4` | `4B/3 + 1 = 4` |
| `S_R <= A E_R + C R² K` | `A = 2` | `4(A+1)/3 = 4` |

In either case the low-owner CORR boundary constant becomes `4C/3 + 4`.
Any smaller coefficient also suffices by `E_R >= 0`. These are sufficient
thresholds for the displayed comparisons, not a claim that no other method
could allow larger coefficients. The old `B <= 7/4` and `A <= 3/2` consumers
in the [post-789 control module](research/GLOBAL_RETURNED_CORE_POST789_DIAGONAL_SUBTRACTED_CONTROL.lean)
remain valid and unchanged; they are not the strongest sufficient targets now
available. Historical snapshots that quote them should be read accordingly.

The exact certificates, writing `F = FinalStokes_R`, are

```text
S_R − (3G_R²/4 − E_R − 3R²)
  = (G_R + 4Q_R)²/4 + (E_R − 4Q_R²) + (3R² − D_R),
4F − 3G_R² + 3E_R + 4D_R
  = (G_R + 4Q_R)² + 3(E_R − 4Q_R²).
```

All terms on the right are nonnegative. Consequently

```text
3G_R²/4 − E_R − 3R² <= S_R,
3G_R²/4 − 3E_R/4 − 3R² <= FinalStokes_R.
```

The comparison module contains both polynomial certificates, both lower
comparisons, both general coefficient transfers, and conditional CORR-4/RH
consumers at `A = 2` and `B = 9/4`. The uniform upper bounds are still explicit
hypotheses. Relevant hosted Lean checks at the PR head certify elaboration;
symbolic checks alone are not Lean certification. See the
[research-state note](research/POST789_SHARPENED_COEFFICIENT_CORRIDOR.md)
for the derivation, exact quantifiers, and two-sided research interpretation.

Full quarter cancellation is stronger than required. The original comparison
also proves

```text
G_R²/2 − E_R/2 − 3 R² <= S_R,
S_R <= (1+a) G_R² + b E_R       (a > 0, 4ab = 1).
```

Existence of some remainder bound is equivalent to existence of some CORR-low
bound. This statement does not preserve an arbitrary fixed coefficient and
does not say that every finite coefficient closes RH. The displayed consumer
thresholds must still be met.

## What the latest work does and does not prove

- **Prefix-tail mixed remainder (2026-09-29):** the far-tail/mixed cell
  mass left after the reciprocal prefix is
  [exactly](research/GLOBAL_RETURNED_CORE_PREFIX_TAIL_MIXED_REMAINDER_IDENTITY.lean)
  `2·Mixed_R = S_R + D_P` with `0 <= D_P <= 3 R²`. A mixed bound with
  coefficient `B` is therefore an `S_R` bound with the same `B`. Coefficient
  `2` already closes the consumer, and the remainder is not a narrower seam
  than `S_R`.
- **Owner-two clipped exit (2026-09-29):** at first owner `2` there is a
  single compensated cell, and
  [its exact evaluation](research/GLOBAL_RETURNED_CORE_OWNER_TWO_CLIPPED_EXIT.lean)
  gives clipped exit `= M(X_R)` and compensated interior `= Q_R − M(R−1)`.
  The interior satisfies `I² <= 4 E_R + 8 R² K` unconditionally, and
  `SquareEndpointRoundedOddQ2EnergyStep C` is literally a bound on the
  clipped-exit square. A
  [companion module](research/SQUARE_ENDPOINT_STEP_POLYLOG_STRENGTH.lean)
  proves that the step forces `(M(x)−1)² <= B^j (x+1)` for `x < 2^(2^j)`, a
  polylogarithmic Mertens envelope. See the
  [audit note](research/OWNER_TWO_CLIPPED_EXIT_AUDIT.md). Neither module
  proves the step.
- **Coefficient sharpening (2026-09-27):** the same exact signed carrier and
  quarter frame admit `A = 2` or `B = 9/4`, rather than only `3/2` or `7/4`.
  This improves the sufficient coefficient budget. It does not prove the
  required uniform arithmetic upper estimate or a converse from RH.
- **#797:** the top-two clip retains the whole signed cell below the top two
  owners. A top-two estimate forces a bound on the endpoint gap. Discarding
  the branch slack loses the cancellation one needs to estimate.
- **Unconditional finite baseline (2026-09-27):** the same
  [global-bound module](research/GLOBAL_RETURNED_CORE_POST789_UNCONDITIONAL_GLOBAL_BOUND.lean)
  now kernel-proves the elementary all-scale estimate
  `S_R <= E_R/4 + 8 R^4` for every `R >= 56`.  This uses only
  `|M(n)| <= n`, the exact correlation dictionary, and the compiled Young
  comparison.  It is the first explicit polynomial rung in the tightening
  ladder; it is not yet a bound of the target form `A E_R + C R^2 K` because
  the quartic surplus cannot be absorbed by a fixed root-scale constant.
- **#798:** the stronger asymptotic unconditional bound gives
  `S_R <= E_R/4 + 4 B(X)² + 4 B(R−1)²`, with
  `B(x) = C x exp(−c (log x)^(1/10))`. Its leading envelope is of order
  `R⁴ exp(−c' (log R)^(1/10))`, still above the required `R² K` scale.
- **#799:** [Möbius inversion](research/MOBIUS_INVERSION_GLOBAL_CANCELLATION.lean)
  proves `sum_{d<=X} M(floor(X/d)) = 1` for `X >= 1`, and
  `bornSmooth + farSurvivor = M(X) + E_root` with an explicit root strip.
  The root strip uses lower arguments; that fact alone is not a bound on its
  aggregate size. The top Mertens value remains.
- **#800:** the [K₂ closeout](research/K2_COHERENT_MODE_KILL_GATE.md) separates
  the compiled summatory/PNT comparison from a classical Dirichlet-series
  calculation and a finite regression. Its corrected signed series is
  `2 (zeta'/zeta)² − zeta''/zeta`, retaining double poles at zeta zeros.

Finite examples can falsify a proposed identity or reproduce these exact
relations. A negative remainder on all tested roots, or strong cancellation
between large terms, cannot certify a constant uniform over all roots.
A finite certificate plus a proved all-scale induction can certify such a
bound; a finite list of successful evaluations alone cannot.

Failure of one sufficient bound is not a disproof of RH. A reverse implication
must first be proved for that same statement and its exact quantifiers.
Neither the source audits nor the research pause establish impossibility of
proving the remaining estimates.

## Existing forward analytic bridge

[`MertensEnergyRHForward.lean`](RHLean/Analysis/MertensEnergyRHForward.lean)
proves `riemannHypothesis_of_mertensEnergy` from
`MertensEnergyBoundedStatement`. The latter is the all-epsilon bound
`|M(x)|² <= C_epsilon (x+1)^(1+epsilon)`.
[`TerminalMertensForward.lean`](RHLean/Proof/TerminalMertensForward.lean)
constructs `mertensForwardCriterion` and the square-prefix-to-RH implication.
These forward consumers do not take `ClassicalMertensRHCriterion` as an
external argument. Historical equivalences still do; the reverse implication
is not needed for the present proof route. An implication from an unproved
energy estimate is not a proof of RH.

## Regression constraints retained from earlier contracts

1. A periodic contact mask is not a periodic physical Möbius field.
2. [Coefficient energy is not recursive Mertens energy](RHLean/Proof/ExceptionalContactFrameEnergyNoGo.lean):
   at daughter cutoff two, Mertens energy vanishes while coefficient mass is
   positive. Sum with signs first.
3. [Selected prime-11 tensors are not the true Möbius tensor](RHLean/Analysis/PhysicalRecoveredPrimeTensorCompatibility.lean).
   The abstract `19/23` factor cannot be substituted without the physical
   compatibility theorem that the executable counterexamples rule out.
4. [Go daughters require high transport](RHLean/Proof/TwoWheelQ2GoCompatibility.lean):
   `M(X/q²) = Go_q(X) − highTransport_q(X)`.
5. [Whole physical daughters are already reassembled](RHLean/Proof/PhysicalQ2BookkeepingSynthesis.lean):
   `physicalReassembledQ2Daughter K q = M(4K/q²)` for odd prime owners.
   Prime `2` belongs to the base mod-four geometry, not the odd contact schedule.
6. A bounded endpoint may be used only after an exact theorem attaches it to
   the same parent decomposition. No replacement by a similarly named object.
7. Support counts, coefficient norms, positive ownerwise energy, the prime-11
   budget, and a coordinate change do not supply the open signed estimate.
8. [The compensated interior is not the seam](research/GLOBAL_RETURNED_CORE_OWNER_TWO_CLIPPED_EXIT.lean):
   at owner `2` the clipped exit is exactly `M(X_R)`. A bound on the
   reassembled interior is already unconditional and cannot close CORR-4.

## Preservation and success conditions

Preserve all obstruction modules, exact reassembly theorems, root/export
manifests, declaration-graph checks, owned-warning gates, and terminal axiom
checks. Do not add unfinished proofs, new analytic axioms, independence
assumptions, or a renamed RH-strength hypothesis.

A new route must identify the quantitative ingredient, its exact carrier and
quantifiers, and the compiled consumer it meets. Success means proving a
sufficient uniform estimate and composing it with that consumer without a new
open premise. The present coefficient sharpening makes no such closure claim.

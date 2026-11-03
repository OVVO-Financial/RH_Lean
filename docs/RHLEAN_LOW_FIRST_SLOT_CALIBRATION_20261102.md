# LOW-first, source-calibrated contraction

## Status

This focused extension is based on the verified PR #1073 head
`9cbfce5295343bcb411e6d2cb159b59995cd985b`. New claims require the dedicated
exact-head kernel run and live endpoint audits. At authoring, the new modules
are unverified; no successful compilation is inferred from the paper ledger.
Independent mathematical review and human merge remain separate requirements.

## Tighten one component

Keep the finite positive slot family and write `m=(7/8)*D.rmin`.
The complete LOW theorem `SourceData.tiltedProbe_low` accepts the non-strict
charge `24*tilt <= m`. Therefore select

    delta = m/24 = 7*D.rmin/192 > 0,

rather than the earlier draft's `m/48` or the first source choice `D.e/48`.
This saturates the available sufficient gate; it is not a claim of optimality
for the underlying arithmetic.

From the actual source fields, `m <= D.t/200` and `0<D.t<=10^-8`. Thus
`24*delta=m<D.t` and `delta<1/960`. The complete LOW consumer gives, for every
positive loss omega, the same physical normalized probe bound

    P_delta = O(Z^(3/16 - 9*delta + omega)).

Its unchanged residue normalization has shift

    c = -11/16 - 8*delta.

Consequently the LOW crossing is exactly `7/8-delta`.

## Preserve rather than improve the original HIGH arithmetic

Use the already-proved `beta<=7/8` as a contour reference. The small-row contour
is `7/8+8*e`, and the principal contour is `7/8+e`; both lie in the domains of
the original estimates and to the right of the actual supremum. The actual
supremum is not changed, and the old strict-gap endpoint is not a supplier.

Set `sigma=m/4=6*delta`, keeping slots and detector parameters fixed after the
existing final-allowance cap. The constructor checks every sigma-dependent
HighData field. The complete anchored HIGH comparison has exponent

    7/8 + c - sigma.

The floor and nonfloor comparisons are now against this fixed proved reference.
The same ideal coefficients, phases, slot weights, exclusions, finite source,
normalizer and exact physical partitions are retained.

The independent arithmetic Delta is `10^-6`. The central payment is

    10^-6 + sigma + t/4 <= 49/881280.

Using `sigma<=t/800` and `t<=10^-8` leaves the positive exact reserve
`6014563223/110160000000000`.

## Complete consumer

Suppose the true supremum is above theta=`7/8-delta`, and use
omega=`(beta-theta)/2`. The known `beta<=7/8` implies `0<omega<delta`.
LOW and HIGH bound the same signal to the right of

    max(theta+omega, 7/8-sigma) = theta+omega < beta.

The actual correction is analytic and within 1/2 of one on Re(s)>21/25;
theta remains to the right of that line. A primitive zero near the true
supremum, preserved by finite prime deletion, contradicts the existing
variable-boundary continuation theorem. The constructor supplies all source
parameters before the character, scale, arbitrary LOW loss and selected zero.

The endpoint is a source-calibrated assertion

    exists D, 0<slotTilt D and beta<=7/8-slotTilt D,
    where slotTilt D=((7/8)*D.rmin)/24.

The exact native converse then yields MertensGrowthAtMost at that exponent,
a fixed power envelope after spending half the gap, and the complete signed-pair
inequality with its actual squarefree diagonal retained. No short-shell sum of
squares or RH conclusion is inferred from the all-prefix bound.

## One-component improvement ledger

For physical scale exponents x,y and a further proved LOW row-energy saving
`gamma`, the algebraic crossing is

    (5*x+y)/12-gamma/2 - (x/3-5/6+1/36)
      = 7/8 - (5/6-(x+y))/12 - gamma/2.

This identity does not assert such a gamma. For two completed amplitude bounds
with gains L and H relative to a common reference b, their complete comparison
retains `max(b-L,b-H)=b-min(L,H)`. A LOW-only improvement therefore passes in full
until the already-proved HIGH reserve becomes limiting. The new choice uses
L=delta and H=sigma=6*delta; no new independent HIGH cancellation is assumed.

## Reproduction and proof integrity

`prepare_anchored.py` reads original files only after byte equality with the
pinned Git objects is checked. It writes fresh suffixed declarations, replacing
only the contour/reference coordinate in those copies and explicitly providing
the true zero-free premises from the non-strict native replay. The original
files are never overwritten. All generated full Lean sources and provenance
are archived by the dedicated shared-cache workflow.

The kernel compiles every original baseline module and new module with warnings
as errors. The runtime audit checks the complete endpoint type against the
literal delta `((7/8)*D.rmin)/24`, permits only propext/Classical.choice/Quot.sound,
requires the actual new LOW/HIGH and native moment suppliers in live proof
values, and rejects the previous strict-gap shortcuts. Static source generation
or rational checks are never treated as a substitute for this kernel run.

## Integration after #1075 merged into the target branch

The earlier `m/48` construction from PR #1075 remains in its original
`VF919PhysicalTiltFullBudget`, `VF919SlotCalibratedData`, and
`VF919SlotAnchoredEndpoint` modules, with its original audit and workflow.
The LOW-first `m/24` variant from PR #1076 is now in distinct
`VF919LowFirst*` modules with `_low_first` theorem names, preserving its
separate exact-type and live-dependency audits. The original pinned-source
HIGH generator is unchanged. This namespace separation is an integration
operation only; the new merged head must pass CI before acceptance.

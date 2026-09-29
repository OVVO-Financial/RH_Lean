# Owner-two clipped exit audit

Status: 2026-09-29. Lean sources:
[`GLOBAL_RETURNED_CORE_OWNER_TWO_CLIPPED_EXIT.lean`](GLOBAL_RETURNED_CORE_OWNER_TWO_CLIPPED_EXIT.lean)
and [`SQUARE_ENDPOINT_STEP_POLYLOG_STRENGTH.lean`](SQUARE_ENDPOINT_STEP_POLYLOG_STRENGTH.lean),
checked by `.github/workflows/owner-two-clipped-exit.yml`. Compiled source
is authoritative; this note only explains it.

## Question

The compensated owner block
([`GLOBAL_RETURNED_CORE_COMPENSATED_OWNER_BLOCK.lean`](GLOBAL_RETURNED_CORE_COMPENSATED_OWNER_BLOCK.lean))
proves, for each owner `p` and lower-signature cell `sig`,

```text
Base(p,sig) + Child(p,sig) = CompensatedInterior(p,sig) + ClippedExit(p,sig),
CompensatedInterior = sum_admitted (DaughterCrossing(a) - RootCrossing(a)) mu(a).
```

The proposed attack was to reassemble the compensated interior globally with
signs, square it, and prove `I_R^2 <= 4 E_R + C R^2 K`, leaving only literal
wall/escape terms to pay `C R^2 K`.

## Result: the whole top value is the clipped exit

No prime lies below `2`, so at owner `p = 2` the lower signature is always
empty. There is exactly one owner-two cell, and it is already global. On it:

| Object | Exact value (Lean) |
| --- | --- |
| `ClippedExit(R,2,∅)` | `M(X_R)` — `lowOwnerFirstOwnerClippedAmplitude_two_eq_topMertens` |
| `CompensatedInterior(R,2,∅)` | `Q_R − M(R−1)` — `lowOwnerFirstOwnerCompensatedInteriorAmplitude_two_eq` |
| `Base + Child` | `A_R = Q_R + G_R` — `lowOwnerFirstOwnerBase_add_child_two_eq_amplitude` |

Both follow from one elementary identity, proved for every prime `p`
(`sum_Icc_pFree_clipped_realMoebiusStep_eq_mertens`):

```text
M(Y) = sum_{1 <= a <= Y, p ∤ a, Y < p a} mu(a).
```

Every p-free site past the owner-two clip `X_R < 2a` has AMP weight exactly one:
it is at least `R`, and it lies beyond every odd `q^2` daughter cutoff
`X_R/q^2 <= X_R/9`.

Consequences, all kernel-checked in the same module:

1. `SquareEndpointRoundedOddQ2EnergyStep C` is, with the same constant,
   exactly a recurrence for `ClippedExit(R,2,∅)^2`
   (`squareEndpointRoundedOddQ2EnergyStep_iff_ownerTwoClippedExit`).
2. The globally reassembled interior satisfies the proposed target
   unconditionally:
   `I_R^2 <= E_R/2 + 8 R K <= 4 E_R + 8 R^2 K` for all `R >= 2` and every
   admissible envelope (`ownerTwoCompensatedInterior_fourEnergyBound_unconditional`).
   It uses only the quarter frame `Q_R^2 <= E_R/4` and the envelope at
   `y = R − 1`.

Since the interior bound is already a theorem, it cannot be the missing
ingredient. Summing with signs before squaring puts no top-scale mass in the
interior. The endpoint value `M(X_R)` sits entirely in the clipped exit.

### Numerical filter at other small owners

For `p ∈ {3, 5, 7}` and `12 <= R <= 119` (plus `R = 199, 256, 313, 399`),
summing the cells over all lower signatures gives exactly the same split:
clipped exit `= M(X_R)` and interior `= Q_R − M(R−1)`. For `p >= 11` the
clipped exit is `M(X_R)` plus daughter-window corrections for the owners with
`q^2 < p`. This is a finite check. Only the `p = 2` statement is formalized.

## Reading of the three proposed tightenings

1. **Exact signed reciprocal synthesis inside the interior.** At owner two
   this is already exact. The daughter crossings synthesize to `Q_R`, which is
   bounded by `E_R/4`, and the root crossings give `M(R−1)`. The result is
   bounded, and it does not reach `M(X_R)`.
2. **Separate the stable interior from literal wall escapes.** The literal
   owner-two escape is `M(X_R)` itself. Asking it to pay `C R^2 K` restates the
   open recurrence.
3. **#802 after reciprocal entry.** This addresses boundary terms. At owner
   two the boundary term is the whole open quantity, so it is not cleanup.

Sharpening coefficient-L2 majorants such as `X/4 + 4R` cannot help either.
Those are unsigned bounds on per-site coefficients. The quantity to control is
one signed endpoint sum.

## Strength of the remaining step

`SQUARE_ENDPOINT_STEP_POLYLOG_STRENGTH.lean` iterates the compiled
step-to-amplification closure with no epsilon loss:

* `lowerMertensCriticalEnvelope_sq_of_amplification`: with fixed endpoint
  amplification constant `A`, an envelope `K` at root `R` gives `(2A+8) K` at
  root `R^2`;
* `squareEndpointRoundedOddQ2EnergyStep_forces_polylogMertensEnvelope`: the
  step yields `B >= 1` with `(M(x)−1)^2 <= B^j (x+1)` whenever `x < 2^(2^j)`.

With the least such `j`, this is `M(x) = O(x^{1/2} (log x)^c)`. That is a
polylogarithmic Mertens bound. It implies RH, and it is stronger than the
bounds known to follow from RH. Those bounds are of the shape
`x^{1/2} exp((log x)^{1/2} (log log x)^c)` (Soundararajan; later
improvements). The literature comparison is commentary, not formalized. The
implication itself is kernel-checked.

So the "one remaining inequality" is not a bookkeeping estimate. It is a
statement at least as strong as a polylogarithmic Mertens bound.

## Finite diagnostics

For `56 <= R <= 3000`, the smallest constant that makes the packaged step hold
on that range is about `0.11` (worst at `R = 548`). In that range the envelope
is `K* = 1.5`, set by tiny `y`. As the proof contract says, finite evaluations
cannot certify a uniform constant. The step is hard only asymptotically.

## What a new route must supply

Any route through the compensated owner block must bound the owner-two clipped
exit. That exit is literally `M(R^2 − 1)`, and the bound must be in terms of the
envelope at roots below `R` plus the odd `q^2` daughters. Coordinate changes
inside the interior, cellwise squaring, and coefficient-L2 majorants cannot
supply it.

# Dynamic-denominator Viole baseline

## Status

The repository previously contained only the generic arbitrary-baseline interface in
`RHLean/Proof/SquareBlockTransportBaseline.lean`. It did **not** contain a concrete
formalization of the original Viole function, so no Lean theorem was deleted or
silently replaced.

`RHLean/Analysis/DynamicVioleBaseline.lean` now supplies the canonical concrete VF
specialization used by the latest experiment.

## Definition

At the square-block midpoint

```text
xi_r = r^2 + r + 1/2,
L = log xi_r,
```

the fitted effective logarithmic-base exponent is

```text
s(x) = log b(x)
     = 2 + 22.407744267407335 / log x
         - 152.12857519277964 / (log x)^2.
```

The dynamic correction is

```text
G(x) = (1 + L / s(x)) log(1 + s(x) / L),
```

and the square-block anchor is

```text
VF_dyn(r) = r^2 / (log(r^2) - G(xi_r)).
```

The cumulative baseline is the piecewise-linear interpolant through the anchors
`(xi_r, VF_dyn(r))`.

The full fitted decimals from the experiment summary are represented in Lean as exact
rational numbers. Their empirical origin is not promoted to a theorem.

## Empirical protocol

Exact prime counts were sieved through `10^7`. The coefficients were fitted only on
square-block midpoints from `10^3` through `10^5`, frozen, and then tested on later
decades.

Midpoint RMSE:

| Range | Li | Original VF base 10 | Dynamic VF |
|---|---:|---:|---:|
| `10^5`–`10^6` | 73.384 | 54.526 | **13.863** |
| `10^6`–`10^7` | 183.009 | 255.406 | **119.786** |

The exact-activity sign-blind interval energy ratio `dynamic VF / Li` ranged from
approximately `0.446` at `N=1000` to `0.547` at `N=50000`.

The Möbius-signed aggregate energy was nearly unchanged. Consequently the current
interpretation is deliberately limited:

- dynamic VF is a materially better deterministic square-block baseline;
- it removes a substantial rowwise interval bias relative to Li;
- it does not by itself remove the signed RH-hard residual.

The phrase “Möbius high-pass filter” is useful empirical shorthand, but it is not an
unconditional square-root-cancellation theorem: a general estimate of size
`O(C^(1/2+epsilon))` for a smooth Möbius-weighted sum would itself be RH-strength.

## Logical boundary

Lean proves only:

1. the exact deterministic formula;
2. its local midpoint-segment interpolation identities;
3. its exact specialization of the generic square-block baseline decomposition.

Lean does not assert that dynamic VF approximates `pi`, outperforms `li`, satisfies a
prime-number-theorem error bound, or implies RH.

# Square-index dynamic-denominator Viole baseline

## Status

`RHLean/Analysis/DynamicVioleBaseline.lean` now uses the square-block index `r`
inside the Euler convergence correction. This is the principled architecture
for an effective logarithmic base asymptotic to `e`.

The main denominator retains `log(r^2)`, but the convergence factor uses
`log_b(r)`, not `log_b(x)` with `x approximately r^2`.

## Definition

At square-block index `r`, let

```text
R = log r,
s(r) = log b(r)
     = 1 + 5.5872416013500885 / log r
         - 18.957724430717928 / (log r)^2.
```

Hence

```text
s(r) -> 1,
b(r) = exp(s(r)) -> e.
```

The correction is

```text
G(r) = (1 + R / s(r)) log(1 + s(r) / R),
```

and the square-block anchor is

```text
VF_dyn(r) = r^2 / (log(r^2) - G(r)).
```

The cumulative baseline is the piecewise-linear interpolant through
`(r^2 + r + 1/2, VF_dyn(r))`.

## Empirical protocol

The coefficients were fitted only on square-block midpoints from `10^3`
through `10^5`, frozen, and tested with exact prime counts through `10^8`.

Midpoint RMSE:

| Range | Li | Square-index dynamic VF | VF / Li |
|---|---:|---:|---:|
| `10^3`–`10^5` | 27.920 | **3.879** | 0.139 |
| `10^5`–`10^6` | 73.384 | **13.755** | 0.187 |
| `10^6`–`10^7` | 183.009 | **118.549** | 0.648 |
| `10^7`–`10^8` | **485.667** | 1066.307 | 2.196 |

Pointwise square-block-midpoint win rate against Li:

| Range | Square-index dynamic VF |
|---|---:|
| `10^3`–`10^5` | 100.000% |
| `10^5`–`10^6` | 100.000% |
| `10^6`–`10^7` | 100.000% |
| `10^7`–`10^8` | 6.405% |

## Interpretation

The square-index correction is the mathematically coherent way to obtain
`b(r) -> e`. However, the frozen two-term fit does not remain superior to Li
through `10^8`; it loses decisively on `10^7`–`10^8`.

This separates two questions:

1. the correct variable and asymptotic base;
2. the finite-dimensional approximation used for the dynamic optimum.

The first is now correct: use `log_b(r)` and obtain base `e` asymptotically.
The second remains open: the two-term model

```text
1 + a/log r + b/(log r)^2
```

does not accurately track the exact optimum far enough out.

A next experiment should compute the exact optimum `s_*(r)` block by block by
inverting the monotone correction map, then study its asymptotic expansion
before imposing a low-order parametric form.

## Logical boundary

Lean proves only the exact deterministic formula, interpolation identities,
and specialization of the generic square-block baseline decomposition. It does
not prove a prime-counting error bound, superiority over Li, or RH.

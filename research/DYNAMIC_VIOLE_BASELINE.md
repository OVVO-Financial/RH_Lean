# Corrected dynamic-denominator Viole baseline

## Status

`RHLean/Analysis/DynamicVioleBaseline.lean` now formalizes the corrected dynamic
Viole specialization whose effective logarithmic base tends to `e`.

The previous experiment used

```text
log b(x) = 2 + a / log x + b / (log x)^2,
```

which unintentionally forced `b(x) -> e^2`. That implementation has been
replaced. The compatibility entrypoint `experiments/vf_dynamic_test.py` now
runs `experiments/vf_dynamic_e_asymptote_test.py`.

## Corrected definition

At the square-block midpoint

```text
xi_r = r^2 + r + 1/2,
L = log xi_r,
```

the fitted effective logarithmic-base exponent is

```text
s(x) = log b(x)
     = 1 + 40.64408021414064 / log x
         - 233.433772115277 / (log x)^2.
```

Therefore

```text
s(x) -> 1
b(x) = exp(s(x)) -> e.
```

The dynamic correction is

```text
G(x) = (1 + L / s(x)) log(1 + s(x) / L),
```

and the square-block anchor is

```text
VF_dyn(r) = r^2 / (log(r^2) - G(xi_r)).
```

The cumulative baseline remains the piecewise-linear interpolant through the
anchors `(xi_r, VF_dyn(r))`.

The fitted decimals are represented in Lean as exact rational numbers. Their
empirical origin is not promoted to a theorem.

## Empirical protocol

The two coefficients were fitted only on square-block midpoints from `10^3`
through `10^5`, frozen, and then tested with exact prime counts through `10^8`.

Midpoint RMSE:

| Range | Li | Corrected dynamic VF | VF / Li |
|---|---:|---:|---:|
| `10^3`–`10^5` | 27.920 | **3.927** | 0.141 |
| `10^5`–`10^6` | 73.384 | **11.187** | 0.152 |
| `10^6`–`10^7` | 183.009 | **29.311** | 0.160 |
| `10^7`–`10^8` | 485.667 | **99.225** | 0.204 |

Pointwise square-block-midpoint win rate against Li:

| Range | Corrected dynamic VF |
|---|---:|
| `10^3`–`10^5` | 100.000% |
| `10^5`–`10^6` | 100.000% |
| `10^6`–`10^7` | 100.000% |
| `10^7`–`10^8` | 99.825% |

The corrected function therefore remains materially better than Li throughout
the tested range, including the fully out-of-sample decade `10^7`–`10^8`.
This is an empirical finite-range result, not an asymptotic theorem.

## Interpretation

The corrected asymptote changes the conclusion of the previous experiment.
The apparent deterioration after `10^7` was caused by convergence toward the
wrong base `e^2`, not by failure of the intended dynamic Viole architecture.

The current interpretation is deliberately limited:

- corrected dynamic VF is a materially better deterministic square-block
  midpoint baseline through `10^8`;
- the fitted effective base remains dynamic in `x` while tending to `e`;
- no claim is made that VF is closer at every real or integer input;
- no uniform or asymptotic error bound has been proved;
- improved prime-counting baseline accuracy does not by itself remove the
  Möbius-signed RH-hard residual.

## Logical boundary

Lean proves only:

1. the exact corrected deterministic formula;
2. its local midpoint-segment interpolation identities;
3. its exact specialization of the generic square-block baseline decomposition.

Lean does not assert that corrected dynamic VF approximates `pi`, outperforms
`li`, satisfies a prime-number-theorem error bound, or implies RH.

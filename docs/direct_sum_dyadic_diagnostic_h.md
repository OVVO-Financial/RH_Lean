# Diagnostic H: direct-sum dyadic dispersion scan

This note records the finite diagnostic behind the direct-sum dyadic FAR-4 bridge in PR #695. It is empirical only; it does not prove any asymptotic bound.

## Quantity scanned

For each integer root `R` define

```text
eta_R = |W_H(R) + W_L(R)|^2 / (E_H(R) + E_L(R)),
```

where `W_H,E_H` are the reciprocal high-channel wavelet and Abel-potential energy, and `W_L,E_L` are the freshness-restricted low-channel wavelet and its direct-sum Abel-potential energy.

The scan keeps the scalar numerator coupled before squaring and keeps the coefficient energy as the honest direct sum. The high and low potential lattices are not artificially identified.

## Full integer scan through R = 100000

Every integer `56 <= R <= 100000` was evaluated. The finite support/census is exact; the logarithmic-integral part is evaluated in double precision with a blockwise numerical Li table. The implementation reproduces the previously checked roots, including the `R = 3588`, `4000`, `5000`, and `23064` values, to the displayed precision relevant to the diagnostic.

The largest value remains the Diagnostic G spike:

```text
R       = 23064
eta_R   = 232.631026680689
W_H     = -5205.18162683305
W_L     = -15247.17453660598
E_H     = 1479226.201897613
E_L     = 318895.3926492874
W_L^2/E_L = 729.004986300937
W_H^2/E_H = 18.3162762622533
K_min(R)   = 1.5
```

No larger `eta_R` occurs for `23065 <= R <= 100000`.

## Running-max exponent

For the running maximum

```text
eta_max(R0) = max_{56 <= R <= R0} eta_R
```

define the finite-scale exponent

```text
delta(R0) = log(eta_max(R0)) / log(R0^2 - 1).
```

Selected values are:

| R0 | eta_max(R0) | attained at | delta(R0) | eta_max/(log R0)^2 |
|---:|---:|---:|---:|---:|
| 23064 | 232.6310267 | 23064 | 0.2712243 | 2.30504 |
| 30000 | 232.6310267 | 23064 | 0.2643069 | 2.18896 |
| 40000 | 232.6310267 | 23064 | 0.2571313 | 2.07172 |
| 50000 | 232.6310267 | 23064 | 0.2518283 | 1.98715 |
| 60000 | 232.6310267 | 23064 | 0.2476552 | 1.92184 |
| 75000 | 232.6310267 | 23064 | 0.2427321 | 1.84619 |
| 100000 | 232.6310267 | 23064 | 0.2366668 | 1.75508 |

The earlier estimate `delta(23064) approx 0.054` was arithmetic error: with `log eta approx 5.45` and `log X_R approx 20.09`, the ratio is about `0.271`, independent of logarithm base.

The running exponent decreases monotonically after the `R = 23064` record because the record is not surpassed through `R = 100000`. This is consistent with subpower growth, but a finite scan cannot establish an `X^epsilon` bound for arbitrarily small epsilon.

## Distribution through 100000

Across all 99,945 scanned roots:

```text
median  = 11.2449
mean    = 20.7167
p90     = 51.7508
p95     = 70.7687
p99     = 140.0004
p99.9   = 185.9726
maximum = 232.6310
```

`K_min(R)` is identically `3/2` throughout the scan, so ordinary correlation with `eta_R` is undefined (zero variance in the envelope).

## Interpretation

The scan does not falsify the direct-sum `X^epsilon` dispersion target. After the low-channel resonance near `R = 23064`, the running maximum remains flat for more than 76,000 consecutive roots and the finite-scale exponent decreases from about `0.2712` to `0.2367` by `R = 100000`.

It also does not justify a fixed small polylogarithmic constant. The previous empirical bound `eta <= 1.2 (log R)^2` is false. More precisely, the scan falsifies that constant-1.2 envelope; it does not by itself falsify the asymptotic class `O((log R)^2)`, since the largest observed normalized value is about `2.305` and then decreases when normalized at later scan endpoints.

The low freshness channel remains the dominant source of the largest excursion. Therefore PR #695 deliberately leaves the fixed-scale absorption as the separate open proposition `DirectSumDyadicFarFourBudgetStatement`; no dispersion estimate or FAR-4 budget estimate is inferred from this diagnostic.

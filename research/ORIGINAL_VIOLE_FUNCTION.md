# Original parameter-free Viole Function

## Published definition

For real `x`, define

```text
N(x) = floor(sqrt(x))^2,
t(x) = log_10(x),
C(x) = (1 + 1/t(x))^(1 + t(x)).
```

The continuous core of the published Viole Function is

```text
VF_cont(x) = N(x) / log(N(x)/C(x)).
```

The R implementation returns

```text
max(0, floor(VF_cont(x))).
```

This construction is parameter-free. It contains no calibrated coefficients
and does not evaluate `pi(x)`.

## What is dynamic

The dynamic term is

```text
C(x) = (1 + 1/log_10(x))^(1 + log_10(x)).
```

It changes analytically with every input `x`. The `base = exp(1)` argument in
the original R code only instructs R to use the natural logarithm in the
outer denominator; it is not the dynamic base itself.

## Implied logarithmic base

Writing the continuous estimator as

```text
N(x) / log_(b_VF(x))(N(x)),
```

gives the implied log base

```text
log b_VF(x)
  = log N(x) / (log N(x) - log C(x))
  = 1 / (1 - log C(x)/log N(x)).
```

Thus, if

```text
log C(x) / log N(x) -> 0,
```

then

```text
log b_VF(x) -> 1
```

and therefore

```text
b_VF(x) -> e.
```

## Separation from later fitted experiments

The later expression

```text
1 + A/log(x) + B/log(x)^2
```

with fitted constants `A` and `B` is not the original Viole Function. It is a
separate empirical emulator and must not replace or redefine the published
parameter-free VF.

## Lean status

`RHLean/Analysis/OriginalVioleFunction.lean` formalizes:

- the exact square-floor numerator;
- the base-ten Euler correction;
- the original continuous and integer-valued estimators;
- the implied dynamic base;
- positivity of the implied base;
- the final continuous-mapping theorem from correction-ratio convergence to
  convergence of the implied base to `e`.

A subsequent proof layer should discharge the correction-ratio limit directly
from the Euler-sequence limit and growth of the square-floor numerator.

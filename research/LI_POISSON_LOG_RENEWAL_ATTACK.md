# Pure-Li Poisson logarithmic renewal attack

This successor to PR #816 starts from its green head
`852936c63390c88a1abbf820aa04f2016c8e59c4`. The theorem source is
`research/EXACT_LI_PURE_MODEL_CLOSURE.lean`.

The pure-Li uniform bound remains open. No new analytic assumption or
unconditional closure theorem is introduced here.

## Exact signed carrier

Let `P_k` be the Dirichlet product of the Poisson factors at integer sites
2 through k+1. Sites are integers, not actual primes. The Li weight at 2
is zero. Put `D f(n) = log(n) f(n)`. The complex derivation extends the
existing real logarithmic derivation in `LogWeightedPrimeExtensionEndpoint`.

The new finite identities are

```text
D(f * g) = D(f) * g + f * D(g)
D(exp_*(-w_q delta_q)) = (-log(q) w_q delta_q) * exp_*(-w_q delta_q)
D(P_k) = (-sum_{q=2}^{k+1} log(q) w_q delta_q) * P_k.
```

Thus all Poisson multiplicities are combined with their signs before any
norm is taken. No separate collision forcing remains in this identity.

For the stabilized critical reference A(X) and critical coefficients a(n),
the exact floor-quotient renewal is

```text
sum_{n=1}^X log(n) a(n)
  = -sum_{q=2}^X log(q) (w_q / sqrt(q)) A(floor(X/q)).
```

Every child in that sum is positive. The artificial convention A(0)=1
is never substituted for an empty coefficient sum.

## Quantitative new input

For every q >= 3, define

```text
epsilon_q = log(q) w_q - 1.
```

The bin integral and monotonicity of log give

```text
0 <= epsilon_q <= 1 / ((q-1) log(2)).
sum_{q>=3} epsilon_q / sqrt(q) < infinity.
```

The proof uses a q^(-3/2) majorant, independently of any Poisson bound.
The exact critical generator consequently splits into

```text
log(q) w_q / sqrt(q) = 1/sqrt(q) + epsilon_q/sqrt(q).
```

The new child-operator estimate bounds a finite defect response by its
child sup norm times this finite budget. Its child bound is explicit;
it does not assert that the Poisson reference is already bounded.

## What remains

The signed unit-integer floor renewal still needs a uniform stability
estimate strong enough to absorb this summable perturbation. Identifying
that discrete renewal with, or controlling it through, the continuous
Dickman reference remains part of this estimate. The new generator is not
silently identified with a continuous measure.

`allScaleLiSquareRootBounded_of_criticalPoisson_uniform` now connects a
proved uniform bound on the critical Poisson reference directly to the
existing all-scale Li square-root consumer. The uniform bound is still
an explicit premise of that theorem.

## Validation

The existing Prime flip PNT workflow compiles the whole module with
warnings treated as errors. Ten new named theorem axiom checks extend
the existing audit from 25 to 35 declarations and retain the same allowed
axioms: propext, Classical.choice, and Quot.sound.

An independent floating-point reconstruction from the finite Poisson
products checked the logarithmic renewal at X=0,1,2,3,9,64,210,317,1000,5000;
the largest absolute residual was 1.9e-14. At 210 and 317 the critical
cumulatives were approximately -1.092092054907 and -1.113426371077.
The critical defect mass through 5000 was approximately 0.370104019089.
These are sign, scaling, and endpoint diagnostics only, not uniform bounds.

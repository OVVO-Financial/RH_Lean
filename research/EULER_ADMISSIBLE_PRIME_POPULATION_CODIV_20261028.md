# Admissible Euler prime population and weighted signed Co-Div

**2026-10-28. Source-faithful arithmetic, Lean 4.34.1. Stacked on PR #1042.**

## Purpose

Prove the original Euler population statement without replacing admissible prime
products by independent signs or a complete binomial cube. Preserve the sharp
product ceiling X=R^2-1, root-boundary prime p=R, actual prime availability,
signed chronological cross interactions, and the existing Euler floor weight.

This branch is exact arithmetic, not an independent power-saving estimate.

## Exact unweighted arithmetic

For R>=2, X=R^2-1, define E_R to be the signed Mobius population of all
positive integers n<=X whose largest prime factor is <R, including 1.
Define T_R = sum_{R<=p<=X, p prime} M(floor(X/p)).
Let H_R=-T_R and N_R(k)=pi(floor(X/k))-pi(max(R-1,floor(X/(k+1)))).

The exact product-admission laws are

    M(X) = E_R - T_R = E_R + H_R,
    T_R = sum_{k=1}^{R-1} M(k) N_R(k).

The p=R contribution is exactly M(R-1) if R is prime. It is not included
in the existing p>R transport. At the prime-admission level,

    E_{<=p}(X)-E_{<=p-1}(X) = -1_{p prime} M(floor(X/p)).

For all p>=R, the signed scalar energy step is

    |E_{<=p}|^2 - |E_{<=p-1}|^2 =
      |1_{p prime} M(floor(X/p))|^2
        - 2 Re(conj(E_{<=p-1}) * 1_{p prime} M(floor(X/p))).

This signed mixed term is the genuine NNS/owner covariance mechanism.

## Original Euler floor and corner

The certified self-dual source is Q_R=2M(R-1)-M(X). Thus

    Q_R=2M(R-1)-E_R+T_R.

PR #1042 preserves the asymmetric rectangle, original omitted strip and
|corner|<=2R. This module imports that proof and expresses its endpoint in
the same genuine Euler prime population.

The native historical Abel Gram is Q_R=D_R+2B_R. The signed-pair bridge
uses the original weight

    w_R(a,b)=floor(X/(ab))-floor(X/(b^2)), 1<=a<b<R

and defines weighted same-sign Co and opposite-sign Div directly on the
actual Mobius coefficients.

## Exact regression

The script scripts/euler_admissible_population_probe.cpp sieves the original
Mobius coefficients, largest prime factors and true prime-count population.
It checks every square root R=2..10000, and directly checks admitted
prime products and the weighted Gram at R=317,1027,5561,10000.

## Open arithmetic theorem

The required independent estimate remains, for some eta>0,

    |2M(R-1)-E_R+T_R| << R^(7/4-eta+epsilon).

Equivalently the complete weighted Co-Div residual must obey this
power-saving estimate, with the historical diagonal retained. No independent
rate is proved by finite population identities or the numerical census.

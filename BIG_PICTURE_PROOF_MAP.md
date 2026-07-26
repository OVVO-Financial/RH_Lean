# Big-picture proof map

This document is the strategic invariant for every subsequent theorem and pull request in `RH_Lean`.

## 1. The final object is the full signed subtraction

The exact square-block identity is

```text
squareBlockSmoothTransportResidual n
  = squareBlockSmoothPrefix n - squareBlockTransportPrefix n
  = squarePrefixMertens n.
```

The unresolved analytic target is therefore the uniform local energy of the **complete signed residual**, with the smooth energy, transport energy, and their full signed interaction retained. The facts that the smooth population lies below the largest-prime square-root boundary and the transport population lies above it are support statements. They are not, by themselves, bounds for either cumulative amplitude.

Every proposed estimate must identify how it controls the signed residual rather than merely one support set.

## 2. Three compatible routes into the same protected criterion

### Direct smooth/transport route

```text
full signed smooth/transport Gram estimate
  -> SquarePrefixUniformLocalBoundedStatement.
```

This route may exploit cancellation between the two diagonal pieces. Separate diagonal bounds are sufficient but stronger than necessary.

### Canonical low/high route

```text
proved low-height occupancy
  + canonical high-sector local estimate
  -> SquarePrefixUniformLocalBoundedStatement.
```

The low-height contribution is already controlled. The native high-sector estimate remains open.

### Lifetime/death route

```text
active = birth - death
Delta death_t = death-shell Mobius mass
```

The honest endpoint criterion has two obligations:

```text
1. local-energy control of the death process;
2. local-energy control of the survivor discrepancy birth - death.
```

A death-process theorem alone does not close the full residual.

## 3. Current death-shell coordinate

For positive cutoff and nonzero Mobius support, the repository proves the exact finite identity

```text
Delta death_t
  = sum over represented k of N_k(t) * (-1)^(k+1),
```

where `N_k(t)` counts shell sources whose canonical cofactor has `k` distinct prime factors. The class `k = 0` is retained.

This is a cancellation coordinate, not a cancellation estimate. Individual comparisons such as `N_2(t)` versus `N_3(t)` do not replace the complete alternating sum over all represented `k`.

## 4. The Fermat sieve couples source and death coordinates

For an odd prime-cofactor source in exact Fermat coordinates,

```text
q = a + b,
c = a - b,
m = q*c = a^2 - b^2,
height = |q^2 - c^2| = 4*a*b.
```

The complete Fermat tables classify the **source coordinate** `m = a^2 - b^2` modulo `20` through the terminal pair `(a mod 10, b mod 10)`. Because death height is `4*a*b`, those same tables also induce congruence restrictions on the **death coordinate**.

Thus the Fermat sieve is not merely a density filter on an unrelated candidate set. It gives a finite-state coupling between source residue and death position. What it does **not** do automatically is determine the parity of the full prime factorization of the cofactor.

The useful question is therefore not simply how many candidates the sieve removes. It is whether the permitted lanes support an exact or controlled sign-reversing transport.

## 5. The 2ab scale-transfer route

For one canonical source `m=cq`, the source enters at square-root scale and becomes smooth at its largest-prime transition. The normalized `2ab` coordinate determines the exact dilation

```text
lambda = q / sqrt(cq) = sqrt(q/c).
```

Square-root inversion

```text
iota_R(x) = R^2/x
```

is an involution with fixed point `R`, and at `R=sqrt(cq)` it exchanges `c` and `q`. The repository now proves the exact source and finite-family identity

```text
entered = smooth - transport,
```

together with the dynamic canonical identity

```text
squarePrefixMertens = squareRootSmoothMass - squareRootTransportMass.
```

For `X=R^2-1`, finite Fubini reindexing reads the high transport population prime first. Analytically,

```text
T_R = sum_{R<q<=X, q prime} M(floor(X/q))
    = sum_{d<R} K_R(d) M(d),
```

where `K_R(d)` is the prime count in the reciprocal interval `X/(d+1)<q<=X/d`. Thus the high transport term is exactly a lower-triangular prime-dilation operator applied only to Mertens values below `R`.

The numerical experiment through `R=10000` verifies all exact identities with zero integer error, gives `corr(A,T)=0.999949`, and gives

```text
E(S)/(E(A)+E(T)) = 1.7730e-5.
```

A truncated Riemann-`R` prime-density baseline explains `0.999270` of the sampled transport variation without fitting an aggregate coefficient. By contrast, twenty deterministic random-sign assignments on the same geometry have mean cancellation ratio about `0.755`. Therefore:

```text
geometry gives the exact transfer map;
Mobius arithmetic gives the exceptional contraction.
```

The next analytic target is a cancellation-aware bound for the triangular kernel or for the exact weighted scale-transfer discrepancy. An absolute row-sum estimate discards the signed mechanism and is expected to be too weak.

## 6. Corrections that must remain permanent

1. If every shell increment were exactly zero, then the cumulative death process would be constant. Autocorrelation matters for nonzero or only statistically centered increments, not for identically zero increments.
2. Landau's theorem counts unrestricted almost-primes up to a size parameter. It does not directly give an asymptotic for the canonical largest-prime-factor population inside a constant-width difference-of-squares shell.
3. Ordinary sieve cardinality estimates face the parity obstruction: unsigned divisibility information does not by itself distinguish even from odd numbers of prime factors.
4. Congruence lanes need not affect every `omega` class in identical proportions. Local conditions can interact with divisibility by the sieving primes and with the canonical largest-prime-factor constraint. They still require a theorem before any sign bias is inferred.
5. Shell sparsity, pointwise shell balance, cumulative death control, survivor-discrepancy control, source-level scale transfer, prime-density approximation, and the full smooth-minus-transport Gram estimate are different statements and must not be collapsed.
6. Raw Euclidean interval scaling is not the correct aggregate model; prime density is an essential component of the low-to-high operator.
7. A high finite-range correlation or `R^2` is evidence and diagnosis, not an asymptotic estimate.

## 7. Next structural and analytic tests

The next dependency-bounded work should combine the scale-transfer operator with the retained arithmetic coordinates:

1. identify each prime-first lower cofactor fiber directly with the existing `mertensSummatory` API;
2. group the exact transform by `d=floor((R^2-1)/q)` and formalize the kernel `K_R(d)`;
3. refine the kernel or discrepancy by Fermat residue lane, cofactor `omega`, and orientation;
4. test whether multiplication by a new prime, orientation reversal, or another canonical transport maps admissible lanes to admissible lanes while flipping the Mobius sign;
5. retain every unmatched boundary term and the born-smooth remainder explicitly;
6. state a cancellation-aware operator estimate sufficient for the protected pointwise or uniform-local criterion;
7. preserve the complete signed interaction when passing to energy.

A successful operator or pairing theorem could be materially stronger than applying an unrestricted almost-prime asymptotic to the wrong population.

## 8. Acceptance rule for every future PR

Every PR must state:

- the exact node of this proof map that it advances;
- whether it is an identity, realization, sufficient criterion, open analytic premise, or finite certificate;
- the scale of the estimate, if any;
- whether the full signed interaction is retained;
- which obligations remain after the theorem.

A theorem that only redescribes a support set is valuable structural work, but it must not be presented as amplitude control or cancellation.

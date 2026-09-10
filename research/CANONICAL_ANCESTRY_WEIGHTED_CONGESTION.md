# Canonical ancestry: raw congestion fails, q^-2 scaling survives

This note records the diagnostic requested after the NS-cascade / collision-defect
synthesis. Numerical data below are route-selection evidence only; none of them
are used as a theorem.

## Exact carrier and trajectory

For `X = squareRootEndpoint R = R^2 - 1`, merged #629 identifies the saturated
second-contact source with the independent owner window

```text
max R (X / q^2) < m <= X / q,
P+(m) < q,
q prime, q < R,
m squarefree.
```

Equivalently `n=q*m` is squarefree, `P+(n)=q<R`, `n<=X`, `q*n>X`, and
`n/q>R`.

`CanonicalGapAncestryBridge.sourceParent` keeps `q` fixed and strips the largest
prime factor of `m` whenever `m>q`. The parent is unique and the core decreases
strictly. Thus a canonical ancestry edge is determined by its smooth child
`(q,c)`.

The diagnostic counts how many saturated sources traverse each such edge.

## Exact full-carrier results

The following values were obtained from the exact #629 inequalities and the
exact largest-prime stripping rule.

| R | max edge multiplicity | worst edge (q,c) | fraction of repeated edges | sum(depth/q^2) | /R |
|---:|---:|---:|---:|---:|---:|
| 100 | 4 | -- | -- | 0.6265 | 0.00627 |
| 200 | 6 | -- | -- | 1.4180 | 0.00709 |
| 500 | 14 | -- | -- | 4.1644 | 0.00833 |
| 1,000 | 22 | -- | -- | 9.3280 | 0.00933 |
| 2,000 | 51 | -- | -- | 20.8042 | 0.01040 |
| 5,000 | 138 | -- | 1.62% | 59.8547 | 0.01197 |
| 10,000 | 272 | (103,105) | 1.29% | 134.0151 | 0.01340 |

At `R=10,000`, the median and 95th-percentile edge multiplicities are both `1`;
even though the maximum has already reached `272`, only about `1.3%` of edges
are repeated.

The targeted exact ancestor-product counter avoids an `R^2` sieve. It confirms
that the local stacks keep growing:

```text
R=10000    edge=(103,105)   exact_multiplicity=272
R=100000   edge=(317,330)   exact_multiplicity=2834
R=1000000  edge=(1097,1155) exact_multiplicity=31684
```

This is not a fork of `sourceParent`. Many distinct higher ancestors coalesce
onto the same unique downstream edge.

## The pointwise multiplicity target is rejected

A theorem of the form

```text
max_edge chargeMultiplicity <= C * log(R)^k
```

is not the right interface. The canonical parent remains deterministic, but raw
congestion can be very large on a sparse set of low downstream edges.

The diagnostic quantity

```text
sum over ancestry edge traversals 1 / q^2
  = sum over saturated seeds depth(seed) / q(seed)^2
```

is empirically near-linear through the exact full sweeps above. This remains a
useful diagnostic, but it is no longer necessary to *postulate* a new global
packing theorem before using the collision information: #629 already exposes a
more local fibre on which the required q-square budget can be proved exactly.

## Exact #629 collision-fibre theorem

`lowWheelFrozenSecondContactChildOwnerColumn_eq_signed_fibers` writes the
reassembled coefficient of one face using

```lean
lowWheelFrozenSecondContactOldOwnerFiber R r d
```

and the old owners in that fibre carry the same face sign. So raw cardinality
cannot cancel inside the fibre.

The correct coefficient after the q-square descent is instead the reciprocal-
square mass

```lean
lowWheelFrozenSecondContactOldOwnerReciprocalSquareMass R r d
```

and the current branch proves

```lean
lowWheelFrozenSecondContactOldOwnerReciprocalSquareMass_le_one
```

as well as the literal daughter-cutoff version

```lean
sum_oldOwnerFiber_squareDilatedCutoffs_le_parent
```

because every old-owner fibre is a subset of `primesUpTo (R-1)` and #634 has
already proved the complete finite prime-owner reciprocal-square budget is at
most one.

Combining that exact fibre budget with the exact selected-11 weight-one energy
factor gives the stronger interaction theorem

```lean
elevenWeighted_sum_oldOwnerFiber_squareDilatedCutoffs_lt_parent
```

for every positive parent scale. Thus arbitrarily large *raw* collision
multiplicity is harmless once the natural `q^-2` scale is retained before the
11-sector energy contraction.

## Incomplete q^2 periods are explicit boundary charges

#636 originally proved the q-owner first-moment estimate only when `q^2 | K`.
The current branch removes that restriction. Exact modular counting gives at
most one extra hit per active residue, hence

```text
|outsidePrimeLeastDeletionChannel P (range K) q|
  <= 18 * (floor(K/q^2) + 1).
```

The extra `+1` is the finite incomplete-period frontier, not a new analytic
hypothesis.

Separately, `OutsidePrimeLeastSquareEndpoint` already proves that the aggregate
incomplete least-square super-orbit endpoint in one physical square block has
root-scale size

```text
|squareBlockOutsidePrimeLeastEndpointT P R| <= 3 * (2R + 1).
```

This is a **local square-block boundary theorem**. It must not be misread as an
automatic bound on the signed accumulation of all earlier square-block
endpoints; the global cascade still has to preserve the interaction structure.

## Revised hard seam

The remaining obstruction is therefore not:

- uniqueness of the canonical parent;
- pointwise collision multiplicity;
- the q-square reciprocal-scale budget;
- or the final incomplete q^2 period of one owner.

It is the physical **complete-super-orbit interior intertwining** already named
by #634/#635/#636:

> transport the Mertens-visible degree-one first-moment / rank-one Schur block
> through the exact selected-11 T-sector action and the least-square q-owner
> decomposition onto the Go `X/q^2` daughters, without taking ownerwise norms,
> so that the physical energy profile satisfies `ElevenQ2EnergyStep`.

Once that exact recurrence is established, the compiled theorem
`elevenQ2EnergyStep_implies_linear` supplies the subcritical energy induction;
`ThreeSlotDegreeOneCriterion` already connects the resulting degree-one energy
bound to the repository's protected RH chain.

The ancestry multiplicity objects remain in the Lean interface as diagnostics
and as a guard against reintroducing a false max-congestion estimate. They are
not asserted as the terminal theorem.

No `ClassicalMertensRHCriterion`, RH assumption, iid/random-sign model,
prime-gap assumption, or norm before the signed carrier identity belongs in the
remaining bridge.

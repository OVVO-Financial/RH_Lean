# Canonical ancestry: raw congestion fails, q^-2 weighted congestion survives

This note records the diagnostic requested after the NS-cascade / collision-defect
synthesis.  It is route-selection evidence only; none of the numerical data is
used as a theorem.

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
prime factor of `m` whenever `m>q`.  The parent is unique and the core decreases
strictly.  Thus a canonical ancestry edge is determined by its smooth child
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
are repeated.  Other high-congestion edges include `(101,105)`, `(109,110)`,
`(139,154)`, `(107,110)`, `(151,154)`, and `(97,105)`.

The exact targeted-edge counter gives

```text
R=10000 edge=(103,105) exact_multiplicity=272
```

without sieving through `R^2`.

## Consequence

A theorem of the form

```text
max_edge chargeMultiplicity <= C * log(R)^k
```

is not the right interface.  The canonical parent does not fork; instead many
higher ancestors coalesce onto a sparse set of low downstream edges.  Pointwise
congestion is therefore the wrong regularity norm.

The natural surviving quantity is the square-scale weighted congestion

```text
sum over ancestry edge traversals 1 / q^2
  = sum over saturated seeds depth(seed) / q(seed)^2.
```

Empirically this is close to linear over the range above, while the unweighted
maximum grows rapidly.  This is exactly the weight already compiled in two
independent pieces of the current route:

1. `SquareRootLowPrimeTSectorQ2Renormalization` proves the finite daughter-scale
   budget `sum_q X/q^2 <= X` and the resulting subcritical energy induction.
2. `OutsidePrimeCompleteDeletionFirstMoment` proves the physical complete-period
   first-moment estimate `|m_q| <= 18 K/q^2` for each odd prime owner.

So the next arithmetic seam is not bounded maximum multiplicity.  It is a
Carleson-style/global packing statement asserting that ancestry coalescence is
summable in the same `q^-2` scale measure.

## Correct Lean target

The interface should expose both the raw multiplicity (for diagnostics) and the
weighted quantity, but only the latter should become a proof obligation.  In
schematic form:

```lean
def canonicalAncestryChargeMultiplicity ... : Nat

def canonicalAncestryOwnerSquareWeight ... : Rat

def canonicalAncestryWeightedCongestion ... : Rat

/-- Hard arithmetic seam; no claim that it is already proved. -/
def CanonicalAncestryWeightedCongestionBound : Prop :=
  exists C > 0, forall R,
    canonicalAncestryWeightedCongestion R <= C * R * polylog R
```

An eventual linear bound would be stronger and is consistent with the current
finite data, but the formal target should permit a polylogarithmic loss until the
packing proof itself determines otherwise.

No `ClassicalMertensRHCriterion`, RH assumption, prime-gap assumption, or norm
before the signed carrier identity belongs in this interface.

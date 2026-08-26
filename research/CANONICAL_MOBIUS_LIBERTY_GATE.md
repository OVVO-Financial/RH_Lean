# Canonical Möbius liberty terminal-closure gate

## Accepted theorem

At the canonical terminal cutoff

```text
P_R = R - floor(sqrt R),
```

construct a finite compressed boundary `LibertyBoundary(R,K,j)` and prove both

```text
T(P_R) = signedMass(LibertyBoundary(R,K,j))
```

and

```text
#LibertyBoundary(R,K,j) <= C * R
```

for one explicit absolute numeral `C`, under the actual packet-crossing data

```text
j <= reciprocalLayerCard(R,K),
0 <= V(R,K,j),
V(R,K,j) < K,
1 <= K < R.
```

The boundary must be constructed from the actual creation/response carrier and
its prime-toggle matchings.  It may not be defined as an arbitrary remainder.

## Canonical liberty dichotomy

The finite processed-seat matching already gives the literal statement:

every original state either

1. is removed in one concrete fresh-prime pair at a uniquely located matching
   stage; or
2. survives in the terminal no-liberty frontier.

This is formalized in

```text
RHLean/Proof/SquareRootLowPrimeCanonicalLiberty.lean
```

The dichotomy is structural and is not the terminal estimate.

## The boundary must be compressed before counting

The raw terminal seat frontier is not the desired boundary.  Its shallow
post-root prime multiplicity is too large.  The complete reciprocal packet must
first be combined into the ordered residual

```text
V(R,K,j) = squareRootCrossingLayerPartialPacketInt R K j.
```

The packet boundary is represented by exactly `V` positive unit cells, hence
has fewer than `K` cells.  This is formalized in

```text
RHLean/Proof/SquareRootLowPrimePartialPacketBoundary.lean
```

No raw prime count and no `j * |M(K)|` term is admitted into the final boundary
budget.

## Two matchings, one alternating forest

The final carrier has two zero-mass matching structures:

1. creation-to-response cancellation between the shallow carrier and the deep
   response carrier;
2. processed-prime toggle cancellation inside the response carrier.

Their union has alternating components.  Flipping a component changes the
location of an unmatched state but not the represented signed mass.

The existing displacement theorem proves that every apparent unstable prime
pivot has a strictly earlier blocker.  Therefore every displacement chain is
well founded.  The missing theorem must perform this rematching globally and
show that the only endpoints are:

* one head cell;
* the born exit frontier, already bounded by `2*R`;
* the genuine root/near-root boundary, to be bounded by an explicit multiple
  of `R`;
* canonical least-failure endpoints after all duplicated displacement paths
  have been cancelled;
* the compressed partial packet, with fewer than `K` cells.

## Exact remaining obstruction

It is not enough to prove that every terminal seat reaches a canonical root.
Several seats may reach the same root.  The required result is a signed fibre
cancellation theorem:

```text
for every canonical root r,
  the alternating creation/response displacement component over r
  has residual cardinality at most one.
```

Equivalently, after flipping all finite alternating paths, at most one unmatched
unit state remains per root.

This is the point at which the cofactor-to-root map becomes a quantitative
boundary theorem rather than another reindexing.

## Endpoint and energy consequences

If the completed boundary has cardinality at most `C*R`, then unit weights give

```text
|T(P_R)| <= C*R,
T(P_R)^2 <= C^2 * R^2 <= C^2 * R^2 * K.
```

The exact global energy telescope then gives

```text
sum_{K<p<=P_R} (2*T(p-1)*Delta_p - Delta_p^2)
  >= T(K)^2 - C^2 * R^2 * K.
```

No separate analytic or covariance step remains after the boundary theorem.

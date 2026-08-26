# Descending-pivot closure strategy

## Governing insight

The six residual populations are not six independent arithmetic errors.  They
are the critical cells produced by processing commuting prime toggles in an
order that allows a larger prime to destabilize a smaller pivot.

For a fixed arithmetic root and literal response seat, the admissible cofactors
form a multiplicative interval in the fresh-prime Boolean cube.  Process the
fresh primes from largest to smallest.

If `p < q` and the four corners

```text
x          p*x
q*x        q*p*x
```

belong to the carrier in the expected channels, the `q`-matching removes the
two endpoints of the `p`-edge together.  It cannot leave a one-sided `p`-edge.
Therefore an unstable `p` pivot can occur only where this arithmetic square is
not closed.

The repository already identifies the only square-closure failures:

1. **lower birth boundary:** a born partner is admitted by `p*x` but not by
   `x`; this is the first-failure shell;
2. **upper product boundary:** the next extension crosses `R^2-1`; this is the
   root-crossing/near-root frontier;
3. **shallow crossing plateau:** the incomplete layer contributes the single
   signed correction `j M(K)`.

Thus the unstable populations should disappear as independent classes.  They
are absorbed into the same three genuine boundaries as the no-toggle
populations.

## Why descending order is the right topological sort

The existing diagnosis says that every unstable pivot is charged by a strictly
larger prime.  This is stronger than a counting statement: it says the pivot
dependency graph is upper triangular.  Descending prime order is its topological
order.

The generic one-step theorem now lives in

```text
RHLean/Proof/SquareRootLowPrimeDescendingPivotStability.lean
```

It proves that, under the commuting-square condition, a fresh `q` step preserves
the endpoints of a smaller `p` edge together.  The descending frontier still
has signed mass exactly `T(U)` because every prime-coordinate matching has zero
mass independently of order.

## Carrier-specific closure statements to prove next

### High/post-root channel

For a fixed post-root partner, product admissibility is downward closed in the
cofactor.  Hence the full multiplicative square is closed away from the owner
cutoff.  Consequences:

- every nontrivial high state has its canonical smaller parent in the carrier;
- descending matching removes parent and child together through all larger
  coordinates;
- the interior high no-toggle and high unstable populations are empty;
- the surviving high support is only the already-isolated cutoff/near-root
  boundary.

The branch already contains the pointwise downward-parent theorem and the
vanishing of the interior high no-toggle set in

```text
SquareRootLowPrimeNoTogglePopulationBound.lean
```

The missing step is to lift that pointwise fact through the descending matching
fold using the square-stability theorem.

### Born channel

The product upper bound remains downward closed.  The only failed lower corner
is the order condition saying that the partner has just become no larger than
the cofactor.  Therefore a failed square is exactly a first-hit/birth face.
The existing first-failure theorems should identify its signed mass before any
absolute value is taken.

The born exit side is already directly bounded:

```text
# BornNoSuccessor(P_R) <= 2 R.
```

The remaining born critical cells must be mapped to the lower first-failure and
upper root-crossing boundaries, not estimated prime by prime.

### Head and shallow crossing

Do not count `j` copies of `|M(K)|`.  Recombine the transition shell first.  The
crossing-layer construction gives one signed partial packet, with the existing
overshoot hypotheses

```text
0 <= V(R,K,j),
V(R,K,j) < K.
```

So the whole shallow defect costs less than `K`, not `j K` and not
`j |M(K)|`.

## Proposed terminal estimate

After the carrier-specific descending-square theorem, the terminal signed mass
should have an exact boundary form

```text
T(P_R)
  = born_exit
  + born_first_failure
  + root_crossing
  + near_root
  + crossing_overshoot,
```

with no independent unstable term.

The target is a bound of the shape

```text
|T(P_R)| <= C * R + K.
```

This is already stronger than the required energy scale.  Under `1 <= K < R`,

```text
(C*R + K)^2 <= (C+1)^2 * R^2 <= (C+1)^2 * R^2 * K.
```

The real energy telescope then gives directly

```text
sum_{K<p<=P_R} (2*T(p-1)*Delta_p - Delta_p^2)
  >= T(K)^2 - (C+1)^2 * R^2 * K.
```

This route deliberately chooses the accepted sequential-energy endpoint rather
than taking absolute values of the six-way cardinality decomposition.

## Acceptance criterion

The next theorem must establish the carrier-specific square closure and the
resulting exact boundary support for the descending frontier.  Merely defining
the descending list or restating mass preservation is not closure.

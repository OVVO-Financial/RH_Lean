# Covariance capacity: bridge closed, signed capacity open

**Status.** The covariance *bridge* is no longer an unproved abstract seam.
`MertensCovarianceDescent.lean` now proves it in two increasingly faithful forms:

1. the one-face prime-product Euler frontier dominates the global integer-order
   covariance, with an exact diagonal-gap formula; and
2. at square endpoints the centered middle-bias Euler coordinate has covariance
   **exactly equal** to the global covariance.

The open problem is now the **RH-scale signed capacity estimate** on that global
centered coordinate. The raw support-only frontier remains a full power too
large.

## 1. Keep the lag-zero energy

Write

```text
Q(X+1) = sum_{n <= X} mu(n)^2
C(X+1) = sum_{1 <= a < b <= X} mu(a) mu(b).
```

The deterministic Green--Kubo identity is

```text
|M(X)|^2 = Q(X+1) + 2 C(X+1),
C(X+1) = (|M(X)|^2 - Q(X+1)) / 2.
```

`Q` is the sign-definite lag-zero quadratic variation (the uncentered variance
analogue). The factor `1/2` appears because the square contains both orientations
of every off-diagonal pair.

This diagonal is not bookkeeping. Any positive covariance excursion must first
overcome it. The theorem

```text
realMertensPositiveLagPairSum_eq_norm_sq_sub_diagonal
```

records the identity directly, while

```text
realMertensDiagonal_eq_card_squarefreeUpTo
```

identifies `Q` with the exact squarefree population.

## 2. Exact one-face bridge

Let `F(X,ell)` be the first-failure frontier population after exposing Euler
coordinate `ell`. The frontier covariance used by the support calculation is

```text
C_frontier = (|M(X)|^2 - F(X,ell)) / 2.
```

Because every first-failure face is a genuine admissible squarefree face,

```text
F(X,ell) <= Q(X+1).
```

Therefore the difference from global covariance is exact:

```text
C_frontier - C_global = (Q - F) / 2 >= 0.
```

Compiled as:

```text
primeProductFrontierSurvivingCovariance_sub_global_eq_diagonalGap
realMertensPositiveLagPairSum_le_primeProductFrontierSurvivingCovariance
covarianceEnvelopeDominates_primeProductFrontier
```

So `CovarianceEnvelopeDominates` is proved for the prime-product Euler frontier.
No probability, independence, asymptotic estimate, or sign assumption is used.

## 3. The sharper support-only bound

The existing Othello pairing gives

```text
|M(X)| <= F(X,ell).
```

Restoring the *global* diagonal before taking covariance yields

```text
C(X+1) <= (F(X,ell)^2 - Q(X+1)) / 2.
```

This is compiled as

```text
realMertensPositiveLagPairSum_le_frontier_sq_sub_diagonal.
```

It is strictly sharper than the older frontier-only maximum
`F(F-1)/2`, because `F <= Q`.

This does **not** rescue support exhaustion. The minimizing raw frontier is still
linear. For the prime-2 face it is the odd squarefree top-half wall and has
asymptotic density `2/pi^2`. Hence `F^2` remains quadratic while the restored
diagonal is only linear.

At the diagnostic cutoff `X = 200000` the existing script records

```text
Q = 121581,
F_2 = 40527.
```

Thus the exact diagonal correction `(Q-F)/2` is `40527`: large on the linear
scale, but still unable to cancel the quadratic support term.

## 4. The terminal-correction scalar is not the right global carrier

`MiddlePrimeFibreCollapse` defines a hierarchical terminal-correction mass and
bounds its worst-case surviving covariance. That scalar is useful Euler
bookkeeping, but its amplitude is not `M(R^2-1)`, so its covariance cannot simply
be declared global.

This distinction remains important: the theorem below does **not** identify
`squareRootHierarchicalSurvivingCovariance` with global covariance.

## 5. The centered middle-bias residual *is* the global carrier

The repository already had the exact identity

```text
squareRootMiddleBiasResidual R = -squarePrefixMertens (R-1).
```

The current PR now rewrites that same centered coordinate into the elementary
reciprocal Euler hierarchy:

```text
squareRootMiddleBiasResidual R
  = topPrimeCard
    - squareRootSmoothMass (R-1)
    + sum_{2 <= d < R} N_R(d) * M(d).
```

Compiled as

```text
squareRootMiddleBiasResidual_eq_top_sub_smooth_add_reciprocalLayers.
```

This is the faithful prime-by-prime carrier:

- the top prime block is deterministic;
- the smooth term is the completed low-prime state;
- every remaining reciprocal layer samples a complete lower-scale Mertens state;
- no absolute value is taken between layers.

Define its covariance using the **global** lag-zero diagonal:

```text
squareRootMiddleBiasResidualCovariance R
  = (|squareRootMiddleBiasResidual R|^2
       - Q(squareRootEndpoint R + 1)) / 2.
```

Then the bridge is equality:

```text
squareRootMiddleBiasResidualCovariance_eq_global:
  squareRootMiddleBiasResidualCovariance R
    = realMertensPositiveLagPairSum (squareRootEndpoint R + 1).
```

So at square endpoints there is no remaining carrier mismatch at all.

## 6. Square endpoints lose no RH-scale information

`SquarePrefixMertensBridge.lean` already proves

```text
MertensEnergyBoundedStatement
  <-> SquarePrefixEnergyBoundedStatement.
```

The interpolation from square endpoints to arbitrary `x` uses only
`|mu(n)| <= 1` across the gap to the nearest square.

Therefore an RH-scale covariance bound on the centered reciprocal Euler carrier
above is enough to return to the full Mertens energy criterion. The geometry is
now on the correct carrier; the remaining issue is quantitative cancellation.

## 7. What remains open

The remaining native task is a **signed capacity/descent theorem**, not another
bridge theorem and not another support count.

Two existing pieces point in the right direction.

### Record descent

`MertensCovarianceDescentStatement` says every supercritical covariance record is
forced by a strictly smaller supercritical record. Natural-number well-foundedness
then rules out any such record. The implication to the Mertens energy criterion
is already compiled.

What is still needed is the elementary prime-by-prime theorem that produces this
descent from the Euler geometry.

### Fresh-prime covariance copies

For a fresh post-root prime `p`, multiplication by `p` reverses Möbius mass but
preserves pair products. Thus each prime family is covariance-isomorphic to a
lower prefix. Grouping families by reciprocal quotient gives the schematic
upper sum

```text
sum_{z < sqrt W} N_W(z) C(z),
N_W(z) <= W/(z(z+1)) + 1.
```

At a minimal supercritical scale, every lower `C(z)` is already subcritical. The
remaining work is to preserve the signed cross-family/smooth interaction while
performing this descent, rather than replacing it with a magnitude-first bound.

## 8. Why the diagonal observation matters for the next attack

The diagonal is the fixed baseline. Off-diagonal covariance is only the excess
(or deficit) of total signed energy over that baseline:

```text
2 C = |M|^2 - Q.
```

Thus every refinement should carry its lag-zero energy with it. Squaring a sum of
support capacities and subtracting a surrogate atom count only at the end loses
the most useful sign-definite part of the identity.

The next theorem should therefore refine the centered global carrier

```text
top - smooth + sum_d N_R(d) M(d)
```

prime by prime while preserving:

1. the exact lower-scale covariance copied by each fresh prime;
2. the exact diagonal contribution of each physical squarefree seat; and
3. the signed cross terms between distinct prime families and the smooth block.

That is the elementary Euler version of the covariance tree already formalized
by `BlockCovarianceRefinement`.

## Do not

- replace signed layer interactions by `sum |layer|` before squaring;
- count surviving pairs as a substitute for covariance;
- identify the hierarchical terminal-correction covariance with global
  covariance without recentering;
- discard `Q`: it is the lag-zero energy that makes the exact bridge and the
  sharper support bound work;
- aim for `C(X) = O(X)` as though it were automatic. That would already imply
the false-conjecture-scale square-root strength far beyond what the trivial pair
count gives.

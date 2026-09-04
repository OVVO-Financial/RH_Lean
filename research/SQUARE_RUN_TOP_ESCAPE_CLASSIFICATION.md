# Square-run top-escape classification

After canonical first-separation ownership, a subdoubling square run has a rigid geometry: stripping the owner prime from the endpoint carrying it lands strictly below the left square anchor. Hence the owner cube is boundary-crossing rather than a complete cube internal to the run.

The formal module `RHLean.Analysis.SquareRunFreshPrimeCubeBoundary` strengthens this to a two-sided statement. For every contributing owned pair, the stripped owner parent lies below the lower anchor while adjoining the owner prime to the opposite parent reaches or crosses the upper cutoff. Thus a unique owner cube exists, but no such cube is completely contained in a subdoubling square-run window. Four-corner cancellation is genuinely nonlocal in square time.

The module `RHLean.Analysis.SquareRunTopEscapeClassification` records that the natural same-prime nonpositive covariance leaf is empty on subdoubling runs and that its associated escape is therefore the whole square-run covariance. It also records the exact quantitative classification

```text
SquareRunTopEscapeCovarianceBoundedStatement (squareRunPrimeLeafCovariance p)
  <-> MertensEnergyBoundedStatement.
```

So unique ownership closes the combinatorial no-overlap question at the atom/owner level, but the RH-scale top-escape estimate is not a weaker residual theorem. The non-circular continuation must preserve the signed cross-family chronology and derive covariance descent rather than bound the boundary by support.

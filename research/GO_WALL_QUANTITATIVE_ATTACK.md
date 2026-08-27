# Go wall quantitative attack

The wall is treated as a no-liberty boundary, not as an interior Othello board.

## Exact first descent

For consecutive old-prime universes `ell < q`, the adjacent frozen strip is

```text
F_{q^-}(X/q) - F_{q^-}(X/ell).
```

The fresh-`q` recurrence at cutoff `X/q` gives

```text
F_q(X/q) = F_{q^-}(X/q) - F_{q^-}((X/q)/q).
```

Hence

```text
GoStrip_q(X)
  = Diagonal_q(X) - Diagonal_ell(X)
    + SquareResidual_q(X),
```

where

```text
SquareResidual_q(X) = F_{q^-}((X/q)/q).
```

Summing genuinely consecutive Go strips therefore telescopes the diagonal
states and leaves only square-dilated lower-scale residuals plus endpoints.

## Square-kill interpretation

The residual is the signed mass of old squarefree faces `t` satisfying

```text
q^2 * P(t) <= X.
```

Equivalently, writing `c=P(t)` and `m=q*c`,

```text
P+(m)=q,
q*m <= X,
mu(m)=-mu(c).
```

Thus distinct residual slices have unique largest-prime ownership.  The
physical lift `q^2*c` is a selected-prime square hit, but the relevant carrier
is the closed `q`-smooth kill slice, not the whole animation kill channel.

## Quantitative strategy

Do not take `sum_q |SquareResidual_q|` as the primary target.  Assemble the
signed square-kill ledger first and take the norm only after ownership.

At `X_R=R^2-1` split by `q^3`:

* if `q^3 > X_R`, then `(X_R/q^2) < q`, so roughness is vacuous and the residual
  is an ordinary lower-scale Mertens value;
* if `q^3 <= X_R`, composite interior can remain.  This is exactly the
  `R^(2/3)` support threshold already formalized in
  `SquareRootPredecessorPrimeCells`.

The low-`q` sector must remain one signed packet.  Splitting it into the
positive `c<q` prefix and the born `q<=c` continuation exposes the open
prime-indexed Mertens transform and destroys the intended cancellation.

## Existing repository structures to reuse

1. `SquareRootSmoothParityClasses`: the first reciprocal rough transform.
2. `LowWheelDoubleCubeTransport`: the high square-kill tail embeds as the
   diagonal `u={q}, k=q` slice of the two-cube transport carrier.
3. `LowWheelCanonicalPairingFrontier`: cancel the assembled diagonal carrier by
   the canonical least-prime involution before taking norms.
4. `CanonicalGapAncestryBridge`: classify the remaining no-liberty roots by
   canonical arithmetic ancestry.
5. `SquareRootLowPrimeResponseForest`: if the cubic born packet is used instead,
   internal fresh-prime children flip sign and only explicit exits survive.

No PNT, Mertens product theorem, random-sign model, or chain-parity estimate is
to be introduced.

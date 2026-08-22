# Canonical frontier incidence no-go

## Status

This note records the closure of the one-prime canonical frontier coordinate after the exact low-pivot / post-root split.

The conclusion is a no-go for further progress by merely reindexing, taking a positive norm of, or recursively reinserting the same completed one-prime frontier.  It is not a negative statement about bilinear or genuinely restricted prime-coordinate constructions.

All theorem-level claims below are finite and exact.  No PNT estimate, zeta input, asymptotic, or RH hypothesis is used.

## 1. Pointwise incidence is a lower-scale Mertens bundle

For

```text
X = R^2 - 1,
T_n = floor(R/n),
```

the canonical incidence coordinate is represented by

```text
B_R(n) = 1 - sum_{1 <= q <= T_n} M(floor(X/(n q))).
```

The intended cofactor-hyperbola form is the equivalent identity

```text
B_R(n)
  = sum_{1 <= c < R} mu(c)
      (floor(X/(n c)) - floor(R/n)).
```

The first formula is formalized in `LowWheelSurvivorFloorExpansion`; the second is the exact pointwise arithmetic form to connect directly to the already-proved floor expansion.

## 2. The top half is literally Mertens

If

```text
R/2 < n <= R,
```

then `floor(R/n) = 1`, so

```text
B_R(n) = 1 - M(floor(X/n)).
```

Consequently the positive top-half energy is exactly

```text
J_top(R)
  = sum_{R/2 < n <= R}
      n * |1 - M(floor(X/n))|^2.
```

This is the rigorous positive-norm obstruction: the incidence norm has not eliminated the Mertens function; it contains a local Mertens second-moment functional verbatim.

The numerical observation that the full weighted incidence energy appears to scale like roughly `0.02 R^3` is **not** promoted to a theorem here.  No unconditional local second-moment lower bound for Mertens is being asserted.

## 3. The signed bootstrap has the corrected sign

With

```text
H = floor(R/2),
```

the exact split is

```text
M(X)
  = M(H)
    - sum_{n <= H} mu(n) B_R(n)
    + sum_{H < n <= R} mu(n) M(floor(X/n)).
```

The final top-half correlation has a plus sign.

## 4. Generic triangular Mobius collapse

For every function `F : N -> C` and every `R >= 1`, the finite identity

```text
sum_{n <= R} mu(n)
  sum_{q <= R/n} F(n q)
= F(1)
```

holds.

Regroup by `m = n q`.  The coefficient of `F(m)` is

```text
sum_{n | m} mu(n),
```

which is `1` for `m = 1` and `0` otherwise.  This is exactly `mu * 1 = delta` on the triangular region `n q <= R`.

This is the criterion for future routes: a completed one-prime divisor fibre is annihilated by Mobius inversion.  New leverage must preserve some structure not erased when the full divisor fibre is completed.

## 5. The bootstrap collapses to the identity

Substituting the pointwise bundle into the corrected split gives

```text
M(X)
  = sum_{n <= R} mu(n)
      sum_{q <= R/n} M(floor(X/(n q)))
  = M(X).
```

Thus the proposed finite-volume renormalization equation supplies no independent recurrence or uniqueness principle.  It is algebraically the identity operator after `mu * 1 = delta`.

## 6. Local rough-prime mechanism

The low/post cancellation nevertheless has genuine local algebra behind it.  For prime `p`, the relevant roughness coordinates satisfy the formal convolution pattern

```text
1_{rough >= p} * (mu * 1_{rough > p}) = 1_{p-powers}.
```

Every factor containing a prime `q > p` cancels by a local `1 - 1` Mobius factor; only pure powers of the pivot survive.  The repository already formalizes the corresponding signed one-prime peeling law in `Arithmetic/SignedBuchstabRecursion.lean`:

```text
Z(p-1,y) = Z(p,y) - Z(p,y/p).
```

The frontier crossing window truncates this complete convolution.  Its boundary is exactly where the lower-scale Mertens bundle reappears.

## 7. Final four-layer diagnosis

| Layer | Status | Exact content |
|---|---|---|
| Local algebra | real structure | rough-Mobius fresh-prime cancellation leaves the pivot-power channel |
| Truncation boundary | Mertens remains | `B_R(n) = 1 - M(floor(X/n))` on `R/2 < n <= R` |
| Positive norm | embeds Mertens | top-half energy is an explicit local Mertens energy |
| Signed bootstrap | tautological | the full triangular reinsertion collapses by `mu * 1 = delta` to `M(X) = M(X)` |

## Conclusion

The one-prime frontier coordinate family is closed.

Its exact local cancellation mechanism is useful structural information, but neither completing the one-prime fibre, taking a positive norm of the resulting incidence field, nor recursively reinserting that same completed frontier creates new cancellation.  A genuinely new route must introduce an operation that survives the complete divisor-fibre collapse: for example, a nontrivial restricted region, a genuinely bilinear interaction, or another structure not reducible to the full `n q <= R` Mobius triangle.

# The invariant behind the x = 210 survivor cancellation

The zero at x=210 is not the invariant. The invariant is fibrewise.

Let
\[
R=\lfloor\sqrt x\rfloor
\]
and let \(p>R\) be prime. Every squarefree outer state on the \(p\)-fibre is
uniquely \(cp\) with \(c<p\). Pair \(cp\leftrightarrow2cp\) whenever both
states are physical.

Write
\[
y=\left\lfloor\frac{x}{p}\right\rfloor.
\]
Since \(p>\sqrt x\), one has \(y<p\), so \(p\nmid c\) for every
\(1\le c\le y\), and therefore
\[
\mu(cp)=-\mu(c).
\]

The surviving cofactors are precisely the odd integers
\[
y/2<c\le y.
\]

But the elementary dyadic Möbius identity gives
\[
M(y)
=
\sum_{\substack{c\le y\\c\text{ odd}}}\mu(c)
-
\sum_{\substack{c\le y/2\\c\text{ odd}}}\mu(c)
=
\sum_{\substack{y/2<c\le y\\c\text{ odd}}}\mu(c).
\]

Hence the signed survivor amplitude on the individual high-prime fibre is

\[
\boxed{
\sum_{\substack{cp\text{ survives}}}\mu(cp)
=
-M\!\left(\left\lfloor\frac{x}{p}\right\rfloor\right).
}
\]

Summing over all \(p>\sqrt x\) gives

\[
\boxed{
\mathrm{SurvivorAmplitude}(x)
=
-\sum_{\substack{p>\sqrt x\\p\le x\\p\text{ prime}}}
M\!\left(\left\lfloor\frac{x}{p}\right\rfloor\right).
}
\]

This is exactly the strict upper-prime Mertens transform already present in
the square-root transport coordinate, with the survivor orientation carrying
the minus sign.

The new regression
`experiments/survivor_mertens_invariant.py` verifies the identity
**prime-by-prime** for every \(2\le x\le10000\), not merely after summing
fibres. No failure occurs.

Sample totals:

| x | survivor count | survivor amplitude |
|---:|---:|---:|
| 210 | 38 | 0 |
| 224 | 42 | 4 |
| 317 | 59 | -1 |
| 3135 | 557 | 47 |

Thus the value zero at 210 is accidental, while the exact lower-scale Mertens
transform is invariant.

## Consequence for the proof search

The first-stage survivor population should not be bounded or forced to cancel.
It should be **identified exactly with the already-formalized upper-prime
Mertens transform** and carried into the matched born-smooth/transport and
response/re-entry machinery.

The repository already proves at production square endpoints:

- `primeDilatedLowCofactorMass_eq_mertensSummatory`: each upper-prime fibre is
  the reciprocal-cutoff Mertens value;
- `squareRootTransportPrimeFirst_eq_mertensTransform`: the full transport is
  the sum of those lower-scale Mertens fibres.

What the x=210 family contributes is a direct physical parent/child
interpretation of that transform: the high-prime transport is literally the
signed residual left after exact dyadic cancellation on each fibre.

That is the invariant to formalize as a bridge, not the special zero at 210.

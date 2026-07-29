# Using the full-factorization semantic guard

Any new module that introduces parent/cofactor transport together with Möbius
signs should import:

```lean
import RHLean.Arithmetic.FullPrimeFactorizationState
```

Then keep these notions separate:

- `fullPrimeFactorDepth n`: complete factor depth with multiplicity;
- `distinctPrimeFactorDepth n`: distinct-prime depth;
- `PrimeTransportEdge`: the compressed arithmetic edge `parent * terminal = child`.

A transport proof may use `PrimeTransportEdge.moebius_child_eq_neg_parent` for a
fresh terminal prime.  A parity proof should use
`moebius_eq_negOnePow_fullPrimeFactorDepth` and must establish squarefreeness.

Do not infer factor depth from the number of displayed multiplicands in a
transport equation.

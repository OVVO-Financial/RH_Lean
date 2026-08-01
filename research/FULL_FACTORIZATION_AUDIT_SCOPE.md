# Audit scope: full factorization versus compressed transport

This companion note records the operational scope of
`FULL_FACTORIZATION_SEMANTIC_AUDIT.md`.

The audit searched the Lean source, research notes, and experiment scripts for:

- `canonicalCofactor`
- `parent`
- `primeFactors`
- `primeFactors.card`
- `cardFactors`
- `cardDistinctFactors`
- Möbius sign-flip and collision language
- factor-depth and omega-parity language

## Result

No inspected proved Lean theorem derives Möbius parity by treating an opaque
composite cofactor as one prime factor.  Existing parity proofs use one of:

- `Nat.primeFactors` and its cardinality;
- `ArithmeticFunction.cardFactors`;
- `ArithmeticFunction.cardDistinctFactors` plus squarefreeness;
- multiplicativity and coprimality for a fresh appended prime.

The primary defect was semantic ambiguity: compressed transport displays such
as `n = c * q` can be misread as two-factor Möbius parity.  The new guard module
makes that interpretation formally unavailable.

## PR #138 status

PR #138 was merged into its stacked base branch rather than directly into
`main`.  Its terminal-prime extension logic was included in the audit as a
transport construction.  It is algebraically valid as a recurrence between the
separate integers `c` and `cq`, but any later merge into `main` should import and
cite `FullPrimeFactorizationState` so the parent is never counted as one prime.

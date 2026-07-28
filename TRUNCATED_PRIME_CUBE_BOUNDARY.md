# Truncated prime-cube boundary layer

This note records the exact finite statement introduced after PR #118.

Let `s` be a finite coordinate set and let `admissible` be a downward-closed
predicate on faces `t ⊆ s`. The truncated alternating mass is

```text
sum_{t ⊆ s, admissible t} (-1)^|t|.
```

Fix a coordinate `a ∈ s`. Every admitted child `insert a t` has an admitted
parent `t`, and the two alternating signs cancel. Therefore the full truncated
cube is exactly the signed first-failure boundary

```text
sum_{t ⊆ s \ {a}, admissible t, not admissible (insert a t)} (-1)^|t|.
```

This is an identity, not an estimate. It formalizes the statement that complete
interior cells cancel and every nonzero contribution is caused by a failed
extension at the cutoff. Iterating the construction over several coordinates is
the next step toward a complete ordered multi-prime boundary stratification.

The present PR does not claim:

- an arithmetic realization of `admissible` by a specific product cutoff;
- a cardinality or signed bound for the first-failure boundary;
- a Gram estimate;
- an RH implication.

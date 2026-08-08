## Boundary classification

- [ ] Maintenance or documentation only; no Lean mathematical source changed.
- [ ] Quantitative boundary advance.

If this is a quantitative advance, update `boundary/frontier.json` and provide:

- Previous frontier:
- New frontier:
- Witness module:
- Witness theorem:
- Certified exponent, if using `power_bound`:

The witness theorem must prove the canonical predicate from
`RHLean.Analysis.MobiusSynthesisBoundary`. Equivalent decompositions,
reindexings, alternate bases, and other representation-only changes to Lean
mathematical source are intentionally rejected by the `boundary-advance` check.

## Validation

- [ ] `lake build RHLean --wfail`
- [ ] The boundary witness type-checks against the canonical contract.

# Möbius synthesis boundary policy

The synthesis endpoint is intentionally frozen at the canonical nonzero response
`H_{k,n} = squareWheelNonzeroSampleResponse (...)`. Exact rewrites, new bases,
reindexings, conductor reorganizations, equivalent energies, and other alternate
representations are not counted as progress by themselves.

The required PR check is `boundary-advance`.

## Canonical contract

`RHLean/Analysis/MobiusSynthesisBoundary.lean` defines two propositions.

- `NonzeroResponsePowerBound r` is a uniform pointwise bound on the canonical
  nonzero response at exponent `r`, for every complete square sample in every
  synchronized primorial block with `k >= 2`.
- `NonzeroResponseRHScale` is the final target: `NonzeroResponsePowerBound
  (1/2 + epsilon)` for every positive epsilon.

The contract is immutable inside an ordinary boundary-advance PR. A contributor
cannot weaken or redefine the predicate and then use the weakened statement as
its own witness.

## Certified frontier

`boundary/frontier.json` records the strongest certified state.

The initial state is `exact_reduction`: the zero mode has been eliminated, the
coupling is uniformly contractive, and the nonzero response is exactly identified
with the collapsed expansion-reindexed numerator, but no nontrivial pointwise
power saving is certified.

A research PR touching Lean source must make one of these strict transitions:

1. `exact_reduction -> power_bound`, with a rational exponent strictly below 1;
2. `power_bound(r_old) -> power_bound(r_new)`, with `r_new < r_old`;
3. either open state -> `rh_scale`.

The candidate manifest must name a Lean module and theorem. The workflow creates
an independent Lean `example` whose type is exactly the claimed canonical
predicate and then asks Lean to check it. A theorem about an equivalent
representation does not pass unless it actually proves the bound on the canonical
response.

## Maintenance changes

A PR that does not change `RHLean.lean` or a Lean file below `RHLean/` may leave
the certified frontier unchanged. This permits documentation, CI, and repository
maintenance without pretending that such work advances the analytic boundary.

Any Lean mathematical source change with an unchanged frontier fails closed.
This is deliberate: the synthesis repository is not the default destination for
more exact decomposition once the canonical residual has already been isolated.

## Trust model

The workflow uses `pull_request_target` only to obtain the workflow and checker
from the trusted base branch. It then checks out the candidate with persisted Git
credentials disabled and grants only read access. The candidate cannot make its
own edited copy of `scripts/check_boundary_advance.py` decide the current PR.

The Lean build runs with no GitHub token exported to the build step. The boundary
contract itself is also rejected if modified in the same research PR.

After the witness type-checks, the workflow runs `#print axioms` on the witness
and rejects any dependency outside Lean's standard logical axioms `propext`,
`Classical.choice`, and `Quot.sound`. In particular, a contributor cannot make a
fresh axiom whose type is the desired bound and use that as a boundary advance.

## Repository settings

For the standalone `mobius-synthesis` repository, protect the default branch and
make the status check named `boundary-advance` required. Also enable Code Owner
review for the gate infrastructure listed in `.github/CODEOWNERS`.

Inside the parent `RH_Lean` repository this workflow is intentionally stored
under `export_mobius_synthesis/.github/workflows/`. GitHub does not execute nested
workflow directories there. It becomes an active root workflow when this export
is published as the standalone synthesis repository.

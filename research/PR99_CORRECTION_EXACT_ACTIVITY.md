# Correction record for PR #99: midpoint lifetime versus exact activity

## Status

PR #99 was merged as a finite research and reproducibility contribution. It did not change the compiled Lean theorem library or assert an analytic theorem. This correction preserves its exact identities and historical experiment while withdrawing an interpretation that later diagnostics falsified.

## What remains valid from PR #99

- the complete odd-annulus reconstruction;
- the exact cofactor packet-start identity;
- zero-error finite checks of those identities;
- the algebraic decomposition for any chosen deterministic model;
- the observation that a local prime-density model predicts aggregate high transport accurately over the tested finite range.

## What is corrected

The historical model assigned all expected prime mass in one birth interval the packet lifetime of the interval midpoint. At aggregate level this approximation is accurate. At cofactor-row level it introduces a large deterministic, highly coherent lifetime mismatch.

Subsequent diagnostics showed that this mismatch generated:

- approximately 96% of the oversized cofactor diagonal in the dominant `N=5000` band;
- the reported 99.5% top singular mode;
- the apparent low-rank Mellin structure;
- the apparent need for a Möbius-weighted power-saving off-diagonal theorem.

Those conclusions do not describe the pure prime-count discrepancy.

## Canonical replacement

At time `t` and odd cofactor `c`, define

```text
L(t,c) = max(t+2, ceil((t+1)^2/(2c)))
U(t,c) = floor(((t+1)^2-1)/c).
```

A compressed high packet with canonical cofactor `c` is active at time `t` exactly when its largest prime factor lies in `[L(t,c),U(t,c)]`.

The canonical deterministic model integrates prime density over that exact active interval:

```text
H_hat_active(t,c)
  = -mu(c) * integral_[L(t,c)-1/2]^[U(t,c)+1/2] dq/log(q).
```

The corrected residual is the prime-count discrepancy on the same exact interval. The historical midpoint-lifetime mismatch is moved into the complementary main term.

## Corrected finite finding

For the exact-activity prime discrepancy, the largest sign-blind dyadic-band diagonal divided by `HN^2` decreases from approximately `0.00223` at `N=1000` to `0.000667` at `N=200000` over the tested large-cofactor range. The pure discrepancy is not near rank one and its leading right singular vector is not well represented by a single real Mellin mode.

These are finite diagnostics only. The new analytic target is a sign-blind averaged short-prime-interval variance bound for the exact reciprocal interval family.

## Formalization consequence

The next exact Lean layer should prove the activity equivalence

```text
packetActive(t,c,q) <-> L(t,c) <= q and q <= U(t,c)
```

under the canonical odd-cofactor/prime hypotheses, and then reindex the exact high packet process by the active-prime interval. The variance estimate should remain an explicit open proposition used only through a conditional bridge.

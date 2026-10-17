# RH_Lean Coordinator synthesis - 2026-10-17

**Status:** IN_PROGRESS
**Run ID:** 2026-10-17T19:09:01-04:00, scheduled invocation
**Authority:** `main@827b291f16992d9f98e22338b1e01f932218600e`; `agent-reports@914e6c431203fb71b356e15bdee23d5da00549b6` at intake.
**Canonical objective:** `VFCanonicalSquareVonKochStatement` remains OPEN.
**Active directive:** merged PR #970, complete signed Mobius covariance.

## A. What changed mathematically?

A new exact obstruction was proved for the most natural local sign-reversing prime toggle. For every prime `p` and integer `N>=1`,
```text
sum_(N/p < n <= N, p does not divide n) mu(n) = M(N).
```
Pairing a `p`-free integer `m<=N/p` with `pm` cancels their opposite Mobius signs; the displayed upper boundary is exactly what remains. Thus a fixed-prime toggle does not reduce the problem: it transports the complete Mertens sum to its unmatched boundary. Any valid gain must couple different primes/boundary faces or introduce a genuinely nonlocal signed input. Status: `PAPER_PROOF / IDENTITY_ONLY / LOCAL-MECHANISM NO-GO`. An independent integer regression checked every `N<=500` for `p=2,3,5,7,11,13,17,19`.

## B. Live state requiring completion

- PRs #967, #968, #970 are merged to `main`; their exact heads have green CI.
- PR #969 is marked merged, but its base is the #968 feature branch and its three files are absent from current `main`. Exact ancestry/status must be recorded without upgrading it to `PROVED_IN_LEAN_ON_MAIN`.
- Today's Wheel, Census, Referee and Lean reports exist but predate the covariance pivot. Today's Owner, Analytic and Coordinator reports were absent at intake and remain `PENDING`.
- The weighted covariance identity and diagonal p-series are compiled on main through #968. The weighted-L2/Mellin bridge remains explicit and open.

## C. Next work in this invocation

Complete the exponent/dependency DAG; compare shell energy, full covariance/gcd incidence, and the Hecke low-quotient comparator; state a single shared mechanism and falsifier; allocate nonredundant next specialist questions; refresh exact PR/CI state; then replace this checkpoint at both compatibility paths with a verified final synthesis.

No quantitative Mobius exponent improvement or RH proof is claimed.

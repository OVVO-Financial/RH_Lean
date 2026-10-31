# RH_Lean Coordinator research report - 2026-10-31

**Status:** IN_PROGRESS
**Role:** RH | Proof Architect
**Invocation:** scheduled run begun 2026-10-31 07:10 America/New_York
**Checkpoint:** 2026-10-31 07:14 America/New_York
**Pinned main:** `6b2a869750b92fcdbebff78a591e7722b4f2c747`
**Authority blobs:** `AGENTS.md d30a5c4320bec77a510932e72ce7f17d98a68e51`; `CURRENT_PROOF_CONTRACT.md 7a067ec0423a998e1079e37494061346d8ee02b0`
**Report branch intake:** all six 2026-10-31 specialist reports present; all available 2026-10-30 reports consumed; 2026-10-30 Owner report absent and not inferred.

## A. What changed mathematically?

A source-faithful coefficient-weighted root-period estimate has survived the first audit. With the actual moving coefficient
[
\beta_R(n)=\sum_{1\le a<b<R,\,ab=n}\mu(a)\mu(b)
]
and corrected resonance
[
\delta(R,j,k)=\gcd(j^2,jR+k),
]
the candidate theorem is
[
\sum_{H\le R<2H}\delta(R,j,k)|\beta_R(jR+k)|^2
\ll_\varepsilon ((2j+1)H)^\varepsilon
(H+j)\gcd(j,k)\tau(j)
]
for (H\ge2), (j\ge1), (0\le k<H). The proof combines the exact period-average formula accepted today with the elementary divisor bound on the literal moving coefficient. This controls the resonance-admission diagonal; it does not prove the signed incomplete quadratic moment, the complete shell bound, a fixed positive eta, the canonical VF estimate, or RH.

## B. Live frontier

- The near first moving band (1\le k\le\sqrt R) is paid at (H^{2+o(1)}) by accepted claim `20261031-analytic-1`.
- Complete inverse-weighted owner fibres have no positive owner-prime decay by accepted claim `20261031-owner-1`.
- The old root-independent resonance identity is refuted by `20261031-wheel-1`; the exact root-period average in `20261031-referee-2` keeps a root-averaged mechanism viable.
- PR #1060 is open, green at head `80ee69a861398007046e35b79f7040e923078942`, review-ready, and unmerged.
- The complete original-source shell bound and every fixed exponent gain remain OPEN.

Full portfolio, proof, route coverage, assignments, and publication verification are being completed.

# RH_Lean Coordinator research report - 2026-10-31

**Status:** IN_PROGRESS continuation at 15:13 America/New_York  
**Live main:** `05c3fcfc2ad699f09d7d473f17ac63a918a3aad3`  
**Authority:** `AGENTS.md` blob `d30a5c4320bec77a510932e72ce7f17d98a68e51`; `CURRENT_PROOF_CONTRACT.md` blob `7a067ec0423a998e1079e37494061346d8ee02b0`  
**Prior completed synthesis retained:** claim `20261031-coordinator-1`, accepted with scope by `20261031-referee-4`.  
**Candidate continuation claim:** `20261031-coordinator-2`.

## A. What changed mathematically?

The coherent positive semiprime block from `20261031-analytic-2` has an exact legal factor-depth completion. For a prime (q<R), put
[
 X=R^2-1,quad L=lfloor(R-1)/2floor,quad A_q=lfloor X/(2q)floor.
]
The original admitted pairs ((2m,q)), with (mle L) odd, contribute after continuous-minus-fractional reassembly
[
 T_R(q)=2sum_{substack{mle L\m {m odd}}}mu(m)lfloor A_q/mfloor.
]
The (m=1) term is exactly the positive ((2,q)) obstruction. The complete odd-Mobius identity gives
[
 T_R(q)=2left(1+lfloorlog_2 A_qfloor-
 sum_{substack{L<mle A_q\m {m odd}}}mu(m)ight).
]
Thus for (R-U<q<R), (Ule R/2), the full legal ray is
(O(U+log R)), not order (R). Summing over at most (U) primes and taking (U=lfloor R^{1/3}floor) gives a pointwise (O(R^{2/3})) completed-ray bound and dyadic energy (O(H^{7/3})=O(H^{5/2-1/6})).

This is a candidate `PAPER_PROOF_NEEDS_INDEPENDENT_REVIEW`. It is a fixed positive-eta gain only for the named completed near-root prime-ray subsector. The complete source, canonical VF theorem, strict global exponent below (7/8), and RH remain OPEN.

## B. Continuity and exact carrier

All October 31 specialist reports and the October 30 carry-forward set were read. External inbox blob `038018145c0fddb2f6306c0712373adf9cd1ea52` has no handoff newer than October 18. The exact carrier is `research/EULER_FRACTIONAL_COUPLED_20261027.lean` blob `e6c4b1690e497760d366e36b28a1f7aa60e19f85`, especially the compiled continuous-minus-fractional floor identity and the original strict off-diagonal source.

## C. Remaining work before completion

- finish the quantifiers, endpoint bounds, no-duplication proof, and no-circularity audit;
- compare the mechanism against root-period, factor-depth, and MU-LIFT routes;
- record the post-`20261031-owner-2` through `referee-6` specialist findings;
- verify PR #1062 exact head and CI;
- publish byte-identical PM/AM reports and verify GitHub readback.

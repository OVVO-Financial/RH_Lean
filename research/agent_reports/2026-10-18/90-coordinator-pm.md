# RH_Lean Coordinator synthesis - 2026-10-18

**Status:** IN_PROGRESS
**Run ID:** 2026-10-18T11:55:28-04:00, scheduled invocation
**Checkpoint:** 2026-10-18T11:59:14-04:00
**Agent:** RH | Research Coordinator / Proof Architect
**Reporting rule:** `00-coordinator-am.md` and `90-coordinator-pm.md` are byte-identical compatibility mirrors of this one run, not two executions.

## A. What changed mathematically?

A new PNT-scale obstruction has been isolated by combining the merged PNT-first shell carrier with the merged #978 half-run anchor localization.

For
[
P_r(c)=\pi(\lfloor((r+1)^2-1)/c\rfloor)-\pi(\lfloor r^2/c\rfloor),
]
the only cofactor-window tops reaching the original #915 half-run for large roots are `c=1,2,3`. Their literal contribution to
(delta_r=a_r^{smooth}-\sum_c\mu(c)P_r(c)) is
[
A_r^{anchor}=-P_r(1)+P_r(2)+P_r(3).
]
On every dyadic block, the fixed-`c` shell intervals telescope, and square-boundary exclusions contribute no primes outside finite base cases. Ordinary PNT therefore gives
[
\sum_{H\le r<2H}A_r^{anchor}
\sim {3H^2\over2\log H}(-1+1/2+1/3)
=-{H^2\over4\log H}.
]
Thus the anchor-visible high-prime modes have a coherent nonzero main term. They cannot by themselves be the missing restorative payment. Any direct original-#915 use of the new renewal coordinates must transport compensation from `c>=4` through the compressed historical anchor, or use a source-legal smooth/cross-owner term. This is a scoped no-go, not a Mertens or VF bound.

**Evidence status:** `PAPER_PROOF / PNT-SCALE LOCAL-MECHANISM NO-GO`; finite exact checks at `H=16,32,...,2048` are all negative, with ((\log H/H^2)\sum A_r^{anchor}) moving from `-0.075813` to `-0.170231`. Independent referee review remains required.

## B. Current proof objective and authority

- Live `main@5ae5a524ca447d1936e351bbbe4b134c068a1a13` (merge of #979).
- Canonical open theorem: `VFCanonicalSquareVonKochStatement`.
- `AGENTS.md` blob and live contract were read at the exact head; contract blob `2fa9931dcdc1fc8a816aefb8aa348db12ee9a384`.
- Merged #977 makes the PNT-first signed cofactor/historical-return seam primary.
- Merged #979 adds the two-scale `S=A-T` attack plan; it is an experiment contract, not a signed estimate.
- Merged #978 proves exact Lambda-hyperbola, historical model, and half-run anchor localization interfaces; exact head `ba89ca4e5fc6a341ca0422698ec40b4646480000` has all ten returned workflows successful.
- No open PR existed at the checkpoint.

## C. Continuity checkpoint

Today's Wheel, Census, Referee, and Lean reports were read from blobs `62da494755501409879e894779d026aed70835f8`, `08d80d6fe5f8114e210d6e50f5939603a511994e`, `096513f9a32d79bc6699719fcac3c997572b31f0`, and `0ed62011c7a02051b634928b10ef670380033e34`. Today's Owner and Analytic reports are absent and remain `PENDING`. The complete 2026-10-17 report set and `EXTERNAL_HANDOFFS.md` were consumed as carry-forward evidence.

The final mechanism portfolio, no-circularity audit, specialist assignments, and exact publication readback will follow in this same report.

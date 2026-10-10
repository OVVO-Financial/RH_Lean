# VF-mid: canonical c₀ alignment of **discrete** square-block staircases

**Formalization / research contract — 2026-10-10, PR #925.**
This note corrects a recurrent misidentification: **VF does not obtain its
arithmetic content by smoothing a continuous prime-count model.**
The primary data are the DISCRETE sequence of complete square-block masses
and genuine integer prime/sieve events. The continuous \`vfMid\` curve is an
additional midpoint-based interpolation, used for the Li bridge. Its
continuity is not a hypothesis about the true discrete arithmetic process.

## 1. Three distinct objects (never silently substitute them)

Write
\[
m_R=\frac{2R+1}{\log(R^2+R+\tfrac12)},\qquad
F_R=\sum_{r=2}^{R-1}m_r,\qquad
P_R=\pi((R+1)^2)-\pi(R^2).
\]

1. **Fundamental discrete block sequence:** \(R\mapsto F_R\), with
   \(F_{R+1}-F_R=m_R\). Its parameters are the integer square-block
   indices \(R=\lfloor\sqrt x\rfloor\), *not* continuous time.
   Code: \`vfMidFinishedMass\`, \`vfMidBandMass\` in
   \`VF_MID_VON_KOCH_BRIDGE.lean\`.
2. **Integer-aligned square-block step graph:**
   \[
   K_R(c)=\lfloor F_R+c\rfloor,\quad
   c_0:=\pi(9)-F_3=4-\frac5{\log(13/2)}
       =1.328777548342988\ldots.
   \]
   This is a genuine *integer staircase on square-root indices*,
   vertically aligned at \(x=9\).
   Code: \`vfMidAlignedIntegerBlockLevel\`,
   \`vfMidInitialAnchor\`, \`vfMidAlignedMass_initialAnchor_three\`
   in \`VF_MID_ALIGNED_STEP_GRAPH.lean\`.
3. **Parity-aligned within-block fractional staircase:** after the
   exact parity sieve, the open R-th square block has exactly R ODD
   original candidate seats. Assign each of those sites the original
   fixed fractional VF mass
   \[
   w_R=m_R/R,\quad
   S_R(x)=F_R+w_R\#\{n:\ R^2<n<(R+1)^2,\
     n\text{ odd},\ n\le x\}.
   \]
   This is a canonical *fractional site-placement* realization of
   the block mass (not another definition of \(\pi\)):
   \(\sum_{\text{R original odd sites}} w_R=m_R\).
   Code: \`vfMidOddCandidateSeats\`,
   \`vfMidOddCandidateSeats_card\`,
   \`vfMidOddFractionalPrimeSeatWeight_sum\` in
   \`VF_MID_ODD_FRACTIONAL_CLUSTER.lean\`.
   **Do not conflate the within-block fractional staircase** with the
   separately floored *one-level-per-square-root* staircase K_R(c).
4. **Optional continuous interpolant:** \`vfMid x =
   F_R+(x-R^2)/\log((R^2+x)/2)\`, for
   \(R=\lfloor\sqrt x\rfloor\) and \(x\ge4\).
   At \(x=R^2\) it equals \(F_R\); in the interior it is
   generally **NOT** the discrete \(S_R(x)\) or \(K_R(c)\).
   It is used for the unconditional VF-to-Li quadrature bridge,
   not as the source of the original prime/sieve events.

The canonical actual-prime endpoint defect remains
\(D_R:=\pi(R^2)-F_R\) with recurrence
\[
D_{R+1}=D_R+(P_R-m_R).
\tag{A}
\]

## 2. Exact c₀ rounding-phase bookkeeping: no rescaling

The additive phase \(c_0\) is a **vertical translation**, NOT a
multiplicative calibration factor. For general \(c\ge0\), put
\[
\epsilon_R(c):=(F_R+c)-K_R(c)=\{F_R+c\},\qquad
0\le\epsilon_R(c)<1.
\tag{B}
\]
The rounding remainder \(\epsilon_R\) must not be confused with
the *arithmetic prime-minus-VF defect* \(D_R\).

Exact identities, now explicitly proved in
\`VF_MID_ALIGNED_STEP_GRAPH.lean\`:

\[
\boxed{
K_{R+1}(c)-K_R(c)
=m_R+\epsilon_R(c)-\epsilon_{R+1}(c).
}
\tag{C}
\]
In particular, the aligned integer increment differs from the
original VF block mass by **strictly less than one**, but can have
either rounding sign. No \(\pi\), density hypothesis, or RH assumption
enters this identity.

Let \(B_R(c):=K_R(c)-\pi(R^2)\) be the genuinely arithmetic
integer backlog. Then
\[
\boxed{
B_R(c)=-D_R+c-\epsilon_R(c),
\quad
B_{R+1}(c)-B_R(c)
=m_R-P_R+\epsilon_R(c)-\epsilon_{R+1}(c).
}
\tag{D}
\]
Most importantly, over ANY range \(A\le B\) of consecutive
square blocks,
\[
\boxed{
B_B(c)-B_A(c)
=-(D_B-D_A)-(\epsilon_B(c)-\epsilon_A(c)).
}
\tag{E}
\]
The **constant c cancels exactly** from cumulative increments.
Because the two end phases lie in [0,1), the total extra rounding
difference has absolute value <1, regardless of the number of
blocks in the range.

Consequently c₀ can align the plotted staircase and supply a
bounded endpoint allowance, but **cannot supply the open
RH-strength arithmetic cancellation**. That cancellation is carried
by actual signed \(P_R-m_R\), including its native prime-factor
inheritance and original weighted Sector Six packet.

The associated Lean declarations are
\`vfMidAlignedRoundingPhase\`,
\`vfMidAlignedRoundingPhase_bounds\`,
\`vfMidAlignedIntegerBlockLevel_succ_real\`,
\`vfMidAlignedIntegerBlockLevel_stepError_abs_lt_one\`,
\`vfMidAlignedIntegerBacklog\`,
\`vfMidAlignedIntegerBacklog_eq_direct_error_phase\`,
\`vfMidAlignedIntegerBacklog_succ\`,
and \`vfMidAlignedIntegerBacklog_interval_eq_direct_error_phase\`.

## 3. What the aligned STEP-GRAPH actually tests

The plotted graph contains **horizontal block faces** and
**vertical boundary jumps**. The three native predicates are:

* Horizontal face in block R:
  \(\pi(R^2)\le K_R(c)\le\pi((R+1)^2)\).
* Left vertical face:
  \(K_{R-1}(c)\le\pi(R^2)\le K_R(c)\).
* Right vertical face:
  \(K_R(c)\le\pi((R+1)^2)\le K_{R+1}(c)\).

\`VFMidAlignedStepGraphCrossed\` is their disjunction. A
full-graph crossing is **not** equality \(F_R+c=\pi(R^2)\);
nor does it imply one specific crossing orientation in every
block.

A one-time c₀ alignment at x=9 affects all plotted levels equally.
It does not alter the raw \(m_R\), the FTA wheel identifying
each genuine prime, the parity count R, or any historical
prime-parent charged occurrence.

## 4. Reproducible EXACT prime-count finite diagnostics

Independent integer-sieve reproduction of
\`scripts/VFMidAlignedStepGraph/verify.py\`, for all
\(R=2,\ldots,10{,}000\) (9,999 square blocks), produces:

| Test | Result |
|---|---:|
| Canonical \(c_0=4-5/\log(6.5)\) | 1.3287775483429884 |
| c₀ full-graph failures | **0** |
| c₀ horizontal crossings | 9,994 |
| c₀ left-vertical-only rescues | 4 |
| c₀ right-vertical-only rescues | 1 |
| c=0 full-graph failures | 3, first at R=2,3,4 |
| Good phase grid, step 0.001, scanning 0.000–3.000 | **1.329–1.865**, 537 values |

The canonical c₀ is slightly BELOW the first successful
0.001-grid point simply because **1.328777... lies between
grid points**; it passes by a separate direct test.
The grid interval is a finite numerical finding, not an
exact analytic maximal interval, nor a universal bound on c.

Concrete genuine-prime checkpoints:

| R | \(\pi(R^2)\) | \(F_R\) | \(K_R(c_0)\) | \(B_R(c_0)\) |
|---:|---:|---:|---:|---:|
| 3 | 4 | 2.671222452 | 4 | 0 |
| 17 | 61 | 63.275274344 | 64 | 3 |
| 317 | 9,631 | 9,669.131636076 | 9,670 | 39 |
| 1027 | 82,462 | 82,578.133854051 | 82,579 | 117 |

Both the exact counter and the independent full-graph
finite diagnostic are replayable using
\`scripts/VFMidAlignedStepGraph/verify_c0_contract.py\`.
This is **evidence about finite crossing geometry**, never
a theorem about all square roots.

## 5. Nonnegotiable proof scope

The actual outstanding RH criterion remains the signed
square-endpoint tracking estimate
\[
|\pi(R^2)-F_R|\le C R\log R.
\tag{F}
\]
A single fixed phase cannot be assumed to cross the prime
staircase in **every** block forever; that would imply a
stronger one-sided \(\sqrt x/\log x\)-scale bound
incompatible with the known positive Littlewood oscillation
of \(\pi(x)-\mathrm{Li}(x)\) (see \`CURRENT_PROOF_CONTRACT.md\`).

Therefore: distinguish
(1) exact block-geometry and integer-floor phase,
(2) tested finite c₀ crossing,
(3) actual signed Möbius/prime-owner inheritance,
(4) the still-open original native Sector Six quantitative
first-bad payment. **The first two cannot be substituted
for the fourth.**

This note supplements, rather than changes,
\`research/VF_WILES_PARENT_ROOT_QUADRATIC_LAW.md\`:
the multiplicative \(1/\sqrt c\) parent-window contraction is
an exact geometric phenomenon, while c₀ is an additive
one-time *vertical* alignment, and neither supplies a new
universal bound on actual prime distribution by itself.

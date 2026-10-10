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

## 5. The sqrt(2) test and an unconditional fixed-phase no-go

The suggestion \(c=\sqrt2\) is natural to TEST because factor-2
ancestry rescales the *square-root coordinate* by \(1/\sqrt2\).
But this multiplicative contraction does not imply a unique additive
VF prime-count shift. In fact the canonical x=9 real anchor is
\(c_0=4-5/\log(13/2)\approx1.328777548\ne\sqrt2\).

Removing the prime 2 from actual \(\pi(x)\), for x>=2, changes the
count by **exactly 1**, not sqrt(2). More explicitly,
\[
c_0=4-m_2
=\underbrace{1}_{\text{prime 2}}
  +\underbrace{(3-m_2)}_{\text{remaining anchor discrepancy}}.
\]
Thus the first prime is *not* an independent derivation of sqrt(2)
as a count-space phase.

### Exact finite red-team: sqrt(2) also crosses every sampled block

The updated authentic-prime script
\`scripts/VFMidAlignedStepGraph/verify_c0_contract.py\` uses
the **original unaltered VF sequence** and \(\pi(R^2)\), and
independently measures the graph for \(c=\sqrt2\):

* \(R=2,\ldots,10000\): 9999 tested blocks.
* \(c=c_0\): 9994 horizontal; 4 left-only; 1 right-only; 0 failures.
* \(c=\sqrt2\): **identical crossing-mode counts** and 0 failures.
* **863 out of the 10000 integer square-root levels** R=2..10001
  differ between \(K_R(c_0)\) and \(K_R(\sqrt2)\).
* First such difference: R=6, \(\pi(36)=11\),
  \(F_6\approx11.640926795663164\),
  \(K_6(c_0)=12\), \(K_6(\sqrt2)=13\).
* Fixed alignment shift:
  \(\sqrt2-c_0\approx0.0854360140301067\).

Therefore the finite crossing property does **not** select
sqrt(2), nor does a visually successful phase identify the
owner-2 arithmetic correction uniquely. Both phases can cross
while producing different integer *increments* on some blocks.
The original real-valued \(m_R\) remains the same.

### Uniform midpoint quadrature: the actual square-block integration
error is O(1) at square endpoints

This sharpens the existing coarse O(sqrt(x)) quadrature bridge
*at the original square endpoints* without needing any prime
distribution or RH assumption. Put \(f(t)=1/\log t\). Then
\[
f''(t)=\frac{\log t+2}{t^2(\log t)^3}>0,\quad t>1.
\]
For the r-th square band of width \(h_r=2r+1\) and midpoint
\(u_r=r^2+r+\frac12\), midpoint quadrature says
\[
0\le\delta_r:=
\int_{r^2}^{(r+1)^2}f(t)\,dt-h_r f(u_r)
\le \frac{h_r^3}{24}
   \sup_{r^2\le t\le (r+1)^2}|f''(t)|
=O\left(\frac1{r\log^2 r}\right).
\]
The upper-bound series \(\sum_{r\ge2}1/(r\log^2 r)\)
converges. Hence the exact **actual midpoint VF** obeys
\[
\boxed{
F_R=\operatorname{Li}_2(R^2)-C_{\rm mid}
       +O(1/\log R),\qquad
C_{\rm mid}:=\int_2^4f(t)\,dt+\sum_{r=2}^\infty\delta_r>0
}
\]
and in particular \(|F_R-\operatorname{Li}_2(R^2)|=O(1)\).
Here \(\operatorname{Li}_2(x)=\int_2^x dt/\log t\).
The remainder from the convergent tail is O(1/log R)
by the integral test.

Numerically, \(F_R-\operatorname{Li}_2(R^2)\) equals
\(-2.078328519\) at R=17, \(-2.097198532\) at R=317,
\(-2.100041334\) at R=1027 and \(-2.103386266\)
at R=10000. The true
\(\pi(10000^2)-F_{10000}\approx-751.226898\),
far larger than the ~2.10 constant midpoint quadrature offset.
It cannot be attributed to the midpoint discretization or to
the 0.0854 change from c0 to sqrt2.

**Status:** this is a paper-level calculus proof included for
research use. The sharpened O(1) endpoint estimate has NOT
yet been kernel-formalized in Lean; the existing weaker
VF/Li bridge remains the compiled theorem.

### No fixed additive phase can cross in ALL sufficiently large blocks

The following **unconditional mathematical no-go**, using
classical Littlewood oscillation, rules out the proposed
universal \(\sqrt2\) statement (and EVERY other fixed c).
It is stronger than the previous "not yet proved" warning:

> For every real constant c, there are infinitely many R such
> that the full three-mode aligned step-graph predicate
> \`VFMidAlignedStepGraphCrossed c R\` fails.

**Proof outline.** Suppose, contrariwise, that some fixed
c makes the graph cross every block R>=R0.
Write \(K_R=K_R(c)=\lfloor F_R+c\rfloor\).
The three source-native horizontal/left/right crossing cases,
monotonicity of \(K_R\) and of \(\pi\), applied in the two
adjacent blocks R-1 and R, give for all R>=R0+1:
\[
\boxed{K_{R-2}\le\pi(R^2)\le K_{R+1}.}
\tag{G}
\]
The lower inequality is supplied by the crossing in block R-1;
the upper inequality by the crossing in block R.
For example, in the right-vertical case on block R,
\(\pi(R^2)\le\pi((R+1)^2)\le K_{R+1}\).
The other cases are immediate from the definitions.

Since \(m_R=F_{R+1}-F_R=O(R/\log R)\),
the width of the G sandwich is O(R/log R).
The constant c and all floor errors contribute only O_c(1).
Together with the proved-on-paper
\(F_R=\operatorname{Li}_2(R^2)+O(1)\), this forces
\[
\pi(R^2)-\operatorname{Li}_2(R^2)=O(R/\log R).
\]
For every real \(x\in[R^2,(R+1)^2]\),
monotonicity of \(\pi(x)\) and of \(\operatorname{Li}_2(x)\)
then extends it to
\[
\pi(x)-\operatorname{Li}_2(x)
=O(\sqrt x/\log x).
\]
But the **unconditional** classical Littlewood theorem gives
\[
\pi(x)-\operatorname{li}(x)
=\Omega_\pm\left(
 \frac{\sqrt x}{\log x}\log\log\log x\right),
\]
and \(\operatorname{li}\) differs from \(\operatorname{Li}_2\)
by only a constant. Contradiction. QED.

**Formalization boundary:** the local two-block sandwich
(G) is a natural, finite Lean theorem, but the global
no-go also imports analytic calculus/summability and the
classical Littlewood result. Neither this mathematical proof
outline nor the finite sqrt2 check should be represented as
a kernel-checked infinite no-go theorem until those results
are fully imported and compiled.

The valid RH-scale goal remains
\(|\pi(R^2)-F_R|=O(R\log R)\), which is vastly weaker
than universal fixed-phase crossing and is not contradicted
by Littlewood.

## 6. Nonnegotiable proof scope

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

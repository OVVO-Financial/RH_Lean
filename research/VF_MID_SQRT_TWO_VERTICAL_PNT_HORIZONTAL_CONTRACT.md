# Chosen c0 = sqrt(2): vertical phase and proven PNT horizontal resolution

**2026-10-10, PR #925.** This is a research/proof contract, not RH closure.

The chosen vertical phase for the new route is c0 = sqrt(2).
It is an *additive convention*, NOT an asserted identity with the
historical exact x=9 real-valued anchor
c_anchor = 4 - 5 / log(13/2) = 1.328777548... .
Both phases have been numerically successful through R=10000;
they are not equal. Existing exact anchor theorems remain intact.

Actual primes are already exactly defined in arithmetic:
Nat.Prime, and Nat.primeCounting is the actual count. The exact
square-root/Fundamental-Theorem-of-Arithmetic wheel is in
VF_MID_SQUARE_WHEEL_BACKLOG.lean. Unknown is the necessary quantitative
prime *distribution*, not the definition of primes.

## I. Vertical c0 does not change actual VF block masses

Let
\[
F_R=\sum_{r=2}^{R-1}m_r,\qquad
m_R=\frac{2R+1}{\log(R^2+R+\tfrac12)},\qquad
K_R=\lfloor F_R+\sqrt2\rfloor.
\]
New Lean names: vfMidChosenC0, vfMidSqrtTwoVerticalPhase,
vfMidSqrtTwoIntegerLevel.

Write epsilon_R = F_R + sqrt(2) - K_R in [0,1). Then exactly
\[
K_{R+1}-K_R=m_R+\epsilon_R-\epsilon_{R+1}.
\]
The constant phase changes neither original m_R nor genuine
prime population P_R, and the rounding correction telescopes.
Existing native Lean phase identities are reused, not postulated
as a mechanism paying Sector Six.

The authentic-prime numerical replay at R=2..10000 gives
0 full-graph misses with either c0 or sqrt(2), and precisely
9994 horizontal, 4 left-vertical-only, and 1 right-vertical-only
crossings for each phase. Nevertheless the integer VF levels
differ at 863 square-root indices. Thus no unique vertical
phase follows from this finite alignment experiment.

## II. Two DIFFERENT horizontal notions

First, horizontal graph crossing INSIDE ONE square block is
\[
\boxed{\pi(R^2)\le K_R\le\pi((R+1)^2).}\tag{H1}
\]
Lean VFMidSqrtTwoHorizontalCrossed.
The exact native prime-supply theorem translates this to
\[
\pi(R^2)\le K_R\le \pi(R^2)+P_R,
\quad P_R=\#\{p\text{ actual prime}:R^2<p<(R+1)^2\}.
\tag{H2}
\]
Lean vfMidSqrtTwoHorizontalCrossed_iff_actualWheel
specializes the right side to the original actual wheel.
If P_R=0, H1 is possible only if K_R=pi(R^2); that
case is explicitly formalized. NO positive supply follows
from monotonicity or PNT alone.

Second, to align a fixed actual prime height by translating
the VF *square-root clock*, allow a window L <= R <= U:
\[
\boxed{K_L\le\pi(R^2)\le K_U.}\tag{H3}
\]
Lean VFMidSqrtTwoHorizontalRootWindow L R U.
This has the EXACT signed error consequence
\[
\boxed{F_L-F_R+\sqrt2-1
<D_R\le F_U-F_R+\sqrt2,\quad
D_R=\pi(R^2)-F_R.}\tag{H4}
\]
Lean vfMidSqrtTwoHorizontalRootWindow_bounds_actualDefect.
It does not assume any bound on how narrow L,U can be.

## III. PNT is already PROVED, not an additional hypothesis

The native theorem RHLean.Analysis.nativePrimeNumberTheorem is
\[
\frac{\pi(N)\log N}{N}\longrightarrow1.
\]
The new module formally transfers this proven theorem to square
endpoints:
\[
\boxed{\frac{\pi(R^2)\log(R^2)}{R^2}\longrightarrow1,}
\]
with a proved arbitrary-percentage eventual corridor; check
vfMidSqrtTwoActualPrimeSquarePNT and
vfMidSqrtTwoActualPrimeSquarePNT_percent.

Separately, elementary VF midpoint quadrature and the standard
Li asymptotic imply (on paper)
\[
F_R\sim R^2/\log(R^2).
\]
The new native theorem
vfMidSqrtTwoRelativeHeightAlignment_of_VF_mainTerm uses an
EXPLICIT hypothesis for this independent VF asymptotic and
proves the normalized difference tends to zero. The module
does NOT purport to have imported and kernel-compiled the
VF-main-term asymptotic at this step.

Together, the PNT-scale result is
\[
\boxed{D_R=o(R^2/\log R).}
\]
The VF block derivative is m_R~R/log R, so the INVERSE
square-root clock horizontal displacement is only
\[
\boxed{\Delta R=o(R)}
\]
from PNT. This inversion is a classical analytic consequence,
not yet a separately Lean-certified inverse-clock theorem.

Our desired RH-scale difference
|D_R|=O(R log R) would correspond to the MUCH tighter
horizontal lag
\[
\boxed{|\Delta R|=O((\log R)^2)}
\]
after using the actual VF band mass growth. Proving that
tighter lag is the OPEN ARITHMETIC problem; PNT alone cannot.

The fixed c0 shift changes D_R by only O(1). It is completely
negligible relative to either PNT or RH-scale bounds.

## IV. Explicit countermodel: PNT permits infinitely many empty
square-root blocks

This demonstrates why PNT alone cannot supply the missing
within-block arithmetic estimate WITHOUT ever redefining
the actual primes in the formal proof.

For this LOGICAL counterexample only, begin with the actual
prime set and DELETE primes inside square bands with roots
R_k=2^k (k>=2). Let A(x) count the remaining selected
primes. The total integers in all deleted blocks up to x
are bounded by
\[
0\le \pi(x)-A(x)
\le \sum_{2^k\le\sqrt x}2^{k+1}=O(\sqrt x).
\]
Since sqrt(x)=o(x/log x), A obeys THE SAME PNT:
\[
A(x)\sim x/\log x.
\]
Yet A has no event in any of those infinitely many square
blocks. A is monotone and its jumps are still 0 or 1.

Therefore: PNT plus a unit-jump monotone staircase CANNOT
imply even positive supply in every square block, much
less force H1 everywhere. A is not a substitute for actual
pi and is never used as one in the Lean proofs. It is only
a counterexample to the claimed implication from PNT.

## V. Mathematical and formalization limits

The original fundamental square-block recurrence
\[
D_{R+1}=D_R+P_R-m_R
\]
remains exact. The original FTA primes and weighted Sector Six
are untouched.

* PROVED in native Lean: c0 is defined to be sqrt(2);
  exact vertical phase preservation and bounded telescope;
  exact finite horizontal root-window defect implication;
  authentic prime supply/wheel identification; square-clock
  PNT as a consequence of nativePrimeNumberTheorem.
* EXPLICIT hypothesis in Lean: separate VF main-term limit
  when deriving matched relative prime-VF heights.
* PAPER-level mathematical consequence: eventual horizontal
  lag o(R) from PNT and the elementary VF main term.
* STILL OPEN: horizontal lag O(log^2 R) or, equivalently at
  leading scale, the original O(R log R) prime-minus-VF
  bound. Littlewood oscillation also rules out a globally
  bounded one-block horizontal lag.

The next direct target is to bound the horizontal square-root
clock displacement by genuine arithmetic prime-factor
inheritance, using proven PNT as background and preserving
once-charged original signed Sector Six interactions.
No fantasy replacements and no hidden RH assumption.

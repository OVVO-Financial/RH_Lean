# Minimal first-bad parity payment — production proof contract (v2)

**Status: DRAFT, open arithmetic theorem. Not a proof of RH.**
**Base:** clean `main`, deliberately NOT the accumulated #915 feature branch.
**Supersedes for new work:** [PR #915](https://github.com/OVVO-Financial/RH_Lean/pull/915)
as the single small target for an actual signed first-bad closure.
**Fast entry point:** `python3 scripts/vf_mid_first_bad_payment_v2_test.py --extended`.
**Lean entry point:** `research/VF_MID_FIRST_BAD_PAYMENT_V2_KERNEL.lean`.
**Native consumer:** `research/VF_MID_FIRST_BAD_PAYMENT_V2_NATIVE_CONSUMER.lean`.
**Only open proof gate:** `VFMidMinimalActualFirstBadPaymentV2Statement`.

## 1. One objective, no substitute theorems

For each square block $(R^2,(R+1)^2)$, set

$$
m_R=R^2+R+\tfrac12,\qquad
V_R=\frac{2R+1}{\log m_R},\qquad w_R=\frac{V_R}{R}.
$$

$$
D_R=\pi(R^2)-VF_{\rm mid}(R^2),\qquad
P_R=\pi((R+1)^2)-\pi(R^2),\qquad C_R=R-P_R.
$$

Here $\pi(x)$ is the ACTUAL prime counting function, not a floor-Li
staircase or density proxy. Exact recursion:

$$
D_{R+1}=D_R+P_R-V_R.
\tag{1}
$$

The complete integer block contains exactly $2R$ integers, but ALL
$V_R$ reference mass resides on its exactly $R$ odd candidate seats.
This accounts for reference advance at even integers while actual
$\pi(2k)=\pi(2k-1)$ for $2k\ge4$:

$$
\boxed{w_R=V_R/R\quad\text{(never }V_R/(2R)\text{)}.}
\tag{2}
$$

Per original odd candidate $n$, the signed charge is

$$
z_R(n)=w_R-\mathbf 1_{\mathbb P}(n).
\tag{3}
$$

The full signed block is $\sum_{\rm odd}z_R=V_R-P_R$. Including
the historical anchor $-D_R$ gives **exactly** $-D_{R+1}$.
Even composites have **zero independent source mass**. No reintroduction
of $2q$, no auxiliary parity-neighbor heat, no inflated historical
absolute denominator, no fake Li "prime" event.

## 2. Exactly what production hbalance says

For $R\ge8$ define the original anchored zero-target partial masses

$$
\boxed{\begin{aligned}
U_R&=(-D_R)_+ + w_RC_R,\\
L_R&=( D_R)_+ + (1-w_R)P_R.
\end{aligned}}
\tag{4}
$$

Their signed and absolute identities (NO distributional assumptions) are

$$
U_R-L_R=-D_{R+1},\qquad
U_R+L_R=|D_R|+w_RC_R+(1-w_R)P_R.
\tag{5}
$$

The original **NNS squared anchored L1 mass**, not ordinary
statistical variance, is

$$
\boxed{
M_R^2=(U_R+L_R)^2
=\big(|D_R|+w_RC_R+(1-w_R)P_R\big)^2.
}
\tag{6}
$$

The exact original payment is

$$
\boxed{
\mathcal B_R=(U_R+L_R)^2-2(U_R-L_R)^2\ \ge 0
}
\tag{7}
$$

which is equivalent to BOTH of

$$
\boxed{2D_{R+1}^2\le M_R^2}
\tag{8}
$$

and

$$
\boxed{U_R^2+L_R^2\le 6U_RL_R.}
\tag{9}
$$

Equations (4)–(9) are algebraic and kernel-tested in the standalone
`VF_MID_FIRST_BAD_PAYMENT_V2_KERNEL.lean`. No one has proved (7)
on all actual prime blocks, nor do we assume that: the unconditional
all-state statement is **false**. The same Lean file contains a
verified scalar counterexample with $w=1/4,\ P=0,\ C=8,\ D=0$,
for which $\mathcal B=-4$. Such hypothetical scalar states are
NOT thereby asserted to occur as actual prime blocks.

### EXACT RH-strength remaining arithmetic assertion

Let $\rho_R=R\log R$ and let
$\mathrm{FirstBad}_2(R+1)$ mean:

$$
|D_{R+1}|>2\rho_{R+1},
\qquad
\forall j<R+1,\ j\ge2:\ |D_j|\le2\rho_j.
\tag{10}
$$

The one and only open arithmetic gate is

$$
\boxed{
\forall R\ge8:\quad
\mathrm{FirstBad}_2(R+1)\ \Longrightarrow\
2D_{R+1}^2\le M_R^2.
}
\tag{11}
$$

**Lean native type (defined as a `Prop`, NOT proved):**

```lean
def VFMidMinimalActualFirstBadPaymentV2Statement : Prop :=
  ∀ (R : ℕ), 8 ≤ R →
    VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1) →
      2 * vfMidActualPrimeEndpointDefect (R + 1) ^ 2 ≤
        vfMidFirstBadZeroTargetTotalMass R
```

This uses original `vfMidFirstBadZeroTargetTotalMass R`, which the
pre-existing **main** theorem
`vfMidFirstBadZeroTargetTotalMass_eq` identifies with (6).
No #915-only proxy object or new denominator appears.

## 3. Native contradiction is ALREADY conditional and compiled on main

The following green main theorems are the accepted starting point:

- `vfMidOddCandidateSeats_card`: there are exactly $R$ odd candidates.
- `vfMidOddFractionalPrimeSeatWeight_sum`: odd mass is exactly $V_R$.
- `vfMidOddSignedSeatCharge_sum`: signed physical charge tracks $V_R-P_R$.
- `vfMidFirstBadZeroTargetTotalMass_eq`: exact original denominator.
- `vfMidFirstBadNormalizedProduct_eq_nextEndpointDefect_sq`: normalized
  numerator times mass is $D_{R+1}^2$.
- `vfMidActualPrimeFirstBadAt_two_succ_half_totalMass_le_radial`:
  under first-bad, $M_R^2/2$ fits within the next radial wall.
- `vfMidActualPrimeFirstBadAt_two_succ_nnsNormalized_gt_half`:
  hypothetical first-bad forces NNS normalized correlation > $1/2$.
- `vfMidActualPrimeFirstBadAt_two_succ_finalContraction_of_nnsNormalized_le_half`:
  an authentic ≤ $1/2$ bound would contradict first-bad.

The tiny **native conditional consumer**
`vfMidMinimalActualFirstBad_closed_of_exactPaymentV2` imports
the existing main theorems. Given **(11) as an explicit hypothesis**,
the proof uses

$$
\frac12 M_R^2\ge D_{R+1}^2
=\mathcal N_R\,M_R^2
>\frac12 M_R^2,
$$

where $M_R^2>0$ under first-bad.
The contradiction is exact, but WITHOUT (11) it is not an RH proof.

Never describe the conditional consumer as the missing signed theorem.
The objective is to *derive (11)* without additional distribution
assumptions, not to rename (11), restate the normalized inequality,
or invoke a universally false cone.

## 4. Allowed arithmetic mechanism / exact missing inequality

The physical first-owner sieve is exact. Historical endpoint history
is compressed into **one scalar** $D_R$, not a fresh list of
independently spendable negative parent seats. A valid proof must
exhibit an actual prime/composite arithmetic restriction on this
compressed scalar and current $P_R$, *under (10)*, that establishes (7).

The existing main owner/Fubini modules already supply:
- finite unique least-prime owner classification, including owner 2;
- signed Möbius role of genuine owners; squareful restoring cells;
- retained-weight first-owner Fubini and boundary classes;
- three-boundary / six-sector structural reassembly;
- first-bad prior-good historical anchor controls;
- protected prime-Euler star nonexpansion in its separate carrier.

**What none supplies yet:** a weight-preserving, occurrence-matched,
global nonpositive original Co/Div excess under first-bad. Formal
$-4|z|$ local sign reversal is not the global payment without a
proved historical boundary map. One cannot drop the diagonal,
borrow restored even-site mass, replace $D_R$ by the sum of absolute
historical charges, or assume every owner sector pays separately.

The exact desired arithmetic inequality in terms of counts is

$$
\boxed{
2\big(D_R+P_R-V_R\big)^2
\le
\big(|D_R|+w_R(R-P_R)+(1-w_R)P_R\big)^2
}
\tag{12}
$$

*under (10)*. This is the only place new arithmetic proof work should go.
Do not add another equivalent source ledger without using it to prove
the inequality (12).

### Critical guardrails from #915

1. Full factor buckets $p\le\sqrt x,\ \sqrt x<p\le x/2,\ p>x/2$
   are correct for INTEGER FACTORIZATION; the odd physical carrier
   cannot credit even $2p$ as an independent NNS charge.
2. $x/3$ is only the no-ODD-descendant cutoff, not the full lattice
   terminal cutoff $x/2$.
3. A true historical $q$ with even child $2q$ still contributes
   ZERO new original odd-seat charge. Actual first-owner effects
   are already reflected in $P_R$ and $D_R$.
4. The verified wheel bound $H_R\le R-P_R$ compares cardinalities,
   not signed weights of historical prime parents; it does not pay (12).
5. Floor-Li events at composite indices are not "missing primes."
   PNT alone does not supply an RH-order second-order cancellation law.
6. All finite empirical balance/correlation checks are TESTS, not proofs.
7. The cone $\mathcal B_R\ge0$ cannot be asserted for every state
   or every sieve stage; early intermediate slacks may be negative.
8. The user-facing objective is the single *hfirst-specific* target,
   NOT an unconditional all-$R$ inequality.

## 4A. Actual pi versus floor Li on the TRUE prime-factor buckets

**Implemented directly in #918, without importing #915's heavy modules.**
The full consecutive R=8..6000 scan uses ACTUAL integer primality
from an independent sieve, plus the explicit floor-Li baseline.
The revised CI check passed all **5,993** R blocks in **0.56 seconds
of Python runtime**, including the native composite-cofactor audits.

Set X=(R+1)^2, S=R+1=sqrt(X), H=floor(X/2), and
Q(n)=floor(Li_2(n)) where Li_2(x)=integral from 2 to x of dt/log t.
Write E(n)=pi(n)-Q(n). Q is a DETERMINISTIC integer reference,
not a second prime sieve. Q-events that fall on even or composite
integers have no genuine prime owner.

The true integer-prime FACTOR buckets are exactly:

1. p<=S: all possible least-prime sieve owners (every composite
   n<=X has a prime divisor <=S).
2. S<p<=H: genuine prime factors with at least one even composite
   descendant 2p<=X, ALREADY accounted for in the reference baseline.
3. H<p<=X: truly terminal prime factors, none with a proper
   integer multiple <=X.

For R>=8, **all current physical odd primes** are in (R^2,X],
a subinterval of the terminal factor bucket (H,X]. Splitting the
terminal bucket at R^2 is essential to distinguish historical
drift already compressed in D_R from the CURRENT block error.

The corresponding signed bucket telescope is EXACT:

$$
\begin{aligned}
E(X)=E(2)
 &+[E(S)-E(2)]\\
 &+[E(H)-E(S)]\\
 &+[E(R^2)-E(H)]\\
 &+[E(X)-E(R^2)].
\end{aligned}
\tag{13}
$$

Here E(2)=1 (because pi(2)=1 while Q(2)=0). The last term,
delta_R=E(X)-E(R^2), is exactly actual P_R minus the current
floor-Li demand F_R=Q(X)-Q(R^2).

### Reproduction on ACTUAL primes

| R | low E <=sqrt X | middle E (sqrt X,X/2] | terminal historical E (X/2,R^2] | terminal CURRENT delta | E(X) |
|---:|---:|---:|---:|---:|---:|
| 119 | -4 | -13 | -5 | -6 | -27 |
| 317 | -5 | -27 | -9 | -1 | -41 |
| 1027 | -9 | -52 | -58 | -4 | -122 |
| 1760 | -9 | -98 | -55 | -32 | -193 |
| 5267 | -17 | -264 | -46 | +2 | -324 |
| 6000 | -17 | -188 | -356 | +8 | -552 |

All entries are exact integer counts of ACTUAL pi minus Q.
Example: at R=1027, 1-9-52-58-4=-122. At R=317,
1-5-27-9-1=-41. **The x/2 split works exactly**; it
does NOT independently bound terminal prime fluctuations.

### Put Q back into the ORIGINAL first-bad inequality

The deterministic square-endpoint bridge is b_R=Q(R^2)-VF_mid(R^2).
The ACTUAL anchor is

$$
D_R=b_R+E(R^2),\qquad
P_R=F_R+\delta_R,\qquad
D_{R+1}=D_R+F_R+\delta_R-V_R.
\tag{14}
$$

Hold the **ACTUAL** D_R fixed. Using F_R in place of P_R defines
a comparison count, not an imagined real prime arrangement.

Let

$$
\begin{aligned}
M_R^0&=|D_R|+w_RR+(1-2w_R)F_R,\\
Y_R^0&=D_R+F_R-V_R,\\
G_R^+&=M_R^0+\sqrt2Y_R^0,\\
G_R^-&=M_R^0-\sqrt2Y_R^0.
\end{aligned}
\tag{15}
$$

Because P_R=F_R+delta_R, the TWO actual signed cone margins are

$$
\boxed{\begin{aligned}
M_R+\sqrt2D_{R+1}
 &=G_R^++(1-2w_R+\sqrt2)\delta_R,\\
M_R-\sqrt2D_{R+1}
 &=G_R^-+(1-2w_R-\sqrt2)\delta_R.
\end{aligned}}
\tag{16}
$$

and their product is **literally the original** hbalance:

$$
\boxed{\mathcal B_R
 =(M_R+\sqrt2D_{R+1})(M_R-\sqrt2D_{R+1}).}
\tag{17}
$$

There is NO new denominator and NO separate even 2p negative heat.
For R>=8, w_R<1/2. Thus the admissible ACTUAL signed
current error interval (conditioned on the already ACTUAL D_R) is

$$
\boxed{
-\frac{G_R^+}{1-2w_R+\sqrt2}
 \ \le\ \delta_R\ \le\
 \frac{G_R^-}{\sqrt2-1+2w_R}.
}
\tag{18}
$$

All these identities and the conditional **two-margin certificate**
are in \`VF_MID_FIRST_BAD_PAYMENT_V2_KERNEL.lean\`:
\`vfV2LiPlus_actual\`, \`vfV2LiMinus_actual\`,
\`vfV2Balance_factor\`,
\`vfV2Payment_of_floorLi_actual_signed_bounds\`.
The certificate is algebra, not an unconditional assertion that (18)
always holds for genuine prime counts.

**Actual error tolerance and observations** (rounded only for display):

| R | actual P_R | floor-Li F_R | delta_R | allowed actual signed delta interval | actual NNS |
|---:|---:|---:|---:|---|---:|
| 119 | 19 | 25 | -6 | [-15.870,102.230] | 0.206054 |
| 317 | 54 | 55 | -1 | [-36.309,240.453] | 0.093334 |
| 1027 | 144 | 148 | -4 | [-96.498,759.962] | 0.107592 |
| 1760 | 204 | 236 | -32 | [-159.763,1162.700] | 0.123155 |
| 5267 | 617 | 615 | +2 | [-436.565,2887.044] | 0.052116 |
| 6000 | 698 | 690 | +8 | [-453.228,3989.729] | 0.095024 |

Over R=8..6000 the largest |delta_R| was 61 at R=5266.
There were **zero** failing actual signed margins, while the
tightest normalized actual covariance was 0.206054 at R=119.
These are finite demonstrations that the floor-Li placement
works with genuine pi, **not** a proof of a uniform δ-bound.

### Native odd-composite cofactor Fubini, without 2p charging

For each ODD c>=3, actual q>R prime descendants n=cq in the current
open band are counted by the true interval

$$
\max(R,\lfloor R^2/c\rfloor)
 <q\le\lfloor((R+1)^2-1)/c\rfloor.
$$

Define A_c=actual pi interval, F_c=floor-Li interval *reference*;
each event A_c is a genuine PRIME q but the floor-Li events F_c
may be at composites. Let G=sum A_c, G_Li=sum F_c,
and let S=R-P_R-G, S_Li=R-F_R-G_Li be the respective actual
smooth-composite population and formal benchmark complement.

The three signed error populations obey

$$
\delta_P+\delta_G+\delta_S=0.
$$

Keeping the NATIVE VF odd-seat weights, the correction is

$$
\boxed{
(w_R-1)\delta_P+w_R\delta_G+w_R\delta_S=-\delta_P.
}
\tag{19}
$$

This is an exact one-block restoration identity. It neither
creates negative physical capacity nor bounds δ_P.
The corresponding algebraic Lean theorem is
\`vfV2OddCohortFloorLi_restores_primeError\`.

| R | actual high-q odd composites G | floor-Li cofactor events G_Li | error (G-G_Li) | signed cofactor-window + / - |
|---:|---:|---:|---:|---:|
| 119 | 80 | 72 | +8 | +24 / -16 |
| 317 | 192 | 204 | -12 | +50 / -62 |
| 1027 | 659 | 648 | +11 | +144 / -133 |
| 1760 | 1169 | 1134 | +35 | +291 / -256 |
| 5267 | 3400 | 3411 | -11 | +735 / -746 |
| 6000 | 3878 | 3882 | -4 | +895 / -899 |

The current odd-site population identities and weighted restoration
are verified independently, not inferred from square-endpoint totals.
The current weighted cofactor sign fluctuates:
R=317 contributes w*(-12)=-2.086446;
R=1027 contributes w*(+11)=+1.586956.

**Proof status:** Both signed bucket transports and the actual-prime
numerical matches hold. Neither exact telescope (13) nor weighted
conservation (19) establishes that the true δ_R lies in (18)
under a hypothetical first-bad. Indeed at such a first bad the
existing compiled NNS theorem forces the opposite strict sign.
The unproved step is a FIRST-BAD-SPECIFIC prime-distribution/
cross-time-correlation inequality on the real E(R^2) and
delta_R, not a new factorization, not a stronger fitted Li proxy,
and not the mere fact that the observed samples fit.

## 4B. Accumulated historical drift: the exact first-bad obstruction

The terminal current prime-count error $\delta_R$ can be ordinary at
a first bad, since the endpoint can begin almost on its admissible wall.
**No single-block spike is needed.** What IS necessary is an unusually
large *historical signed imbalance* before the final block.

Put $A=\lfloor R/2\rfloor+1$, $B=R+1$,
$W_t=2t\log t$,
$E_t=\pi(t^2)-Q(t^2)$ and
$b_t=Q(t^2)-VF_{\rm mid}(t^2)$, so $D_t=E_t+b_t$.
For either sign $\sigma\in\{-1,+1\}$ define the
ORIGINAL admissible signed wall clearance

$$
S_t^\sigma=W_t-\sigma D_t.
$$

Exact finite historical telescoping (NO approximation to prime supply):

$$
\boxed{
S_B^\sigma=S_A^\sigma+(W_B-W_A)
-\sigma(E_B-E_A)-\sigma(b_B-b_A).
}
\tag{20}
$$

If $B$ is a hypothetical first bad in direction $\sigma$,
then $S_B^\sigma<0$, while first badness guarantees
$S_A^\sigma\ge0$. Thus

$$
\boxed{
\sigma(E_B-E_A)>
S_A^\sigma+(W_B-W_A)-\sigma(b_B-b_A).
}
\tag{21}
$$

The squared-endpoint Li/VF bridge has an established uniform
bound $|b_t|\le C_0$, where the existing proof supplies the
deterministic choice $C_0=1+$ square-endpoint VF/Li constant.
Consequently a hypothetical first-bad event NECESSARILY implies

$$
\boxed{
\sigma(E_B-E_A)>W_B-W_A-2C_0.
}
\tag{22}
$$

This is mathematically important: a harmless LAST block can cross
only after the longer half-scale window has built a large enough
ACTUAL floor-Li error to overcome the expanding wall. Since
$A\simeq B/2$, the required discrepancy in (22) is
of order $B\log B$, even though individual $\delta_r$ may
be comparatively tiny.

**But (22) is only a necessary condition for first badness, not a
contradiction.** Ordinary PNT gives no $O(B\log B)$
error estimate over this moving half-scale difference.

The new *Mathlib-only* Lean kernel formally proves both
positive and negative versions:

- \`vfV2HistoricalPositiveWallClearance\`
- \`vfV2HistoricalNegativeWallClearance\`
- \`vfV2PositiveFirstBad_requires_historicalPrimeLiExcess\`
- \`vfV2NegativeFirstBad_requires_historicalPrimeLiDeficit\`

These theorems take the actually established bounded
bridge and prior-good/first-bad conditions as explicit hypotheses.
There is no extra owner arithmetic asserted.

### Where original composite owners must enter

Use ONLY the true R odd seats. Write

$$
C_r=r-P_r=G_r+H_r,
$$

where $G_r$ counts current odd composites having a unique
ACTUAL prime factor $q>r$ (with odd cofactor $c\ge3$),
and $H_r$ counts all remaining actual odd composites.
Let $G_r^{Li}$ be the same odd-cofactor prime windows evaluated
using $Q$ rather than $\pi$, and set
$H_r^{Li}=r-F_r-G_r^{Li}$ as an **algebraic reference complement**,
not a new physical smooth-prime sieve.

Then, with the original native carrier,

$$
\boxed{
E_B-E_A
=\sum_{r=A}^{B-1}(P_r-F_r)
=-\sum_{r=A}^{B-1}
 \big[(G_r-G_r^{Li})+(H_r-H_r^{Li})\big].
}
\tag{23}
$$

The fixed-c historical $G_r$ prime windows telescope and obey the
weight-retaining Abel identity already investigated in #915.
This transfers THEIR signed errors to endpoint prime backlogs and
weight-variation terms; it DOES NOT bound their combined signs.
The complementary smooth sector $H_r$ ensures exact conservation,
not automatic restoration. Multiplicative $2q$ children remain
EVEN and supply zero independent original odd-carrier mass.

**The precise additional theorem we would need** is an
actual-prime, half-run, signed owner correlation inequality which
places the right-hand side of (23) strictly below the breach threshold
(21) in the would-be escaping direction. It must account for
cross-cofactor overlap, smooth-sector response, prior history
compressed in $D_A$, and all native VF weights. Merely writing (23)
in Möbius, Fubini or floor-Li coordinates is not that theorem.

### Distinguish restorative control from forced sign reversal

Actual numerics already DISPROVE universal absolute pullback:
for R=317, $E(A^2)=-26$, $E(B^2)=-41$,
hence **$E_B-E_A=-15$** (the negative defect GREW).
For R=1027, $E(A^2)=-64$, $E(B^2)=-122$,
hence **$E_B-E_A=-58$** (the negative defect GREW).

Yet both examples are far inside the growing $W_B$ wall.
A new independent R=8..6000 **actual-prime half-run audit** computes
the required historical drift including the real preceding wall slack,
not merely the minimum necessary drift (22):

| R | A | signed E(B²)-E(A²) | wall growth W_B-W_A | actual outward error | required oriented error for crossing |
|---:|---:|---:|---:|---:|---:|
| 317 | 159 | -15 | 2052.753 | 15 | 3640.416 |
| 1027 | 514 | -58 | 7842.116 | 58 | 14196.824 |
| 1760 | 881 | -95 | 14373.926 | 95 | 26226.080 |
| 5267 | 2634 | -130 | 48795.130 | 130 | 90094.819 |
| 6000 | 3001 | -332 | 56357.358 | 332 | 104194.993 |

All rows use the negative first-bad orientation because the actual
terminal signed defect is negative. The last column is
$S_A^{-1}+(W_B-W_A)+(b_B-b_A)$, from (21); it is
**not** the amount that must occur unconditionally, nor a
numerical RH proof. The data show that the ACTUAL prime discrepancy
moves farther from zero while its normalized wall clearance
improves substantially. Over all 5993 tested runs, the maximum
ratio $|E_B-E_A|/(W_B-W_A)$ is about 0.100142 at R=9;
the scan is finite and does not establish this as an all-R bound.

Thus a proposed lemma requiring
$\operatorname{sgn}(D_A)(E_B-E_A)\le0$ over every half-run
would already be **false on actual primes**. The true objective
is wall-RELATIVE control: growth must be sufficiently restrained
WHEN historical wall clearance is in danger of exhaustion.

The built-in fast regression now computes (20)--(22) from
actual prime counts for every R=8..6000 (and optional R<=15000),
prints the signed half-run accumulation and its ratio to
wall expansion, and reports the exact historical excess that
would be necessary to breach. These numerical checks can
FALSIFY candidate owner-pullback laws; they cannot
establish them for all R.

## 4C. Empirical cross-block correlation and all NNS partial moments

**Research-only numerical evidence, NEVER the missing first-bad theorem.**
All rows below are from ACTUAL sieve-computed pi through X=6001^2,
R=8..6000 (5993 blocks), with Q=floor Li_2 and original odd VF weights.
The independent comprehensive vectorized run completed in ~4.4 sec
(excluding runner startup); its floor-Li array included 12,004,000
integer arguments and six near-jump values were verified with
55-decimal-digit mpmath (zero corrections). The standard-library
#918 --extended --floor-li CI also independently checks its original
odd-seat accounting and endpoint discrepancies.

### Three DIFFERENT empirical operators: do not conflate

1. **Aggregate-first block errors.** z_r=P_r-V_r or
   delta_r=P_r-[Q((r+1)^2)-Q(r^2)]; for lag k and FIXED t
   apply partialUpper/Lower to z_r-t and z_(r+k)-t, then sum across r.
2. **Physical seat-first all-pairs NNS.** On the ORIGINAL r odd
   sites use q_r(n)=w_r-1_Prime(n). Apply target t to EVERY literal site
   FIRST; pair ALL sites from block r with ALL sites from block r+k.
   At t=0, the two masses of each block are
   U_r=w_r(r-P_r), L_r=(1-w_r)P_r.
3. **Original anchored first-bad SELF Gram.** Add ONE earlier
   signed scalar -D_r to block r's literal odd-site carrier.
   This is neither operator 1 nor a temporal cross-block Gram.
   Its normalized value is D_(r+1)^2 / M_r^2 >=0.

For any fixed-target pair panel, the four raw quadrant totals are

    CUPM=sum upper(x,t)*upper(y,t)
    CLPM=sum lower(x,t)*lower(y,t)
    DUPM=sum upper(x,t)*lower(y,t)
    DLPM=sum lower(x,t)*upper(y,t)
    Co=CUPM+CLPM, Div=DUPM+DLPM,
    Raw=Co-Div, Total=Co+Div,
    NNS=(Co-Div)/(Co+Div).

The zero-denominator convention is 0. Centered Pearson is shown
separately for comparison. The main Lean library proves the Schur
correction makes centered covariance TARGET INVARIANT
(\`RHLean.Analysis.finiteTargetScaledSchur_target_invariant\`).
No sample/rolling mean is used as the target in these NNS matrices.

### Raw vs normalized, at fixed target zero and lag 1

| Carrier | CUPM | CLPM | DUPM | DLPM | Co-Div | NNS |
|---|---:|---:|---:|---:|---:|---:|
| Literal physical odd seats, Cartesian r/r+1 | 800755069 | 800286757 | 800562087 | 800556934 | -77195.67 | **-0.000024107** |
| Aggregate signed VF block first | 106874 | 113012 | 154681 | 142401 | -77195.67 | **-0.149324** |
| Aggregate true prime-minus-floorLi block first | 106663 | 113367 | 155048 | 143150 | -78168 | **-0.150837** |

**CRITICAL:** The physical and aggregate VF methods have the
SAME signed pair-product numerator, by Fubini.
They have radically different denominators because
\`abs(sum q)\` differs from \`sum abs(q)\`. Thus an impressive
aggregate-first NNS anticorrelation is NOT the normalized
physical-seat coefficient of #918's actual original carrier.

An added seconds-fast CI audit computes *all four* literal
seat-first quadrants at t=0 and t=+/-0.1, computes the
aggregate-first quadrants at t=0, and **asserts exact signed
Gram equality** (to floating verification tolerance), without
altering the five-file PR or building StrongPNT.

### Lagged true-prime and composite-owner dependencies

| Actual block series, R=8..6000 | Pearson lag 1 | NNS at t=0 lag 1 |
|---|---:|---:|
| P_r-V_r | -0.096143 | -0.149324 |
| P_r-floorLi block demand | -0.097081 | -0.150837 |
| (P_r-V_r)/sqrt(V_r) | -0.112556 | -0.173846 |
| High-q odd composites, actual minus floorLi | -0.362482 | -0.440971 |
| Remaining smooth composites, actual minus formal Li complement | -0.530072 | -0.578448 |
| High-q odd composites, actual minus CONTINUOUS Li | -0.186247 | -0.125619 |
| Remaining smooth composites, actual minus CONTINUOUS Li complement | -0.337538 | **+0.043147** |

This continuous-versus-discrete Li comparison matters.
A substantial part of the apparent negative cofactor-series
autocorrelation depends on using the discrete floor-Li
staircase. For the smooth composite sector with continuous Li,
the **same** data have NEGATIVE Pearson but POSITIVE t=0
NNS. Target-zero Co/Div is UNcentered signed interaction and
can have a different sign from centered Pearson when
the series have nonzero baseline imbalance.

Lag response is neither simply always negative nor
a monotone restorative kernel: for the floor-Li
large-q/smooth residuals Pearson at lag 2 is
+0.044098/+0.124722, whereas at lag 1 it is
-0.362482/-0.530072. For actual P-floorLi
lags 1,2,4,8,16,32, Pearson is
-0.097081,-0.061939,-0.046641,-0.021079,-0.009869,+0.018995.
Lag-1 prime-error Pearson remains negative in all three
fixed subranges 8..1000, 1001..3000, 3001..6000
(-0.1509,-0.1289,-0.0858).

### Full 3-by-3 native weighted cross-block NNS matrix at target zero

Rows = source sector at block r;
columns = source sector at block r+1.
All three are corrections against floorLi relative to the
original physical VF charges:

    a_r=(w_r-1)*delta_r     [prime]
    g_r=w_r*(G_r-G_r^Li)   [large-prime odd composite]
    h_r=w_r*(H_r-H_r^Li)   [smooth composite]

Their sum is **EXACTLY** -delta_r. The normalized Co-Div
lag-1 matrix is

| r source / r+1 destination | prime | large q | smooth |
|---|---:|---:|---:|
| Prime | -0.150004 | -0.123705 | +0.062769 |
| Large-q | -0.113788 | -0.439351 | +0.486929 |
| Smooth | +0.048999 | +0.480987 | -0.575189 |

Notice large->smooth and smooth->large are POSITIVE, while
both self-sector lag-1 diagonals are NEGATIVE. That is a
mixed signed interaction structure, NOT automatic globally
nonpositive Co-Div energy. The raw Co and Div matrices
are separately computable with the code below; normalizing
each cell does not produce an additive global inequality.

### Fixed target stress test

Aggregate actual P-floorLi at lag 1:

| fixed t | Co | Div | normalized NNS | centered Pearson |
|---:|---:|---:|---:|---:|
| -1 | 223079 | 296363 | -0.1411 | -0.0971 |
| 0 | 220030 | 298198 | -0.1508 | -0.0971 |
| +1 | 225944 | 297012 | -0.1359 | -0.0971 |

For the **literal physical seats** (changing t on each
of the r actual site charges), lag-1 NNS values are:

    t=-0.1   +0.121559
    t= 0.0   -0.000024107
    t=+0.1   +0.548503
    t=+0.25  +0.999999741

These target shifts are legitimate *alternative* partial-moment
statistics, but NOT the original tracking-defect physics.
At a shifted t the signed source itself changes by a
deterministic multiple of the physical seat count; the
original #918 first-bad weld remains defined at t=0.
One cannot choose a convenient target solely to make the
normalized Co/Div sign look favorable.

### Historical versus current: the actual Fubini term

The existing Lean identity
\`vfMidOddHistoricalCurrentSeatGram_eq_endpointPolarization\`
computes the signed **historical/current** Gram for
A=floor(R/2)+1. On the block-level panel

    history_r = D_r-D_A
    current_r = P_r-V_r

the Pearson cross-statistic is **-0.06963** and t=0
NNS is **-0.05035** across all r=8..6000. By contrast,
D_r versus the current increment gives Pearson -0.04374
and t=0 NNS -0.01782. The empirical historical sign
association is modest, far weaker than the isolated
smooth-composite lag-one NNS. Again, the original
global mass is not the aggregate-first denominator.

The maximum measured occupancy of the wall
|D_r|/(2r log r) is only **0.04599** (at r=15).
NONE of the sampled trajectories is anywhere close to
a hypothetical first-bad boundary, so these correlations
do not verify feedback where it actually matters.

### Nonlocal genuine owner pairs (q prime -> c*q composite)

The literal negative historical prime q carries signed
charge w_floor(sqrt(q))-1, while its odd composite descendant
c*q at root R carries +w_R.
Each selected parent/descendant pair is, trivially,
DIVERGENT with positive mass w_R*(1-w_parent).
Its NNS on this PRESELECTED pair population is -1 by
construction; that is not a global contraction.

Independent true-prime owner matching finds:

| current R | ALL high-q odd descendants | within half-run ancestor A..R-1 | divergent matched mass within half-run | divergent matched mass from all history |
|---:|---:|---:|---:|---:|
| 119 | 80 | 11 | 1.759838 | 11.490544 |
| 317 | 192 | 23 | 3.229685 | 24.787636 |
| 1027 | 659 | 52 | 6.326219 | 74.631875 |
| 1760 | 1169 | 94 | 10.763633 | 125.391234 |
| 5267 | 3400 | 229 | 23.392887 | 328.670776 |
| 6000 | 3878 | 233 | 23.498222 | 370.264993 |

Inside the half-run all these q parents are c=3
(the previously established top-third geometry);
most matched parents belong to EARLIER history already
compressed in the single D_A anchor.
The selected negative pairing heat CANNOT be added to
#918's original Co/Div denominator, nor spent twice.
Its deficit relative to the massive total physical pair
mass illustrates why a proof must route ALL other
unmatched, diagonal and restoring terms quantitatively.

### What this comparison establishes, and what it does not

The empirical evidence is robust for short-range
anti-correlation of real prime-count residuals and
some odd-owner sectors. But:

- Partial-moment normalization **does not commute**
  with signed block aggregation.
- Large/smooth Li benchmark residuals are constrained
  by the exact tautology
  delta_prime+delta_large+delta_smooth=0.
  Their extreme long-horizon mutual negative correlation
  is partly a consequence of this algebra and benchmark
  biases, NOT an independent theorem about prime owners.
- Floor versus continuous Li can materially change
  sector lag-correlation magnitudes and even normalized
  signs.
- The original first-bad SELF NNS coefficient is
  **nonnegative**, unlike temporal cross-block lag
  covariance: its maximum over R<=6000 is 0.206054,
  not the -0.149324 or -0.000024107 of the two
  temporal operators.
- The data do not sample any near-wall endpoint.
- No unconditional signed owner-tree estimate follows
  from these correlations; RH remains open.

The necessary NEW mathematical theorem would be a
first-bad-CONDITIONAL wall-relative bound on the FULL
retained-weight historical/current signed physical Gram
(including the compressed anchor and all owner sectors),
not an observational lag-one Pearson or an
aggregate-first normalized NNS value.


## 5. Testing: deliberately separate seconds from native compilation

**Fast lane** (automatically on every PR update; no Lean/StrongPNT):

```sh
python3 scripts/vf_mid_first_bad_payment_v2_test.py
python3 scripts/vf_mid_first_bad_payment_v2_test.py --extended
```

Tests **ACTUAL** prime flags, not Li or random prime density:
- each current R block has exactly R odd candidates;
- actual prime events occur only on the original odd physical carrier;
- full-lattice VF block mass is assigned at V_R/R;
- signed recurrence (1) and both partial-mass identities (5);
- original denominator (6), two-sector form (9), and exact quadratic slack;
- finite actual $R=8..6000$ regression in extended mode;
- deliberate negative **synthetic** balance counterexample to prevent
  accidental "unconditional cone" promotion.

**Verified first fast run (GitHub Actions, Oct 8 ET):**

The stand-alone actual-prime audit passed **all 5,993 consecutive blocks,
R=8 through R=6000**, in **0.32 seconds of Python runtime**. It computed
pi from the actual sieve; the complete signed and absolute odd-carrier
identities matched independently enumerated real odd prime/composite seats.
Selected exact-source diagnostics:

| R | Current actual prime seats | U_R | L_R | Normalized D_(R+1)^2/M_R^2 |
| ---: | ---: | ---: | ---: | ---: |
| 8 | 4 | 2.810542 | 2.015682 | 0.027125 |
| 119 | 19 | 39.967911 | 15.011178 | 0.206054 |
| 317 | 54 | 83.859574 | 44.610994 | 0.093334 |
| 1027 | 144 | 243.523135 | 123.225304 | 0.107592 |
| 1760 | 204 | 367.765162 | 176.695261 | 0.123155 |
| 5267 | 617 | 867.435421 | 544.992045 | 0.052116 |
| 6000 | 698 | 1168.342977 | 617.759722 | 0.095024 |

All observed 5,993 original full-block slack values were positive.
This is a **finite regression result only** and does not supply (11).
The independent kernel Lean lane and manual native lane are separate
verification statuses.

**Small Lean algebra lane** (automatic; Mathlib cache):
```sh
lake env lean -DwarningAsError=true \
  research/VF_MID_FIRST_BAD_PAYMENT_V2_KERNEL.lean
```
Mathlib-only; no StrongPNT patch, no native project import cascade.
Rejects syntax/typing errors and forbids `sorry` / `admit`.

**Native integration lane** (manual deep CI, not on every PR edit):
```sh
python3 scripts/compile_research_import_closure.py \
  research/VF_MID_FIRST_BAD_PAYMENT_V2_NATIVE_CONSUMER.lean
```
This imports the pre-merged main first-bad chain and checks that
the conditional consumer's proof has not drifted. It is unavoidably
slower after a cold cache and is **NOT** called by fast smoke CI.
Neither this deep check nor the algebra check tries to prove (11).

The workflow `.github/workflows/vf-first-bad-payment-v2.yml`
splits these lanes and cancels stale PR runs; the first job needs only
Python 3 stdlib. The GitHub manual workflow has `deep_native` input.

### Acceptance contract for any future proof patch

- Exactly one new unconditional theorem must discharge (11) **under
  hfirst and genuine actual primes**; the native consumer then
  supplies the contradiction, without adding premises.
- Source is the original R odd seats, with $D_R$ compressed and
  $M_R^2$ unchanged. No even $2q$ physical charges.
- Use no `sorry`, `admit`, new `axiom`, trusted guessed wheel density,
  synthetic negative parent, or global unverified cone.
- The independent fast sieve audit remains green, including
  $R=317,1027,1760,5267$.
- Native Lean strict compilation of the actual final theorem (not only
  the conditional consumer) must become green before claiming closure.
- Check `#print axioms` of the finished production theorem.
- No new speculative module or PR until the exact inequality is
  either proved or a precise obstruction/counterexample is shown.

## 6. Dependency/size budget

New branch is based directly on `main`.
This workstream starts with **exactly five files**:

1. This canonical proof contract (one `.md`);
2. One small Mathlib-only algebraic kernel file;
3. One native conditional consumer importing existing main;
4. One stdlib actual-prime regression script;
5. One isolated fast workflow with an opt-in deep lane.

Do not transplant #915's 36-file exploratory diff, commit history,
experimental Li/floor-Li scripts, or failing terminal file.
Historical exploratory work remains available at
[PR #915](https://github.com/OVVO-Financial/RH_Lean/pull/915);
that history is a reference, **not a dependency**.

**Plain outcome criterion:** (11) must become a genuinely proved
actual-prime signed inequality, compiled in Lean with no added
arithmetical hypothesis. Until then this PR is a clean, green *proof
infrastructure* PR, not an RH proof.

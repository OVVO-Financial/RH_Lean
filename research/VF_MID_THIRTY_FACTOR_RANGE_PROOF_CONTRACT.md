# Wheel-30 factor-range lower channel: source-native proof contract

**2026-10-10 • PR #925.** The new file
\`research/VF_MID_THIRTY_FACTOR_RANGE_LOWER_GATE.lean\` replaces
hypothetical “prime-staircase admissibility” assumptions with an exact
FORMULATION using only integer factors, finite gcds, and VF masses.
**It does NOT claim to have proved the final lower-channel inequality.**

## 1. Exact pure factor-range carrier

For every integer square root R>=5, define
\[
I_R=\{n\in\mathbb N:R^2<n<(R+1)^2\},\qquad
W_R=\{n\in I_R:\gcd(n,30)=1\}.
\]

This deletes ALL even numbers; ALL odd multiples of 3; and ALL
odd numbers congruent to 5 modulo 10, including those divisible by
several of 2,3,5. Each integer is discarded **once**, not counted
separately under each factor. Since R>=5, no exceptional prime
2,3,5 is in any of these blocks. The only possible mod-30 residues
are {1,7,11,13,17,19,23,29}. Write N_R=|W_R|.

**Pure divisor-range covered set:**
\[
\boxed{\mathcal C_R=
  \{n\in W_R:\exists d\in\mathbb Z,\ 7\le d\le R,\ d\mid n\}.}
\]
The divisor d need NOT be prime; including all d in [7,R]
introduces **no independent double charge** because the
definition is a set and each n is counted once.

Write C_R=|\mathcal C_R|.

On the ORIGINAL square carrier a composite n must have a factor at
most R (by FTA and n<(R+1)^2), while surviving the fixed 30-wheel
excludes factors 2,3,5. Thus the fully uncovered population
is EXACTLY N_R-C_R.

This **is not a new prime-counting function**.
\`Nat.Prime\` is used only by the existing FTA bridge at the end.
The new source-native types \`vfMidThirtyCandidates\` and
\`vfMidThirtyFactorCovered\` do not contain \`Nat.Prime\` or
\`Nat.primeCounting\` in their definitions.

The exact decoder theorem is
\`vfMidThirtyCovered_add_actualPrimeSupply_eq_candidates\`:
\[
\boxed{P_R=N_R-C_R},\qquad
P_R=\pi((R+1)^2)-\pi(R^2).
\tag{1}
\]
A second exact theorem identifies \(\mathcal C_R\) as
the cutoff-5 wheel survivors MINUS the full cutoff-R survivors.
It is also the disjoint census of all least-prime owners p>=7:
\[
\boxed{
 C_R=\sum_{p\in{\cal O}_R,\ p>5}
 \#\{n\in I_R:n\text{ composite},\ \minFac(n)=p\}.
}
\tag{2}
\]
This reuses the original owner fibers, including their positions,
rather than stripping the occurrence identity in a Möbius sum.

## 2. What the fixed 30-wheel proves unconditionally: O(1)!

Let
\[
F_5(N)=\#\{1\le n\le N:\gcd(n,30)=1\}.
\]
It has exactly eight survivors per 30 integers. The
prefix periodic phase has the exact finite law
\[
 F_5(N)=8\lfloor N/30\rfloor+
   \#\{a\in\{1,7,11,13,17,19,23,29\}:a\le N\bmod30\}.
\]
In fact its optimal phase is between -2/3 and 14/15 (by
checking residues 0,...,29), but that sharp constant is not
yet imported as a native theorem.

The already-compiled Boolean floor discrepancy lemma proves the
safe uniform estimate
\[
 |F_5(N)-\tfrac4{15}N|\le8.
\tag{3}
\]

**The unexpected stronger result applies across arbitrarily many
whole square blocks:** the exact four-endpoint prefix potential
already proved in \`VF_MID_DYADIC_PREFIX_OWNER.lean\` gives
\[
 \sum_{r=A}^{B-1}N_r =
 F_5(B^2)-F_5(A^2)-F_5(B)+F_5(A).
\tag{4}
\]
Therefore for EVERY pair A<=B,
\[
\boxed{\left|
\sum_{r=A}^{B-1} N_r-
\frac4{15}\bigl[(B^2-A^2)-(B-A)\bigr]
\right|\le32.}
\tag{5}
\]
This is **O(1) regardless of the number of square blocks**.
The root-endpoint correction \(-F_5(B)+F_5(A)\) is essential:
it subtracts coprime perfect squares from the consecutive
open square intervals. Naïvely summing an O(1) error separately
over each block would wrongly lose an O(B-A) term.

The new module specializes the existing general theorem at
z=5, proving both the prefix-supply and physical-candidate
run forms. This is a real, unconditional long-run simplification.
It isolates the ONLY potentially unbounded contributor in this
factor decomposition: the evolving owner coverage p>=7.

**Sharp periodic refinement: universal 32/15 rather than 32,
mathematically complete on paper; not yet kernel-compiled.**
Define the exact fixed-wheel prefix phase
\[
e(n)=F_5(n)-\frac4{15}n.
\]
Since the eight residues modulo 30 repeat EXACTLY,
\(e(n+30)=e(n)\). Define the square-clock correction
\[
q(r):=e(r^2)-e(r),\qquad q(r+30)=q(r).
\]
Equation (4) makes the full A-to-B count error
\(\varepsilon_{A,B}=q(B)-q(A)\), literally a difference
of two values of a **30-state periodic function**.
The 30 exact rational cases are exhaustively checked by
\`scripts/VFMidThirtyFactorRange/verify_periodic_certificate.py\`:
\[
-\frac43=\min_{0\le r<30}q(r),\qquad
\max_{0\le r<30}q(r)=\frac45.
\]
Thus for ALL A,B (not merely tested intervals),
\[
\boxed{
|\varepsilon_{A,B}|\le \frac{32}{15}
\approx2.1333333.
}\tag{5-sharp}
\]
The logical reason this finite computation GENERALIZES is a
**proved elementary algebraic periodic reduction**:
every r equals \(30k+t\), and q depends only on t.
The independent script displays each exact rational
certificate and tests all 900 ordered residue pairs.
This is different in kind from extending a finite prime
staircase plot: the dynamically moving factor-owner sequence
has no comparable proved finite-period reduction.
The native Lean bound (5) remains 32 until the small
closed-form 30-residue certificate is transplanted and
kernel checked; do NOT label (5-sharp) Lean-proved yet.


It does not itself force a lower bound on the remaining survivors.

## 3. The signed excess is EXACTLY the old native VF currency

Set the original VF band mass
\[
V_R=\frac{2R+1}{\log(R^2+R+\tfrac12)},\qquad
F_R=\sum_{r=2}^{R-1}V_r,
\]
without reweighting it after the fixed sieve. Define
\[
\boxed{E_R^{30}:=C_R-(N_R-V_R).}\tag{6}
\]
By (1),
\[
 E_R^{30}=V_R-P_R,
\]
which is PRECISELY the existing
\`vfMidOddCompositeTrackingDefect R\`: all p=3,5 owners
have been subtracted from BOTH candidate seats and actual
composite reference. One cannot collect an unwarranted
“20% extra payment” just by excluding last digit 5.

Accumulate in source coordinates
\[
T_R^{30}=\sum_{r=5}^{R-1}E_r^{30}.
\]
The initial arithmetic anchor is \(\pi(25)=9\), so
\[
\boxed{
\pi(R^2)-F_R=(9-F_5)-T_R^{30}.}\tag{7}
\]
Here \(F_5\) on the RIGHT denotes **the real VF completed mass
at root 5**, NOT the 30-wheel prefix count \(F_5(N)\) above;
in Lean these have disjoint names
\`vfMidFinishedMass 5\` and \`vfMidPrefixWheelCounting 5 N\`.

## 4. Source-only lower barrier, exact FTA bridge, and first-bad bill

The factor-only statement \`VFMidThirtyLowerFactorSafe K R\`
requires
\[
\boxed{T_R^{30}\le
  9-F^{VF}_5+K R\log R.}\tag{8}
\]
This contains **NO prime test, no pi function, no Li state**.
Only after (8) is given does
\`vfMidThirtyLowerFactorSafe_iff_actualLowerChannel\`
transfer it by FTA to
\[
\pi(R^2)-F_R\ge-KR\log R.
\tag{9}
\]

For the user's chosen additive vertical phase
\(c_{\rm chosen}=\sqrt2\), the horizontal factor-only condition
at arbitrary root L is
\[
\boxed{T_R^{30}\le
9-F^{VF}_5+F_R-\lfloor F_L+\sqrt2\rfloor.}\tag{10}
\]
A native theorem makes this **iff**
\(\lfloor F_L+\sqrt2\rfloor\le\pi(R^2)\)
for R>=5. In particular choose
\[
 L=R-\min(\lfloor R/2\rfloor,
            \lfloor A(\log R)^2\rfloor).
\]
This converts lower RH-scale horizontal safety entirely to
the cumulative finite divisor-range coverage inequality (10).
It is the MISSING MATHEMATICAL theorem, NOT a new name for
an already-established bound.

At an earlier safe root A define historical slack
\[
 S_A=9-F^{VF}_5 + KA\log A-T_A^{30}.
\]
If a first lower-wall breach occurs at B>A, then the new
theorem \`vfMidThirtyFirstLowerBreach_forces_factorRunOverrun\`
shows necessarily
\[
\boxed{
T_B^{30}-T_A^{30}>
S_A+K(B\log B-A\log A).}\tag{11}
\]
This preserves ALL earlier slack. It does not treat mature
least-prime owners as freely spendable negative payments.
(11) is a necessary failure trigger; its reversal is the
open signed historical-owner restriction.

## 5. Outside-the-box closure attempt: frozen plus late-owner return

Because the entire 30-wheel prefix has only the FOUR-ENDPOINT
error (5), we can eliminate fixed-mask oscillation from the
first-bad analysis. Exactly decompose:
\[
\begin{aligned}
\sum_{r=A}^{B-1}(P_r-V_r)
&= \sum_{r=A}^{B-1}(N_r-C_r-V_r)\\
&=\frac4{15}[(B^2-A^2)-(B-A)]
   -\sum_{r=A}^{B-1}C_r
   -(F_B-F_A) + \varepsilon_{A,B},\\
|\varepsilon_{A,B}|&\le32 .
\end{aligned}
\tag{12}
\]
Thus an RH-violating run **cannot be blamed on a large
residue-30 boundary effect**. It must be an extreme
non-compensated *disjoint owner-coverage surplus*
among the progressing factors >=7.

Concrete next theorem to attack in the existing owner
Fubini/sector-six machinery (NOT presently proved):

For all hypothetical first-bad roots B and their last safe
anchor A, show the accumulated once-charged p>5 owner
coverage does NOT exceed (11)'s historical wall budget.
Equivalently, show the strict factor-coverage overrun (11)
contradicts an independent arithmetic owner-return/energy
certificate. The certificate must preserve survivor masks,
owner ages, signed parent/child interactions, and all
cross-owner terms through the Fubini swap.

Pure inclusion-exclusion or fixed-modulus Euler densities
cannot substitute for this. This is the classical parity
barrier of sieve methods in a concrete root-square guise:
a static sieve easily upper-bounds survivors but cannot
force an RH-quality lower supply of actual primes.

**Practical experimental discriminator:** condition the
disjoint p>=7 owner cover surplus on BOTH age of its owners
and the historical slack S_A, not just current R. Test the
signed *future return* within the exact available
h_R = O(log(R)^2) VF-root lag, and look for a coercive,
uniform sign inequality. Existing finite owner-sector
numerics may help nominate such an inequality; an actual
all-R structural proof is still necessary.

## 6. Exact signed owner weld with a fixed 32-count boundary

This closes the principal *representation mismatch* between the new
divisor-only factor-range statement and the old physical-sector
proof currency. It does NOT close the missing inequality itself.

The new native theorem
\`vfMidThirtyLateOwnerRemoval_eq_factorCoveredRun\` identifies
the ENTIRE count \(\sum_{A\le r<B}C_r\) literally with the
original once-charged
\`vfMidDyadicLateRemoval 5 A B\`, hence retains the real
least-prime-owner incidence and occurrence multiplicities.

The theorem
\`vfMidThirtyRunExcess_eq_nativeTracking\` identifies
\[
T_B^{30}-T_A^{30}
=\mathrm{vfMidDyadicVFTrackingDefect}(A,B)
= (F_B-F_A)-(\pi(B^2)-\pi(A^2)).
\tag{13}
\]
The core uniformly signed transfer is
\[
\boxed{
\left|
 [\mathrm{LateRemoval}_5(A,B)-\mathrm{LateReference}_5(A,B)]
 -\mathrm{VFTracking}(A,B)
\right|\le32.
}
\tag{14}
\]
The difference inside the absolute value is EXACTLY the
four-endpoint *fixed* wheel-30 density phase from (5).
There is no hidden cutoff-dependent error of size O(B-A).
The proof uses the already verified generic wheel theorem and
the original exact owner census, not an extra prime
distribution hypothesis.

Combining (11), (13), (14), the new theorem
\`vfMidThirtyFirstLowerBreach_forces_ownerResidualOverrun\`
proves the **precise physical signed first-bad obstruction**:
\[
\boxed{\begin{aligned}
&\mathrm{LateRemoval}_5(A,B)
-\mathrm{LateReference}_5(A,B)\\
&\qquad>
S_A+K(B\log B-A\log A)-32.
\end{aligned}}
\tag{15}
\]

Equation (15) is a true theorem conditioned on a hypothetical
first-bad lower source event, *not* the inequality in the opposite
direction. An unconditional native signed owner-return
upper bound
\[
\mathrm{LateRemoval}_5-\mathrm{LateReference}_5
\le S_A+K(B\log B-A\log A)-32
\]
(on the needed first-bad configuration) would create the
contradiction and exclude the lower escape. That independent
upper bound remains **OPEN**; one cannot derive it by dropping
signed cross-owner terms or by assuming an empirically fitted
class property.

The Wiles-style classification target is therefore now
concrete: identify an independently provable factor-range
coherence/return restriction on *actual chronological owners*
strong enough to exclude the physical sign in (15), including
the historical slack S_A. The known finite 317/1027 and
owner-age conditioned numerics may propose such a restriction,
but only an all-R proof can discharge it.

## 7. Adaptive frozen-wheel proof kernel: more than a fixed 30-wheel

The true extra mathematical latitude is an INFINITE family of finite
low-factor prefixes, frozen separately at the historical anchor A.
For any cutoff z<=A, write
\(d_z=2^{\#\{p\le z:p\mathrm{\ prime}\}}\),
the exact number of Boolean faces in its inclusion-exclusion cube.
The existing generic four-endpoint theorem gives
\[
\boxed{
\left|
(\mathrm{LateRemoval}_z-\mathrm{LateReference}_z)
-\mathrm{VFTracking}(A,B)
\right|\le 4d_z
}
\tag{16}
\]
for *every* B>=A, with NO dependence on B-A. Crucially,
this is an **already-proved generic mathematical theorem**, now
explicitly welded to the actual p>z owner ledger in the new
\`research/VF_MID_ADAPTIVE_FACTOR_OWNER_RETURN.lean\` module.

Select ONLY finite cutoffs satisfying the INDEPENDENT
non-RH face budget
\[
\boxed{
z\le A,\qquad 2^{\#\{p\le z\}}\le A.
}
\tag{17}
\]
These restrictions involve only the starting prime-coordinate
list, not pi(A²), Li, or any hypothesized endpoint channel.
Then (16) has error <=4A, well inside a K A log A
RH-scale radial width. This is a genuine all-scale rule
for choosing an evolving cutoff without paying a boundary
error proportional to run length.

At a hypothetical lower first bad, the *entire* remaining
p>z native signed late owner residual MUST obey the strict
inequality
\[
\boxed{\begin{aligned}
 &\mathrm{LateRemoval}_z(A,B)
 -\mathrm{LateReference}_z(A,B)\\
 &\quad > S_A + K(B\log B-A\log A)-4A.
\end{aligned}}
\tag{18}
\]
The opposite owner-return estimate under an INDEPENDENT
structural hypothesis would exclude that lower breach;
the exact implication is now in
\`vfMidAdaptiveLowerSafe_of_physicalReturnUpper\`.

Unlike the trivial choice z=5, (17) allows z to GROW with A.
For example, the safe rough sufficient inequality
\(2^z\le A\) (since there are at most z prime coordinates
up to z) permits z as large as \(\lfloor\log_2 A\rfloor\).
The new theorem does NOT require PNT, zero-free regions,
or such an explicit cutoff formula: the admissible property
is a finite parameter passed to it. Using the true
number of prime faces permits higher cutoffs than 2^z
would suggest.

This is a promising new tradeoff: larger frozen base means
fewer active least-prime owners, while the cumulative
fixed-wheel error stays O(A). Its weakness is that 4A
is a much larger allowance than the sharp fixed mod30
32/15. We can optimize z for different anchors and
owner-age strata. It does NOT produce the missing
signed upper bound automatically: the sieve parity/owner
correlation gap remains.

## 8. Finitude boundary and CI



\`scripts/VFMidThirtyFactorRange/verify.py\` independently
builds the least-prime-factor sieve, verifies every covered
candidate's smallest divisor lies in [7,R], checks the exact
candidate/covered/survivor identity, checks VF signed
telescoping, checks the four-endpoint wheel-30 error,
and diagnoses the chosen sqrt(2) root-lag condition.
The experiment is not substituted for (8)/(10).

The main \`prime-flip-pnt-telescope\` CI workflow warning-fatally
compiles the new module and axiom-audits all mathematical lemmas.
The independent Wiles workflow reruns the numerical diagnostic.
No new classical axioms, \`sorry\`, \`admit\`, or user-defined
RH assumption is permitted to prove the unconditional claims.

**Status:** (5) comes from an already-established generic
finite-wheel theorem; the specific specialization and the
new factor-only definitions are under PR #925 CI until a
successful warning-fatal compile confirms them.
The lower-channel bound (8) is still **open**.

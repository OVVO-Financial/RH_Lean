# Minimal first-bad parity payment — production proof contract (v2)

**Status: DRAFT, open arithmetic theorem. Not a proof of RH.**
**Base:** clean `main`, deliberately NOT the accumulated #915 feature branch.
**Supersedes for new work:** [PR #915](https://github.com/OVVO-Financial/RH_Lean/pull/915)
as the single small target for an actual signed first-bad closure.
**Fast entry point:** `python3 scripts/vf_mid_first_bad_payment_v2_test.py --extended`.
**Lean entry point:** `research/VF_MID_FIRST_BAD_PAYMENT_V2_KERNEL.lean`.
**Native consumer:** `research/VF_MID_FIRST_BAD_PAYMENT_V2_NATIVE_CONSUMER.lean`.
**Only open proof gate:** `VFMidMinimalActualFirstBadPaymentV2Statement`.

## 0A. Oct 9 sign audit: NO sign inconsistency; the contradictory sign is the open theorem

The production implication is a proof by contradiction, not a statement that
the first-bad hypothesis and a nonpositive sector budget are compatible.
Write

\[
\mathcal E_R=2D_{R+1}^2-M_R^2,\qquad
\mathcal K_R=\mathcal R_R+2\mathcal S_R .
\]

On the original active prime/squarefree carrier, with \(P_R\) actual primes,
\(F_R\) actual odd squarefree composites, and \(w_R=V_R/R\),

\[
Z_R=\frac{(w_RF_R-(1-w_R)P_R)^2-
 ((1-w_R)^2P_R+w_R^2F_R)}{2},
\]

\[
A_R=\frac{(w_RF_R+(1-w_R)P_R)^2-
 ((1-w_R)^2P_R+w_R^2F_R)}{2}.
\]

The original Co/Div excess is \(\mathcal E_R=\mathcal R_R+4Z_R-2A_R\).
The six-sector signed reassembly gives \(\mathcal S_R=Z_R\), so

\[
\boxed{\mathcal K_R
 =\mathcal E_R+2(A_R-Z_R)
 =\mathcal E_R+4w_R(1-w_R)P_RF_R.}
\]

**The correction has a PLUS sign.** For \(0\le w_R\le1\), it is
nonnegative. The earlier numerical table is consistent. Under the
hypothetical first-bad hypothesis, the already-compiled radial lemma
gives \(\mathcal E_R>0\), and hence \(\mathcal K_R>0\).
This is entirely EXPECTED. It does **not** disprove the proposed missing
theorem \(\mathrm{FirstBad}\Rightarrow\mathcal K_R\le0\):
deriving that opposite sign independently from genuine prime history
would immediately contradict first-badness. The alternative
\(\mathrm{FirstBad}\Rightarrow\mathcal E_R\le0\) has the same logical
structure; it is weaker as a pointwise requirement. The universally
quantified first-bad-conditioned versions are both equivalent to
no first bad, because their antecedent itself forces the reverse sign.
Neither implication can be inferred from the sign identity.

The Mathlib-only sign audit is
`vfV2SixBudget_eq_originalExcess_add_pairCorrection`.
The native exact-carrier assertions are
`vfV2ActualFirstBad_originalExcess_pos` and
`vfV2ActualFirstBad_sixSectorBudget_pos`.
These are proof-check targets in the dedicated CI; the first-bad
*nonpositive* arithmetic payment remains unproved.

### Correct first-bad local normal form, and a dangerous false shortcut

Let \(W_R=2R\log R\) and \(\delta_R=P_R-V_R\).
If \(|D_R|\le W_R\) and \(|D_R+\delta_R|>W_{R+1}\), then

\[
|\delta_R|>W_{R+1}-|D_R|\ge W_{R+1}-W_R
\]

and \(\delta_R\) has the same sign as \(D_{R+1}\).
That NECESSARY logarithmic jump is valid. It is not a sufficient
contradiction with any standard one-block prime-count upper bound.

**In particular the suggestion that \(|D_R|\gg P_R+V_R\) rules out
first badness is false.** A near-wall prior defect can cross on a
small jump, even when \(|\delta_R|\ll P_R+V_R\). A concrete *scalar*
counterstate (NOT a claim about the actual prime history) is
\(R=100000,\ D_R=W_R,\ P_R=8712,\ V_R\approx8685.929295\).
Here \(\delta_R\approx26.071\) exceeds
\(W_{R+1}-W_R\approx25.026\), while
\(P_R+V_R\approx17397.929\) and the original
\(N_R\approx0.98637>1/2\). This satisfies the local prior-good
and next-bad inequalities with an ordinary-sized block count.

Thus a regime split or a Brun--Titchmarsh count bound alone does NOT
establish the missing payment. One needs a genuinely quantitative
historical arithmetic restriction forbidding the approach to
the wall. No additional owner energy may be manufactured by
reclassifying sites.

---

## 0B. Oct 9 quantified implication and energy audit

### EXACT scope of the equivalence with RH: record explicit interfaces

1. **Already available on the #918 branch:**
   `vfV2ActualPrime_signedOwnerRule_iff_noFirstBad` establishes that
   the original sign-payment rule
   `VFMidActualPrimeSignedOwnerEscapeRule` is logically equivalent to
   **no first-bad successor with index R+1, R>=8**.
   This equivalence is a logical closure, NOT an arithmetic proof.
2. **New native checked target:**
   `vfV2ActualPrime_allInside_of_noFirstBad_and_base` performs the
   minimal-counterexample argument. It explicitly requires finite
   base containment for **2<=B<=8**. No missing early indices are
   silently ignored.
3. **New conditional RH bridge:**
   `vfV2ActualPrime_RH_of_signedOwnerRule_and_base` derives RH from
   the signed rule **provided the finite base and the existing
   `ClassicalVonKochRHCriterion` argument**. The latter is an
   explicit classical analytic interface in
   `VF_MID_VON_KOCH_BRIDGE.lean`, NOT a Lean-kernel proof of the
   classical analytic criterion itself.
4. **Do NOT yet state an unconditional Lean equivalence with RH.**
   The existing classical criterion provides an equivalence between
   RH and an arbitrary-constant von-Koch estimate. Turning that
   estimate back into **this fixed K=2 containment at every
   square endpoint** requires a quantitative RH implication
   (e.g. Schoenfeld's conditional explicit bound, careful Li
   normalization, the deterministic VF/Li bridge, and finitely
   many small roots). That reverse step has not been installed
   in the repository. Conversely, the forward implication remains
   conditional on its explicitly supplied classical criterion.

### Prior-good is NOT an NNS induction invariant

The proposed energy induction
\(\Phi_R=M_R^2-2D_{R+1}^2\ge0\)
cannot start from the assertion that the previous endpoints are
inside their radial wall. These are different properties.

The fast Lean theorem
`vfV2PriorGoodEvenNextGood_doesNotForcePhi_nonneg`
checks a concrete **scalar** counterstate:

\[
D=20,\quad w=1/4,\quad P=C=4,\quad W_{\rm prior}=20,\quad
W_{\rm next}=23.
\]

It has a prior GOOD endpoint, next GOOD endpoint (\(D'=22\)),
and yet

\[
M=(|20|+1+3)=24,\qquad
\Phi=24^2-2(22)^2=-392.
\]

This is NOT an example of actual primes. It shows only that an
energy induction needs a *separate arithmetic invariant*;
the prior-good radial assumption does NOT imply
\(\Phi_{R-1}\ge0\) or \(\Phi_R\ge0\).

The signed jump-normal-form lemmas now in the tiny kernel are
`vfV2FirstBad_requires_strictCurrentDeviation`,
`vfV2FirstBad_positive_outward`,
`vfV2FirstBad_negative_outward` and
`vfV2FirstBad_outward_orientation`. They prove the correct
necessary outward-sign and wall-growth implications, not a
quantitative restriction on actual prime history.

### What additional prime arithmetic must actually achieve

Write \(B=R+1\), \(A=\lfloor R/2\rfloor+1\),
\(\sigma=\mathrm{sgn}(D_B)\in\{-1,1\}\), and
\(\delta_r=P_r-V_r\). The first-bad inequality gives

\[
\boxed{\sigma\sum_{r=A}^{B-1}\delta_r>W_B-\sigma D_A.}
\]

The prior-good anchor says \(\sigma D_A\le W_A\), so
the required outward accumulation is substantial. The
half-run FTA/wheel/Möbius decoder in the existing repository
gives an *exact* expression for the same sum,

\[
\sum_{r=A}^{B-1}\delta_r
=\frac12\sum_{r=A}^{B-1}
 \left(Q_{A,r}-\mathcal M_{A,r}-2V_r\right)
\]

when the proven cubic-depth restriction holds, where
\(Q_{A,r}\) is the *actual frozen-wheel survivor count* and
\(\mathcal M_{A,r}\) is its restricted signed Möbius census.
This is the genuine prime-supply decoder; no synthetic floor-Li
jump is inserted.

**Arithmetic seam:** prove an original-weight,
occurrence-preserving, historical correlation restriction that
forbids the corresponding oriented survivor/Möbius sum
from exceeding the actual wall clearance **at a putative
first bad**. Merely replacing \(\delta_r\) by the decoded
expression, or multiplying both sides by 2, is an identity,
NOT a restoring inequality. No old negative parent charge
may be independently spent for each later child.

The original Sector Six budget is a sufficient, stronger
pointwise certificate: \(E_R\le K_R\), with a nonnegative
opposite-sign correction. Since first bad already forces
\(E_R>0\) and \(K_R>0\), proving \(K_R\le0\) is **exactly**
the RH-strength arithmetic contradiction. A current-block
bound on \(P_R\) or a finite Möbius census does not control
the potentially wall-sized historical anchor \(D_R\).

### Circularity and numerical-testing boundaries

The owner-weighted Fubini identities are finite carrier
reindexings and do not *by themselves* use the desired
quantitative prime discrepancy. The status of the complete
native dependency graph still must be checked with the
opt-in full import-closure job and `#print axioms`.
The **explicit parameter** `ClassicalVonKochRHCriterion`
must be kept visible in any RH bridge theorem; do not
mislabel a conditional consumer as an unconditional proof.

Extending finite sieves verifies arithmetic and can catch
a mistaken correction coefficient, but cannot establish
first-bad exclusion. In particular, \(N_R>1/2\) and
\(K_R<0\) are already algebraically incompatible on the
original carrier because \(E_R\le K_R\). A search for
that combination cannot discover a new sign phenomenon.

Classical Littlewood oscillation plus short-interval
Brun--Titchmarsh estimates suggests the stronger
asymptotic observation \(\limsup N_R=1\) on actual primes:
the discrepancy can outweigh the local \(O(R/\log R)\)
physical mass along exceptional square indices. This
**has not been formalized in Lean here** and requires
real classical analytic inputs, not an invented local
cancellation law. Such occurrences are compatible with
remaining *inside* a growing RH wall.

The classical explicit formula for prime counts may provide
an alternative analytic approach, but there is currently NO
proved identity identifying the six owner sectors with a
grouping of zeta-zero terms. A conventional zero-free region
alone does not yield RH-order cancellation.

---


## 0C. Oct 9 adversary-vs-adversary: genuine historical sieve and near-wall test

**Status:** finite exact certificates plus new small Lean structural theorems.
No all-scale first-bad payment and NO RH proof.

### Attacker 1: freeze prime supply from a genuine prefix

Choose the genuine anchor A, fix D_A=pi(A^2)-VF_mid(A^2),
then impose synthetic future P_r=0. The first lower-wall
breach occurs at B. Because B<=A^2 in these examples, ALL
prime factors required to determine genuine primality through
B^2 were ALREADY PRESENT in the historical prime prefix <=A^2.

| Real anchor A | First zero-supply bad B | Frozen blocks | Breach past wall | Real primes in run | Minimum primes to avoid breach at B |
|---:|---:|---:|---:|---:|---:|
| 317 | 395 | 78 | 40.271857 | 4,729 | 41 |
| 1000 | 1102 | 102 | 95.150981 | 15,446 | 96 |
| 2000 | 2120 | 120 | 124.247283 | 32,441 | 125 |
| 5267 | 5417 | 150 | 536.4552 | 93,259 | 537 |
| 6000 | 6154 | 154 | 591.469814 | 107,382 | 592 |

Finite exact-integer prime censuses plus deterministic float VF weights.
The hypothetical ZERO-prime final block has original NNS N=1
because M=|D_previous|+V=|D_next|. These are synthetic paths,
NOT actual native Sector Six counterexamples.

### Defender 1: exact finite mathematical wheel/owner inequality

Put L=A^2, U=B^2-1, and select a small-prime cutoff y<=B.
Let Q_y be the product of actual primes p<=y and define

\[
 F_y(t)=\sum_{d\mid Q_y}\mu(d)\lfloor t/d\rfloor.
\]

This counts integers <=t not divisible by any p<=y.
Every composite n in (L,U] surviving this small wheel has
a genuine prime factor y<p<=B, and ALL these factor primes
are already in the prefix <=A^2. The arithmetic union bound is

\[
\boxed{
\pi(U)-\pi(L)\ge
\underbrace{F_y(U)-F_y(L)}_{S_y(L,U)}
-\underbrace{\sum_{\substack{y<p\le B\\p\ {\rm prime}}}
 [F_y(\lfloor U/p\rfloor)-F_y(\lfloor L/p\rfloor)]}_{T_y(L,U)}.
}
\tag{AD1}
\]

This is a GENUINE unconditional finite sieve inequality.
The correction T_y counts all high-owner hits and may OVERCOUNT
overlapping factors; it is not independently spendable NNS capacity.
No future prime indicator appears on the right.

At A=317,B=395, choosing y=7 (wheel Q=210) gives
S=12693, T=11178 and a *rigorous* 1515-prime lower count,
far more than the 41 needed to beat the proposed drought.
At y=13, Q=30030 and S=10650,T=7566 yield 3084.

At A=6000,B=6154, y=13 yields signed -30527
(S=359011,T=389538) and y=17 yields -8856
(S=337892,T=346748). Cutoff y=19 first gives a positive
certificate S=320109,T=311709, lower bound 8400,
beating the 592-prime requirement. However its
Q=9699690 exceeds the interval's 1,871,715 open sites,
so there is NO complete CRT period from which to infer an
all-scale phase uniformity bound.

Smallest tested successful y: 7,11,13,19,19 for
A=317,1000,2000,5267,6000.
For the project checkpoint A=5267,B=5417, cutoff y=19
certifies 274083-262893=11190 primes in the run, while
only 537 are needed to defeat a zero-prime first crossing. The growing-wheel incomplete
residue phase is the remaining bottleneck, not an
undocumented probability assumption.

### Attacker 2: keep GENUINE current primes, spoof only the near-wall anchor

The stronger adversary sets D_R=-W_R, thereby satisfying the
prior-good radial condition, while using the exact true prime
population P_R in the next block.

Define DeltaW_R=W_(R+1)-W_R. The fake-anchor next endpoint
crosses the lower wall if and only if

\[
\boxed{V_R-P_R>\Delta W_R.} \tag{AD2}
\]

The real P_R satisfies EVERY actual factor and wheel identity
in that block! Thus current-block factorization and the
abstract prior-good inequality ALONE cannot prevent escape.
The actual historical D_R must be carried throughout.

The finite independent scan R=8..6000 finds **333** genuine
lower-vulnerable blocks satisfying (AD2) and **324** genuine
upper-vulnerable blocks satisfying P_R-V_R>DeltaW_R.
These are fake-anchor scalar breaches only; no actual-prime
first-bad was found in these 5,993 blocks. Lower examples:

| Root R | Genuine P_R | V_R | Delta wall | Hypothetical breach | Actual D_R | Actual historical clearance D_R+W_R |
|---:|---:|---:|---:|---:|---:|---:|
| 425 | 56 | 70.292636 | 14.106529 | 0.186107 | -46.035259 | 5098.240535 |
| 2456 | 268 | 314.673957 | 17.612986 | 29.060971 | -180.235002 | 38164.257987 |
| 5065 | 547 | 593.830762 | 19.060416 | 27.770346 | -416.835777 | 85993.172614 |

The UPPER counterpart is even more directly relevant to the existing
5267 first-bad slack calculation. At R=5266, the COMPLETELY
GENUINE prime population is P_R=675; V_R=614.590437,
DeltaW_R=19.138243. With a fictitious prior defect
D_R=+W_R, the next endpoint violates the UPPER wall
by **41.271320** despite using all actual prime-factor
incidence in the current square band. The genuine historical
defect is D_R=-385.159422, not +W_R; its true upper
clearance W_R-D_R=**90634.144836**. The fake-anchor
original scalar NNS normalization is about **0.976684**.
This confirms exactly why the historical slack dominates
the local first-bad gradient in the project checkpoint.

These blocks remain safely inside the true wall.
Their ORIGINAL one-block NNS values using the FAKE anchor
are approximately 0.96472, 0.97609 and 0.97803 (>1/2).
The fake anchor is NOT pi(R^2)-VF_mid(R^2), and substituting
it into native owner Fubini is illegitimate.

### The exact historical buffer

The true scalar lower crossing is exactly

\[
\boxed{
D_R+W_R<(V_R-P_R)-\Delta W_R.
} \tag{AD3}
\]

The upper counterpart has buffer W_R-D_R and forcing
(P_R-V_R)-DeltaW_R. These are now Mathlib-only Lean theorems.
The missing **joint historical arithmetic** must prevent the
actual buffer and actual prime-factor incidences from
simultaneously satisfying the breach inequality. This is
NOT implied by knowing each current P_R exactly.

### Fixed wheel spoofing and first concrete counterexample

A primorial shift H=60060 preserves the prime congruences
2,3,5,7,11,13 but not the full growing wheel. The first
found spoof moves genuine prime 100501 to alleged prime
160561=307*523. That site is not divisible by any of the
first six primes but has a genuine historical factor 307.

### Branch deliverables and remaining status

The exact factor-lock theorem
vfV2HistoricalPrefixLocksPrime proves that actual primes
through A^2 determine primality of A^2<n<A^4. The
vfV2HistoricalDrought_iff_completeFactorCover theorem
rules out assigning an arbitrary prime-free future
without a genuine historical factor certificate.

The Mathlib-only finite owner-union theorem
vfV2FiniteOwnerUnion_card_le_sum, the generic
vfV2PartialWheelForcedPrimeLower, and the actual
Nat.Prime specialization
vfV2HistoricalPrimePartialWheelBonferroni
retain all high-prime overlaps and require no RH hypothesis.
Two further lemmas give the exact lower and upper
historical-buffer first-bad equivalences.

scripts/vf_mid_918_adversarial_sieve_duel.py regenerates
every numerical certificate and scans all 5993 real blocks for
both upper-wall and lower-wall fake-anchor vulnerabilities;
the seconds-fast #918 workflow runs it.

**Conclusion:** Four synthetic drought attacks are defeated
by elementary, genuine finite historical sieve arithmetic;
657 = 333 lower + 324 upper scalar fake-anchor attacks WITH GENUINE prime counts
show why local factorization alone cannot close the proof.
The original all-scale signed Sector Six historical payment
remains the unique open RH-strength theorem. No new proxy
or replacement denominator was introduced.

---


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
are in `VF_MID_FIRST_BAD_PAYMENT_V2_KERNEL.lean`:
`vfV2LiPlus_actual`, `vfV2LiMinus_actual`,
`vfV2Balance_factor`,
`vfV2Payment_of_floorLi_actual_signed_bounds`.
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
`vfV2OddCohortFloorLi_restores_primeError`.

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

- `vfV2HistoricalPositiveWallClearance`
- `vfV2HistoricalNegativeWallClearance`
- `vfV2PositiveFirstBad_requires_historicalPrimeLiExcess`
- `vfV2NegativeFirstBad_requires_historicalPrimeLiDeficit`

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
The checked-in complete vectorized experiment\n`scripts/vf_mid_918_crossblock_moments.py`\ncompleted in ~4.4 sec
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
(`RHLean.Analysis.finiteTargetScaledSchur_target_invariant`).
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
`abs(sum q)` differs from `sum abs(q)`. Thus an impressive
aggregate-first NNS anticorrelation is NOT the normalized
physical-seat coefficient of #918's actual original carrier.

An added seconds-fast CI audit computes *all four* literal
seat-first quadrants at t=0 and t=+/-0.1, computes the
aggregate-first quadrants at t=0, and **asserts exact signed
Gram equality** (to floating verification tolerance), without rebuilding StrongPNT; the complete scientific cohort study is an independently opt-in script.

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
nonpositive Co-Div energy. The full raw Co and Div matrices are separately available in\nthe checked-in opt-in cross-block experiment; normalizing
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
`vfMidOddHistoricalCurrentSeatGram_eq_endpointPolarization`
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


## 4D. State-dependent transition operators: connect the OLD 27-state cube
to the ACTUAL VF midpoint square-block dynamics

This is a direct crosswalk to the existing, already formalized transition
work. **Do not mistake 27-state Möbius sign statistics for a Markov law
on actual prime counts.** The two carriers must be kept distinct.

### Already-proved 27-state ternary/8-state signed physical transition model

The genuine Möbius cells are

$
S_k=(\mu(4k+1),\mu(4k+2),\mu(4k+3))
\in\{-1,0,1\}^3.
$

The full space has 27 states, of which only eight have no zero
coordinates. The **other 19 states must be retained** as an explicit
zero-sector defect. The existing main modules

- `RHLean/Analysis/ThreeSlotMertensDegreeOneProjection.lean`
- `RHLean/Analysis/PhysicalDegreeOneMixingConjecture.lean`
- `RHLean/Analysis/PhysicalPartialMomentSchur.lean`
- `RHLean/Analysis/FinitePrimeTMixing.lean`
- `RHLean/Analysis/DeterministicTGreenKuboComparison.lean`

prove exact integer transition counts, a degree-one Walsh observable,
zero-sector remainder, target-invariant physical Schur covariance,
complete-period prime-local finite transfer, and exact lagged signed
energy reassembly. They **do not prove** an asymptotic bound on the
incomplete physical transition matrix. The outstanding analytical
statement `PhysicalDegreeOneMixingConjecture` remains a named
unproved proposition.

The archived empirical eight-state *conditioned* row matrix at
$x=10^7$ has maximum entrywise deviation about **0.003305**
from a uniform $1/8$ row. The COMPLETE local odd-prime three-slot
Walsh eigenvalues are

$
\lambda_{p,j}=1-\frac{2j(p-1)}{p^2-3},\quad j=1,2,3.
$

The six-coordinate **transition** transfer has a different
$p^2-6$ denominator. These are distinct finite CRT operators.
Neither eigenvalue product automatically controls an INCOMPLETE
physical square-block prefix. Its endpoint/zero-sector boundary
has to be bounded in retained physical signs and weights.

The degree-one Möbius statistic encodes Mertens, not $\pi$:
even though an actual prime has $\mu(p)=-1$,
an odd squarefree product of three distinct primes also has
$\mu(n)=-1$. Consequently a negative Möbius state is NOT
an actual prime event. A transfer to #918 must preserve the
prime-indicator decoder/actual first-owner sieve, original
$R$ odd seats and full native $w_R=V_R/R$ reference mass.

### Empirical ACTUAL pi square-block transitions

These are NEW finite diagnostics for R=8..6000, evaluated from
true prime counts. The state is the **fixed target 0**
of $e_R=P_R-V_R$, not a moving empirical mean.

| current $e_R$ sign / next | next below VF | next above VF |
|---|---:|---:|
| below | 1421 (46.882%) | 1610 (53.118%) |
| above | 1610 (54.374%) | 1351 (45.626%) |

The empirical conditional nonconstant eigenvalue IF one modeled
this coarse two-state table as a Markov kernel is about **-0.074913**.
There is NO proof the actual arithmetic process is Markov, autonomous,
or that these probabilities hold in unobserved root regimes.

The actual $P_R-F_R$ sign, with $F_R$ the floor-Li integer demand,
has the full **three-state** transition count table:

| row / next | negative | zero | positive |
|---|---:|---:|---:|
| negative | 1296 | 125 | 1483 |
| zero | 110 | 16 | 125 |
| positive | 1498 | 109 | 1230 |

The stronger high-q/smooth sector sign transitions should NOT
be interpreted as three independent sources. The exact
$\delta_P+\delta_G+\delta_H=0$ forces all three sector errors
to share an algebraic conservation law; floor-Li event phases also
change across scales.

### Actual VF-midpoint WITHIN each square block

Split at integer $m_R=R^2+R$, directly below the geometrical
midpoint $R^2+R+\tfrac12$. The exact reference advance to the
integer split is the existing live VF-mid interpolation

$
V_R^{\mathrm{first}}=
\frac{R}{\log(R^2+R/2)},\qquad
V_R^{\mathrm{second}}=V_R-V_R^{\mathrm{first}}.
$

Here $P_R^{\mathrm{first}}=\pi(m_R)-\pi(R^2)$ and
$P_R^{\mathrm{second}}=\pi((R+1)^2)-\pi(m_R)$.
Both are ACTUAL primes. Their signed deviations sum EXACTLY
to $e_R$; the same fixed original full-block odd-seat VF
mass $V_R$ is used, with **no new even prime candidate**.

Observed within-block transition counts:

| first-half state / second-half | second below VF | second above VF |
|---|---:|---:|
| first below VF | 1383 | 1605 |
| first above VF | 1634 | 1371 |

First-half below predicts second-half above with conditional
frequency **53.715%**; first-half above predicts second-half
below with frequency **54.376%**. Across all 5,993 blocks,
within-block Pearson is **-0.098403** and target-zero
aggregate NNS **-0.154673**. For the end-of-block second
half to the NEXT block's first half, Pearson is **-0.096360**
and NNS is **-0.150727**.

Do not confuse this live midpoint reference with an artificial
uniform half-splitting of odd-seat weights: the max measured
difference from $(\lfloor R/2\rfloor)w_R$ is **0.148832**.
The original #918 proof still uses the full block original
carrier with $V_R=Rw_R$.

### Conditional restoration at greater empirical wall pressure

For each R let $D_R$ be the **ACTUAL** historical endpoint
defect and $W_R=2R\log R$. To avoid guessing the future
sign, orient the next increment using the earlier history:

$
\mathrm{outward}_{R+1}
=\operatorname{sgn}(D_R)\,[P_{R+1}-V_{R+1}].
$

Negative values are inward. On the 5,992 consecutive transitions:

| historical wall occupancy stratum | n | next move inward | mean next outward increment |
|---|---:|---:|---:|
| bottom decile of $|D_R|/W_R$ | 600 | 43.50% | +1.9373 |
| top decile of $|D_R|/W_R$ | 600 | 51.83% | -0.3562 |
| middle 50% | 2996 | 50.27% | -0.3390 |

In the **three fixed root bands** 8..1000, 1001..3000,
3001..6000, the top wall-occupancy quintile has empirical
next-inward probabilities **51.76%, 56.75%, 57.17%**.
This finite evidence hints at state-dependent restraint.

**Critical limitations:** Every sampled $D_R$ is NEGATIVE,
so there is no observed positive-wall restoration sample.
The MAXIMUM observed wall occupancy is only
**0.045990 at R=15**, i.e. below five percent of the
$K=2$ wall, nowhere near first badness. Occupancy strata
select different root regimes, so these conditional
frequencies do not isolate a causal or stationary transition
law. They cannot be used to infer boundary-proximate behavior.

To distinguish occupancy-conditioning from the TRIVIAL
last-sign alternation, a second explicit finite split holds the
most recent block sign fixed and compares the top 20% of
historical wall occupancy against the remaining 80%:

| immediately preceding VF block | P(next above VF), remaining 80% | P(next above VF), highest 20% |
|---|---:|---:|
| preceding BELOW VF | 52.00% (2475 states) | 58.09% (556 states) |
| preceding ABOVE VF | 45.25% (2318 states) | 46.97% (643 states) |

This persists descriptively after controlling one lag-one sign,
but still does NOT control the hidden prime-residue state,
time-scale variation, or an unobserved near-wall regime.
The actual-prime panel is deterministic, not a random Markov
training sample, and conditional percentages cannot be multiplied
to obtain an all-scale cumulative-tail theorem.

The sign-runs are short in this observed window
(max ten consecutive under-VF, seven consecutive over-VF).
There is no deterministic all-$R$ maximum-run theorem.

### "101 acts like 2": retain the chronological delay

The genuine prime 101 occurs in square block R=10.
Its even child 202 is in block R=14 and has ZERO
independent physical odd-seat charge; its first odd
composite child 303=3*101 occurs only in block R=17.
Thus the same-prime odd composite owner mechanism
is NOT universally a next-block immediate reversal.
A next-block empirical anticorrelation alone cannot
identify the owner-level source of the feedback.

At scale R, a high prime factor q has potential odd
future descendants c*q and is active on cofactor
windows with their own root entry times. The proof
needs their **exact signed nonlocal transition kernel**
and smooth-composite restoration, not the stationary
two-state sign Markov approximation.

### Reproduction and the actual unproved theorem

Run the opt-in `crossblock_moments` workflow input,
which calls `scripts/vf_mid_918_crossblock_moments.py`
and publishes additional outputs:

- `state_transition_summary.json`: all physical-prime sign matrices,
  live midpoint matrices, row normalization, conditional fixed
  historical states and observed wall occupancy;
- `state_dependent_restoration.csv`: whole-panel, fixed
  root-window and occupancy-conditioned transitions;
- `midpoint_halves.csv`: every integer midpoint actual-prime
  count and signed VF-half discrepancy.

The exact twenty-seven-state Walsh transport is **not**
the two-state prime-count Markov surrogate.
For a deterministic proof, the admissible extended physical
state would have to retain relevant residue/owner phases,
the actual first-owner/prime decoder, the signed smooth-core
completion, and the historical $D_A$. Only after establishing
a weight-preserving physical pushforward AND an incomplete-CRT
frontier bound could a quantitative transition estimate
control the original first-bad historical Gram.

A candidate estimator for conditional one-step expectation is
not the required pointwise arithmetic inequality.
**No step of the proof currently bounds the true owner-driven
positive-lag accumulation uniformly near the hypothetical wall.**


## 4E. Sparse-tier owner attack: exact prior-half-run ancestor theorem (Oct 9)

**Status:** the new sparse owner/cofactor transport, prime-semiprime/triple
partition, residual calibration, original Co/Div expansion, and numerical
regressions are proved or verified as stated below. Their *global signed
near-wall payment* is still OPEN. In particular, empirical lag-one
anticorrelation is NOT a pointwise owner-restoring theorem.

### 4E.1 The strict-open, parity-locked least-owner partition

The ORIGINAL physical source is exactly the R odd integers
`n` with `R^2 < n < (R+1)^2`. In particular, upper prime squares
are **excluded**, even though the defect recurrence can use pi at closed
square endpoints because a square greater than 4 is composite.

Write `ell(n)` for the smallest prime factor of an odd composite.
For every physical composite, `ell(n) <= R` because
`ell(n)^2 <= n < (R+1)^2`. Define disjoint native counts:

$
\begin{aligned}
G_R&=\#\{n:\ R^2<n<(R+1)^2,\ n\ {\rm odd\ composite},
                         \ell(n)^2\le R\},\\
S_R&=\#\{n:\ R^2<n<(R+1)^2,\ n\ {\rm odd\ composite},
                         R<\ell(n)^2\}.
\end{aligned}
$

The exact no-double-counting partition is

$
\boxed{P_R+G_R+S_R=R.}
\tag{E1}
$

**A p hit is not a p owner.** At R=100, the square 101^2=10201 is the
EXCLUDED upper boundary. The single interior multiple of 101 is even,
so **there are ZERO original 101-owned sites**, not one. At R=101 there
are two interior 101 multiples, exactly one odd and uniquely owned by
101: the semiprime 101*103=10403. The previous boundary-count assertion
`unique_p==1 and count_square==1` for R=100 was false and caused
the previous fast CI to fail. It has been corrected; no square is
counted as a phantom restoring physical source.

### 4E.2 Exact TWO/THREE-factor theorem for every sparse owner

Let `p=ell(n)` in the sparse tier, so `R<p^2`.
Since p^2 and R are integers, p^2 >= R+1. If n had FOUR
prime factors (with multiplicity), each would be >=p, implying

$
 n\ge p^4\ge(R+1)^2,
$

contradicting the STRICT upper physical boundary. Thus every
sparse-owned composite has Omega(n)=2 or Omega(n)=3.

In the two-factor case, write n=pq, p<=q primes. Since p<=R and
n>R^2, **q>R**. The semiprime sparse packet has the exact finite
prime-interval formula

$
\boxed{
S_R^{(2)}
=
\sum_{\substack{p\ {\rm prime}\\ \sqrt R<p\le R}}
\left[
\pi\!\left(\left\lfloor\frac{(R+1)^2-1}{p}\right\rfloor\right)
-\pi\!\left(\left\lfloor\frac{R^2}{p}\right\rfloor\right)
\right].
}
\tag{E2}
$

In the three-factor case, n=pqt with primes p<=q<=t and
p^2>R. If t>=R+1 then n>=p^2(R+1)>=(R+1)^2,
impossible. Therefore the entire **triple-smooth remainder**
has **all three prime factors <=R**. This is a finite
number-theoretic classifier, not a heuristic bucket or an extra
NNS source:

$
\boxed{S_R=S_R^{(2)}+S_R^{(3)}.}
\tag{E3}
$

All counts were independently checked using a segmented least-prime
sieve and the separate prime-interval formula (E2).

| R | Actual P | Mature G | Sparse S | Sparse semiprimes | Sparse triples |
|---:|---:|---:|---:|---:|---:|
| 8 | 4 | 0 | 4 | 3 | 1 |
| 100 | 23 | 54 | 23 | 18 | 5 |
| 101 | 22 | 54 | 25 | 22 | 3 |
| 119 | 19 | 65 | 35 | 34 | 1 |
| 317 | 54 | 201 | 62 | 56 | 6 |
| 1027 | 144 | 710 | 173 | 161 | 12 |
| 1760 | 204 | 1250 | 306 | 281 | 25 |
| 5267 | 617 | 3929 | 721 | 644 | 77 |
| 6000 | 698 | 4490 | 812 | 724 | 88 |
| 10201 | 1096 | 7783 | 1322 | 1169 | 153 |

Over ALL 5,993 true-prime blocks R=8..6000, precisely
**88.9695784%** of sparse composites are the genuine prime-prime
semiprime packet (E2), and the remaining **11.0304216%** are
the three-factor packet. This constrains the arithmetic proof
to two finite factor shapes instead of a freely branching owner tree.

### 4E.3 The real half-run ancestry theorem

Set `A=floor(R/2)+1`. For EVERY R>=9, p^2>R implies
p>=4, and integer arithmetic gives

$
R+1\le 2A,\qquad
p\,A^2\ge4A^2\ge(R+1)^2.
$

Consequently, for **every sparse composite n=p*c** on the
original physical carrier,

$
\boxed{c< A^2,\qquad A=\lfloor R/2\rfloor+1,\quad R\ge9.}
\tag{E4}
$

The result covers semiprime parent q as well as the entire
two-prime cofactor of a sparse triple. It needs NO prime
equidistribution assumption. The R=8 exceptional possibility
is genuine: 75=3*(5*5), where the cofactor 25 equals A^2,
so the Lean lemma correctly starts at R>=9.

This is now a **formal Mathlib-only Lean theorem**
`vfV2SparseCofactorBeforeHalfAnchor` in the existing kernel,
rather than a conjectured ancestor cutoff. Its companion
`vfV2SparseFourFactorImpossible` formalizes the four-factor
exclusion. Every sparse cofactor is within the *prior-good
historical square range* of a hypothetical first bad.

**Crucial no-double-spend limitation:** for semiprime n=pq, the
genuine negative prime seat at q lies in an EARLIER square
block, below A^2. Its contribution is ALREADY represented in
the compressed historical anchor D_A. It does not create
a new negative site in the current original R-seat NNS norm.
Merely finding a prior-good parent cannot restore the required
CURRENT signed Gram unless a true charge-conserving boundary
map is proved.


### 4E.3a One high-prime parent has at most one odd child per block

Fix R and any integer q>R. If two DISTINCT odd cofactors c,d
produced q*c and q*d strictly inside (R^2,(R+1)^2), then
|c-d|>=2, hence

$
|qc-qd|\ge2q\ge2R+2>2R+1=(R+1)^2-R^2.
$

This is impossible. Therefore

$
\boxed{\text{Each }q>R\text{ has at most ONE odd child in block }R.}
\tag{E4a}
$

The Mathlib-only Lean theorem
`vfV2HighFactorOneOddChildPerOpenBlock` establishes this
one-block occurrence injection. The opt-in true-prime owner
probe checks each q>R occurs at most once among the original
odd c*q sites. The theorem complements the prior-good
cofactor bound (E4).

**Crucial limitation:** this injection is valid for ONE fixed
root R. The SAME historical prime q can have different
odd cofactor children in different blocks; its original
negative NNS charge cannot be paid again in each block.
Across-block occurrence multiplicity and the old D_A
historical anchor still need a native, weighted signed proof.

### 4E.4 First-owner Fubini AND exact boundary Abel transform

For p prime, define the rough-cofactor prefix

$
F_p(t)=\#\{c\ {\rm odd}: c\ge p,\ pc\le t^2,\
                 q\nmid c\ \forall q<p\ {\rm prime}\}.
$

If N_{r,p} counts actual odd interior composites of least owner p,
then exactly

$
\boxed{N_{r,p}=F_p(r+1)-F_p(r)-b_{r,p},}
\tag{E5}
$

where b_{r,p}=1 if the odd upper square (r+1)^2 itself has
least-prime owner p, and zero otherwise. NEVER silently remove
this boundary correction; R=8, n=81, owner 3 is a witness.

The full sparse-tier VF packet retains the physical weight
`w_r=V_r/r`:

$
\begin{aligned}
\mathcal S_{A,B}
 &=\sum_{r=A}^{B-1}w_r
       \sum_{\substack{p\ {\rm prime}\\p\le r<p^2}}N_{r,p}\\
 &=\sum_{p\ {\rm prime}}\ 
       \sum_{r=\max(A,p)}^{\min(B,p^2)-1}w_rN_{r,p}.
\end{aligned}
\tag{E6}
$

Empty ranges contribute zero. The on-branch Lean lemma
`vfV2SparseOwnerFubini` proves the finite
weight-preserving summation interchange with an abstract
occurrence-count N; the prime/rough-cofactor ownership
classification is separately checked arithmetically.

For a fixed p and a<=r<b, the exact Abel transform is

$
\boxed{\begin{aligned}
\sum_{r=a}^{b-1}w_rN_{r,p}
={}&w_{b-1}F_p(b)-w_aF_p(a)\\
&+\sum_{r=a+1}^{b-1}(w_{r-1}-w_r)F_p(r)
 -\sum_{r=a}^{b-1}w_rb_{r,p}.
\end{aligned}}
\tag{E7}
$

For p=101, the **216** successive roots 101<=r<317
have 141 UNIQUE first-owner hits, all semiprimes. Both native
site integration and (E7) give, independently,

$
\boxed{\sum_{r=101}^{316}w_rN_{r,101}
=26.456125656779307\ldots .}
\tag{E8}
$

The numeric value is **weighted original VF positive mass**;
it is NOT 26.456 units of freely spendable independent
negative parent energy. The fast stdlib regression checks
the exact 141 count and the independent Abel equality.

### 4E.5 Floor Li on the mature-survivor / sparse-owner buckets

Let `Q(x)=floor(Li_2(x))` be ONLY a deterministic reference
and `F_R=Q((R+1)^2)-Q(R^2)`. The mature-owner survivors are

$
T_R=R-G_R=P_R+S_R.
$

Set the calibrated floor-Li **sparse benchmark**

$
\widehat S_R=T_R-F_R.
$

Unlike fabricated floor-Li prime owners, this projects Li
demand onto the ACTUAL mature-sieve survivor set; it
introduces no fake physical sites. Define the genuine
signed sparse surplus

$
\boxed{
\sigma_R=S_R-\widehat S_R
        =F_R-P_R=-(P_R-F_R).
}
\tag{E9}
$

This is proven symbolically by
`vfV2SparseOwnerFloorLiResidual`.

| R | Actual S | floor-Li demand F | projected sparse T-F | actual sparse surplus sigma |
|---:|---:|---:|---:|---:|
| 119 | 35 | 25 | 29 | +6 |
| 317 | 62 | 55 | 61 | +1 |
| 1027 | 173 | 148 | 169 | +4 |
| 1760 | 306 | 236 | 274 | +32 |
| 5267 | 721 | 615 | 723 | -2 |
| 6000 | 812 | 690 | 820 | -8 |

The opt-in original owner probe can be run with `--sparse-full` to
reproduce the full-panel count of **2,318,557** sparse semiprimes and
**287,454** sparse triples (and both lag-one correlations) without
changing production Lean or the ordinary seconds-fast lane.

Across R=8..6000, raw sparse counts correlate nearly +1
because their base levels grow. That trend must NOT be
confused with restoration. The calibrated sigma residual's
lag-one Pearson is **-0.097081** (the negative of the
prime-floor-Li error process has the SAME autocorrelation,
since both coordinates are multiplied by -1). This is weak
empirical anticorrelation, NOT a quantitative bound on its
partial sums or a proof near the wall.

The historical defect transport is EXACT:

$
\boxed{
D_B=D_A+
   \underbrace{\sum_{r=A}^{B-1}(F_r-V_r)}_{\beta_{A,B}\text{ deterministic}}
   -\sum_{r=A}^{B-1}\sigma_r.
}
\tag{E10}
$

Consequently, EVERY unknown actual-prime deviation from the
floor-Li benchmark in this owner partition lives in the
calibrated sparse-owner surplus; the mature survivor count
is determined by the lower sieve. This makes the proposed
signed error transparent, but does **not** independently
bound it: (E9) means a uniform RH-strength bound on the
cumulative surplus is itself RH-strength.

### 4E.6 The COMPLETE native Co/Div requirement and proof boundary

The one-block original anchored masses are unmodified:

$
\begin{aligned}
U_R &=(-D_R)_++w_R(G_R+S_R),\\
L_R &=(D_R)_++(1-w_R)P_R.
\end{aligned}
$

Set `U0=(-D_R)_++w_R G_R`, `s=w_R S_R`.
Then the exact complete, cross-owner-preserving expansion is

$
\boxed{
\begin{aligned}
\mathcal B_R
=6U_RL_R-U_R^2-L_R^2
&=(6U_0L_R-U_0^2-L_R^2)\\
&\quad +6sL_R-2sU_0-s^2.
\end{aligned}}
\tag{E11}
$

The standalone Lean lemma
`vfV2SparseCoDivFullCrossTerms` checks (E11).
It prevents us from counting the favorable 6sL_R without
its adverse 2sU0+s^2 cross-owner cost.

**The strongest new arithmetic fact is (E4): ALL sparse
cofactors are below the prior-good half-run square.**
This provides the exact domain in which the earlier
compiled historical first-owner / restricted-reciprocal
contraction lemmas can be applied, WITHOUT an extra
statistical independence assumption. But to close RH
one STILL has to produce a native **signed**, occurrence-
matched, weight-conserving inequality for (E11)
or equivalently a historical surplus barrier in (E10)
which excludes every first-bad wall approach.

Concretely, write W_B=2B log B. The first-bad exclusion needs

$
\boxed{
-W_B\le
D_A+\beta_{A,B}-\sum_{r=A}^{B-1}\sigma_r
\le W_B
\quad\text{for the hypothetical first-bad history}.
}
\tag{E12}
$

Equation (E12) is a **target**, not a theorem: by (E10)
it is exactly the wall constraint. The proof would need a
NEW actual-prime signed estimate on the rough-cofactor
incomplete-wheel phases (or a valid conserved Gram payment)
to establish it. The finite R=8..6000 checks and an
empirical transition matrix do not establish this estimate.

Also, the old main first-bad radial lemma already shows that
at a HYPOTHETICAL first bad the production half-NNS
inequality must FAIL. Hence simply proving the half gate
from local owner-count inequalities is impossible: the
historical arithmetic must actually eliminate the
near-wall trajectory. The exact cross-owner signed
remainder is the unproved mathematical seam.

**Progress classification:** exact sparse factor geometry,
cofactor descent, finite Fubini, algebraic Gram split:
PROVED (kernel / elementary arithmetic); numeric
semiprime/triple and Abel scans: VERIFIED FINITELY;
actual-prime first-bad historical payment (11):
OPEN. No RH claim.



## 4F. Sector Six is still the production objective: cross-block once-charge obstruction (Oct 9)

**This section corrects an interpretation of 4E.** The sparse
semiprime/triple partition is NOT a different sufficient theorem and
has NOT proved the original Sector Six cone. The empirical
`sigma_R=F_R-P_R` is an exact restatement of prime supply and its
lag correlation cannot bind historical wall slack. The last open
production gate remains the one declared in
`VFMidMinimalActualFirstBadPaymentV2Statement`, equivalently:

$
\boxed{
\mathrm{FirstBad}_{2}(R+1)\Longrightarrow
6U_RL_R-U_R^2-L_R^2\ge 0.
}
\tag{F1}
$

The main repository's compiled route
`vfMidActualPrimeFirstBadAt_two_succ_false_of_activeSixBoundaryBudget`
instead uses the original owner-sector boundary:

$
\boxed{
\operatorname{ActiveGlobalResidualExcess}(R)
+2\,\operatorname{SixOrientedIncompleteBoundaryMass}(R)\le0.
}
\tag{F2}
$

That is a SHORT NAME for the exact six nested first/next/returned
left/right raw-parent `Finset` sums in
`VF_MID_FIRST_BAD_ACTIVE_RAW_PARENT_SPLICE.lean`, **not** a new
unproved equivalence. Its exact inequality is STILL OPEN. The
weighted first-owner Fubini and existing sector-six decomposition
already express the anchored source and retain all diagonal,
squareful, omitted-site and residual contributions. The sparse tier
can feed these native sectors only through an incidence-preserving
source-to-boundary classifier **on their original weighted carrier**.

### 4F.1 Why an old prime's one negative site CANNOT pay its own later children

For a fixed old odd prime q, consider its sparse *semiprime*
descendants n=pq with p another odd prime. Their root is
r=floor(sqrt(pq)), and the least owner p is sparse exactly when

$
\boxed{p<q<p^3.}
\tag{F3}
$

All such n lie in a distinct open square block
r^2<pq<(r+1)^2, with p<=r<p^2 and q>r.
The distinct-root claim follows from the previously proved
`vfV2HighFactorOneOddChildPerOpenBlock`.

Thus the exact number of those children is

$
\boxed{
N(q)=\pi(q-1)-\pi(\lfloor q^{1/3}\rfloor).
}
\tag{F4}
$

For q>=11 there is only ONE earlier original prime-negative
site at integer q (for the exceptional smaller roots, the native
signed value must be used rather than asserting a negative sign).
For q>=11, its original absolute negative weight is

$
h_q=1-w_{\lfloor\sqrt q\rfloor}.
$

But each of the N(q) later positive physical composite sites has
its OWN weight w_r. Since r<q, for q>=5 we have

$
w_r=\frac{2r+1}{r\log(r^2+r+\frac12)}
     >\frac{1}{\log q}.
$

Hence, with genuinely different later blocks,

$
\boxed{
C_q:=\sum_{\substack{p\ {\rm prime}\\p<q<p^3}}w_{\lfloor\sqrt{pq}\rfloor}
>\frac{N(q)}{\log q}.
}
\tag{F5}
$

The ordinary PROVED prime number theorem implies
`N(q)~q/log(q)` along primes q, so
`C_q` grows at least on the order of `q/(log q)^2`, while
`h_q` stays bounded and approaches 1. **Therefore a proposed
per-old-prime bound C_q<=h_q is false for arbitrarily large q**,
independently of RH. It cannot be the Sector Six payment.

Concrete full actual-prime regressions:

| Historical prime q | Original prime root | Original negative h_q | Distinct sparse semiprime children N(q) | Later positive VF mass C_q | C_q/h_q |
|---:|---:|---:|---:|---:|---:|
| 101 | 10 | 0.553667784804 | 23 | 5.743609659795 | 10.37 |
| 997 | 31 | 0.705479535555 | 163 | 25.886856393834 | 36.69 |

The seconds-fast actual-primes test checks these independently by
enumerating actual prime p, genuine semiprime pq, actual root r,
unique open-block incidence and original w_r. It also checks
the exact p<q<p^3 classification and weight lower bound.

### 4F.2 Lean: the high-prime q charge is SUBTRACTED ONCE, not per child

Two more Mathlib-only lemmas in the SAME seven-file #918 scope:

* `vfV2HighParentChargeOnceFubini` interchanges the history/root
  sum with the high-prime-parent q sum while subtracting the old
  prime-negative weight **exactly once per q, outside the child sum**.
* `vfV2HighParentRepeatedChargeOvercount` displays the false
  extra restoring allowance when the same old h_q is subtracted
  once per descendant:

$
\boxed{
\sum_{c\in \mathrm{Kids}(q)}(w_c-h_q)
+\bigl(\#\mathrm{Kids}(q)-1\bigr)h_q
=\sum_{c\in \mathrm{Kids}(q)}w_c-h_q.
}
\tag{F6}
$

The `(#Kids-1)*h_q` correction is not optional. The q=101
family would otherwise spend the original historical negative
23 times; q=997, 163 times.

**Importantly:** D_A already contains the historical q-site and
its contribution, so the Fubini lemma is a tool for an EXACT
decompression of D_A, not permission to subtract h_q again
from an already-anchored source. The full original physical
`M_R^2` denominator and signed Gram cross-owner products
must be reconstructed *after* this once-only accounting.

### 4F.3 Remaining FIRST-BAD payment, with no substitute target

The sparse tier tells us where historical cofactors live:
below A^2 for A=floor(R/2)+1. It does NOT say how signs of
their **reused** parent occurrences combine. Moreover the
old negative parent h_q, although within the prior-good
anchor, is not free capacity that can pay every later child.

The next *arithmetic* step is a genuinely **signed**
incidence-preserving mapping of the once-counted historical
q charges and their many later positive p*q children into
the MAIN Sector Six incomplete left/right raw-parent
fibers, retaining the other Gram/diagonal and residual terms.
Its quantified conclusion must be the bound (F2), or the
unchanged first-bad payment (F1), based on a NEW restriction
on actual prime-factor residue phases. The previous elementary
summation identities and the PNT alone give NO sign for this
complete weighted source.

The hypothesized channel slacks at A, whether denoted
`S_A^+` or `S_A^-`, must not be treated as additional
uncompressed material. Their conservation is exactly what
the missing bound must establish. A sequence can approach
the wall through many ordinary blocks. One-block negative
autocorrelation, individual Euler-star nonexpansion,
and the half-run prior-good status do not rule out such
a walk.

**Final mathematical status:** F3-F6 are exact relations
(the numeric table is a finite audit; the PNT asymptotic is
an ordinary-paper deduction from established PNT).
The Lean lemmas prove their algebraic once-charge content.
F1/F2 still require a new actual-prime signed theorem.
We have not proved RH and should not describe this work
as a resolved Sector Six cone.



## 4G. Complete admissibility-rule audit and TRUE localized Möbius decoder

This is the response to the request to **establish all the required
admissibility rules**, without treating an open signed assertion as proved.
Two new Lean artifacts in #918 intentionally keep very different
certainty levels separate:

* `research/VF_MID_FIRST_BAD_PAYMENT_V2_KERNEL.lean` now proves
  Mathlib-only generic monotone 0/1 step-counting, the true prime/nonprime
  finite-seat split, exact weighted signed prime-site charges, unique-owner
  Fubini for *any* covering finite owner assignment, and the once-counted
  historical charge law. These results are unconditional.
* `research/VF_MID_FIRST_BAD_ACTUAL_ADMISSIBILITY_CERTIFICATE.lean`
  assembles twelve existing actual-prime arithmetic identities into
  `VFMidActualPrimeVerifiedStructuralRules` and proves its witness
  `vfV2ActualPrime_verifiedStructuralRules`. It imports the original
  production graph, so compilation and `#print axioms` require the
  optional cached full-native CI; the underlying lemmas already live
  on `main`. Do **not** report this new composite native declaration as
  kernel-checked until that job completes.

### 4G.1 Rules already present in the TRUE prime arithmetic

| Rule | Exact original production theorem | Result type |
|---|---|---|
| Monotone 0/1 jumps | `vfV2GenericUnitStepCount_succ`, `..._monotone` | Generic Boolean counting function, Mathlib only |
| Exactly R odd seats | `vfMidOddCandidateSeats_card` | Actual open square block |
| VF reference on original seats | `vfMidOddFractionalPrimeSeatWeight_sum` | Sum native w_R = V_R |
| Actual prime-site filter | `vfMidOddCandidateSeats_filter_prime` | Literal `Nat.Prime` on original sites |
| FTA prime/composite partition | `vfMidOddActualComposite_card_add_primeSupply` | P_R+C_R=R |
| Exact signed charges | `vfMidOddSignedSeatCharge_sum` | Sum (w_R-1_Prime)=V_R-P_R |
| Unique least-prime owner | `vfMidOddCompositeTrackingDefect_eq_ownerCensus_sub_reference` | Every composite counted once |
| Restricted depth-two Möbius decoder | `vfMidOddSignedSeatCharge_eq_affineCenter_add_half_moebius_of_cube` | On a FROZEN rough survivor carrier under cubic cutoff |
| Historical source charged once | `vfMidActualPrimeEndpointDefect_eq_anchor_sub_frozenAffineRun` | Actual D_B = D_A - signed owner run |
| Original NNS denominator | `vfMidFirstBadZeroTargetTotalMass_eq` | Exact anchored L1 square |
| Complete signed Co/Div ledger | `vfMidFirstBadAnchoredCoDivExcess_eq_activeResidual_add_weightedCells` | No deleted diagonal, squareful or cross-owner terms |
| Returned Sector Six weld | `vfMidActiveCellGram_eq_scaledReturnedClippedCellMass` and `vfMidActiveScaledReturnedClippedCellMass_eq_sixOrientedSectors` | Actual weighted incomplete raw-parent sectors |
| First-bad strict direction | `vfMidActualPrimeFirstBadAt_two_succ_nnsNormalized_gt_half` | First bad => original NNS > 1/2 |

The new generic once-owner theorem
`vfV2UniqueOwnerOnceCharge` and existing
`vfV2HighParentRepeatedChargeOvercount` prevent the dishonest shortcut
of spending a historical prime-negative charge once per child.

**Limit of the cube decoder:** It is proved on the restricted
`vfMidSquarePrefixWheelSurvivors A r` set when
`(r+1)^2 <= (A+1)^3`. One must not apply the affine
prime/semiprime formula on arbitrary odd composites, where triple
and higher factor signs occur.

### 4G.2 Genuine LOCAL signed Möbius census, in exact original units

Write
`Q_{A,r} = #vfMidSquarePrefixWheelSurvivors(A,r)` and
`M_{A,r} = sum_{n in vfMidSquarePrefixWheelSurvivors(A,r)} mu(n)`.

In a finite frozen-wheel run `A <= r < B`, provided
`3 <= A` and `(r+1)^2 <= (A+1)^3` throughout, the repository's
true rank-two Möbius prime decoder proves

$
\boxed{2P_r=Q_{A,r}-M_{A,r}.}
$

Summing and subtracting the EXACT VF midpoint band masses gives

$
\boxed{
2(D_B-D_A)=
\sum_{r=A}^{B-1}\left(Q_{A,r}-M_{A,r}-2V_r\right).
}
\tag{F7}
$

Two new native Lean theorems express this finite TRUE arithmetic
relation with all cube and interval hypotheses explicit:

* `vfV2ActualPrimeFrozenRunMobiusDecoder`;
* `vfV2ActualPrimeFrozenRunMobiusDeviation`.

This is an exact **localized signed owner-balance identity**,
not the corresponding **localized quantitative bound**. It is a
more precise translation of the user's Möbius-density argument
into the actual physical survivor population.

Why ordinary proved densities are not a proof of the latter:
`M(x)=sum_{n<=x}mu(n)=o(x)` estimates μ on ALL integers, not
the restricted rough set, and offers no rate at
`H=O(sqrt(x) log(x)^2)=o(x)`. Even equality of limiting odd
squarefree positive/negative proportions does not estimate
the centered sum in (F7) uniformly for EVERY finite frozen
historical window. That localized arithmetic is the missing
Sector Six sign information; it must be derived without
postulating a rate equivalent to the desired conclusion.

### 4G.3 Precisely ONE remaining signed admissibility rule

`VFMidActualPrimeSignedOwnerEscapeRule` is a NEW NAME for
the OLD production signed first-bad requirement, preserving
exactly the six raw-parent sums:

$
\mathrm{FirstBad}_{2}(R+1)\quad\Rightarrow\quad
\underbrace{\mathrm{ActiveGlobalResidualExcess}(R)}_{\text{old anchor/omitted source}}
+
2\underbrace{\mathrm{SixOrientedIncompleteBoundaryMass}(R)}_{\text{old native weighted Gram}}
\le0.
\tag{F8}
$

The original conditional contradiction
`vfMidActualPrimeFirstBadAt_two_succ_false_of_activeSixBoundaryBudget`
then eliminates any first bad at R+1 for R>=8.

**Do not call (F8) independently established.** A new
logical-audit theorem
`vfV2ActualPrime_signedOwnerRule_iff_noFirstBad`
even proves that (F8), with these first-bad quantifiers,
is logically equivalent to NO first bad above the finite base:
the reverse implication is vacuous. A proof must use
actual local owner incidence and the signed Fubini ledger,
not assert (F8) as a generic admissibility axiom.

This **is** the full rule inventory. All independently verified
structural rules are source-identifiable; the only absent
mathematical ingredient remains unconditional actual-arithmetic
proof of (F8). The finite CI of ordinary algebraic rules is
not a certificate of (F8), and no RH conclusion is claimed.



## 4H. Floor-Li fantasy: proved O(1) square-endpoint safety, but not the actual wheel class

The central suggestion is mathematically valid in logical form:

1. Define a class of monotone integer staircases by *independently
   checkable* arithmetic admissibility laws.
2. Prove EVERY member of that class lies within C R log R of the
   deterministic VF_mid square-endpoint series.
3. Show both floor-Li Q and actual prime counting pi satisfy those laws.
4. Apply class containment to pi and the already-compiled von-Koch bridge.

**What is actually established:** Main already proves a *stronger*
deterministic floor-Li reference rate than the basic root bound.
`research/VF_MID_LI_UNIFORM_QUADRATURE.lean` has
`abs_vfMidLiError_sq_le_uniform`, asserting that
`|VF_mid(R^2) - Li_2(R^2)| <= C0` for ALL R>=2 with one
fixed constant C0. `research/LI_FLOOR_PRIME_COUNT_FANTASY.lean`
has `abs_liFloorPrimeCountProxy_sub_li_lt_one`.
Therefore, at EVERY square endpoint,

$
\boxed{|Q(R^2)-VF_{\rm mid}(R^2)|<C_0+1.}
\tag{F9}
$

This is an **unconditional, proved O(1) bound** for the floor-Li
fantasy, hence it cannot have a first bad endpoint for some
sufficiently wide fixed K R log R wall. The coarse theorem by
itself does not certify the special numerical K=2 at the very
smallest roots; sharpen the constant or verify finite base separately
if specifically using K=2. No RH conclusion follows yet.

**Concrete obstruction to claiming the same actual owner class:**
On block R=8 with frozen cutoff A=4, n=65=5*13 satisfies
64<n<81, minFac(n)=5>A and the valid cube-depth hypothesis
`(R+1)^2=81 <= (A+1)^3=125`. The actual physical decoder
(`vfMidOddSignedSeatCharge_eq_affineCenter_add_half_moebius_of_cube`)
uses `mu(65)=+1`, therefore the ACTUAL prime jump at n=65
must be zero, giving charge `w_8`.

But the numerical floor-Li integer potential at this site is

$
Li_2(64)=20.8895045479\ldots,\qquad
Li_2(65)=21.1295054848\ldots,
$

so `Q(65)-Q(64)=1`; its hypothetical prime-seat charge would
be `w_8-1`. These differ by EXACTLY one count. The
transcendental floor comparison is numerical in this audit, NOT
a Lean-certified inequality. An earlier even violation occurs
at n=6, and at R=317 there are 26 even floor-Li jumps and 51
composite floor-Li jumps within its 55 block events.
Thus Q cannot be substituted for the literal `Nat.Prime` site
filter or pointwise restricted Mobius/FTA decoder. Calling
these different values of the *same* owner admissibility law
is invalid, not merely a loss of precision.

**There is a qualitative asymptotic mismatch as well.** The
event gaps of floor(Li_2(n)) are asymptotic to `log n`
(by the mean value theorem applied to Li and the at-most-one
integer rounding at jump sites). Actual consecutive prime
gaps divided by `log p_n` have unbounded limsup
(Westzynthius, strengthened by Ford--Green--Konyagin--Tao
and Maynard; see Annals of Mathematics 183 (2016)).
Consequently any rule requiring every gap to stay between
fixed logarithmic-base multiples is NOT shared by Q and pi.
This does not rule out a suitable WEAKER class with exceptional
gaps: such a class must be proved sufficient on all histories.

**Exact comparison that a shared class MUST control:**
Let `q_n := Q(n)-Q(n-1)`, `p_n := 1_Prime(n)`,
`xi_n := p_n-q_n`. Then

$
\boxed{
\pi(R^2)-VF_{\rm mid}(R^2)
=[Q(R^2)-VF_{\rm mid}(R^2)]
+[\pi(4)-Q(4)]+\sum_{n=5}^{R^2}\xi_n.
}
\tag{F10}
$

The fantasy bracket in (F10) has proved O(1) size.
The actual cumulative signed primitive relocation
`sum xi_n` does NOT. This is precisely the arithmetic
content of the first-bad signed payment.

A possible non-circular class property, *not yet proved for pi*,
would bound ranked event relocations `|p_j-q_j|` by
`O(sqrt(q_j) log(q_j)^2)`. By monotonicity and the
known Li floor increment bound, only events in a window
of that width could be unmatched at a given x, so

$
|\pi(x)-Q(x)|=O\bigl((\sqrt{x}\log^2 x)/\log x\bigr)
=O(\sqrt{x}\log x).
$

This is a logically sufficient deterministic **event-transport
certificate**, not independent evidence that actual primes satisfy it.
The previously recorded floor-Li transport miner found short
FIFO lifetimes empirically through 1e8 but did not prove any
uniform asymptotic matching. Its owner-realization/payment is
the actual unresolved theorem; the reference's O(1) property
cannot substitute for it.

**Research policy:** Preserve the proved fantasy cancellation
and native Sector Six mechanics. Do not claim floor-Li belongs
to the actual wheel/FTA owner class, do not assume pointwise
even/odd parity alignment, and do not replace the remaining
actual signed transport or six-sector inequality by the
fact that the reference itself is well-behaved.


## 4I. Joint historical wall occupancy / genuine parent age: exact Lean scope and finite results (Oct 9)

The **production target is UNCHANGED**: under an ACTUAL prime first bad at
R+1, prove the original weighted occurrence-preserving six-sector signed return

\[
\boxed{
\mathrm{ActiveGlobalResidualExcess}(R)
+2\,\mathrm{SixOrientedIncompleteBoundaryMass}(R)\le 0.
}
\]

Use the original odd-seat carrier, historical anchor D_R charged ONCE, full
diagonal, mature/sparse/smooth terms, the cross-owner Gram and all incomplete
first/next/returned left/right fibers.  Do **NOT** substitute an estimated
conditional expectation or add a wall-near stochastic assumption.

### Exact physical age classification and what it does NOT pay

For each original odd composite n=cq in R^2<n<(R+1)^2 with genuine prime
factor q>R (and odd c>=3), put b=floor(sqrt(q)) and age=(R-b)/R.
Genuine high-q prime factors already existed below R^2.  Cohorts are:

- bucket 0: age < 0.55;
- bucket 1: age 0.55..0.70;
- bucket 2: age 0.70..0.85;
- bucket 3: age >= 0.85.

All comparisons in Lean use integer inequalities on 20*b, 10*b and R.
Age cohorts partition CURRENT physical composite sites: their total native
weight equals the original high-q composite mass.  Each site is included
only ONCE and a prior negative prime q is NOT credited once per later child.
The complete squared source includes all SIX cross-age terms.  The
four-cohort prime/high-q/smooth conservation identity still totals
-P_R+F_R: it is **a census identity**, NOT independent restoring capacity.

The Mathlib-only existing kernel file
`research/VF_MID_FIRST_BAD_PAYMENT_V2_KERNEL.lean` now includes:

- `vfV2HighPrimeParentPrecedesCurrentSquare`;
- `vfV2AgeCohortNativeMass_sum`, `..._disjoint`;
- `vfV2AgeFourCohortFullGram` and
  `vfV2FourAgeCohorts_do_not_create_restoringMass`;
- `vfV2StrictPastRoots_lt_current`, past-only score ranking;
- `vfV2BlockFlux_telescope`,
  `vfV2DelayedFlux_eq_futureBlockSum`,
  `vfV2CurrentPlusDelayedFlux`,
  `vfV2DelayedMovingWallClearance`;
- `vfV2JointDelayedFluxCell_sum`, a finite full nine-cell
  reassembly into the SAME actual signed flux;
- `vfV2NoUniversalDelayedInwardFlux`, an explicit counterexample to
  claiming an unconditional future inward drift for generic sequences.

The existing actual-prime certificate now specializes the Mathlib kernel to
the literal `Nat.Prime` physical parent filter, actual floor-Li backlog,
strictly future block corrections, and the native VF radial wall.  The
terminal consumer **requires the SAME original signed Sector Six inequality**
as before.  New actual-prime bridge declarations are subject to slow native
import-closure CI; their existence as source is not a claim of compilation.

### Finite joint conditioning: observations, not universal laws

Independent actual-prime census through roots R=8..31621 (31,614 blocks).
Prospective panel R=1000..31493 uses trailing 1,000 roots only to define
low/mid/high occupancy quantiles and Li-calibrated q-parent age exposure
tertiles.  The *strictly delayed* response excludes block R:

\[
J^{\rm delayed}_{16}(R)
=\mathrm{sgn}(D_R)\,[E_{R+17}-E_{R+1}],\quad
E_R=\pi(R^2)-Q(R^2).
\]

Negative J means inward motion, not guaranteed defect sign reversal.
Measured means, age exposure columns younger/middle/older:

| Past-only relative wall occupancy | Younger | Middle | Older | All |
|---|---:|---:|---:|---:|
| Low | +22.07 | +19.81 | +18.06 | +19.98 |
| Middle | +0.88 | -1.19 | -3.32 | -1.23 |
| High | -18.02 | -14.00 | -20.09 | -17.31 |

The high-low mean is -37.29; contiguous 250-root block bootstrap
sensitivity interval approximately [-45.7,-29.3].  Oldest-youngest
*within high* is only -2.07, bootstrap interval [-6.4,+2.0]
(includes zero).  Mature least-prime owner p provides a NEGATIVE
CONTROL: in high occupancy the apparent next-16 mean INCLUDING the
current block is -33.21 (high maturity) vs -1.71 (low maturity),
but EXCLUDING current it becomes -13.59 vs -20.75.  Therefore mature
owners CANNOT be treated as newly spendable negative energy.

**Severe extrapolation limitation:** historical "high occupancy" here
averages only ~0.392% of the K=2 wall.  No near-wall first-bad case or
positive-wall history was observed.  Finite conditional means do NOT
establish a pointwise all-R signed return or a Markov contraction.

The only permitted mathematical next step is to prove the existing original
Sector Six signed source-to-boundary inequality directly from real
owner incidences and once-charged history.  Do not create a new PR, rename
the RH-strength gate, or replace its physical denominator by a cohort
normalization.

Full finite research archive and notes were generated in the associated
ChatGPT analysis workspace; the true prime audit remains the only arithmetic
input, not a Lean hypothesis.

---

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
splits these lanes and cancels stale PR runs. The standard PR smoke path
requires only stdlib Python plus the tiny cached Lean kernel. Manual
`workflow_dispatch` inputs `deep_native` and `crossblock_moments`
are independent and BOTH default to false. The latter installs its own
NumPy/SciPy/mpmath dependencies, runs the entire 5,993-block cohort
NNS/Pearson/Schur study (~4.4s CPU after setup), runs the selected
true owner-matched q->c*q probe, and uploads CSV/JSON results as
the `vf918-crossblock-actual-primes` GitHub Action artifact.

Reproduce this optional research analysis locally:

```sh
python3 -m pip install numpy scipy mpmath
python3 scripts/vf_mid_918_crossblock_moments.py \
  --max-root 6000 --outdir vf918_crossblock
python3 scripts/vf_mid_918_owner_matched_probe.py
```

Neither research script imports or changes production Lean,
nor is its finite numerical output used as a proof hypothesis.

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
This workstream has **exactly seven narrowly scoped files**:

1. This canonical proof contract (one `.md`);
2. One small Mathlib-only algebraic kernel file;
3. One native conditional consumer importing existing main;
4. One stdlib actual-prime regression and full physical-seat matrix script;
5. One isolated fast workflow with opt-in native AND empirical cohort lanes;
6. One opt-in fast NumPy/SciPy entire actual-prime/Co-Div experiment;
7. One opt-in genuine prime-owner-to-odd-composite probe.

Do not transplant #915's 36-file exploratory diff, commit history,
experimental Li/floor-Li scripts, or failing terminal file.
Historical exploratory work remains available at
[PR #915](https://github.com/OVVO-Financial/RH_Lean/pull/915);
that history is a reference, **not a dependency**.

**Plain outcome criterion:** (11) must become a genuinely proved
actual-prime signed inequality, compiled in Lean with no added
arithmetical hypothesis. Until then this PR is a clean, green *proof
infrastructure* PR, not an RH proof.

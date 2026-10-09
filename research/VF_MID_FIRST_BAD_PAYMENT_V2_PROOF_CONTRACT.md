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

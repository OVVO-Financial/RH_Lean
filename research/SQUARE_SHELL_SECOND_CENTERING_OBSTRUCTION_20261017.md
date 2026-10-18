# Square-shell second centering: exact no-go and signed-moment obligations

**Date:** 2026-10-17. **Follow-up:** merged #972; new draft #973. **Status:** mathematical identities are paper proofs; Lean verification in progress, census integer-exact. NO independent 7/8 exponent or RH proof.

## 1. Actual prime-owner decomposition, retaining every physical atom

For I_r={r²+1,...,r²+2r} and 1<=d<=r let
\[
F_r(d)=\sum_{n\in I_r,\ d\mid n}\mu(n),\quad
B_r(d)=\sum_{n\in I_r,\ P^+(n)\le r,\ d\mid n}\mu(n),\quad
T_r(d)=\sum_{c\le r,\ d\mid c}\mu(c)P_r(c).
\]
Because every high-prime owner q>r is unique and mu(qc)=-mu(c),
\[
\boxed{F_r(d)=B_r(d)-T_r(d).}\tag{1}
\]
The first cofactor compensator \(a_r(c)=\sum_{k\le r/c}\mu(k)B_r(kc)\) matches these divisibility profiles; its centered row satisfies \(F_r(d)=-\sum_{c\le r,d\mid c}e_r(c)\).

## 2. Obstruction to second inversion from higher divisors

The actual high-prime cofactor c=1 has a nonzero transport population
\[
Q_r=P_r(1)=\#\{q\text{ prime}:r^2<q<(r+1)^2\},
\]
but is *invisible to every profile with d>1*. Indeed, \(d\nmid 1\) for d>=2. Thus the restricted incidence matrix indexed only by d>=2 has the nonzero unit-coordinate kernel vector. **No linear/inversion operator using only the higher divisor channels can reconstruct the full d=1 mass for arbitrary cofactor profiles.**

A second operator must explicitly keep Q_r or other new nonlocal physical data. Let \(V_r=F_r(1)+Q_r\) (genuine nonprime mass). Then
\[
\boxed{\Delta_r^2=(V_r-Q_r)^2=V_r^2-2V_rQ_r+Q_r^2.}\tag{2}
\]
The prime-only square is supertarget: PNT gives
\[
\sum_{H\le r<2H}Q_r=\pi(4H^2)-\pi(H^2)
\sim\frac{3H^2}{2\log H}.
\]
Cauchy-Schwarz yields
\[
\boxed{\sum_{H\le r<2H}Q_r^2\gg H^3/(\log H)^2,}
\]
which dominates \(H^{5/2+\eta}\) for fixed eta<1/2. **Deleting or subtracting prime-only coherence without paying its signed mixed composite counterterm does not advance the proof.** This uses the classical PNT, not any external OAI seven-eighths theorem.

## 3. Exact dyadic band collapse: a second tautology trap

For dyadic D=1,2,4,... with D<=r set
\(f_D(k)=1_{\{D\le k<2D\}}\) and
\(\beta_D(d)=\sum_{k\mid d}\mu(d/k)f_D(k)\).
These dyadic ranges partition every positive k<=r. Therefore
\[
\boxed{\sum_D\beta_D(d)=\sum_{k\mid d}\mu(d/k)=1_{\{d=1\}}.}\tag{3}
\]
Write \(L_r(D)=\sum_{d<\sqrt r}\beta_D(d)F_r(d)^2\) and
\(U_r(D)=\sum_{\sqrt r\le d\le r}\beta_D(d)F_r(d)^2\). For r>=3:
\[
\boxed{\sum_D L_r(D)=\Delta_r^2,\qquad\sum_D U_r(D)=0.}\tag{4}
\]
In particular for D=1, \(\beta_1(d)=\mu(d)\), so
\[
L_r(1)=\underbrace{F_r(1)^2}_{\Delta_r^2}+
\sum_{2\le d<\sqrt r}\mu(d)F_r(d)^2,\qquad
\sum_{D\ge2}L_r(D)=-
\sum_{2\le d<\sqrt r}\mu(d)F_r(d)^2.\tag{5}
\]
The cancellation between bands is exact, but reassembling them simply returns shell energy. Hence **the proposed second centering obtained by rearranging the same \(\beta_D\) is circular** unless a new independent signed bound is supplied. A one-shell bound \(L_r(D)\ll_\eta r^{3/2+\eta}\) remains a possible *new theorem*; it is NOT a consequence of inversion or band recombination.

## 4. Exact machine census

The new scripts/square_shell_second_centering_census.cpp uses a genuine linear Möbius sieve and independently counts F_r(d), smooth B_r(d), signed high-prime T_r(d), all \(\beta_D(d)\), and all shell/low-band energies. Compile with g++ -O3 -std=c++17 -Wall -Wextra -Werror, then run with argument 4096. It checks **each coefficient** of (3), every shell of (1), squareful zero channels, and the zero-mode identity (4) at every 3<=r<=4096, for every dyadic gcd band. This is exact finite evidence, not uniform extrapolation.

The separate Python SS/ST/TT direct physical-pair certificate now checks EVERY admissible gcd band of every shell 3<=r<=80, plus the prior r=137 and r=317 stress cases: **1,568 distinct windows**.

| r | prime-only Q_r | delta_r | delta_r² | L_r(1) | sum_(D>=2) L_r(D) |
|---:|---:|---:|---:|---:|---:|
| 14 | 4 | 9 | 81 | 56 | +25 |
| 31 | 10 | -8 | 64 | 50 | +14 |
| 137 | 22 | 44 | 1,936 | 1,255 | +681 |
| 317 | 54 | 11 | 121 | 59 | +62 |
| 1,000 | 152 | 22 | 484 | -1,541 | +2,025 |
| 2,000 | 267 | 3 | 9 | -2,155 | +2,164 |
| 3,000 | 340 | 39 | 1,521 | -2,145 | +3,666 |
| 4,096 | 491 | 118 | 13,924 | 1,082 | +12,842 |

Full dyadic sums from every shell in each band (not curve fitting):

| H | energy/H^(5/2) | sum L_r(1)/H^(5/2) | sum_(D>=2) L_r(D)/H^(5/2) |
|---:|---:|---:|---:|
| 256 | 0.10511 | 0.00536 | 0.09975 |
| 512 | 0.08209 | 0.00912 | 0.07297 |
| 1024 | 0.05136 | 0.00096 | 0.05040 |
| 2048 | 0.03888 | 0.00209 | 0.03680 |

These ratios do not establish a uniform all-H estimate.

## 5. Seven-role research routing, preserving once-daily budget

- **Owner:** retain the greatest-prime labels and exact prime-only c=1 square and mixed term inside every proposed second operator; preserve original masked #915 / root-wall distinctions.
- **Finite Wheel:** formalize the coefficient-level dyadic collapse (3), strict shell wall, owner collision and all valid gcd bands; seek an additive difference kernel with new genuine signed phase rather than a repartitioned inversion.
- **Analytic:** attack \(-2Q_rV_r\) as a genuine signed prime/composite bilinear quantity, or design an admissible nonlocal signed divisor-phase moment whose estimate is independently easier than (SB-7/8). Do not import external OAI 7/8 or misapply the 19/35 all-interval result to square-root shells.
- **Census:** reproduce the exact all-shell C++ audit, separate composite-prime and unshared-prime signs, and predeclare held-out shells >4096.
- **Referee:** reject any theorem hiding \(\Delta_r^2\) in a residual, or subtracting \(Q_r^2\) without an equally real signed bill. Check dyadic summability, exponent loss and pointwise-vs-averaged quantifiers.
- **Lean:** kernel-check finite Mobius profile matching, completed square, explicit d=1 nullspace and, if possible, coefficient-level dyadic partition delta. Keep hypotheses visible and audit #print axioms.
- **Coordinator:** select one genuinely new phase-bearing analytic difference plus an adversarial falsifier for next authorized once-daily pass; do NOT increase schedules, change agent configurations or auto-merge.

## 6. Verdict against user's stop conditions

The first compensator and high-divisor/boundary/owner payments remain valid paper reductions and finite certificates. **Second centering solely by restricted Möbius inversion fails (lost c=1 channel). Second centering solely across complete dyadic gcd bands fails (exact return to \(\Delta_r^2\)). A prime-only coherent subtraction has an unconditional \(H^3/\log^2H\) positive square to compensate.**

The unresolved task is an independently proved sign-preserving prime/composite or unshared-prime bilinear moment, with enough true cancellation to save the missing \(H^{1/2}\). The proposed target is still OPEN; the current deliverables are structural certification, a falsifiable stop test, and new exact census.

# VF_mid, actual prime owners, PNT, and the first-bad signed payment

> **Comprehensive proof-mechanism audit — 2026-10-08**
>
> **Status:** A proposed RH proof mechanism, **not a completed proof of the Riemann Hypothesis**. The deterministic VF midpoint/Li transfers, square-wheel and least-owner reconstruction, normalized NNS identities, first-bad implication, weighted first-owner Fubini, formal owner-reversal heat, and eventual PNT reciprocal-star nonexpansion have proved Lean components. The decisive first-bad-specific **signed aggregate payment** remains unproved.
>
> **Production snapshot:** [PR #915](https://github.com/OVVO-Financial/RH_Lean/pull/915), head [48305e6](https://github.com/OVVO-Financial/RH_Lean/commit/48305e606fe1d4b6a631b6fad7ad190dad94a8ae), **draft, unmerged** as of this audit. This note is a **standalone documentation change against main**; source links below deliberately pin to the #915 head where some named declarations exist only on its unmerged branch.
>
> **CI snapshot:** [#915 fast workflow](https://github.com/OVVO-Financial/RH_Lean/actions/runs/37812961563): all numerical regressions passed, including every integer square-root index \(8\le R\le6000\); warning-fatal production Lean compilation failed at the **existing unproved hbalance goal**, line 1354 of the pinned file. Lean source audits, documentation, and public-export checks passed. The terminal theorem and its consumers are **not compiled** through that failing proof.

## Contents

1. [Dependency chain and epistemic status](#1-dependency-chain-and-epistemic-status)
2. [The VF midpoint reference and von Koch/RH transfer](#2-the-vf-midpoint-reference-and-von-kochrh-transfer)
3. [The original exact sieve identity \(S=A-T\)](#3-the-original-exact-sieve-identity-sa-t)
4. [Reconstruction in signed VF-error coordinates](#4-reconstruction-in-signed-vf-error-coordinates)
5. [First badness, radial budget, and NNS partial moments](#5-first-badness-radial-budget-and-nns-partial-moments)
6. [Ascending the actual owners from prime 2](#6-ascending-the-actual-owners-from-prime-2)
7. [Physical quadratic Fubini, residual, and owner sectors](#7-physical-quadratic-fubini-residual-and-owner-sectors)
8. [Greatest-owner sign reversal and the remaining sharp transport](#8-greatest-owner-sign-reversal-and-the-remaining-sharp-transport)
9. [What proved PNT and the protected Euler star do—and do not—supply](#9-what-proved-pnt-and-the-protected-euler-star-doand-do-notsupply)
10. [Numerical reproducibility and saturation diagnostics](#10-numerical-reproducibility-and-saturation-diagnostics)
11. [Why an unconditional anchored cone induction is invalid](#11-why-an-unconditional-anchored-cone-induction-is-invalid)
12. [The single open production inequality, precisely](#12-the-single-open-production-inequality-precisely)
13. [Terminal implication and additional formal closeout work](#13-terminal-implication-and-additional-formal-closeout-work)
14. [Lean theorem/dependency index and work restrictions](#14-lean-theoremdependency-index-and-work-restrictions)

---

## 1. Dependency chain and epistemic status

The intended mathematical implication is

$$
\boxed{
\begin{array}{c}
\text{Exact integer sieve and signed owner reconstruction}\\
+\ \text{PNT-controlled actual-prime reciprocal Euler stars}\\
+\ \color{red}{\text{UNPROVED occurrence-matched signed first-bad payment}}\\
\Downarrow\\
\text{No }K=2\text{ first bad square endpoint}\\
\Downarrow\\
|\pi(R^2)-VF_{\rm mid}(R^2)|\le 2R\log R\\
\Downarrow\\
\pi(x)-Li(x)=O(\sqrt{x}\log x)\\
\Downarrow\ (\text{classical von Koch criterion})\\
\text{RH}.
\end{array}}
$$

Some parts are equivalences or *conditional consumer* theorems, not new distributional estimates. Specifically:

- The deterministic reference curves are known to approximate Li. **This does not assert actual \(\pi(x)\) is a deterministic fantasy curve.**
- The complete square wheel reconstructs the actual prime *set* by exact divisibility; its exactness alone says nothing sufficiently sharp about the *number* of surviving primes in long runs.
- PNT is a proved theorem in this repository. A PNT-based bound on a sum of actual reciprocal prime owners is valid, but **PNT does not supply RH-precision errors in each short square block**.
- The completed owner-star has a proved **nonexpansion** inequality on a separate protected correlation carrier; it is **not already an inequality on the #915 first-bad anchored source**.
- An identity expressing the target payment in new NNS or sector coordinates is **not a proof that the payment is nonnegative**.
- The hypothetical first-bad assumption itself forces the *opposite* sign of the desired payment. The objective is a genuine contradiction from an additional arithmetic restriction on actual physical owner interactions.

This document distinguishes (i) proved formal facts, (ii) separate external classical facts, (iii) numerical observations, and (iv) the unproved RH-strength step.

## 2. The VF midpoint reference and von Koch/RH transfer

### 2.1 Definition on square tiles

For \(r\ge2\), define the tile midpoint and expected mass

$$
m_r=r^2+r+\tfrac12,
\qquad
V_r=\frac{2r+1}{\log m_r}.
$$

For \(x\ge4\) let \(R=\lfloor\sqrt{x}\rfloor\). The chosen continuous approximation is

$$
\boxed{
VF_{\rm mid}(x)
=
\sum_{r=2}^{R-1}V_r+
\frac{x-R^2}{\log((R^2+x)/2)}.
}
\tag{2.1}
$$

At an exact square endpoint, the live term vanishes:

$$
\boxed{VF_{\rm mid}(R^2)=\sum_{r=2}^{R-1}V_r.}
\tag{2.2}
$$

**Lean:** [vfMidBandMidpoint; vfMidBandMass; vfMidFinishedMass; vfMidLiveMass; vfMid; vfMid_sq](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_VON_KOCH_BRIDGE.lean#L63-L118).

### 2.2 Deterministic midpoint error against Li

Let the normalized logarithmic integral be

$$
Li(x)=\int_2^x\frac{dt}{\log t},
\qquad
Q(x)=VF_{\rm mid}(x)-Li(x).
$$

The repository proves

$$
\boxed{|Q(x)|\le B\sqrt{x}\quad(x\ge4)}
\tag{2.3}
$$

for some fixed \(B\). It also proves the stronger *square-endpoint* statement

$$
\boxed{|Q(R^2)|\le B_0}
\tag{2.4}
$$

for some \(B_0\) independent of \(R\).

These require no prime-distribution hypothesis. They are deterministic quadrature estimates.

**Lean:** [vfMidLiRootBounded](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_VON_KOCH_BRIDGE.lean#L534-L572); [abs_vfMidLiError_sq_le_uniform; vfMidLiSquareEndpointUniformBounded](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_LI_UNIFORM_QUADRATURE.lean#L688-L742).

### 2.3 The four fantasy proxies: what is proved

The repository considers continuous Li, the exact fractional VF-mid cluster at square endpoints, the VF midpoint-to-midpoint linear interpolant, and discrete floor-Li. They have proved deterministic Li-approximation bounds. It also proves conditional proxy-to-RH reductions:

$$
\left.
\begin{array}{r}
|F(x)-Li(x)|=O(\sqrt{x})\\
|\pi(x)-F(x)|=O(\sqrt{x}\log x)
\end{array}
\right\}
\Longrightarrow
|\pi(x)-Li(x)|=O(\sqrt{x}\log x).
\tag{2.5}
$$

For example, the hypothetical equality \(\pi(x)=Li(x)\) trivially makes the von Koch error zero, but the *equality is explicitly an assumption*, not an established fact about primes. Likewise, identifying actual primes with the fractional VF cluster is a counterfactual identification used to check the deterministic geometry.

**Lean:** [FOUR_FANTASY_PROXY_RH_CLOSURES.lean](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/FOUR_FANTASY_PROXY_RH_CLOSURES.lean); [VF_MID_SOLVED_FANTASY_CONE.lean](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_SOLVED_FANTASY_CONE.lean#L34-L285).

The solved fantasy-cone theorem proves the *region is von Koch-safe*; its consumer still takes the explicit assumption

$$
\operatorname{ActualPrimeContainedInSolvedFantasyConeStatement}.
$$

This actual-containment assertion is not proved by solving the deterministic cones.

### 2.4 Square endpoints suffice

Define

$$
D_R=\pi(R^2)-VF_{\rm mid}(R^2).
$$

The repository proves the *conditional implication*

$$
\left[\exists C\ \forall R\ge2,\quad |D_R|\le CR\log R\right]
\Rightarrow
|\pi(x)-VF_{\rm mid}(x)|=O(\sqrt{x}\log x).
\tag{2.6}
$$

The transfer uses finite integer-count control on the unfinished square interval; it does not demand an RH-scale estimate in every separate block. Then (2.3) transfers VF to Li, and the classical von Koch theorem equates this prime–Li discrepancy bound with RH.

**Lean:** [vfMidVonKochBounded_of_squareEndpoint; vfMidSquareEndpointVonKochBounded_iff](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_VON_KOCH_BRIDGE.lean#L685-L744); [vfMidVonKochBounded_iff_primeLiVonKochBounded; riemannHypothesis_of_vfMidSquareEndpoint](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_VON_KOCH_BRIDGE.lean#L867-L909).

**Formal interface caution:** The terminal theorem currently accepts an argument of type **ClassicalVonKochRHCriterion**. That structure packages the known classical criterion but is not constructed by this module. A fully standalone kernel proof must discharge/import that premise.

## 3. The original exact sieve identity \(S=A-T\)

### 3.1 Exactly \(R\) odd candidate seats

Consider the open square block

$$
I_R=\{n\in\mathbb N:R^2<n<(R+1)^2\}.
$$

There are \(2R\) interior integer sites. Exactly \(R\) remain after the parity wheel (owner \(2\)). Every prime in this interval is odd for \(R\ge2\), and every composite \(n\in I_R\) has a prime factor at most \(R\): otherwise its two smallest factors are both at least \(R+1\), giving \(n\ge(R+1)^2\), impossible.

Consequently,

$$
\boxed{
n\in I_R\text{ is prime}
\iff
n\text{ survives every prime owner }p\le R.
}
\tag{3.1}
$$

The direct band \((R^2,(R+1)^2]\) has the same prime population because the additional upper square is composite.

**Lean:** [vfMidSquareWheelSites_card; vfMidSquareBand_commonWheelSurvivor_iff_prime; vfMidSquareWheelSurvivors_eq_primes](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_SQUARE_WHEEL_BACKLOG.lean#L51-L165); [vfMidOddCandidateSeats_card](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_ODD_FRACTIONAL_CLUSTER.lean#L37-L68).

### 3.2 Exactly one least-prime owner per removed composite

For odd prime \(p\le R\), define

$$
c_{p,R}
=
\#\left\{
n\in I_R:
n\text{ composite},\quad \operatorname{minFac}(n)=p
\right\}.
$$

The fibres for distinct \(p\) are disjoint. Write

$$
C_R=\sum_{\substack{3\le p\le R\\p\text{ prime}}}c_{p,R}
$$

for the total composite removals on the parity carrier, and

$$
P_R=\pi((R+1)^2)-\pi(R^2)
$$

for the actual prime population. Since the parity carrier has exactly \(R\) elements,

$$
\boxed{
\underbrace{P_R}_{S}
=
\underbrace{R}_{A}
-
\underbrace{\sum_{3\le p\le R}c_{p,R}}_{T}
=R-C_R.
}
\tag{3.2}
$$

This is the original **\(S=A-T\)** sieve identity. Here \(A=R\) is the **candidate population**, not the count of primes \(\le\sqrt{x}\). The small primes are sieve *owners*. The sieve count \(T=C_R\) satisfies \(0\le T\le A\).

**Lean:** [vfMidOddActualComposite_card_add_primeSupply; vfMidOddCompositeTrackingDefect_eq_ownerCensus_sub_reference](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_ODD_FRACTIONAL_CLUSTER.lean#L87-L217).

### 3.3 Upper supply bounds already proved

For a prefix \(s\le R\), define

$$
Q_s=\prod_{p\le s}p,\qquad
U_R(s)=\varphi(Q_s)
\left(\left\lfloor\frac{2R}{Q_s}\right\rfloor+1\right).
$$

The proven wheel bounds state

$$
\boxed{
P_R\le
|\operatorname{PrefixSurvivors}(s,R)|
\le U_R(s).
}
\tag{3.3}
$$

Hence

$$
\boxed{C_R\ge R-U_R(s).}
\tag{3.4}
$$

The finite wheel therefore gives a rigorous *minimum removal* population / *maximum surviving prime* population. **It does not automatically provide a comparably sharp minimum actual prime supply in each block**, especially not over arbitrarily many consecutive blocks at the von Koch scale.

**Lean:** [vfMidIntegerBlockPrimeSupply_le_prefixWheelCard; vfMidIntegerBlockPrimeSupply_le_every_prefixWheelEnvelope](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_SQUARE_WHEEL_BACKLOG.lean#L338-L424).

## 4. Reconstruction in signed VF-error coordinates

### 4.1 Exact square-endpoint recurrence

Since

$$
VF_{\rm mid}((R+1)^2)=VF_{\rm mid}(R^2)+V_R
$$

and the actual prime-count increment is \(P_R\),

$$
\boxed{D_{R+1}=D_R+P_R-V_R.}
\tag{4.1}
$$

Substitute \(P_R=R-C_R\):

$$
\boxed{
D_{R+1}=D_R-\underbrace{[C_R-(R-V_R)]}_{F_R}.
}
\tag{4.2}
$$

Thus

$$
F_R=C_R-(R-V_R)=V_R-P_R
$$

is **actual composite removals minus the deterministic VF-implied composite-removal mass**. This use of \(T\) differs from the raw sieve-count \(T=C_R\): \(F_R\) is signed and can exceed, equal, or fall below any historical anchor.

**Lean:** [vfMidSquareEndpointError_succ](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_SQUARE_BAND_COMPOSITE_BRIDGE.lean); [vfMidOddCompositeTrackingDefect_eq_neg_bandError](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_ODD_FRACTIONAL_CLUSTER.lean#L114-L140).

### 4.2 Aggregate history, not isolated block estimates

For \(a<B\), telescope:

$$
\boxed{
D_B=D_a-\sum_{r=a}^{B-1}\big[C_r-(r-V_r)\big].
}
\tag{4.3}
$$

The statement \(D_B=A-T\) now means

$$
A=D_a,\qquad T=\sum_{r=a}^{B-1}(V_r-P_r),
$$

and \(A\) is a **signed earlier VF tracking error**, not the population of small primes.

For #915 choose

$$
a=\left\lfloor\frac R2\right\rfloor+1,\qquad B=R+1.
$$

Then \(B\le2a\), so the frozen-wheel subdoubling decomposition applies. The historical run and current block have an **exact** physical charge

$$
F_{a,R+1}
=
\operatorname{FrozenAffineRunPhysicalCharge}(a,R)
+
\operatorname{FrozenAffineBlockPhysicalCharge}(a,R),
$$

and

$$
\boxed{D_{R+1}=D_a-F_{a,R+1}.}
\tag{4.4}
$$

All processed owners and remaining survivors occur in the exact source; the earlier anchor is not discarded.

**Lean:** [vfMidDyadicVFTrackingDefect_eq_neg_primeError_increment](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_DYADIC_OWNER_EXACT.lean); [vfMidOddRunSeatMass_eq_frozenSurvivor_add_processedOwnerCharge](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_AFFINE_OWNER_SPLICE.lean#L284-L324); [vfMidActualPrimeEndpointDefect_succ_eq_decompressedHistoricalSource](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_SOURCE_TO_SECTOR_SIX_INLET.lean#L37-L73); [vfMidHalfScaleRunPlusBlock_eq_trackingDefect](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean#L1057-L1090).

## 5. First badness, radial budget, and NNS partial moments

### 5.1 A hypothetical first bad endpoint

Write \(\rho_R=R\log R\). The production route proposes the **fixed \(K=2\) wall**

$$
|D_R|\le2\rho_R.
$$

Assume that \(R+1\) is a first bad scale:

$$
\boxed{|D_{R+1}|>2\rho_{R+1},\qquad
|D_s|\le2\rho_s\quad(2\le s\le R).}
\tag{5.1}
$$

This implies in particular \(|D_R|\le2\rho_R\) and \(|D_a|\le2\rho_a\).

**Lean:** [VFMidSyntheticRadialScale; VFMidSyntheticBadAt](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_ADVERSARIAL_PROOF_FUZZER.lean#L48-L222); [VFMidActualPrimeFirstBadAt; vfMidActualPrimeFirstBadAt_prior_inside](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_ACTUAL_PRIME_FIRST_BAD_MOBIUS_TRIGGER.lean#L35-L53).

### 5.2 The exact energy increment

Let \(e_R=P_R-V_R\). Then

$$
D_{R+1}=D_R+e_R,
$$

and the welded quadratic identity is

$$
\boxed{
D_{R+1}^2-D_R^2=2D_Re_R+e_R^2.
}
\tag{5.2}
$$

The cross term \(2D_Re_R\) is historical/current interaction, so a bound on \(e_R^2\) alone cannot close the energy budget. All owner/Fubini work must retain the cross term rather than reclassify it as available independent capacity.

**Lean:** [vfMidSquareEndpointAccumulationCorrelation](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_UNIFORMITY_BIAS_CORRELATION.lean); [VF_MID_GLOBAL_FIRST_BAD_RADIAL_BUDGET.lean](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_GLOBAL_FIRST_BAD_RADIAL_BUDGET.lean).

### 5.3 The original one-block physical charge field

There are exactly \(R\) parity-surviving seats. Put

$$
w_R=\frac{V_R}{R},\qquad
z_R(n)=w_R-\mathbf 1_{\mathbb P}(n)
$$

for such a physical seat \(n\). For \(R\ge3\), \(0<w_R<1\); thus

$$
z_R(n)=
\begin{cases}
w_R-1<0,&n\text{ prime},\\
w_R>0,&n\text{ composite}.
\end{cases}
$$

Include a single historical signed anchor \(z_0=-D_R\). On the occurrence-preserving anchored population, define its zero-target UPM and LPM masses \(U_R,L_R\). They are

$$
\boxed{U_R=(-D_R)_++w_R(R-P_R),}
\tag{5.3}
$$

$$
\boxed{L_R=(D_R)_++(1-w_R)P_R.}
\tag{5.4}
$$

The resulting identities are

$$
\boxed{U_R-L_R=-D_{R+1}}
\tag{5.5}
$$

and

$$
\boxed{
M_R:=U_R+L_R
=
|D_R|+\sum_{n\in\operatorname{OddSeats}(R)}|z_R(n)|
=
|D_R|+w_R(R-P_R)+(1-w_R)P_R.
}
\tag{5.6}
$$

No norm inequality has been taken in (5.3)–(5.6). **\(M_R^2\) is the ORIGINAL anchored NNS denominator.** Replacing it with an enlarged absolute history changes the theorem.

**Lean:** [vfMidOddSignedSeatCharge](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_SIGNED_SEAT_CHARGE.lean); [vfMidFirstBadAnchoredUpperPartialMass; vfMidFirstBadAnchoredLowerPartialMass](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean#L660-L673); [vfMidFirstBadAnchoredUpper_sub_lower_eq_signedSource](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean#L681-L720); [vfMidFirstBadAnchoredUpper_add_lower_eq_absMass](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean#L721-L764).

### 5.4 NNS Co/Div and the half-covariance gate

For positive/negative masses \(U,L\), the anchored zero-target pair masses simplify to

$$
\mathrm{Co}=U^2+L^2,\quad
\mathrm{Div}=2UL.
$$

Hence

$$
\mathrm{Co}+\mathrm{Div}=M_R^2,\qquad
\mathrm{Co}-\mathrm{Div}=(U_R-L_R)^2=D_{R+1}^2.
$$

For \(M_R>0\), the normalized covariance is

$$
\boxed{
N_R=
\frac{\mathrm{Co}-\mathrm{Div}}{\mathrm{Co}+\mathrm{Div}}
=
\frac{D_{R+1}^2}{M_R^2}.
}
\tag{5.7}
$$

The desired half-gate \(N_R\le\tfrac12\) is

$$
2D_{R+1}^2\le M_R^2
$$

or equivalently

$$
\boxed{\mathcal B_R=M_R^2-2D_{R+1}^2=6U_RL_R-U_R^2-L_R^2\ge0.}
\tag{5.8}
$$

The associated Co/Div *excess* is

$$
\mathcal E_R=\mathrm{Co}-3\mathrm{Div}
=2D_{R+1}^2-M_R^2=-\mathcal B_R.
\tag{5.9}
$$

**Lean:** [vfMidAnchoredZeroTargetTotalMass_eq_absSum_sq; vfMidFirstBadNNSNormalizedCovariance](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_NORMALIZED_PARTIAL_MOMENT.lean#L162-L245); [vfMidUpperLowerBalanceSlack; vfMidUpperLowerBalanceSlack_nonneg_iff_sourceMass; vfMidFirstBadAnchoredBalanceSlack_eq_neg_coDivExcess](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean#L839-L895).

### 5.5 First badness already forces the opposite inequality

Under (5.1), every current physical charge has \(|z_R(n)|\le1\). Consequently

$$
M_R\le |D_R|+R\le2\rho_R+R.
$$

The proved radial estimate gives, for \(R\ge8\),

$$
\frac12(2\rho_R+R)^2\le (2\rho_{R+1})^2.
$$

Therefore,

$$
\frac12M_R^2\le(2\rho_{R+1})^2<D_{R+1}^2.
$$

So a first-bad successor forces

$$
\boxed{N_R>\tfrac12,\quad\mathcal B_R<0,\quad\mathcal E_R>0.}
\tag{5.10}
$$

**This direction is already proved.** The entire remaining arithmetic program tries to force \(\mathcal B_R\ge0\) under the *same* first-bad hypothesis, contradicting (5.10).

**Lean:** [vfMidActualPrimeFirstBadAt_two_succ_half_totalMass_le_radial](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_NORMALIZED_PARTIAL_MOMENT.lean#L376-L441); [vfMidActualPrimeFirstBadAt_two_succ_nnsNormalized_gt_half](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_CORRELATION_DESCENT.lean#L92-L135).

## 6. Ascending the actual owners from prime 2

### 6.1 A provisional physical sieve with original VF weights

Define

$$
C_{s,R}
=
R-|\operatorname{PrefixSurvivors}(s,R)|.
$$

Start at owner \(2\): \(C_{2,R}=0\). Ascend through genuine odd prime least-owners, adding each new removed composite *once*, until the cutoff \(s=R\).

Define provisional *signed* and *absolute* coordinates

$$
\boxed{
G_R(C)=-D_R+(w_R-1)R+C
}
\tag{6.1}
$$

and

$$
\boxed{
M_R(C)=|D_R|+(1-w_R)R+(2w_R-1)C.
}
\tag{6.2}
$$

At the **completed sieve** \(C=R-P_R\),

$$
G_R(R-P_R)=-D_{R+1}=U_R-L_R,
$$

$$
M_R(R-P_R)=U_R+L_R.
$$

At intermediate cutoffs these are **provisional** classifications, not the actual prime indicator. Their cone slack need not be nonnegative.

**Lean:** [vfMid915AscendingProcessedMass; vfMid915AscendingProcessedMass_two; vfMid915AscendingProcessedMass_eq_processedOwner; vfMid915AscendingProcessedMass_full](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean#L1111-L1142); [vfMid915AscendingSigned_full_eq_anchored; vfMid915AscendingAbsolute_full_eq_anchored](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean#L1196-L1280).

The inherited least-owner partition itself is in [vfMidSquarePrefixWheelSurvivors_card_add_processedOwnerCards_eq_root; vfMid_root_sub_prefixSurvivorCard_eq_processedOwnerCards](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_AFFINE_OWNER_SPLICE.lean#L227-L271).

### 6.2 Every owner step exposes the actual cross-owner term

If the next prime owner removes \(d\ge0\) newly surviving seats, then

$$
\Delta G=d,\qquad \Delta M=(2w_R-1)d.
$$

For \(\mathcal B=M^2-2G^2\), direct expansion yields

$$
\boxed{
\Delta\mathcal B
=
2d\big[(2w_R-1)M-2G\big]
+
d^2\big[(2w_R-1)^2-2\big].
}
\tag{6.3}
$$

The term linear in \(d\) involves the **entire prior accumulated signed and absolute state**. No sign is guaranteed for either term. Ownerwise positive slack or a monotone cone induction is therefore unjustified.

**Lean:** [vfMid915AscendingStage_step; vfMid915AscendingStage_slack_step](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean#L1143-L1182); [vfMid915AscendingFinalSlack_eq_anchoredBalance](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean#L1281-L1302).

### 6.3 Numerical stage checks

The ascending-stage audit gives the following **provisional** cone slacks, followed by the **actual final** one:

| \(R\) | After owner 2 | After owner 3 | Completed owner cutoff \(R\) |
| ---: | ---: | ---: | ---: |
| 18 | 89.626 | 165.913 | 104.492 |
| 317 | -10,120.581 | 25,572.580 | 13,423.785 |
| 1027 | -173,464.141 | 211,608.389 | 105,561.281 |

This makes it clear that intermediate negative states are not arithmetic errors; favorable aggregate cross-owner restoration is required. The identities alone do not explain why all first-bad escapes must be impossible.

**Code:** [vf_mid_915_ascending_sieve_regression.py](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/scripts/vf_mid_915_ascending_sieve_regression.py).

## 7. Physical quadratic Fubini, residual, and owner sectors

### 7.1 Why quadratic pair accounting is required

The target is quadratic in the full anchored physical source:

$$
\left(\sum_i z_i\right)^2
=
\sum_i z_i^2+2\sum_{i<j}z_i z_j.
$$

A degree-one owner census cannot control the sign of all historical/current pair interactions merely by counting composite removals. Hence #900/#903/#914/#915 reconstruct the **same physical pair products**, with retained weights, through first-owner and greatest-owner Fubini.

### 7.2 Partition the physical seats without fabricating owners

The parity-surviving field splits into:

- actual prime sites;
- processed squarefree composite sites;
- processed squareful composite sites.

The first two form the **active nonzero-Möbius carrier**. The last are the **squareful restoring packet**. The historical anchor \(-D_R\) is kept as a special identity-root contribution; it is not an actual integer with a fictitious least-prime owner.

The repository proves the active carrier's inclusion in the Möbius clock, the least-owner disjointness, and the omitted-squareful set equality.

**Lean:** [VF_MID_FIRST_BAD_WEIGHTED_OWNER_FUBINI.lean](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_WEIGHTED_OWNER_FUBINI.lean#L1-L202); [vfMidOddCandidates_sdiff_active_eq_squarefulProcessedCarrier; vfMidWeightedOmittedSeatAbsMass_eq_squarefulCharge](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_ACTIVE_EXCESS_LEDGER.lean#L98-L221).

### 7.3 Exact active residual and pair Fubini

Write

$$
X_R=\sum_{\rm active}z_i,\quad
H_R=\sum_{\rm active}|z_i|,\quad
J_R=\sum_{\rm active}z_i^2,
$$

and let \(C_R^{\rm sf}\) be the **signed squareful restoring charge** and \(O_R\) its original absolute mass. (This \(C_R^{\rm sf}\) is **not** the total least-prime composite census \(C_R\) defined in §3.)

For unordered active pairs,

$$
Z_R=\sum_{i<j}z_i z_j=\frac{X_R^2-J_R}{2},
$$

$$
A_R^{\rm pair}=\sum_{i<j}|z_i z_j|=\frac{H_R^2-J_R}{2}.
$$

The exact residual demand and capacity are

$$
\begin{aligned}
\mathcal E_R^{\rm demand}
&=2(D_R^2-2D_RX_R)+2J_R
-2C_R^{\rm sf}(2D_{R+1}+C_R^{\rm sf}),\\
\mathcal E_R^{\rm capacity}
&=D_R^2+2|D_R|H_R+J_R
+O_R\left[2(|D_R|+H_R)+O_R\right],\\
\mathcal E_R^{\rm residual}
&=\mathcal E_R^{\rm demand}-\mathcal E_R^{\rm capacity}.
\end{aligned}
\tag{7.1}
$$

The identity/root, diagonal, squareful and omitted-seat terms remain in the residual, not in invented owner fibres. The active pair contribution is \(4Z_R-2A_R^{\rm pair}\), so

$$
\boxed{
\mathcal E_R
=
\mathcal E_R^{\rm residual}
+
4Z_R-2A_R^{\rm pair}.
}
\tag{7.2}
$$

**Lean:** [vfMidActiveDemandResidual; vfMidActiveCapacityResidual; vfMidActiveGlobalResidualExcess](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_ACTIVE_EXCESS_LEDGER.lean#L222-L283); [vfMid_globalDemand_eq_activeResidual_add_cells; vfMid_globalCapacity_eq_activeResidual_add_cells](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_ACTIVE_EXCESS_LEDGER.lean#L284-L355); [vfMidFirstBadAnchoredCoDivExcess_eq_activeResidual_add_weightedCells](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_ACTIVE_EXCESS_LEDGER.lean#L387-L420).

### 7.4 The six orientations reduce to three actual incomplete sectors

The weighted active pairs are partitioned by first-owner signature, then mapped into a greatest-owner returned/raw-parent continuation with clipping restrictions. The six candidate orientations are distinguished by first, next, and returned positions, each left/right.

For this retained physical active carrier, three oriented sectors contribute:

$$
\boxed{\mathrm{first\text{-}left}
+\mathrm{next\text{-}right}
+\mathrm{returned\text{-}left}.}
\tag{7.3}
$$

The other three corresponding clipped orientations vanish by the actual support restrictions. This is an **exact signed Fubini classification**; it does not assign a positive cone property to the sixth priority class from earlier #903 recursion.

Thus

$$
\boxed{
\mathcal E_R
=
\mathcal E_R^{\rm residual}
+
\mathcal E_R^{\rm boundary}.
}
\tag{7.4}
$$

**Lean:** [vfMidActiveWeightedCellExcess_eq_threeBoundaryExcess](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_FINAL_AGGREGATE_CONTRACTION.lean#L1056-L1109); [vfMidFirstBadAnchoredCoDivExcess_eq_activeResidual_add_threeBoundaryExcess](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_FINAL_AGGREGATE_CONTRACTION.lean#L1147-L1155).

## 8. Greatest-owner sign reversal and the remaining sharp transport

### 8.1 Signed local heat

The local pointwise Co-minus-three-Div excess is

$$
f(z)=4z-2|z|.
$$

For a genuine Möbius sign reversal with identical retained scalar,

$$
\boxed{f(z)+f(-z)=-4|z|\le0.}
\tag{8.1}
$$

This is exact algebra: it does not require probabilistic independence, mean-zero assumptions, or a density approximation.

**Lean:** [vfMidPointwiseCoDivExcess_add_neg; sum_vfMidPointwiseCoDivExcess_add_neg](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_FINAL_AGGREGATE_CONTRACTION.lean#L562-L599); [descendingGreatestOwner_retainedScalar_pointwiseCoDivExcess_pair_eq_heat](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean#L94-L120).

### 8.2 Exact transported boundary heat

Let \(\mathcal Z_R\) denote the formal returned/stripped-parent **transported excess**, and \(H_R^{\rm boundary}\ge0\) the exact boundary **absolute pair mass**. Summation of the local identities gives

$$
\boxed{
\mathcal E_R^{\rm boundary}
+\mathcal Z_R
=-4H_R^{\rm boundary}.
}
\tag{8.2}
$$

**Lean:** [vfMidActiveThreeBoundaryExcess_add_transported_eq_neg_four_abs](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean#L579-L628).

But a **formal negative stripped parent** is not automatically a second physical source entry with which the original positive child has been paired. One must prove exact occurrence matching within the actual historical/current, survivor-restricted carrier **before spending** the negative heat as a payment.

### 8.3 The sharp transport inequality is the unchanged outstanding sign

Combine (7.4) and (8.2):

$$
\mathcal E_R
=\mathcal E_R^{\rm residual}
-\mathcal Z_R-4H_R^{\rm boundary}.
$$

Thus the required condition \(\mathcal E_R\le0\) is **exactly equivalent** to

$$
\boxed{
\mathcal E_R^{\rm residual}
\le\mathcal Z_R+4H_R^{\rm boundary}.
}
\tag{8.3}
$$

The factor \(4H_R^{\rm boundary}\) is the exact heat correction. Removing it, adding an unrepresented parent contribution, or enlarging the denominator changes the proof problem.

This equivalence is already proved:

**Lean:** [vfMidActiveResidual_le_transported_add_fourAbs_iff_anchored_nonpos; vfMidActiveResidual_sharpTransport_iff_sourceInlet](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean#L962-L987).

**Interpretation:** (8.3) is an RH-strength **inequality**, not a tautological consequence of the already-proved equalities. Merely rewriting it using the negative heat identity does not establish its sign.

## 9. What proved PNT and the protected Euler star do—and do not—supply

### 9.1 The proved PNT input

The repository already proves the native Prime Number Theorem:

$$
\boxed{\pi(x)\sim \frac{x}{\log x}.}
\tag{9.1}
$$

**Lean:** [nativePrimeNumberTheorem](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/RHLean/Analysis/NativePNTTransfer.lean#L421-L447).

On a run of square blocks with \(a\) comparable to \(B\), PNT yields the aggregate law

$$
\sum_{r=a}^{B-1}C_r
=
\sum_{r=a}^{B-1}r
-\left[Li(B^2)-Li(a^2)\right]
+o\left(\frac{B^2}{\log B}\right).
\tag{9.2}
$$

This uses actual prime counts, but its remainder is much larger than the desired \(O(B\log B)\) endpoint budget. **PNT does not imply a per-square-block \(P_R=V_R+o(1)\) estimate or a von Koch error bound by adjacent differencing.**

The stronger useful application is to reciprocal sums of actual primes over a *longer* interval.

### 9.2 A genuine subunit mass of actual high-prime owners

Define

$$
\beta_R=\sum_{\substack{R<q\le R^2\\q\text{ prime}}}\frac1q.
$$

Abel summation and PNT give the classical asymptotic

$$
\boxed{
\beta_R
\longrightarrow
\int_R^{R^2}\frac{dt}{t\log t}
=\log2<1.
}
\tag{9.3}
$$

(The integral expression is shorthand for the asymptotic main term; the variable lower bound is understood.) In particular, \(\beta_R<1\) for sufficiently large \(R\). This *eventual strict subunit bound* is a proved Lean theorem:

**Lean:** [vfMidActualRootSquareReciprocalPrimeMass_eq_abel; eventually_vfMidActualRootSquareReciprocalPrimeMass_lt_one](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_ACTUAL_PRIME_ROOT_SQUARE_CONTRACTION.lean#L298-L563).

### 9.3 Why a protected high-prime star has simple geometry

For a parent cofactor \(m<R\), legal fresh prime owners \(q>R\) satisfy \(mq\le R^2-1\). Hence \(\gcd(m,q)=1\), and on squarefree occurrences

$$
\mu(mq)=-\mu(m).
$$

Moreover two distinct primes above \(R\) cannot both divide a number below \(R^2\). Thus high-prime additions form a one-high-owner star on the protected physical carrier.

For each parent \(m\), write

$$
\mathcal Q_{R,m}
=\{q\text{ prime}: R<q\le R^2-1,\ mq\le R^2-1\}
$$

and

$$
\beta_{R,m}=\sum_{q\in\mathcal Q_{R,m}}\frac1q\le\beta_R.
$$

**Lean:** [vfMidActualHighPrimeStarSet; vfMidActualHighPrimeStar_no_two_owner_child; vfMidActualHighPrimeStarReciprocalMass_le_rootSquare](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_ACTUAL_PRIME_ROOT_SQUARE_CONTRACTION.lean#L909-L1080).

### 9.4 Exact signed Euler-star identity

Let \(v_R(m)\) be the retained reciprocal Möbius correlation for an actual protected parent cofactor; denote the literal signed parent-to-child response difference by \(\delta_R(m,q)\). A fresh prime satisfies the exact identity

$$
v_R(m)+v_R(mq)
=
\left(1-\frac1q\right)v_R(m)+\delta_R(m,q).
$$

Sum over legal actual high-prime owners:

$$
\boxed{
\operatorname{Star}_R(m)
=
(1-\beta_{R,m})v_R(m)+\operatorname{Defect}_R(m),
}
\tag{9.4}
$$

where

$$
\operatorname{Defect}_R(m)
=\sum_{q\in\mathcal Q_{R,m}}\delta_R(m,q).
$$

**Lean:** [vfMidActualHighPrimeProtectedStarMass_eq](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_ACTUAL_PRIME_ROOT_SQUARE_CONTRACTION.lean#L973-L1020); [nativePNTSignedSquareBlockCorrelationReciprocalSummand_add_mul_freshPrime](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/RHLean/Analysis/DynamicVioleBaseline.lean#L806-L850).

The repo proves the physical defect bound

$$
\boxed{
|\operatorname{Defect}_R(m)|
\le\beta_{R,m}|v_R(m)|.
}
\tag{9.5}
$$

When \(\beta_R\le1\),

$$
\begin{aligned}
|\operatorname{Star}_R(m)|
&\le(1-\beta_{R,m})|v_R(m)|
+|\operatorname{Defect}_R(m)|\\
&\le|v_R(m)|.
\end{aligned}
$$

Therefore

$$
\boxed{|\operatorname{Star}_R(m)|\le|v_R(m)|.}
\tag{9.6}
$$

**Lean:** [abs_vfMidActualHighPrimeProtectedStarDefectMass_le; abs_vfMidActualHighPrimeProtectedStarMass_le_parent_of_rootMass](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_ACTUAL_PRIME_STAR_DEFECT_CONTRACTION.lean#L36-L136).

### 9.5 Why (9.6) is not the final first-bad payment

There are **two different carriers**:

1. The **ascending low-prime** sieve \(p\le R\) on the \(R\) actual odd sites of the present square block, from which #915's \(U_R,L_R\) are assembled.
2. The **protected high-prime** reciprocal Euler star \(q>R\) on the native PNT/Möbius correlation below \(R^2\).

The theorem \(|\operatorname{Star}_R(m)|\le|v_R(m)|\) is valid on carrier (2), but is **not a proved original-source payment** on carrier (1) or on the historical/current anchored pair packet.

Even on carrier (2), the signed response defect is allowed to exhaust the nominal gain \(\beta_{R,m}|v_R(m)|\). Thus (9.6) guarantees **nonexpansion**, not a positive fixed strict saving.

Exactly this near-saturation appears in the finite computations below.

## 10. Numerical reproducibility and saturation diagnostics

### 10.1 What the numerical program actually tests

The [PNT-star signed-payment regression](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/scripts/vf_mid_915_pnt_production_regression.py) uses **actual sieved primes**, not \(P_R\approx V_R\). It computes the unchanged anchored physical \(U_R,L_R\), and independently recomputes the residual/active pair-Fubini sharp-transport identity. Separately it computes the legal high-prime Euler-star parent, children, signed defect, reciprocal coefficient, and absolute budgets.

It does **not** demonstrate a literal physical identification of every transported stripped parent with a historical/current occurrence. It does **not** test first-bad configurations: none occur in the tested range.

### 10.2 Original signed-payment margins

Define the exact original positive-gate margin

$$
\boxed{
\mathcal B_R
=
(U_R+L_R)^2-2D_{R+1}^2
=
\mathcal Z_R+4H_R^{\rm boundary}
-\mathcal E_R^{\rm residual}.
}
\tag{10.1}
$$

Representative numerical results at actual square blocks:

| \(R\) | Actual \(\beta_R\) | Signed margin \(\mathcal B_R\) | Normalized \(D_{R+1}^2/M_R^2\) |
| ---: | ---: | ---: | ---: |
| 8 | 0.537667 | 22.028829 | 0.027125 |
| 18 | 0.622831 | 104.491820 | 0.105070 |
| 56 | 0.668437 | 628.228360 | 0.184765 |
| 119 | 0.669896 | 1,777.023204 | 0.206054 |
| 317 | 0.679984 | 13,423.784662 | 0.093334 |
| 1027 | 0.689169 | 105,561.281363 | 0.107592 |
| 5266 | 0.691959 | 2,090,948.119616 | 0.045816 |
| 6000 | 0.691933 | 2,583,879.010666 | 0.095024 |

The complete consecutive scan \(8\le R\le6000\) passed:

- **5,993 square indices** with nonnegative computed signed margin.
- Max normalized squared imbalance: **0.206053679** at \(R=119\), against the candidate threshold \(1/2\).
- Minimum original signed margin: **18.949363** at \(R=9\).
- Max computed actual reciprocal coefficient: **0.692571322** at \(R=5380\), below 1.
- Max \(|D_R|/(2R\log R)\): **0.045990242** at \(R=15\).
- **No first-bad endpoint is observed**; passing these instances is not a test of the first-bad-conditional theorem itself.

### 10.3 High-prime star defect nearly saturates its allowed capacity

For each \(R\), compare the aggregate absolute defect to \(\sum_m\beta_{R,m}|v_R(m)|\), and the completed star absolute mass to the parent absolute mass:

| \(R\) | \(\beta_R\) | Abs(defect) / allowed defect capacity | Abs(star) / abs(parent) |
| ---: | ---: | ---: | ---: |
| 17 | 0.606596 | 0.991898 | 0.995554 |
| 56 | 0.668437 | 0.997863 | 0.998670 |
| 317 | 0.679984 | 0.999707 | 0.999811 |
| 1027 | 0.689169 | **0.999922** | **0.999949** |

At \(R=1027\), the actual signed sums are

$$
\underbrace{-4920.204}_{\text{retained parent}}
+
\underbrace{(-13113.115)}_{\text{signed response defect}}
=
\underbrace{-18033.319}_{\text{completed star}}.
$$

The response defect is not a negligible positive scalar remainder; it may have the same sign as the retained term and nearly consume the full available \(\beta\)-capacity. Thus **\(\beta_R<1\) alone does not provide the strict original #915 signed payment**.

### 10.4 How to rerun

On the #915 branch, from the repo root:

    python3 scripts/vf_mid_915_ascending_sieve_regression.py
    python3 scripts/vf_mid_915_pnt_production_regression.py --extended

The full numerical audit is [VF_MID_915_SECTOR_SIX_CONE_AUDIT.md](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_915_SECTOR_SIX_CONE_AUDIT.md).

GitHub Actions snapshot: [fast run 37812961563](https://github.com/OVVO-Financial/RH_Lean/actions/runs/37812961563); the numerical job passed while the production Lean compile failed at the one known unproved theorem. These are **finite deterministic checks**, not an all-scale arithmetic proof.

## 11. Why an unconditional anchored cone induction is invalid

The sign \(\mathcal B_R\ge0\) has held in the tested interval but **cannot be assumed for all \(R\)**.

A classical external analytic argument uses Littlewood's oscillations

$$
\pi(x)-Li(x)
=
\Omega_\pm\left(
\frac{\sqrt{x}\log\log\log x}{\log x}
\right)
$$

together with short-interval Brun–Titchmarsh prime upper bounds and the proved VF–Li \(O(1)\) square-endpoint bridge. Passing from an arbitrary \(x\) to a nearby square changes the prime–Li error by \(O(\sqrt{x}/\log x)\), so there is a sequence of square indices for which

$$
\frac{|D_R|}{R/\log R}\longrightarrow\infty.
$$

On the other hand, Brun–Titchmarsh gives

$$
P_R=O(R/\log R),\qquad
V_R=O(R/\log R),
$$

so

$$
|D_{R+1}-D_R|=O(R/\log R)
$$

and the current-block physical seat absolute mass satisfies

$$
w_R(R-P_R)+(1-w_R)P_R=O(R/\log R).
$$

Consequently, on such a sequence,

$$
M_R=|D_R|+O(R/\log R),\qquad
D_{R+1}=D_R+O(R/\log R)
$$

and hence

$$
\mathcal B_R=M_R^2-2D_{R+1}^2
=-D_R^2+o(D_R^2)<0.
$$

**Status of this argument:** external classical analysis and repository quadrature facts, not a Lean formalization of the final sequence. It does **not** refute an implication *conditional on a hypothetical first-bad scale*; those Littlewood oscillations are far smaller than \(2R\log R\). It does refute the strategy of making \(\mathcal B_R\ge0\) an unconditional all-\(R\) invariant. It also forbids assuming all ascending intermediate states lie in the cone.

The target must be genuinely first-bad-specific. Numerical positivity through 6000 does not establish a universal result.

## 12. The single open production inequality, precisely

### 12.1 The exact current Lean declaration

The unproved theorem is [vfMidActualPrimeFirstBadAt_two_succ_halfScaleSectorSixPayment](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean#L1305-L1366). Its statement is:

    theorem vfMidActualPrimeFirstBadAt_two_succ_halfScaleSectorSixPayment
        {R : ℕ} (hR : 8 ≤ R)
        (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) :
        2 * vfMidActualPrimeEndpointDefect (R / 2 + 1) ^ 2 +
          2 * (vfMidFrozenAffineRunPhysicalCharge
                 (R / 2 + 1) R +
               vfMidFrozenAffineBlockPhysicalCharge
                 (R / 2 + 1) R) ^ 2 -
          4 * vfMidActualPrimeEndpointDefect (R / 2 + 1) *
            (vfMidFrozenAffineRunPhysicalCharge
                 (R / 2 + 1) R +
             vfMidFrozenAffineBlockPhysicalCharge
                 (R / 2 + 1) R) ≤
        vfMidFirstBadZeroTargetTotalMass R

By the proved half-scale decomposition, the left-hand side is **exactly**

$$
2(D_a-F_{a,R+1})^2=2D_{R+1}^2.
$$

The right-hand side is **exactly** \(M_R^2\). Thus its mathematical content is

$$
\boxed{
\big[R+1\text{ is a first bad }K=2\text{ endpoint}\big]
\Longrightarrow
2D_{R+1}^2\le M_R^2
\quad(R\ge8).
}
\tag{12.1}
$$

Or equivalently, with the complete original physical masses,

$$
\boxed{
\big[h_{\rm first}\big]
\Longrightarrow
6U_RL_R-U_R^2-L_R^2\ge0.
}
\tag{12.2}
$$

The already-proved first-bad lemma forces the **strict opposite** inequality; therefore (12.1) is exactly the outstanding RH-strength contradiction.

### 12.2 What hprior, hsplit, and hheat do—and do not—prove

The open proof site currently has:

- **hprior:** prior-good \(D_a\) lies inside the radial wall.
- **hsplit:** exact anchored source \(=\) active residual \(+\) three-boundary excess.
- **hheat:** exact boundary \(+\) formally transported parent \(=-4\) times boundary absolute mass.

Then the proof requests

    have hbalance :
        0 ≤ vfMidUpperLowerBalanceSlack
          (vfMidFirstBadAnchoredUpperPartialMass R)
          (vfMidFirstBadAnchoredLowerPartialMass R) := by
      rw [vfMidFirstBadAnchoredBalanceSlack_eq_neg_coDivExcess]
      linarith

**Lean correctly rejects this goal.** The three inputs are exact equalities / earlier radial containment. They supply no independent sign on the complete original source. Changing tactics cannot turn an algebraic equivalence into a new arithmetic inequality.

### 12.3 Required mathematics, without a new equivalent problem

There are two inseparable obligations:

**(A) Complete physical signed correspondence.** Lift the already-proved owner-2 ascending degree-one source into an **occurrence-tagged, weight-preserving pair-Fubini reconstruction** that also identifies the protected high-prime Euler stars / genuine compensated owner returns with the corresponding *actual* historical/current terms. This must preserve:

1. original integer occurrences and multiplicity;
2. least- and greatest-prime owner labels;
3. surviving prefixes and clipping orientation;
4. the site's original VF scalar, including fractional multipliers;
5. historical anchor \(D_a\), the compressed current anchor \(D_R\), and their interaction;
6. diagonals, active squarefree, squareful restoring, and omitted-seat masses;
7. exact original \(M_R^2\) denominator;
8. signs of the response defect and all cross-owner terms;
9. only **genuinely matched** parent heat, never synthetic negative capacity.

The present owner-star and ascending-sieve modules are on *different carriers*. There is no proved theorem identifying them with correct global weights, restrictions, and signs in the #915 source.

**(B) A new first-bad-specific signed estimate.** Once (A) is an actual equality, use the proved PNT reciprocal mass, true Euler-star defect, and historical owner restrictions to establish, under only \(h_R\) and \(h_{\rm first}\),

$$
\boxed{
\operatorname{ActiveGlobalResidualExcess}(R)
\le
\operatorname{ThreeBoundaryTransportedExcess}(R)
+
4\,\operatorname{ThreeBoundaryAbsMass}(R).
}
\tag{12.3}
$$

This **cannot** follow just by substituting the already-proved heat identity. It must use an independent arithmetic restriction strong enough to rule out the signed residual excess at a first-bad endpoint. In particular, \(|\operatorname{Star}|\le|\operatorname{parent}|\) is too weak if the signed defect can saturate the contraction allowance.

### 12.4 Scope of the theorem

It is **not** required or valid to prove \(\mathcal B_R\ge0\) for every square block. It **is** required to prove (12.2) for every hypothetical first-bad endpoint. That conditional claim is not a mere premise reformulation: in combination with the existing strict first-bad inequality, it rules out such endpoints.

The documented obstacle is a mathematical gap in an arithmetic sign estimate, **not** an import, syntax, namespace, or Lean tactic issue.

## 13. Terminal implication and additional formal closeout work

Once the missing payment (12.1) is supplied as a genuine theorem, the downstream contradiction algebra is present.

The source-inlet equivalence and the victory lemmas are:

- [vfMidFirstBadSourceInlet_iff_halfScalePayment](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean#L922-L935)
- [vfMidActualPrimeFirstBadAt_two_succ_victory_of_sourceInlet](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean#L1019-L1043)
- [vfMidActualPrimeFirstBadAt_two_succ_sourceInlet; vfMidActualPrimeFirstBadAt_two_succ_closed](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean#L1367-L1394).

The intended terminal chain is

$$
\begin{aligned}
&h_{\rm first}\implies N_R>\tfrac12,\\
&h_{\rm first}+\text{proved payment}\implies N_R\le\tfrac12,\\
&\therefore\neg h_{\rm first},\\
&\therefore |D_R|\le2R\log R\ \text{for all }R\ge2,\\
&\therefore |\pi(x)-Li(x)|=O(\sqrt{x}\log x),\\
&\therefore\mathrm{RH}\quad\text{by the classical criterion}.
\end{aligned}
$$

This final chain also requires the following **separate formal obligations** to be checked or wired into a standalone terminal proof:

1. **Finite base indices.** The #915 contradiction is stated for \(R\ge8\), i.e. first-bad successor \(R+1\ge9\). The excluded small square indices must be formally checked at \(K=2\). This is finite, but not yet verified here as connected to the final proof.
2. **Eventual PNT to all required scales.** The proved \(\beta_R<1\) is eventual, with an unspecified sufficiently-large threshold. If the final payment relies on it, the remaining earlier indices must be handled mathematically and formally. A scan through 6000 does not establish coverage of a nonconstructively selected eventuality threshold.
3. **Classical criterion interface.** The existing RH consumer explicitly accepts **ClassicalVonKochRHCriterion**; a standalone RH theorem must supply a proven instance or a kernel-checked external theorem. Do not mistake a theorem with that parameter for an unconditional closed proof.
4. **Compilation and axiom audit.** After adding the missing signed theorem and connecting the above premises, rerun warning-fatal target compilation and the declaration/axiom audit. A green helper or numerical test is insufficient.

## 14. Lean theorem/dependency index and work restrictions

| Proof component | Lean file / declaration | Status as of pinned #915 head |
| --- | --- | --- |
| Midpoint tile and square-endpoint identity | [VF_MID_VON_KOCH_BRIDGE.lean](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_VON_KOCH_BRIDGE.lean#L63-L118) | Proved |
| VF–Li root quadrature | [vfMidLiRootBounded](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_VON_KOCH_BRIDGE.lean#L534-L572) | Proved |
| VF–Li uniform square-endpoint quadrature | [VF_MID_LI_UNIFORM_QUADRATURE.lean](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_LI_UNIFORM_QUADRATURE.lean#L630-L742) | Proved |
| Four fantasy proxy-to-RH conditional reductions | [FOUR_FANTASY_PROXY_RH_CLOSURES.lean](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/FOUR_FANTASY_PROXY_RH_CLOSURES.lean) | Proved implications; actual tracking not thereby proved |
| Square-wheel prime-survivor equivalence | [vfMidSquareBand_commonWheelSurvivor_iff_prime](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_SQUARE_WHEEL_BACKLOG.lean#L87-L124) | Proved |
| Exactly \(R\) odd candidates | [vfMidOddCandidateSeats_card](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_ODD_FRACTIONAL_CLUSTER.lean#L37-L68) | Proved |
| Actual primes + composites \(=R\) | [vfMidOddActualComposite_card_add_primeSupply](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_ODD_FRACTIONAL_CLUSTER.lean#L92-L101) | Proved |
| All-prefix prime-supply envelopes | [vfMidIntegerBlockPrimeSupply_le_every_prefixWheelEnvelope](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_SQUARE_WHEEL_BACKLOG.lean#L393-L424) | Proved |
| Signed owner census and VF tracking | [VF_MID_ODD_FRACTIONAL_CLUSTER.lean](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_ODD_FRACTIONAL_CLUSTER.lean#L114-L217) | Proved |
| Historical frozen survivor + already-processed owner charge | [VF_MID_FIRST_BAD_AFFINE_OWNER_SPLICE.lean](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_AFFINE_OWNER_SPLICE.lean#L227-L323) | Proved |
| First-bad definition and prior-good anchor | [VF_MID_ACTUAL_PRIME_FIRST_BAD_MOBIUS_TRIGGER.lean](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_ACTUAL_PRIME_FIRST_BAD_MOBIUS_TRIGGER.lean#L35-L53) | Proved |
| Exact anchored total \(M_R^2\) and NNS product | [VF_MID_FIRST_BAD_NORMALIZED_PARTIAL_MOMENT.lean](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_NORMALIZED_PARTIAL_MOMENT.lean#L162-L300) | Proved |
| First-bad \(N_R>\tfrac12\) | [vfMidActualPrimeFirstBadAt_two_succ_nnsNormalized_gt_half](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_CORRELATION_DESCENT.lean#L92-L135) | Proved |
| Ascending prime-2 source and exact numerator/denominator | [VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean#L1111-L1302) | New #915 declarations elaborate; production file as a whole does not compile |
| Active physical first-owner Fubini | [VF_MID_FIRST_BAD_WEIGHTED_OWNER_FUBINI.lean](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_WEIGHTED_OWNER_FUBINI.lean) | Proved |
| Physical residual and omitted-seat restoration | [VF_MID_FIRST_BAD_ACTIVE_EXCESS_LEDGER.lean](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_ACTIVE_EXCESS_LEDGER.lean) | Proved |
| Three oriented nonzero incomplete sectors | [VF_MID_FIRST_BAD_FINAL_AGGREGATE_CONTRACTION.lean](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_FINAL_AGGREGATE_CONTRACTION.lean#L1056-L1155) | Proved |
| Möbius pair reversal \(f(z)+f(-z)=-4|z|\) | [vfMidPointwiseCoDivExcess_add_neg](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_FINAL_AGGREGATE_CONTRACTION.lean#L562-L599) | Proved |
| Three-boundary formal negative heat | [vfMidActiveThreeBoundaryExcess_add_transported_eq_neg_four_abs](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean#L579-L628) | Algebraically proved; literal physical source payment still missing |
| Native PNT | [nativePrimeNumberTheorem](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/RHLean/Analysis/NativePNTTransfer.lean#L421-L447) | Proved |
| Actual root-to-square reciprocal \(\beta_R<1\) eventually | [VF_MID_ACTUAL_PRIME_ROOT_SQUARE_CONTRACTION.lean](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_ACTUAL_PRIME_ROOT_SQUARE_CONTRACTION.lean#L298-L563) | Proved eventually |
| Protected physical Euler-star identity | [vfMidActualHighPrimeProtectedStarMass_eq](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_ACTUAL_PRIME_ROOT_SQUARE_CONTRACTION.lean#L973-L1020) | Proved on its carrier |
| Protected Euler-star defect bound and nonexpansion | [VF_MID_ACTUAL_PRIME_STAR_DEFECT_CONTRACTION.lean](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_ACTUAL_PRIME_STAR_DEFECT_CONTRACTION.lean#L36-L136) | Proved on its carrier |
| Signed aggregate physical-source numerical check | [vf_mid_915_pnt_production_regression.py](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/scripts/vf_mid_915_pnt_production_regression.py) | Verified for finite test indices, not a theorem |
| **Complete literal PNT-star to original historical/current source splice** | [#915 scope and gap](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_915_SECTOR_SIX_CONE_AUDIT.md) | **UNPROVED** |
| **First-bad-specific signed aggregate payment** | [vfMidActualPrimeFirstBadAt_two_succ_halfScaleSectorSixPayment](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean#L1305-L1366) | **UNPROVED; target CI error at line 1354** |
| Final contradiction assuming payment | [vfMidActualPrimeFirstBadAt_two_succ_closed](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean#L1367-L1394) | Syntactically downstream; not fully compiled until payment is proved |
| Square-endpoint VF bound \(\Rightarrow\) classical error criterion | [VF_MID_VON_KOCH_BRIDGE.lean](https://github.com/OVVO-Financial/RH_Lean/blob/48305e606fe1d4b6a631b6fad7ad190dad94a8ae/research/VF_MID_VON_KOCH_BRIDGE.lean#L685-L909) | Proved as conditional transfer, explicit classical criterion parameter |

### Non-negotiable proof restrictions

- Do **not** make another fantasy/reference approximation theorem in place of the physical payment. Their geometry has already been established.
- Do **not** replace \(P_R\) by \(V_R\), or claim PNT provides a vanishing error in individual square blocks.
- Do **not** derive the signed sharp inequality merely by rewriting the Co/Div slack or the negative-heat equality.
- Do **not** assume all owner fibres, all intermediate sieve stages, all recursion priorities, or all completed actual anchored states lie in the positive cone.
- Do **not** treat algebraically manufactured stripped parents as genuinely occurring negative physical capacity without an incidence-preserving correspondence.
- Do **not** enlarge \(M_R^2\) by taking absolute values before historical compression.
- Do **not** discard the squareful restoring packet, anchor cross term, diagonal, or original \(\pm\) VF fractions.
- Do **not** treat passing finite tests or an eventually subunit reciprocal mass as an all-scale first-bad proof.
- **Do** use proved PNT as input; do not add a new conjectural prime-distribution hypothesis.
- **Do** prove the actual occurrence-matched signed payment (12.3) under only the existing first-bad premises, then let the compiled terminal consumer do the contradiction.

### One-paragraph terminal statement

The original sieve law \(P_R=R-C_R\) and the completed prime-2 ascending chronology reconstruct exactly the VF tracking error \(D_{R+1}=D_R+P_R-V_R\), including its original anchored NNS signed and absolute masses. At a supposed first bad \(K=2\) endpoint, the proved radial estimate forces normalized covariance \(N_R>1/2\). The exact first-owner Fubini partitions the same physical quadratic source into an identity/squareful/diagonal residual and three nonzero oriented boundary sectors; local Möbius reversal gives a formal \(-4|z|\) heat equality on matched returned pairs. Independently, proved PNT gives an eventually subunit reciprocal mass for actual high-prime owners, and the protected Euler-star response is nonexpansive, but numerical defect saturation shows this does not deliver a strict original-source gain. **The remaining theorem is the actual, multiplicity- and weight-preserving signed correspondence from the historical/current source into genuinely matched compensated returns, together with a first-bad-specific inequality \(\mathcal E_R^{\rm residual}\le\mathcal Z_R+4H_R^{\rm boundary}\).** Once that new arithmetic inequality is proved, the existing Lean consumer yields \(N_R\le1/2\), contradicting first badness; after the finite base and criterion interfaces are formally closed, the square-endpoint VF bound transfers to the classical von Koch criterion and RH.

---

**Maintainer scope:** This note is an audit of a **research program**. A precisely localized RH-strength unresolved inequality is not evidence that the inequality is true, nor is a numerical scan a substitute for proof. Update this document only when a new declaration genuinely establishes an additional quantitative arithmetic implication and survives warning-fatal Lean compilation and axiom audit.

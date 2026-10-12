# Finite A / finite C alignment with the direct VF proof contract

**Date: 2026-10-11. Status: research coordination, exact identities, and conditional deductions. NO unconditional finite A, finite C, or RH proof.** This note is an index and an assumption audit, not a new analytic premise or a replacement for CURRENT_PROOF_CONTRACT.md. The direct VF-mid cumulative-prime-error route remains CANONICAL; the finite-A/C Mertens route in PR #929 is a DISTINCT SUFFICIENT ALTERNATIVE. A result on one carrier must not be silently substituted on the other.

## 1. Three differently normalized objects, never conflate them

For integer R>=2 let
\[
X_R=R^2-1,\qquad
M(y)=\sum_{1\le n\le y}\mu(n),\quad M(0)=0,
\qquad
K_R=\max_{0\le y<R}\frac{(M(y)-1)^2}{y+1}\ge1.
\]
The strict historical cutoff is y<R. Define the actual bilinear floor-kernel and endpoint amplification:
\[
Q_R=\sum_{1\le a,b<R}\mu(a)\mu(b)
  \left\lfloor\frac{X_R}{ab}\right\rfloor,\qquad
C_R^{\rm bil}=\frac{|Q_R|}{R\sqrt{K_R}},\qquad
A_R^{\rm amp}=\frac{(M(X_R)-1)^2}{R^2K_R}.
\]
The **finite-C assertion** is \(\exists C<\infty\ \forall R\ge2:C_R^{\rm bil}\le C\).
The **finite-A assertion** is \(\exists A<\infty\ \forall R\ge2:A_R^{\rm amp}\le A\).
Neither uses the **direct VF-mid** defect \(D_R^{\rm VF}=\pi(R^2)-VF_{\rm mid}(R^2)\), whose canonical target is \(|D_R^{\rm VF}|=O(R\log R)\). Here C and A are Mertens amplification constants, NOT the direct VF radial-wall constant.

## 2. What is unconditional, what is conditional

The formal Dirichlet coefficient calculation below R² is exact:
\[
\boxed{Q_R=2M(R-1)-M(X_R).}
\]
The historical envelope gives \(|M(R-1)-1|\le\sqrt{RK_R}\). Therefore, **pointwise for every R**,
\[
\boxed{\sqrt{A_R^{\rm amp}}\le C_R^{\rm bil}+\sqrt2+\frac12,\qquad
C_R^{\rm bil}\le\sqrt{A_R^{\rm amp}}+\sqrt2+\frac12.}
\]
The existence of uniform finite A and uniform finite C is equivalent, with explicit constants. It is NOT established that RH implies either one; these particular uniform assertions may be strictly stronger than RH.

The existing Lean module RHLean/Proof/SquareRootAmplificationClosure.lean verifies the conditional implication from the endpoint-amplification premise to the full Mertens critical-energy estimate; RHLean/Analysis/MertensEnergyRHForward.lean supplies the forward energy-to-RH theorem. **Their theorem hypotheses have NOT been discharged.**

In particular,
\[
\boxed{\text{finite C}\iff\text{finite A}\Longrightarrow
M(x)=O(\sqrt x(\log x)^d)\text{ for some finite d}
\Longrightarrow RH.}
\]
This is a CONDITIONAL implication, not a discovered RH proof.

## 3. The full signed live-packet autopsy is already explicit

The exact prime-2 pairing at arbitrary integer x gives
\[
M(x)=\sum_{\substack{x/2<m\le x\\m\ {\rm odd}}}\mu(m).
\]
At \(x=X_R\), write \(\mathcal L_R=\{m:X_R/2<m\le X_R,\ m\ {\rm odd},\mu(m)^2=1\}\), \(L_R=|\mathcal L_R|\), and the unordered *signed pair count*
\[
\Gamma_R=\sum_{\substack{m<n\\m,n\in\mathcal L_R}}\mu(m)\mu(n).
\]
Then the unconditional identities and diagonal capacity are
\[
\boxed{M(X_R)^2=L_R+2\Gamma_R,\qquad
0\le L_R\le R^2/2.}
\]
The actual squarefree limiting count is \(L_x=(2/\pi^2)x+O(\sqrt x)\) for the odd upper-half carrier; the global 39.2% Möbius-zero frequency is NOT a density to assign to selected gcd/owner fibers.

For \(m=ga,n=gb\), with \(g=\gcd(m,n)\), squarefree and coprime supports, \(a<b<2a\),
\[
\mu(m)\mu(n)=\mu(ab),
\]
and the exact physical pair incidence is
\[
\boxed{\Gamma_R=
\sum_{\substack{a<b<2a,\;a,b\ {\rm odd}\\
(a,b)=1,\;\mu(a)^2\mu(b)^2=1}}
\mu(ab)
\#\left\{g:\frac{X_R}{2a}<g\le\frac{X_R}{b},
\ \mu(g)^2=1,\ (g,2ab)=1\right\}.}
\]
This preserves every occurrence and sign. It is a QUADRATIC pair population; its magnitude cannot be bounded by the linear number of integers merely by subtracting the zero-Möbius frequency.

Across square-time generations the parent m and a fresh-prime child pm satisfy the *exact* conditioned law \(\mu(pm)=-\mu(m)\) for \(p\nmid m\) on squarefree support, and their clocks satisfy \(t\approx\sqrt p\,r\). Their anticorrelation is at MOVING multiplicative lags, not fixed adjacent-square lags. **Two distinct simultaneously LIVE odd packets cannot be direct prime multiples**, since both lie in \((x/2,x]\). Therefore negative parent/child edges are not free negative charges within \(\Gamma_R\); they operate through past/future birth-death chronology.

Other unconditional structure: complete signed square-block birth/death recurrence; unique first-prime owner and gcd classification; fixed-T signed ancestry asymptotics with exact rational coefficients, showing a positive \(g>x/15\) population and negative compensation by \(g>x/500\); and explicit mixed signs of the true full covariance, including the exception at R=5561. The fixed-T \(O_T(\sqrt x)\) constants do NOT give uniform bounds when T grows with R. The sign/density arguments are research-note mathematics and experiments where not already independently kernel-compiled.

## 4. The only additional finite-A/C estimate and its logical status

A sufficient bound on the SAME physical signed pair ledger is
\[
\tag{H(B)}
\boxed{\exists B<\infty\;\forall R\ge2:
\Gamma_R\le B R^2K_R.}
\]
If H(B) is PROVED, the diagonal identity gives
\[
M(X_R)^2\le(2B+1/2)R^2K_R,\quad
(M(X_R)-1)^2\le(4B+3/2)R^2K_R;
\]
hence A=4B+3/2 works and finite C follows. Conversely finite A implies H(B) with B=A+1/4. Thus:
\[
\boxed{\text{H(B) for a fixed B}\iff\text{finite A}\iff\text{finite C}}
\]
as **existence statements with changed constants**. H(B) is NOT an independent new assumption one may simply add to Lean: doing so would rename the unsolved RH-strength input.

A noncircular proof must derive the signed bound from genuine arithmetic cofactor/owner counts, or construct and verify a weight- and multiplicity-preserving signed compensation **including all cross-owner terms and incomplete boundaries**. A one-edge or per-owner pairing cannot suffice: the twisted finite-C Euler ledger has genuine positive singleton faces with no available single-edge mate at the upper wall. Exact cancellation of COMPLETE Euler cubes cannot be spent inside a truncated subdoubling run; the proved boundary theorems show the complementary corners straddle the run. Complete chronology must be reassembled BEFORE taking a norm or invoking an energy inequality.

## 5. How the original VF autopsy relates, without silently bridging carriers

The authoritative CURRENT_PROOF_CONTRACT.md says the **generic no-independent-persistence / signed cell cancellation infrastructure is ALREADY PROVED**. Do not reopen it by proposing ordinary decorrelation, nonlinear correlation, additional Möbius densities or stochastic assumptions.

The VF first-bad route already has:
- exact source \(D_{R+1}=D_R+P_R-V_R\), parity-wheel survivors, and cumulative chronological owner census;
- first-owner and greatest-owner physical pair Fubini with three genuine clipped/boundary sectors;
- negative-heat identity for legitimately matched \(z,-z\) weights;
- sector-six continuation and a strict decrease in fresh-owner rank;
- known fixed-prefix endpoint budget and the run-level classifier.

Its **remaining actual-prime obligation** is narrower than "show cancellation exists": map the exact first-bad *historical/current VF weighted source* into the already-cancelled owner/terminal/sector-six ledger, preserving EACH original occurrence, its weight, survivor mask, ancestor, clipped exit, and inherited cross term. If an excess survives, prove its run-level transfer to an actually supercritical STRICTLY LOWER child run (not automatically one bad child endpoint). The explicitly named open interfaces include VFMidDyadicSignedLateCorrectionStatement (run-level correction) and downstream VFMidActualPrimeOwnerEscapeAdmissibleStatement. A signed payment for a formal parent without literal source identification is NOT an accepted payment.

The finite-A/C path is another **sufficient** route to RH on the *Mertens* carrier. It is NOT the same as the direct-VF physical source, and neither route may treat a different carrier's nonexpansion theorem as its own signed estimate without a proved correspondence.

## 6. Tested range and interpretation: NOT a universal constant

Actual endpoints reported in PR #929:

| R | M(R²−1) | Q_R | K_R | observed C_R | observed A_R |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | -1 | +3 | 1 | 1.500000 | 1.000000 |
| 317 | -28 | +22 | 1.5 | 0.056665 | 0.005579 |
| 5561 | -2544 | +2554 | 1.5 | 0.374992 | 0.139630 |
| 10000 | +1928 | -1974 | 1.5 | 0.161176 | 0.024756 |
| 20000 | -1599 | +1651 | 1.5 | 0.067402 | 0.004267 |

A genuine Möbius/prime census covers every square root \(2\le R\le 20{,}000\). The greatest observed normalized finite-C value among R>=31 is about 0.374992 at R=5561; this does NOT bound its value for R>20000. Its full live-pair covariance is \(\Gamma_{5561}=+102625\), directly disproving any general \(\Gamma_R\le0\) claim. Fixed-lag Pearson, Spearman and Kendall being near zero likewise does not give an all-R signed bound; the exact prime-conditioned multiplicative kernel has strong dependencies.

## 7. Definition of done: finite A/C or direct VF closure

An admissible mathematical completion must provide:
1. a new **independently proved**, uniform-in-R inequality with the original carrier and strict historical K_R, or an independently proved original-source first-bad run descent in the direct VF route;
2. a literal source/target correspondence with no duplicate or missing positive and negative occurrences, actual prime-factor masks and clipped two-wall boundaries;
3. the corresponding compiler-checked theorem at the exact PR head (no sorry/admit/new axioms), connected to the already-existing RH consumer; and
4. documentation and exact CI/audit results at that SAME head. A paper derivation, density calculation, finite scan, heuristic correlation, reformulation, or conditional consumer does not meet this bar.

**Current verdict:** no unconditional finite A, finite C, or direct-VF RH-scale prime-discrepancy theorem. The arithmetic genealogy is explicitly dissected and large portions of its sign reassembly are formally established; the actual-carrier quantitative closure remains OPEN. Do not label it a missing formula, new decorrelation/persistence theorem, or routine Lean tactic.

## 8. Canonical links (read existing theorems before adding analogues)

- [Current proof contract](../CURRENT_PROOF_CONTRACT.md) — CANONICAL direct VF target and multi-block owner descent.
- [Research route registry](../RESEARCH_ROUTE_REGISTRY.md) — status of alternative routes.
- [Finite-C/A original Euler floor kernel](EULER_PRODUCT_SQUARE_ROOT_FINITE_C_A.md) and [standalone handoff](SEQUENTIAL_EULER_SQUARE_BLOCK_FINITE_C_A_RESEARCH_NOTE.md).
- [Unconditional one-sided cross-owner results](FINITE_C_ONE_SIDED_CROSS_OWNER_BOUNDS_2026_10_11.md); the favorable negative direction is not the needed positive upper bound.
- [Data-driven ancestry hypotheses](FINITE_C_DATA_DRIVEN_ANCESTRY_HYPOTHESES_2026_10_11.md) — finite 20,000-root census and falsified independent small budgets.
- [Live cohort full interaction](CUMULATIVE_SQUARE_BLOCK_PRIME_COHORT_CLOCK_2026_10_11.md) and [density-preserving multiplicative Gram](MOBIUS_DENSITY_PRESERVING_MULTIPLICATIVE_GRAM_2026_10_11.md).
- [Prime-scale conditional block dependence](PRIME_SCALE_CONDITIONAL_BLOCK_DEPENDENCE_2026_10_11.md).
- [Two-wall matching no-go](TWISTED_EULER_TWO_WALL_FINITE_C_LEDGER.md).
- [Original VF first-bad autopsy](VF_MID_FIRST_BAD_FULL_PROOF_MECHANISM_AND_OPEN_PAYMENT.md).
- [Square-run top-escape classifier](SQUARE_RUN_TOP_ESCAPE_CLASSIFICATION.md) and the corresponding square-run Lean source.
- RHLean/Proof/SquareRootMertensEndpointAmplification.lean and RHLean/Proof/SquareRootAmplificationClosure.lean are **conditional Lean interfaces**, not proofs of the amplification premise.

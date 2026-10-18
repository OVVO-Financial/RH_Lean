# Two-scale signed renewal attack: from S = A - T to an independent arithmetic gain

**Date:** 2026-10-18 (America/New_York). **Status:** research attack plan; exact identities cited below are proved in existing Lean or labeled paper identities; the new general-cutoff divisor-tail estimate below is an elementary **paper calculation proposed for Lean**, not yet kernel verified. **No new unconditional signed-moment estimate, Mertens exponent gain, finite A/C, native #915 payment, VF von Koch bound, or RH proof is claimed.**

**Decision:** one source, two quantitative research horizons, seven complementary roles. This document *refines*, but does not replace, [the merged PNT-first contract](../docs/PNT_FIRST_SIGNED_COFACTOR_SEAM_2026_10_18.md) and [CURRENT_PROOF_CONTRACT.md](../CURRENT_PROOF_CONTRACT.md). Use established PNT and the externally established 7/8 result as mathematical **benchmarks/available external input**; do not pretend the 7/8 result is already a native independent proof in this Lean toolchain. Main canonical target remains the original actual-prime VF_can square-root von Koch bound. Human-only merge, unchanged schedules and saved Agent Studio permissions.

## 0. What is exact, and what is not a new theorem

For R >= 2 and X_R = R^2 - 1, set (with the original **strict high-prime cutoff**)

\[
A_R=\sum_{\substack{1\le n\le X_R\\P^+(n)\le R}}\mu(n),\qquad
T_R=\sum_{\substack{R<p\le X_R\\p\ {\rm prime}}}M(\lfloor X_R/p\rfloor),\qquad
S_R=M(X_R)=A_R-T_R.
\]

Use this as the primary arithmetic source; it is already formalized in [TwoABScaleTransfer.lean](../RHLean/Analysis/TwoABScaleTransfer.lean), [SquareRootMatchedTransport.lean](../RHLean/Analysis/SquareRootMatchedTransport.lean), and [SquareBlockSmoothTransportGram.lean](../RHLean/Proof/SquareBlockSmoothTransportGram.lean). The *other* PNT-first cofactor convention has smooth cutoff P^+(n)<R and high primes p>=R. When R is prime the two coordinate systems differ by the exact boundary fibre M(R-1); see [SquareRootSmoothRenewalInstantiation.lean](../RHLean/Analysis/SquareRootSmoothRenewalInstantiation.lean). Do not blend cutoffs.

**Threshold handoff at fixed X_R:** when R+1 is prime, all integers of greatest prime factor R+1 have form (R+1)c with 1<=c<=R-1. At fixed ceiling X_R, raising smooth cutoff R -> R+1 gives

\[
\Delta_{\rm handoff}A_R=\Delta_{\rm handoff}T_R
=-{\bf1}_{R+1\ {\rm prime}}M(R-1);
\quad \Delta_{\rm handoff}(A-T)=0.
\]

This is a source-conservation statement and must be confirmed against existing Lean before new declarations; it also holds for arbitrary source weights under the corresponding reclassification. **It does not explain the exceptional Möbius cancellation quantitatively.** The only changes to S_R along the arithmetic clock come from newly entering integers, whose signed accumulation remains the open problem.

## 1. The exact shell and prime/composite mixed term

For r>=2 let I_r = {n: r^2<n<(r+1)^2}, U_r=(r+1)^2-1, and use the same shell cutoff P^+(n)<=r as the existing square-block source. Define

\[
\delta_r=\sum_{n\in I_r}\mu(n)
        =M((r+1)^2)-M(r^2),\qquad
Q_r=\pi(U_r)-\pi(r^2).
\]

For 1<=c<=r use the **actual** high-prime extension count

\[
P_r(c)=\pi(\lfloor U_r/c\rfloor)-\pi(\lfloor r^2/c\rfloor).
\]

This is exactly the P_r(c) convention in [SQUARE_SHELL_INCIDENCE_COMPENSATION_20261017.md](SQUARE_SHELL_INCIDENCE_COMPENSATION_20261017.md). Both inequalities r^2<pc<(r+1)^2 are strict. In this range c<=r forces p>r and hence p does not divide c. In particular P_r(1)=Q_r. **Do not** substitute a lower endpoint floor((r^2-1)/c), which can erroneously admit p=r when c=r and r is prime.

Define the literal smooth shell and the signed composite charge:

\[
a_r^{\rm smooth}=\sum_{\substack{n\in I_r\\P^+(n)\le r}}\mu(n),\quad
t_r^{\ge2}=\sum_{c=2}^r\mu(c)P_r(c),\quad
C_r=a_r^{\rm smooth}-t_r^{\ge2}.
\]

Then, with no distribution assumptions,

\[
\boxed{\delta_r=a_r^{\rm smooth}-\sum_{c=1}^r\mu(c)P_r(c)=C_r-Q_r.}
\]

The exact signed shell energy is

\[
\mathcal E(H)=\sum_{H\le r<2H}\delta_r^2
=\sum_r(C_r^2+Q_r^2-2C_rQ_r).
\]

**This is the first joint arithmetic carrier.** The prime-only term has an unconditionally PNT-forced coherent square:
\(\sum_{H\le r<2H} Q_r^2\gg H^3/(\log H)^2\). An analysis that controls only the higher-divisor modes or only the Li-density model has not paid the mixed \(-2C_rQ_r\).

### Exact outer-prime interchange (candidate independent analytic inlet)

For a prime q in (H^2,4H^2), let r(q)=floor(sqrt q). Every such q belongs to one shell I_{r(q)}. Thus exactly

\[
\boxed{
\sum_{H\le r<2H} Q_r C_r
=\sum_{\substack{H^2<q<4H^2\\q\ {\rm prime}}}
\left[a_{r(q)}^{\rm smooth}
-\sum_{c=2}^{r(q)}\mu(c)P_{r(q)}(c)\right].
}
\]

The right side is a **physical two-prime/cofactor incidence plus its genuine smooth companion**, not a proof of saving. For its high-prime interior use the exact condition

\[
r(q)^2<pc<(r(q)+1)^2,\quad p>r(q),\quad 2\le c\le r(q).
\]

The inequality \(|p-q/c|<(2r(q)+1)/c\) is only a **necessary** coarse window, not an equivalent replacement. The exact shifted interval is
\((r(q)^2-q)/c < p-q/c < ((r(q)+1)^2-q)/c\).
The outer prime q and inner prime p remain distinct populations; if c>=2 then p<q in this geometry. Keep their real prime indicators unless exact PNT errors are retained.

### A stronger arithmetic-centered version to test

Re-use **the existing paper-level** smooth divisor compensator, *not* a new independent density:

\[
B_r(d)=\sum_{\substack{n\in I_r\\P^+(n)\le r\\d\mid n}}\mu(n),\qquad
a_r^{\rm inc}(c)=\sum_{k\le r/c}\mu(k)B_r(kc),
\qquad e_r(c)=\mu(c)P_r(c)-a_r^{\rm inc}(c).
\]

The proven-on-paper finite Möbius inversion gives
\(\sum_{d\mid c\le r}a_r^{\rm inc}(c)=B_r(d)\);
hence the exact **paper identity**
\(\sum_{c\le r}e_r(c)=-\delta_r\).
Its normal equation G_D a_r = b_D eliminates one coherent mixed term but **does not** bound the centered quadratic.

Pilot a dyadic owner tile

\[
\mathcal J(H;C)
=\sum_{\substack{H^2<q<4H^2\\q\ {\rm prime}}}
\sum_{\substack{C\le c<2C\\2\le c\le r(q)}}e_{r(q)}(c).
\]

The task is **not to assume** \(\mathcal J\) is tiny (the full sum can carry Mertens coherence). Instead decompose it using genuine Type I/II or an exact prime-difference operation, prove a NONTRIVIAL quantitative bound on a properly centered arithmetic suboperator, and bound **every complement**, including c=1, the q-prime square, smooth side, and historical boundary. Give scales P*C roughly H^2, admissible q/p windows, and an actual nontrivial estimate before using Cauchy–Schwarz. An equivalent bound on the complete \(\delta_r^2\) is not an acceptable alleged independent sublemma.

## 2. Quantitative milestone A: an independent improvement below 7/8

**Target A (UNPROVED):** exhibit an explicit eta>0 such that for every epsilon>0,

\[
\boxed{\mathcal E(H)\ll_\epsilon H^{5/2-\eta+\epsilon}\quad(H\ge H_0).}
\]

The existing shell-energy/Cauchy–Schwarz reduction then yields
\(M(x)=O_\epsilon(x^{7/8-\eta/4+\epsilon})\), after an ordinary epsilon reparameterization and within-shell O(sqrt x) interpolation. This would BEAT the external 7/8 benchmark if proved independently. By contrast a bound of size H^{5/2+epsilon} at best supplies another derivation of 7/8, not a gain.

### New tractable optimization of the already-paid divisor tail (paper argument)

Use the same [compensation note](SQUARE_SHELL_INCIDENCE_COMPENSATION_20261017.md)'s

\[
F_r(d)=\sum_{\substack{n\in I_r\\d\mid n}}\mu(n),\qquad
\beta_D(d)=\sum_{\substack{k\mid d\\D\le k<2D}}\mu(d/k).
\]

Its old high-divisor split is at d>=sqrt r, costing H^{5/2+epsilon} after H shells. More generally, for any real 1<=Y<=r, any band D, and any epsilon>0, elementary divisor counting gives the **proposed paper lemma**

\[
\boxed{\sum_{Y\le d\le r}|\beta_D(d)|F_r(d)^2
 \ll_\epsilon r^\epsilon\left(\frac{r^2}{Y}+r\right).}\tag{TAIL(Y)}
\]

Proof sketch: \(|\beta_D(d)|\le\tau(d)\ll_\epsilon d^\epsilon\) and
\(|F_r(d)|\le \#\{n\in I_r:d\mid n\}\le (2r+1)/d+1\); square and sum d>=Y using
\(\sum_{d\ge Y}d^{-2}\ll1/Y\), \(\sum_{d\le r}1/d\ll\log r\), absorbing logarithms into r^\epsilon. Constants are uniform in D and Y. This is elementary but requires exact endpoint formalization; **not yet Lean-verified**.

Choose \(\kappa\in(0,1/2)\), \(Y_r=\lceil r^{1/2+\kappa}\rceil\). Then

\[
\sum_{H\le r<2H}\sum_{Y_r\le d\le r}
 |\beta_D(d)|F_r(d)^2
 \ll_\epsilon H^{5/2-\kappa+\epsilon}.
\]

This is a genuine tail optimization but **NOT a shell-energy saving**: the unpaid low and middle divisor range has expanded to d<r^{1/2+\kappa}, including d=1 where \(F_r(1)^2=\delta_r^2\). All dyadic bands recombine to the original energy by Möbius inversion. No agent may announce an exponent gain until its independent low-range arithmetic bound is proved and every band/error is reassembled with the same signed source.

### Primary missing quantitative lemma

Independently obtain a Type II/dispersion or equivalent coefficient-level estimate on the **full physical low-divisor and c=1 compensated channel** that controls the remaining signed power, after the exact TAIL(Y), SS boundary and high-owner-collision budgets are subtracted. Every claimed improvement must prove the actual full \(\mathcal E(H)\) bound, not an isolated tile alone. The arithmetic information must come from actual integer spacing and multiplicative Möbius signs (e.g., admissible factor extraction and an independently bounded phase), **not** the identity \(\mathcal E(H)=\sum\delta_r^2\) as a premise.

Suggested falsification pilot: C scales 1,2,3, dyadic blocks near H^{1/4}, H^{1/2}, H^{3/4}, H and prime window scales P~H^2/C; test the complete matched \(\mathcal J\), not only the Li model. Require all p,q prime, both actual shell walls, c=1 prime-only mass and the zero smooth squareful sites.

**NO SHORT-INTERVAL MIRACLE FROM THE EXTERNAL 7/8:** knowing
\(M(b)=O_\epsilon(b^{7/8+\epsilon})\) implies at most
\(|\sum_{a<c\le b}\mu(c)|\ll b^{7/8+\epsilon}\). It supplies no fixed gain over a moving cofactor interval of length much less than \(b^{7/8}\). The proposed \(c^{-1/8}\) factor in every reciprocal short window is **not a theorem**. Conditionalize it if proposed and check all Type II off-diagonal costs.

## 3. Quantitative milestone B: cross-shell historical renewal toward RH

The exact prefix and square-block laws are

\[
M(R^2-1)=-1+\sum_{2\le r<R}\delta_r,\qquad
\left(\sum_{r\in J}\delta_r\right)^2
=\sum_{r\in J}\delta_r^2+
2\sum_{\substack{r<s\\r,s\in J}}\delta_r\delta_s.
\]

The second line is a **consumer identity**; bounding its full right side at the RH scale just renames the required Mertens bound. A second-moment improvement alone is not RH: for a dyadic shell energy exponent b,
the Cauchy–Schwarz endpoint exponent in x is \((b+1)/4\).
In particular b=2 gives 3/4; b=5/2-eta gives 7/8-eta/4. A hypothetical b=1+epsilon WOULD suffice for RH by Cauchy, so do not claim no diagonal inequality could ever imply RH, but it is far stronger than the natural H^2 energy scale.

For this long-range stage, split the **actual two-shell signed prime/cofactor sources** into shared-prime and distinct-prime ownership, and then by exact cofactor shifts and their own birth/death clocks. The next NEW lemma must control a genuinely arithmetic *restricted* positive-lag bilinear piece with all complements paid; a blanket assumption that all distinct shells have negative covariance is false.

The proposed same-prime consecutive-cofactor source has the exact signed factor
\(\mu(pc)\mu(p(c+1))=\mu(c)\mu(c+1)\) when p is prime and p>c+1.
This product has **no fixed sign** (e.g. mu(2)mu(3)=+1, mu(5)mu(6)=-1, mu(3)mu(4)=0). Its mean correlation is a difficult new number-theoretic input, not a free restoring law. For c mod 4, exactly **half** of consecutive pairs have one member divisible by 4, not a quarter. The complete long-range response needs other shared-prime and distinct-prime channels.

Likewise the suggested sign of the "Volterra feedback" is not automatic:
for a high prime p>j, floor((j^2-1)/p)<j. A fibre at shell index j cannot directly sample an earlier entire square-prefix M(i^2) when i is comparable with j. The smooth population moves with the transport and may offset its sign. **Do not assume monotone restorative drift from the minus sign in S=A-T.** Test it as an arithmetic hypothesis and seek a source-level inequality.

**True RH endpoint:** only once the missing independent arithmetic estimates imply \(M(x)=O_\epsilon(x^{1/2+\epsilon})\) for every epsilon, or yield the original \(VFCanonicalSquareVonKochStatement\), use the already-compiled classical criterion. Neither Stage A nor an exact cross-shell Gram implies RH without such a quantitative theorem.

## 4. Original physical VF/NNS obligation, not a silent consequence

[PR #975](https://github.com/OVVO-Financial/RH_Lean/pull/975) (merged) has the original first-bad positive historical residual and native boundary equation
\(\mathcal F_R=G_R+2U_R^\partial-6L_R^\partial\).
[PR #976](https://github.com/OVVO-Financial/RH_Lean/pull/976) (merged) proves a same-base two-prime orbit has **positive** Möbius pair product, not forced sign alternation.
[PR #978](https://github.com/OVVO-Financial/RH_Lean/pull/978) was OPEN/DRAFT at this plan's GitHub inventory: separate exact Λ-hyperbola signed-error and original-anchor localization. It claims for R>=13 that only c<=3 has reciprocal cofactor-window top in the original half-run; c>=4 lies below compressed historical height. **Do not treat draft #978 as merged/accepted until exact-head Lean CI and independent scope audit.**

If claiming a direct VF #915 descendant payment, write an occurrence-level map with actual weights, masks, squareful restorative source, once-only parent admission, true historical anchor and unchanged zero-target NNS denominator. A scalar Möbius S=A-T or a signed shell result is NOT termwise the original VF prime-minus-midpoint source. No half-run violations or repeated ancestors.

## 5. Seven-agent next-pass contract: one mechanism, distinct output

| Agent | Nonduplicate deliverable | Rejection test |
| --- | --- | --- |
| Research Coordinator | Source-to-bound DAG from exact S=A-T through q/p cofactor mixed term; rank one independent tile and quantify best \(\eta\) conditional on proven input; read #978 current head. | Reject all full-E or Mertens equivalent assumptions labeled new mechanism. |
| Owner Payment | Original a_r(c)/z_r(c)/e_r(c) incidence and prime outer-variable map with legal historical ancestry; isolate one payable mixed cross-owner sector. | No reused parent, omitted c=1, lost positive global residual or false sign conversion to physical VF. |
| Analytic Type II | Perform actual prime-q/prime-p dispersion on one dyadic P*C~H^2 tile, retaining mu(c), exact floor windows and compensating smooth profile; quantify EVERY remainder; optimize Y=r^{1/2+kappa}. | Reject pointwise PNT short-shell estimates, an assumed c^{-1/8} local gain, "Vaughan applies" without coefficient and scale. |
| Finite Wheel & Incidence | Verify actual shell P_r(c), the q/p double-count, endpoint p=r and divisor profile; propose a nonlocal arithmetically signed compensated kernel. | Refute guaranteed mu(c1)mu(c2)=-1, lost d=1, or "absolute neighborhood" replacing exact shell membership. |
| Prime Census Laboratory | Independently compute δ,Q,C, exact A/T, P_r(c), a_r(c), e_r(c), Q*C, dyadic E(H), divisor high-tail and tiles at predeclared held-out roots. | Reject false c=r prime boundary, fake power-law fit, wrong model, or success on only in-sample roots. |
| Adversarial Referee | Audit exact/claimed inequalities for false equivalences and accidental use of external 7/8 as native independent Lean input; test all four counterexamples in Section 6. | Provide minimal integer counterstate or missing analytic lemma for each rejected mechanism; single-session self-audit is NOT independent certification. |
| Lean Verification | Reuse already compiled S=A-T and handoff/prime-sieve modules; formalize *only* genuinely missing exact q/p reindex and TAIL(Y), then independent arithmetic estimate if analytically proved. | No sorry/admit/custom axioms, full imports, warning-fatal, standard-axiom audit and dedicated exact-head CI; do not duplicate old results. |

**Resource rule:** keep current one/day schedules and available compute budget. No new agent invocations, Studio edits, automatic merge or conditional theorem presented as proof. Every cycle produces one source-preserving research report with precise PAPER PROOF / NUMERICAL / LEAN / CONDITIONAL / UNPROVED labels.

## 6. Predeclared falsifiers, CI and stop conditions

1. **Prime-cutoff boundary:** r=7,13 are prime. Wrong use of floor((r^2-1)/r) would count the forbidden p=r; the correct lower endpoint floor(r^2/r)=r excludes it. Verify original strict q>R and newer q>=R root variants separately.
2. **Geometric equivalence failure:** q=101, p=83, c=1: with r(q)=10, \(|p-q/c|=18<2\sqrt{101}\), but pc=83 is NOT in I_10. Only the exact two-sided shell walls are admissible.
3. **Cofactor signs:** \(\mu(2)\mu(3)=+1\), \(\mu(5)\mu(6)=-1\), \(\mu(3)\mu(4)=0\). No blanket negative pair or forced shift decorrelation.
4. **Short-interval 7/8 misuse:** a root-scale cofactor short window often has bounded length and the prefix bound \(O(c^{7/8+\epsilon})\) is larger than the trivial count. Show a real savings from arithmetic **bilinear averaging**, not intervalwise PNT.
5. **Cross-owner/masks:** reproduce R=56,317,1000,5561,6000, plus adverse R=8,18 and independent withheld roots; compare complete SS/ST/TT signs and note sector sign reversals. Historical VF R=317/1027 comparisons require original weights and 3 vs >=5 cofactor windows.
6. **Falsify supposed independent lemma:** remove every equal-to-target premise, return to true physical integers, and prove that its bounded complement is actually small, including q prime-only and the d=1 nullspace.
7. **Novelty gate:** an independently proved estimate with a strict polynomial gain and a verified reduction to a real consumer is progress. A new exact reindex, model mean, normalized residual, or high-tail budget *alone* is not an improved exponent.

**Next preferred standalone deliverable:** a source-exact Lean theorem for the outer-prime reindex of the C_r Q_r mixed term, a parameterized Lean generalization TAIL(Y), and then one experimentally falsifiable **independent** Type II bound on a complete compensated q/p/cofactor tile. Stop claiming closure until all complementary sectors are paid. The eventual canonical VF von Koch bound remains open.

# FULL VF AUTOPSY — ONE CANONICAL SQRT(2)-ALIGNED DEFINITION

**Effective 2026-10-12; PR #932.**
**Authority:** new work must use the public *real* VF defined below, not silently resurrect unshifted VF_mid, historical c0, floor-Li, odd fractional seats, midpoint-linear fantasies or arbitrary corner phases under the name "VF". Old Lean names remain FROZEN INTERNAL COORDINATES so compiled theorems do not change meaning retroactively. The new default is implemented in [VF_CANONICAL_SQRT_TWO.lean](VF_CANONICAL_SQRT_TWO.lean), with the full all-real uniform quadrature in [VF_CANONICAL_ALL_REAL_LI_O_ONE.lean](VF_CANONICAL_ALL_REAL_LI_O_ONE.lean) and von Koch bridge in [VF_CANONICAL_SQRT_TWO_VON_KOCH.lean](VF_CANONICAL_SQRT_TWO_VON_KOCH.lean).

**Mathematical status:** O(1) Li quadrature is UNCONDITIONAL; actual-prime canonical von Koch tracking and RH remain OPEN. The final Lean classical von Koch ↔ RH equivalence remains the explicitly supplied standard theorem interface ClassicalVonKochRHCriterion. All new declarations must pass warning-fatal compilation and axiom audit before being called formally verified.

## 1. The single PUBLIC definition: square midpoint with a fixed sqrt(2) vertical phase

Let x>=4 and R=floor(sqrt(x)). Preserve the original square-block mass without ANY change of horizontal clock, cutoff, prime assignment, width, or denominator:

\[
m_r^{\rm mid}=r^2+r+\frac12,\qquad
V_r=\frac{2r+1}{\log(m_r^{\rm mid})},\qquad
F_R=\sum_{r=2}^{R-1}V_r.
\]

The original real live-band mass (this is NOT an integer staircase) is

\[
L_R(x)=\frac{x-R^2}{\log((R^2+x)/2)}.
\]

**Canonical VF, superseding every older user-facing plotting or tracking definition:**

\[
\boxed{\mathrm{VF}_{\rm canonical}(x)=
\sqrt2+F_R+L_R(x),\qquad R=\lfloor\sqrt x\rfloor,\quad x\ge4.}
\tag{VF-1}
\]

At square endpoints

\[
\boxed{\mathrm{VF}_{\rm canonical}(R^2)=
\sqrt2+\sum_{r=2}^{R-1}\frac{2r+1}{\log(r^2+r+1/2)}.}
\tag{VF-2}
\]

Its auxiliary integer staircase is derived ONLY AFTER the real value:

\[
\boxed{K_R=\left\lfloor\mathrm{VF}_{\rm canonical}(R^2)\right\rfloor.}
\tag{VF-3}
\]

There is no extra multiplicative coefficient or prime-dependent reweighting. The fixed additive phase does not alter any difference F_(R+1)-F_R, any square-band prime supply, any FTA wheel, least/greatest prime-owner decomposition, cofactor mask, theta scaling, or Möbius sign.

The canonical normalized Li baseline is

\[
\boxed{\operatorname{Li}_2(x)=\int_2^x\frac{dt}{\log t}.}
\tag{VF-4}
\]

The classical principal-value li(x) differs by the FIXED additive li(2). Never conflate a comparison to Li_2 with the identically normalized comparison to the standard li.

The chosen user-facing phase is **exactly sqrt(2)**. The historical exact first-anchor calibration

\[
c_{\rm anchor}=4-\frac5{\log(13/2)}
=1.328777548342988\ldots
\]

is different, and historical c_anchor graphs MUST NOT be called the canonical curve. In particular the anchored R=3 original-mass level is exactly pi(9)=4, but the canonical R=3 height is

\[
\mathrm{VF}_{\rm canonical}(9)=
\frac5{\log(13/2)}+\sqrt2
\approx4.085436\quad(\text{not }4).
\]

At x=4, VF_canonical(4)=sqrt(2), pi(4)=2 and Li_2(4)≈1.922421; VF is NOT closer than Li_2 at that endpoint. The phase is a chosen convention, NOT a theorem of optimal prime approximation.

## 2. ALL-REAL O(1) quadrature is provable NOW, not merely endpoint O(1)

There were ALREADY THREE independently proved Lean facts in the repository:

1. [VF_MID_LI_UNIFORM_QUADRATURE.lean](VF_MID_LI_UNIFORM_QUADRATURE.lean) proves the actual full signed square-band quadrature residual E_r satisfies
\[
|E_r|\le\frac{108}{r(\log r)^2},
\]
and establishes the explicit **uniform square-endpoint bound**
\[
\boxed{|\mathrm{VF}_{\rm raw}(R^2)-\operatorname{Li}_2(R^2)|\le C_{\rm square}}
\qquad\forall R\ge2,
\]
where
\[
C_{\rm square}:=|\mathrm{VF}_{\rm raw}(4)-\operatorname{Li}_2(4)|
+108\left[\frac1{2(\log2)^2}+\frac1{\log2}\right].
\]
This uses the summable \(\sum_{r\ge2}1/[r(\log r)^2]\); it does NOT depend on RH or any fact about prime distribution.

2. [VF_MID_VON_KOCH_BRIDGE.lean](VF_MID_VON_KOCH_BRIDGE.lean) ALREADY proves the uniform **single live partial-band** estimate
\[
\boxed{|L_R(x)-\int_{R^2}^x dt/\log t|\le
C_{\rm live}:=\frac9{(\log4)^2}}
\quad(R^2\le x\le(R+1)^2,\ R\ge2).
\]
3. The SAME existing file ALREADY proves the exact completion/live split
\[
\mathrm{VF}_{\rm raw}(x)-\operatorname{Li}_2(x)=
[\mathrm{VF}_{\rm raw}(R^2)-\operatorname{Li}_2(R^2)]
+[L_R(x)-\int_{R^2}^{x}dt/\log t].
\]

**Therefore, FOR EVERY REAL x>=4 without any endpoint restriction:**

\[
\boxed{\left|\mathrm{VF}_{\rm raw}(x)-\operatorname{Li}_2(x)\right|
\le C_{\rm square}+C_{\rm live}<\infty.}
\tag{VF-5}
\]

Applying the only canonical phase:

\[
\boxed{
\left|\mathrm{VF}_{\rm canonical}(x)-\operatorname{Li}_2(x)\right|
\le C_{\rm square}+C_{\rm live}+\sqrt2<\infty,
\quad \forall x\in[4,\infty).}
\tag{VF-6}
\]

At square endpoints the sharper bound is \(C_{\rm square}+\sqrt2\). The older compiled all-real \(O(\sqrt x)\) theorem was true but unnecessarily weak. **This was a theorem ASSEMBLY omission; its entire proof was already present.** The new file VF_CANONICAL_ALL_REAL_LI_O_ONE.lean makes the inference explicit; VF_CANONICAL_SQRT_TWO.lean transports it to the sole public sqrt2 path.

This is a legitimate fixed constant bound, not a claim that VF-Li has zero or negligible finite error at EVERY x. An \(O(1)\) difference also need not imply that either function is pointwise closer to true primes.

## 3. Genuine-prime endpoint arithmetic: every sector unchanged

Write P_R for the ACTUAL number of primes between consecutive square endpoints, using the repo's exact prime-counting convention. Define

\[
\boxed{D_R^{\rm canon}=
\pi(R^2)-\mathrm{VF}_{\rm canonical}(R^2)
=D_R^{\rm raw}-\sqrt2.}\tag{VF-7}
\]

Then exactly

\[
\boxed{D_{R+1}^{\rm canon}
=D_R^{\rm canon}+(P_R-V_R).}
\tag{VF-8}
\]

No prime count changes; no Sieve/FTA event is replaced by a fantasy count. On an interval A<=R,

\[
D_R^{\rm canon}-D_A^{\rm canon}
=D_R^{\rm raw}-D_A^{\rm raw}
=\sum_{r=A}^{R-1}(P_r-V_r).
\tag{VF-9}
\]

For any original owner/sector energy E(D), the phase MUST be inserted BEFORE taking abs/squares. In particular

\[
\boxed{(D_R^{\rm canon})^2
=(D_R^{\rm raw})^2-2\sqrt2\,D_R^{\rm raw}+2.}
\tag{VF-10}
\]

Thus original **linear** signed raw-parent/multi-block source sums are unchanged, while **absolute-value denominators, first-bad wall occupancy, cross terms and quadratic energy** must be evaluated in the new translated defect if the public theorem uses canonical VF.

The existing exact theta identity \(V_R\log(m_R^{mid})=2R+1\) is unchanged. Any proof using an historical anchor has to translate the anchor value \(D_A\mapsto D_A-\sqrt2\); it is not permitted to replace an absolute historical seat denominator by a single translated endpoint defect without proving compatibility.

The user's finite A/C quantities belong to a DIFFERENT, Mertens amplification criterion with strict historical K_R:
\[
Q_R=2M(R-1)-M(R^2-1),\quad
(M(R^2-1)-1)^2\le AR^2K_R.
\]
They do not inherit the sqrt2 phase and must NOT be renamed "VF constants."

## 4. Classical von Koch in the canonical coordinates: NO loss and NO new RH proof

The native earlier module already proves at the level of original real midpoint:

\[
\mathrm{VF}_{\rm raw}\text{ tracks actual }\pi
\text{ at }O(\sqrt x\log x)
\iff \pi-\operatorname{Li}_2=O(\sqrt x\log x).
\]

The square endpoints suffice for the full real-cutoff criterion. The new canonical module proves the **two-way fixed-phase transports**, with a harmless adjustment of the absolute multiplicative constant, and recovers

\[
\boxed{
\begin{aligned}
\exists C\,\forall R\ge2:
  |D_R^{\rm canon}|\le CR\log R
&\iff \exists C'\,\forall x\ge4:
 |\pi(x)-\mathrm{VF}_{\rm canon}(x)|\le C'\sqrt x\log x\\
&\iff \exists C''\,\forall x\ge4:
 |\pi(x)-\operatorname{Li}_2(x)|\le C''\sqrt x\log x .
\end{aligned}}
\tag{VF-11}
\]

The last statement is the classical von Koch criterion for RH. However RH_Lean's terminal Lean consumers still accept an EXPLICIT ClassicalVonKochRHCriterion argument; they do not construct that classical theorem internally. The other open and RH-equivalent premise is the actual-prime \(O(R\log R)\) bound in (VF-11). The phase neither proves nor assumes it.

It is false that the all-real O(1) deterministic bound (VF-6) implies RH or finite A/C, and false that any fixed vertical shift makes individual square-block prime errors small.

## 5. Complete legacy-to-canonical map: do NOT silently identify different objects

| Historical source / coordinate | Mathematically EXACT relation to new canonical VF | Legacy status |
| --- | --- | --- |
| vfMid / raw VF | VF_can(x)=vfMid(x)+sqrt2 | INTERNAL raw midpoint quadrature |
| vfMidFinishedMass R | VF_can(R²)=F_R+sqrt2 | INTERNAL raw completed band |
| vfMidLiveMass(x) | unchanged inside VF_can; +sqrt2 applied ONCE globally | INTERNAL live mass |
| vfMidChosenC0, vfMidSqrtTwoVerticalPhase | equal sqrt2 | same phase adopted as ONE public canonical alias |
| vfMidAligned(sqrt2,x) | definitionally identical to VF_can(x) | INTERNAL generic alignment engine |
| vfMidAlignedMass(sqrt2,R) | definitionally equal to VF_can(R²) | INTERNAL generic square engine |
| vfMidSqrtTwoIntegerLevel R | floor(VF_can(R²)), not real VF itself | INTERNAL rounded step |
| vfMidInitialAnchor | c_anchor ≠ sqrt2; historical x=9 exact anchor, NOT public VF | HISTORICAL calibration only |
| vfMidAlignedIntegerBacklog, rounding epsilon | K_R-F_R-sqrt2=-epsilon; bounded phase telescope | DERIVED rounding |
| vfMidOddFractionalPrimeSeatWeight | unchanged w_R=V_R/R on R true odd seats | PHYSICAL finite site realization, not VF continuum |
| vfMidOddFractionalPrimeCluster | exact at specified square endpoints **before** global +sqrt2 | AUXILIARY fantasy/fractional cluster |
| vfMidLiUpperLeftPhase, corner fan | shift VF corner by sqrt2 once; Li chord itself unshifted | PLOT/PHASE derived |
| vfMidForwardShiftedUpperLeftPhase | shift every height by sqrt2 without duplicating at edges; widths unchanged | DERIVED phase-fan |
| VF floor-Li / midpoint-linear fantasy | independent counterfactual proxies; NOT actual primes or canonical real VF | EXPERIMENT ONLY |
| vfMidDirectSquareEndpointError | D_can=D_raw-sqrt2 | INTERNAL real arithmetic defect |
| vfMidPrimeError real | E_can=E_raw-sqrt2 | INTERNAL raw running error |
| vfMidSquareEndpointVonKochBoundedStatement | equivalent to NEW VFCanonicalSquareVonKochStatement | LEGACY analytic proposition; bridge required |
| Li_2 integral_2^x | exact comparison function without sqrt2 | FIXED logarithmic-integral convention |
| classical li(x) | Li_2(x)+li(2); extra constant | DIFFERENT normalization |
| optimum logarithm base, corner-channel, theta / prime-owner classes | require their OWN proved coordinate map to shifted VALUE; source weights and prime events unchanged | NOT alternate VF definitions |
| original Mertens finite A/C | independent endpoint M and historical max K | SEPARATE research route |

The new [scripts/vf_canonical_definition_autopsy.py](../scripts/vf_canonical_definition_autopsy.py) inventories every VF-labelled definition in BOTH main RHLean and research Lean sources, with path and line number, and emits a complete machine-readable migration table. Research exports copied from primary sources are excluded to avoid counting reexports as distinct mathematics.

**Critical preservation rule:** "supersedes previous VF definitions" means the NEW public and research default is VF_can, **not** replacing legacy Lean definitions in place and invalidating thousands of existing theorem statements. Existing code importing vfMid or vfMidDirectSquareEndpointError continues to refer to their proven raw physical coordinates; a translation theorem must be used at every new public-facing boundary.

## 6. Consistency tests: original physical events, shifted endpoint and vertical phase

At the original square endpoints:

| R | x | pi(x) | Raw VF F_R | Chosen canonical VF F_R+sqrt2 | Canonical pi-VF |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 4 | 2 | 0 | 1.414214 | +0.585786 |
| 3 | 9 | 4 | 2.671222 | 4.085436 | -0.085436 |
| 4 | 16 | 6 | 5.442700 | 6.856914 | -0.856914 |

The shift has not changed any corresponding P_R or V_R.

From the existing 2499-root (R=2..2500) real-prime census, sqrt2-aligned VF is closer to Li_2 for 2498 roots, but NOT at R=2; this is empirical, not a universal theorem. The exact squared-error comparison depends on actual prime counts and can change sign.

The existing full owner/sector-six autopsy and finite-A/C ancestry results are valuable **because they expose the true signed arithmetic**. They must not be reused as proof that the new shifted first-bad bound is automatic. A constant phase does not settle positive covariance, historic unfinished owners, or signed run-level payment.

## 7. Verification, original-source trace, and definition of done

The only NEW unconditional mathematical result beyond the previous theorem inventory is the transparent **ALL-REAL O(1) theorem assembly**. Its inputs were already proved in distinct Lean modules. The new canonical API unifies chosen vertical phase, real square/live path, actual prime discrepancy, signed recurrence, Li baseline, phase corners, and von-Koch endpoint statement.

CI: [vf-canonical-sqrt-two.yml](../.github/workflows/vf-canonical-sqrt-two.yml) checks (i) full source definition autopsy, (ii) the complete all-real O(1) result with warning-fatal Lean 4.24 and standard-axiom audit, and (iii) the canonical/full von Koch closure import tree and its axioms. At PR creation these NEW declarations are PROPOSED and pending CI. An older successful quadrature job validates the historical inputs, not the new import closure until the new check passes.

**Remaining open actual-prime target in the sole public coordinate:**

\[
\boxed{\exists C\ge0\quad
\forall R\in\mathbb N,\ R\ge2:\quad
|\pi(R^2)-\mathrm{VF}_{\rm canonical}(R^2)|
\le CR\log R.}
\tag{VF-OPEN}
\]

Neither this bound nor finite A/C has been proved. Historical anchor normalization, phase plots, Euler products, and the all-real O(1) deterministic approximation cannot substitute for the missing actual-prime signed bound.

**Effective migration order:** New docs/public theorem -> VFCanonical*; unshifted source notebooks -> explicit "legacy/raw" label; old chosen phase and existing bytewise Lean proof -> preserved as implementation; corner/fantasy -> auxiliary labelled; latest proof-DAG -> explicit same-statement equivalences. Never rewrite original source quantities in an already-verified theorem as though they had silently acquired sqrt2.


## 8. Direct real-prime numerical comparison — canonical VF vs BOTH Li normalizations

**Genuine sieve, no fantasy series, and the real (unrounded) canonical sqrt2 VF.**
The dedicated, zero-extra-dependency
[compare_canonical_pi_li.py](../scripts/VFMidAlignedStepGraph/compare_canonical_pi_li.py)
sieves actual primes all the way through x=100,000,000, evaluates the
EXACT displayed real VF formula, integrates \(Li_2=\int_2^x dt/\log t\)
by composite Simpson quadrature and computes the standard
\(\operatorname{li}(x)=Li_2(x)+\operatorname{li}(2)\), with
\(\operatorname{li}(2)\approx1.045163780117493\) from the Ei Taylor series.

It then compares three signed errors and their absolute values:

\[
E_{\rm VF}(x)=\pi(x)-VF_{\rm canon}(x),\quad
E_{Li_2}(x)=\pi(x)-Li_2(x),\quad
E_{\rm li}(x)=\pi(x)-\operatorname{li}(x).
\]

Sample TRUE-prime counts and computed absolute errors:

| x | Genuine pi(x) | Real canonical VF(x) | Li_2(x) | Classical li(x) | \|pi-VF\| | \|pi-Li_2\| | \|pi-li\| |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 4 | 2 | 1.414214 | 1.922421 | 2.967585 | **0.585786** | **0.077579** | 0.967585 |
| 9 | 4 | 4.085436 | 4.676074 | 5.721238 | **0.085436** | 0.676074 | 1.721238 |
| 100 | 25 | 28.426283 | 29.080978 | 30.126142 | **3.426283** | 4.080978 | 5.126142 |
| 317 *(live, not a square)* | 66 | 69.589962 | 70.254489 | 71.299653 | **3.589962** | 4.254489 | 5.299653 |
| 1,000 *(live)* | 168 | 175.893512 | 176.564494 | 177.609658 | **7.893512** | 8.564494 | 9.609658 |
| 10,000 | 1,229 | 1,244.413401 | 1,245.092052 | 1,246.137216 | **15.413401** | 16.092052 | 17.137216 |
| 100,489 = 317² | 9,631 | 9,670.545850 | 9,671.228835 | 9,672.273998 | **39.545850** | 40.228835 | 41.273998 |
| 1,000,000 | 78,498 | 78,625.818221 | 78,626.503996 | 78,627.549159 | **127.818221** | 128.503996 | 129.549159 |
| 100,000,000 = 10000² | 5,761,455 | 5,762,207.641112 | 5,762,208.330284 | 5,762,209.375448 | **752.641112** | 753.330284 | 754.375448 |

The independent SciPy Ei evaluation reproduced the square-endpoint
values within numerical floating precision, including the pi(1e8) checkpoint.

The **COMPLETE** enumerations, not cherry-picked sample endpoints, give:

- Every square \(R^2\), for **9999 consecutive roots \(2\le R\le10000\)**: canonical VF has smaller absolute actual-prime error than \(Li_2\) at **9998/9999** roots. The sole exception is \(R=2\), \(x=4\). Against *standard* li, VF wins at **9999/9999** roots.
- Every integer cutoff **4<=x<=1,000,000** (999,997 genuine-prime checks, including all square-band interiors): canonical VF wins against \(Li_2\) at **999,992/999,997**, with exactly five exceptions \(x=4,5,6,7,8\). Against *standard* li it wins at **999,995/999,997**, exceptions \(x=5,7\).
- Mean absolute error over all square endpoints 2<=R<=10000:
  **VF 359.471266**, **Li_2 360.158813**, **standard li 361.203961**.

**Important interpretation:** at x=1e8, \(Li_2(x)-VF_{\rm canon}(x)\approx0.689173\) and \(\operatorname{li}(x)-VF_{\rm canon}(x)\approx1.734336\), whereas the errors relative to actual pi are about 753. The VF improvement is only **0.689 prime-count units**, approximately **0.0915%** of the \(Li_2\) absolute error, not a new asymptotic order or an enormous statistical gain. The near-universal sampled wins arise partly because the observed true pi is below both comparable reference curves for the large tested x; shifting the curve downward slightly helps numerically. Classical prime/li oscillations prevent inferring a universal pointwise advantage for all x. This numerical experiment does **not** establish finite A, finite C, or RH.

For reproducibility the GitHub Actions [canonical VF workflow](../.github/workflows/vf-canonical-sqrt-two.yml) executes this test on genuine primes and uploads the JSON data, independently of the Lean proofs. The ALL-REAL O(1) theorem above is unconditional mathematical content; the stronger *empirical closeness to pi* is not a universal theorem.

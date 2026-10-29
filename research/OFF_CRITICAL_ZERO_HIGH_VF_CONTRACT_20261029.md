# Off-critical zero, canonical HIGH, and actual-prime VF

**2026-10-29. Scope: finite/conditional Lean formalization and analytic proof contract. NOT an RH proof or a new uniform arithmetic bound.**

## 1. Mathematical setup

Hypothetical actual nontrivial zero:
\[
\zeta(\rho)=0,\quad \rho=\beta+i\gamma,\quad 1/2<\beta<1.
\]

The canonical Mertens LOW/HIGH decomposition is geometrical, NOT the dichotomy \(n\lessgtr\sqrt{x}\): for \(m=qc\), \(q=P^+(m)\), the gate is
\[
Y_m=(q^2-c^2)/2,\quad
LOW:\ |Y_m|\le\Lambda R,\quad HIGH:\ |Y_m|>\Lambda R
\]
in \([R^2,(R+1)^2)\). Each signed atom remains \(\mu(m)\in\{-1,0,1\}\).

The actual-prime source uses theta shortage
\[
U_R=(2R+1)-[\theta((R+1)^2)-\theta(R^2)]
\]
and canonical VF deviation
\[
D_R=\pi(R^2)-VF_{\rm can}(R^2).
\]
These are separate physical carriers until the analytic Dirichlet/log-derivative bridge is proved.

## 2. Source-certified existing theorems

- RHLean.Proof.squarePrefixMertens_eq_canonicalLow_add_high: exact actual-Mobius decomposition.
- RHLean.Proof.canonicalLowIncrementControl: uniform fixed-height LOW occupancy, and cumulative LOW = O_\Lambda(R).
- RHLean.Proof.canonicalHighUniformLocalBounded_iff_squarePrefixUniformLocalBounded_realized: HIGH criterion equivalent to total square-prefix criterion.
- RHLean.Analysis.squarePrefix_uniformLocalBounded_iff_mertensEnergyBounded: square-root Mertens energy bridge.
- RHLean.Analysis.riemannZeta_ne_zero_of_half_lt_re: INTERNALLY proved continuation to zero-free half-plane from Mertens energy.
- RHLean.Analysis.MertensExponent.zero_re_le_of_powerBound: global Mertens power envelope implies upper bound on zero real part.
- RHLean.Analysis.vfCanonicalSquareDefect_succ: actual prime/VF square-block recurrence.
- RHLean.Analysis.vf925FactorThetaForcing_eq_nativeOwnerPacket: exact wheel-to-theta-to-signed-native-owner identification.

The source file research/OFF_CRITICAL_ZERO_HIGH_VF_BRIDGE_20261029.lean adds conditional contrapositive zero->HIGH failure and exact finite true-theta coarsening/prime-VF identities, with no new axioms or unproved analytic assumptions.

## 3. Analytic obligations NOT yet formalized in Lean

**A. Global LOW Dirichlet series.** Define \(\mu_L^\Lambda(n)\) using the unique square block containing n, correct small-n/prime-square endpoint conventions, and the repository's actual largest-prime/cofactor predicate. Prove arbitrary-cutoff LOW partial sums \(O_\Lambda(\sqrt x)\) using existing per-block cardinality. By partial summation establish local-uniform convergence and holomorphy of
\[
F_L(s)=\sum_{n\ge1}\mu_L^\Lambda(n)n^{-s}
\qquad(\Re s>1/2).
\]
This is not absolute convergence at \(\Re s>1/2\).

**B. HIGH carries the reciprocal pole.** First prove on \(\Re s>1\)
\[
F_L(s)+F_H(s)=1/\zeta(s),
\qquad F_H(s)=\sum_{n\ge1}\mu_H^\Lambda(n)n^{-s}.
\]
Continue \(F_H=1/\zeta-F_L\) meromorphically to \(\Re s>1/2\). At an actual zero \(\rho\) there, \(F_H\) has pole order equal to the zero multiplicity. Do NOT assert that the HIGH Dirichlet series converges at \(\rho\).

**C. Log derivative and genuine primes.** Formally justify on the meromorphic domain
\[
-\zeta'/\zeta
=F_H'/F_H+(\zeta F_L)'/(1-\zeta F_L).
\]
At \(\rho\), the second term is holomorphic and the first has residue \(-m_\rho\). The classical series for \(-\zeta'/\zeta\) uses true von Mangoldt coefficients, not a floor-Li or VF synthetic event sequence.

**D. Theta-shortage Mellin residue.** Initially for \(\Re s>1\), define
\[
\mathscr M_U(s)=\sum_{R\ge1}U_R(R+1)^{-2s}.
\]
Prove the actual-prime formula
\[
\mathscr M_U(s)
=2\zeta(2s-1)-\zeta(2s)-1
+\zeta'(s)/\zeta(s)+\mathcal P_{\ge2}(s)-\mathcal A(s),
\]
where
\[
\mathcal P_{\ge2}(s)=\sum_p\sum_{k\ge2}\log(p)p^{-ks},
\qquad
\mathcal A(s)=\sum_p\log(p)(\lceil\sqrt p\rceil^{-2s}-p^{-s}).
\]
Both corrections are holomorphic on \(\Re s>1/2\). Therefore \(\operatorname{Res}_{s=\rho}\mathscr M_U(s)=+m_\rho\). The plus sign matters: the residue of \(-\zeta'/\zeta\) is negative.

**E. Coarsening Mellin discretization defect.** Finite coarsening
\[
(\mathcal C_qA)_R=q^{-1}\sum_{j=qR}^{q(R+1)-1}A_j
\]
has no interior endpoint leakage; the Lean bridge handles this. However its Dirichlet-Mellin transform is
\[
\mathscr M_{\mathcal C_qA}(s)=q^{2s-1}\mathscr M_A(s)+H_{q,A}(s),
\]
where \(H_{q,A}\) has a FINITE initial-boundary term AND an INFINITE within-block rounding term. The latter is not generally entire. For the actual theta shortage \(A_R=O(R\log R)\) it is holomorphic for \(\Re s>1/2\). Conclude
\[
\operatorname{Res}_{s=\rho}\mathscr M_{\mathcal C_qU}(s)
=q^{2\rho-1}m_\rho.
\]
This algebraic residue extraction does NOT imply bounded spectral extraction on polynomial-weight spaces.

**F. Explicit zero modes and realification.** With positive-real complex powers, define
\[
g_\rho(R)=((R+1)^{2\rho}-R^{2\rho})/\rho.
\]
Prove \(\mathcal C_qg_\rho=q^{2\rho-1}g_\rho\). Reuse the existing stableFarComplexToRealPair and its norm/Gram lemmas, including reflected zero \(1-\overline\rho\), radial factors \(q^{\pm2(\beta-1/2)}\), and the \(q=2,3\) joint spectral uniqueness theorem.

**G. VF escape and owner source.** The finite native prime/VF theta-to-owner identity is in the first Lean layer. Upgrade to an analytic statement proving that an off-critical zero forces failure of every prime/VF bound \(\pi(x)-VF_{\rm can}(x)=O(x^a)\) for \(1/2<a<\Re\rho\). Keep the actual-prime position correction and prime-power endpoint jumps.

## 4. Acceptance and no-drift rules

1. Lean toolchain is pinned to 4.34.1; use warning-fatal import closure compilation and #print axioms.
2. Labels must distinguish PROVED_IN_LEAN, CONDITIONAL_FROM_ZERO, ANALYTIC_CONTRACT, and OPEN_ARITHMETIC_SOURCE.
3. No sorry/admit/axiom, fictional hformula, random sign substitution, hidden RH premise, or imported unverified arithmetic rate.
4. Test strict square endpoints, prime squares and cubes, R=317, R=1027, q=2 and q=3.
5. Do NOT mark the right-half-plane pole/extraction as kernel checked until analytic tools establish meromorphic continuation and residue rigorously.
6. Do NOT mark the arithmetic HIGH bound as proved, and do not change central proof DAG or status to claim a new exponent or RH.
7. Keep human-only merge control and existing once-daily agents unchanged.

## 5. The remaining genuinely new theorem

An independent, quantified signed restriction on the complete moving-owner HIGH ancestry, or on its actual-prime theta/VF transfer, that excludes the coherent off-critical mode. Telescoping, correspondence, bounded LOW occupancy, and failure-of-HIGH-under-hypothetical-zero do NOT prove that restriction.

## 6. Code implementation ledger (2026-10-29)

The following have been added to the same draft PR for strict Lean 4.34.1
kernel checking. **Until a clean warning-fatal workflow completes,
all newly added declarations remain unverified source claims.**

| Layer | New module | Status of mathematics |
| --- | --- | --- |
| Hypothetical zero -> failure of native HIGH local energy; exact native theta/VF owner bridge | OFF_CRITICAL_ZERO_HIGH_VF_BRIDGE_20261029.lean | Exact source/conditional theorem; kernel verification pending |
| All-integer genuine LOW/HIGH coefficients and LOW support O(sqrt N) in absolute mass | OFF_CRITICAL_ZERO_LOW_HIGH_COEFFICIENTS_20261029.lean | New unconditional arithmetic theorem; kernel verification pending |
| Absolute LOW Dirichlet convergence and holomorphy for Re(s)>1/2 | Same LOW module | Known consequence via Mathlib LSeriesSummable_of_sum_norm_bigO; kernel verification pending |
| Actual Euler reciprocal on Re(s)>1 and actual von Mangoldt log derivative | OFF_CRITICAL_ZERO_EULER_LOGDERIV_20261029.lean | Existing Mathlib Euler results combined with actual LOW/HIGH; kernel verification pending |
| HIGH preserves negative meromorphic pole order | OFF_CRITICAL_ZERO_HIGH_POLE_ORDER_20261029.lean | Proved in terms of explicit negative reciprocal-pole hypothesis; actual zero -> that hypothesis still to formalize |
| Exact q-coarsening zero-mode eigenlaw and its genuine Phi realification | OFF_CRITICAL_ZERO_REALIFIED_SCALE_20261029.lean | Exact elementary spectral algebra; kernel verification pending |
| Full finite theta Mellin coarsening with within-block correction | OFF_CRITICAL_ZERO_THETA_MELLIN_FINITE_20261029.lean | Exact finite algebra; kernel verification pending |
| Continuous/holomorphic defect implies residue transport | OFF_CRITICAL_ZERO_MELLIN_RESIDUE_20261029.lean | General functional-analytic implication; kernel verification pending |

### Actual unresolved analytic sublemmas

1. Genuine prime-index block-location correction A(s) and prime-power correction P>=2(s): show locally uniform convergence and analyticity on Re(s)>1/2.
2. Identify the actual theta-shortage Mellin transform meromorphically with the explicit zeta-log-derivative expression; fix first square and s=1 endpoints.
3. Establish a uniform in q local defect majorant for the INFINITE within-block Mellin correction and prove its holomorphy for Re(s)>1/2. Then instantiate the already-written abstract residue transport, obtaining q^(2rho-1)m_rho.
4. Use zeta analyticity and isolated-zero theory to construct a strictly negative reciprocal meromorphic order at any actual off-critical zero, including higher multiplicities, and formalize the resulting HIGH pole-order and log-derivative residue.
5. Formalize arbitrary-exponent actual prime/VF escape without importing the desired prime-error estimate as an assumption.
6. Finally prove an independent, source-native uniform signed HIGH restriction. **This is an RH-strength open theorem, not a missing tactic.**

Do not collapse (1)-(5) into a single hypothetical analytic premise when claiming certification of the full sequence. Existing geometric identities alone cannot prove (6).

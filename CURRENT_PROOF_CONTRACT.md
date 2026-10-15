# RH_Lean current proof contract

**Live revision: 2026-10-15. Reviewed baseline: `main@df353c9d40c660cc247bd2fdb96c536c74b04fe3`.** Refresh live main on every run. This contract changes research direction, not any Lean definition, theorem, coefficient or proof assumption.

## Unchanged canonical object and open theorem

For x>=4, R=floor(sqrt(x)), the single public real VF is

```text
VF_can(x) = sqrt(2)
  + sum_(2<=r<R) (2*r+1)/log(r^2+r+1/2)
  + (x-R^2)/log((R^2+x)/2).
F_R = vfMidFinishedMass R.
D_can(R) = pi(R^2) - F_R - sqrt(2).
```

The public arithmetic goal remains

```text
VFCanonicalSquareVonKochStatement:
  exists C >= 0, forall R >= 2, |D_can(R)| <= C*R*log(R).
```

Read the exact [canonical interface](research/VF_CANONICAL_SQRT_TWO.lean), [criterion and consumer](research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean), [all-real quadrature](research/VF_CANONICAL_ALL_REAL_LI_O_ONE.lean), and [coordinate autopsy](research/VF_CANONICAL_SQRT_TWO_AUTOPSY_2026_10_12.md). Preserve the actual `ClassicalVonKochRHCriterion` or other explicit hypotheses of any terminal consumer.

The global VF_can-Li_2 difference is unconditionally O(1). This does not bound pi-VF_can. Li_2=int_2^x dt/log(t); principal-value li differs by a fixed constant. The sqrt(2) phase is additive and fixed, not the old exact anchor, a multiplicative scale, or a proved uniformly superior pointwise choice.

Legacy raw defect `D_raw(R)=pi(R^2)-F_R` satisfies `D_can=D_raw-sqrt(2)`. Existence of a uniform von-Koch constant is phase invariant through the compiled equivalence; a fixed-K first-bad statement or energy is not. Carry the exact correction `-2*sqrt(2)*D_raw+2` when translating squared defects. Do not modify legacy definitions or original weights.

## Active portfolio: independent arithmetic restrictions

Follow [AGENTS.md](AGENTS.md), the [dynamic protocol](docs/DYNAMIC_RESEARCH_AGENTS.md) and the [factor-depth research brief](docs/FACTOR_DEPTH_RESEARCH_BRIEF.md). The leading empirical frontier is the coupling between negative prime/semiprime tag mass and positive squareful/higher-factor mass. **It is not a new compulsory RH-strength premise.**

Start with three independently falsifiable candidates:

1. **Signed factor-depth transport/invariant:** a coefficient-preserving relation between complete depth layers, with an independently proved restriction or remainder estimate.
2. **Inverse arithmetic obstruction:** excessive imbalance forces a specified factor/ancestry/quotient configuration; separately prove that this configuration is impossible or quantitatively limited.
3. **Mobius finite-prefix signed amplification:** use the genuine, now-compiled arithmetic extension while investigating an independent bound on its signed summatory gain. Exact reconstruction is not amplitude preservation.

Nonlocal response-weighted analysis, finite A/C and CORR-4 remain eligible alternatives when their independent inputs genuinely differ. The Coordinator may revise or reject a lane with evidence; do not manufacture diversity or send all specialists to the same missing inequality in three notations. Weaker uniform estimates and exact structural theorems count at their actual strength, even before they compose with the final target.

## Raw factor-depth ledger and exact scope

For natural R>=3, the raw odd-seat carrier is

```text
C_R = {(r,n): 2<=r<R, r^2<n<(r+1)^2, n odd}.
w_r = (2*r+1)/(r*log(r^2+r+1/2)).
c(r,n) = w_r - 1_Prime(n).
L_R = sum_(C_R) c(r,n).
```

For odd prime tags 5<=q<R^2, let X_R(q) sum `w_floor(sqrt(p*q))` over odd primes p<q with p*q<R^2; put `Y(q)=1-w_floor(sqrt(q))`, `G_R(q)=X_R(q)-Y(q)`, and `T_R=sum_q G_R(q)`. Let H_R be the positive native weight of the remaining composite seats: squareful seats and squarefree seats with at least three prime factors. Perfect squares excluded by the strict block convention must not be silently added.

The reported exact partition is `L_R=T_R+H_R` (`20261015-census-1`, referee accepted on paper). Under these displayed endpoint conventions, telescoping prime counts gives the elementary coordinate relation `L_R=F_R-pi(R^2)+2`, hence `D_can(R)=2-sqrt(2)-L_R`. This paragraph is paper-level algebra, not a newly compiled bridge. Verify its match to native definitions before a Lean/source transfer.

Thus an O(R log R) bound for the total mismatch is the endpoint problem in these coordinates, not an independently paid new lemma. The **masked/clipped first-bad returned-pair carrier remains a separate object**: raw-seat admission or eligible ancestry is not a theorem of returned-cell admission.

The complete square is `L_R^2=T_R^2+H_R^2+2*T_R*H_R`. Keep all within-tag, cross-tag, cross-depth, anchor and restoration interactions when using the full zero-target NNS statistic. This raw square must not be silently substituted for the compressed #915 normalization. A sum of tag squares, local signs or mean-centered empirical correlations is not the global statistic.

## Verified Mertens baseline: do not re-prove the completed coordinate map

Live source, not the overnight report's old queue, is authoritative. PRs #948-#951 are merged at the reviewed baseline; a stale PR body may still say draft/unmerged.

- [Mertens converse identification](research/MERTENS_CONVERSE_IDENTIFICATION.lean), source blob `c15bdfcb0b050b26e3f0ea54775d8fd61d8af8bb`: `growthAtMost_iff_strip`, `growthExponent_eq_rightmost` and `logLimsup_eq_rightmost` identify the independently defined arithmetic growth exponent, literal natural-number logarithmic limsup and rightmost nontrivial-zero boundary. PR #949 head `982500b01f0f008b1164a172d06d28d14f8171d0` had all ten attached workflows successful. This is the **bidirectional** identification; the converse is no longer open. It gives no new numerical value of the common boundary.
- PR #950 establishes the finite positive-amplitude/complex-strip coordinate map. Constructed strip points are not asserted to be zeta zeros; the height is supplied independently. Zero amplitudes have no finite sample coordinate, while the separate asymptotic coordinate displays `max(1,|M(n)|)` explicitly. Finite lower-cone crossings do not imply a new upper exponent bound.
- [Finite-prefix extension](research/MERTENS_FINITE_PREFIX_EXTENSION.lean), source blob `0474a156e020dd11b32a9c023cc1ac25e48195ce`: in the integer Dirichlet convolution ring, `T(a)=2a-a*a*zetaInt` and `D(a)=1-a*zetaInt` satisfy `D(T(a))=D(a)*D(a)`. Agreement below B propagates below B^2; seed-only iteration reconstructs genuine coefficients. `guarded_interval_extension` consumes an explicitly checked finite anchor margin. Neither result proves an all-scale summatory norm estimate or perpetual guard availability. PR #951's finite computational certificates are not kernel-certified numerical data, and its optimized double-loop implementation is not silently identified with the formal convolution without the stated bridge.

A new arithmetic gain theorem would be quantitative progress. Repackaging `MertensGrowthAtMost(1/2)`, a finite-A/C bound or universal certificate preservation as an assumed input is not. There is no new unconditional seven-eighths or half-exponent estimate in these coordinate/extension results.

## Frozen #915 source and no-narrowing safeguards

For the original raw implementation in its proved range, retain

```text
m_R=(2*R+1)/log(R^2+R+1/2), w_R=m_R/R,
P_R=pi((R+1)^2)-pi(R^2),
beta_R=m_R+(1-2*w_R)*P_R,
Source(R)=D_raw(R+1)=D_raw(R)+P_R-m_R,
TotalMass(R)=(|D_raw(R)|+beta_R)^2.
```

The historical fixed-2 first-bad payment is `2*Source(R)^2 <= TotalMass(R)` **under its exact first-bad hypothesis**. Merged #939 audits this condition; it is not an independent positive covariance budget. Merged #938 proves target equivalences for signed-late correction, VF tracking and actual-prime owner-escape admissibility. Check both compiled arrows before calling any reformulation a narrower last lemma.

Do not replace compressed `|D_raw(R)|` by an uncompressed historical absolute mass without the exact lost/restored terms. Owner-cell no-independent-persistence, rank descent and Sector Six reassembly are established infrastructure on their stated carriers, not actual-source admission or the missing uniform estimate. Multi-block child runs cannot be replaced by an unsupported pointwise bad-child selector.

The paper-level original-denominator limsup obstruction `EXT-20261014-5` concerns an **unconditional all-R strict-fraction bound**, not a disproof of a conditional first-bad strategy. Preserve this distinction and its paper status. New signed mechanisms are not excluded by a technique-specific no-go.

## Retained model and local-theorem warnings

Floor-Li's bounded rounding error is by construction, not prime-counting control. Actual-prime/floor-Li, Abel, Duhamel and Volterra transports are exact identities until an independent size estimate is supplied. The continuous-Li density quadratic collision budget is finite; the naive prime-indicator version contains divergent reciprocal-prime mass. The centered sitewise scalar correction has paper asymptotic `-(1/2)*log(log X)+O(1)` (analytic-6). That refutes this local summable correction, not every response-weighted/renormalized mechanism; compare any residual logarithm with the actual permitted endpoint loss.

Local same-tag spacing, sharp four-owner packets and isolated signed inequalities retain their exact local hypotheses. They do not cover unrestricted historical descendants or survive arbitrary quadratic regrouping. The brief records mandatory small regressions and a direct full-depth census. Reuse them; do not rerun unchanged large searches merely to rediscover an accepted obstruction.

## Sufficient alternatives and history

Finite A/C remain unproved sufficient alternatives on their genuine Mertens carrier; consult [scope and assumptions audit](research/FINITE_A_C_VF_ALIGNMENT_2026_10_11.md). Their existence equivalence does not make `Gamma_R<=B*R^2*K_R` an independently known bound. Preserve native K_R, all signed cross-family terms and the actual conditional consumer. Fixed-T density/CRT or ancestry statements need a uniform transfer to growing selected carriers. CORR-4 remains optional and open; its existing conditional Stokes/remainder consumer and #797-#800 no-rediscovery restriction are unchanged.

The entire pre-update contract is preserved **byte-for-byte**, at its original root-relative link depth, in [PROOF_CONTRACT_HISTORY_2026_10_15.md](PROOF_CONTRACT_HISTORY_2026_10_15.md), blob `90510f021cf3dda5ab981fed22e7747306fa80be`. Its older 'route lock', 'binding' and 'single remaining seam' language is historical and superseded by this live portfolio; no archived prose upgrades a theorem. `CURRENT_RESEARCH_HANDOFF.md` and `RESEARCH_ROUTE_REGISTRY.md` remain detailed contextual navigation. Existing Lean source, counterexample modules, original definitions and theorem hypotheses are untouched.

**Open quantitative obligations:** canonical endpoint bound; complete-source signed payment; finite A/C; CORR-4; new uniform Mertens gain/amplitude bound. The completed bidirectional exponent identification is not on that open list. A report must distinguish independently proved structural, quantitative, finite, conditional and formal implementation progress.

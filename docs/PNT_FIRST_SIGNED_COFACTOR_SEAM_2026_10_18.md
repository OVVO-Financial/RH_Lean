# PNT-first signed cofactor / historical-return seam — seven-agent directive

**Date:** 2026-10-18 (America/New_York). **Status:** user-authorized research steering; exact arithmetic, already proved Prime Number Theorem (PNT) allowed as an input; independent uniform signed estimate and RH still OPEN. **Priority:** this contract supersedes the October 17 *mechanism-selection* priority on global covariance / Hecke / low quotients while preserving their findings, proof obligations and alternate routes. It does **not** redefine the canonical VF or authorize merge, agent Studio edits, extra runs, or altered source weights.

## 1. The research decision

**Assume the proved PNT from the outset. Do not spend agents' research budget rederiving average prime density.** Build an independent *quantitative signed* Euler–Möbius cancellation estimate from the genuine prime-extension availability and root-smooth population, treating the same historical wheel, square clocks and shared-prime ancestry as one coupled arithmetic source. The numerical evidence is important for selecting and *falsifying* a mechanism but cannot certify a uniform rate.

**Primary arithmetic seam:** show, by a genuinely new bound rather than an equivalent re-labeling, why actual prime-location discrepancies weighted by Möbius cofactors cannot accumulate a coherent adverse cross-owner response after the corresponding root-smooth contributions and historical boundary have been restored. Preserve the complete sign pattern until the final inequality.

**Unchanged public objective:** `VFCanonicalSquareVonKochStatement`, the actual-prime bound for `VF_can=VF_mid+sqrt(2)`. A valid uniform square-root Mertens estimate is a separate sufficient route to RH; it is **not** an automatic identification with the original first-bad #915 VF/NNS physical source. The proved all-real `VF_can-Li_2=O(1)` is available and does not supply `pi-Li_2` error.

## 2. Exact cofactor/PNT split; no asymptotic replacement hidden as equality

For an integer `R>=2`, put `X=R^2-1`, `t_c=floor(X/c)` and `y=R-1=floor(sqrt X)` (for `R>=2`). Define actual
```text
N_R(c) = pi(t_c)-pi(R-1)               (1<=c<R)
S_R    = sum_{n<=X, P+(n)<R} mu(n)     (P+(1)=1)
T_R    = sum_{1<=c<R} mu(c)*N_R(c)
H_R    = -T_R
M(X)   = S_R-T_R = S_R+H_R.
```
The unique high-prime factor `p>=R` of `n<=X` has `c=n/p<R`, `gcd(p,c)=1`, and `mu(pc)=-mu(c)` (also valid for squareful `c` because both sides vanish). Include `p=R` **if and only if R is prime**. Source-level comparisons using the legacy `p>R` convention must carry the `p=R` correction explicitly; do not silently equate it with root cutoff `y=R-1`.

Define `Li_2(t)=int_2^t du/log u` and **actual** `Delta(t)=pi(t)-Li_2(t)`. PNT is an established theorem `Delta(t)=o(t/log t)`, and stronger published unconditional remainders may be used with their actual hypotheses. Define
```text
L_R = sum_{1<=c<R} mu(c)*[Li_2(t_c)-Li_2(R-1)]
E_R = sum_{1<=c<R} mu(c)*[Delta(t_c)-Delta(R-1)]
    = sum_{1<=c<R} mu(c)*Delta(t_c)-M(R-1)*Delta(R-1).
```
Then **exactly**, including `c=1`, floors and endpoints,
```text
T_R = L_R+E_R,  H_R=-L_R-E_R,
M(R^2-1)=S_R-L_R-E_R.                         (PNT-FIRST IDENTITY)
```
This is an identity plus a **proved** density theorem, not a proof of a small `E_R`, a source payment, or RH. There is no general assertion of uniform short-interval PNT across moving `c`. In particular, `c` close to `R` yields intervals of bounded length near `R`; fixed-`c` asymptotics cannot be applied uniformly. Ordinary PNT and triangle inequality give at best a noncritical `E_R=o(R^2)` (and known unconditional zero-free-region errors remain roughly `R^(2-o(1))`); RH-quality pointwise `Delta(t)=O(sqrt(t)log t)` still only yields `E_R=O(R^(3/2)log R)` by separate absolute counting. **We do not assume RH-quality pointwise Delta**.

The signed Abel reassembly is also exact. With `a_c=Delta(t_c)`,
```text
E_R = sum_{c=1}^{R-2} M(c)*(a_c-a_(c+1))
      +M(R-1)*(a_(R-1)-Delta(R-1)).
```
It exposes historical correlations but provides no saving until a new genuine-arithmetic restriction is proved. Important: `E_R` by itself can carry a coherent mode proportional to `M(X)` (existing late-flip tests); a **stronger-than-needed** isolated bound on `E_R` must not be assumed, inferred from PNT, or set to zero. The whole matched source `S_R-L_R-E_R` is the scalar to control. A newly proposed sub-operator must have an independently controlled complement.

## 3. The precise unpaid estimate and three valid consumers

**PNT is not the missing theorem.** We need a theorem that controls the **joint, signed** root-smooth / prime-location / historical-return response, with complete smooth/high and cross-owner mixed terms, preferably by a source-level bilinear/Gram inequality or a genuine marked-minus-rescaled Euler operation whose principal local mode is *proved* to cancel. A statement `|S_R-L_R-E_R|<=C_eps R^(1+2eps)` is a **target-equivalent goal**, not evidence of progress without an independent signed payment. In an original VF/first-bad proof, even this scalar identity is not an occurrencewise mapping to the original clipped physical NNS source: preserve positive VF composite charges `w_R`, prime charges `w_R-1`, squareful restoration, history `D_A`, masks, and one payment per admissible occurrence.

**Consumer A (Mertens/RH):** an independently obtained `forall eps>0, |M(R^2-1)|<=C_eps R^(1+2eps)` (for all sufficiently large roots) plus the elementary `O(R)` incomplete square-block bound yields `M(x)=O_eps(x^(1/2+eps))` and hence RH via the existing classical criterion. A fixed power `<7/8` is a legitimate intermediate improvement over the externally cited 7/8 benchmark, **not** RH. Do not claim the external 7/8 theorem is kernel-proved in this repository; check its hypothesis/toolchain.

**Consumer B (finite A/C):** use the exact `Q_R=2M(R-1)-M(R^2-1)`, `K_R=max_(0<=y<R)(M(y)-1)^2/(y+1)` and seek an **independent** uniform `|Q_R|<=C R sqrt(K_R)`. Finite C is an open global estimate; substituting `Q_R` as a renamed signed remainder is circular. Preserve its genuine original normalization and initial-root conventions.

**Consumer C (canonical VF / #915):** retain `D_can(R)=pi(R^2)-VF_mid(R^2)-sqrt(2)`, target `O(R log R)`, and the #915 original signed/absolute zero-target NNS. In draft [PR #975](https://github.com/OVVO-Financial/RH_Lean/pull/975), a hypothetical large `K=2` first-bad forces positive global residual `G_R` on the ORIGINAL source, and exact pressure `E_firstbad=G_R+2U_boundary-6L_boundary`. Parent cofactor flips outside the historical half-run cannot be spent without anchor restoration. Any proposed descent must carry the historical anchor into a **strictly lower contiguous child-run** with the **same norm** and once-only source. Do not equate `mu(pc)=-mu(c)` with opposite original physical VF charge.

**Existing signed-PNT machinery:**
- `RHLean/Analysis/PrimeSievePNTCentering.lean`: actual tail = Li-density bulk + exact error.
- `research/PRIME_FLIP_PNT_TELESCOPE.lean`: reciprocal-band error, signed Möbius-atom Abel telescope, exact quadratic cross term.
- `research/PRIME_FLIP_SECOND_ORDER_PNT_CLOSURE.lean`: **conditional** RH consumer with still-OPEN independent second-order replacement bound and Li-model Stokes input.
- `research/LATE_FLIP_PNT_SPLIT_DIAGNOSTIC.md`: signed replacement error empirically follows `M(X)`; pure PNT substitution rehouses rather than pays the hard mode.
- `research/COFACTOR_CONDITIONAL_PRIME_AVAILABILITY_GCD_FINITE_C_2026_10_11.md`: precise non-independent extension sets and measured cross-owner compensation.
- `research/CUMULATIVE_SQUARE_BLOCK_PRIME_COHORT_CLOCK_2026_10_11.md`: actual packet chronology, all-scale odd `mu(2n)=-mu(n)` annihilation and incomplete-window limitation.
- [PR #976](https://github.com/OVVO-Financial/RH_Lean/pull/976): two-prime same-base shell orbit has **positive** pair product; no assumed automatic negative two-prime covariance.

## 4. Falsification / acceptance before any new RH claim

1. Define the exact physical/multiplicity carrier, ranges, cutoff and signs, the PNT theorem used, and any endpoints; do not replace real prime indicators with Li jumps where their errors matter.
2. Show algebraically where the principal density term cancels against the complete smooth/reference and where the **remaining signed error** sits. A density identity, an exact Boolean-cube cancellation of completed packets, or a signed covariance identity is not itself a bound.
3. State an independently provable new **uniform** quantitative inequality and its nonnegative/negative cross terms *before* reassembly, without hiding `M(X)`, `Delta(X)`, the original desired conclusion, `E_R`, or an RH-equivalent normalization in an unbounded remainder or named premise.
4. Test counterexamples: `R=7,13,103` for the split-prime `p=R` correction; `R=8,18` for false raw cone balance; `R=56,317,1000,6000` for reversed shared-gcd/coprime signs; `R=5561,88130` for finite-A excursions when the relevant benchmark is used. CDF crossings and changing signed sectors prevent blanket stochastic dominance and pointwise negative covariance.
5. Measure BOTH the full `S_R,L_R,E_R,M(X)` and its exact signed sector/orbit disassembly, historical source, normalized worst cases, and held-out endpoints; check integer exactness before floating Li approximation. Fit-free, predetermined power/exponent test and adversarial held-out scales are mandatory. Finite agreement never proves the uniform inequality.
6. A result must say `EXACT IDENTITY`, `FINITE NUMERICS`, `PAPER PROOF`, `PROVED IN LEAN`, `CONDITIONAL CONSUMER` or `UNPROVED`. A genuine local saving that does not control the complement is partial progress, not closure. Prefer one strictly new bounded component over ten re-labelings.
7. Never claim PNT includes pointwise RH precision, a prime short-interval theorem, a uniform square-shell sign law, or an original #915 source mapping. Retain previously certified obstructions and the existing published zero-free results as separate explicit inputs.

## 5. Seven distinct next-run contracts (same daily schedule, no new compute window)

| Scheduled role | REQUIRED next mathematical deliverable | Falsifier / stopping rule |
| --- | --- | --- |
| **RH - Research Coordinator** | Produce a one-page source-to-bound dependency DAG `prime availability -> Li+Delta -> signed matched smooth/error source -> independent uniform inequality -> one of A/B/C`; rank one attackable sub-operator and one decisive counterexample. Read both live PRs #975/#976 and recent reports. | Reject any node whose assumed bound is a reformulation of its consumer. Do not count conditional CI as a proof. |
| **RH - Owner Payment** | Produce occurrence-accurate map joining root-smooth charge, signed prime-extension `N_R(c)`, cross-owner compensation, historical `D_A`, returned masks and true native VF weights. Identify a specific source-legal mixed term that PNT density does not pay. | Reject paid parent outside original half-run, reused ancestor, imaginary even physical site, or lost positive historical global residual. |
| **RH - Analytic Type II** | Attack a stated uniform **joint signed** Li-model/error + smooth-return bilinear or mixed-moment estimate. Try a genuine compensating difference removing the principal density mode, then bound the nontrivial signed remainder by a method that is not pointwise PNT or an assumed Mertens bound. | Demonstrate nonzero power saving and control **all other terms**; do not equate a bounded density model with actual prime weights. |
| **RH - Finite Wheel & Incidence** | Prove the exact full-depth incidence kernel for `(mu(c), N_R(c), P+(c), gcd(c,d), p=R)`; locate which negative contributions physically couple distinct owners/blocks and which are geometrically forbidden. | Refute any uniform negative same-prime/coprime/shared pair sign by the known countersectors, or positive two-prime orbit. |
| **RH - Prime Census Laboratory** | Independently enumerate genuine `S_R,L_R,E_R,M(X)`, weighted and unweighted cofactor sign exposure, joint gcd-owner signed populations, and a preregistered `E_R`/matched-source residual hypothesis at held-out square roots. Include small boundary cases and adverse peaks. | Reject fitted power laws, post-hoc norm division, stale cached Li floor windows or a same-sample-only success. |
| **RH - Adversarial Referee** | Audit exact PNT remainder scales, non-uniform `c`, `c=1` endpoint `Delta(X)`, 3-vs-5 ancestral half-run frontier, false one-edge cancellation, actual source/legal clips, and whether the new inequality is independent. | State an explicit minimal counterstate or missing theorem for every rejected mechanism; do not silently inherit an agent's claim as proof. |
| **RH - Lean Verification** | Reuse the existing PNT/prime-flip/cofactor source modules; certify the exact `N=Li+Delta` and `M=S-L-E` boundary bridges **only if not already implied by compiled declarations**. Formalize one accepted independent arithmetic lemma if supplied; warning-fatal, standard-axiom audit, no admissions, actual head CI. | Do not prove the requested conclusion via an introduced RH-strength assumption, duplicate a compiled identity, or call PR #976's positive orbit a negative covariance. |

Each agent reads live `main`, `AGENTS.md`, `CURRENT_PROOF_CONTRACT.md`, `docs/DYNAMIC_RESEARCH_AGENTS.md`, **today AND yesterday's reports** from `agent-reports`, this complete directive, and actual GitHub PR states. Keep existing one/day schedules, six report-only permissions, independent referee scrutiny, Lean branch isolation, human-only merge, and report provenance. **Changing a GitHub file does not itself edit saved Agent Studio instructions, schedules, or trigger a run.** This new steering is authoritative to main-following agents **only once merged**.

## 6. Explicit route disposition

- **Promoted:** previously proved unconditional PNT as default available input; exact signed cofactor `N_R(c)` and `Delta` decomposition; reciprocal-band Möbius-atom Abel; complete historical cross-owner smooth/high joint source; original VF physical admission audit.
- **Demoted to input/comparison:** October 17 global `M^2=D+2C` covariance primary mandate, Hecke `P0-2P1`, low-bucket variation, pure cofactor CDF dominance, raw owner-sector reassemblies, local prime-edge pairing. All remain valid research lanes with their actual scope and strengths.
- **Still explicitly OPEN:** independent signed remainder/compensation estimate, finite A/C, original #915 first-bad payment, canonical `pi-VF_can` von Koch bound, RH.
- **No schedule/permission changes:** no auto-merge, no new seven-agent invocation, no imported theorem strengthened, no assumed all-scale density equilibrium.

**Next accepted discovery:** one exact source-legal *arithmetic-specific* compensating identity plus an independent nontrivial all-scale inequality controlling it (or a provably small complement), with a Lean-correct statement and a falsification script. Mere PNT replacement is not progress on the unpaid estimate.

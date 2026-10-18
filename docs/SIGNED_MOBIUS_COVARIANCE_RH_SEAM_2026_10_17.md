# Seven-agent priority: independently pay the complete signed Möbius covariance

> **Research steering update, 2026-10-18.** This October 17 global-covariance mandate is preserved as a **secondary mathematical source and alternative consumer**. The new PRIMARY seven-agent assignment is [PNT-first signed cofactor / historical compensation](PNT_FIRST_SIGNED_COFACTOR_SEAM_2026_10_18.md). No conclusion is drawn from global `M^2=D+2C` alone. Reuse full signed pair-incidence and numerical falsifiers, but apply them to genuine `N_R(c)=pi(floor((R^2-1)/c))-pi(R-1)`, `M=S-L-E`, historical boundary and actual original source. No separate signed-covariance campaign is authorized by this old document after the pivot.


**Date / authority:** 2026-10-17, America/New_York. **Status:** user-authorized strategy revision proposed on a dedicated instruction PR. Becomes live only after the human-owned merge to `main`. This is an operational research directive, NOT a new unconditional bound or RH proof. `AGENTS.md` controls actions, report permissions and schedules; `CURRENT_PROOF_CONTRACT.md` retains the canonical VF goal.

## 0. Short directive: every specialist must attack the SAME identified seam

The first independent quantitative result is not another source reassembly or zero-strip correspondence. It is a new uniform arithmetic restriction on the FULL actual signed Möbius pair mass, with no imported 7/8 theorem in the arithmetic proof:

```
mu(n) in {-1,0,+1}  (the GENUINE arithmetic Moebius function)
M(N) = sum_{1<=n<=N} mu(n)
D(N) = sum_{1<=n<=N} mu(n)^2
C(N) = sum_{1<=a<b<=N} mu(a)*mu(b)
     = sum_{1<=h<N} sum_{1<=a<=N-h} mu(a)*mu(a+h)
M(N)^2 = D(N) + 2*C(N),   0 <= D(N) <= N,   C(N) >= -D(N)/2.
```

**Benchmark conditional on the external OpenAI 7/8 result plus classical analytic transfer:**

```
for all eta>0: |M(N)| <= K_eta * N^(7/8+eta)
therefore: 0 <= D(N)+2*C(N) <= K_eta^2*N^(7/4+2*eta)
and: C(N) <= -D(N)/2 + (K_eta^2/2)*N^(7/4+2*eta).
```

The last step is EXACT algebra and **does not explain** the factor-parity cancellation. The external 7/8 theorem is a benchmark and permitted input for CONSEQUENCES, never an independent arithmetic proof of a stronger result.

**First meaningful uniform improvement:** establish, by an independently justified original-coefficient argument, for some fixed `kappa>0`, all `eta>0`, all `N>=N0(eta)`,

```
C(N) <= -D(N)/2 + K_eta*N^(7/4-kappa+eta).
```

This improves the Mertens exponent to at most `7/8-kappa/2` and, via the ALREADY compiled exponent/zero-strip mapping, excludes a larger symmetric outer zero region. The algebraic target itself is **equivalent in strength** to a Mertens power improvement; credit only a NEW independently proved source estimate as progress.

**RH-scale full-prefix target:**
```
for all eta>0: D(N)+2*C(N) = O_eta(N^(1+eta)).
```
Since `D(N)<=N`, the weaker-looking one-sided `C(N) <= O_eta(N^(1+eta))` is also sufficient. Both are RH-strength statements, not incremental independent lemmas. Reach them through a proven arithmetic mechanism or a sequence of strictly improved exponent bounds that tends to 1/2; do not promote conditional arrows to unconditional theorems.

## 1. Weighted epsilon seam, and the precise meaning of 3/8

```
E_eps(T) = sum_{1<=n<=T} M(n)^2 / n^(2+2eps)
D_eps(T) = sum_{1<=n<=T} D(n)   / n^(2+2eps)
C_eps(T) = sum_{1<=n<=T} C(n)   / n^(2+2eps)
E_eps(T) = D_eps(T)+2*C_eps(T)
0 <= D_eps(T) <= zeta(1+2eps) < infinity (eps>0).
```

The native #968 Lean implementation uses shifted `(n+1)^(-2-2eps)`; it is an equivalent convergence criterion at each fixed eps>0, but preserve the shift when referring to a theorem.

For any fixed `eps>0`, an all-T ONE-SIDED bound `sup_T C_eps(T)<infinity` implies bounded nonnegative energy and, by the standard weighted-L2/Mellin theorem, zero confinement in `[1/2-eps,1/2+eps]`. The last analytic weighted-L2 implication is **currently a separate explicit open Lean formalization obligation**, not an unconditional result of #968.

The accepted external 7/8 input gives this weighted covariance bound only for `eps>7/8-1/2=3/8`; at `eps=3/8` the inherited p-series exponent is borderline and its convergence is NOT established. Hence:

- **Benchmark:** all eps>3/8 (conditional on accepted external OAI ZF78).
- **First beyond-benchmark achievement:** one independently proved fixed `0<eps0<3/8`.
- **Specific milestone:** eps0=1/4 implies the symmetric strip [1/4,3/4].
- **RH:** bound at EVERY eps>0, with constants depending on eps, is equivalent to RH, provided the classical weighted-L2 converse and Mellin argument. No uniform-in-eps constant is required.

If using an exact power `C(N)<=O(N^(7/4-kappa))`, explain that it controls weighted `eps>(3/8-kappa/2)` and that a stronger sign-bilinear estimate (NOT the algebraic identity) pays the new `kappa`.

## 2. Do NOT mistake correlation labels or finite ratios for missing theorems

Three different carriers:

1. `C(N)`: COMPLETE unordered physical Möbius pair sum. Can be large positive or negative, NOT a [-1,1] Pearson correlation.
2. Pairwise squarefree-site average `2*C(N)/(D(N)*(D(N)-1))` for `D(N)>1`. The 7/8 premise implies `O_eta(N^(-1/4+eta))`, which tends to zero; not a near -1 law for individual pairs or lags.
3. Native root/smooth **two-aggregate** normalization `rho_R=2U_R*V_R/(U_R^2+V_R^2)`, where `U_R+V_R=M(R^2-1)-1` and diagonal `G_R=U_R^2+V_R^2>0`. This one IS in [-1,1] and `(1+rho_R)*G_R=(M(R^2-1)-1)^2`. At the measured R=5561 with U=125204, V=-127749, `rho=-0.9997975667069334`; a finite witness, not a uniform estimate. OAI 7/8 implies `(1+rho_R)*G_R=O_eta(R^(7/2+eta))`, not `rho_R -> -1` without NEW lower control on `G_R`.

The original VF/NNS historical masked, weighted, clipped, returned-source zero-target covariance is a FOURTH carrier and **requires an exact occurrence-preserving bridge** before any estimate transfers. A good scalar rho on U/V or a bucket reassembly does not establish the #915 payment.

## 3. Prefer the mechanism over its exact restatement

The novel proving ingredient must constrain the genuine signed pairs. Two exact physical decompositions provide a starting point:

```
C(N) = sum_{h=1}^{N-1} sum_{a=1}^{N-h} mu(a)mu(a+h).
```

For squarefree a,b let `d=gcd(a,b)`. Because all shared factors occur just once on each side, `mu(a)mu(b)=mu(a/d)mu(b/d)`, and in the additive-shift representation `d|h`. Thus the signs arise from UNshared prime parity, not simply the presence of shared ancestry. Explicitly retain every squareful zero, parity, even cofactor, cutoff, boundary, self/diagonal and cross-owner pairing. Do not assert independence, Chowla, decorrelation or an unproved averaged bilinear theorem.

**Potential independently sufficient, though stronger, square-shell route:** for true `delta_r = M((r+1)^2)-M(r^2)`, prove uniformly for every dyadic H:

```
sum_{H<=r<2H} delta_r^2 <= K_eta H^(5/2-kappa+eta).
```

For `kappa>0` this implies a Mertens exponent `<= 7/8-kappa/4` by the exact square-clock dyadic argument in `research/INDEPENDENT_SEVEN_EIGHTHS_SQUARE_SHELL_ENERGY_20261016.md`. Its signed pair form is the COMPLETE within-shell upper bound `sum_r sum_{a<b in I_r} mu(a)mu(b)=O_upper(H^(5/2-kappa+eta))` plus diagonal `O(H^2)`. This shell condition is stronger than merely the global 7/8 Mertens outcome; do not treat the already-known external OAI bound as proof of it. Do not identify this shell Gram with global C(N) or original VF/NNS source.

Also eligible: an independently proved nonlocal high/low-prime owner mixed moment, a complete signed Hecke `P0-2P1` payment before absolute values, or an averaged shifted-factor bilinear inequality that genuinely bounds the above complete pair carrier. Do not let any of these degenerate to `M^2 = D+2C` plus an assumed bound of exactly the desired size.

## 4. Mandatory role-specific first output: seven independent specialties, one seam

| Saved Studio role | Required first mathematical deliverable | Explicit rejection test |
| --- | --- | --- |
| **RH | Research Coordinator** | Build the quantitative dependency DAG: exact `C(N)`, `C_eps`, root/smooth rho, shell signed energy, 7/8 baseline and RH `1+eta` endpoint. Assign ONE shared candidate signed arithmetic mechanism and ONE competing falsifier for this cycle. Supply gap exponent, original physical carrier, uniformity, first unproved lemma, day-prior handoff and primary accountable owner. | Reject an all-role report containing only recast RH, benchmark reuse or seven disparate unexplained PRs. |
| **RH | Owner Payment** | Preserve actual greatest-prime chronology and derive an occurrencewise, once-only mapping of ORIGINAL root/smooth U,V and full cross-owner pairs to `C(N)` or a clearly distinct full-shell carrier. Seek nonlocal matched born-smooth/transport signs BEFORE norms. Record what source/mask/anchor is and is NOT transported to #915. | Reject a near-minus-one scalar sample as a per-edge pairing, an unproved denominator lower bound, or missing restored historical charges. |
| **RH | Analytic Type II** | Attack a standalone uniform signed shifted-correlation/bilinear or two-variable mixed-moment estimate with full `h`/cofactor range. State a candidate `kappa>0`, endpoint `N`, quantified losses, major/minor arcs and unbounded-height limitations; demonstrate the strict route from its lemma to `C(N)=O_upper(N^(7/4-kappa+eta))` or a full shell `5/2-kappa` input. Distinguish the OAI consequence from a new theorem. | Reject pointwise or almost-all shifts substituted for all N; rejecting a signed global estimate via triangle inequality; treating OAI ZF78 as the independent saving. |
| **RH | Finite Wheel & Incidence** | Derive an exact pair-incidence partition by `d=gcd(a,a+h)|h`, squarefree gates, unshared-prime parity, largest-prime ownership and shifts h, including all cross-owners and off-square boundaries. Identify a candidate arithmetic constraint whose proof would save `N^kappa` when recombined. | Reject solely fixed-modulus survivor density, character selector mean-zero, same-owner local sign flip, missing squares or omitted self/diagonal terms. |
| **RH | Prime Census Laboratory** | Independently enumerate `M,D,C` as integers and `C_eps` as floating/high-precision diagnostics; distinguish global pair ratio `2C/D`, pair average and root/smooth rho. Predeclare witnesses R=7,13,103,317,1027,5561, held-out nonsquares and dyadic shells; verify exact `M^2=D+2C`, `U+V=M(R^2-1)-1`; test the specific role-selected inequality, sign falsifiers and worst-window spikes. | Reject extrapolating finite rho to a uniform rate, re-running giant scans without hypothesis, or reporting a non-equivalent normalization as proof. |
| **RH | Adversarial Referee** | Independently challenge every new `kappa` estimate; check theorem quantifiers/all N, shifted pair double-counting, gcd/parity signs, positive cross-owners, squareful terms, the precise 7/8->3/8 p-series and epsilon endpoint, external provenance and RH-equivalent circularity. Reproduce one counterexample or a distinct verification. | Reject self-review as independent; accept conditional consumers only with explicit unsolved input; never promote a Lean iff to an independently paid arithmetic inequality. |
| **RH | Lean Verification** | Inspect exact-head #968/#969 first and their stack; audit warnings-fatal dependencies, standard axioms, analytic weighted-L2 bridge and mathlib source. Formalize ONLY new exact original-carrier lemmas that survive referee or an independently proved quantitative saving, with named explicit hypotheses. Verify CI, provenance and reports. | Reject `sorry`, `sorryAx`, unproved imported OAI, changing the native coefficients, duplicate identity PRs or a claim that the open weighted-L2 bridge is automatically closed. |

Role assignments here DO NOT grant new permissions, change schedules or guarantee agent execution. All six non-Lean specialists remain report-only on their own path in `agent-reports`, while Lean may use only its authorized draft proof branch. The reporting order, one-run-per-agent-per-day budget and human-only merge remain unchanged.

## 5. Acceptance contract: any proposed new gain

A report must present (i) an unambiguously NEW arithmetic inequality with its carrier (full prefix, weighted prefix, dyadic shell, original VF/NNS), (ii) signs, weights, strict endpoints and all diagonal/off-diagonal/cross-family terms, (iii) uniform all-scale quantifiers, (iv) a candidate exponent with a proof of its effect on the 7/8 wall or RH, (v) explicit comparison to what external OAI already implies, (vi) exact finite adversarial tests and cited source/PR/CI proof status, (vii) independent Referee decision, (viii) one next mathematical bottleneck, and (ix) no hidden circular premise. Record if failure is OPEN, FALSE on real arithmetic, TARGET_EQUIVALENT, or source transport missing.

**Only the discovery/proof of an independently justified uniform signed arithmetic restriction is new mathematical progress.** The classical symmetry, exponent identity, Green--Kubo square expansion, positive p-series bound, root/smooth normalization and conditional OAI transfer are now established baselines, not recurrent proof tasks.

### Authority and live status

- Main historical source: `RHLean/Analysis/DeterministicTGreenKuboComparison.lean` (native `M^2=D+2C`) and `RHLean/Proof/SquareRootLegalAncestryGramReduction.lean` (root/smooth physical state).
- On 2026-10-17, **PR #968** introduces `research/MERTENS_WEIGHTED_COVARIANCE_RH.lean`, and **PR #969**, stacked on #968, introduces `research/OAI_SEVEN_EIGHTHS_WEIGHTED_COVARIANCE.lean` and `research/OAI_SEVEN_EIGHTHS_ROOT_SMOOTH_ANTIALIGNMENT.lean`. These are NOT on main until actually merged; refresh live PR metadata at execution. PR #968's dedicated workflow required the pinned StrongPNT patches (fix commit is on its branch); do not assume CI success without inspecting the latest head.
- Existing compiled analytic zeta/Mertens mapping on main: `research/MERTENS_CONVERSE_IDENTIFICATION.lean`. The standalone weighted L2 -> Mellin/RH analytic consumer in #968/#969 is intentionally an explicit, unproved Lean bridge; paper mathematics is standard.
- The OpenAI 7/8 theorem is an **external published formally claimed result** in a different Lean toolchain, not a newly proven theorem of RH_Lean. Treat its use as a conditional input until exact integration and source verification. Later claimed refinements must be source-checked before adjusting the baseline.

Do not reconfigure Studio schedules or misrepresent an Agent Studio update based on a GitHub Markdown commit. Saved Studio role instructions must already direct each agent to fetch fresh `main` authority; repository changes activate only after an authorized human merges this instruction PR.

# QRH source-estimate execution contract (26 October 2026)

**Status: RESEARCH INSTRUCTIONS AND CONDITIONAL SENSITIVITY, NOT A NEW ZERO-FREE THEOREM.** Derived from the user's 2026-10-26 `QRH Source-Estimate Ledger v1` and source-checked against the actual tracker declarations. The numerical ledger is a parameter model; source improvements are **hypothetical until the original analytic inequality is proved with all its hypotheses and its consumer is recompiled**. This file is the operational interface for agents; the full uploaded numerical package is not vendored by this instructions-only PR. Never label its model outputs as proof.

## 1. Targets, certified benchmark and theorem scope

- **Merged all-Dirichlet tracker benchmark:** GTimG/QuasiRiemannTracker PR [#76](https://github.com/GTimG/QuasiRiemannTracker/pull/76), merge commit `01c21abe8547304d033798ae7e4752dba4038209`: β = 349843/400000 = **0.8746075**, not merely the original OpenAI 7/8. Recheck the actual tracker main, verifier and latest merged submission at each run.
- **Not yet merged at this document's verification:** tracker [#79](https://github.com/GTimG/QuasiRiemannTracker/pull/79), proposed β = 0.8746074 at h=0.8018. Do not call a pending candidate certified or silently downgrade a later verified baseline. Compare proposed margins both against the latest merged record and the best credible pending candidate.
- **Native RH_Lean current certified import:** pinned original OpenAI 7/8, proved complete arithmetic transfer to genuine Mertens signed covariance on main via [#987](https://github.com/OVVO-Financial/RH_Lean/pull/987), but **not** an import of tracker #76/#79 as Lean theorems. A new zeta-only result and a stronger **all-Dirichlet** tracker submission are different achievements.
- Every genuine zeta/Mertens β-bound implies the original real Co/Div residual D(N)+2C(N)=M(N)^2 = O_ε(N^(2β+ε)), the one-sided signed C upper envelope, and weighted-covariance convergence for each η>β-1/2. The reverse arithmetic boundary is formalized in `research/MERTENS_CONVERSE_IDENTIFICATION.lean`; original Co/Div receiver in `research/VF_919_OPENAI_434_UNCONDITIONAL_SQUARE_BLOCK_COVARIANCE_20261019.lean`. They **receive** improved β; by themselves they do not improve it.

## 2. Hecke / tracker source-estimate lane (OAI-NNS)

**The live binding source is not the arbitrary NNS split.** In tracker #76, `FinalReturn/ReturnFormulas.lean` the most constrained newTop edge at d≈h≈0.802 is near p=q/δ=1/2 and δ≈0.4525 on count face C. Under the uploaded idealized return model, the count-exponent exchange rate is Δβ ≈ 0.133×(saving in the actual saturated-row count exponent), until a different edge binds. This is **conditional model sensitivity**, not a certified local derivative of the full theorem.

Primary independent input to prove (actual row family, not fabricated amplitudes): for a fixed admissible near-saturation strip e.g. p≥0.49, establish a genuine extra factor Z^(-ν) with ν>0 in the complete **weighted row-count/energy bound used by the current HIGH source**. Write its original selected slots, character family, masks, norms, cutoff, height, conductor, wave profile, amplitude-bin geometry and allowed dependence of constants. The gain must hold **uniformly over all legal row families and every required bin**, not merely at the optimizing numerical parameters. Then retain the unsaturated rows and all admissions. A proposed ν≈7.5e-5 is a numerical benchmark for beating the pending #79 model by about 1e-5, **not** an existing theorem or blanket guarantee.

The already-proved RH_Lean `vf919OAI_saturationTail_le_deficitLPM2` and the associated LPM2/UPM2 identities reduce a tail count to a moment **only after an independent actual-source moment saving**. They are not such a saving. Do not infer phase-independent sparsity from an arbitrary zero-target or a finite owner census.

Competing proper source inputs to test if the saturated-row gain is blocked:
1. Original marked inverse-moment cost μ=2: investigate a **source-valid** μ<2, e.g. 1.995, replacing `r+2z≤m-c₁`, while also re-proving the second marking/Poisson condition, natural/face counts, positive diagonal and every admission guard. Varying μ only inside the return model is invalid.
2. Sixth-power inverse-amplification α=5/6: a lower α requires an independently proved improvement to the actual amplifier/source geometry, not a free numeric change.
3. Sil's physical `GlobalSource (99999/100000) (93/25) (3/50)` and the repeated-mark source-step: strengthen the **actual quantified** source, then regenerate all downstream face families, slots, caps, guards and the full return.

**Hard source links:** tracker #76 `Source/ActualWeightedK.lean`, `FourthPower/RepairedRestrictedSource.lean`, `FourthPower/RepairedActualSideProvider.lean`, `FourthPower/MixedFirstCenteredSourceMoment.lean`, `Gain/Gain.lean`, `FinalReturn/ReturnFormulas.lean`, `FinalReturn/ReturnConstants.lean`. Full path prefix: `submissions/arvi-repeated-marks-on-sil-face-20261025/src/Submissions/arvi_repeated_marks_on_sil_face_20261025/`. Distinguish leader `UnitFaceSource` from original OAI `PositiveFineSourceInput`. [RH_Lean draft #1028](https://github.com/OVVO-Financial/RH_Lean/pull/1028) studies hard-face saturation, but its analytic source saving remains unproved and its branch is **not main**.

**Rejected false savings:** a t→t/2 reduction when t is a freely chosen o(1) loss (e.g. `source_batch_plain_marked_fine_sharper_signed_NNS`); raising the source budget B₀ above its legal maximum 1; simply replacing `‖A−B‖²≤2(‖A‖²+‖B‖²)` by the exact Gram identity without proving a source-dependent **power** in the nonzero-frequency row; assuming the zero-mode already proved diagonal grants additional savings.

## 3. Direct Co/Div / square-block lane (zeta-first)

Use the **genuine** signed Green–Kubo object, not Pearson correlation: `M(N)^2=D(N)+2C(N)` with squarefree diagonal D and complete strictly ordered original Möbius covariance C. A strict power saving κ>0 relative to tracker-derived zeta scale would require a new original-source estimate
```text
for every eps>0, exists A_eps,N0 such that for all N>=N0,
 D(N)+2*C(N) <= A_eps * N^(1.749215-kappa+eps).
```
This is the **output target**, **not** an admissible independent input/renamed lemma. Prove a new arithmetical estimate on a proper component that actually implies it.

Preferred proper source from merged [RH_Lean #982](https://github.com/OVVO-Financial/RH_Lean/pull/982), `research/SQUARE_SHELL_LONG_LAG_FIVE_SIXTHS_20261019.md`: for H dyadic, 0≤K≤H, square-shell increments Δ_r, and L=floor(H^ρ),
```text
S(H,K)^2 <= 32*H^3 + 32*H^3*L + 2*U(H,K,L)
U = the COMPLETE original-sign long-lag physical pair sum
    over H<=r<s<H+K, s-r>L, gcd(n,m)<=H,
    r^2<n<=(r+1)^2, s^2<m<=(s+1)^2.
```
The diagonal, near lags and gcd>H contribution are already independently paid in #982. **Do not pay them twice or delete the small-gcd g=1 mode.** A genuinely new arithmetic theorem `sup_{0≤K≤H} U(H,K,L)≪_ε H^(γ+ε)` with γ<3.49843 and 0<ρ<γ-3 gives the zeta/Mertens exponent
```text
beta_new <= max(3+rho, gamma)/4;
CoDiv residual exponent <= max(3+rho, gamma)/2;
weighted-covariance threshold <= max(3+rho, gamma)/4 - 1/2.
```
Example **conditional math only**: ρ=0.45 and γ=3.49803 give β_new≤0.8745075, a 0.0001 gain. Every partial K and the entire family of H must be covered; interpolate non-square endpoints using |μ|≤1. The source should exploit the exact g=gcd(n,m) split, (a,b)=1, gcd(g,ab)=1, true μ(g)^2μ(a)μ(b) sign, strict square-shell clipping, and genuine balanced prime/cofactor Type-II windows. The actual signed estimate on the coprime **unshared-factor** component is unproved. Prefix positivity has genuine counterexamples; universal negative far covariance is false.

**Scope warning:** A theorem on only these integer Möbius pairs improves the **Riemann zeta** zero-free boundary, not automatically all Dirichlet characters. A tracker-eligible all-Dirichlet improvement requires independently uniform character/conductor generalization and the verifier's exact challenge statement. Never label one as the other.

## 4. Loop / release gates

For every attempted estimate, the owning agent must supply a compact machine-readable or Markdown ledger row with:
- **Where:** exact original carrier, qualified theorem file/term, source SHAs, amplitude bin, cutoffs, conductor/character or gcd/square-run family.
- **Quantifiers:** the order of ∀ε, ∃C,J,Z₀ and ∀ admissible character/row/conductor/K/H; spell out allowable dependence on fixed smooth profiles and ambient data.
- **Expense:** previously certified exponent, independently proved new exponent (or `UNKNOWN`), source multiplicities, diagonal, exceptions, resonances, omitted sectors, physical masks and gates; complete quantitative *net* exponent ledger.
- **Sensitivity:** model-predicted Δβ; exact **certified** returned β or `NOT_PROVED`; next binding row/sector; ζ vs all-Dirichlet scope; implied 2β and β-1/2.
- **Proof/evidence:** original Lean declaration, axioms and warning-fatal CI on the exact head; or explicit `CONDITIONAL` / `FINITE_COMPUTATION` / `PAPER_PROOF_NEEDS_REVIEW`. One adversarial falsifier. No invented certification of hypothetical parameter reruns.

**Acceptance of a strict boundary gain:** an independently proved uniform analytic or arithmetic source inequality with no circular invocation of the desired global Mertens bound; all complementary source bills paid; complete original consumer leading to a rational β strictly better than the current relevant certified benchmark; and a verified source-level Lean certificate. A model-predicted Δβ is useful prioritization, **never** this acceptance.

**Status policy:** If there is no new uniform source theorem, report `NO_UNIFORM_SOURCE_GAIN` with the FIRST original-source failing estimate and the exact obstacle. Do not create a fresh coordinate identity, generic conditional interface, or duplicate bridge to simulate progress. The one-on-main zero-free source program coexists with independent VF-LOW/SAT/JOH, CORR4/FINITE-AC/MU-LIFT and NYMAN routes; do not reroute all seven agents to the same mathematical task.

**Governance:** One existing scheduled run per specialist/day, six report-only agents (their existing paths on `agent-reports`), Lean #7 limited draft proof branches, no direct main edits, no auto-merges. This file changes GitHub instructions **only** after human merge; it does not modify saved Studio settings or launch agents.

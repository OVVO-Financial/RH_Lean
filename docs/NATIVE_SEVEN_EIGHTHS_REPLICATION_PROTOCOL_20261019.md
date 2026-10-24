# Independent reproduction of the seven-eighths *mechanism* — proof authority and execution contract

> **2026-10-22 source-first execution update:** The user-directed **independent seven-eighths proof objective remains unchanged**, but the *first* unproved arrow is now specified by [the OAI compensated one-prime / signed NNS seam](OAI_COMPENSATED_ONE_PRIME_NNS_SEAM_20261022.md). #987 imports the original already-certified 7/8 proof; merged #1000–#1004 carry exact original source-algebra/type-checked Gaussian/NNS identities; draft #1005/#1006 isolate (A), multiplicity and sixth-moment/principal bills. On \(\tau_S=1\), ideal factorization provides only one prime/cofactor representation; original CentralSlots gives conditional \(720Q^{-51/100}\) local decay, which has **not** been lifted to the full globally normalized coefficient. Work on that bridge or its true source-admitted counterexample FIRST. Do not equate intermediate algebra with the independent analytic proof, import the terminal conclusion as a premise, or hide source assumptions in a character-isometry toy model. Older stage listings below are retained as the full eventual proof checklist.

**2026-10-19, historical high-level directive (still the independent end goal):** FULLY REPRODUCE THE MECHANISM THAT PROVES THE 7/8 ZERO-FREE LINE. Do not prioritize extrapolated 5/6, finite A/C, or RH-strength conditional gates until the new seven-eighths mechanism itself has been reconstructed and independently proved on a true arithmetic carrier. The original canonical \(\pi-VF_{\mathrm{can}}\) / von Koch target is unchanged; other historical attacks remain available but are secondary.

**Honest status:** This file is a research plan and source-verified dependency DAG, **not** an independent 7/8 theorem. The initial native Lean file \`research/NATIVE_SEVEN_EIGHTHS_LOCAL_COMPENSATION_20261019.lean\` records one exact local identity, but has **no standalone acceptance status**. The ONLY acceptable output is a kernel-checked full source-to-nonvanishing proof; no intermediate artifact is counted as achieving the user's objective. Real coefficient identification, nonprincipal phase extraction, error majorants, inverse/plain moments and final detector are all required.

## Precise upstream source and expected toolchains

- Manuscript (source fixed on examination): OpenAI, **The Quasi-Riemann Hypothesis**, 2026-09-30, \`openai/math/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex\` (blob \`268c4e3206d460c617d3d2129742a72b831b3def\`). See \`sec:compensation\`, \`sec:local-compensation\`, \`old-eq:5.13a\`, \`old-eq:5.13b\`, \`old-eq:5.13c\`, \`sec:inverse\`, \`sec:plain\`, \`sec:refined-row-counts\`, and \`sec:conclusion\`.
- Final external Lean export: \`openai/math/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean\`, proving \`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re\` and a statement for all Dirichlet characters. Main dependency \`OAI/NumberTheory/DirichletL/Detector/FinalAssemblyUnconditional.lean\`; proof depends on \`Energy.CertifiedExistence\`, \`Detector.FinalAssemblyCertifiedBands\`, \`Moments.DetectorPlainSlotProfile\`. Actual core theorem is \`SevenEighths.ProbeFinalAssemblyUnconditional.zeta_nonzero\`. Upstream uses Lean 4.34.1; its imported closure is thousands of modules.
- Separate **RH_Lean migration draft PR #983**, \`chore/lean-4.34.1-tracker-compat\`: as of current audit, 4.34.1 is ISOLATED in \`.github/lean434/\` and root defaults remain 4.24. Do NOT flip the root toolchain or import unbuilt OAI modules. Once the migration is independently green and merged, rebase and recheck native modules on 4.34.1.
- Importing the entire OAI theorem or quoting its \`7/8\` estimate as a hypothesis is **not** an independent RH_Lean reproduction. Rebuilding the upstream OAI closure is an essential provenance/environment check, but the native arithmetic-and-analytic dependency chain below must be proved without calling the upstream terminal zero-free theorem.

## The actual mathematical engine — why 7/8 appears

### Stage I: obtain the genuine 11/12 analytic detector, not a placeholder

- Construct the original theta/Poisson physical probe on completed cubic data \(cn^3\), \(c\) squarefree, and the sextic-ideal Hecke rows. The principal \(u=1\) contributes the Mellin pole; high nonprincipal \(u a^6\) rows require nontrivial cancellation.
- Build both bounds for the *same normalized probe*: low direct/reflected theta bound; high Poisson expansion with inverse polynomial zero detector and appropriate sextic large sieve. \(\theta=1-h/6+b/12\) with \(h=1/2,\ b=0\) gives \(11/12\). Nonzero principal signal and all excluded Euler masks are required.
- Neither a root-count equality nor a generic symmetric polynomial is the Stage I analytic estimate.

### Stage II: the COMPENSATING difference really changes the high coefficients

At each selected prime \(p\), on disjoint annular prime slots:
\[
\overline{\eta(p)} I_{\eta;p}(X,Y,Zq_p)
\;-\;q_p^{-3/2}I_\eta(X/q_p,Y/q_p,Z).
\]
The COMPLETE \((-1)^{|J|}\) finite subset expansion must preserve the same original physical slot weights, squarefree-product restrictions and zero-on-nonunit masks. No prior historical owner may be charged twice.

Let \(Q=q_p,\ A=\overline{\eta(p)}Q^x,\ Q_w=Q^{-w},\
U=\chi_p(u)^{-1},\ W=\chi_p(u)Q^{-w},\ D=\eta(p)\chi_p(u)^{-1}Q^{-x}\) when \(p\nmid u\). Then
\[
AD=U,\qquad UW=Q_w.
\]
The actual local Euler factors satisfy
\[
P_p=(1-V)^{-1}+\frac{W}{1-W}+P_p^*,
\qquad E_p=P_p^*+D,
\quad H_p=P_p\frac{(1-V)(1-W)}{1-D},
\]
and the compensated selected factor is
\[
G_p=\frac{(A-Q_w)(1-V)(1-W)P_p^*-Q_w(1-VW)}{1-D}.
\]
The exact source identity (paper 5.13b) is
\[
\boxed{
G_p+UH_p=
\frac{(1-V)(1-W)}{1-D}
\left[
(U-Q_w)\left(\frac{V}{1-V}-D\right)
+(A+U-Q_w)E_p
\right].
}
\]
Here the main \(-U\) is a **genuine inverse sextic-character phase**, not a standalone combinatorial minus sign. The right-hand numerator is an actual analytical ERROR object, not automatically small just because this equation holds. For \(p\mid u\), \(W=D=0\) and the source follows the distinct zero-extension branch; do not apply \(U=\chi_p(u)^{-1}\) there.

The native file proves this complex-algebra identity from honest local phase and Euler-series formulas *as explicitly named hypotheses*, paying all algebraic cancellations. Required next proof: derive those formulas for the genuine source from complete Euler factors; replace the abstract local hypotheses with native actual-prime/Hecke declarations. Then prove the global finite selected subset expansion and exact locally-to-globally corrected high representation.

### Stage III: pay the nonprincipal rows analytically

This is the decisive NONTAUTOLOGICAL work, not an optional follow-up:

1. **Inverse selected-slot second moment** for an actual ideal-Möbius inverse polynomial with true sextic-character phases and exactly disjoint slots.
2. **Ordinary/plain refined fourth moment** for the matched nonprincipal character rows, including primitive inducing-character exclusions and the centered same-product rectangle where its volume term truly cancels.
3. Two finite Poisson/Cauchy reductions, sixth-power-free-to-\(ua^6\) amplification and large-sieve counting by actual slot amplitude. Keep exceptional rows, principal \(u=1\), local \(p\mid u\) zero masks, all off-diagonal and different-owner terms.
4. Uniformity in all required heights, row bins, conductor/ray classes, and moving prime slots. No finite-root correlation, imported OAI final estimate, constant-width numerical fit, or \(\mu\)-randomness premise is admissible.

The Stage II exponent parameters are
\[
h=13/16,\qquad b=1/8,\qquad \ell=1/6,\qquad
\ell_x=17/48,\quad\ell_y=23/48,\quad
\ell_x+\ell_y=5/6,\quad 5/6+\ell=1,
\]
and
\[
\theta=1-\frac h6+\frac b{12}=\frac78,\qquad
C_{\rm II}(s)=s-\frac{11}{16},\quad C_{\rm II}(7/8)=3/16.
\]
These rational equalities by themselves DO NOT establish the moment margins or the continuation. The external method has a limiting \(2\beta_*-1\ge3/4\) parameter and contour hypotheses tied to \(7/8\); simply replacing \(7/8\) with \(5/6\) invalidates those dependencies.

### Stage IV: finish a fully native endpoint certificate

Prove the two comparison bounds for the *same compensated probe*, nonzero principal Euler scalar, holomorphic correction at the detector points and polynomial-growth strip estimates. Recover \(\zeta(s)\ne0\) on \(\Re s>7/8\), and ideally all Dirichlet L-functions there, from actual native proof terms **not** the external zero-free theorem as a hypothesis. Print all proof axioms. On eventual Lean 4.34.1, compare the native declaration with the challenge/tracker statements using a kernel/comparator check.

Only after this completed 7/8 baseline should the team spend primary effort on moving to 5/6 via a new reflected LOW-side saving / admissible geometry AND the correct high-row moment improvement. Having one intact baseline often exposes opportunities but **does not logically force** a stronger exponent.

## Interface to existing RH_Lean work, without source conflation

- \`S=A-T\`: true signed Möbius root-smooth/prime transport and the existing \`#915\` VF masked original source; good candidates for a SECOND independently quantified compensation law, **not** automatically OAI's Hecke coefficients.
- \`#919\` Hecke map and owner-two native Gram: structural start for actual sextic/ideal character source; its \(\chi_{-3}\) selector is **not** the required variable sextic high-row phase. Do not claim that the principal coefficient map supplies the large sieve.
- \`#982\` trapezoid/endpoints/owner orientation/317-1027 scans: useful source experiments and falsifiers only. The signed long-lag \(5/6\) gate is not a stage of the established OAI proof.
- \`#983\` isolated compiler upgrade: necessary for eventual theorem comparators and OAI dependency mapping, not itself a result.

## Division of actual proof work for the seven research roles

| Role | One new deliverable that must be independently tested |
|---|---|
| Coordinator | Exact dependency graph from actual upstream paper equations / proof-theorem imports to native RH_Lean declarations; no stage skipped |
| Owner Payment | Occurrence-faithful compensation, exact \(p\mid u\) zero-mask and two-term/no-double-use historical source audit |
| Analytic Type II | Native proof of one genuine character-twisted inverse/plain moment estimate *with the precise region and quantifiers* |
| Finite Wheel | Real ideal/prime/coprimality & sextic phase map, not simply \(\chi_{-3}\) or fitted density |
| Prime Census | Compare compensated actual coefficients and all signed/error slots to independently enumerated real prime and ideal examples, including R=317/1027 and adverse K-prefixes |
| Adversarial Referee | Countercheck marked-minus-rescaled phase, local error rates, principal normalizer, exceptional rows, hidden imported estimates and honest 11/12-to-7/8 acceptance |
| Lean Verification | Native kernel-checked local identity, complete subset formula, genuine local Euler factors, moment lemmas, final end-to-end certificate; warning-fatal & no sorry/custom axioms |

Every agent must read BOTH current and previous calendar day's research reports on its next authorized run, and retain the one-run-per-day usage cap. A GitHub PR or AGENTS.md edit **does not** update saved Agent Studio configuration or trigger the agents.

## ONE acceptance condition: the entire proof, end to end

**COMPLETE** means the fully native source-to-theorem closure reproduces BOTH stages and yields a kernel-verified statement of zero-freeness for \(\Re s>7/8\), with no unproved Mertens hypothesis, no reliance on \`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re\` as a premise, no \`sorry\` or custom axioms, complete actual-phase/error/moment/exceptional-row bounds, warning-fatal compilation and all-original-sources numerical/mask checks. Prefer all Dirichlet characters as upstream proves. Until every part exists in that same proof dependency chain, the project must report only **INCOMPLETE; NO INDEPENDENT 7/8 PROOF**.

The new workflow \`.github/workflows/full-seven-eighths-proof-replay.yml\` replays the WHOLE upstream OpenAI proof at pinned commit \`1581d4cbdd69a0faf34b2089614fe2a814316a6a\` under Lean 4.34.1, compiling \`OAI.NumberTheory.DirichletL.Nonvanishing\`, rechecking both terminal theorem types and their Lean axioms. Its success is *complete external-source replay* and provides a dependable reference while porting, **not** an independent RH_Lean derivation. That distinction remains mandatory even after the replay is green.

Intermediate source files, experimental root tables, scripts and exact local lemmas are implementation artifacts **only**. Do not celebrate, mark complete, or present them to the user as proof milestones. The true deliverable is the entire independently reconstructed mechanism and terminal theorem; if unavailable, clearly report the blocker and refrain from claims of a 7/8 replication.


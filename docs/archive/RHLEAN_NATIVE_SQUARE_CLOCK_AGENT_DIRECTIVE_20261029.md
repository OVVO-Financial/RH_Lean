# RH_Lean seven-agent arithmetic-first attack: square-clock, shared-GCD, complete signed source

**2026-10-29. User-directed priority proposal. Active only after human merge to main. Not a new theorem, scheduled run, or permission change.**

## 0. Objective: make RH_Lean's representation produce a NEW inequality

Stop making additional zeta-zero, Mellin, LOW/HIGH, NNS realification, or von Koch equivalences the principal deliverable. Those are already useful **consumers and coordinates**, especially merged #1052, not the independent saving. Use the original, signed square-block / prime-factor-owner arithmetic and aim first for a genuine fixed exponent improvement beyond the imported OAI 7/8 benchmark.

**Precise sufficient goal:** for a fixed \(\eta>0\), for every \(\varepsilon>0\) and every sufficiently large integer \(H\),
\[
\mathcal E_\Delta(H)=\sum_{H\le R<2H}|\Delta_R|^2\ll_{\eta,\varepsilon}H^{5/2-\eta+\varepsilon},
\quad \Delta_R=\sum_{R^2\le n<(R+1)^2}\mu(n).
\]
Together with exact square-to-all-integer interpolation, dyadic Cauchy–Schwarz gives \(M(x)=O_{\eta,\varepsilon}(x^{7/8-\eta/4+\varepsilon})\). **Not proved.** Do not inflate a partial source bound into this target. Preserve other independent routes (direct pi-VF_can/first-owner, CORR4, FINITE-AC, MU-LIFT, JOH/SAT, NYMAN); they are not canceled.

## 1. Attack the exact original Euler fractional source

The source declaration is research/EULER_FRACTIONAL_COUPLED_20261027.lean : eulerFractionOffQ. Write \(X_R=R^2-1\) and for \(d\ge2\)
\[
f_d(R)=\frac{X_R\bmod d}{d},\quad
m_d=\frac1d\sum_{r=0}^{d-1} f_d(r),\quad F_d(R)=f_d(R)-m_d.
\]
The original symmetric strict off-diagonal source (with no modified coefficients) is
\[
U_R=2\sum_{1\le a<b<R}\mu(a)\mu(b)f_{ab}(R).
\]
For \(d\le Q<R\), where \(d=s^2t\), \(s,t\) squarefree, coprime and \(t>1\), genuine nonzero terms group with \(\alpha_d=\mu(t)2^{\omega(t)-1}\), and \(\alpha_d=0\) otherwise. The EXACT low-product source is
\[
U_R^{\le Q}=2\sum_{2\le d\le Q}\alpha_df_d(R)
=\underbrace{2\sum_{2\le d\le Q}\alpha_dF_d(R)}_{L_Q(R)}
+\underbrace{2\sum_{2\le d\le Q}\alpha_dm_d}_{P_Q}.
\]
The high-product complement uses the actual moving cutoff \(1\le a<b<R\):
\[
U_R=L_Q(R)+P_Q+U_R^{>Q}\qquad(Q<R).
\]
**Do not erase \(P_Q\) by centering.** Do not bound the low energy and forget \(\langle L_Q,U^{>Q}\rangle\), \(\langle P_Q,U^{>Q}\rangle\), diagonal, continuous reciprocal square or other original floor-bilinear terms. The original source is EXACTLY continuous reciprocal square minus (fractional diagonal plus twice off-diagonal). A sharp shell \(\Delta_R\) requires its actual moving boundaries and full transfer; its source is not interchangeable with an arbitrary smooth OAI Hecke probe.

## 2. Evidence the seven agents must use

**MERGED Lean sources:** PR #1051 supplies exact coprime centered square-clock CRT/ZMod lemmas. PR #1052 supplies LOW analytic sparsity, HIGH pole-order transport, exact theta/VF and realification formulas; these latter identities do not yield signed cancellation. #987 imports the OAI unconditional 7/8 benchmark, not an independent native reproduction.

**PAPER PROOF ACCEPTED WITH SCOPE, NOT YET LEAN-FORMALIZED:** 2026-10-29 Analytic claim 20261029-analytic-1 and Lean review 20261029-lean-1 give
\[
\sum_{H\le R<2H}|L_Q(R)|^2
\ll_\varepsilon H Q^{1+\varepsilon}+Q^{4+\varepsilon},
\quad2\le Q<H.
\]
This covers all cubefree product moduli, including shared primes. It uses quadratic Gauss sums and nonzero shared Fourier frequencies: 
\[
|\widehat F_d(h)|\le\frac{(1+\log d)\sigma_{-1/2}(d)}{\sqrt d},\qquad
|\langle F_d,F_e\rangle_{\rm complete}|
\le\gcd(d,e)\,A(d)A(e).
\]
In the range \(Q^3\le H\) this is \(O_\varepsilon(HQ^{1+\varepsilon})\), saving roughly one \(Q\) in squared energy against the triangle bound on this **centered subsector**. Referee must independently audit the even-modulus/Gauss details and \(\varepsilon\) constants before Lean promotion. It does NOT improve Mertens 7/8.

**PRINCIPAL AND MIXED OBSTRUCTIONS:** 20261029-wheel-1 proves at paper level the negative coherent principal first-prime mode and complete-orbit centered variance floor. 20261029-census-1 finds true composite/shared-factor compensation and reversals at moduli 6, 10, 12. 20261029-referee-2 constructs an infinite primorial-period obstruction to applying the centered \(O(HQ)\) bound to the UNcentered row. Do not say the principal signal is small or that shared-factor columns decorrelate like independent primes.

**Original source bridge:** research/OAI_PAIRED_SHARP_EULER_SQUARE_LOCALIZATION_20261028.lean certifies sharp source and moving prime-population identities where stated; a complete OAI smooth-to-sharp signed moment transfer is still OPEN.

## 3. Prioritized mathematical steps

A. Formalize and independently audit the complete low-product shared-GCD paper moment: the cubefree \(\alpha_d\) coefficient, genuine \(Q<R\) factor-pair admission, finite Fourier quadratic Gauss bound including powers of 2, shared frequencies, finite incomplete-period residue, quantified \(H,Q,\varepsilon\).

B. **Break the long-period barrier.** The current loss \(Q^4\) confines the clean range to \(Q^3\le H\). Test a source-faithful incomplete quadratic-correlation inequality when \(H<\operatorname{lcm}(d,e)\), preserving shared gcd, 2-adic exceptions, principal modes and resonances. Improving the aggregate \(Q^4\) cost toward \(Q^3\operatorname{polylog}Q\), with useful \(Q\) toward \(H^{1/2}\), is only a **falsifiable candidate**, not an established bound. Prove it or find a legal coherent counterexample.

C. **Pay the original complete source.** Reinsert \(P_Q\), \(U^{>Q}\), the low/high mixed terms, diagonal, reciprocal square and full sharp-shell transport. A saving isolated in centered \(L_Q\) is not a Mertens exponent gain. Identify the first physically irreversible triangle/Cauchy step and improve it with actual owner arithmetic, not assumed stochastic independence.

## 4. Role assignments (one distinct obligation each)

**#1 Research Coordinator / Proof Architect:** Maintain one same-source ledger from \(\alpha_d,L_Q,P_Q,U^{>Q}\) to complete fractional/floor source, and separately to \(\Delta_R\). Track certified/paper/falsified/open, original and new \(H,Q\) powers, required \(\eta\), current SHA/PR/CI, first missing arithmetic lemma and one adverse example. Allocate different sub-bills; no seven-agent repetition of NNS/zeta identities. Keep the ten-route DAG and avoid marking paper results PROVED.

**#2 Owner Payment / Signed Arithmetic:** Own the **principal, high-product, and mixed** bills. Derive source-exact \(\alpha_d\) ancestry including \(s>1\), repeated-prime gcd, squareful-zero masks, first-owner historical returns and moving \(a<b<R\). Quantify composite compensation of the coherent negative prime principal mode; produce one new signed cross-sector estimate or a falsifier, retaining the original reciprocal/diagonal terms. No one-prime-only claim as full source payment.

**#3 Analytic Type II:** Independently verify/repair 20261029-analytic-1. Then attack genuine incomplete quadratic phases for \(H<\operatorname{lcm}(d,e)\), by Fourier completion, Weyl/van der Corput, admissible Type II bilinear estimates or better source-faithful arguments. Bound all gcd, parity/2-adic, conductor, principal and resonance costs with explicit \((H,Q,d,e)\) hypotheses. Demand a net source gain, not an assumed \(\sqrt{de}\log^3(de)\) cancellation.

**#4 Finite Wheel & Incidence:** Verify the exact cubefree unordered-factor multiplicity and \(\mu(a)\mu(b)\) signs; test common-prime/2-adic Gauss congruences, CRT-period logic and extremal lcm families. Supply an exact finite combinatorial lemma and a coherent counterexample family for analytic testing. Distinguish integer-prime tags from OAI Hecke ideal phases.

**#5 Prime Census Laboratory:** Exact integer/rational square-clock census of \(f_d,m_d,\alpha_d,F_d\) and centered/un-centered energies. Reproduce compensation sign reversals at \(d=6,10,12\), include held-out \(Q^3\gtrless H\), \(R=317,1027\) when feasible, and near-resonant incomplete-period packets. Measure principal \(\langle P_Q,L_Q\rangle\) and mixed \(\langle L_Q,U^{>Q}\rangle\) with full physical cutoffs; deliver scripts, source SHA and counterexamples, not asymptotic conclusions from finite fits.

**#6 Adversarial Referee:** Independently audit shared-GCD Fourier/Gauss bounds (especially even moduli), all epsilon losses, the primorial uncentered counterexample and alpha grouping. Attack proposed incomplete \(\sqrt{de}\) packet bounds with coherent/adjacent moduli and shared frequencies. Reject RH-equivalent circular premises, unproved source masks and incomplete mixed/diagonal bills. Report ACCEPT_WITH_SCOPE, COUNTEREXAMPLE or UNPAID with a mathematical witness.

**#7 Lean Verification:** With #1051/#1052 now merged, reuse current main declarations and formalize **only** referee-accepted independently useful source lemmas: original \(\alpha_d\) grouping; finite shared-frequency GCD covariance; incomplete-window correction; and the full quantified low-conductor moment. Warning-fatal Lean 4.34.1 import closure, no sorry or project axioms, #print axioms, exact source regression; only the pre-authorized scoped draft proof PR and Actions verification. No unconditional analytic saving or merge without a true kernel theorem.

## 5. Reporting and guardrails

Every authorized run fetches **current main** AGENTS, CURRENT_PROOF_CONTRACT, this directive, source declarations, current PR status, today's/yesterday's actually committed handoffs on agent-reports (including 2026-10-29 Analytic/Wheel/Census/Referee/Lean), with source/blob SHA. A proposed directive is not active main until HUMAN MERGE. Preserve Coordinator's two identical mirror files and the existing staged report order.

Required report: physical source with \(\mu\), cutoffs, signs and weights; exact claim/status; original and improved \(H,Q,\eta\) exponents; full principal/high/mixed/diagonal/reciprocal/boundary bills; adversarial witness; downstream sharp-shell theorem and its still-open premise; next smallest independent lemma; actual commit/readback or NOT_PUBLISHED. Report NO_NEW_INDEPENDENT_INEQUALITY when warranted.

**No governance changes:** one existing scheduled run per agent/day; no new tasks/schedules, no direct-main commits or auto-merges, six own-report-only specialists, existing scoped Lean proof branch, current report paths, and human-only main merges. Repository instructions do not change saved ChatGPT Agent Studio prompts; the user/Studio owner must separately synchronize any saved prompt that does not already dynamically load current main. Historical daily reports must not be edited.

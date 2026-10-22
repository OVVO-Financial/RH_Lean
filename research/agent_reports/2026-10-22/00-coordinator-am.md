# RH_Lean Coordinator synthesis - 2026-10-22

**Status:** COMPLETED  
**Run:** 2026-10-22T19:09:00-04:00 scheduled invocation  
**Final audit:** 2026-10-22T19:15:09-04:00  
**Mirrors:** identical bytes at 00-coordinator-am.md and 90-coordinator-pm.md; these are compatibility paths, not two executions  
**Canonical objective:** VFCanonicalSquareVonKochStatement remains OPEN  
**Campaign status:** INCOMPLETE; NO INDEPENDENT 7/8 PROOF  
**Evidence classes:** PROVED_IN_LEAN_ON_MAIN, PROVED_IN_LEAN_ON_PR_HEAD, PAPER_PROOF, IDENTITY_ONLY, FINITE_COMPUTATION, CONDITIONAL, REFUTED, PENDING

## A. What changed mathematically?

The strongest new mechanism is a phase-stratified reduction of the exact original one-prime residual. On a dyadic source-admitted good-prime-ideal band, the exact D-tier has one genuinely difficult order-three head,

    - eta(P) * conjugate(v_P(u))^2 * Q_P^(-x),

while its conjugate-sextic head, principal head, rational tail, BR tier and BKV tier are absolutely payable after genuine prime-ideal counting. This isolates a direct cubic large-sieve problem instead of feeding the entire local residue into an undifferentiated sixth-moment hypothesis.

**Claim 20261022-coordinator-1 (uniform cubic-head reduction; PAPER_PROOF / SOURCE-ADMISSION CONDITIONAL).** Let P>=4 and S be distinct source-admitted good prime ideals with P<=Q_P<2P and

    #S <= C0 P / log P.

Assume the literal original central-contour hypotheses 7/8<=a, 0<e<=1/1000, a+6e<=1, Re(x)=a+16e, Re(w)=1-a-6e, Re(z)=17/50, and all hypotheses needed for the exact three-tier split and its displayed full-tier bounds. If r_P(u) is the exact recombined one-prime residual, then

    sum_(P in S) r_P(u)
      = - sum_(P in S) eta(P) conjugate(v_P(u))^2 Q_P^(-x) + Err(u)

and, uniformly in u,a,e,

    |Err(u)| <= C0/log(P) *
      [3 + 12 P^(-26/25) + 8 P^(-3/4)
         + 120 P^(-283/200) + 24 P^(-1/25)].

In particular |Err(u)|<=167 C0/log P. The key point is uniformity down to e=0: the two secondary heads have sizes at most 2Q^(-1) and Q^(-1), because Re(x+w)=1+10e and Re(x+2w)=2-a+4e>=1+10e. The exact remaining tail is bounded by 12Q^(-51/25)+8Q^(-7/4), while the full BR and BKV tiers contribute 120Q^(-483/200) and 24Q^(-26/25). Multiplying by #S gives the displayed powers.

This is mathematically different from claim (A). It does not provide a pointwise bound for every grouped effective ideal, and it does not use cancellation among multiple factorizations. It instead proposes a direct weighted-L2 attack on the one-prime source after all noncubic pieces have been paid.

**Claim 20261022-coordinator-2 (free cubic-dual sixth moment and inverse diagnostic; PAPER_PROOF).** For a finite prime-label set S and coefficients a_P, average independently over the complete cubic torus mu_3^S. Put

    S2=sum_P |a_P|^2,   S3=sum_P |a_P|^3.

Then

    E |sum_P a_P chi_P|^6 <= 6 S2^3 + S3^2.

Proof: in the sixfold expansion, cubic orthogonality requires each positive-minus-negative local multiplicity to be 0 or plus/minus 3. The zero case is equality of the two triple multisets and costs at most six negative orderings per positive ordered triple, hence 6S2^3. Every nonzero case is a pure cube at one prime against a pure cube at another, whose total absolute contribution is at most S3^2.

For an actual normalized weighted row family, let K3 be its ordered-triple Gram and P3 the complete cubic resonance projector. If ||K3-P3||op<=delta, then for the same coefficient vector

    M6_actual <= (6+delta) S2^3 + S3^2.

Thus failure of the desired one-prime sixth-moment rate forces a large restricted triple-Gram defect after the already-payable pure-cube resonances are removed. With #S<=C0 P/log P and |a_P|<=A P^(-7/8), the complete cubic sixth-root scale is O(A P^(-3/8)(log P)^(-1/2)); the pure-cube term is smaller, O(A P^(-13/24)(log P)^(-1/3)). This is an exact reference theorem, not a claim that the original incomplete OAI row family is complete or has bounded delta.

The literature bridge is real but not yet source-instantiated. Alexandre de Faveri, [Optimal large sieve for fixed order characters](https://arxiv.org/abs/2610.04045), Theorem 1.1, treats fixed n-th order Hecke families over a number field containing the n-th roots of unity and n-th-power-free ideals away from a fixed bad set. Its operator bound has the four scales A+B+A^(1-1/n)B^(2/n)+A^(2/n)B^(1-1/n), up to (AB)^epsilon. PR #1008 correctly separates n=3 for the cubic head and n=6 for the primitive sextic head. The missing bridge is exact identification of original OAI FreeRow elements, masks, units, bad primes, physical weights and row spread with that fixed family; analogy is not acceptance.

## B. Current proof objective and source authority

Final live authority is main@bd283dc4c8d8c6b0dc93bf06779aafde5d7368cd. Authoritative blobs are:

- AGENTS.md a5c1f409bd5a5ac92b7a9297b2d1328b6788c744.
- CURRENT_PROOF_CONTRACT.md 37fa0c327886643653d6d07517621d9e7a2e1e3d.
- OAI compensated one-prime/NNS seam 45b46929d33af6449f61fdec2428fa9b122056ed.
- External handoffs 038018145c0fddb2f6306c0712373adf9cd1ea52.

The unchanged public objective is

    exists C>=0, forall R>=2,
      |pi(R^2)-vfMidFinishedMass(R)-sqrt(2)| <= C R log R.

The current first quantitative arrow is still: transport the original recombined good-central local saving into the actual normalized post-compensation coefficient claim (A), or falsify (A) on a genuine source coefficient. Then separately pay true ell^(6/5) multiplicity, the actual incomplete-family moment, principal normalization and the full signed NNS cross energy.

### Formal-authority correction

The live contract says #1000-#1004 are merged source bridges. GitHub marks all five PRs merged, but exact ancestry and tree inspection show a stacked-merge integration defect:

- #1000 merge 7182239320f6858625aa7ca1a5d108e816cb3b3c is on main.
- #1001-#1004 merge commits 41caa8b, 044f221, 700eaea and 40ff2f6 are on stacked feature histories and are not ancestors of main; comparison with current main is DIVERGED with merge base 9edc4ad3.
- research/oai_434/VF919OriginalGaussianIntegratedNNS.lean and research/VF_919_OAI_GAUSSIAN_SUBSET_EXACT_COEFFICIENT_NNS_20261021.lean return 404 on current main.
- Therefore #1003/#1004 declarations, including originalOAI_gaussian_normalized_NNS_full_weighted_moment, are PROVED_IN_LEAN_ON_PR_HEAD at e9bed435..., not PROVED_IN_LEAN_ON_MAIN.

This is not a mathematical refutation, but it changes formal evidence status and the import base of #1005-#1008. A human-approved integration PR or equivalent main-ancestry repair is required. The central contract/AGENTS claim should then be amended; this Coordinator is not authorized to edit them.

## C. Competing mechanism portfolio

### 1. Full grouped coefficient route (A + tau + sixth moment) - CONTINUE

Concept: transport the exact recombined local source to every normalized grouped effective-ideal coefficient, prove the true tau ell^(6/5) budget, then use the post-grouped dual sixth moment and principal/cross payment.

Independent input: source-specific local-to-global normalization, genuine multiplicity geometry, and actual incomplete-family operator bound.

First missing theorem: a fully typed equality/inequality from original selected prime/cofactor/Gaussian columns to b(m), including D_cond^(-1/2)Z^(-sigma), unmatched faces, noncentral contours and the principal column.

Obstruction: the local Q^(-7/8) theorem alone does not pay cofactor multiplicity, normalization or coherent cross-prime energy. Claim (A) may also be stronger than necessary.

Disposition: continue as the contract's direct route.

### 2. Phase-stratified direct large-sieve energy - PROMOTE as strongest competitor within the Oct. 22 seam

Concept: use Claim 20261022-coordinator-1 to pay every noncubic local tier absolutely, then apply n=3 and n=6 fixed-order large-sieve estimates directly to the actual weighted source energy. This can bypass a global pointwise claim (A) and a generic sixth-moment detour on the one-prime sector.

Independent input: exact original-family adapters to de Faveri's fixed character families, plus physical-weight spread and source reindexing.

Target implication: a true one-prime nonprincipal energy saving, followed by the already separate principal and cross-term budgets. It is not yet the complete Gaussian detector.

First missing theorem: original FreeRow/selected-prime character and weight intertwining with all unit, mask, conductor and bad-prime data, and a bound on U*rho_max/W. PR #1008 has finite ideal/cube-root infrastructure but not this analytic instantiation.

Falsifier: one legal row whose character is outside the fixed family, one omitted zero mask or unit slice, or unbounded physical weight concentration.

Disposition: promote; it imports genuinely new quantitative mathematics instead of renaming the target.

### 3. Original VF #915 nonlocal owner compensation - RETAIN secondary, currently suspended

This remains a distinct physical carrier and could bypass OAI entirely, but no new non-target-equivalent full signed owner estimate appeared today. Prior diagonal/local sign mechanisms are defeated after offdiagonal restoration. Resume only with a complete original-weight signed theorem or a new independently testable inverse statement.

## D. Conceptual research and no-circularity review

Claim 20261022-coordinator-1 uses exact source algebra from #1008 head c596281...: VF919OriginalOnePrimePowerGain.lean blob 661063d..., three-tier native blob 83ad0b0..., and the paper full-tier constants in OAI_THREE_TIER_CODIV_RATE_SOURCE_AUDIT_20261022.md blob 45b935d.... These are draft-head materials pending mixed-source CI and main integration. The deduction itself assumes a genuine prime-ideal count and source admission visibly; it does not call hHigh, SourceMomentsAt, claim (A), the desired NNS inequality or a terminal 7/8 theorem.

Claim 20261022-coordinator-2 is finite harmonic analysis. Its restricted-family premise delta is not asserted. It explains exactly what a sixth-moment failure forces and separates the unavoidable pure-cube resonance from the genuinely nonorthogonal row defect.

The direct large-sieve route passes no-narrowing: de Faveri's theorem is independent of the repository target, has explicit family hypotheses and known nonorthogonal terms, and supplies quantitative information not contained in Co-Div identities. Applicability remains CONDITIONAL until the original-source adapter is complete.

## E. Specialist findings and continuity

Today Owner Payment and Analytic Type II reports are absent: TODAY=PENDING. No execution is inferred.

Today's completed reports were written before the Oct. 22 routing merge, but their durable results remain valid:

- Wheel blob 67d6d669...: 20261022-wheel-1, PAPER_PROOF. Literal subset ideal products are injective; quotient aliases have exact parity phase. No analytic saving.
- Census blob e1c4ae90...: 20261022-census-1, FINITE_COMPUTATION / REFUTED. Genuine Eisenstein quotient fibers realize both coefficient-energy contraction and expansion.
- Referee blob 2755d24d...: 20261022-referee-1, PAPER_PROOF. Any nonidentity normalized Hermitian character Gram has an indefinite defect; source-agnostic incidence cannot force a sign.
- Lean blob 548be1bb...: 20261022-lean-1 was green at #1004 head e9bed435 with standard axioms only. Its status is now corrected to PROVED_IN_LEAN_ON_PR_HEAD / STRUCTURAL-CONDITIONAL because that file is absent from main.

All available Oct. 21 Coordinator, Owner, Analytic, Census, Referee and Lean reports were read; Oct. 21 Wheel is missing. Their surviving claims are carry-forward only. The external inbox has no handoff newer than Oct. 18; those programs are historical/secondary selectors under current main.

## F. Mathematical bottlenecks

1. Repair the stacked source history so #1001-#1004 declarations actually exist on main, without weakening their proofs.
2. Prove the exact original source map from supported selected primes and FreeRow elements to the three phase-stratified heads, including Gaussian/Mellin integration and the row-independent complex normer.
3. Instantiate the fixed n=3 and n=6 Hecke character families, bad-prime sets, unit normalizations and masks from de Faveri's theorem.
4. Prove the actual physical weight-spread bound U*rho_max/W, or retain its precise loss.
5. Complete the effective-ideal multiplicity bound with repeated labels and split/inert/ramified cases.
6. Pay noncentral/negative-Re(w), exceptional, ramified and unmatched sectors.
7. Transport the principal inverse-Mellin estimate into the full row-weighted E_R and combine via squared constants c_R+c_H<=1.
8. Reassemble LOW/HIGH detector geometry without importing hHigh or the terminal OAI conclusion.

## G. Strategy decisions

- Preserve the direct claim-(A) route, but do not let it monopolize the seam.
- Promote phase-stratified fixed-order large sieve as the highest-value independent mechanism.
- Treat the complete cubic-dual sixth-moment theorem as a reference/inverse diagnostic, not source closure.
- Reject alias abundance, positive semidefiniteness, complete orbit cancellation and local diagonal decay as standalone signed NNS payments.
- Correct all #1001-#1004 formal labels until actual main ancestry is repaired.
- Do not merge, retarget, rerun or modify proof branches through the Coordinator role.

## H. Next specialist assignments

**Owner Payment.** Prove one exact original-source theorem that reindexes a legal good-prime dyadic band into cubic, primitive-sextic, principal and tail columns with the true Gaussian/Mellin coefficient, normer, masks and once-only labels. Reuse the #1008 three-harmonic identity. Falsifier: any missing W=vQ^(-w), duplicated split ideal, omitted unmatched face or row-dependent factor treated as constant.

**Analytic Type II.** Instantiate de Faveri Theorem 1.1 separately for the n=3 cubic and n=6 sextic heads. State K,S, power-free ranges A,B, coefficient L2 norms, epsilon loss and U*rho_max/W. Derive the final source energy exponent. Falsifier: family mismatch, conductor-dependent implied constant, or use of a squarefree theorem on sixth-free rows without the proved fiber decomposition.

**Finite Wheel & Incidence.** Finish the actual FreeRow element/ideal decomposition into power-free remainder and cube/sixth-power factors, including units, primes above 2 and 3, split/inert/ramified ideals and repeated labels. Separately certify the tau cap on the complete effective carrier. Falsifier: two element representatives counted as distinct ideals or a repeated slot escaping the valuation cap.

**Prime Census.** Do not enlarge the alias table. Extract the smallest legal original good-prime band and compute, coefficientwise, the exact full residual, cubic head and error; measure U*rho_max/W and independently reconstruct the character-family labels. Reject on the first mismatch or error exceeding Claim 20261022-coordinator-1's bound.

**Adversarial Referee.** Audit Claims 20261022-coordinator-1/-2, especially the 3+12+8+120+24 constants, dyadic prime count, cubic collision classification and operator-norm transfer. Independently check de Faveri n=3/n=6 hypotheses against OAI. Also review the #1001-#1004 ancestry correction.

**Lean Verification.** First report the stacked-main integration defect and await human direction. After independent paper acceptance, the smallest valuable new formal theorem is the complete cubic-dual sixth-moment inequality plus restricted triple-Gram transfer, or the exact original source adapter needed by de Faveri. Do not create a filler PR or encode the analytic family match as an axiom.

## I. Lean and PR status

- main remains bd283dc4...; only #1000 of the #1000-#1004 stack is actually in its ancestry.
- #1005 is open draft at 0091470e1d49d11027c8956ccae48d4d7f802174, based on the #1004 feature branch. At final audit: Documentation, Public export and Proof inventory succeeded; five material workflows were still in progress.
- #1006 is open draft at 905f21641f906a3fd01585590d5d22bb0aaec43c, stacked on #1005. All seven observed exact-head workflows succeeded. This certifies its conditional native content only and does not put it on main.
- #1008 is open draft at c59628159730f38ce8f8a5aa40cf931e2cff76e2, stacked on #1006. Documentation, Public export, Proof inventory, Lean source audits and Targeted Lean succeeded; the square-block workflow was in progress and the two mixed original/native jobs were pending.
- #1008 source blobs used here: OriginalOnePrimePowerGain 661063d..., native three-tier 83ad0b0..., OriginalCubeFreeIdealAdapter ad63c50..., and adapter audit feed5810....
- No workflow was rerun, no PR was reviewed/retargeted/merged, and no main source, central contract, schedule or permission was changed.

## J. Next-run resume capsule

Authority: main@bd283dc4c8d8c6b0dc93bf06779aafde5d7368cd; contract 37fa0c3...; seam 45b4692...; agent-reports began this run at 8a497184....

New claims: 20261022-coordinator-1, uniform cubic-head reduction with explicit O(1/log P) whole-band remainder; 20261022-coordinator-2, complete cubic-dual sixth-moment bound and restricted triple-Gram inverse diagnostic.

Highest-value next task: verify the actual original OAI character/weight adapter needed to apply de Faveri's n=3 and n=6 large sieve, including U*rho_max/W. Decisive blocker: #1001-#1004 are absent from current main despite merged badges and contract prose.

Publication history preserved: IN_PROGRESS primary commit 8f6a0f46877224299299e9197bb2ae13b5f86384 and mirror commit 931e26006a520b0d4730f3ab07a65ed1af322ab0. Final completed readback must verify identical blobs.

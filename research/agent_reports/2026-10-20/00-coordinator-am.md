# RH_Lean Coordinator synthesis - 2026-10-20

**Status:** COMPLETED
**Run:** 2026-10-20T19:09:04-04:00, one scheduled invocation
**Mirrors:** this synthesis is published with identical bytes at 00-coordinator-am.md and 90-coordinator-pm.md; these are compatibility paths, not two executions
**Canonical objective:** VFCanonicalSquareVonKochStatement remains OPEN
**Campaign status:** INCOMPLETE; NO INDEPENDENT 7/8 PROOF
**Evidence classes:** PAPER_PROOF, PROVED_IN_LEAN_ON_MAIN, FINITE_COMPUTATION, CONDITIONAL_BRIDGE, IMPORTED_INTERMEDIATE_ASSEMBLY, REFUTED, NO_NEW_GLOBAL_BOUND

## A. What changed mathematically?

Pointwise contraction of a complete four-label sextic fiber is dead, but the corresponding complete-residue moment has an exact nontrivial law.

Today's Census and Referee established coherent fibers with trace T=+4 and T=-4, including infinitely many T=4 fibers for each fixed split selected prime. I therefore changed the question from "is each fiber smaller than 4?" to "what does the exact trace do over the complete genuine residue carrier?"

Claim 20261020-coordinator-1 is the following exact complete-residue calculation.

Let p be a split rational prime greater than 3. Under the two conjugate roots of X^2+X+1 modulo p, the unit residue ring is

    (O / pO)^x = F_p^x x F_p^x.

Identify each genuine sixth-power residue with zeta_6^e, e in Z/6Z. For a complete four-label unit fiber put

    tau(e) = zeta_6^e + zeta_6^(-e),
    T(e,f) = tau(e) + tau(f).

Because p is 1 modulo 6, each phase occurs exactly (p-1)/6 times in each coordinate. Hence (e,f) is exactly uniform on (Z/6Z)^2 over the complete unit residue carrier. The trace distribution for T=-4,-3,...,4 is

    1, 4, 4, 4, 10, 4, 4, 4, 1.

Consequently

    average T^2 = 4,
    average T^4 = 36,

whereas the pointwise maxima are 16 and 256. For m distinct split selected primes, CRT makes the phase pairs independent on the complete product-residue carrier, so the product trace has exact second and fourth moments 4^m and 36^m.

This is PAPER_PROOF / EXACT FINITE LOCAL MOMENT. It is genuinely different from a pointwise sign or norm-only phase collapse. It is not a detector estimate: the actual cofactor-prime source occupies weighted prime/ray-class subsets rather than the complete residue carrier, the p|u zero-extension rows are absent from this calculation, and the full selected source has decorations and exceptional rows.

The exact inverse diagnostic is also useful. If nonnegative phase-bucket weights w(e,f) have total W and discrepancy delta(e,f)=w(e,f)-W/36, then

    |sum w T^2 - 4W| <= 12 sum |delta|,
    |sum w T^4 - 36W| <= 220 sum |delta|.

Thus a second moment at least (4+eta)W forces total phase-bucket discrepancy at least eta W/12. Coherent individual fibers are harmless to the complete moment unless the actual source concentrates in their ray classes. This identifies a falsifiable arithmetic input rather than assuming randomness.

No zero-free line, Mertens exponent, canonical VF estimate, or RH conclusion follows.

## B. Current proof objective and authority

Final live authority:

- main@c7d4f6d1140992c25a13068e255fcad651b55686, merge of PR #988 after merged #983, #989 and #990;
- AGENTS.md blob 20bff52d6784c17d4a7d6ac731f4a71c2bdad8a6;
- CURRENT_PROOF_CONTRACT.md blob 2fa9931dcdc1fc8a816aefb8aa348db12ee9a384;
- native replication protocol blob 53194dc3ae106be363bc22cf85a88bac4a3b2e6e;
- dynamic protocol blob bd1189617c069565a881c2a5c5dbd9a138bc48c1;
- external inbox blob 038018145c0fddb2f6306c0712373adf9cd1ea52;
- merged conjugate-product source blob 2d2046ee52af6f551a9eeedbc4ddad04f9ff1c05.

The public target remains

    exists C >= 0, forall R >= 2,
      |pi(R^2) - vfMidFinishedMass(R) - sqrt(2)| <= C R log R.

The binding intermediate campaign is a source-faithful native reconstruction of the completed-cubic theta / sextic Hecke mechanism proving nonvanishing for Re(s)>7/8. The required chain still includes Stage I 11/12, actual marked-minus-rescaled local factors and global selected ownership, inverse/plain moments, principal and exceptional rows, common-probe assembly, and terminal Mellin contradiction.

Until the complete independent source-to-theorem chain exists, status remains INCOMPLETE; NO INDEPENDENT 7/8 PROOF.

## C. Competing mechanism portfolio

### 1. Native completed-theta / sextic detector reconstruction - CONTINUE, primary

Concept: reproduce the actual LOW/HIGH common probe, marked-minus-rescaled source, genuine ideal phases, inverse second moment, refined plain fourth moment and detector.

Independent input: native proofs of the completed-theta/Poisson estimates and the actual source moment families with all conductor, height, selected-slot and exceptional-row uniformity.

Target implication: certified bands and the common-probe contradiction yield zeta nonvanishing for Re(s)>7/8.

First missing proof-order theorem: the native Stage-I normalized completed-cubic probe with its genuine 11/12 low/high comparison. First Stage-III theorem: one actual varying-conductor source moment, not an imported terminal certificate.

Support: merged #984 local/source structure, merged #988 conjugate product, and the exact external proof DAG.

Obstruction: finite ideal identities and rational exponent arithmetic do not supply analytic saving. Draft #992 assembles the conclusion from imported pinned intermediate analytic certificates; it does not independently reprove those certificates.

Disposition: continue. Treat #992 as a useful Stage-IV assembly/comparator if it becomes green, not as completion of the binding independent reconstruction.

### 2. Ray-class trace-moment mechanism - PROMOTE within Stage III

Concept: retain both conjugate ideal phases and use exact complete-residue second/fourth moments, then pay the deviation of the actual source from complete phase buckets.

Independent input: a uniform weighted prime-ideal/ray-class discrepancy or large-sieve theorem for the genuine source, with moving selected primes, conductors, heights and annular slots. The theorem must restore p|u rows, primitive-inducing exclusions, principal normalization and multi-slot decorations.

Target implication: insert the resulting labelled inverse/plain moment into the genuine common probe. The exact local tensor moments control the uniform model; the discrepancy theorem controls the arithmetic source.

Unproved step: determine from the actual upstream moment statement the precise weighted bucket discrepancy and exponent margin required. A generic fixed-modulus prime ideal theorem is not uniform enough when the selected modulus moves.

Support: claim 20261020-coordinator-1; merged #988 product conservation; Owner's occurrence-faithful fiber criterion; Analytic's complete-character Plancherel identity and fixed-order norm-fiber frame.

Obstructions: coherent fibers have positive ray-class density and refute pointwise contraction. The actual source is not uniform by definition. The calculation presently covers only two-active unit fibers. For complex signed source coefficients, the displayed nonnegative discrepancy bound cannot be applied without first reaching an energy measure.

Decisive experiment: for each actual selected-prime/conductor bin, compute weighted 36-bucket discrepancy and the exact T^2/T^4 excess on held-out prime-ideal data; compare it with the margin required by the certified moment theorem. A fixed positive excess or concentration growing at the forbidden rate rejects this route.

Disposition: continue, high priority. Do not infer asymptotic equidistribution from today's finite tables.

### 3. Sharp exterior Abel / Green-Kubo source route - RETAIN, secondary direct route

Concept: merged #989 gives exact discrete exterior Abel and signed Green-Kubo/NNS identities on the original Mobius carrier; merged #990 adds the exact logarithmic partition and period-three cofactor cutoff.

Independent input: a uniform high-norm compensated source/Mellin-height moment bound on the actual sharp exterior carrier, plus the concrete admissible smooth primitive and low-norm ideal counting with acceptable loss.

Target implication: control the original square-block covariance directly, without first passing through the imported terminal nonvanishing theorem.

Unproved step: the high-norm source-level compensated moment. Counting alone gives O(Y log Y) at Y=X^(7/8), so the required signed/phase saving is not supplied by #990.

Obstructions: exact Abel reassembly is IDENTITY_ONLY until the high-norm moment is paid; the ideal-labelled-to-once-only physical pushforward remains necessary.

Disposition: retain as a genuinely distinct direct-source mechanism. Do not let it displace Stage I/III reconstruction merely because its finite identities are now compiled.

The older moving-window low-gcd and original #915 historical-payment lanes remain valid but suspended under the merged native-replication priority.

## D. Conceptual research performed

### Proof of claim 20261020-coordinator-1

For e=0,...,5,

    tau(e) = 2, 1, -1, -2, -1, 1.

Convolving this six-value multiset with itself gives the stated 36-pair distribution. Direct exact summation gives

    sum T^2 = 144,
    sum T^4 = 1296.

Division by 36 gives 4 and 36. For distinct selected split primes, the Chinese remainder theorem identifies the complete unit carrier modulo their product with the product of the individual unit carriers, so moments of the product trace factor.

For weighted buckets, sum delta=0. Subtracting the uniform moments gives sums of delta(T^2-4) and delta(T^4-36). Since |T^2-4|<=12 and |T^4-36|<=220, the discrepancy bounds follow by the triangle inequality.

### No-circularity review

- The claim assumes neither a zero-free line nor a Mobius bound and is not target-equivalent.
- It is an exact model theorem on the genuine complete residue carrier, not a theorem that actual cofactor primes are equidistributed.
- Fixed-p ray-class equidistribution is insufficient unless its error is uniform over the moving moduli, heights and slot family used by the detector.
- Tensorization on complete residues does not prove tensorization of actual prime generators.
- The coherent-fiber infinite family remains compatible with the average law: the +4 and -4 buckets each have complete-residue mass 1/36.
- The p|u one/zero-active branches, principal row and ramified prime must be added before any global moment conclusion.
- The phase trace cannot be collapsed to rational norm before the moment; merged source explicitly refutes that transfer.

### Audit of draft #992

The exact source imports OAI Energy.CertifiedExistence and invokes terminal_certificate to construct DetectorCertifiedBands. It then writes the chosen-moment, common-probe and beta-supremum assembly without calling FinalAssemblyUnconditional or its terminal zero-free wrapper.

If exact-head CI succeeds, this is a valid kernel-checked assembly from proved imported analytic intermediates and a useful dependency/comparator result. Under the merged acceptance contract it remains IMPORTED_INTERMEDIATE_ASSEMBLY, not an independent reproduction of Stages I and III. Avoiding the final wrapper does not independently prove the imported terminal certificate or its moment chain.

At final report preparation, run 39504745317 was still in progress in "Build the actual intermediate moments, not the terminal theorem"; prerequisite, compatibility and original covariance compilation steps had succeeded. No green mathematical status is inferred.

## E. Specialist findings

Today's Finite Wheel report, blob 16519e3f2bb2ee0da08ae843f5b3311c2fb5276c, established claim 20261020-wheel-1: exact split/inert/ramified ideal incidence, the 2/1/0 active-slot law and conjugate phase-product conservation. It supplied structural control but no moment saving.

Today's Census report, blob 3d8b87747418bb4db86fe191f01a78801623a643, established the exact trace classification and finite masks, and refuted |T|<=3 with genuine T=+/-4 fibers. Today's Referee, blob bebdcfdf3490b82ea907af7eb5403f7a17b950dc, strengthened this to infinitely many coherent T=4 fibers for each fixed split selected prime and accepted Wheel's product law. This retires pointwise contraction, not the averaged moment route.

Today's Lean report, blob 7511adca99ef29b13b7f54d9f2efe48c60570b15, formalized the conjugate-product theorem. That result is now superseded in repository status by human merge of #988 onto main; source blob is 2d2046ee52af6f551a9eeedbc4ddad04f9ff1c05.

Today's Owner and Analytic reports are absent: TODAY=PENDING. Their 2026-10-19 reports are dated carry-forward evidence only:

- Owner blob fbb74ff27ebbac9f9e3a683c569ec31c9f437b5e: claims 20261019-owner-1/-2, occurrence-faithful norm-fiber criterion and exact good/ramified full-Gram split.
- Analytic blob c89e9038e1e1b61919b8788c294455680c2575b4: claims 20261019-analytic-1/-2, fixed-order norm-fiber frame and complete-character Plancherel; Referee requires tuple order/decorations to be proved before a d2/d4 specialization.
- Census blob f87aaa1dc0d7e4b7f093e44141cefdce69ecc480 and Wheel blob 3ad449f5bd364aafcbe65375da865dfccad30d61 preserve the pre-pivot moving-window falsifier/tail only.
- Lean blob e460a4ccf95702bbea472e1847cf619f57e7d855 is superseded where #984 and #988 repairs have since merged, but its exact-head caution remains valid.

External claims EXT-20261018-PNT-1..3 retain exact-identity, finite-falsifier and source-no-go scope. They do not override the native replication campaign.

## F. Mathematical bottlenecks

1. Stage I: native completed-cubic theta source and genuine 11/12 comparison.
2. Actual source: occurrence-faithful labelled ideal measure, zero masks and once-only pushforward to physical coefficients.
3. Stage II global source: complete selected subset ownership with no duplicated historical or ideal occurrence.
4. Stage III inverse moment: a uniform moving ray-class collision/discrepancy theorem for the genuine selected source.
5. Stage III plain moment: refined fourth moment with centered same-product rectangle, primitive-inducing exclusions and all exceptional rows.
6. Principal and ramified restoration: nonzero principal scalar, p|u branches and holomorphic error majorants.
7. Stage IV: native common-probe/Mellin assembly from independently reconstructed inputs. Draft #992 addresses assembly only from imported intermediates.
8. Direct sharp route: high-norm compensated exterior-source moment and smooth-to-sharp quantitative bridge.
9. Original canonical VF: a separate bridge from any seven-eighths benchmark to the unchanged VFCanonicalSquareVonKochStatement remains insufficient for RH.

## G. Strategy decisions

- Reject universal or eventual pointwise four-fiber contraction. The infinite coherent family settles that program.
- Promote exact complete-residue moments plus weighted ray-class discrepancy as the strongest new Stage-III mechanism.
- Continue the source-faithful native detector reconstruction; do not count imported terminal_certificate as independent proof of its analytic inputs.
- Retain #989/#990 as a distinct direct sharp-source route, but classify their current content as exact structural consumers.
- Suspend wider unweighted four-fiber scans; future computation must use actual detector weights, zero masks and moving conductor/slot bins.
- Do not formalize an assumed equidistribution or moment premise as though it were the missing quantitative theorem.

## H. Next specialist assignments

**Owner Payment.** On the actual completed-theta selected source, define the nonnegative energy weight carried by each two-active phase bucket and prove the coefficientwise labelled-to-once-only physical pushforward. Include the one-active and zero-extension p|u branches and the good/ramified mixed Gram. Falsifier: n=133 must not be counted four times as four physical seats.

**Analytic Type II.** Pull the exact selected-slot weights and margins from the imported source moment theorem, then state the weakest uniform moving-ray-class discrepancy estimate that turns the exact 4/36 local moments into the required inverse second and plain fourth bounds. Prove one genuine range or prove a quantitative obstruction. Fixed-modulus equidistribution, an assumed large sieve, or an unspecified X^epsilon loss is not sufficient.

**Finite Wheel & Incidence.** Prove the complete unit-residue phase-pair map has exactly ((p-1)/6)^2 preimages per pair and tensorizes by CRT for distinct selected split primes. State the exact interaction with primary congruence modulo 3 and keep the p|u strata separate. A valid output is a universal finite theorem, not a cancellation corollary for primes.

**Prime Census Laboratory.** Replace the settled pointwise scan by weighted 36-bucket tables for the actual selected-prime/cofactor windows and detector decorations. Report T^2 and T^4 excess above 4W and 36W, total-variation discrepancy, coherent-bucket mass, and held-out adverse primes. A stable finite fit is evidence only.

**Adversarial Referee.** Audit claim 20261020-coordinator-1 on the actual ideal labels, especially phase orientation, primary-generator restrictions, tensor CRT and nonnegative-weight applicability. Independently classify #992: identify every imported theorem carrying Stage I or III content and reject any "independent 7/8" label unless those inputs are native under the protocol.

**Lean Verification.** After Referee acceptance, formalize the finite trace distribution and second/fourth complete-residue moments, reusing merged #988. Keep the theorem finite and structural. Continue exact-head #992 dependency/axiom audit, but report imported-intermediate provenance even if CI turns green. Do not add a conjectural ray-class bound as a hypothesis advertised as progress.

## I. Lean and PR status

- #983 merged at 0f3eb35726e27bd3d2d8517aa00a0dfc57628816: Lean 4.34.1 migration, infrastructure only.
- #988 merged at current main c7d4f6d1140992c25a13068e255fcad651b55686: conjugate split sextic residue product is PROVED_IN_LEAN_ON_MAIN with structural scope only.
- #989 merged at 6c777cc7c70cc26a4864d30a71bf4429f84269ec: exact exterior Abel / Green-Kubo source identities.
- #990 merged at fe379095ee2c6fb4cd04dc96027dfb71b3d891b9: exact logarithmic partition and cofactor cutoff; no high-norm moment.
- #985 open at 8f51ddcb62c805ef19104399ede62d93731f6fca: numerical censuses pass but native Euler and targeted Lean workflows fail.
- #986 open at 4345260a58f1c14f4018e46292469767c54cd908: ideal bridge, termwise cancellation and targeted Lean workflows fail at that exact head.
- #987 draft at 1a3a6486bad446c955f4ea196f3284eed943908b: native square-block and direct transport gates pass; both full certified 7/8 gates and the real ideal-fiber bridge fail. It does not establish independent moments.
- #991 draft at 27b9c90acaf09764ab4c9c28195797727fb27457: exact-head full-certificate and ideal-bridge workflows remain failed.
- #992 draft at 13a6bc10b835ff363ad402292b0ece60442cacee: source/audit/export/targeted checks pass; the material LOW/HIGH workflow run 39504745317 remains in progress at the imported intermediate-moment build.

No PR, review, workflow rerun, merge, schedule or permission change was performed by the Coordinator.

## J. Next-run resume capsule

- Authority: main@c7d4f6d1140992c25a13068e255fcad651b55686.
- New claim: 20261020-coordinator-1, exact complete-residue trace distribution, moments 4 and 36, CRT tensor moments 4^m and 36^m, and weighted discrepancy inverse bounds; PAPER_PROOF.
- Retired route: every pointwise/eventual strict four-fiber contraction.
- Primary surviving idea: convert exact complete-residue moments to the genuine source through a quantitatively uniform moving ray-class discrepancy/large-sieve theorem.
- First falsifier: weighted actual-source phase buckets concentrate enough that T^2 or T^4 excess exceeds the available certified margin.
- First proof-order blocker: native Stage-I 11/12 detector.
- First Stage-III blocker: exact weighted moving-ray-class moment with zero/principal/exceptional restoration.
- #992 status: pending exact-head material CI and, regardless of green, imported-intermediate assembly rather than independent Stage-I/III reconstruction.
- Highest-value next reasoning task: extract the precise source weights and strict margin from the inverse/plain moment theorem and compute the weakest phase-bucket discrepancy exponent that suffices.

## Publication verification

An early IN_PROGRESS checkpoint was published as PM commit f01e2c50d2665c0ca642ea61842ac0e212f00693 and AM mirror commit 489f866c85cd54b4546e7685236014e9a8f3109d, with identical checkpoint blob 5aefcebf96427fab412cd26cd4655a8675c72b4c. The first completed replacement committed as PM bf98143b43b903cbf213577691b7b2c2ab72a0fd and AM mirror c02cbeafb9dc1f2754696d2d71ffc5688fdc5d53; both returned identical content blob ecc8a1b29e02fa3af1e9696e0e1b6821666c60ef. A final metadata-only replacement records those identifiers. Publication success does not change any mathematical or PR status.

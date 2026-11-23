# Native theta descent, orbit freeness, and the complete source

## Scope and verification

This work continues from merged PR #1198, main
0a6a2a7ddbe1859d8d954d6c43f2ef340b32cdaf. The pinned mathematical source is
CocoSgt/riemann-hypothesis-lean at
7cbf7a0c32fca1badf05931879a37c3f8a2b03b4. The source is inspected as proof
material; no upstream compiled object or terminal RH theorem is imported.

The complete local bundle contains nineteen new native Lean modules, the
root import update, this report and the companion sixty-two-root axiom audit.
The first implementation batch reconstructs six concrete supplying modules.
The further batches add the actual period quotient and its finite-order
freeness, a rank-independent fixed-level criterion, full formal-jet and
descended-value triangular covariance, local chart descent, the exact
prime-power decomposition with its paid ramified contribution, and the
served-prime quotient-length estimate. All nineteen modules and the
sixty-two-root audit passed the hosted changed-research closure on source
head 4300924af3527e04c3f31c9e8897aad82d9318f9. The full native build and
publication outcome are recorded below. No local Lean is run,
no proof budget is raised, and only propext, Classical.choice and Quot.sound
are permitted terminal axioms. The companion research audit checks exact
public types and rejects any other terminal axiom.

Publication status: PUBLISHED in
[PR #1199](https://github.com/OVVO-Financial/RH_Lean/pull/1199), branch
research/alpoge-native-theta-realization-20261123. The initial local
checkpoint was blocked by automatic approval review. The user's subsequent
instruction, "Put it on main!", explicitly authorized publication and merge.
The shell transport had no GitHub credentials, so the connected GitHub writer
published commit f9c7a64acd3a9a00827e58931c19a7a044d807db. Its tree
064ae8c9988ee241392b59607d40d8d618530ed8 exactly matches local completion
commit c12f95bdcfb9efb57f28e795706a7cd76394a0df, which preserves the preceding
local commits 63fe4cb35c5bfba247c698b1ae7f4b63c5c20c36 and
d7695f1e58b7ca462c06158d5ec88f7100142c6b. The published commit metadata differs;
the file contents do not. The native hosted checks passed as recorded in
section 10. Historical original-OAI replay is explicitly retired from the
native acceptance gate; section 12 records the correction to its CI triggers.
The linked PR records the subsequent authorized merge outcome.

The complete native signed Gz bound and RH remain open. In particular, the
construction below does not assert that an arbitrary formal theta germ has
positive rank, or that a natural rule already satisfies the section weight,
integrality, Petersson norm and cusp conditions.

## 1. Exact chart agreement

NativeThetaChartAgreement constructs the permutation between two finite
enumerations of the same isotropic subgroup after translation. Its phase
argument retains both original relations: each column phase has N-squared
torsion, while isotropy makes the product of phases square to one. Odd N
forces the product itself to be one.

This proves equality of the literal rawShortValue expressions, including the
normalization, coefficient sum and every column derivative, after transport
into a common algebra. The final equality of theta values is not a premise.
The actual geometric chart must still supply the torsion enumeration, column
jet transformation and pairing identities.

NativeThetaLocalChartAgreement corrects an important source-level distinction:
the permutation and phases may vary on local pieces of a common algebra.
It proves that the actual maximal-ideal localization maps jointly detect
scalar equality, then derives common-algebra theta equality from local
phase cancellation. Effective descent constructs valueOfLocalPhases in the
original base ring, with its exact raw-value characterization, naturality
under base change, and its triangular weight law. A global permutation is
not required on this path.

Sources: IsotropicSumIndependentOfChoicesLocal.lean and
ShortThetaSumEqOfWitnessesCommonAlgebra.lean, under
src/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/.

## 2. Construct the cover and descend the value

NativeThetaFiniteFlatCover starts with an actual finite, flat, surjective
scheme morphism. It forms the scheme pullback over an affine point, takes its
global-sections algebra, and constructs a faithfully flat map over which the
point lifts. Finite induction constructs one cover carrying a whole finite
family of lifts.

This is the source's point-root mechanism for multiplication by N on an
abelian scheme. A scalar polynomial root construction would not supply these
point roots and is not substituted.

NativeThetaFaithfullyFlatDescent constructs the tensor-product comparison
algebra and proves unique effective descent of compatible elements.
NativeThetaSectionRealization composes that descent with the finite phase
calculation. It constructs values in the original base algebra, a linear map
on the prescribed homogeneous polynomial space, and natural rules in the
existing NativeFramedRules.Rules carrier. The common-chart transitions are
explicit finite permutations and phases, rather than a value-agreement law.

Sources: FaithfullyFlatPointsBaseChangeDescent.lean,
ExistsFaithfullyFlatRoots.lean,
ShortThetaValueExistsUniqueNaturalOfLaws.lean and
ShortThetaValueLinearInPolynomial.lean, in the same source directory.

The polarized moduli object, the actual multiplication morphism and the
theta-group transitions on it are still to be instantiated. This distinction
is retained in the native theorem types.

## 3. Prove the finite orbit-freeness mechanism

NativeThetaOrbitTorsion reconstructs the finite-order unipotence theorem.
Let g be prime, A a g-divisible g-primary additive group, and beta a finite
order endomorphism. Suppose its g-torsion has at most g^r elements,
r+2 <= g, and beta-1 is nilpotent on that g-torsion. Then beta is the identity.

The proof first regards the finite g-torsion as a vector space over ZMod g.
Its cardinal bounds its dimension by r, and Cayley-Hamilton lowers the
nilpotence index to r. The coprime and g-power parts of the finite order are
then removed using primary torsion and divisibility.

Source: FiniteOrderUnipotentAutDivisiblePrimaryEqId.lean, under
src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/.
Its source consumers are ExistsSmallTorsionSetForEndomorphism.lean and
LevelAutomorphismUnipotentFixesComplexPointEqOne.lean.

This theorem proves the orbit-freeness ingredient. It does not prove that a
chosen space of theta sections separates those distinct points. The original
separator also uses a sufficiently positive Hodge line bundle.

## 4. Actual native lattice cardinalities

NativeThetaOrbitLattice specializes finite flat module cardinality to the
already constructed inverse-ideal lattice on the native host.

For a maximal ideal I, the quotient cardinality is

    absNorm(I)^N.

For a rational integer level g, the actual additive lattice quotient has
cardinality

    g^(N * [E:Q]).

The full integer rank is retained. No degree-one prime is silently supplied,
and the projective O_E-lattice is not replaced by a free O_E-module. The
quotient is finite whenever g is nonzero.

Source: NatCardQuotSmulTopLePowFinrank.lean in DivisorProofs, together with
the existing native twistedLattice finite-projective construction and its
two exact rank theorems.

A nonzero finite g-primary quotient is not itself g-divisible. The orbit
freeness theorem therefore must be applied to the divisible primary tower,
with the quotient identified as its first torsion layer. Applying it directly
to the finite quotient would be invalid.

## 5. Construct the actual native period-primary group

NativeThetaPeriodTorsion constructs the additive quotient V/P(L) for the
existing prescribedPeriodMap, with no replacement lattice or period object.
Division in the real ambient vector space proves that multiplication by g
on this quotient is surjective. The map l -> [P(l)/g] is surjective onto
the actual g-torsion, and its kernel is exactly gL. Thus

    L/gL = (V/P(L))[g] up to the constructed additive equivalence,
    card((V/P(L))[g]) = g^((k+m-1)*[E:Q]).

The compatible primary tower inside this quotient is g-divisible. The
finite-order unipotence theorem now applies to that concrete tower without
asking for a Tate identification, torsion count, or divisibility premise.
Its remaining hypotheses describe the actual endomorphism: finite order,
unipotence on the full g-torsion, and g at least the full integer rank plus
two. This endpoint fixes the primary points.

NativeThetaPeriodFreeness continues to the whole quotient. A real-linear
lift F and compatible integral action alpha induce the actual quotient
action. Primary fixedness puts alpha(l)-l in g^a L for every a. The actual
free integer basis proves that intersection is zero; the already constructed
real tensor equivalence proves the periods span the ambient real space.
Thus alpha, F, and the whole quotient action are all the identity. This
avoids a separate general scheme-theoretic torsion-density theorem for
this concrete period application.

This is not yet the source's moduli-stabilizer theorem. The original source
uses unipotence at a particular norm-g ideal and its actual level action;
full rational-g torsion unipotence is a stronger input. The stronger level
condition must either be constructed with its costs, or the ideal-primary
action must be supplied before invoking this endpoint for those stabilizers.

### A concrete reduction of the auxiliary-prime threshold

The finite-order proof itself only needs a nilpotence index. Its refined
finite_order_unipotent_eq_id_of_index therefore removes the finite torsion
set and cardinality premises entirely: if the actual index is u, the prime
condition is u+2 <= g. The older theorem retains its exact type and now
factors through the index theorem after deriving its index by Cayley-Hamilton.

NativeThetaPeriodIndexFreeness transports this improvement to the same native
period quotient. In particular alpha(l)-l in gL gives u=1, so every prime
g >= 3 suffices, independent of the rank and [E:Q]. The literal native
endpoint prescribedPeriod_finite_order_congruent_five_eq_id uses g=5 and
concludes identity on the integral lattice, ambient space and actual quotient.

NativeDyadicFixedAuxiliaryLevel proves that this fixed candidate is unramified
on every original dyadic host: q mod 8=3 and d mod 16=7 exclude 5 from q,d,
hence 5 does not divide 2^(e+2)*q*d and the actual native inertia at 5 is
trivial. No norm-five prime ideal is assumed.

This is a real improvement of the freeness criterion. It does not yet
replace the original geometric level: the moduli action must be realized
with full level-five congruence, and the added level's rank and metric
costs must be transported before claiming a global cost reduction.

## 6. Derive triangular covariance from the native harmonic conditions

NativeThetaTriangularFrame proves the full lower-triangular transformation
law for the existing HHa polynomials, over any coefficient algebra of the
infinite coefficient field. Elementary row invariance extends to algebra
coefficients; finite unipotent elimination and the individual row degrees
give

    P(c*y) = (product over rows of c_ii^(a_i)) * P(y).

The HHa membership proof supplies RowInv and RowDeg. No triangular
covariance premise is added. NativeThetaFormalCalculus proves the formal
substitution chain rule and coordinate coefficient identities on the
existing native Series and substitutions. NativeThetaFormalGroup retains
the actual formal coefficients and structural unit, commutativity and
associativity identities. Differentiating associativity gives jac_F;
NativeThetaInvariantDerivatives derives commutation of the original native
directional derivatives from those identities.

NativeThetaJetFrame then forms their commutative operator algebra and
contracts its column tensor powers against the same gauge-corrected germs.
This proves the triangular identity for shortValueOfFormalGerms, preserving
beta, the lattice index, the level-function count, every level-power
normalizer and N-squared section power. NativeThetaSectionWeight transfers
that law through the same faithful cover to the constructed original-base
values. The local-phase version is also proved in NativeThetaLocalChartAgreement.
The actual chart/germ instance, cusp property, integrality and Petersson
estimates remain to be supplied.

Source: InvariantOperatorValueTriangularChange.lean, RowTriangular section
Poly, under CuspFormEvaluations.

## 7. Identify the complete arithmetic source and pay all d powers

NativeDyadicHostPrimePowerWeights uses the existing full native
Frobenius/inertia census on the same modular-unit host. It proves the local
weights for every exponent, including the ramified sites:

| Actual prime class | Exponents | Coefficient and site |
| --- | --- | --- |
| Unramified inert | Odd | 2 at i*frob(p) |
| Unramified inert | Even | 0 |
| Unramified split | All | 0 |
| Conductor primes 2 and q | All | 0 |
| Ramified d | All positive | 1 at iod+i*frob(d) |

The d-inertia is proved to be exactly {0,iod}, and the existing CRT
Frobenius representative has trivial d-character. The full ASK therefore
equals the odd class sums plus the complete d correction. The original
cutoff is retained; when d lies beyond it, the correction is proved zero.
Composing with the existing exact ASK-minus-MAIN identity gives the full
signed De with the original ell-dependent MAIN unchanged.

For nonnegative amplitude and actual widths, the geometric series proves

    norm(D_d(a,w)) <= a*log(d)/(d-1).

Summing over the actual finite row and translation sets and dividing by
their earned divisor |T|*|J|*b*Delta/2 gives

    norm(sum D_d)/Q <= 2*(x+1)*log(d)/(Delta*(d-1)),

provided a_t <= b*(x+1). Every positive d-power is present before the
inequality. This is a paid arithmetic component, not a proof that the
odd-prime class sum is bounded by the geometric finite-place gain.

Sources: FrameCodeOfAdditive.lean, right3/inert_sum, and
PowFourLtCeilThresholdPrime.lean, pb_atD/ASK_at.

### The explicit served-prime quotient-length payment

NativeServedPrimeLength reconstructs the actual finite-layer estimate used
by StabilizerCount.core, stmt6G, the length clause of AuxBlock8.admG1, and
then linkG_at_core. For a finite free DVR lattice M of rank d, a submodule
N, and a nonzero element a, the explicit exceptional sets C_beta satisfy

    card(C_beta) <= d*s^(beta+1),
    a^(tau+beta*S) M <= N + span(C_beta),
    a^(V*S) M <= N,
    0 <= s <= 1/2.

The constructed quotient maps and its successive cyclic layers give

    length(M/(N intersect a^tau M)) <= v_O(a)*d*(tau+2*S*s).

Here v_O(a) is proved equal to length(O/(a)); a ramified rational prime is
not treated as a uniformizer. Restriction to an actual saturated submodule
uses the natural quotient injection and retains the ambient rank d.

The source has an explicit exceptional-set supplier:
G.LatticeSystems.theta_kernel_expansion / stmt1Loc_proved, assembled from
jEquiv, jDelta, jRank, jLocal/jSmith/jBase. Its actual Fock/served-orbit
module, trivial stabilizers, finite classes and LPprime local data must be
realized natively before extracting those C_beta. Thus the next gap is a
specific construction and transport, rather than an unspecified new
arithmetic cancellation hypothesis. The valuation-gain clause of admG1
and its complete native ASK comparison remain open.

Sources: ManyOrbitsRefined.lean, CyclicSpanLengthLemmas.lengthPart2;
LatticeSystems.lean, lengthFromAllBut; and
GrowthBounds/MultisetValuation/StabilizerCount.lean, core/stmt6G.

## 8. Smaller theta image: exact scope

The existing regular-multiplier constructor accepts an actual subspace U of
the section algebra. Taking U to be the actual theta image can avoid full
cusp surjectivity for that branch if the image separates the required finite
translation orbit and has the required integral norm bounds.

Replacing the main descent source by that image is a separate operation.
If the old source rank is R, the target has rank at most (1+rho)R, and the
retained image has rank at least (1-delta)R, its rank-defect allowance becomes

    (rho+delta)/(1-delta).

The actual slope and complete arithmetic trace also need a proved comparison.
A positive-density image alone does not pay those costs. The native frame
and all-place complement theorems can consume quantitative physical estimates;
no further abstract complement interface is needed.

## 9. Remaining source attachment

The arithmetic prime-power-to-gain supplier in the source is LinkG_at.
LinkDIV and LinkS serve different parts of the assembly. The exact source
identification must retain every odd unramified class sum, all powers of the
ramified prime d, the original MAIN and ell correction, and the actual
finite-place lengths.

The mass normalization likewise uses the actual rank and mass identities.
A freely chosen record parameter cannot replace those identities.

The original descent budget already pays q^3 exp(2 C z^9) inside exp(b),
while its consumer allows exp(2b). Coarse additional forward-map costs whose
logarithm is at most b can therefore be used. The native mean-energy theorem
is an optional volume saving; it does not establish rank or source identity.

The endpoint remains the existing one-sided square criterion. Exponent
constants must be controlled before choosing the arbitrarily small positive
loss; the fixed-epsilon signed-slope theorem alone does not provide that
uniformity.

## 10. Verification and exact resumption point

The following local static checks passed on the complete candidate:

- `bash scripts/audit_assumptions.sh`: Lean source audit passed.
- `python scripts/check_root_manifest.py`: the root imports all 1,572 native
  modules in sorted order.
- `bash scripts/check_paper_analysis_boundary.sh`: dependency boundary passed.
- `python scripts/proof_inventory.py --json ... --no-summary`: source
  inventory generated successfully.
- `git diff --check`: whitespace check passed.

The three implementation workstreams also reviewed the mathematical
arguments and the pinned API usage, including the local-phase adapter,
explicit-index period criterion, literal level-five conductor proof and
ramification factor in the served-prime length bound. This is source review,
not Lean kernel verification or acceptance by the scheduled Referee role.
The companion audit executed successfully for all sixty-two concrete
declaration roots. Every reported transitive terminal-axiom set contains
only propext, Classical.choice and Quot.sound. All nineteen new native
modules have explicit successful hosted compilation records, and the final
changed closure passed on source head
4300924af3527e04c3f31c9e8897aad82d9318f9 in
[run 45231625619, job 137892698719](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45231625619/job/137892698719).
Its first research-audit pass reported compiled=1 cached=0; the second
reported compiled=0 cached=1. No Lean or Lake command was run locally.

The full native `RHLean` build, RHLean-owned warning gate, exact elaborated
declaration-graph validation and cache save also passed on that same source
head in
[job 137895327217](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45231625619/job/137895327217).
The full build completed 10,523 jobs. Its exact graph contains 19,632
declarations and agrees with the source inventory on 13,820 named proofs,
with no source-only or elaborated-only declarations and no cyclic
declaration components.
The static audit passed all eleven controlled-process tests and twenty-three
research/cache tests. The failure-cancellation job was correctly skipped on
this successful primary run.

The initial publication payload is precisely the nineteen mathematical
modules, root import manifest, mathematical report and research audit.
The user's subsequent fail-fast request also adds the CI changes below.
The explicit user authorization covers publication and merge; the required
hosted checks run on PR #1199. The compiler repairs retain the original
statements and actual geometric objects; the successful hosted closure and
axiom audit, rather than local source inspection, establish the verification
reported here. The full native build and exact declaration-graph gates
also passed. The seventeen other completed workflows on this source head
were successful. The only still-running workflow at that checkpoint was
the obsolete original-OAI fractional-owner replay described in section 12;
that historical replay is not a native merge prerequisite.

The first geometric supplying proof to instantiate next is
`GlobalTheory.exists_cover_shortVal_data` in
`ExistsFaithfullyFlatCoverShortThetaValueData.lean`. Its actual polarized
object, multiplication cover, formal charts, theta-group sections and
translated germs must feed the local common-algebra comparison
`GlobalTheory.ShortCompare.shortSum_eq_of_witnesses`; the new native local
descent and weight chain then has a concrete input. For the finite-place
branch, instantiate `G.LatticeSystems.theta_kernel_expansion` /
`stmt1Loc_proved` on the actual served-orbit module to supply the exceptional
sets used by `lengthFromAllBut`. Cusp/orbit separation, measured rank and
Petersson mass, the valuation-gain comparison and exponent uniformity remain
explicit downstream construction obligations.

The fixed-level result is the reusable strengthening from this round:
explicit nilpotence index replaces torsion cardinality in the finite-order
theorem, and full odd-level congruence gives identity on every actual free
integral period lattice with a spanning real period map. Its application to
the geometric moduli level and the resulting global cost improvement remain
open. No universal Gz bound or RH closure is claimed.

```text
descent_payment_ack=ALPOGE_NATIVE_DESCENT_PAYMENT_V1
tractability_ack=ALPOGE_VIOLE_TRACTABLE_RH_V1
MATHEMATICAL_STATUS=GENUINE_PARTIAL_KERNEL_VERIFIED
FORMAL_STATUS=HOSTED_NATIVE_KERNEL_AND_AXIOM_AUDIT_VERIFIED
PUBLICATION_STATUS=PUBLISHED_PR_1199
GLOBAL_NATIVE_BOUND=OPEN
```

## 11. Hosted repair and fail-fast CI

The first published head f9c7a64acd3a9a00827e58931c19a7a044d807db failed both
the native and targeted hosted builds. The diagnostics identified concrete
elaboration/API issues in chart agreement, formal invariant derivatives,
prime-power arithmetic and period torsion, plus owned-source warnings.
The first repair preserves the theorem statements while supplying explicit
finite-sum functions, host-tag and quotient coercions, formal substitutions,
and current Mathlib API names. No proof budget or linter is weakened. The
sixty-two-root audit could not run until its native prerequisites compiled;
its eventual successful execution is recorded in section 10.

The user requested that CI fail faster and stop further runs after earlier
failures. The pipeline now orders the cheap source audit, changed research
closure, and full native build. The research workflow is reusable/manual,
so a PR no longer starts an independent duplicate research build. An earlier
failure skips the later build; a metadata-only job cancels still-active
workflows associated with the same PR number, head SHA, branch and repository.
It cannot cancel the current workflow or a different revision or PR.

Pinned Lake v4.34.1 has no fail-fast CLI flag. The new Python process monitor
streams its output and stops its own process group on a compiler failure or
RHLean-owned warning. Dependency warnings retain their existing treatment.
Controlled subprocess tests cover termination and resistant children, and
research-cache tests verify that failed prerequisites cannot start later
proofs. No local Lean process is used for those tests.

Completed native prerequisites are saved under a distinct preflight cache
key for the full build and repair iterations; they cannot masquerade as a
complete native-root cache hit. Obsolete preflight entries are trimmed to
avoid evicting the dependency caches. All source, type, declaration-graph,
warning and transitive-axiom acceptance checks remain in force.

The failure path was exercised on published head
2249f884987073e5f5ae0b9299613ce5a8c394f4, hosted run
[45222581857](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45222581857).
The targeted build reported the failing prime-power module at 17:02:19 UTC
and returned failure at 17:02:20 UTC. It saved completed prerequisites;
the full native build was skipped. The cancellation job succeeded and stopped
eight other same-revision PR workflows. The remaining source diagnostics in
that pass concern explicit group types, map-one normalization and finite-set
cardinality applications; they do not establish a mathematical counterexample.

The static-audit failure path was also observed on head
bc0c9b5f67786194273296ef42a01f77a72119cc, run
[45226956388](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45226956388).
A process-cleanup regression test failed before Lean setup. Both the changed
research closure and full native build were skipped, the cancellation job
succeeded, and fourteen other workflows for that revision were cancelled.
This is evidence for the static-audit gate, not a Lean compilation result.

Source inspection identified an early-return race: dispatching SIGKILL did
not confirm that a descendant had completed its asynchronous exit. The
monitor now uses Linux pidfds to confirm exit of remaining live members of
its own process group within a one-second bound. It does not wait for PID 1
to reap zombies. The immediate non-running-child assertion is retained,
and a second test covers a TERM-resistant child that has closed stdout.
All eleven controlled-process tests and twenty-three research/cache tests
passed locally; twenty repeated cleanup trials also passed. The old race
was not reproduced in thirty local trials, so the hosted failure and the
identified early-return path, rather than a claimed local reproduction,
are the evidence for this repair. No Lean or Lake was run locally.

## 12. Retire the remaining automatic original-OAI rebuilds

The user identified an unnecessary rebuild in
[run 45231625944](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45231625944),
job `fractional-owner-proof`. Its native numerical, core and kernel jobs had
already succeeded. A change to the shared research compiler had triggered
the Universal envelope workflow, whose unguarded historical job restored
the original OpenAI project and fell back to rebuilding
`OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional` on a cache
miss. This replay was already retired by the repository's 2026-11-21 user
priority override. Waiting for it as a native merge prerequisite was an
acceptance-policy mistake, not a missing native proof dependency.

The correction gates this job and thirteen other remaining automatic
original-OAI jobs behind `workflow_dispatch` and the explicit boolean input
`run_original_oai`, defaulting to `false`. Eleven exclusively historical
workflows become dispatch-only. The Universal envelope workflow retains its
native numerical, core and kernel checks; the two other mixed workflows
retain their independent arithmetic checks. Historical proof sources and
build/cache steps are preserved for explicit archival replay.
The same audit also found an unused reusable entry point in the historical
Gaussian workflow. It is removed, and that job receives the same explicit
default-false manual gate, so another workflow cannot silently call it.

The cache-policy guard now checks original-OAI retirement across every
workflow, including untouched YAML files. It also runs when the shared
research compiler or fail-fast monitor changes. Its regression suite checks
the manual event, explicit default-false boolean gate, preserved native
jobs and repository-wide absence of automatic original-OAI jobs. This closes
the previous gap, where a short list of named historical workflows and
changed-file-only inspection missed the mixed workflow.
The primary static audit runs this regression suite before either Lean stage,
so a policy regression also prevents the expensive native builds from starting.

Universal envelope concurrency is now scoped to the branch instead of the
head SHA, so new revisions supersede old ones. A metadata-only cleanup job
handles already-running legacy SHA-scoped runs: it cancels only older
automatic runs of this workflow for the same PR, branch and repository that
still have an active fractional-owner job. It excludes the current run,
newer runs, completed jobs and explicit manual replays, and never checks out
PR code. This CI correction changes no mathematical source or proof budget.

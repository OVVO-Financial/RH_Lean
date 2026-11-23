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
served-prime quotient-length estimate. Hosted Lean verification is blocked
at this checkpoint. No local Lean is run,
no proof budget is raised, and only propext, Classical.choice and Quot.sound
are permitted terminal axioms. The companion research audit checks exact
public types and rejects any other terminal axiom.

Publication status: NOT_PUBLISHED. Automatic approval review rejected the
branch push, and rejected a second attempt after the exact public repository,
authenticated push permission, existing non-main authorization, and the
mathematical-only payload had been checked. The second review requires
explicit user approval of this particular payload before it is published.
No alternative write path is used. Hosted CI therefore remains
BLOCKED_CI_NOT_TRIGGERED; the new source and audit are uncompiled. The first
two local commits are 63fe4cb35c5bfba247c698b1ae7f4b63c5c20c36 and
d7695f1e58b7ca462c06158d5ec88f7100142c6b on
research/alpoge-native-theta-realization-20261123; the completion commit
contains this revised report. The destination is
https://github.com/OVVO-Financial/RH_Lean, and no main update or merge is proposed.

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
The companion audit has sixty-two concrete declaration roots and is prepared
to reject terminal axioms other than propext, Classical.choice and Quot.sound;
it has not yet executed. No Lean or Lake command was run locally.

The publication payload is precisely the nineteen mathematical modules,
root import manifest, mathematical report and research audit. It contains
no workflow, permission or agent-schedule change. Approval must cover this
specific public payload before the branch can be pushed and a draft PR can
trigger the required hosted checks. After those checks, repair actual
compiler failures before treating any declaration here as verified.

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
MATHEMATICAL_STATUS=GENUINE_PARTIAL_SOURCE_REVIEWED
FORMAL_STATUS=BLOCKED_CI_NOT_TRIGGERED
PUBLICATION_STATUS=NOT_PUBLISHED
GLOBAL_NATIVE_BOUND=OPEN
```

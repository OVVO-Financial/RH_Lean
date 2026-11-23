# Geometry construction: source map and native extraction

## Pins and verification state

Upstream: [CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4](https://github.com/CocoSgt/riemann-hypothesis-lean/tree/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4).

Native integration base: `OVVO-Financial/RH_Lean@608b5702a20ab34a9efcd38b5d59e09f9f565f61`.

The files under `RHLean/Geometry/` are proof drafts awaiting the parent's hosted Lean validation. No local Lean or Lake execution was performed. Source-inspected upstream proofs and closed source suppliers are distinguished from a newly checked native theorem. `closed-lattice-port-manifest.json` records source and extracted-file SHA-256 hashes for the six-file closed number-field lattice construction.

## The constructed finite witness

The decisive native endpoint is:

`RHLean.Geometry.nativeExists_component_short_integral_group_section`

in `RHLean/Geometry/NativeComponentRegularSection.lean`.

It uses one ambient number-field vector space $V$, one integral lattice $L\subset V$, actual component subspaces $V_z$, integral component lattices $L_z\subset V_z$, and the same norms $N_\sigma$ at every complex embedding. It performs these constructions in order:

1. In each $L_z$, construct integral generators from a given short spanning set using the original all-place number-field lattice theorem.
2. Include these actual generators into the ambient $L$; prove that their union spans $V$.
3. Construct a regular group-determinant seed from the actual orbit-evaluation independence.
4. Replace its field coefficients by natural coefficients bounded by $q^2$, preserving all component determinants.
5. Bound the resulting section at every point and embedding using the same generators and pointwise norm comparison.

Let $d=[K:\mathbb Q]$, let $r$ bound the rank of each component section space, let $q=|S|$, and let the original spanning vectors satisfy $N_\sigma(v)\le A$ for every embedding. The generator conversion constructs at most $2dr$ generators per component, with common bound

\[
\Lambda=\max\{1,d^4r|\operatorname{Disc}(K)|^{1/d}A\}.
\]

If the actual pointwise norm comparison has constant $\beta$, the constructed regular section satisfies

\[
\|\operatorname{realize}_p(u)\|
\le (2dr)q^2\beta\Lambda
\]

simultaneously for every indexed point and place $p$. The proof uses at most one active component at a point. The number of all components does not enter this estimate.

The section belongs to the original $\mathcal O_K$-lattice. Its coefficients are genuine nonnegative integers; there is no division by $q$, no replacement multiplicity, and no cancellation premise. The internal rational/integer basis reduction in the number-field generator proof is exactly the upstream construction and imposes no additional restriction-of-scalars gate on the application.

This theorem still takes the concrete geometric facts from the application: short spanning families, the component decomposition, the actual component lattice embeddings, orbit-evaluation independence, support locality, and the pointwise/Petersson comparison. It constructs both the regular seed and the short generator lists; those are no longer hypotheses.

## Closed native number-field lattice subclosure

| Native file | Native endpoint | Upstream construction retained |
| --- | --- | --- |
| `NativeLatticeTransferenceA.lean` | `NativeTransference.gtB_dual_short` | Minkowski determinant-volume argument giving one short dual vector |
| `NativeLatticeTransferenceB.lean` | `NativeTransference.gtC_prim`, `gtD_lat` | Primitive integral dual vector and actual orthogonal sublattice |
| `NativeLatticeTransference.lean` | `NativeTransference.transference_dual` | Independent dual vectors of norm at most $n^2/\lambda$, with actual integer pairings |
| `NativeTraceDualDiscriminant.lean` | `NativeNumberFieldLattice.finrank_mul_discr_rpow_le_sum_sq_of_mem_traceDual` | Nonzero trace-dual element costs at least $d|\operatorname{Disc}K|^{-2/d}$ in squared embedding norm |
| `NativeShortIndependentIntegers.lean` | `NativeNumberFieldLattice.exists_short_independent_integers` | Constructs $d$ independent algebraic integers with each embedding bounded by $d^3|\operatorname{Disc}K|^{1/d}$ |
| `NativeAllPlaceShortGenerators.lean` | `NativeNumberFieldLattice.exists_isShortGen_of_short_span` | Constructs generators of the complete integral lattice with the exact $d^4r\operatorname{Disc}^{1/d}$ and $2dr$ costs |

All names in the second column have the prefix `RHLean.Geometry.`. Each file imports only Mathlib or earlier files in this six-file closure. The all-place short-generator predicate is the original explicit triple: integer span equals the given integral lattice, every embedding norm is bounded, and the bound is at least one. The native theorem writes the full-span lattice rank as `Module.finrank K V`; this equality was proved inside the original argument, so the substitution changes no numerical cost.

## Regular determinant construction and actual support mechanism

[Upstream CardLeOfDetEqZero.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardLeOfDetEqZero.lean) proves:

- `GlobalTheory.ShortDet.card_le_of_det_eq_zero`: a regular determinant pencil of size $q$ has at most $q$ bad natural parameters.
- `exists_nat_coeff`: successive coordinate replacement preserves a predicate while replacing all coefficients by bounded naturals.
- `comp_unique`: a level automorphism carries a component idempotent to one component.
- `exists_nat_step`: a component-supported generator affects at most $q$ components; their union has at most $q^2$ bad natural coefficients.
- `exists_short`: performs the replacement on the actual component short generators; integrality follows by addition and natural multiplication; disjoint pointwise supports prevent any total-component count.

The native extraction `NativeRegularSectionSelection.lean` generalizes the determinant fields to a dependent family, matching the original generic-point fields `Om Z`. It does not identify these distinct fields or use one common complex evaluation as a substitute for nonvanishing at all components.

[Upstream ExistsVectorGroupDeterminantsNeZero.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsVectorGroupDeterminantsNeZero.lean) supplies `GlobalTheory.GenericGroupDet.exists_vec_det_ne_zero`. The extra geometry import in that file is unused by its proof. `NativeGroupDeterminant.lean` reproduces it with native/Mathlib imports.

The proof constructs a delta function in the scalar-extended evaluation span. Its group matrix is an invertible permutation matrix. Each component determinant polynomial is consequently nonzero; their finite product is nonzero; the original characteristic-zero field is infinite, so a point of that field avoids all zeros simultaneously. The seed is therefore constructed over the original field, rather than assumed to exist.

## Finite-character target spanning

`NativeAllPlaceEigenGenerators.lean` proves
`RHLean.Geometry.nativeExists_allPlace_short_eigen` from the original
`GlobalTheory.CovGminTop.exists_short_eigen` construction. It explicitly forms
the unnormalized twisted trace, proves that every finite-character coefficient
is integral and has norm one at every complex embedding, and bounds each output
by the actual group cardinality times the input bound. The outputs lie in the
same integral lattice and span the character eigenspace over the original
field. Division by the group cardinality is used only in the field-span proof;
the integral vectors and their norm estimates are never divided.

## Actual cusp-section suppliers: source declarations

The native generic construction matches the following concrete upstream objects.

| Native input | Actual upstream object or proof |
| --- | --- |
| Component spaces $V_z$ | `cuspOn Y.U Z (wtOf ...)` |
| Ambient space $V$ | `cuspW ...`, or its subtype `Y.V ...` |
| Component and ambient lattices | `latOn Y.U Z ...` and `latW Y.U ...`; `AllWt.mem_latOn` preserves the actual lattice |
| Component spanning | `GlobalTheory.CuspSplit.iSup_cuspOn` and the full span conclusion from each generator construction |
| Determinant support size $q$ | `ShortDet.comp_unique` and the orbit of a component idempotent under the actual subgroup $S$ |
| At most one active component at a point | `ShortDet.eq_of_mem_framesOn` |
| Zero pointwise norm off the component | `ShortDet.homN_eq_zero` |
| Pointwise norm of a sum | `ShortDet.homN_sum_le` |
| Pointwise/Petersson comparison | `SupBdWt`, supplied in the short-section proof by the Tamagawa/sup-bound theorem |
| Orbit evaluation independence | `GlobalTheory.OrbitSep.separate_orbits_by_cusp` |
| Regular seed | `GlobalTheory.OrbitSep.exists_cusp_regular_level_determinant` and the finite group-determinant construction |
| Quantitative integral generators | `GlobalTheory.ShortGenComp.short_generator_comparison` |

The complete source endpoint is [ExistsShortIntegralVectorOfDeterminantBound.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/HodgeBundleWeights/ExistsShortIntegralVectorOfDeterminantBound.lean), theorem `GlobalTheory.ShortDet.exists_short_integral_vector`, exported as `GlobalTheory.T.exists_short_integral_vector_of_determinant_bound`.

In this paragraph only, write $f_A=D.R.f$ and $r_A=D.R.r$ for the original
host/unitary parameters, and $Z_0=f_A r_A L_b$. These differ from the coefficient-field
degree $d$ and the component section-space rank bound $r$ above. The proof selects

\[
\beta=e^{C_1Z_0^3},\qquad
\Lambda=e^{2C_3Z_0^9},\qquad
N=e^{C_3Z_0^3},\qquad
|S|\le e^{120(f_A r_A)^2L_b}.
\]

The finite section bound is $N|S|^2\beta\Lambda$. It is absorbed into
$\exp((3C_3+240+C_1)Z_0^9)$, then the genuine pointwise multiplication estimate `normW_mul_pull_le` yields the all-place operator bound on multiplication by every translated section. The parent's numerical absorption module handles the subsequent map cost $q^3B^2$, retaining that exact exponent.

## The actual short spanning family

[ExistsGoodCoverAtMinimalLevel.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/HodgeBundleWeights/ExistsGoodCoverAtMinimalLevel.lean), theorem `GlobalTheory.CovGmin.minimal_level_cover_is_good`, constructs an actual theta spanning family. Its proof begins `intro _`: its displayed `PublishedHodgeBundleTheorems` argument is unused.

The actual suppliers are:

- `GlobalTheory.CovGmin.span_thFam`: theta family spans.
- `GlobalTheory.RawThetaSup.homN_smul_raw_le`: actual raw theta pointwise bound.
- `GlobalTheory.T.exists_bounded_integer_goodCover_thetaSeries_integral`: actual positive clearing integer and its logarithmic bound.
- `GlobalTheory.CanonConn.exists_isNab_uncond`: canonical connection.
- `GlobalTheory.T.exists_small_scalar_reflexIdeal_selfDualLattice`: scalar with the exact lattice-index/ideal cost retained.

The proof uses the constructed scalar and clearing integer on the same theta family and obtains simultaneous ambient and component Petersson bounds. [ShortSpanCompositionClosed.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/HodgeBundleWeights/ShortSpanCompositionClosed.lean) then multiplies this family by two explicitly constructed twisting sections to reach the requested weight and component. It retains the bad-prime logarithm, coefficient-field root discriminant, flat-line constant, and archimedean factors.

The bad-prime bound `GlobalTheory.BadLogCov.log_sum_bad_primes_le_sq` also ignores the displayed Hodge package and proves an explicit constant $37$. This does not eliminate the package everywhere: CM-point unramifiedness and the orbit-separation/bigness arguments genuinely use its relevant theorems. The independent audit agent is assembling closed values of all six packages used by the complete short-section theorem and compiling an actual-source wrapper.

## Compatibility of evaluations and the actual section algebra

The native group-determinant constructor establishes nonvanishing at the
component orbit evaluations. To attach it to the actual section algebra,
upstream additionally proves `levDet_mem_secZ` and applies
`GlobalTheory.T.integerExponentSection_mul_eq_zero_imp_eq_zero` at the actual
component points chosen by `separate_orbits_by_cusp`. This converts those
nonvanishing determinants into the required non-zero-divisor statement.
Arbitrary finite evaluations alone do not supply that implication. The native
dependent-field selector separately supports the original generic-point
fields `Om Z`; no identification of generic-point fields with an arbitrary
chosen evaluation is asserted.

## From the constructed section to actual maps

[MapsBoundOfDeepGood.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapsBoundOfDeepGood.lean), `GlobalTheory.CovTop.DescentMaps.mapsCore`, chooses $q=|S|$ and explicitly constructs

\[
\phi_k=\operatorname{proj}_{e(k)}\circ\operatorname{cuspPh}_{S,\chi,u}.
\]

The same actual section $u$, subgroup $S$, character $\chi$, and lattices occur throughout. The proof uses:

- `cuspPh_mem_chiLat` for integral lattice membership;
- `levPh_injective_of_levDet_nonZeroDivisor` for joint injection;
- `sum_sq_normW_cuspPh_le` for the exact collective $q^3B^2$ bound at every place;
- `card_mul_rkK_chiLat_le_rankW` for the genuine target-rank comparison.

Thus the remaining native integration is a faithful use of these actual source objects and their closed suppliers. The finite constructor extraction supplies their arithmetic construction step; it does not relabel a desired RH bound as a geometric hypothesis.


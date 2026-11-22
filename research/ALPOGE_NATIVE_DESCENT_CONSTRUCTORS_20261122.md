# Finite descent: actual theorem and original constructor dependencies

## Verified source pins

- Native baseline: `OVVO-Financial/RH_Lean@608b5702a20ab34a9efcd38b5d59e09f9f565f61`.
- Original geometry: `CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.
- Native mathlib: `leanprover-community/mathlib4@d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Native Lean: `leanprover/lean4:v4.34.1`.

All source statements below were read at those pins. New native proofs have only
been submitted to hosted checking; no local Lean process was run.

## Native finite theorem now drafted

Let A and B be actual Euclidean integral lattices of ranks r and N=r+d. Their
metrics are fixed before selecting the map. Let f be an injective real linear
map carrying A into B, with norm at most exp(P). Suppose S is a set of actual
vectors of B spanning its real vector space, each of norm at most exp(Lambda).

`nativeCompletionFromSpanningSet` extends the image of an integral basis of A
inside `image ∪ S`. It selects exactly d elements of S. They do not need to
form a Z-basis of B. `nativeIntegralCompletionFromSpanningSet` constructs their
full integer coordinate matrix C and proves det C != 0 using the resulting real
basis. Thus no nonsingular completion matrix is requested as an assumption.

`nativeIntegralDescent_with_completion` proves

    (det C)^2 GramDet(B) <= GramDet(A) exp(2 r P + 2 d Lambda).

The argument constructs the map f plus the d actual completion vectors on
the orthogonal direct sum U + R^d. The auxiliary standard lattice has Gram
determinant one. Gram transport is exact; Hadamard is proved through actual
Gram--Schmidt coordinates, without a factorial or dimension-power loss.

Since det C is a nonzero integer, its absolute value is at least one. Hence
`nativeIntegralDescent_from_generators` proves the complete finite volume
inequality from the original map and the actual integral spanning set.
`nativeIntegralDescent_slope` proves the exact normalized conclusion

    mu(B) >= r/(r+d) (mu(A) - 2 P) - 2 d Lambda/(r+d),

where mu(L) = -log GramDet(L)/rank(L). No slope bound is a hypothesis of this
theorem. The map norm and generator bounds are ordinary finite geometric data,
and are not estimates for Gz or the complete arithmetic source.

This is a Euclidean Z-lattice theorem. It is not yet identified with the
original number-field `slope_sq` normalization.

### Genuine map count q

For q jointly injective maps A -> B, the target is the Hilbert direct sum B^q,
of rank q rank(B). Its norm squared is the sum of the q squared norms. Each
short generator of B is placed in one coordinate of B^q. Its norm remains
at most exp(Lambda); no sqrt(q) factor is needed. Here N=q rank(B),
d=N-rank(A). Neither q nor d can be replaced by a convenient synthetic value.

## Original finite descent theorem

Path:
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HtMapLeOfPoints.lean`

Declaration: `GlobalTheory.DescentFamily.descent`.
Blob: `87a9932805b500be9ac51c3250f6dc314b5f3f25`.

Its inputs are one totally complex number field K, K-spaces V and W, actual
finitely generated O_K-submodules A and B, genuine Gram norm families NA and NB,
a nonzero A, and maps phi_h indexed by Fin q satisfying:

- Every phi_h sends A into B.
- If all phi_h(v)=0, then v=0.
- At every embedding sigma, sum_h NB_sigma(phi_h(v))^2 <= exp(2P) NA_sigma(v)^2.
- There is a set s of actual vectors in B, of norm <= exp(Lambda) at every
  embedding, whose K-span contains B.
- Lambda, epsilon >= 0 and q rk_K(B) <= (1+epsilon) rk_K(A).

Its conclusion is

    t <= slope_sq(A)-2P
    implies slope_sq(B) >= t-epsilon(|t|+2Lambda).

The proof constructs the joint map `LinearMap.pi phi` into B^q. Its direct
inputs are `Formalism.ExtensionFiltration.descentSlope`,
`Formalism.ExtensionFiltration.spanMuMin`, and
`Formalism.BranchingDeterminantCap.power_slope_mu`. These are geometric slope
theorems, not the terminal RH theorem.

## Actual integral-map constructor

Path:
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapsBoundOfDeepGood.lean`

Declaration: `GlobalTheory.CovTop.DescentMaps.mapsCore`.
Blob: `c057c3493fb3555ae5ba47c97ed60f49ba67e2eb`.

Its concrete objects include the original moduli/level/coefficient/Gram data,
a finite subgroup S of level automorphisms, its character chi, weights
Gm+W=G and G+W=Gp, and an actual integral cusp section u of weight W.
The constructor chooses q=card S and the maps

    phi_k = LinearMap.proj (e k) composed with cuspPh S chi u,

where e : Fin(card S) ~= S. Its three decisive geometric premises are:

1. u belongs to the integral cusp lattice.
2. `levDet Xo c S u` is a non-zero-divisor on `secRing Xo c`.
3. Multiplication by every translated section `pull gamma u` has norm <= B
   in the original metrics; card(S)^3 B^2 <= exp(2b).

It obtains integrality using `GlobalTheory.LevDesc.cuspPh_mem_chiLat`,
joint injectivity using `GlobalTheory.levPh_injective_of_levDet_nonZeroDivisor`,
the collective norm using `GlobalTheory.sum_sq_normW_cuspPh_le`, and the
first rank inequality using
`GlobalTheory.CovolRank.card_mul_rkK_chiLat_le_rankW`.

These are actual multiplication/translation maps. A coordinate isometry or
the centered action of the finite signed Selberg matrix does not produce u,
the non-zero-divisor assertion, or the rank inequality.

### Short section supplying the constructor

Path:
`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/CoveringDescentMapsCompatible.lean`

Declaration:
`GlobalTheory.CovTop.DescentMaps.covering_descent_maps_compatible_alt`.
Blob: `6fb20c1e98035bff56a28e04480bd42182e0bf84`.

It calls `GlobalTheory.T.exists_short_integral_vector_of_determinant_bound`,
obtaining the SAME u, its integral membership, its levDet non-zero-divisor
property, and its translated multiplication bound. It also calls
`GlobalTheory.T.exists_psi_isTypeLevel_latDeep_eq_latN` to identify the actual
deep lattice with the character/level lattice.

With z=(host factor)*(rank factor)*(logarithmic scale), the squared collective
norm bill is bounded by

    card(S)^3 exp(C z^9)^2
      <= exp(135 z^2+2 C z^9)
      <= exp(2 b).

The older explicit supplier has the following fully exposed signature:

Path:
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUniformHeightConstantStatement.lean`

Declaration: `GlobalTheory.T.exists_uniform_height_constant`.
Blob: `09e2543163f6149a9b9f4663b929fa9b66745ccf`.

From Hypotheses2 plus the stated Grothendieck deformation, HSCore,
Siegel-integrality, toroidal-fan, and semiabelian Lie inputs, it obtains C>=0
such that each compatible good cover, weight and level frame admits an
integral u with the levDet property and translated multiplication norm
exp(C z^9). The native coefficient-frame certificate does not instantiate
these geometric hypotheses.

## Genuine small generators: a distinct constructor

Path:
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MinimalGenusBound.lean`

Declarations:
`GlobalTheory.CovGminTop.exists_short_eigen`,
`GlobalTheory.CovGminTop.gminAt_of_gens`, and
`GlobalTheory.CovGminTop.gmin`.
Blob: `b04dcfb0b738b65b5bf049c02ec03e58d5771fe9`.

The finite reusable content of `exists_short_eigen` is particularly clear.
Let a finite group H act linearly, preserve an actual O_K-lattice Lambda,
and act isometrically at every embedding. Let chi : H -> K^units. Start from
an ACTUAL integral K-spanning set s with all-embedding norm <= B. Its
unnormalized twisted traces

    sum_h chi(h)^(-1) * st(h)y,  y in s,

are integral, belong to the chi-eigenspace, have all-embedding norm <= |H| B,
and span that eigenspace over K. The character values are proved algebraic
integers and have complex norm one using their finite orders. Spanning uses
the genuine twisted-trace identity on eigenvectors.

The trace is deliberately unnormalized: dividing by |H| before integrality
has been established would discard a real denominator cost.

`gminAt_of_gens` applies this to the actual level action and deep character
lattice. If the original section generators have bound exp(B), the price is

    log |S| + B <= PP * kappa.

The resulting short eigen-generators have bound exp(PP*kappa). The newer
`ThirdPlaceSeries/CoveringMinGenusBound.lean`, declaration
`GlobalTheory.CovGminTop.covering_gmin_of_gram_deep_size`, calls
`GlobalTheory.T.exists_good_cover_at_minimal_level` to supply the original
section generators, then uses the same `gminAt_of_gens` mechanism.
Blob: `0780e778b125ccd21b277f7b9adac713540ec94c`.

A native unnormalized trace theorem would reconstruct a genuine finite part
of this mechanism. It would still require the original short section
generators; it would not establish their existence.

## Near rank saturation

Path:
`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/RankGrowthBoundSmallScale.lean`

Declaration: `GlobalTheory.CovTop.HodgeSteps.rk_le_alt_alt`.
Blob: `69dbd84e4f2a3b3ef8fa131305bccc78453692fd`.

This supplies the bound of the larger shifted-weight rank by

    (1+min(1/2,b/(PP*kappa))) times the lower shifted-weight rank.

Its proof consumes actual valuation multiplicity runs, jet-order estimates,
weight gaps, component degree comparisons, cover degrees and share bounds.
It is not a consequence of the abstract dimension of the native colour host.

The exact input predicates appear in
`src/Development/AbelianVarietyTheory/Definitions/Divisors/CovolXOfCovol.lean`:
`MapsAt`, `RkAt`, `GminAt`. Blob:
`4ed4695093989e1f18246a3244b79102db6c548e`.

The actual invocation appears in
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LowerBoundOfAllEstimates.lean`,
`GlobalTheory.CovTop.LowCover.lowAt_of_cover`.
Blob: `4d30dd405b7d5b26d61d37507a095cc7ef426dc5`.
It uses P=b, Lambda=PP*kappa, epsilon=b/(PP*kappa), proving PP*kappa>0.
Consequently 2 epsilon Lambda=2b, a genuinely paid rank-defect cost.

## What is and is not supplied natively

At the native baseline,
`RHLean/Geometry/NativeIntegralLatticeCertificate.lean` (blob
`6ce376b09d73dc1994b03c2390f5de342b6fbb56`) proves integer parity/image,
divisibility, exact Gram/metric transport, arithmetic coefficient-basis
transport, ideal-depth transport, and all-place norm equality under the
specified coordinate equivalence. It does not construct the short cusp u,
its level determinant, a short section spanning set or the geometric rank
comparison. None was found among those native data.

There is therefore a real native finite descent theorem under development,
but no identified native theta/cusp instance satisfying the complete supplier
contract yet. A faithful instance must use one common original cover/host,
section lattice and norm family for integrality, joint injection, rank and
short generators. Reusing separately convenient finite models would not do.

## Number-field normalization still required

The original theorem uses O_K-submodules and its arithmetic `slope_sq`.
The current native theorem uses an honest Z-lattice in a real inner product
space. An O_K-integral generator set spanning over K does not automatically
give a Z-spanning set with the same norm bound: multiplying by an integral
basis of O_K can introduce genuine field-basis and discriminant costs.

A promising exact next lemma is an all-embedding determinant inequality for
one common O_K coordinate matrix C. The nonzero integer Norm_K/Q(det C)
has absolute value at least one, so the product formula supplies the needed
global determinant credit without treating an individual embedding's
determinant as an integer. That lemma must use one common K-basis completion
and the original all-place Gram metrics. Extending it from free coordinate
lattices to the original projective O_K-submodules also requires actual
ideal-index/covolume accounting. No such normalization theorem is claimed
by the present drafts.

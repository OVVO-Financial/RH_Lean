# Finite descent: actual theorem and original constructor dependencies

## Verified source pins

- Native baseline: `OVVO-Financial/RH_Lean@608b5702a20ab34a9efcd38b5d59e09f9f565f61`.
- Original geometry: `CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.
- Native mathlib: `leanprover-community/mathlib4@d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Native Lean: `leanprover/lean4:v4.34.1`.

All source statements below were read at those pins. The native finite-descent,
constructed-completion and normalized-slope modules have passed hosted
compilation during this PR. Acceptance of the delivered PR head is determined
by its exact-head hosted checks. The additional two-point diagnostic also
passed hosted module compilation; its observed axiom list contains only
`propext`, `Classical.choice` and `Quot.sound`. No local Lean process was run.

## Native finite theorem with constructed witnesses

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

There is therefore an implemented, hosted-checked native finite descent theorem,
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
by these native modules.

## Extended native supplier audit at 608b5702

The following are statement-level checks of additional native candidates,
not an inference from filenames. None is being dismissed as merely formal:
several retain genuinely useful signed arithmetic data. The missing item is
their identification with the SAME original sectional lattice and metrics.

* `RHLean/Proof/HeightShellGram.lean`, blob
  `d2c418fec2b2176abc02fafae1dc60c5c20290c3`:
  `RHLean.Analysis.energy_sum_heightShells` proves the exact diagonal plus
  full signed off-diagonal energy identity for arbitrary Hilbert-space
  vectors. It supplies neither integrality nor an estimate on those vectors.
* `RHLean/Proof/HeightShellReconstruction.lean`, blob
  `2cbd9c4316ecf77c5dbf44b1e6937e410b30f780`:
  `finiteAmplitude_shell_reconstruction` and
  `canonicalHighPrefix_shell_reconstruction` retain the actual canonical
  high-sector Mobius atoms. `norm_finiteAmplitude_sq_le_of_shell_bounds`
  explicitly takes diagonal, equal-height and each-shell bounds as inputs.
  Its arithmetic height label is not yet identified with the height of a
  theta section or with an all-place covolume.
* `RHLean/Proof/JointGramControl.lean`, blob
  `2307fe20a708375ff806cab6c07715954be53497`:
  `actualResidual_energy_eq_jointGram` is an exact full signed identity for
  the actual residual. The consumers
  `actualResidual_energy_le_of_jointGram_control` and
  `actualResidual_energy_le_of_jointGram_recurrence` take their quantitative
  `hcontrol` as a hypothesis. Scalar coefficient interactions do not
  construct the original higher-rank section lattice: their complex scalar
  Gram has rank at most one if treated as a Gram of the scalar coefficients.
* `RHLean/Analysis/NNSFiniteSelmerFourierIntegral.lean`, blob
  `faa41438966e5e050eef5dd09e825a230638bb59`:
  `nnsFiniteRelationMass_eq_UPM_sub_LPM_target` and
  `nnsFiniteRelation_fullCharacterDetector` identify the exact finite kernel
  count, including target mass and all additive characters. The constraint
  map L is arbitrary, so these identities alone cannot give a nontrivial
  rank or kernel-cardinality bound (L may be zero). A finite-level Sha
  instance still needs its actual cochains and local coboundaries.
* `RHLean/Analysis/AlpogeNativeClassGroupNNSIntegral.lean`, blob
  `ee019037c16562fd7abf5ad0a16228c737850187`:
  `alpogeNativePrimeCl`, `alpogeNativeClDualConstraint` and
  `alpogeNativeClDualMass_eq_char_card` really use the number field K,
  its ring of integers and selected prime ideal classes. Thus there IS
  genuine field-specific native data. The exact character count does not
  bound it, construct the missing Sha comparison, or give maps to the
  K-vector spaces of theta sections used by the descent.
* `RHLean/Analysis/AlpogeNNSBandSchur.lean`, blob
  `d567392c73d134331d0ec99eebd3ee2f12c15ac7`:
  `alpogeNNSBandCharge_le_negative_principal` proves actual negative payment
  for the proper near-root prime band. The complete-source theorem
  `alpogeNNSBandOneSidedCharge_le_principal_overshoot` keeps an arbitrary
  signed complement C explicitly in the remaining positive-part expression.
  The indefinite 2I-J signed kernel is not itself a positive lattice Gram.
  This useful band payment supplies neither short section generators nor
  the original rank comparison.
* `RHLean/Analysis/PhysicalPartialMomentSchur.lean`, blob
  `0044e47f4222544a5e8ff21e4d031de1b048571a`:
  `q2RecoveredDegreeOneBulk_in_affineSynthesisRange` gives a genuine
  three-residue incidence representation of the recovered degree-one bulk.
  `q2RecoveredDegreeOneBulk_coefficientEnergy` pays exactly one half of the
  residue energy through canonical rational half-split coefficients. These
  are not an integral generator certificate for the original theta lattice;
  clearing the denominator would have a real cost. The same file proves
  `q2ExceptionalOwnerGram_three_sharp`, `q2CenteredToy_cross_eq_four` and
  `q2GenericAlignedThirteenSeventeen_not_halfFrame`, so local centering or
  reciprocal-square weights cannot simply be promoted to the needed joint
  norm improvement for arbitrary transported fields.
* `RHLean/Proof/ActualForcingEstimates.lean`, blob
  `429e7fcda2d40a4e617103517c465b697837cc69`:
  derives finite incidence/forcing sums from explicit separation, envelopes
  and endpoint bounds stored in its input structures. It does not prove
  those bounds for the original cover or sectional lattice.
* `RHLean/Proof/AlpogeVerifiedRHSubpowerFiniteC.lean`, blob
  `61c38007009d4f37187ec8c2ac17bfca97d3003d`:
  `alpogeNativeTwoWallSubpower_of_halfGrowth` explicitly assumes the
  RH-strength `AlpogeNativeMertensHalfGrowth`. This cannot supply the missing
  independent descent estimate.

A meaningful reverse-search target is now precise: construct a K-linear,
integral coefficient realization of the ACTUAL section space for one fixed
cover/character, prove its original all-place Gram comparison, then express
the actual cusp multiplication/twisted-trace maps in those same arithmetic
coordinates. Exact shell and joint Gram identities could preserve covariance
through that comparison. Until the representation and norm comparison exist,
native host cardinalities, scalar residual energies, and field-specific
finite character counts are different quantities from the sectional rank
and small-generator budgets in `MapsAt`, `RkAt` and `GminAt`.

## A finite diagnostic for the q-cubed norm bill

The following exact calculation explains why joint injection, integrality
and rank saturation do not automatically remove the q-cubed operator-norm
bill. It is a diagnostic function-algebra model, not a native theta instance.
The general-q argument below is a human proof. Its explicit two-point instance
is formalized in `RHLean/Geometry/NativeTwistedTraceDiagnostic.lean`, included
in the root manifest and guarded axiom audit. Hosted compilation of that module
has passed. The general-q calculation remains a human derivation; the
delivered PR's final checks also validate the guard-message expectations.

Let H be a finite abelian group of order q>0, act by translations on real
functions on H, and use the normalized norm

    ||f||^2 = (1/q) sum_g |f(g)|^2.

Take the integral function u=L*1+delta_e, for a positive integer L, and the
trivial character. The unnormalized traces of multiplication by translated
u are constant functions whose constant values are

    phi_h(f) = L * sum_g f(g) + f(h).

The joint coordinate matrix is I+L*J. It is integral and injective, with
determinant 1+q*L. The source rank is q, the invariant target rank is one,
and q times the target rank equals the source rank. The group matrix of
translated u is a permutation of I+L*J at every point of the function
algebra, so its pointwise determinant is nonzero as well.

Multiplication by any translated u has operator norm B=L+1. On the constant
input f=1, the squared collective target norm is

    sum_h ||phi_h(1)||^2 = q*(1+q*L)^2.

In fact this is the squared joint operator norm: I+L*J has eigenvalues
1+q*L on constants and 1 on their orthogonal complement, while the source
norm is normalized by 1/q. The ratio to the original q^3*B^2 bound is

    (1+q*L)^2 / (q^2*(L+1)^2),

which tends to one as L tends to infinity. Thus a universal improvement
from q^3 to q^2 or q cannot follow just from the finite group action,
unnormalized character trace, integral nonsingularity and rank saturation.
Extra quantitative structure of the actual theta sections, or actual
determinant/singular-value credits retained jointly, is needed. This does
not establish that the q^3 bound is sharp on Alpoge's particular sections.

Here is a full finite proof, including the normalizations. Write the group
additively and let (T_h u)(g)=u(g-h). The trivial-character unnormalized
trace is the constant function Tr(v)=sum_g v(g). Thus

    Tr(f*T_h u) = sum_g f(g)*(L+1_{g=h})
                 = L*sum_g f(g)+f(h).

Translation permutes H, hence preserves the integral function lattice and
the normalized norm. Pointwise multiplication by T_h u is bounded by L+1,
and equality is attained on delta_h, so B=L+1 is the exact operator norm.
The target lattice of invariant functions is generated by the constant
function 1, of norm one. Every trace coordinate is integral on integral f.

Set c=(sum_g f(g))/q and f0=f-c*1. Then sum_g f0(g)=0 and

    ||f||^2 = c^2+(1/q)*sum_g f0(g)^2,
    phi_h(f) = (q*L+1)*c+f0(h).

After summing over h the mixed term vanishes EXACTLY, giving

    sum_h ||phi_h(f)||^2
      = q*(q*L+1)^2*c^2+sum_h f0(h)^2
      <= q*(q*L+1)^2*||f||^2.

Equality holds for f=1. The joint matrix A=I+L*J acts by 1+q*L on the
one-dimensional constant subspace and by 1 on its (q-1)-dimensional
zero-sum complement, proving det A=1+q*L, joint injection, and the exact
operator norm. The section-source rank analogue is q, and q copies of the
one-dimensional invariant target have rank q: the rank defect is zero.

The pointwise group determinant is also nonzero. At x in H its matrix has
entries L+1_{x=h+k}. For each h there is exactly one such k, so this matrix
is L*J+P_x for a permutation matrix P_x. Since P_x*J=J, it equals
P_x*(I+L*J), with determinant det(P_x)*(1+q*L), which is nonzero. This is
the actual finite translation/multiplication/trace model of the injection
mechanism. No change of source or artificial multiplicity is involved
inside this model; it remains distinct from the actual theta section ring.

For a completely explicit diagnostic, take H=Z/2Z and L=2. Then

    u=(3,2),  T_1 u=(2,3),
    phi_0(x,y)=3x+2y,  phi_1(x,y)=2x+3y,
    A=[[3,2],[2,3]],  det A=5.

The normalized source energy of (1,1) is (1^2+1^2)/2=1. Its joint target
energy is 5^2+5^2=50, while q^2*B^2=2^2*3^2=36. Therefore the proposed
q-squared improvement fails even with a nonzero integer determinant and
exact rank saturation. The q-cubed bound gives 72 and is valid. More
precisely, for every real (x,y),

    (3x+2y)^2+(2x+3y)^2
      = 25*(x^2+y^2)-12*(x-y)^2
      <= 50*((x^2+y^2)/2),

with equality on constants. This also shows directly that the squared
collective operator norm is exactly 50 in the stated original metric.

There is a crucial distinction between this sharp OPERATOR norm and the
VOLUME cost. In this same model the source orthonormal basis is sqrt(q)
times the coordinate basis, so the exact image Gram determinant is

    det G(F(ON_source)) = q^q * (1+q*L)^2.

The large eigenvalue appears only once. Repeating the largest squared
singular value once per dimension would instead give
q^q*(1+q*L)^(2*q), which can be much larger. The exact identity
`nativeMap_gramDet_source` retains the former quantity before any Hadamard
or operator bound. Integer-index credit is likewise retained in
`nativeIntegralMap_gram_bound` before its final corollary discards it.

Thus this diagnostic does not rule out a substantially sharper JOINT
determinant payment. A concrete candidate is to prove, on the original
section source, that its map Gram has a controlled bulk plus an explicit
correction of rank k, then pay only k log(1+lambda) for a correction with
eigenvalue excess at most lambda. For example, a bound
F*F <= exp(2P)*(I+lambda*Pi), with Pi an actual orthogonal projection of
rank k, would cost 2rP+k*log(1+lambda) in log determinant, rather than
r*(2P+log(1+lambda)). This requires a proved same-source Gram comparison;
it is not supplied by arbitrary scalar centering. Its formalization and
theta instantiation are not claimed in the present patch.

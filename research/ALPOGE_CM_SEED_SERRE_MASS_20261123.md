# Native CM seed, projective tensor and measured degree construction

## Status and exact scope

This work continues main `4b9881be8fcb2b0b817afe5008d29adbcd829a5c`
(PR #1200), in [PR #1201](https://github.com/OVVO-Financial/RH_Lean/pull/1201).
The complete native signed-source estimate and RH remain **OPEN**.
The new proofs are subject to the hosted compilation and terminal-axiom audit
recorded on that PR; source construction is not a claim of a green build.

The construction retains the actual native host, the same half-different
`B`, the original coefficient module `M = B^-1`, the prescribed lattices
`M^(k+m-1)`, and their exact integral trace polarization. It does not replace
that projective module by a free module. The literal period image and actual
measures enter the calculations below.

```text
descent_payment_ack=ALPOGE_NATIVE_DESCENT_PAYMENT_V1
tractability_ack=ALPOGE_VIOLE_TRACTABLE_RH_V1
ROLE=user-directed manual Lean continuation
SOURCE=original native host, inverse-half-different, EF and signed ASK source
NORMALIZER=Q=card(TT)*m*b*Delta/2; unchanged
FORMAL_STATUS=hosted verification in progress; no local Lean/Lake execution
GLOBAL_STATUS=OPEN
```

## 1. The actual quadratic order and its rank cost

`NativeCMQuadraticOrder.lean` constructs `O_K = Z[w0]` inside the native
`O_E`, using `2w0=1+sqrt(-d)`, rather than introducing an unrelated quadratic
field. It proves unique coordinates `a+b*w0`, the involution `w0 -> 1-w0`,
the quadratic equation, integral closedness and the Dedekind property.

`NativeCMOrderIdentification.lean` then proves that this literal subring is
the full ring of integers of `Q(G.rt)`. For the constructed native host this
is exactly `HostRaw.K = Q(sqd)`, the field in the relative different
calculation. The ring equivalence commutes with the actual inclusion into
`O_E`, maps `w0` to the integral half-root, and preserves its scalar action
on every original `O_E` module. The proof uses the existing native quadratic
integral-basis and degree-two theorems.

For the original finite projective `O_E` module, restriction to `O_K`
remains finite projective. Its rank is proved to be

\[
\operatorname{rank}_{O_K}M
 =\frac{[E:\mathbf Q]}2\operatorname{rank}_{O_E}M.
\]

In particular the coefficient ideal has `O_E` rank one and `O_K` rank
`[E:Q]/2`. The whole prescribed lattice has tensor dimension
`[E:Q]*(k+m-1)/2`. Rank one over the larger coefficient ring does not
make the tensor construction an elliptic curve of dimension one.

## 2. A polarized analytic seed on the actual order

`NativeCMEllipticSeed.lean` and `NativeCMEllipticPolarization.lean` use an
actual complex embedding `tau` of the native field. Put `omega=tau(w0)`.
The period map is the literal embedding

\[
O_K\longrightarrow\mathbf C,\quad a+bw_0\longmapsto a+b\omega.
\]

The proofs construct its real basis, show the lattice is discrete and full,
and construct the compact additive quotient with its actual `O_K` action.
Both signs of `Im(omega)` are retained. The positive Hermitian form is

\[
H_0(z,w)=\frac{z\overline w}{|\operatorname{Im}\omega|},
\qquad |\operatorname{Im}\omega|=\frac{\sqrt d}{2}.
\]

For coefficient pairs `(a,b)` and `(c,e)`, its imaginary part is exactly
`sgn(Im omega)*(b*c-a*e)`. That integer form is alternating, unimodular and
adjoint to the actual CM involution. The tangent normalization is

\[
\pi H_0(1,1)=\frac{2\pi}{\sqrt d}.
\]

This is a constructed, principally polarized analytic lattice and compact
quotient. The quotient type is not silently declared to be an integral
polarized elliptic scheme. Its period shape has normalized analytic scale
one; the algebraic invariant differential's scale still requires its own
comparison theorem.

### Integral equation and exact comparison of its invariants

The `NativeCMWeierstrass*` proof chain goes beyond an analytic quotient.
It uses the actual modular invariant `E4(tau)^3/discriminant(tau)` and
proves its integrality at the actual quadratic period. The upper-half-plane
period is `omega` or `1-omega`, and an exact lattice equality proves that
this orientation choice preserves `Z+Z*omega`.

The finite-model construction gives a number field `M` contained in `C`,
containing the chosen image of the original native field, and an actual
Weierstrass equation `W` over `O_M` with `Delta(W)=1`. Its original
`j` invariant equals the analytic `j` of that same lattice; the integral
CM generator is included in the same field. This is not an elliptic
equation chosen from an independently supplied algebraic `j` witness.

`NativeCMWeierstrassSeedComparison.lean` constructs a genuine complex
Weierstrass coordinate change `C` such that `C • W_C = latticeCurve(Lambda)`.
Writing `u=C.u`, the comparison retains

\[
u^4\,12g_2(\Lambda)=c_4(W),\qquad
u^6\,216g_3(\Lambda)=c_6(W),
\]

\[
u^{12}\Delta_\Lambda=1,\qquad
u^{12}(2\pi)^{12}\Delta_{\rm modular}(\tau)=1.
\]

These equations retain the actual algebraic-to-analytic coordinate scale.
They do not establish the all-embedding arithmetic Lie-norm mean. The
source obtains that mean through CM isogenies, integral derivatives at
good reduction and the product formula, not by setting `u=1`.

`NativeCMWeierstrassSeedPoints.lean` also constructs the actual additive
uniformization of `W_C.toAffine.Point`, using the proved Weierstrass-function
addition theorem and the same coordinate change. Its kernel is precisely
the original seed lattice. Away from that lattice the coordinates are

\[
x(z)=u^2\wp_\Lambda(z)+r,\qquad
y(z)=u^3\wp'_\Lambda(z)/2+u^2s\wp_\Lambda(z)+t.
\]

The original order action is transported through this proved point-group
equivalence and intertwines with multiplication of `z` by the actual CM
embedding. The quadratic CM equation holds on the actual curve points.
This proves a point-group and module comparison; it does not assert that
every such point endomorphism has already been represented by an integral
scheme morphism.

### The actual integral group scheme and its tangent generator

The twelve new scheme modules ending in
`NativeCMWeierstrassIntegralSchemeSeed.lean` construct the actual projective
Weierstrass scheme of that same equation over `O_M`. The algebraic addition
charts are glued and their group identities proved over the reduced base.
The resulting group scheme is smooth, proper and geometrically connected.
Its integral dual-number tangent vector is literally `[epsilon,-1,0]`;
every tangent vector is uniquely `[c*epsilon,-1,0]`. The complex affine
point equivalence joins this scheme's points to the existing exponential
with the exact original period kernel. Algebraicity of the transported CM
action and the polarizing line bundle still require proofs.

`NativeCMWeierstrassAnalyticTangent.lean` removes the actual poles of
`wp` and `wp'` and computes the derivatives of the origin-chart coordinates
`-x/y` and `-1/y`. They are exactly `1/u` and zero. Consequently the
analytic direction `z=u`, with the original coordinate-change unit,
has first jet `[epsilon,-1,0]`. The proof identifies this jet as a scheme
morphism with the scalar extension of the specified integral tangent
generator. A joint existence theorem retains the same field, equation,
coordinate change, exponential and nearby coordinates throughout.
Thus the tangent scale in the period formula is tied to the actual
integral generator; the mean over its arithmetic conjugates remains open.

### Exact analytic CM period, with the original seed in the class-group mean

The five modules from `NativeCMKroneckerIntegral.lean` through
`NativeCMChowlaSelberg.lean` reconstruct the sum/integral estimate,
Kronecker limit formula, quadratic ideal-count factorization, ideal-class
period lattices and Chowla--Selberg analytic identity directly. The mean
identity is proved from those calculations, not taken as a hypothesis.

`NativeCMArithmeticPeriod.lean` specializes them to the actual quadratic
subfield `Q(G.rt)`, proves its discriminant is `-d`, constructs its genuine
quadratic Dirichlet character, and chooses period lattices for every ideal
class. Its principal-class lattice is exactly the original seed lattice.
For `P(Lambda)=log(covol(Lambda)/pi)+log|Delta(Lambda)|/6`, it proves

\[
\frac1{h_K}\sum_{c\in\mathrm{Cl}(O_K)}P(\Lambda_c)
 =\gamma+\log(2\pi/\sqrt d)-\frac{L'(1,\chi)}{L(1,\chi)}.
\]

The equality is in `C`, with the real left side embedded explicitly. The
same module proves the exact coordinate-scale identity
`-log(pi*H0(u,u))=P(Lambda)` from `u^12*Delta(Lambda)=1` and the original
covolume. Identifying the mean over embeddings of the integral Lie
generator with this class-group mean remains the arithmetic CM step.

## 3. Exact period covolume and tangent determinant

`NativeCMPeriodComparison.lean` transfers the **original** perfect integer
pairing to the image of the already constructed native period map. For its
positive Hermitian matrix `Hm`, the proof derives

\[
\operatorname{covol}(P(M))\operatorname{Re}\det H_m=1.
\]

This is the actual Lebesgue covolume; it is not a freely selected scalar.
For any nondegenerate complex tangent basis matrix `W`, it also proves

\[
\det\bigl(\pi H_m(W_i,W_j)\bigr)
 =\pi^g\operatorname{Re}\det(H_m)|\det W|^2
\]

and the corresponding inverse-volume formula. All factors of pi, field
degree and tangent-basis determinant remain. The endpoint specializes the
comparison to the same prescribed `B^-1` lattice and period map used by the
native theta section.

The equation `covol*det=1` is invariant under simultaneous rescaling of
periods and the polarization metric. It does not identify the arithmetic
Lie generator or establish Chowla–Selberg by itself.

## 4. The actual projective module through the Serre point construction

`NativeCMHermitianForm.lean` extracts the algebraic fields of the already
constructed trace lattice. For a sign `epsilon` in `Z^×`, it builds the
unique quadratic-order form with exact formula

\[
h(x,y)=\epsilon\{EF(w_0x,y)-EF(x,y)\}
       +\epsilon EF(x,y)w_0.
\]

Linearity, conjugate symmetry, compatibility with the full `O_E` action,
perfection and a finite dual frame are proved from the original `EF`.
They are not supplied by a newly assumed Hermitian-form witness.

`NativeCMSerreTensor.lean` uses this dual frame to construct maps
`i:M -> O_K^s` and `p:O_K^s -> M` with `p i = id`. The matrix `e=i p`
is proved idempotent. Tensoring those exact maps yields

\[
M\otimes_{O_K}A\;\simeq\;\{v:e_Av=v\}.
\]

The endpoint takes `A` to be the **actual seed quotient** above, and proves
what the equivalence does to every pure tensor `x tensor [z]`. The `O_E`
action remains the original action on the first tensor factor. A global
free basis for `M` is never introduced. The number of dual-frame generators
is not interpreted as a norm or rank saving.

`NativeCMSerreEigenlatticeAlgebra.lean` proves the self-dual integral
coordinate criterion needed to retain the finite index of an eigenline.
It identifies the actual coefficient form with
`sum_sigma sigma(x*conjugate(y))` over the host automorphisms fixing the
same quadratic root. In particular its rank-one coefficient is proved to
be one. The criterion concerns the integral span over the base ring;
passing to its field span would lose the different contribution.

`NativeCMSerreEigenlattice.lean` then constructs the literal integral
tensor `O_F tensor_OK B^-1`. The coefficient action is explicitly the
base change of multiplication on the **second** factor. Scalar action
through the first factor would make the eigencondition vacuous and is
not used. The actual perfect dual frame proves that evaluation into all
root-fixing embedding coordinates is injective and that its range is
their integral `O_F` span. The identity-character axis is exactly

\[
\bigl(O_F\otimes_{O_K}B^{-1}\bigr)_{\mathrm{id}}
\simeq_{O_F}
\operatorname{ext}_{F/E}(B^{-1}\mathfrak D_{E/K})
=\operatorname{ext}_{F/E}(\overline B).
\]

The criterion is the literal condition
`t*conjugate(B^-1) subset O_F`; inversion and conjugation give the stated
different orientation. This is an integral linear equivalence, including
the lattice index, for every field extension of the same host. The native
joint theorem chooses the half-different once before those extensions.

`nativeDyadicHost_exists_coefficientSerreConstruction` chooses one actual
half-different from the host assumptions, retains its coprimality and
Galois invariance, constructs the compatibility with the geometric host,
and supplies this retraction, actual point tensor and exact rank together.
The native coefficient rank is `2*2^e`, as required by its native field
degree. It assumes no new tensor, frame or rank witness.

`NativeCMSerreEquationPoints.lean` carries that same tensor and trace-frame
idempotent to the actual point groups of the constructed integral
Weierstrass equations. Its joint theorem selects one `B`, then the positive
and conjugate seed equations and their coordinate changes, before all
`k,m,j`. It retains both discriminant-one identities, both nontrivial
`u^12*Delta(lattice)=1` period scales, the exact original mixed period
kernel, and the full `O_E` action. The equations currently live in separate
finite subfields of `C`; an arithmetic scheme construction must also place
them in a common finite compositum.

### Represent the original trace-frame tensor and its integral Lie module

`NativeCMSerreSchemeAction`, `NativeCMSerreSchemeTensor`,
`NativeCMSerreSchemeTangent`, and `NativeCMSerreSchemeLie` now construct the
scheme representation directly. Given the actual seed group scheme with
its genuine `O_K` endomorphisms, the same trace-frame matrix defines an
idempotent on a finite power of that scheme. Its equalizer with the identity
is a scheme with a proved retraction, commutative group structure, and a
natural tensor-point equivalence on every test scheme. The coefficient
module is still exactly `B^-1`; no free replacement or representability
premise is used. The full `O_E` coefficient action is constructed by Yoneda
from its action on this tensor functor.

The dual-number construction splits reduction to the base and proves that
the equalizer's intrinsic tangent module is `R tensor_{O_K} B^-1`. Its
linear equivalence sends `r tensor m` to the actual integral seed tangent
`[r*epsilon,-1,0]` followed by the tensor morphism for `m`. It is compatible
with the full `O_E` action. The seed's scheme action and its action on the
literal integral tangent vector are still explicit geometric inputs; those
inputs are not supplied by the already proved complex point action.
`NativeCMSerreSchemeEigenline` differentiates that full coefficient action
by postcomposition and identifies its intrinsic Lie eigenmodule with the
original second-factor eigenmodule. Its coordinate equivalence has the
literal image `B^-1 D = conjugate(B)` after extension. The same integral
equation's full embedding-period sum enters the existing all-place degree
formula on that image. The induced ample line bundle and identification
of its metric with this period profile remain to be constructed before
the source's polarized arithmetic CM-degree theorem applies.

### The actual signed tensor bundle and its integral-eigenline Gram

`NativeCMSerreGramForm` proves the original finite Hermitian-frame Gram
expansion and its polarization identity. `NativeCMSerreSchemeBundle`
constructs the actual bundle on the same represented tensor scheme from
four origin-bundle pullbacks for each frame pair. If `p_i` is the actual
projection and `g_ij=kLin(x_i,x_j)`, the two maps are `g_ij*p_i` and
`w*p_j`; the sum, first, second and zero maps carry exponents `1,-1,-1,1`.
The signed line-bundle atlas and unit rigidification are constructed.
No free module replaces `B^-1` and no chosen Gram replaces its trace form.

`NativeCMSerreBundleGram` computes these four signed contributions. The
cross terms recombine using `w+conjugate(w)=1`, and the native trace formula
turns their sum into the full root-fixing embedding norm of the actual
integral tensor. `NativeCMSerreSchemeMetric` differentiates the actual
projection maps and proves that their derivatives are the same integral
pairing coordinates. On the literal Lie eigenmodule, this signed Gram is
exactly the existing coordinate-line norm squared, with the coefficient
coming from the actual sigma automorphy form at the same infinite place.
This is an algebraic and differential comparison of the actual maps;
the induced global tensor metric, cubical and Rosati identities, relative
ampleness and trivial kernel of this tensor bundle still require their
geometric proofs. Inversion symmetry is supplied by the later nested-chart
construction below.

### Exact analytic Serre periods and the original polarization

`NativeCMSerrePeriods.lean` proves that all embeddings in the selected
native CM type restrict to the same embedding of `O_K`. It constructs the
complex base-change map from the original projective lattice to the
existing embedding coordinates. Surjectivity follows from the previously
proved real realization; the exact projective rank gives injectivity.

Tensoring the actual seed quotient gives a surjection with kernel exactly
`{1 tensor m : m in M}`. Under the constructed coordinate equivalence this
is precisely the original integral period image. Thus the quotient of the
prescribed complex period space is identified with the actual tensor point
module; a separate period-identification hypothesis is not introduced.

`NativeCMSerrePolarization.lean` pairs the actual `kLin` with the actual
seed metric. With the orientation determined by the chosen CM embedding,

\[
\operatorname{Im}H_0(\tau(h(x,y)),1)=EF(x,y),
\]

\[
\pi\operatorname{Re}H_0(\tau(h(x,x)),1)
 =\frac{2\pi}{\sqrt d}\,\epsilon EF(w_0x,x).
\]

The native endpoint derives the required positivity on every nonzero
element of the literal coefficient ideal from the trace identity below.

## 5. Pure types and the sign that the tensor constructor needs

The source's `exists_isExp_of_isTen` explicitly requires `q=0` or `p=0`.
A mixed-signature `W_j` cannot be fed to that theorem as one positive pure
elliptic tensor. `NativeCMPureBlockPositivity.lean` proves, on the actual
coefficient ideal,

\[
2EF(w_0x,x)
 =\operatorname{Tr}_{E/\mathbf Q}(\overline x x)
 =\sum_{\sigma:E\to\mathbf C}|\sigma(x)|^2>0\quad(x\ne0).
\]

The coordinate split is an explicit `O_E`-linear equivalence on the same
inverse-ideal lattice, and the original signed form is exactly

\[
EF_{p,q}=EF_{p,0}-EF_{q,0}.
\]

There is no lattice-index loss and no omitted cross term. The positive
block satisfies the constructor's positivity with `epsilon=1`; the
negative block uses its original form and `epsilon=-1`. The native endpoint
derives these facts from the actual host half-root.

`NativeCMSerreMixedPeriods.lean` uses the two actual seed orientations.
Complex conjugation gives a proved `O_K`-linear equivalence from the positive
seed's point module to the conjugate seed's point module. Tensoring it and
using the literal coordinate split produces

\[
(B^{-1})^p\otimes_{O_K}A_\tau
\;\times\;
(B^{-1})^q\otimes_{O_K}A_{\overline\tau}.
\]

The exponential is surjective, its kernel is exactly the existing
`prescribedPeriodMap` image for every allowed `j`, and its full `O_E` action
is the existing signed `prescribedPeriodType`. The ranks are
`(2*2^e)*(k+j-1)` and `(2*2^e)*(m-j)`. Both conjugations in the negative
block's ray formula are explicit; no single pure-type substitution occurs.

### Exact finite-place correction of the coefficient ideal

`NativeCMFiniteDegreeCorrection.lean` computes the original different twist
before any assertion about an arithmetic Lie metric:

\[
B^{-1}\mathfrak D_{E/K}=\overline B,
\qquad N(B)^2=N(\mathfrak D_{E/K}).
\]

Consequently the exact finite contribution used in twice the CM eigenline
degree is

\[
-\frac{2\log N(B^{-1}\mathfrak D_{E/K})}{[E:\mathbf Q]}
 =\log\operatorname{rd}(K)-\log\operatorname{rd}(E).
\]

Extension of this actual fractional ideal to any number field containing
`E` preserves the normalized correction; its extension degree is retained
and cancelled explicitly. The integral tensor eigenmodule above is now
identified with this exact ideal. Identifying that tensor with the Lie
module of the represented Serre scheme remains necessary before asserting
the arithmetic Lie degree.

`NativeCMLineDegree.lean` carries this calculation into the existing
`AllWt.deg`, using its actual singleton Gram frame and the finite relative
index of the original fractional ideal. For a positive, conjugate-invariant
family of squared norms `n_sigma`, the norm is literally
`sqrt(n_sigma)*|sigma(x)|`, and the theorem proves

\[
\deg(I,n)=-\frac{\log N(I)}{[F:\mathbf Q]}
 -\frac1{2[F:\mathbf Q]}\sum_\sigma\log n_\sigma.
\]

Specializing to `I=B^-1*D(E/K)` and to its actual extensions gives
`2*deg = -mean(log n) + log rd(K) - log rd(E)`. The metric family is an
explicit input to this generic degree theorem; identifying it with the
constructed arithmetic Lie metric is not replaced by a definition.
`NativeCMSerreEigenlatticeDegree.lean` applies this theorem to the image
of the actual integral tensor eigenmodule under its proved injective
coordinate map. It retains the integral index in this passage to
`AllWt.deg`.

## 6. Measured component ranks and arithmetic degrees

`NativeMeasuredComponentDegree.lean` reconstructs norm scaling and
orthogonal-sum rank/degree additivity in RHLean's existing all-place
Hermitian lattice degree, with its original discriminant and covolume
convention. `NativeMeasuredComponentNorm.lean` derives the scaling from
actual integrals, rather than assuming a mass proportionality equation.

For a function supported in a measurable component `S_sigma`, define its
mass to be the actual `m_sigma=mu_sigma(S_sigma)` and normalize the
restricted measure by that mass. The exact norm relation is

\[
\|f\|_{\mu_\sigma}^2
 =m_\sigma\|f\|_{\mu_\sigma|S_\sigma/m_\sigma}^2.
\]

The combined theorem uses injective component maps, the original `O_K`
lattices and disjoint measurable supports. It proves

\[
\operatorname{rank}\bigl(\bigvee_i\phi_i L_i\bigr)=\sum_i\operatorname{rank}L_i,
\]

\[
\deg_{\rm global}\bigl(\bigvee_i\phi_iL_i\bigr)
 =\sum_i\left[\deg_{\rm normalized,i}(L_i)
 -\frac{\operatorname{rank}L_i}{2}
   \frac{\sum_\sigma\log m_{\sigma,i}}{[K:\mathbf Q]}\right].
\]

The zero-rank case is handled explicitly. Positive-rank components have
positive mass derived from the actual nondegenerate norm, rather than an
unjustified positivity assumption. For a probability measure, component
mass is also proved at most one.

This supplies the measured normalization calculation in the source's
component-additivity theorem. It does not yet identify the native analytic
theta functions with global cusp spaces or supply their actual Petersson
Gram data, geometric jet injection or lower-rank shares.

### A constructed finite-adelic vacuum for the same trace lattice

Five `NativeThetaCusp*` modules reconstruct the narrow Schwartz–Bruhat,
quotient-Haar, inner-product and vacuum proof chain, then instantiate it on
the actual native trace lattice. Its already-proved integral symplectic
basis supplies rational coordinates and self-duality. The character is
exactly the product of the native half-root semicharacters on the rows.

The result is a nonzero Schwartz–Bruhat test function `v`, fixed by that
Heisenberg character, with exact Haar inner product `ip(v,v)=1`. Its fixed
line is proved unique. At a level `R`, the Haar normalization is the actual
finite quotient sum with factor `R^(-n*g)`, where
`g=[E:Q]*(p+q)/2`. No normalized mass or fixed-vector witness is assumed.

The native coordinate convention gives `omega(coords x,coords y)=EF(x,y)`.
The source analytic `Data` convention uses the opposite sign. The integral
semicharacter is unchanged because `exp(pi*i*m)=exp(-pi*i*m)` for integers,
but a future complete analytic dictionary must prove that compatibility
explicitly. This construction is a finite-adelic test function, not yet a
global cusp form.

`NativeThetaCuspHaarAlgebra.lean` and `NativeThetaCuspHeisenberg.lean`
add exact Haar linearity and translation invariance on these same test
functions, stability under the rational Heisenberg action, the exact
cocycle, the theta-series covariance identity and unitarity for the
original inner product. The strict overlap bound and complete Weil action
remain separate parts of the source `IsSystem` construction.

`NativeThetaCuspRationalCoordinates.lean` constructs a single ambient
rationalization `Q tensor_Z La`, the base change of the original pairing,
and the base change of the actual half-root action. Its coordinate map
extends the same integral symplectic basis and preserves the form exactly.
The common phase `exp(pi*i*sum EF_Q(x,w0*x))` is defined on this entire
space. Its restriction equals the canonical integral phase; its unit norm,
quadratic-refinement identity and cocycle under integral cross-pairings
are proved. This supplies the common coordinates needed to compare shifted
vacua, avoiding an inverse used outside the integral image. Shifted
self-duality and the strict overlap bound remain separate obligations.

The remaining source `SW.IsSystem` also requires level test functions,
unitary Weil covariance, exact Haar norm, the strict off-diagonal overlap
bound, support outside the level, isotropic no-coinvariants and an admissible
doubled theta kernel. Those premises are not inferred from the vacuum alone.

`NativeThetaCuspSplitLevel.lean` supplies a genuine missing arithmetic
input to that source level. The proved Frobenius at five has dyadic
coordinate of order `2^e`; no power can be complex conjugation. Since the
same native field is unramified at five, conjugation fixes no prime above
five. The existing native prime-pairing constructor therefore gives an
actual ideal `m`, proper and nonzero, with

\[
\mathfrak m\overline{\mathfrak m}=(5),\qquad
\mathfrak m+\overline{\mathfrak m}=O_E,\qquad
\mathfrak m+(2)=O_E.
\]

This uses a conjugate half of `(5)`, preserving the fixed-five arithmetic
choice. The rational ideal `(5)` itself cannot meet the conjugate-coprime
condition. This proves the ideal input to `SW.Level`; the stronger
geometric level also asks for descent of a generator to the quadratic
order, which is not inferred from this prime pairing.

The same module lifts a proved quotient basis to actual integral vectors
`beta : Fin N -> (B^-1)^N` and proves
`span(beta) + m*(B^-1)^N = (B^-1)^N`. This supplies the source's arithmetic
generator condition without asserting that the projective coefficient
ideal has a global integral basis.

### Actual place periods in the literal integral eigenline degree

`NativeCMAllPlaceTangentPeriod` uniformizes the **same** integral equation
`W/O_F`, with `Delta(W)=1`, at each infinite place. Each constructed pair
`(Lambda_v,C_v)` retains its actual equation comparison and
`u_v^12 Delta(Lambda_v)=1`. The actual point exponential has kernel
`Lambda_v`, and its origin-coordinate first jet in direction `u_v` is the
scalar extension of the original integral vector `[epsilon,-1,0]`.

Its positive place profile is constructed as

\[
n_v=\frac{\pi|u_v|^2}{\operatorname{covol}(\Lambda_v)},\qquad
-\log n_v=\log\frac{\operatorname{covol}(\Lambda_v)}\pi
 +\frac16\log|\Delta(\Lambda_v)|.
\]

Pullback along `InfinitePlace.mk` supplies the exact conjugation convention
used by `AllWt`. `NativeCMAllPlaceEigenlineDegree` then proves, for the
**literal image** of the previously constructed integral eigen-coordinate,

\[
2\deg=\frac{1}{[F:\mathbf Q]}
 \sum_{\sigma:F\hookrightarrow\mathbf C}
 \operatorname{latticeLogPeriod}(\Lambda_{[\sigma]})
 +\log\operatorname{rd}(K)-\log\operatorname{rd}(E).
\]

No arbitrary norm parameters remain in this theorem. The full embedding
sum is retained. Identifying the place profile with the polarized Serre
scheme's Lie norm still requires its represented Lie comparison and the
conjugate-chart/polarization compatibility. Those claims are not hidden in
the definition of the profile.

### The actual origin line-bundle atlas

`NativeCMLineBundleAtlas`, `NativeCMWeierstrassProjSections`, and
`NativeCMWeierstrassOriginBundle` construct the two-chart bundle on the
same projective cubic. The first open is the invertibility locus of the
explicit origin cofactor; the other is the affine `Z != 0` chart. Their
union is proved to be the whole scheme. The transition is the actual unit
`X/Y` on their intersection, and all transition cocycle laws are proved.
The canonical section is `(X/Y,1)` and its nonzero locus is exactly the
affine chart. `NativeCMWeierstrassOriginDivisor` proves that this section
is regular on every restricted open and, on every test scheme, vanishes
exactly when the morphism factors through the identity section. This
universal statement includes test rings with nilpotents.

`NativeCMLineBundleSectionIso` derives the actual unit transition
isomorphism from equality of the regular zero subschemes.
`NativeCMWeierstrassOriginSymmetry` applies it to inversion on this same
integral group scheme and constructs a unit generator along the zero
section. `NativeCMWeierstrassOriginSections` uses explicit pole orders in
the affine coordinate ring to prove every global section is a unique base
scalar times the canonical origin section, over any commutative base ring.
The next native cut supplies the remaining two polarization properties.
`NativeCMWeierstrassOriginCube` constructs three sections of the cube of
this same bundle; their nonzero loci are exactly the three projective
coordinate opens, and their ratios are the actual coordinate ratios.
`NativeCMWeierstrassOriginAmple` proves relative ampleness on every affine
base restriction, including surjectivity of the section-algebra evaluation
map. `NativeCMWeierstrassOriginBaseChange` proves the unique-section result
after arbitrary affine base change. The actual sheaf gluing and section
transport in `NativeCMLineBundleTransport` and `NativeCMLineBundleKernel`
then prove the trivial translation kernel on arbitrary test schemes.
`NativeCMWeierstrassPolarizedOrigin.originLB_polarisation` joins
rigidification, inversion symmetry, relative ampleness and this kernel
property on the original integral group scheme. These new proofs await
hosted compilation. The CM scheme action and the analytic identification
of the polarization metric are separate obligations.

### Constructed sigma automorphy and the origin-section frames

The native `Zeta`, `QuasiPeriod`, `Sigma` and `CanonicalTheta` leaves
construct the Weierstrass zeta sum and sigma product on the original
`PeriodPair`. They prove the Legendre relation, simple zeros exactly at
the period lattice, and the canonical-sigma automorphy law with the
actual Hermitian form

\[
H(z,w)=z\overline w/\operatorname{covol}(\Lambda).
\]

The semicharacter and every lattice multiplier are derived from this
product. `NativeCMWeierstrassThetaFrame` compares it with the literal
origin section `x/y`, whose integral dual-number value is `-epsilon`.
Its analytic frame at zero has value `-u^-1`; no sign is changed to the
opposite tangent convention. The affine frame is the inverse of sigma,
and the proved overlap transition is the actual `x/y` transition.
`NativeCMWeierstrassThetaDescent` extends the origin frame across every
period using the actual nonzero sigma derivative, proves its multiplier
law, and proves analytic regularity and nonvanishing on the stated opens.

`NativeCMWeierstrassThetaMetric` proves the multipliers preserve
`|v|^2 exp(-pi Re H(z,z))`. The norm of the actual canonical section is
periodic, and the same integral tangent direction has exact squared
length `pi |u|^2/covol(Lambda)`. This is the previously constructed
`placeProfile` of the same integral equation; its negative logarithm is
the native lattice period. The subsequent actual-atlas and section-jet joins below connect these
frames to both algebraic charts. The final intrinsic Lie-norm and global
holomorphic comparison remains an explicit obligation. No height or class-group mean is assigned as a metric value.

### Actual shifted lattice and one common phase

`NativeThetaCuspAmbient` identifies `Q tensor_Z La` with the original
`E^N`, proves the exact rational trace-pairing formula, and intertwines the
actual coefficient action. `NativeThetaCuspShiftedLattice` constructs the
literal conjugate-level quotient

\[
\operatorname{idq}(\mathfrak m,\overline{\mathfrak m},L)
 =\{x:\overline{\mathfrak m}x\subseteq\mathfrak mL\},
\]

and proves its self-duality from the original one and the actual split-five
modulus. `NativeThetaCuspShiftedPhase` transports the single half-root phase
through the same rationalization equivalence. Its square-one and
semicharacter laws are proved on each constructed shifted lattice. The
phase is defined on the whole rational ambient, so no inverse of an
integral inclusion is evaluated outside its image.

`NativeThetaCuspFiniteOverlap` supplies the finite averaging projection
and its exact overlap calculation. `NativeThetaCuspShiftedVacua` proves
all its lattice and phase hypotheses from the actual original and shifted
modules, constructs their normalized vacua in common coordinates, and
retains the genuine subgroup relative index:

\[
[A:A\cap A']\,|\langle v,v'\rangle|^2=1.
\]

The native endpoint constructs the symplectic integer basis, actual split-five
ideal, both vacua and their overlap together for the prescribed mixed-sign
lattice. The integer basis is used for the rational Schrödinger coordinates;
it does not replace `B^-1` by a free `O_E` module.

The additional `NativeThetaCuspPseudoBasis`, `NativeThetaCuspAuxiliaryLattices`,
`NativeThetaCuspTensorLattices`, and `NativeThetaCuspTensorVacua` extend this
to every actual auxiliary projective lattice in the source's Hermitian
family. Dual pseudobases give the tensor lattice's self-duality and its
common phase law. The same original basis and split-five ideal work
throughout, and the overlap is the exact original relative index raised
to the auxiliary rank. No compatible vacuum family is assumed.

`NativeThetaCuspSeries` proves absolute convergence of the literal rational
Schwartz theta transform. `NativeThetaCuspSeriesInjective` proves its
injectivity by the already native Fourier uniqueness theorem. These are
analytic inputs for Weil covariance. `NativeThetaCuspSeriesHolomorphic`
proves local normal convergence, holomorphy and nonvanishing for the actual
normalized vacuum. The fourteen-module cut ending in `NativeThetaCuspWeil`
constructs the Fourier operator from finite Fourier sums, proves its Haar
unitarity, and derives the standard symplectic-J theta law from Gaussian
lattice Poisson summation. Explicit parabolic operators, their exact Haar
change of variables, transformation composition and a proved symplectic
factorization yield an operator for every rational symplectic matrix in
even coefficient dimension. Its Schwartz preservation, literal `TransS`
law and original Haar inner product are proved, not supplied as premises.
This cut awaits hosted compilation.
The finite level subgroup `J` and its character still need construction:
the existing full-level cardinality
bound and the split-five quotient basis do not supply those objects.
Global theta/cusp realization, its span and geometric rank lower shares
also remain open.

### Explicit finite-level theta sums and their exact Haar norms

`NativeThetaCuspFiniteLevel` and `NativeThetaCuspFiniteLevelNorm` construct
the full general linear group of the literal split-five quotient, with
`J=top` and trivial character. A single base vacuum is fixed before the
auxiliary lattice varies. Bezout lifts put the actual quotient columns
in `2*conjugate(P)*sL`; projectivity, self-duality and coprimality prove
that distinct columns give orthogonal Heisenberg translates. The finite
sum therefore has exact squared Haar norm `Nat.card J`, without an
orthogonality or mass premise. For even auxiliary rank `n` with
`k+m-1 <= n`, this gives nonzero holomorphic theta functions for every
actual lattice in `Vset H n 5`, together with their rational Weil
transforms and unchanged norms.

`NativeThetaCuspQuotientAdjoint` constructs the actual anti-multiplicative
adjoint between the quotients by `P` and `conjugate(P)` from the perfect
integer trace pairing and projective lifting. Its representability and
nondegeneracy, and the literal mod-five pairing divisibility equivalence,
are proved for the prescribed native datum. This supplies the finite
adjoint needed to transport a genuine coefficient character.

This full finite group is a legitimate constructed analytic level family.
The coefficient-matched subgroup/character from the geometric cover,
its isotropic system and Fourier identity, global cusp realization,
Petersson measure identification and geometric rank shares remain open.
The finite Haar norm is not a Petersson mass.

### Exact arithmetic bridge identified by the source

The source's `MeanLogCovolumeEqMeanClassGroup` compares the arithmetic and
class-group means by a double sum. It needs a common field `F`, integral
unit-discriminant equations for all ideal classes, and actual ideal
isogenies between them. Their derivatives `beta_C` must satisfy both
`beta_C b_C^-1 subset O_F` and `beta_C^-1 b_C subset O_F`, together with the
corresponding two-sided period-lattice inclusions.

The narrow native `NativeCMIsogenyDerivativeNorm` proves directly from
those two literal integrality conditions that

\[
b_C O_F=(\beta_C),\qquad
\sum_\sigma\log|\sigma\beta_C|=[F:K]\log N(b_C).
\]

This is a derived arithmetic norm identity; the genuine derivative
integrality remains a geometric obligation. `NativeCMIdealIsogenyPeriods`
now derives the actual CM ideal-class representation and covolume identity
from the two-sided lattice inclusions. `NativeCMPeriodNormInvariant` proves
scale and conjugation invariance of
`covolume(Lambda)^6 * norm(discriminant(Lambda))`.
`NativeCMIsogenyPeriodMean` proves both sums: the fixed-class row follows
from the derivative norm and discriminant product formula, while the
fixed-embedding column follows from the permutation of ideal classes.
Fubini then gives the arithmetic mean. `NativeCMIntegralClassPeriodMean`
expresses that conclusion in the exact native `latticeLogPeriod`
normalization and constructs integral ideal representatives with the
principal class equal to the original seed. These new calculations await
hosted compilation. The integral ideal-isogeny family and derivative
integrality are still explicit geometric inputs; no desired mean or
separate Galois equidistribution assertion is assumed.

### One integral polarized seed and the actual atlas metric

`NativeCMWeierstrassPolarizedSeed` joins the constructed integral equation,
its actual origin polarization, the original exponential/kernel, and the
literal dual-number first jet on one set of witnesses. Its all-place
comparison uses the sigma automorphy form of that same equation.
`NativeCMWeierstrassThetaAtlas` then proves that the explicit frames are
analytic and nonzero on the inverse images of the actual two algebraic
opens. Evaluating the literal canonical section gives sigma times these
frames, and the actual transition unit gives the full frame compatibility.
The proof uses sigma cancellation only away from its genuine lattice zeros;
at a lattice point the available algebraic chart is the origin chart.

`NativeCMWeierstrassThetaAtlasMetric` defines the norm of a local fiber
coordinate `c` as the Gaussian norm of `c/frame`. It proves that the actual
algebraic transition units are isometries, that period translations preserve
the metric on the same scheme point, and that the actual origin section has
the computed periodic sigma norm. The frame sign remains `-u^-1`.
`NativeCMWeierstrassSectionJet` proves analyticity and the exact derivative
of every regular section near the origin using the literal origin ring and
localization. The derivative is `u^-1` times its epsilon coefficient.
These constructions still require the final all-point holomorphic and
intrinsic Lie-norm join, and hosted verification; no general theta
uniformization theorem is assumed.

### Geometry and symmetry of the actual tensor scheme and bundle

`NativeCMSchemeRetract` proves smoothness, properness and geometric
connectedness descend along a genuine scheme retraction.
`NativeCMSerreSchemeGeometry` applies these proofs to the previously
constructed trace-frame equalizer and retraction. Its inclusion in the
finite power is a closed immersion, and the tensor scheme over the actual
seed base is smooth, proper and geometrically connected. The genuine seed
order action remains the stated input at this general endpoint.

`NativeCMLineBundleNested` constructs explicit nested chart-unit products,
retaining every signed integer exponent. `NativeCMSerreBundleSymmetry`
pulls the actual seed inversion trivialization through the actual bundle
maps and constructs an inversion isomorphism for the signed tensor bundle
on the same scheme. Cubical/Rosati compatibility, relative ampleness and
the trivial translation kernel of that tensor bundle remain open.

### Actual finite coefficient data and component-section cuts

`NativeThetaCuspFiniteCharacter` constructs a nontrivial determinant
character of the prescribed projective split-five quotient, together with
a number field containing its values. Integrality and unit norm hold at
every complex embedding. `NativeThetaCuspFiniteCoefficients` joins that
character to the actual quotient adjoint and constructs the normalized
coefficient function on the original `cHalf` quotient. Its support is
exactly the spanning first-row locus, and the original mod-five divisibility
law proves inverse-character covariance. The same construction proves the
normalization, integral values and norm at most one at every embedding.
No coefficient character or those five arithmetic properties are assumed.

`NativeThetaCuspComponentSections` glues a genuine global idempotent from
a clopen set of the original scheme, and multiplies actual line-bundle
sections by it with their unchanged transition units. It proves exact
field-point evaluation, idempotence, scalar-extension compatibility and
complex norm contraction. The moduli/period indexing that identifies the
required clopen sets, the geometric finite-Fourier identity, the resulting
global cusp spaces and their Petersson component masses remain to be
constructed. An arbitrary clopen subset is not asserted to be the physical
component required by the signed-slope comparison.

## 7. Exact next substitutions into the existing signed-slope comparison

The existing physical comparison remains unchanged, including its signed
ASK/MAIN recombination, finite-place gains and divisor
`Q=card(TT)*m*b*Delta/2`.

| Supplier | Constructed here | Still required for the physical comparison |
| --- | --- | --- |
| CM seed | Actual quadratic order, polarized analytic quotient, integral smooth proper group scheme, exact tangent/invariant comparison, all four origin-polarization properties, actual full CM order action over a finite extension, explicit sigma automorphy, actual atlas metric descent and local regular-section derivatives | Integral CM action, final global holomorphic/intrinsic Lie-norm comparison and arithmetic Lie-period comparison |
| Serre construction | Original projective module, perfect Hermitian form, trace-frame scheme equalizer and integral Lie tensor, full coefficient action, exact analytic period kernel and rank, smooth/proper/geometrically connected tensor scheme, literal symmetric signed origin-pullback bundle and intrinsic-eigenline Gram | Integral seed scheme action and its derivative compatibility; cubical/Rosati identities, tensor polarization and global arithmetic metric comparison |
| CM degree | Original covolume, actual elliptic integral tangent scale, integral Lie-tensor comparison given the genuine seed action, exact eigenideal and finite correction, native analytic Chowla--Selberg class mean, derived double-sum arithmetic mean from actual isogeny data | Instantiation of the seed scheme action and its derivative, polarization metric identification, integral ideal-isogeny family and two-sided derivative integrality |
| Component masses | Exact measured restriction and all-place degree correction | Actual global automorphic component spaces and Petersson measure/Gram identification |
| Cusp family and ranks | Existing polynomial span retained, actual auxiliary projective tensor vacua with exact overlap, common phase, rational theta convergence/injectivity/holomorphy, genuine rational Weil covariance and Haar unitarity, split-five modulus, explicit full-level finite theta sums and exact Haar norms, quotient adjoint, constructed character and equivariant coefficient function, actual clopen-section cuts and measured direct-sum rank | Geometric coefficient tie, isotropic system, algebraic/integral theta realization, global cusp span, orbit separation and geometric jet lower shares |

The source's genuine arithmetic period is

\[
x=\gamma+\log(2\pi/\sqrt d)
 -\operatorname{Re}\frac{L'(1,\chi)}{L(1,\chi)}.
\]

That value must be proved for the actual integral seed's Lie metric. It is
not assigned to a height field. Consequently no new unconditional witness
to `DIV`, `Slopes`, `QuotientSlopeBoundsWith`, or the complete set of eleven
physical signed-slope premises is claimed by the finite constructions here.

## Source and verification

All source correspondence uses Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.
The source archive/mirror states no license; attribution is retained without
assigning one. No external compiled object or terminal RH theorem is imported.

The exact source-to-native file hashes and declaration roots are recorded in
`../scripts/alpoge_geometric_source_audit/native_cm_seed_serre_mass_source_manifest.json`.
The executable terminal-axiom audit is
`ALPOGE_CM_SEED_SERRE_MASS_AUDIT_20261123.lean`. It accepts only `propext`,
`Classical.choice` and `Quot.sound`. A source identity, a compiled conditional
calculation and an instantiated physical supplier remain distinct statuses.

Hosted first pass `9a9be760` failed in the period-image transport: one
unreduced inverse-composition goal and missing `NumberField` namespace in
the native endpoint. The repair preserves every statement. The full native
build was correctly skipped after the preflight failure. The integrated
second pass `788d11b3d8eb5ec12f3d22374968f7d5e28bebd0` exposed a missing
`Pointwise` scope for the original ideal Galois action, also repaired without
changing any statement. The third integrated pass is
`fc9f96bcecd870991a1de4cb7c79b711bbf5bbf2`; its inexpensive source audits
passed, and the Lean closure stopped on an unused-section-instance warning
in `NativeThetaCuspSchwartz.isSB_zero`. The required `omit` declarations
were added, with the same lint review applied to the other new modules.
The next snapshot includes the finite-degree correction, algebraic-point
uniformization and full mixed periods described above. Compilation and
terminal-axiom verification remain required; the current PR Actions record
is authoritative. No local Lean or Lake command has been executed.

The fourth snapshot `4d1ebce91f43ea09f07702f42a08475c333a4da9` compiled
`NativeThetaCuspSchwartz` cleanly, then stopped on an unnecessary-`simpa`
warning in `NativeCMWeierstrassLatticeCurve`. The simplification is repaired.
To collect independent supplier diagnostics without repeated cold runners,
the reusable research workflow now has a narrowly guarded, three-minute
diagnostic pass after this audit's failed mandatory preflight. That pass
always returns failure, writes no research certificate and leaves the full
native build blocked. The existing warning-fatal check, process cleanup,
cache identity and standard terminal-axiom checks remain the acceptance gates.

The fifth snapshot `c7010b75778dd253fdf4a7b4d38e3349dc992332` passed the
source audits. Hosted compilation verified the exact period-covolume file
and the newly reconstructed modular-j/CM-integrality proof chain. The
bounded diagnostic pass exposed independent current-Mathlib API and
warning failures in the quadratic order, measured norm, Haar/inner-product
and split-level branches. These are repaired in the next snapshot without
weakening statements or disabling linters. The next snapshot also adds the
quadratic-order identification and the actual equation-point tensor above.
The combined closure and its terminal-axiom audit are not yet verified.

The sixth snapshot `ff07672896b75f4ea095999fa942818087ecc50c` passed the
source audits and compiled the measured-degree, Haar, inner-product,
abstract vacuum and integral-model branches cleanly. It exposed remaining
native-specialization errors in measured norm, split level, native vacuum
and two subtype coercions in the quadratic-order involution. These are
repaired for the next hosted snapshot, which also includes the actual
group scheme, exact analytic class-group period and Heisenberg laws above.

The seventh snapshot `c20912e1b0445f953f1a00fbd562faf64d9b6bd6`, Actions
run `45271744917`, passed the source audits. Hosted diagnostics compiled
the quadratic order, finite-degree correction, native vacuum, split-five
level, Haar algebra and Heisenberg laws cleanly. The analytic period chain
compiled with deprecation or unused-variable warnings. Seed, integral
scheme, Hermitian-form, line-degree and pure-block specialization errors
are being repaired without changing their mathematical claims. The
mandatory warning-fatal closure failed, and the full native build was
correctly skipped. This is not a verified integrated proof closure.

The eighth snapshot `5738de9d7757dbfd48adca9839b2db2e33d781ae`, Actions
run `45274075194`, passed the source audits. Hosted diagnostics compiled
`NativeMeasuredComponentNorm`, `NativeCMLineDegree`, `NativeCMIdealClassPeriods`,
`NativeCMChowlaSelberg`, `NativeCMPureBlockPositivity`, `NativeCMHermitianForm`,
and the projective helper/addition-polynomial/nonvanishing chain cleanly.
The mandatory check stopped on two unused-number-field-instance warnings;
independent diagnostics exposed remaining seed coercion/normalization and
rational-coordinate induction errors. Repairs retain the mathematical
statements. The full native build was skipped; the combined closure and
terminal-axiom audit still require a successful hosted run.

The ninth snapshot `6ac90340e92491d331f2f391518d3e188886e02f`, Actions
run `45275907302`, passed the source audits. Hosted diagnostics compiled
the projective scheme, order identification, rational CM isogeny formulas,
torsion algebraicity, rational lattice coordinates and derivative norm
identity cleanly. The combined closure failed on a two-chart section
normalization, seed/group coercions and the cusp ambient/finite-overlap
API boundary, with additional warning-fatal fixes. Its full native build
was skipped. The next snapshot carries the repairs and the newly
constructed scheme tensor, origin-bundle properties and auxiliary vacuum
family; their combined Lean closure is not yet certified.

The tenth snapshot `f6ec76b52baa9201710cc9c7a3d8f99ddf4f3407`, Actions
run `45277725658`, passed the source audits. Hosted diagnostics compiled
the elliptic seed, projective group law, line-bundle atlas, regular-section
isomorphism, origin bundle, quadratic-zeta/class-period chain, projective
pseudobasis and finite vacuum-overlap theorem cleanly. The closure failed
on tangent/polarization elaboration, Serre point-module projections and
rational theta coordinates, plus a warning in the regular-section file.
The next snapshot repairs those exact errors without weakening statements.
The full native build was skipped. The new polarization, arithmetic-mean
and Weil cuts still require a successful hosted closure and terminal-axiom
audit before being treated as verified native suppliers.

The eleventh snapshot `2299ab167b210f28ba2c3f41bea7df82fdceee71`, Actions
run `45279417852`, passed the source audits. The warning-fatal closure job
`138059899523` failed, and full native compilation was skipped. Hosted
diagnostics compiled the intrinsic integral tangent, Serre scheme action,
ideal-isogeny covolume theorem, section-point evaluations and most of the
Fourier/Poisson, rational theta and holomorphy chain cleanly. Remaining
errors were localized to basis decomposition, semireducible section
restriction, conjugation scope, one shadowed monoid identity, cusp
coordinate rewrites and warning checks. The twelfth snapshot preserves
the statements while repairing these errors. Its new global CM, explicit
sigma, signed tensor-bundle and finite-level leaves still require hosted
verification. The audit retains every prior declaration root; redundant
direct imports are removed only when retained imports transitively cover
them. No audit obligation or build gate is weakened.

The twelfth snapshot `8934d152ea8ef0adc8c17d983f764e8d4428f2ff`, Actions
run `45281314157`, passed all source audits. Hosted closure job
`138066459085` failed and full build `138069732207` was skipped. Diagnostics
compiled the elliptic polarization, line-bundle germs/powers/transport,
origin divisor, coordinate cube and relative ampleness, origin global
sections, intrinsic Serre tangent, period-norm invariance and double-sum
isogeny mean, all six prior cusp repairs and rational Weil covariance.
The remaining errors were in `GeometricPoints`, `QuasiPeriod`,
`OriginSymmetry`, the integral equation's final coercion/sign calculation,
`SerreTensor` and `QuotientAdjoint`, plus zeta deprecations. The thirteenth
snapshot repairs these exact diagnostics and adds the actual atlas/jet,
tensor geometry/symmetry and finite coefficient/component constructions.
The integrated closure and transitive terminal-axiom audit remain unverified.

## Located continuation without inflated import closures

The CM-action branch now uses a smaller cut than the general division-polynomial
closure: torsion-coordinate algebraicity from finite torsion and extension of
field embeddings, followed by the exact rational lattice-isogeny formula.
`NativeCMWeierstrassCMAction` retains `u^-1 Lambda`, proves its invariants
are `c4(W)/12` and `c6(W)/216`, and constructs a number field containing the
same integral equation and all coefficients of the CM generator's formula.
The numerator has leading coefficient `omega^-2`, its degree is the actual
kernel cardinality, and the denominator degree is exactly one smaller.
The derivative factor `omega^-1 (A'D-AD')/D^2` is retained in the y-coordinate.
The point formula is intertwined with the original equation's CM action.
`NativeCMWeierstrassNormalizedModel` proves that the rescaled lattice curve
is the short Weierstrass model defined over the same original field: the
coordinate change uses the algebraic coefficients `-a1/2`, `-b2/12`, and
`(a1*b2-12*a3)/24`. No transcendental period is adjoined to that field.
`NativeCMWeierstrassTranslationScheme` constructs the actual triangular
projective scheme isomorphism and its inverse, matching the prior point
comparison. `NativeCMWeierstrassRationalIdentity` now proves the polynomial
curve identity from the actual elliptic point formula.
`NativeCMWeierstrassRationalSchemeOpen` constructs the literal localization
at the denominator and the actual scheme morphism with coordinates
`A/D` and `alpha^-1*(A'D-AD')*y/D^2`.
`NativeCMWeierstrassCMOpen` supplies those data for the same finite field,
same normalized seed equation and original CM generator.
`NativeCMWeierstrassGeometricPoints` proves detection of morphisms from
actual embedded algebraic points. `OpenPoint`, `GeometricGlue` and
`RationalGlobal` construct a finite-extension point outside the denominator
kernel, cover by the open and its translate, and glue the actual rational
map using the original group law. `NativeCMWeierstrassCMGlobal` thereby
constructs a global monoid scheme endomorphism over a finite extension,
retaining the exact open restriction, original complex-point CM formula
and quadratic order relation. `NativeCMWeierstrassCMOrderAction` then
constructs the full `SerreScheme.OAct (OK G)` through actual integer
coordinates in `1,wK`; fixed-embedding geometric detection proves all
ring laws and the exact all-element action on the same period lattice.
Extension over the integers and compatibility with the original integral
tangent remain open.

For the cusp norm/overlap branch, the declaration cut now reaches the
actual auxiliary tensor-lattice family, normalized vacua, exact relative-index
power overlap, holomorphy/injectivity of its rational theta transform and
the Fourier/Poisson proof of rational Weil covariance.
It uses Heisenberg unitarity and cocycles, finite quotient projections,
projective pseudobases and literal shifted self-duality. The explicit full-level theta sums now have their exact Haar norms and
quotient adjoint. The coefficient-matched subgroup/character and geometric
Fourier identity, global automorphic realization and measured geometric
rank shares remain open.

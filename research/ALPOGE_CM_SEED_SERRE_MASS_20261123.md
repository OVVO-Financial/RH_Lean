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

The point-module tensor still needs representability by the polarized
abelian scheme and compatibility of its line bundle, Lie generator and
finite-place model before the source's arithmetic CM-degree theorem applies.

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
and cancelled explicitly. The theorem proves the finite-ideal term.
Identifying this ideal with the integral Lie eigenspace remains necessary
before combining it with the arithmetic archimedean term.

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

## 7. Exact next substitutions into the existing signed-slope comparison

The existing physical comparison remains unchanged, including its signed
ASK/MAIN recombination, finite-place gains and divisor
`Q=card(TT)*m*b*Delta/2`.

| Supplier | Constructed here | Still required for the physical comparison |
| --- | --- | --- |
| CM seed | Actual quadratic order, polarized analytic quotient, integral discriminant-one equation and exact invariant comparison | Integral polarized elliptic scheme and arithmetic Lie-period comparison |
| Serre construction | Original projective module, perfect Hermitian form, retraction, actual point tensor, exact analytic period kernel and rank | Represented abelian scheme, induced ample line bundle and its integral Lie comparison |
| CM degree | Original archimedean covolume, tangent determinant factors and exact finite different correction | Actual Lie-eigenlattice identification, all-embedding arithmetic period and source CM frame value |
| Component masses | Exact measured restriction and all-place degree correction | Actual global automorphic component spaces and Petersson measure/Gram identification |
| Cusp family and ranks | Existing polynomial span retained, normalized finite-adelic vacuum on the actual trace lattice, actual split-five coefficient modulus and measured direct-sum rank | Complete Weil/overlap/isotropic system, algebraic/integral theta realization, global cusp span, orbit separation and geometric jet lower shares |

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

## Located continuation without inflated import closures

The source's next arithmetic CM-action descent can use two Mathlib-based
division-polynomial files, `GroundTheory/ArithmeticGeometry/AbelianVarieties/`
`DivisionPoints.lean` and `NormEDS.lean`. Their general torsion criterion,
with the nonzero division polynomial in characteristic zero, proves
algebraicity of the coordinates of the actual finite kernel. The generator
satisfies `w0*(1-w0)=(1+d)/4`, so its kernel is killed by this explicit
positive integer. One must first retain the actual `u^-1*Lambda` scale,
whose invariants are `c4(W)/12` and `c6(W)/216`, before descending rational
CM isogeny formulas. This is a located source continuation, not an
already-proved native algebraic endomorphism.

For the cusp norm/overlap branch, a declaration-level dependency cut uses
Heisenberg unitarity and cocycles, finite quotient projections, exact
vacuum overlaps, and actual tensor-lattice relative indices. It avoids the
large unrelated scheme/Moduli import surface. The actual family still needs
vacua for every shifted projective lattice in the source level, rather than
only rows of the one original lattice constructed here. These precise
obligations remain open in this revision.

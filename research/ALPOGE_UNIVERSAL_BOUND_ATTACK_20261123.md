# Alpöge-guided universal-bound attack: actual ray counts and integral volume

## Status and active target

This checkpoint combines the verified geometric construction at PR #1194 head
`2eee27648b7bc24e20bdae068a28bcdc2b9f8b66` with current main
`ff00d98d0a54c4c47017b036dda2c4e8afc6150d`, including #1195's native window
consumer and #1196's square-clock consumer. PR #1194 was merged into the earlier
#1193 feature branch; its construction was therefore absent from main. The
integration preserves the source from both parents and regenerates the shared
import manifest and search catalog.

The new mathematical results below have independent paper review. Their Lean
proofs and strict terminal-axiom audit are submitted for hosted verification;
this initial checkpoint does not yet claim a successful build.

The universal critical target remains

\[
\forall\eta>0\;\exists C_\eta\ge0,R_\eta\;\forall R\ge\max(2,R_\eta),
\qquad G_z(R^2-1)\le C_\eta R^{1+\eta}.
\]

`riemannHypothesis_of_eventual_squareClock_Gz_rpow` already consumes that
statement. The new results pay two concrete construction costs. They do not
supply the complete signed physical estimate or assert RH.

## 1. Keep the modulus in the actual ideal lattice

The existing native construction supplies an equivalence from the integer
plane to the actual ideals in a prescribed ray class, with the ideal norm
represented by

\[
Q(v_1,v_2)=\alpha(v_1+\theta_1+\ell v_2)^2
            +\gamma(v_2+\theta_2)^2.
\]

The old public statement exposed only `alpha >= 1`, `gamma >= 1` and
\(\alpha\gamma=dM^4/4\). The same proof has stronger information:

\[
M^2\le\alpha\le M^2\sqrt d,\qquad
\frac{M^2\sqrt d}{4}\le\gamma,\qquad
\alpha\gamma=\frac{dM^4}{4}.
\]

The lower bound for alpha follows from ideal-norm divisibility for a nonzero
vector in the actual modulus-times-ideal lattice. The upper bound follows from
the reduced integral basis. The gamma bound uses the same covolume and basis.
No new lattice is substituted. The original theorem and its statement remain
available as a corollary.

Source: [NativeRayQuadraticForm.lean](../RHLean/Analysis/AlpogeThin/NativeRayQuadraticForm.lean),
`QuadraticForm.exists_quadratic_norm_coordinates_with_scale`.

## 2. A uniform finite count on the original ideal coefficients

For arbitrary real shear and shifts, positive alpha and gamma, and X > 0,
the plane count satisfies

\[
\left|\#\{v\in\mathbb Z^2:Q(v)\le X\}
 -\frac{\pi X}{\sqrt{\alpha\gamma}}\right|
\le 2\sqrt{X/\alpha}+2\sqrt{X/\gamma}+1.
\]

The proof counts each horizontal row exactly, retaining its integer endpoint
error. The lengths of the rows form a nonnegative unimodal function. Its
sum-to-integral error is bounded by its maximum. Integrating the ellipse gives
the displayed area. The last `+1` is retained, including when a boundary passes
through lattice points.

Let `aRay D g n` be the existing count of nonzero integral ideals of norm n,
prime to the modulus and in ray class g. For the original hypotheses

- d is prime, d is 3 modulo 4, and d >= 100;
- K is the quadratic field with the supplied square root of -d;
- M >= 3 and D is the same native ray datum;

the exact norm-fiber equivalence gives, for every real X >= 1,

\[
\boxed{\left|\sum_{1\le n\le X}a_g(n)
 -\frac{2\pi X}{\sqrt d\,M^2}\right|
 \le\frac{4\sqrt X}{M}+1.}
\]

The sum uses the exact floor of X. This is a uniform bound in the ray class,
the shifts, the shear, and X. The gain is the retained factor 1/M in the error.

Sources: [NativeRayLatticeCount.lean](../RHLean/Analysis/AlpogeThin/NativeRayLatticeCount.lean),
`LatticeBounds.qForm_count`; and
[NativeRayCountTheta.lean](../RHLean/Analysis/AlpogeThin/NativeRayCountTheta.lean),
`rayCountTheta`.

## 3. Gaussian theta cost: normalize before estimating

For the same coefficients, define

\[
\Theta_g(t)=\sum_{n\ge0}a_g(n)e^{-tn},\qquad t>0.
\]

The new theorem proves summability and the uniform estimate

\[
\boxed{\left|\Theta_g(t)-\frac{2\pi}{\sqrt d\,M^2t}\right|
 \le\frac{3\pi}{8}d\sqrt d\,M^2t,\qquad t>0.}
\]

The proof first establishes a one-dimensional shifted Gaussian estimate using
Poisson summation and a summable explicit tail. Applying it to both coordinates
retains the full quadratic-form determinant and gives a two-dimensional theta
bound with arbitrary shear and shifts.

The essential improvement is to divide the actual quadratic form by M squared
before estimating it:

\[
Q_0=Q/M^2,\quad u=M^2t,\quad
\alpha_0,\gamma_0\ge1,\quad \alpha_0\gamma_0=d/4.
\]

For 0 < u <= 1, the Poisson bound is at most
\((3\pi/8)d\sqrt d\,u\). For u >= 1, positivity and monotonicity of the same
Gaussian sum, together with its bound at u = 1, give the same linear bound.
Thus the final theorem covers every positive t. Bounding the unscaled
coefficients separately would instead leave M to the sixth power in this
particular estimate. The normalized calculation saves a factor M to the fourth
power in that coefficient.

This is an estimate for the actual ideal-norm theta series. In the source it
supplies the count/theta fields of the ray-character analytic family used in
prime selection and the thin-character estimates. The geometric section theta
uses a higher-dimensional period/Fock lattice. A direct equality between these
two different theta objects is neither supplied here nor an original required
identification.

Sources: [NativeRayShiftedTheta.lean](../RHLean/Analysis/AlpogeThin/NativeRayShiftedTheta.lean),
[NativeRayTheta.lean](../RHLean/Analysis/AlpogeThin/NativeRayTheta.lean),
`LatticeBounds.theta_qForm_all_time`; and `rayCountTheta` above.

## 4. Complete prime-power mass, including ramification

For every number field K and every finite collection S of actual integral
ideals all having the same absolute norm n, the new theorem proves

\[
\sum_{I\in S}\Lambda_K(I)\le [K:\mathbb Q]\Lambda(n).
\]

At a prime-power norm, distinct contributing ideals have distinct prime
radicals: equality of radicals and equality of norms force equality of the
exponents. Those distinct primes are coprime and their product divides the
rational prime ideal. Taking norms and logarithms yields the degree factor.
This includes every residue degree and ramified prime. At zero, one and norms
that are not prime powers the contributing filtered set is empty.

The actual ray-class fibers are disjoint, so this proves

\[
\boxed{\sum_g\operatorname{lamRay}(D,g,n)
 \le[K:\mathbb Q]\Lambda(n).}
\]

The constructed quadratic field therefore has the full original budget
\(\sum_g\operatorname{lamRay}(D,g,n)\le2\Lambda(n)\), without omitting higher
prime powers or modulus/ramification cases. This pays another named arithmetic
input of the ray-character family. It controls positive source mass; the
complete signed cancellation problem is still separate.

Source: [NativeRayPrimePowerMass.lean](../RHLean/Analysis/AlpogeThin/NativeRayPrimePowerMass.lean),
`PrimePowerMass.finite_mass_le`, `ray_mass_le` and `quadratic_ray_mass_le`.

The companion [NativeRayNormOne.lean](../RHLean/Analysis/AlpogeThin/NativeRayNormOne.lean)
also constructs the required norm-form witness from the actual identity-class
coefficient. For every natural n, nonzero `lamRay D 1 n` supplies an actual
ideal I of norm n. The native class equivalence constructs its generator
pi with (pi) = I and pi congruent to one modulo M. Writing this generator
in the existing quadratic integral basis gives integers A and B satisfying

\[
A^2+dB^2=4n,\qquad M\mid B,\qquad 2M\mid(A-2-B).
\]

These are exactly the pre-existing native `IsNormOne` coordinates. This
implication works for every n under prime d, d = 3 modulo 4 and the actual
degree-two root; it does not need n prime, d >= 100 or M >= 3. It supplies
the original prime-selection theorem's norm-form conclusion, without
asserting that a prime exists in a prescribed window.

### Signed real-character positivity on the same ideals

For any genuine real ray character chi, put A(n) = sum_g aRay(D,g,n),
A_chi(n) = sum_g chi(g)aRay(D,g,n), and let C_chi = A * A_chi denote
the ordinary divisor convolution. The new
[NativeRayRealCharacter.lean](../RHLean/Analysis/AlpogeThin/NativeRayRealCharacter.lean)
proves, for every natural n,

\[
C_\chi(n)\ge0,\qquad A(n)\le C_\chi(n^2).
\]

The proof factors the actual ideal-divisor sum. Each ideal-prime factor is
1 + chi(P) + ... + chi(P) to the power e, with chi(P) in {0,1,-1} after
retaining the modulus exclusions. Each factor is nonnegative; for even
exponents it is at least one. The injective actual map I to I squared
gives the second inequality. This retains every ramified prime and residue
degree, and treats norm zero explicitly. No positivity is asserted for
the signed coefficients A_chi themselves. The direct order-two `AddChar`
adapter supplies exactly the original ray-family `sq` field.

### Class cardinality from the original quotient and discriminant

The existing quotient embeds in the actual class group times the residue
ring. [NativeIdealClassBound.lean](../RHLean/Analysis/AlpogeThin/NativeIdealClassBound.lean)
supplies the missing finite ideal-count/Minkowski bound, using only Mathlib.
In degree two it gives classNumber(K) <= abs(discr(K)). The actual root
and native discriminant theorem give discr(K) = -d, so
[NativeRayClassBound.lean](../RHLean/Analysis/AlpogeThin/NativeRayClassBound.lean)
proves

\[
|D.G|\le dM^2\le4dM^2.
\]

The first inequality is retained in the public theorem. The second supplies
the original LFam budget B = 4dM squared without assuming a class-count
estimate or changing the field or ray datum.

### Assemble every arithmetic field on one actual datum

[NativeRayLFam.lean](../RHLean/Analysis/AlpogeThin/NativeRayLFam.lean)
constructs `NativeRay.LFam.ofRayData` from the same given K, d, M, root and D
under the original prime/modulo-four/degree/size hypotheses. Its group is
`Additive D.G`, its budget is B = 4dM squared, and kappa is
2pi/(sqrt(d) M squared). Its coefficients are definitionally the original
`aRay` and `lamRay`.

Every original arithmetic field is proved: cardinality, kappa bounds,
coefficient signs and normalization, count, theta, complete Lambda mass,
exact logarithmic convolution, and both real-character square inequalities.
No additional quantitative field is assumed. The original small-time
B to the tenth theta allowance is obtained by a numerical weakening;
`ofRayData_sharp_theta` separately retains the stronger all-time estimate,
and `ofRayData_normOne` gives the actual norm-form support at every n.

This closes the arithmetic record construction on that datum, subject to
hosted verification. It does not construct its later analytic F/zero-free/
prime-window proofs or the independent geometric section family.

## 5. Integral descent from mean energy

Let A and B be finite-dimensional Hilbert spaces, with dimensions a > 0 and b,
and let q actual maps phi_h : A -> B have individual squared operator bound H.
Write F for their joint map into the direct sum of q copies of B. Then

\[
\operatorname{tr}(F^*F)
 =\sum_h\|\phi_h\|_{HS}^2\le qbH.
\]

Hadamard followed by the arithmetic-geometric mean inequality gives

\[
\det(F^*F)\le\left(\frac{qb}{a}H\right)^a.
\]

In particular, if qb <= (1 + delta)a,

\[
\boxed{\det(F^*F)\le((1+\delta)H)^a.}
\]

The proof of the Hilbert-Schmidt bound can test the operator inequality on the
conjugate of each row, then sum the resulting row-energy bounds. No spectral
decomposition or probabilistic assumption is needed.

For the actual unnormalized character trace after multiplication by a section
of norm at most B, each map has norm at most qB. Hence H = q squared times B
squared. The volume price becomes

\[
q^2(1+\delta)B^2
\]

per source dimension, compared with repeating the collective operator bound
q cubed times B squared in every dimension. This determinant estimate does not
assert a smaller collective operator bound.

The number-field theorem uses the existing common integral completion and the
product formula. With rank r, completion rank d, short completion-vector norm
at most exp(Lambda), and mean frame energy at most exp(2P), it gives the actual
squared-slope inequality

\[
r(\mu(A)-2P)-2d\Lambda\le(r+d)\mu(B).
\]

The integral matrix and its nonzero determinant are constructed by the existing
completion theorem. Its norm is at least one by the product formula. Thus the
finite-place index credit and the original metric normalization are accounted
for. There is no replacement of the original operator-height premise by an
unproved smaller value.

Source: [NativeMeanEnergyDescent.lean](../RHLean/Geometry/NativeMeanEnergyDescent.lean),
`jointMapMatrix_gram_det_le_of_rank_saturation` and
`mean_energy_weighted_descent`.

## 6. An actual integral trace instance and sharpness

On a finite additive group G, an integral section u gives the literal matrix

\[
C_{h,i}=u(i+h).
\]

Translation invariance gives every column the same energy. With q = |G|,

\[
\det(C)^2\le\left(\sum_i u(i)^2\right)^q.
\]

Under normalized source counting measure, the exact squared-volume expansion
is q to the q times det(C) squared. Therefore, if |u| <= B,

\[
q^q\det(C)^2\le(q^2B^2)^q.
\]

The four-point cyclic example u = (1, 1, 1, -1) has C transpose times C = 4I,
nonzero determinant with square 256, and attains this bound at q = 4 and B = 1.
The existing two-point counterexample to a q squared collective operator bound
is preserved. These examples distinguish the valid volume improvement from
the invalid norm substitution.

Source: [NativeTranslationTraceVolume.lean](../RHLean/Geometry/NativeTranslationTraceVolume.lean),
`nativeTranslationTrace_normalized_volume_le_qSquared` and
`nativeFourTrace_normalized_volume_sharp`.

## 7. What remains to reach the complete universal bound

The constructed dyadic source theorem already retains one physical host,
its actual inertia and Frobenius, its canonical character constants, all prime
powers, the same heights and widths, and the derived divisor

\[
Q=|TT|\,m\,b\,\Delta/2.
\]

Its complete signed-slope consumer still has the original geometric and strong
trace-error/window hypotheses. The new arithmetic bounds supply count, theta
and prime-power mass edges in the actual ray-character family. Separately,
volume descent must be applied to the compatible section, metric, height and
width family. A finite-function trace example alone does not supply that
family. A coordinate theorem for free integral modules alone does not identify
a projective section lattice with a free one.

For the inspected source scales log(q) <= 45 z squared and B = exp(C z to the
ninth), the volume improvement changes the logarithmic loss from
135 z squared + 2C z to the ninth to
90 z squared + 2C z to the ninth + log(1 + delta). The existing large b budget
already absorbs both. Consequently this improvement supplies a sharper finite
descent theorem, but by itself gives no new power of x in the normalized final
source estimate. q here counts descent maps and is distinct from theta-chain
multiplicity m and arithmetic-host size n.

The ray-character suppliers, including signed real-character convolution
positivity and cardinality control, are assembled on the same field,
ray datum and numerical parameters. The coefficient normalization at integer norm one is already proved in
`NativeRayIdealCounts`; the new `NativeRayNormOne` module supplies the
separate implication from a nonzero identity-class coefficient to the
specified quadratic norm condition. The geometric task is to use the actual period/Fock
theta evaluation formula, its compatible metrics and short-section bounds,
and the mean-energy volume comparison while retaining measured heights and
all signed returns. These branches must meet in the same complete physical
source under the already derived Q normalization. The final quantitative Gz
estimate remains open at this checkpoint.

## 8. Downstream paper consequences and precise next implementation

Writing B = 4dM squared and summing the same ray theta estimates over at most
B characters gives a small-time error at most
(pi/64) B to the power 5/2 times t. The original count bound supplies the
large-time decay, so the character theta residual is bounded for every t > 0
by C B to the power 5/2 times min(t,1/t), with absolute C.

The independently reviewed
[real-character capsule](ALPOGE_RAY_REAL_CHARACTER_LOWER_BOUND_20261123.md)
shows the quantitative effect. Keeping the original source's coarse integral
inequality improves its conditional B to the power -45 bound at s = 1 to
B to the power -11. Evaluating the scalar error kernel exactly and retaining
the logarithmic positive kernel instead gives B to the power -6. Both retain
the actual signed coefficients and original Mellin normalization. The
convolution-positivity and cardinality premises are now supplied by the
constructed native arithmetic record. The integral argument itself remains
a paper proof; it is not a new compiled theorem or global exponent gain.

The [projective mean-energy capsule](ALPOGE_PROJECTIVE_MEAN_ENERGY_CAPSULE_20261123.md)
locates the exact attachment to the genuine section lattices without assuming
they are free over the ring of integers. It uses their existing discrete real
realizations, the target-rank energy bound, and an exact equality between
image covolume and the restricted map determinant. The number-field degree
cancels from the rank ratio. The needed formal transport is still open; the
capsule does not replace it with an assumed improved height or norm.

Research capsule for this manual continuation:

~~~text
descent_payment_ack=ALPOGE_NATIVE_DESCENT_PAYMENT_V1
tractability_ack=ALPOGE_VIOLE_TRACTABLE_RH_V1
ROLE=Lean Verification, user-directed manual continuation
SOURCE=actual native ray ideals and the actual integral translation/descent maps
NORMALIZER=retain derived Q=T*m*b*Delta/2 in the complete signed consumer
EVIDENCE=independent mathematical review; new hosted compilation pending
FIRST_UNPAID=downstream ray analysis and compatible projective/window payment
T_C_P=finite reusable estimates; contribution isolated; unconditional RH open
NEXT=repair exact hosted diagnostics, then construct the named remaining suppliers
~~~

## Verification record

First hosted pass: commit `d3d24b98dcb4e6cb8d8a64808be18b6dd9591c05`,
[native run 45179953596](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45179953596).
The inherited integration compiled. The new lattice count, theta and
mean-energy modules reported localized elaboration/linter errors: coercion
alignment, finite-image index typing, a protected theorem name, explicit
column energy, and unused section/simp arguments. The repair pass addresses
these exact diagnostics without changing any estimate, budget or gate.
The full hosted result remains pending until this revised head passes.

- Main and #1194 source trees were read at the exact commits above.
- Integration conflicts were confined to generated manifests/search metadata.
- The new mathematical inequalities were independently reviewed on paper.
- The original public norm-coordinate theorem statement is preserved.
- The root manifest and current source/API records are regenerated.
- [ALPOGE_UNIVERSAL_BOUND_PROGRESS_AUDIT_20261123.lean](ALPOGE_UNIVERSAL_BOUND_PROGRESS_AUDIT_20261123.lean)
  checks the terminal axioms of twenty-seven quantitative roots.
- Hosted Lean compilation, warnings-fatal research closure and exact
  elaborated declaration checks are pending in this initial checkpoint.
- No local Lean or Lake execution was used.

No external terminal RH theorem supplies any of the new estimates. No source
coefficient is defined to equal an analytic endpoint, and no wanted signed
bound is hidden in a constructed object.

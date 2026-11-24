# Native square recovery: global cost and one-sided period audit

**Baseline:** `main@8e5f9b59ebacc022757e13ec6737c272633c13bc`.
**Scope:** obligation P2 in the attached native square-block plan, on the same
object as P1. **Status:** the actual native global capacity supplier is OPEN.
The new Lean module is a conditional quantitative refinement, pending hosted
verification. It does not assert the existence of the required physical
recovery/degree/slope data.

## 1. Existing suppliers inspected and their precise boundary

The current repository has more than an abstract determinant lemma:

- `nativeAllPlaceDescent_of_regular_groupDet` constructs the maps from one
  regular section: multiplication by its translates followed by the original
  unnormalized character trace. Integrality, joint injectivity, the collective
  norm and the opposite rank injection are proved for those same maps.
- `nativeCharacterTrace_jointNorm_le` pays the complete `q^3 B^2` squared
  operator cost; `nativeDescent_collectiveNormBudget` absorbs it at the stated
  original scales. Its stronger version already leaves an additional logarithmic
  reserve of at least `b`.
- `NativeMeanEnergyDescent.jointMapMatrix_gram_det_le_of_rank_saturation`
  already pays image volume by average frame energy. Repeating that improvement
  would not construct the missing native lattice.
- `nativeDescent_mainTermPayment` retains the negative main term, the
  rank-defect/generator-height bill and the final ring-transfer bill.
- `Ga_bound5` combines measured divisor, count, exponent, height variation,
  source/quotient slopes, rank-gap, and height-range bounds. Its
  `key_identity5` cancels the original leading terms.

The first unmet application is an independently measured divisor/degree and
quotient-slope comparison on the same object whose local restriction lengths
supply `Ga`. The existing `physicalData_Ga` preserves that gain; it does not
construct it. The generic lattice and norm theorems do not assign values to the
physical slopes or heights, nor do they prove their required arithmetic degree
comparison. A source-wide search found uses of `DIV`, `Slopes`, and
`QuotientSlopeBoundsWith` as premises, not a native constructor discharging
all three for the physical family.

## 2. A smaller period requirement, proved through the same finite argument

New file:
`RHLean/Geometry/NativeSquareCapacityPeriod.lean`.

Let `P(u,v)` be an independently measured period in the divisor comparison, and
let `Omega = D.logOm`. Suppose

\[
P(u,v)\ge\Omega-\rho.
\]

For the original nonnegative amplitudes, termwise multiplication gives

\[
\sum_t\{m[\operatorname{ph}(a_t)-a_tP(u,v)]-a_t\log T(u,v)\}
\le \operatorname{SDiv}-(\sum_ta_t)\log T(u,v)
       +m\rho\sum_ta_t.
\]

Thus a degree comparison measured at `P` gives the old `DIV` right side with
one explicit debt `m*rho*sumA`. The new theorem follows that debt through
`s_lower5`, the complete `Ga_bound5` proof, and the finite mean-loss theorem.
The gain, lattice slopes, actual heights, width count, `MAIN`, and every other
entry of `D` remain unchanged. There is no auxiliary record with an assigned
height or assigned gain.

The quantitative result is

\[
\langle\mathrm{ASK}\rangle-\langle\mathrm{MAIN}\rangle
\le\operatorname{errorTermWith}(D)+m\rho\sum_ta_t.
\]

The debt is not multiplied by the rank-gap factor. That factor controls
`uF`, whose bound uses exponent and height variation but not `DIV`. The
additional debt affects the lower slope once. This is also why inserting the
debt into every separate cost would overcharge it.

The physical-source endpoint is
`physicalTopExcess_div_le_errorTerm_of_period_lower`. It uses `Data.Losses`,
the two averaged loss inequalities, and the same original
`alpogeNativePhysicalSubgroupTopExcess`. Under the already earned divisor
`Q = T*m*b*Delta/2`, the extra price is exactly

\[
\frac{m\rho\sum_ta_t}{Q}
 =\frac{2\rho\,\overline a}{b\Delta},
\qquad\overline a=\frac1T\sum_ta_t.
\]

This is a conditional refinement of P2, not P2's physical supplier. In
particular, the new theorem explicitly retains the measured degree inequality
at `P`, all slope bounds, and the local mean-loss bounds.

If `|a_t/b-x| <= 1`, then `overline a/b` is of order `x`. For nonnegative
`rho`, its normalized price is at most `2*rho*(x+1)/Delta`. A fixed positive
period error therefore does not fit the root-scale budget. A sufficient
scale-dependent error is `rho = O(Delta*x^(-1/2+eta))`. The zero-error
one-sided case `P >= Omega` is especially useful: exact equality is unnecessary.
The previously proved reverse-integrality norm theorem gives the needed
nonpositive CM row correction **once an actual reverse map and the period
comparison have been attached**. It does not construct that attachment.

## 3. Actual dyadic decoder: gain and cost on one object

The recovery agent uses the actual survivor split on `3 <= A <= R < 2*A`.
For any common weight, write `P` for its prime mass and `C` for its surviving
semiprime mass. The two measured channels are

\[
U=P+C,\qquad S=C-P.
\]

Their integral matrix and recovery numerator are

\[
F=\begin{pmatrix}1&1\\-1&1\end{pmatrix},
\qquad M=\begin{pmatrix}1&-1\\1&1\end{pmatrix},
\qquad MF=2I.
\]

The same construction pays exactly

\[
U^2+S^2=2(P^2+C^2),\qquad
P^2\le\tfrac12(U^2+S^2).
\]

The full-cutoff case `A=R` is permitted and has no surviving composite.
Consequently `S=-U` and the displayed norm bound is an equality on the actual
native arithmetic carrier. This disproves a proposed *strict* improvement
obtained only by applying uncentered two-channel energy to the full wheel; it
is not a disproof of a centered signed or different recovery construction.
The recovery agent's file formalizes this weighted full-cutoff equality.

Stacking `m` copies of the same two rows produces a `2m`-by-2 matrix with
Gram matrix `2m I_2`, still of rank two. Its output energy is
`2m(P^2+C^2)`. Division by the gained copy count cancels the same factor
from the cost. There are no `m` new independent recovered conditions.

Taking an `m`-fold tensor product would have rank `2^m`, Gram matrix
`2^m I_(2^m)`, and recovery multiplier `2^m`; it is a different source space
with `2^m` coordinates. The original prime/semiprime split provides only two
coordinates. Reusing it as the tensor source without constructing independent
arithmetic coordinates is unjustified.

This answers the concrete repeated-channel proposal. It does not rule out
additional genuine characters or local restriction maps. For a complete
character transform on a finite group of order `q`, orthogonality gives
`F* F=q I` and recovery factor `q`; the total energy cost is `q` times source
energy. The principal coefficient is the total source. Removing it loses that
observable; retaining it leaves its size in the energy being bounded. A
successful new character construction therefore still needs a source-specific
estimate or a separately proved geometric capacity bound. Orthogonality alone
is an exact recovery identity, not that bound.

## 4. Upstream constructor audit: what the visible definitions do and do not prove

Inspected local upstream source corresponds to the project pin
`7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`. The following observations concern
specific declarations, not a verdict on the entire upstream development.

- `Definitions/AutomorphicMembership/OverIx.lean` defines
  `anyGeometry := fun _ _ _ => True`, alongside the stronger `geoOf` predicate.
- `Definitions/GlobalTwisting/SetUnipotentTranslate.lean` defines `setDiv` by
  updating the chosen lattices and `div.h`. In the same file `LedPart.ht` is
  assigned `DV.hExpl6`; `LedPart.pt` uses that value and proves its `h_eq` by
  `rfl`. These facts prove preservation of the chosen formula in that record.
  They do not independently identify a physical metric height with the formula.
- `Proofs/IwasawaDecomposition/TupPinsOfMuIsW.lean` constructs
  `geoOver_stages` for `GeoOver (fun _ => True)`. Its `mjAre_x0` and
  `lamAre_x0` are definitional identifications of the constructed reading.
- There are additional substantive fields: `RowsT` includes `inGeo`, metric
  equalities and row/lattice ties. Their existence cannot be inferred just
  from `anyGeometry`, and they cannot be dropped when reusing a constructor.
- `ThirdPlaceSeries/ExistsBaseLatticeOfPrime.lean` states
  `exists_baseLattice_of_prime_alt` with explicit `HypAAlt`,
  `EllipticHypothesis`, `MultiplicityCoverHypotheses`,
  `ExistsUnlocalizedSaturatedState`, local-Langlands, and
  `MultiplicityCondition` inputs. The declaration is not an unconditional
  physical-family constructor merely because its name says `exists`.
- `GoodRankK` in `UnramifiedQuadraticSetting.lean` is a genuine integral
  recovery identity. `goodRank_of_prim` constructs its columns using a
  primitive-combination valuation bound `hprim`. That valuation supplier and
  the actual local evaluation spaces must be instantiated; the native
  two-channel matrix by itself does not satisfy the upstream competing-edge
  vanishing or near-full-rank conditions.

The practical boundary for RH_Lean is precise: obtain the measured degree
inequality at `P`, the original quotient-slope bounds, and the local recovery
length on one independently constructed native object. The period theorem
above reduces the comparison needed of `P`; it does not replace those inputs
with assigned formula fields.

## 5. Latest handoffs considered

The latest actual finite-wheel report at `agent-reports@a52b8d8c` gives the
specific Smith-form obstruction to identifying the signed prime-band matrix
`2I-J` with the complete dyadic division quotient. At its actual `R=48`
example, the band matrix has elementary divisors `2,2,4`; the indicated
coefficient fields force even local cyclic multiplicities. That is a barrier
to that identification, not a proof that every native realization is impossible.

The latest owner report retains the exact top autocorrelation and ramified
prime-power terms; replacing it by independent top density is explicitly
refuted. Its small-quotient remainder remains unpaid. Neither handoff supplies
the measured P2 witness required above. These are report-level arguments;
their status does not change to kernel verification in this audit.

## 6. Follow-up: the growing floor-divisor map has a small mean cost and zero index

The next recovery candidate is the literal finite-prefix restriction of
`RHLean.Arithmetic.freshPrimeDifference p` in
`RHLean/Arithmetic/PrimeCombFiniteDifferenceFreshPrime.lean`. The underlying
`shift` in `PrimeCombFiniteDifference.lean` is `f(n) -> f(floor(n/p))`.
Restrict to the integral coordinate lattice on `1,...,N`, with `f(0)=0`, and
write

\[
F_p(n,k)=\mathbf 1_{k=\lfloor n/p\rfloor\ge1},\qquad D_p=I-F_p,
\quad p\ge2,\ N\ge1.
\]

This is a source-compatible integral linear map on prefix sequences. It is
not a new encoding of an arithmetic height. Since `floor(n/p) < n`, `F_p` is
strictly lower triangular. If `p^L > N`, then `F_p^L=0`, and

\[
D_p^{-1}=I+F_p+\cdots+F_p^{L-1}
\]

is integral. Thus its rank is exactly `N`, its determinant is `1`, and its
cokernel is zero. The same statements hold for any finite product of the
`D_p`. The existing `finiteDifferenceOperator_insert_eq_freshPrimeDifference`
and `shift_comp` identify that product with the original finite Möbius
divisor operator; the commuting finite-difference algebra is already proved.

There is a sharper cost statement than the generic operator estimate.
The matrix has `N` diagonal entries equal to `1` and precisely
`max(0,N-p+1)` strict-subdiagonal entries equal to `-1`. Therefore, at every
complex embedding,

\[
\sum_{k=1}^{N}\|D_pe_k\|_2^2
=N+\max(0,N-p+1)\le2N.
\]

This is a **mean frame-energy bound**. It is not a squared operator bound
of `2`: for `N >= 2p-1`, the actual vector `e_1` has
`||D_p e_1||^2=p+1`. The usual triangle estimate gives an operator bound
`||D_p|| <= 1+sqrt(p)`.

The exact inputs to the existing
`NumberFieldDescent.mean_energy_weighted_descent` in
`RHLean/Geometry/NativeMeanEnergyDescent.lean` can therefore be discharged as
follows, over any fixed number field `K`:

| Input | Actual substitution |
| --- | --- |
| source and target | the same lattice `(O_K)^N` with identity metric frame |
| integral matrix `F` | the integer matrix `D_p`, mapped into `O_K` |
| source rank `r` | `N` |
| complementary rank `d` | `0` |
| injectivity | the displayed integral inverse |
| short spanning set `S` | the original coordinate unit vectors |
| generator cost `Lambda` | `0` |
| image cost `P` | `log(2)/2` |
| source and target squared slopes | both `0`, from their identity Gram determinants |

Its complete conclusion is `-N*log(2) <= 0`, or `-log(2) <= 0` per source
rank. The stronger exact determinant calculation has image Gram determinant
`1` and gives zero net volume change. This supplies an actual map and its
global mean-energy cost, but no positive local length or determinant credit.
Interpreting the full rank `N` as `N` units of gained arithmetic multiplicity
would discard the zero cokernel calculation.

For a family of `q` such maps into `q` copies of the rank-`N` target, the
joint mean frame energy is exactly

\[
qN+\sum_{p\in S}\max(0,N-p+1),
\]

with the maps counted with their actual multiplicity. The rank-saturation
input of `jointMapMatrix_gram_det_le_of_rank_saturation` becomes
`q*N <= (1+epsilon)*N`, so it requires `epsilon >= q-1`. Thus one cannot use
the near-rank version while silently keeping `epsilon` small. Taking the
product instead retains determinant `1`; it changes the map but supplies no
index credit.

Nor can these floor maps be substituted for the action `st` in
`nativeAllPlaceDescent_of_regular_groupDet`. That theorem requires actual
unital algebra maps satisfying a group action. `F_p` is nilpotent on this
prefix and is not injective. For `N>=p`, `D_p` does not preserve the
pointwise constant-one function: its value is zero at every `n>=p`.
Consequently it is not a unital algebra map either. The direct integral
mean-energy theorem above is the applicable existing consumer.

Exact integer matrix checks, separate from Lean verification, confirmed:

| `N` | dilation(s) | rank | determinant | total squared frame energy |
| --- | --- | --- | --- | --- |
| 8 | 2 | 8 | 1 | 15 |
| 10 | 3 | 10 | 1 | 18 |
| 5 | 7 | 5 | 1 | 5 |
| 63 | 2 | 63 | 1 | 125 |
| 24 | product of 2, 3 | 24 | 1 | 90 |
| 63 | product of 2, 3, 5, 7 | 63 | 1 | 667 |

The calculation used integer matrix multiplication, exact integer
elimination, and the explicit geometric-sum inverse. The triangular and
entry-count arguments above prove the claims for all `N,p`; the table is a
diagnostic check, not a kernel-checked theorem. No new wrapper module was
added for this audit. A source-specific bound on the complete signed `Gz`
does not follow from this norm/rank calculation.

The recovery agent also tested literal repetition at a genuine prime square:
`R=p`, `N=p^2-1`. Then `F_p^2=0`, so for every natural `m`,

\[
D_p^m=I-mF_p,\qquad (D_p^m)^{-1}=I+mF_p,
\]

and its exact squared frame energy is

\[
N+m^2(N-p+1).
\]

Thus even this growing repetition has determinant and index `1`. At `m=p`,
the squared norm of its first source column is `1+p^3`. The exact mean
energy price in the existing theorem is
`P = log(1+m^2*(N-p+1)/N)/2`; with the same identity metrics and zero rank
defect, its conclusion remains only the nonpositive cost inequality
`-N*log(1+m^2*(N-p+1)/N) <= 0`.

The separately added
`research/NATIVE_PRIME_POWER_RECOVERY_TEST_20261123.lean` keeps the actual
integer coefficients of every von Mangoldt prime-power logarithm. Its
first-prime coefficient remains `1` under the whole finite wheel and its
iterates. Consequently this actual coefficient is not divisible by any
prime. This is a failure of the proposed positive valuation gain on that
coefficient; it is not a claim about divisibility of the real number
`log(p)`. The exact inverse and full rank have not supplied the needed
positive local multiplicity.

## 7. Follow-up: exact reverse-integrality attachment boundary on main

The search was extended through the actual main-branch ideal, ray-class,
polarization, and period constructors, rather than stopping at the standalone
norm theorem.

`NativeRay.IdealLattice.cls_iff` and `gen_bij` in
`RHLean/Analysis/AlpogeThin/NativeRayIdealLattice.lean` construct genuine
principal equations `I*B=(x)` within a specified ray-class fiber. Their
`normSq_eq` and `abs_im_eq` prove the actual principal norm and ideal-area
identities. These equations concern the product `I*B`; they do not identify
the tangent multiplier of an isogeny between a class model and the seed.

`nativeDyadicHostRaw_exists_principalPolarizationArithmetic` constructs the
half-different ideal and the actual identity

\[
(\xi)B^{-1}\overline B^{-1}\mathfrak D_{E/\mathbb Q}=1.
\]

`nativeDyadicHost_exists_prescribedPeriods` then constructs the period map
on that same inverse-ideal lattice. Its `IsPeriod` predicate, defined in
`RHLean/Geometry/NativeGeometricPeriods.lean`, contains exactly coefficient
intertwining, injectivity, discreteness, real spanning, and a positive
Hermitian form whose imaginary part is the original alternating form.
These are genuine constructions. The predicate contains no integral
arithmetic tangent lattice, ideal-class family of two-curve maps, or
comparison with `Data.logOm`.

The precise missing substitution into the one-sided norm lemma is a
nonzero multiplier `beta_C : M` attached to the actual class-to-seed
tangent map, with

```lean
∀ C (y : 𝓞 K), y ∈ b C →
  IsIntegral ℤ ((β C)⁻¹ * algebraMap K M (y : K))
```

Here `b_C` must be the ideal appearing in the analytic period inclusions
for that same class model. In the period double-sum application, the
simultaneous reverse analytic condition is

\[
\forall C,\sigma,y\in b_C,z\in L_{C,\sigma},\qquad
\sigma(\beta_C^{-1}y)z\in L_{0,\sigma}.
\]

The forward analytic inclusion is still needed. The unit-discriminant
normalization of the same models is what removes the discriminant row
sum. A newly chosen scalar satisfying the bare norm hypothesis is not a
replacement for these attachments. For example, `beta_C=1` satisfies bare
reverse integrality for every integral ideal, but this fact does not prove
that the actual two-model tangent multiplier is `1` or prove the required
period inclusions.

Main contains no constructor of these class-indexed scalar/morphism data.
For comparison, the inspected unmerged
`NativeCMWeierstrassMorphismTangent.exists_tangent_scalar` in
`origin/research/cm-seed-serre-degree-20261123` takes an actual endomorphism
`f : schemeOver V -> schemeOver V`, with its monoid-homomorphism structure
and exact analytic `expPoint` intertwining. It derives the integral tangent
coordinate of that endomorphism. The reverse application here needs a map
from the class model to the seed model, together with the matching
intertwining. Reusing the same-model theorem without constructing that map
does not discharge its telescope.

There is also a concrete reason `IsPeriod` alone cannot supply an absolute
arithmetic period lower bound: its entire predicate is preserved by
`P -> c*P`, `Hm -> c^(-2)*Hm` for every positive real `c`, while the
logarithmic covolume changes by `2g*log(c)` in complex dimension `g`.
This observation does not refute a bound for the fixed canonical
`prescribedPeriodMap`. It identifies the normalization information absent
from the `IsPeriod` interface. The required independently measured degree
comparison must retain that arithmetic normalization.

Accordingly no zero-slack physical period attachment was found on main.
The next exact input is the reverse two-model tangent map and its analytic
compatibility on the original class ideals, followed by the physical
`v=sqrt(d)/2` and canonical-character-log-derivative identifications. This is
a specific supplier boundary; it is not a demand to reconstruct every
unrelated part of PR #1201.

**Execution evidence:** original source/type inspection; finite algebraic proof
of the debt propagation; independent source review by the simultaneous-windows
agent; exact integer checks of the floor-divisor matrices. New Lean execution
is hosted-only and pending. **P2 status: OPEN.**

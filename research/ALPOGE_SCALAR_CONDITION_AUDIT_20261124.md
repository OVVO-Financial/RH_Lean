# Return #1201 to the scalar-bound cut

**Status:** proposed native scalar cost proofs; exact-head hosted verification
required. The critical geometric top-excess estimate and RH remain open.

Pinned original scalar definitions:
- [HostFactsS](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/DedekindLFunctions/SplitInertia.lean).
- [GrowthInequalityHypotheses, SmallCosts, SizeWindows](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean).
- [cost_proposition_at_scale](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/ConductorsKronecker/CostPropositionBasicBound.lean).

Native baseline main@9f84aae95729d566d4aa7189584620fbd0e1099a, prior #1201 head eee6c7af97e8ddef4a00108004fbd6c95cf44738.
The two-parent integration preserves every previous #1201 source and
imports the exact later main declarations. The only overlapping differing
file was RHLean.lean; both sides only added imports, so its resolution is
their sorted union. No completed external RH theorem is imported.

## 1. Complete 43-condition audit

The four bundles contain 43 immediate fields/conjuncts, not 43 independent
geometric problems. The following is a **consumer-level replacement audit**:
"Replaced" means the original literal premise is not needed in the chosen
native theorem, not a proof of the corresponding upstream structure for an
unconstructed instance. "Paid" means the listed native lemma proves it under
its actual retained parameter hypotheses. "Realize" means an actual compatible
family must still supply the stated relation. "Open" means a quantitative
supplier is not established. All statuses are source inspections unless an
exact-head hosted result is explicitly given.

Use
[nativeConstructedDyadicGzPayment](../RHLean/Analysis/AlpogeThin/NativeConstructedDyadicGzPayment.lean)
and
[nativeConstructedDyadicSignedSlopePayment](../RHLean/Analysis/AlpogeThin/NativeConstructedDyadicSignedSlopePayment.lean)
on their actual selected PageN exponent and PairGood prime pair. Their
conclusion is initially a **mean** of Gz at the physical heights. The
new scalar recovery below accounts for that difference.

### HostFactsS (8)

| ID | Original requirement | Native status and source |
|---|---|---|
| H01 | D.d prime | Replaced: PairGood.pair.d_prime in the actual selected pair. |
| H02 | 2 in S | Replaced: dyadic arithmetic host, no separate S input to native payment. |
| H03 | q1 in S | Replaced: selected q in the actual conductor/reciprocity host. |
| H04 | d not in S | Replaced: distinct selected prime data; the native d-inertia term is kept separately. |
| H05 | unramified outside S and d | Paid in the native host: nativeDyadicHostData_inertia_unramified. |
| H06 | split inertia at S | Replaced by native type-I and actual prime-power weight lemmas, not a freely selected inertia table. |
| H07 | split Frobenius at S | Replaced by the same native type-I/prime-power decomposition. |
| H08 | inertia at d equals two stated elements | Paid by nativeDyadicHostData_mem_inertia_d and nativeDyadicHostData_inertia_d_card. |

Source: [native host prime-power weights](../RHLean/Analysis/AlpogeThin/NativeDyadicHostPrimePowerWeights.lean),
[native host windows](../RHLean/Analysis/AlpogeThin/NativeDyadicHostWindows.lean).
The actual Gz payment does not assume HostFactsS as a record.

### GrowthInequalityHypotheses (16)

| ID | Original requirement | Native status and remaining input |
|---|---|---|
| G01 | 3 <= x | Paid by eventual threshold or actual square-clock scale. |
| G02 | 0 < b | Paid by b >= exp(x^eps); realize that width scale. |
| G03 | 0 <= eta | Realize native h >= 0 and its upper bound. |
| G04 | 0 < X' | Paid at X'=exp(x^(eps/3)). |
| G05 | 0 < b' | Replaced by actual beta > 0 and partner-ratio condition; realize widths. |
| G06 | b' X' <= x b | Replaced by actual nonthick ratio >= exp(x^(eps/3))/3; realize on the same profile. |
| G07 | 0 <= theta | Paid by selected exponential thin error. |
| G08 | 0 <= Cd | Paid by alpogeNativeMoveConstant_nonneg and native character movement estimates. |
| G09 | all top heights within 1 of x | Realize near-height family. New proof permits mean displacement cost <= 3*x^(1/2+eps) instead of pointwise unit distance; also require the actual heights in the selected analytic window. |
| G10 | NodeSizes T2 b b' eta w | Realize actual positive widths, thick interval, nonthick ratios, and selected beta. No replacement arbitrary profile is allowed. |
| G11 | sharp cutoff a/w <= N | Paid for the actual N=ceil(Amax/beta), given a<=Amax and w>=beta. |
| G12 | topExcess <= Err | OPEN: complete same-family signed top excess. This is the decisive supplier, not a definitional field. |
| G13 | ThinScales D ell X' theta | Paid in the native selected dyadic comparison at its actual conductor regime; realize its nonthick ratio condition. |
| G14 | LipW D ell | Replaced by native actual prime-power width/freezing comparison, with the original width conditions. |
| G15 | DerivInt D ell Cd | Paid by native Gz/character movement estimates. |
| G16 | ValuesAtX D ell x eps CL | Replaced by the selected PairGood window for the at-most-three nonprincipal characters. Their bound is not assumed for a fixed arbitrary character. |

Sources: [native dyadic cost windows](../RHLean/Analysis/AlpogeThin/NativeDyadicCostWindows.lean),
[native dyadic thick characters](../RHLean/Analysis/AlpogeThin/NativeDyadicThickCharacters.lean),
[native zeta balance](../RHLean/Analysis/AlpogeNativeZetaBalance.lean),
[native complete projection](../RHLean/Analysis/AlpogeNativeCompleteSourcePayment.lean).
Use the actual selected q,d throughout each window, not new pairs at every height.

### SmallCosts (3)

| ID | Original requirement | Native status |
|---|---|---|
| C01 | moveCost <= x^(1/2+eps) | Replaced by paid native mean-height movement, using available scalar headroom; displacement condition retained. |
| C02 | 2 f (x+1) theta <= 1/x | Paid by nativeDyadicCostWindows_eventually under actual host polynomial size and original thin scale. |
| C03 | 6 f (x+1) (eta+1) <= b/x | Paid by the same theorem on the native width deviation h, subject to its actual upper bound and b lower bound. |

### SizeWindows (16)

| ID | Original requirement | Native status |
|---|---|---|
| W01 | 3 <= x | Eventual threshold. |
| W02 | 0 < eps | Choose fixed positive eps < 1/52 before scale. |
| W03 | 0 <= C | Actual fixed cost exponent; verify its nonnegativity and uniformity. |
| W04 | 0 < n | Paid by actual finite group nonemptiness. |
| W05 | 0 < b | Paid by exponential lower bound. |
| W06 | 0 <= aE | Realize the actual nonnegative error scale. |
| W07 | aE <= 2 x b | Realize actual geometric scale, not an assigned value. |
| W08 | x^(-eps/8) n/2 <= nT | Realize actual top-set cardinality. |
| W09 | x^(-eps) <= nT2/n | Realize actual thick-set cardinality. |
| W10 | nT2 <= n | Paid by Finset.card_le_univ. |
| W11 | x^(1/2-eps) <= m | Paid on square clock m=R by alpogeNativeSquareMultiplicity_pageN_of_largeX. |
| W12 | m <= x^(1/2+eps/2) | Paid by the same theorem. |
| W13 | x m <= k | Paid numerically at k=x R; prove this is the physical parameter. |
| W14 | k <= n^2 x^(1/2-eps) | Paid numerically at k=x R on the same PageN host. |
| W15 | Err <= original explicit geometric bracket | Scalar accounting paid by normalizedCosts_add_remainder_le using the actual cost bracket. The signed excess bound G12 must still be earned. |
| W16 | 26 <= x^(3 eps/8) | Paid by alpogeNativeLargeX_of_threshold_le. |

Sources: [size absorption](../RHLean/Analysis/AlpogeThin/NativeGeometricCostWindows.lean),
[square multiplicity](../RHLean/Analysis/AlpogeNativeSquareMultiplicity.lean),
[large scale threshold](../RHLean/Analysis/AlpogeNativeZetaWindowWitness.lean),
[same-ideal lattice and theta realization](../RHLean/Geometry/NativeSquareHostRealization.lean).
The latter realizes base lattices and sections, not the measured rank, height,
thick-set, and loss witnesses of the final family.

## 2. New direct arithmetic payment

The original normalized local shift price is at most

    12*(log(4)+2)*c*ceil(Amax/beta)/(b*Delta).

Let E=exp(x^(eps/3)). On the original width regime b>=exp(x^eps),
beta>=b/(n E), c<=4 exp(x^(eps/4)), Amax/b<=x+1, n<=x^3,
Delta>=x^(-eps), and nonnegative shift/height data, we have

    ceil(Amax/beta) <= 4*x^4*E,
    12*(log(4)+2)*c*ceil(Amax/beta) <= 768*x^4*E^2.

For large x, 768*x^(5+eps)<=E and E^3<=b.
Consequently the complete normalized shift price is <=1/x, uniformly in
all physical parameters after eps is fixed. The native prime-power theorem
uses the actual cutoff and divisor to transfer this bound to the original
TT/lift/prime sum. This is one concrete part of the loss budget, not the
whole loss inequality: the low-central exclusions, local recovery gain,
the other local deductions, and their mean compatibility remain open.

The new global Gz movement follows by subdividing any interval [z,y] with
1<=z<=y into unit cells and applying the existing arithmetic move theorem.
It implies

    Gz(x) <= mean_TT Gz(v_t) + M*mean_TT |x-v_t|,
    M=log(4)+4.

The existing scalar proof has headroom 4*x^(1/2+eps). Its generalization
pays the entire remainder of that size; it preserves the original theorem
as a specialization. Thus the constructed signed-slope mean with analytic
price <=x^(1/2+eps) gives the original scalar exponent as soon as the
actual mean displacement costs <=3*x^(1/2+eps). No pointwise |v_t-x|<=1
is needed for this last recovery. The mean still has to come from the
actual geometric/analytic family. The square-size constructor specializes
the existing PageN multiplicity proof to this same scalar cost consumer.

Implementation:
[NativeScalarSupplierPayment](../RHLean/Analysis/AlpogeThin/NativeScalarSupplierPayment.lean)
and [terminal audit](ALPOGE_SCALAR_SUPPLIER_PAYMENT_AUDIT_20261124.lean).
These proofs require hosted checking; the audit does not certify unproved
premises.

## 3. Exact next mathematical suppliers

The already constructed dyadic signed-slope theorem retains the eleven
physical slope conditions (HidaSetting, DIV, EComp5, HComp, Count5, Slopes,
QuotientSlopeBoundsWith, LossBounds, SlopeIneq, HHBound, FParams) and strong
error windows and B0/Nc bounds. The native mean-loss comparison on main
can replace LossBounds by the two actual averaged inequalities. The
one-sided period comparison on #1201 can replace exact period equality,
using the existing period-DIV theorem; actual measured degree and
reverse derivative integrality are still required. The two substitutions
must be applied on the same physicalData, not independent witnesses.

Priority of the remaining work:
1. Construct the actual height/width/top/thick/recovery family on the same
   PageN and PairGood host at the square-clock parameters.
2. Pay the **complete** signed local recovery loss after the newly paid
   shift term, keeping low-central, ramified, dl/tauP and other costs;
   compare the actual gain and averaged losses.
3. Prove the measured quotient/degree/slopes and rank/mass budgets on
   that same family. Reuse actual native determinant descent, rank-growth
   jet budget and one-sided period direction, constructing geometry only
   where a specific remaining premise requires it.
4. Supply uniform constants and a simultaneous family on arbitrarily late
   complete multiplicative windows; use existing #1205 and #1206.
   The weaker cofinal square-window route must still cover every square
   in such a window and transfer to the complete real window; isolated
   favorable R do not suffice.

No independent proof of the missing complete Gz bound is claimed. Do not
restart downstream Landau, import a terminal RH theorem, or complete
unconnected geometric machinery merely because it occurs upstream.

## 4. Prior hosted failure and correction

The exact R20 head eee6c7a failed the mandatory preflight
[run 45320118677](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45320118677),
job 138196596172. The bounded diagnostic compiled NativeCMIsogenyPeriodMean
(including the one-sided class mean), NativeOneSidedIsogenyNorm,
NativeCMWeierstrassGroupTorsion and NativeCMWeierstrassMultiplicationUnramified.
It did not certify the full closure. The empty-product goal in
NativeCMLineBundleGenerators remained a reflexive-looking unit equality;
the attempted eq_self simp argument was unused. The correction now
explicitly closes the remaining goal after product simplification, using
reflexivity or unit extensionality. The original theorem is unchanged.
Full hosted preflight and axiom audit remain mandatory.


## 5. Replace whole functions of the 43 conditions, not their literal forms

The user has explicitly clarified that the 43 rows are a coverage map,
not a construction mandate. The invariant is the complete native
prime-power source, its exact centering, an independently earned gain
on that same source, every normalized cost, and uniformity. The actual
signed-excess estimate remains OPEN. The following two new finite
inequalities replace additional numerical and recovery requirements;
neither claims the geometric family has been constructed.

### Signed quadratic height recovery

Write S(x) for the literal principal prime-power ramp sum. The existing
ordered bounds prove at every positive x,y

    S(y)-S(x) >= (y-x)*nativeLambdaRecip(floor(x)).

This is the supporting line of the convex piecewise-affine sum, valid
even at prime-power jumps. Since log(y/x)<=y/x-1,

    y log y - x log x - (log x+1)*(y-x) <= (y-x)^2/x.

Keeping the affine Euler term gives the genuinely one-sided inequality

    Gz(x) <= Gz(y) + s(x)*(x-y) + (x-y)^2/x,
    s(x) = nativeLambdaRecip(floor(x)) - log x + gamma.

Sum over the same physical heights v_t=a_t/b and divide by the actual
nonzero top count. If their signed mean equals x, the first-order
term vanishes exactly, and the recovery debt is the variance divided
by x. Otherwise the signed first-moment term remains; it need not be
separately absolutized. The theorem is unconditional arithmetic, not
a bound on Gz itself. The native source is unchanged.

For example, mean-square displacement <=3*x^(3/2+eps) costs at most
3*x^(1/2+eps); the RMS allowance is of order x^(3/4+eps/2).
This exceeds the absolute-displacement scale of the preceding section.
A centered spread above x+1 is NOT permitted by the current analytic
payment at scale x. To exploit the wider symmetric spread use the
existing selected family at a comparable larger scale s, with
Amax/b<=s+1 and s<=2*x, or separately relax its upper-height premise
and prove the cost. All physical heights still belong to the selected
analytic window. For fixed exponents the comparison s<=2*x changes
only the constant, which the native handoff permits. No geometric
selection of such centered families is claimed.

### Smaller rank window from the exact joint cost ratios

Let E>=1, with T,Delta,n,m,b,k all positive and aE>=0. The existing
normalization is exactly

    B/Q = 2*aE/(m*b*Delta)*(1+m^2/k)
          + 4*n*m*E/(T*Delta) + 2*k*E^2/(n*T).

The new arithmetic theorem proves B/Q <=18*m*E^3 from only

    aE <= 2*m^2*b,
    m^2 <= k <= n*T*m,
    n <= 2*E*T,
    1 <= E*Delta.

Indeed the three separate costs are at most 8*m*E,
8*m*E^3, and 2*m*E^2. For x=R^2-1, choose m=R and E=x^eps.
Compared with the original k>=x*m this permits a smaller k by a
factor approximately R. The upper k limit is now the joint quantity
n*T*R. The top count may be as low as n/(2*x^eps); the literal
x^(-eps/8)*n/2 condition is not needed for this scalar conclusion.

If the physical same-family signed excess is bounded by x^(C*eps) B,
the normalized geometric cost is at most
18*R*x^((C+3)*eps). Combining it with the existing paid analytic
remainder and a paid quadratic recovery gives a one-sided bound
O_eps(R*x^((C+3)*eps)). This is RH-strength for fixed C and arbitrarily
small positive eps, with the required uniform window quantifiers.
The constant 18 and modest fixed comparison factors cause no
exponent loss in the already-verified handoff. These are paper
consequences of the precise finite Lean theorem and existing
consumer; they are not assertions that its missing physical bound
or family exists.

The numerical lower-rank relaxation does not prove that the geometric
recovery/degree theorem works at k=R^2. Use the smaller k only when
its actual rank and gain are established. Conversely do not require
the stronger original numerical window merely because it was used
in the upstream proof.

### Exact remaining attack

1. Actual recovery gain plus retained low-central, orbitwise and ramified
   losses: the shift cost is already paid, not a remaining target.
2. Actual measured rank/slope and degree inequalities, with the same
   original physical top excess, and with the joint normalized budget.
3. Compatible family on the already-selected dyadic host and prime-pair
   windows, with actual positive widths and a paid signed height
   displacement/variance; fixed constants before the window choice.

A substitute proof on the native complete candidate-removal, NNS, or
square-block source is admissible if it independently earns the same
critical estimate with those quantifiers. There is no obligation to
realize the original geometry when another native proof supplies it.
The two reductions above simplify the payment and recovery, not the
missing complete signed gain. No new terminal RH wrapper is added.

Implementation: [Native quadratic recovery](https://github.com/OVVO-Financial/RH_Lean/blob/8fdfe7b76cf0763c3480ae069042a08ba80b0524/RHLean/Analysis/AlpogeNativeQuadraticRecovery.lean)
and [six-root audit](https://github.com/OVVO-Financial/RH_Lean/blob/8fdfe7b76cf0763c3480ae069042a08ba80b0524/research/ALPOGE_NATIVE_QUADRATIC_RECOVERY_AUDIT_20261124.lean).
Hosted validation required. Prior verified and draft geometric sources
are preserved.


## 6. Attach the smaller rank to the actual constructor and the existing scalar output

The original same-half-different lattice and theta construction is available
for every natural k satisfying R+3<=k. The new
[reduced-rank realization](https://github.com/OVVO-Financial/RH_Lean/blob/8fdfe7b76cf0763c3480ae069042a08ba80b0524/RHLean/Geometry/NativeSquareReducedRankRealization.lean)
specializes it to m=R, k=R^2, R>=3, on the SAME selected PageN exponent and
WinPair. It preserves the actual different factorization, coprimality, Galois
invariance, positive Hermitian form, nonzero holomorphic theta sections,
automorphy and invariant fiber norm. The actual rank over the ring of integers
is R^2+R-1, and over Z it is (R^2+R-1)*(4*2^e), by the original rank theorems.
This is a real base-space realization, not an assigned rank. It does not
construct the restriction gain, measured degree, or recovery losses there.

The scalar payment theorem
`alpogeNativeGzArithmetic_le_of_centeredJointRatios`
combines the signed quadratic recovery and the three-cost inequality at
the actual finite TT and T2. It accepts the literal mean Gz inequality
from the existing selected dyadic signed-slope payment, with the same
normalized costs and the paid analytic remainder. For x>=1, x<=m^2,
C>=0, epsilon>=0, the joint ratios and centered variance debt
<=3*x^(1/2+epsilon), its conclusion is

    Gz(x) <= 22*m*x^((C+3)*epsilon).

Indeed the geometric part is at most 18*m*x^((C+3)*epsilon), and each
of the four units of analytic/recovery allowance costs at most
m*x^((C+3)*epsilon). Thus this is the existing scalar endpoint with a
harmless explicit constant on the native square clock. It does not require
the literal SizeWindows record or import a finished RH theorem. The
complete actual signed-excess estimate, its compatible geometry if used,
and uniform windows remain the genuine unpaid inputs. The new nine-root
audit includes the actual rank construction and direct scalar payment.
Hosted verification required.


## 7. User correction: apply the existing signed recovery, do not redesign it

The original parameter regime m=R, k=(R^2-1)*R is restored as the
active route. The optional unverified R22/R23 quadratic-height and
reduced-rank modules are parked in the reachable commit
[8fdfe7b](https://github.com/OVVO-Financial/RH_Lean/commit/8fdfe7b76cf0763c3480ae069042a08ba80b0524); their proofs and
reports are preserved in history. They are not required in the active
build or a reason to construct a new recovery mechanism. The R21
native payments and all prior genuine geometric constructions remain.

The exact-head run [45323160932](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45323160932)
failed static manifest sorting, before Lean ran. Regenerate the root
from the complete tree, not by insertion beside a similarly named
module. The earlier R21 static audit passed but the changed closure
was cancelled on a superseding push. No success is inferred from that.

### Use the upstream proved recovery route

`GainBoundAtPairUniform` is a proposition, not itself an unconditional
theorem. Its actual supplying result is `gain_bound_all_of_star` in
[NotSingularOfCentral](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/NotSingularOfCentral.lean).
It accepts ParameterChoice', GainBoundConstants, adm9 and StarAll.
The higher proved theorem AuxBlock8.Pf.stmtF in LogarithmicSums.lean
accepts AdmF and returns ConclusionOnFamily, with a uniform cost
constant and a defect function tending to zero. Do not reprove its
gain summation or assume AdmF.

There is a particularly relevant shorter original route:
[AdmissibleFamilyNoKernel.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/LocalToGlobal/GroupLattices/AdmissibleFamilyNoKernel.lean).
Use its dependency trace through linkG_fam_noKer and
link_of_local_closed. The latter takes Loc (supplied by loc_proved),
TrivialStabiliserFiniteClasses, Joints.StdSubAt, Adm2F and NPDescF
on the actual family class. These are substantial compatibility
requirements, not four automatically satisfied propositions.

The source's zeroCh changes only the auxiliary Ch field. Direct
inspection of LatInst, LatTied, yProd, NP and LatticeLengthsAtPlace in
[IsResidueClassZero.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean)
shows that NP and its quotient length depend on vOf, the actual orbit
operators, Vram, and the original tau/Sv, not on Ch. The original
no-kernel theorem nevertheless proves its two auxiliary valuation
premises using the zero chain. Do not present these as bounds on the
actual physical maps. A native application may omit that auxiliary
chain only after proving the same independence for every retained
consumer, including its comparison to the actual Ga, IO and degree.
Do not import a finished RH theorem or replace any physical gain by zero.

### Direct native applications

[NativeServedPrimeApplication](../RHLean/Geometry/NativeServedPrimeApplication.lean)
follows the original invariant-factor and inverse-shift arguments in
ElementarySymmetricExpBound.lean, then invokes the existing
NativeServedPrimeLength.lengthFromAllBut_saturated. It removes the
need to assume a second set of exceptional generators on the smaller
lattice or an independent saturation statement. It uses the original
quotient image, its PID basis, the actual inverse shift, and the
fraction-field ramified subspace. Given the exceptional counts on Mna,
the actual restriction-product transfer, and the original stopping
inclusion on M, the derived length on the ramified intersection is

    length <= vUnit * d * (e + tau + 2*S*s).

The actual restriction submodule is NB intersect a^(e+tau) M,
further restricted to the actual fraction-field ramified part.
There is no replacement rank, lattice or new gain inequality. The
original theta-kernel expansion must still supply the exceptional
sets on Mna, the operator transfer and the stopping inclusion on M.
Their actual attachment to the original host and served orbit remains
open. The length theorem itself is reused, not reconstructed.

[NativeExistingRecoveryPayment](../RHLean/Analysis/AlpogeThin/NativeExistingRecoveryPayment.lean)
applies the already proved mean-loss version of physicalTopExcess
directly within the existing constructed dyadic consumer. It selects
the same host and pair once and preserves the original scalar cost
and size regime; it does not require pointwise recovery losses.
The original height interval from InWin gives x <= a_t/b <= x+1
whenever k>=x and sigma>=1. This pays the original height-movement
input without a new rank or variance regime. The zero-debt
one-sided period theorem also supplies the existing DIV premise
from the genuine measured degree bound and actual period lower bound.

The seven-root audit is a hosted proof check for these applications.
No claim is made that it proves the native family exists, that the
full upstream dependency closure has been independently validated,
or that the critical signed-excess bound or RH is proved.

### Active attack

Use the original admissible parameters and existing recovery theorem.
Apply the original local expansion to the actual native module, with
its stabilizers, class representatives, standard submodules, orbit
weights and comparison map. Use the existing lattice length and
native descent theorem at that very module. Trace NPDescF to the
literal local/global lattice image and the actual lengths. Prove
the remaining physical identifications and measured slope budgets,
not another theorem whose premise is the desired complete bound.
Use the already merged #1205 and #1206 only after the same-family
uniform window estimate is supplied.


## 8. Final-PR objective: close the suppliers using the original proof

The R24 run 45324333102 passed the static source audit and failed its
mandatory preflight on two served-prime coercions and redundant tactics
in NativeCMLineBundleGenerators. The repairs preserve their exact
statements. No successful full build is inferred.

### Pay the actual integral extension by smooth normalization

The pinned Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 already has:

- IsFinite.of_isProper_of_locallyQuasiFinite, in
  Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean;
- Scheme.Hom.normalizationPullback and its Smooth instance,
  Scheme.Hom.normalizationDesc and normalizationDesc_comp, in
  Mathlib/AlgebraicGeometry/Normalization.lean.

No general smooth-scheme normality reconstruction is necessary for the
proper elliptic case. A DVR R is integrally closed in its fraction field
K, so the relative normalization of Spec K -> Spec R is Spec R. For
the actual smooth group model G, smooth base change shows the relative
normalization of the generic fibre projection j is G. The existing
flat commutative graph Ga of the given generic homomorphism has
quasi-finite first projection p. Properness follows from the closed
immersion into the product and properness of the target elliptic
equation, so p is finite. Its generic projection is the original
isomorphism e. Factor j through p using e^-1 on the generic fibre.
By the universal property of relative normalization, this factorization
extends to a section s of p. Since p is an isomorphism after base
change to K, p*s is the identity there. The existing flat generic-fibre
faithfulness on Ga gives p*s=id globally. This constructs the actual
inverse and extends the original homomorphism; uniqueness and the
group law follow from the same generic-fibre faithfulness.

[NativeCMWeierstrassIntegralExtension](../RHLean/Geometry/NativeCMWeierstrassIntegralExtension.lean)
implements this argument and invokes the already constructed literal
dual-number tangent vector of the target equation. No abstract
extension premise or assigned geometric period is introduced. The
new theorem is proposed proof source pending hosted checking.
The two actual class-model generic homomorphisms and their normalized
tangent scalars, all-place integrality and global family identifications
still have to be supplied. In particular this is not a claim that
the entire period/degree input, the signed-excess estimate or RH
has been proved.

### The final acceptance gate

This PR is the completion branch, not a sequence of future PRs for
additional conditional consumers. Retain the original recovery theorem,
native source and original admissible parameters. Close the actual
local compatibility, measured global costs and same-family uniformity.
A green intermediate build is not proof completion. Before removing
draft status or proposing final merge, the branch must contain a
closed theorem of type `RiemannHypothesis` obtained by applying
the existing native handoff to an independently proved complete
critical estimate. Audit the theorem's full type and its transitive
proof and actual source constructors, with only the accepted standard
terminal axioms. A theorem assuming the bound, a new equivalent
hypothesis, a zero-map physical substitute, a tautological geometric
assignment, or an imported finished RH theorem does not satisfy the
gate. Until then the PR remains an incomplete research draft.

## 9. Supplier-first application: the actual normalized class lattices

The R25 [mandatory preflight](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45325705993/job/138214875115)
failed on two argument-order errors in the scalar shift-cost proof. Both
repairs preserve the exact inequalities; the full build was skipped.
The R25 integral-extension theorem is not thereby certified.

The existing original supplying proof, `GlobalTheory.exists_cm_curves_of_weierstrass_curves`
in [ExistsCmCurvesOfWeierstrassCurves.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsCmCurvesOfWeierstrassCurves.lean#L125),
uses the ratio of the actual homotheties of the seed and inverse-ideal
models, then applies the two elementary ideal inclusions. In native
coordinates the homotheties are u0^(-1) and uC^(-1), so the ratio is
beta_C=u0/uC. No new period theory is necessary.

Apply the existing `tangentCoordinatePeriods_mem`, `inverseIdealPeriod_forward`
and `inverseIdealPeriod_reverse` directly in
[NativeCMInverseIdealClassModels](../RHLean/Geometry/NativeCMInverseIdealClassModels.lean).
The new normalized-family constructor uses the existing actual common
discriminant-one model constructor and retains the original principal
seed, comparison and both actual normalized lattice inclusions at the
distinguished complex embedding. In particular beta_C is not assigned
independently of the constructed equations.

The next exact consumer is `mean_log_covolume_ge_mean_classGroup` in
[NativeCMIsogenyPeriodMean](../RHLean/Geometry/NativeCMIsogenyPeriodMean.lean).
Its input is beta_C in the common number field, both inclusions across
all embeddings and reverse derivative integrality. Reuse the original
all-section tangent proof in
[NativeCMWeierstrassMorphismTangent](../RHLean/Geometry/NativeCMWeierstrassMorphismTangent.lean)
for a morphism between distinct equations. The proposed cross-model
lemma reads c from the actual dual-number tangent vector and obtains
sigma(c)=alpha*u_source/u_target by comparing the original derivatives.
This is the same existing derivative argument, not a new cancellation
mechanism. The equality does not assert a morphism exists.

The first remaining leaf for this period application is the actual
cross-model generic isogeny from the existing rational lattice map,
with coefficient descent and its true exponential action. Then apply
the original integral extension at the local models, compare the
tangent scalars and use the existing one-sided class mean. In parallel
the existing local recovery and measured slope suppliers remain to
be instantiated. Three new axiom-audit roots are proposed. No successful
Lean closure, all-place period supplier, complete signed estimate or
RH is claimed; hosted validation remains mandatory.

## 10. Supplier-first application: descend the literal reverse class isogeny

The exact supplier at the preceding checkpoint is the existing
`exists_latticeIsogeny_eq_div` theorem, reconstructed from
[AddMonoidHomEqZeroOfEventually.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AddMonoidHomEqZeroOfEventually.lean).
It needs the actual multiplier in a coefficient field and the actual
kernel x-coordinates in that field. Do not assume either of these
for the newly constructed inverse-ideal models.

The native `exists_representatives` supplies the actual finite index;
the standard subgroup relative-index theorem kills its kernel by
that positive integer n. Choose an actual nonzero two-torsion target
point with nonzero x-coordinate (existence follows from its nonsingular
cubic). If w is its period parameter and z=alpha^(-1)*w, then 2n kills
z and all z-r_t modulo the source lattice, while n kills the actual
kernel representatives r_t. The existing `weierstrassP_mem` theorem
of torsion algebraicity, reconstructed from
[IntegralJAndAlgebraicData.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralJAndAlgebraicData.lean),
applies to every term; lattice points have the existing value zero.

The existing `weierstrassP_mul_eq_sum` identity gives

    alpha^2 * wp_target(w)
      = sum_t (wp_source(z-r_t) - wp_source(r_t)).

The right side is algebraic; the target coordinate is algebraic
and nonzero. Division and algebraicity of powers imply the actual
alpha is algebraic. Adjoin alpha and the finitely many actual kernel
x-coordinates to the common field, exactly as for the native CM
generator. Apply the existing rational formula theorem on this field.
The new [torsion applications](../RHLean/Geometry/NativeCMWeierstrassTorsionAlgebraicity.lean)
are proposed Lean proofs of these steps, with the actual period
inclusion and both algebraic equation invariants as inputs.

The new [actual reverse class map](../RHLean/Geometry/NativeCMInverseIdealClassModels.lean)
applies that result to the previously constructed tangent-coordinate
periods of the two actual equations. Its multiplier is beta_C^(-1)
times the embedded nonzero ideal element; the algebraic equation
invariants come from the existing c4/12 and c6/216 identities.
The field extension contains the original common model field.
The point-map and kernel-degree statements are the literal original
rational formula, not a replacement map or assigned derivative.

Five additional audited roots are proposed. The exact next
application is to extend this rational map between the actual two
short equations to their scheme morphism and conjugate by their
existing equation isomorphisms. Then use the submitted R25 integral
extension and cross-model tangent comparison, transport across all
embeddings and invoke the original one-sided period mean. Forward
maps and the common-family assembly remain to be attached as needed.
The actual scheme map, all-place period supplier, signed-excess
bound and RH are not proved by these source changes. No hosted
verification of the new roots is claimed; no new module or
conditional RH endpoint is introduced.

## 11. Integrate the existing Phi map in the string-first suppliers

The native map is already `complexRealPair` in
[DistinguishedPrimeTransitionSupport](../RHLean/Analysis/DistinguishedPrimeTransitionSupport.lean),
not a newly chosen coordinate system. Its existing inverse, addition,
multiplication and norm identities supply the exact additive equivalence,
the conjugated multiplication action and the normalized Gram and area
formulas. Compare the existing proof of the same identities in
[STABLE_FAR_PERRON_REALIFICATION](STABLE_FAR_PERRON_REALIFICATION.lean).
No new cancellation mechanism or norm hypothesis is introduced.

For z=a+bi, Phi(z)=(a-b,a+b). For any multiplier c, its action in these
coordinates is the matrix [[Re c,-Im c],[Im c,Re c]]. The determinant
price is |c|^2. Both real and imaginary parts of z*conj(w) are retained
by the normalized Gram and oriented determinant (the latter has the
orientation of Im(z*conj(w))). The factor 1/2 compensates for the
determinant two of Phi. The signed real projection is the diagonal mean.

Use these SAME identities in the current supplier chain:

- The existing `covol_eq` in
  [NativeCMIdealIsogenyPeriods](../RHLean/Geometry/NativeCMIdealIsogenyPeriods.lean)
  now pays its homothety determinant by the real-pair area identity.
  The actual period lattice, fractional ideal, basis determinant and
  absNorm remain unchanged. The existing one-sided class mean consumes
  the same covolume theorem with exactly its original hypotheses.
- [NativeCMPeriodNormInvariant](../RHLean/Geometry/NativeCMPeriodNormInvariant.lean)
  identifies the normalized Phi parallelogram area with the original
  ZLattice.covolume, and uses the real area scaling in the existing
  homothety proof. Keep the full discriminant and original period scale.
- [NativeCMWeierstrassRationalIsogeny](../RHLean/Geometry/NativeCMWeierstrassRationalIsogeny.lean)
  maps the actual period additive subgroups by the existing invertible
  Phi. The image of the actual multiplier commutes with that map.
  Mathlib's injective relIndex transport applied to the existing
  kernel-index theorem gives the identical degree.
  [NativeCMInverseIdealClassModels](../RHLean/Geometry/NativeCMInverseIdealClassModels.lean)
  now returns that actual real index equality in the original reverse
  rational-isogeny constructor, not a second chosen degree.
- [NativeCMSerreSchemeMetric](../RHLean/Geometry/NativeCMSerreSchemeMetric.lean)
  applies the normalized energy to the original scheme Gram on the
  actual integral Lie eigenvector, with the same canonical sigma metric.
- [NativeMeasuredComponentNorm](../RHLean/Geometry/NativeMeasuredComponentNorm.lean)
  rewrites the integrand in the original measured norm and applies the
  existing exact mass payment to those real-pair coordinates. No measure,
  component, rank, mass, or geometric Gram is chosen to fit the formula.
- [NativeMeanEnergyDescent](../RHLean/Geometry/NativeMeanEnergyDescent.lean)
  transports the original complex operator-energy hypothesis bijectively
  to Phi vector coordinates and applies the existing rank-saturation
  determinant estimate. Keep the original complex rank in the exponent.
  This is the existing mean-energy proof, not a joint operator bound.
- The complete signed arithmetic inlet is already the existing
  [literal ASK-MAIN to NNS identity](ALPOGE_LITERAL_ASK_MAIN_NNS_COORDINATE_MAP_20261121.md).
  Use the real diagonal projection only after original character
  recombination; do not discard phases or replace the signed gap by
  unsigned energy. No new arithmetic inlet is required.

The remaining exact period application is still the genuine cross-model
scheme morphism and its local extension at the original good-reduction
models, plus all-embedding compatibility and the one-sided integral
derivative norm. An invertible real coordinate alone does not prove these
arithmetic statements. Reuse the already submitted rational map and
existing extension/derivative proofs. Likewise realification of the
measured integral does not realize the actual Petersson family, and
operator-energy equivalence does not supply an unproved energy bound.
Do not rebuild any of these real algebraic calculations in the upstream
complex representation. Eighteen guarded roots are added, no new Lean
modules, no new conditional RH endpoint, no imported terminal RH theorem.
All changes are proposed source pending exact-head hosted verification.
The full signed source estimate and RH remain OPEN.

## 12. Correct status: existing quantitative proof, unfinished native application

The existing growth bound is **not** the mathematical discovery
objective of #1201. The pinned upstream
[`proposition_at_point`](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean)
has type `GrowthBoundAtPoint`, defined in
[GrowthBoundGivesRiemannHypothesis](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean):

    forall C eps x, GrowthInequalityDataExists C eps x ->
      Gz x <= x^(1/2 + (C+3)*eps).

The existing `chain_at_alt` in
[PChain](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean)
applies this theorem to the supplied chain data. The existing
`chain_analytic_at_point` in
[AnalyticFirstToLatticeDiscriminant](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/AnalyticFirstToLatticeDiscriminant.lean)
follows the analytic-to-lattice, discriminant and first-variant
reductions to that application. Trace their actual hypotheses and
supplying proofs; neither a proposition definition nor a conditional
theorem alone certifies the unconditional result.

The native consumer
[`nativeConstructedDyadicSignedSlopePayment_of_meanLoss`](../RHLean/Analysis/AlpogeThin/NativeExistingRecoveryPayment.lean)
already composes the physical signed top-excess comparison, analytic
payment and normalized-cost absorption, yielding the existing
square-root-plus-epsilon mean estimate under its actual hypotheses.
Use this proof as written. Pay its original family, recovery, measured
cost and uniformity inputs using the pinned supplying proofs and the
existing native identifications, including section 11's Phi transport.
InWin height proximity, complete signed source, actual Frobenius/inertia,
and original square clock must be preserved.

The existing
[`statementOCGz_eq_native`](../RHLean/Analysis/AlpogeNativeBoundHandoff.lean)
identifies the literal finite prime-power source with
`alpogeNativeGzArithmetic` without any estimate. Keep this exact source
identification and prove the remaining compatibility with the pinned
supplier application. The already-merged #1205 handoff exposes
`riemannHypothesis_of_eventualRealBound`,
`riemannHypothesis_of_squareClockBound`, and
`riemannHypothesis_of_smallEpsilonWindowBound`. Use the weakest
genuinely supplied input. #1206 is a distinct positive-moment alternative
only if its actual stronger input is available.

Status separation:
- Existing upstream growth theorem and proof mechanism: EXISTING PROOF.
  Do not reinvent them or label them as an undiscovered estimate.
- Native same-family applicability and exact transport: OPEN until
  actual prerequisites are discharged and Lean verifies them.
- Native eventual critical estimate and closed `RiemannHypothesis`:
  OPEN until that application has been verified end to end.

For every open item, name the precise hypothesis, existing upstream
supplying proof, native identification, remaining prerequisite and
hosted status. No independently hypothesized critical bound, terminal
RH import, artificial geometry/height, or new cancellation mechanism.
The string is the existing proof securely attached to RH_Lean, not
another mathematical discovery. The stone bridge is subsequent
simplification of the verified connection. This section is a proof
contract/status correction only; no new proof source or verification
claim is made.

## 13. String-first continuation: the actual terminal principal cyclic inlet

The pinned terminal `MainTheorems.lean` reaches `UpperTheory.FinalTheorems.everyCharacter`, then `every_character_of_literature_of_vWin`, `every_character_of_theta_integrals_local_matching`, and `every_character_of_green_v_win`. In [ZeroFreeAllOfTopG.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean), the actual consumer applies `zeroFreeOn_of_tiedWin_cyc` at the cyclic level of each primitive character. The window scale in the terminal application is 3/2. We need only the primitive principal specialization, **before** zero-freeness or RH is deduced. The earlier `proposition_at_point` reduction is not itself a certificate of this application.

The exact supplying proof is [level_gm_le_on_family_scales](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/PrimitiveCosets/LevelGmLeOnFamilyScales.lean), which invokes the actual tied-core proof, including [core_gm](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean) with genuine EAtH and CoreAtH on the same host, and the complete signed cost and character movement suppliers. Its exponent is 1/2+(eD+eL+7)*eps. The real prerequisites are the fixed eD,eL,eps1, actual principal FamilyClassConnected/ChainTied, EFamC, and complete HasWindows of the same family. See the existing supplier map in docs/RHLEAN_ALPOGE_NATIVE_DESCENT_PAYMENT_20261122.md. These remain proof obligations; do not infer them from the terminal zero-free theorem or from a definition of their types.

In the existing NativeExistingRecoveryPayment module, the principal cyclic KEPT set is proved in source to be exactly {PChar.one}. Therefore Nt is empty and the actual Gm equals statementOCGz and the native prime-power expression, without a new estimate. The window transport applies the quantifier order of [TopWin.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopWin.lean) and [Window.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Window.lean) to #1205's exact SmallEpsilonWindowBound (eD+eL+7) eps1, with coefficient 1 and threshold max(Y0,x1,1). Thus the string needs the original uniform principal window application, not a stronger eventual all-real estimate, a newly discovered bound, the full all-character conclusion, or new cancellation. Three additional audit roots. This is exact arithmetic/window transport and not a closed RH theorem.

Checkpoint 6c893f3: mandatory preflight [138400433724](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45381092366/job/138400433724) failed in eight reached geometry modules. This continuation repairs the reported quotient, instance, coercion, explicit projective-witness and group-law elaboration sites. The identity section is checked directly on [0,1,0] rather than rerunning field-point group-law reduction. These repairs and the new inlet require hosted validation; no successful Lean build, genuine tied-family application, or unconditional critical estimate is claimed.

## 14. Apply the existing cross-model reverse isogeny supplier

Hosted checkpoint [22539fc](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45393478344/job/138443224895): NativeExistingRecoveryPayment and NativeCMWeierstrassRationalSchemeOpen compiled. The mandatory preflight failed in downstream geometry; the full build was skipped. Principal cyclic source identification and the existing conditional window transport are compiled, not an unconditional bound.

The continuation retains the actual inverse-ideal class models, period lattice inclusion, nonzero multiplier, and finite-field rational formula. Generalize the existing cleared polynomial identity to distinct source and target cubics, derive it from the actual analytic point formula, and descend it by the injective field embedding. Use the source denominator-open map with the genuine target equation and the existing two-patch kernel-open gluing theorem (already generic in source and target). Enlarge the finite coefficient field using the existing point-off-denominator supplier. The resulting scheme morphism is required to be a monoid homomorphism with the exact complex lattice-point action. Apply this to the actual reverse class-period isogeny using the original normalized models and multiplier, not a postulated map or a replacement height. The existing upstream period comparison is pinned in ExistsCmCurvesOfWeierstrassCurves.lean and the scheme gluing source in MulLeftCompOfPullbackPointEquivMul.lean. This is supplier application, not a new estimate or an import of RH.

The next attachment is conjugation to the original integral models, integral extension and genuine tangent comparison at every embedding, then the existing one-sided class-period mean and DIV. The complete uniform tied-family application still needs the genuine recovery, measured degree, rank/mass, and signed scalar-cost suppliers. Ten additional guarded roots. Explicit coefficient-map identities and both syntactic CM-field instance heads also address reported elaboration sites. Other failed atlas, Serre, tangent and translation checks remain open. Refresh changed-source manifest entries from the exact staged source bytes; the new source and audit are not yet Lean-verified. No unconditional critical bound or RH proof is claimed.

## 15. Exact-head preflight repair (92f46c8)

The mandatory [preflight](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45397859051/job/138458541468) failed in six reached modules: NativeCMSerrePolarization, NativeThetaCuspTensorVacua, NativeCMWeierstrassThetaAtlas, NativeCMWeierstrassOpenPoint, NativeCMWeierstrassMorphismTangent, and NativeCMWeierstrassTranslationGroup. The prior cross-model RationalIdentity and RationalSchemeOpen modules, CMOpen coefficient descent and ShiftedVacua compiled. The full build and guarded terminal closure remain unverified.

Repair the literal trace-form normalization, matrix-coordinate index and self-duality transport, let-bound shifted family, actual localization witnesses, and the finite coefficient extension using the pinned Mathlib IsAlgClosed.exists_pow_nat_eq theorem. Transport section evaluations across point equalities with their dependent chart-membership witnesses; give explicit base-change morphism types and evaluation equalities in the tangent comparison; use typed point-group equalities in translation. No geometric assumptions, bound statements, or existing guarded roots are removed. Replace deprecated dependent-if rewrites. The overlapping-instance warning is scoped only to the DVR lemma: the pinned Mathlib class IsDiscreteValuationRing explicitly requires IsDomain as a parameter, so neither required instance can be deleted. Translation has a bounded 8M heartbeat budget rather than 4M while the explicit proof repairs are checked. The resulting source requires hosted Lean validation; no claim of a green build, completed geometric supplier, or RH proof is made.

## 16. Exact-head preflight repair (6937f9a)

The [linked preflight](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45408740936/job/138499685869?pr=1201) reached seven failing modules: NativeCMSerreMixedPeriods, NativeCMSerreSchemeBundle, NativeCMSerreBundleGram, NativeThetaCuspTensorVacua, NativeCMWeierstrassThetaAtlas, NativeCMWeierstrassMorphismTangent, and NativeCMWeierstrassRationalGlobal. NativeCMSerrePolarization, NativeCMWeierstrassGraphKernelTorsion, NativeCMSerreGramForm, NativeCMWeierstrassSectionJet and NativeCMWeierstrassOpenPoint compiled. The full native build remains skipped after preflight failure.

The repair uses dependent dimension transport on the entire original mixed lattice, the actual tensor conjugation and coefficient action, the diagonal transition unit and explicit evaluation of the original trace frame, exact inverse-coordinate identities for the semicharacter, explicit chart witnesses, the original prime-ideal contradiction, and the already supplied finite-type instance and coefficient/point transports for both global rational maps. Statements and guarded roots are retained, without adding axioms, admitting proofs, changing CI, or expanding the proof target. Hosted Lean validation of the repair and further dependency closure remain required. This is a repair of reported Lean errors, not a claim of unconditional quantitative closure.

## 17. Consolidation of #1208 and exact-head repair (496398b)

#1208 is folded into this PR and closed as superseded. The consolidation
record and the retained G1–G7 gate map are in
[ALPOGE_ACTUAL_GEOMETRIC_SUPPLIERS_20261124.md](ALPOGE_ACTUAL_GEOMETRIC_SUPPLIERS_20261124.md).

[Run 45418252140](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45418252140)
on `496398b`: static audits passed; the warning-fatal changed-research
closure rebuilt 343 modules (the main merge touched widely imported
kernel sources) and failed after 29 minutes at
NativeThetaCuspFiniteLevelNorm. The bounded diagnostic pass then reached
NativeCMSerreSchemeBundle, NativeCMSerreEquationPoints,
NativeCMSerreBundleGram, NativeCMWeierstrassRationalGlobal,
NativeCMLineBundleSigmaMetric and a warning in
NativeCMWeierstrassThetaAtlasMetric before the 35-minute job cap
cancelled it. The cancellation also skipped the native-prerequisite
cache save, so the next run would have recompiled the same modules.
NativeCMSerreMixedPeriods, NativeCMSerreGramForm,
NativeCMWeierstrassMorphismTangent, ThetaAtlas, OpenPoint, SectionJet,
RationalSchemeOpen and the CMOpen layer compiled.

Repairs on the same statements (no hypothesis added, nothing weakened):

- FiniteLevelNorm: pass the `IsSB` component to `heis_neg_heis`; finish
  the `Pi.single` contraction with `Finset.sum_eq_single_of_mem`; rewrite
  only the target submodule `(C * span {s}) • L = s • (C • L)` because the
  same ideal indexes `rows` through its coprimality proof; give
  `Submodule.Quotient.eq` and `mem_smul_pointwise_iff_exists` their
  explicit arguments; state the additive map for
  `AddSubgroup.mem_map_iff_mem`; use `finsum_eq_sum_of_fintype`
  (`finsum_eq_sum` needs a support hypothesis); supply `IsCMField H.E` for
  the native host as ShiftedVacua already does.
- SchemeBundle: adopt #1208's rigidification body (see the consolidation
  record); #1201's body failed at this head.
- EquationPoints: the tensor scalar case used `smul_tmul'` backwards; use
  the three-step transport already compiled in `conjugateTensor_smul`.
- BundleGram: parenthesize `coefficientEvaluation … (fr.x i)`; give
  `sum_squareGram` its coefficient families explicitly (`?p k.1` is not a
  higher-order pattern, which exhausted the whnf budget).
- RationalGlobal: `have` instead of `letI` for the Prop instance (style
  linter), drop two unused simp arguments, and a bounded 1M heartbeat
  budget for the two-curve gluing theorem, whose proof mirrors the
  compiled same-curve proof but exhausted the default budget.
- LineBundleSigmaMetric: import NativeCMLineBundleGerms (home of
  `LB.wchart_inter_le`); `Real.exp_int_mul` does not exist in the pinned
  Mathlib, so derive the integer-power identity from `Real.rpow_intCast`
  and `Real.exp_mul`; rewrite `Finset.prod_pow` in the needed direction;
  drop unused simp arguments; omit the unused `Algebra R ℂ` section
  instance (also in ThetaAtlasMetric).
- research-iteration.yml: the changed-research job cap is 60 minutes so
  that compile plus the bounded diagnostic pass reaches the cache save.

These are proof repairs awaiting hosted validation. They do not discharge
any G1–G7 supplier premise. The hypothesis `h` of
`nativeSmallEpsilonWindowBound_of_principalCyclic`, the native critical
estimate and `RiemannHypothesis` remain OPEN.

## 18. Exact-head four-module repair and prediagnostic cache checkpoint (5dcb3c3)

The [mandatory preflight and diagnostic log](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45431015648/job/138576449633) failed first at NativeCMSerreBundleGram:175, then reported NativeThetaCuspFiniteLevelNorm:398, NativeCMSerreBundleSymmetry:73–74, and the NativeCMWeierstrassRationalGlobal two-curve theorem at the 1M whnf budget (its later unknown constant is a consequence). The diagnostic reached additional compiled prerequisites including SchemeEigenline, ThetaDescent, ThetaAtlasMetric, MorphismTangent and OpenPoint before the runner received a shutdown signal (exit 143). This log does not establish OOM or a specific shutdown cause; the native save step was skipped.

Batch every reached error. The frame Gram uses an explicit ordered triple-sum identity, with named coefficient families and exact evaluation of both original integral frame resolutions. FiniteLevelNorm transports the actual membership by the typed subtraction-map equality. BundleSymmetry renames the ambiguous inclusion identifier and transports the existential generator, retaining the same pullback and inversion maps. RationalGlobal separates the actual nonkernel affine lift and denominator-open point-value/nonzero calculation from the existing generic scheme gluing; named source/target objects, maps, and instances avoid repeating dependent rewrite/elaboration across two distinct curves. The exact public theorem type, nonkernel criterion, actual chart formula, target equation, monoid homomorphism and complex point action are retained. Remove the failed 1M heartbeat override rather than increasing it. Two private lemmas and the finite-sum identity are transitive dependencies of the existing guarded roots. All are unverified source repairs, not mathematical closure.

Move the failed-compile native-artifact save ahead of the optional diagnostic pass, retaining the original cache key and restore checks. The normal final save remains a fallback or success-path checkpoint, skipped if the early save succeeded. This avoids another diagnostic shutdown discarding all completed mandatory native prerequisites; no second successful archive of the same key, no lowered warning/axiom/semantic gate, and no cache artifact is treated as a proof certificate. The tradeoff is that further diagnostic-only progress need not be cached after a successful early save. Hosted verification of this batch remains required; the genuine supplier application and RH remain open.

## 19. Exact-head symmetry, metric and gluing repair (a141d8f)

The [mandatory preflight and diagnostic log](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45441779606/job/138614989464) confirms that NativeCMSerreBundleGram and NativeThetaCuspFiniteLevelNorm now build, and the early native cache save succeeded. The reached failures are NativeCMSerreBundleSymmetry:80 (composition with identity), NativeCMSerreSchemeMetric:168 (unqualified categorical mul_assoc rather than scalar multiplication), NativeCMLineBundleSigmaMetric:52 and :147 (unit-to-section coercion through the chart type), and NativeCMWeierstrassRationalGlobal:226 (whnf timeout; subsequent missing constant is consequential). The diagnostic also reports unused simp arguments/section instances in those modules. The runner received a shutdown signal after these reports; the full build remains skipped and later obligations have not been checked.

Batch the reached errors and warnings. Use explicit Category.comp_id and the scalar _root_.mul_assoc, remove only the identified unused simp/section arguments, and evaluate the literal restricted transition units using their values with the original chart-membership witnesses. Transport section evaluation across equality of morphisms by equality elimination. For RationalGlobal, move the kernel-open equivalence and the generic gluing-plus-monoid conclusion into a private theorem over abstract source/target group schemes, then instantiate it with explicit canonical group, finite-type, reducedness, separation, product and immersion instances. Lift and local action at scheme-valued points are separate declarations derived from the previously reached affine helpers. Retain the exact public gluing statement, actual field-point map, all original hypotheses, and downstream finite coefficient and integral extension goals. No heartbeat increase, new axioms, admitted proofs, changed workflow, or new unguarded supplier premise. These are unverified source repairs, not certification of the remaining geometry or an unconditional native RH claim.

## 20. Exact-head parser and unit-product regression repair (b9f4842)

The [mandatory preflight and diagnostic log](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45448545444/job/138639248412) confirms that NativeCMSerreBundleSymmetry, its cube and bundle pairing now compile and the early cache save succeeded. The earlier mandatory failure is a regression from b9f4842: eight omit commands were placed after declaration docstrings, contrary to Lean command syntax. Correct all eight by placing omit before the docstring, matching the already compiled convention in NativeCMWeierstrassGeometricGlue. In NativeCMLineBundleSigmaMetric replace the nonexistent Units.val_prod API with the actual pinned Mathlib Units.coeHom, composed with the existing evaluation ring hom; map_prod and evalPt_unit_zpow prove the unchanged finite product of the original restricted transition units. The RationalGlobal timeout was observed while four private helper declarations had failed parsing, so it is not evidence that the restored application succeeds or that an independent timeout has disappeared. Enable declaration-scoped elaboration diagnostics on the exact original global gluing theorem, without increasing heartbeats. No mathematical statement, genuine witness, workflow or proof gate is relaxed. These source repairs still require exact-head hosted validation; later obligations and unconditional closure remain open.

## 21. Exact-head projective elaboration boundary (82042a7)

The [preflight diagnostics](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45451577863/job/138650157962) confirm that the parser/unit-product regressions are cleared; NativeCMSerreSchemeMetric and NativeCMLineBundleSigmaMetric build. The only reached Lean error (apart from the consequential missing declaration) is the two-curve gluing theorem in NativeCMWeierstrassRationalGlobal:300, with the deterministic whnf timeout at 200000 heartbeats. The diagnostics report DFunLike.coe 83996, AddMonoidAlgebra.coeff 154136, inferInstance 120555, and repeated attempted unfolding of Classical.choice 68974. These counters show excessive reduction of the underlying polynomial/projective constructions; they do not yet isolate the precise failing unification expression. The early cache checkpoint succeeded; the optional diagnostic pass again ended with runner shutdown, leaving later obligations unchecked.

Isolate the canonical Weierstrass structural witnesses in complete_curve_kernel_open, over abstract open-chart maps and a genuine point action. Use locally irreducible scheme, toSpec, cubicIdeal and grading definitions only within the GluingApplication section, to inhibit elaborator expansion of the independently constructed projective models. This is a local transparency setting, not an axiom, opaque substitute for a geometric witness, or changed kernel theorem. The final application supplies named, typed chart, translation point, point action and local lift/value obligations, retaining the existing original public theorem statement and every downstream declaration byte-for-byte. No heartbeat increase, workflow change or proof-gate relaxation. The remaining timeout repair is source-level and requires hosted validation; later obligations and unconditional closure remain open.

## 22. Normalization-first continuation after the two-curve build

The exact-head [preflight on 3e9d842](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45453890561/job/138658361081) built NativeCMWeierstrassRationalGlobal in 49s. The subsequent diagnostic replayed it. The mandatory preflight failed at NativeCMWeierstrassCMGlobal (nine reached rewrite/instance errors); the full native build was skipped and the optional diagnostic pass ended on runner shutdown. The two-curve module has compiled; this is not the full G1 supplier or terminal RH certification.

By user direction, apply normalization first on the existing #1201 branch. Keep the now-built gluing and its structural abstraction unchanged; do not split it out into a new module merely to repeat a successful build. Reuse its exact normalized point transport in the first downstream failure: the CM generator on the actual original short model. Separate polynomial coefficient descent, the three evaluated coordinate identities and the literal multiplier from dependent nonsingularity transport. Use the existing pointCongr/pointConjugate equivalences, the original scheme morphism and canonical finite-type witness, and explicit affine-point and power identities to transport the actual quadratic relation. The public theorem statement, actual models, original kernel cardinality, leading coefficient, degree, period scale, point action and group law are unchanged. The already built two-curve declaration and all other source modules are unchanged. No new premises, axioms, admitted proofs, increased heartbeat limit or check relaxation. Exact-source manifest refreshed. The CMGlobal proof-body repair is not yet hosted verified; the original integral transport, all-embedding period comparison, measured suppliers and unconditional critical bound still require closure. No separate PR.

## 23. Exact-head normalized quadratic relation rewrite (0c55738)

The [mandatory preflight and diagnostic replay](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45456489533/job/138667576353) on 0c55738 report only one reached Lean error: NativeCMWeierstrassCMGlobal:179:41. The previous coefficient, dependent point, finite-type, and original-model errors are no longer reported. NativeCMWeierstrassRationalGlobal replays successfully. Both research and native prerequisite caches saved before the optional diagnostic was terminated by runner shutdown. The full native build remains unexecuted.

The error context itself shows that all compositions with f have already been rewritten: the goal is the product of the double CM action and the generatorNorm power, equated to the single action, on the actual normalized point group. Remove only the redundant final hpoint rewrite. Retain the subsequent power transport, group law and original rescaledCMAction_quadratic proof, the identical public statement, all original geometric witnesses, source manifest and existing warning/axiom/semantic guards. No new hypothesis or heartbeat increase. Hosted validation of the remaining quadratic-relation proof and later suppliers is required; no G1 discharge or RH closure claimed.

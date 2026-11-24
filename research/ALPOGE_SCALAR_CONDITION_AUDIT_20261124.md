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

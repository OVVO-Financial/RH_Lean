# Actual weighted square-survivor recovery

Date: 2026-11-23. Base: `8e5f9b59ebacc022757e13ec6737c272633c13bc`.

Status: **genuine finite arithmetic result; P1 remains open**. Source written in
`research/NATIVE_SQUARE_WEIGHTED_RECOVERY_20261123.lean`; hosted Lean verification
is required before describing these additions as kernel checked. No local Lean
or Lake execution was performed.

## The constructed native recovery

Take the existing, independently defined square-wheel survivors
`vfMidSquarePrefixWheelSurvivors A R`, with

\[
3\le A\le R<2A.
\]

The existing classification in `VF_MID_DYADIC_OWNER_EXACT.lean` proves that every
survivor is a prime or a product of two **distinct** primes. Their actual Möbius
values are respectively minus one and plus one. For one arbitrary real site
weight `w`, define

\[
U=\sum_{n\in S_{A,R}}w(n),\qquad
S=\sum_{n\in S_{A,R}}\mu(n)w(n),
\]
\[
P=\sum_{n\in\mathrm{Primes}_R}w(n),\qquad
C=\sum_{n\in\mathrm{CompositeSurvivors}_{A,R}}w(n).
\]

The new theorem `nativeSquareWeightedRecovery` proves simultaneously

\[
2P=U-S,\qquad 2C=U+S.
\]

All four quantities use the same set partition and the same weights. The proof
uses the existing disjoint-union theorem and the actual Möbius sign of each
stratum, then finite sums. It does not replace `C` with a chosen residual.

The specialization `nativeSquareWeightedRecovery_completeKernel` sets

\[
w(n)=\log n\,(N/n-1).
\]

This preserves the weighted prime-site source and its actual composite removal.
It is a local block identity; proper prime powers are not prime sites and must
remain in the separate correction of the completed `G_z` expression. No upper
bound on `P`, `S`, or the completed source is inferred from the equality alone.

## Integral recovery and its complete cost

The stratum signature matrix and its recovery numerator are

\[
E=\begin{pmatrix}1&1\\-1&1\end{pmatrix},\qquad
M=\begin{pmatrix}1&-1\\1&1\end{pmatrix}.
\]

The additions prove

\[
\det E=2,\qquad ME=2I,
\]

and prove that no integer matrix `B` satisfies `BE=I`. The recovery multiplier
two is a real integral index cost. At the dyadic place it corresponds to one
power of two; it is not a free denominator or a vanishing order growing with `R`.
For the abstract two-stratum coefficient module this realizes the schematic
recovery identity with `u=id`, `π=2`, `D=1`, and two coordinates. It is **not** an
instance of upstream `LPprimeAt`: no identification with its `Nsrc`, `Ntgt`,
Frobenius, edge lattices, or competing-edge vanishing is claimed.

On these same weighted quantities, `nativeSquareWeightedRecovery_energy` proves

\[
U^2+S^2=2(P^2+C^2).
\]

Consequently the uncentered Euclidean inequality is

\[
P^2\le\frac{U^2+S^2}{2}.
\]

There is no `R`-fold gain in this inequality. The proof is sharp on an actual
native carrier: at `A=R`, full-wheel survivors are precisely the primes,
`C=0`, and the displayed inequality is equality. The new theorem
`nativeSquarePrimeWeight_full_energy_equality` records this fact. Thus a hoped-for
strict contraction cannot come from applying an uncentered norm estimate to
this decoder alone. It requires further information about the centered,
weighted arithmetic source.

The two-stratum matrix has two scalar coordinates, independently of `R`.
This must not be confused with recovering all site coefficients. At `A=R`,
all surviving sites have the same signature `(1,-1)`, so distinct prime-site
contrasts lie in the kernel of the site-to-channel map. For example, the
`R=3` block has survivors `11,13`; coefficients `+1,-1` give `U=S=0`.
This only restricts recovery from these two measurements. It is not an
obstruction to every possible source-compatible construction.

## Attempts checked against existing suppliers

1. **Root-length forward jets.**
   `AlpogePrimeFreeForwardJet.lean` and
   `AlpogeSquareRootArithmeticMultiplicity.lean` already construct the native
   additive jet and prove its sharp `2^R` coefficient cost. They also retain the
   actual prime-power and Frobenius/inertia commutator. Repeating those results
   would not supply an additional finite-place recovery gain.
2. **Integral all-place descent.**
   `nativeAllPlaceDescent` consumes actual integral maps, collective injectivity,
   collective norm, short target generators, and the near-rank inequality.
   The weighted decoder supplies only its two aggregate coordinates; it does
   not construct the physical section lattices or their slope comparison.
3. **Upstream local recovery.**
   `Formalism.MainNotions.G.GoodRankK` in
   `src/Formalism/SharpRestriction/GrowthBounds/UnramifiedQuadraticSetting.lean`
   requires integral columns and an integral matrix recovering `π^D` times
   every coordinate. `LPprimeAt` additionally requires actual edge lattices,
   source membership, vanishing on every competing edge, and
   `n ≥ (1-κ) dimV`. The new two-channel result proves none of those uninstantiated
   physical attachments.
4. **Upstream averaged loss.**
   `losses_of_small_share_weight` in
   `src/Formalism/LocalToGlobal/GlobalTheory/LossRequirementsOfSmallShares.lean`
   takes `ChosenTT`, `ChosenBadp`, and `LinkG` on one family; it also uses
   the existing window and source-identification suppliers. Its conclusion
   cannot be applied by selecting unrelated good profiles for different costs.

The upstream source inspected was the local copy pinned by the repository to
`7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

## Exact remaining P1 premise

The live native consumer is
`physicalTopExcess_le_errorTerm_of_meanLoss` in
`RHLean/Analysis/AlpogeNativeSignedSlopeComparison.lean`.
Its `hLoss : (physicalData ...).Losses C` expands to

\[
\operatorname{umean}(\mathrm{ASK}-\mathrm{Ga})\le\mathrm{LoP},
\qquad
\operatorname{umean}(\mathrm{IO})\le\mathrm{LoP}.
\]

`physicalData_Ga` preserves the previously constructed `D0.Ga`; it does not choose
it to make either inequality true. The outstanding task is to construct that
gain on the actual host/source and prove these mean bounds while satisfying
the global-cost premises on the same object. The weighted decoder provides an
exact arithmetic attachment for a candidate gain; it does not identify its
two recovered channels with `D0.Ga` or prove those mean bounds.

## Exact diagnostic computations

An independent integer sieve and factorization check tested `w(n)=n` and the
rational kernel `w(n)=N/n-1`, with `N=(R+1)^2`. Both decoder identities and the
energy identity held exactly over rational arithmetic:

| A | R | Prime survivors | Composite survivors |
| --- | --- | --- | --- |
| 3 | 3 | 2 | 0 |
| 3 | 5 | 2 | 1 |
| 159 | 317 | 54 | 16 |
| 514 | 1027 | 144 | 31 |

All surviving composites in these tests had Möbius value plus one. These finite
checks are diagnostics, not evidence of a universal asymptotic saving.

`descent_payment_ack=ALPOGE_NATIVE_DESCENT_PAYMENT_V1`

`tractability_ack=ALPOGE_VIOLE_TRACTABLE_RH_V1`

## Further P1 attempt: full native wheel recovery on prime-power coefficients

This attempt uses a growing source module and the **existing** full inverse,
rather than duplicating the two-channel calculation.

`RHLean/Arithmetic/PrimeCombComplementSmoothInversion.lean` already proves
`finiteDifferenceOperator_eq_sum_complementSmooth`: for an integer sequence
`f` with `f(0)=0`, the full finite prime-wheel transform has an exact inverse
through the same set of smooth-number floor shifts. All powers of the selected
primes appear in that inverse; restricting the inverse to squarefree divisors
would be false. Thus the native arithmetic already supplies full integral
recoverability, not only two aggregate channels.

For a fixed prefix `1,...,N`, write

\[
(F_p f)(n)=f(\lfloor n/p\rfloor),\qquad D_p=I-F_p,
\]

with `f(0)=0`. For `p≥2`, `F_p` is strictly lower triangular and nilpotent.
Therefore `D_p` has rank `N`, determinant one, and integral inverse
`I+F_p+F_p²+...`. Every finite product of these maps has the same rank,
denominator one, and index one. One can obtain exact coordinate recovery and
off-diagonal coordinate vanishing by applying the explicit inverse to the
standard basis. These coordinate rows have not been identified with the
physical neighbouring-edge pairings in `LPprimeAt`.

At a genuine prime square clock `R=p`, `N=p²-1`, one has `F_p²=0` on the
entire prefix. Hence, for **any** iteration count `m`,

\[
D_p^m=I-mF_p,\qquad (D_p^m)^{-1}=I+mF_p.
\]

This gives an explicit growing, full-rank native map on the original
coefficient module. Its squared Frobenius norm in the standard coordinate
metric is exactly

\[
N+m^2(N-p+1).
\]

There is one strict off-diagonal entry `-m` for every `p≤n≤N`. At `m=p`,
the first source column has squared norm `1+p³`. These are complete norm
costs of this particular map; no averaging convention changes its determinant
from one to a prime-power index. Repeating a prime is a repeated arithmetic
operator, not insertion of fresh distinct prime coordinates into a set.

### The actual von Mangoldt coefficient test

For every prime `q`, define the integer coefficient fibre

\[
a_q(n)=\mathbf 1_{\{n=q^j:\ j\ge1\}}.
\]

It is the coefficient of `log q` in the actual von Mangoldt source. The
existing `alpogeNativeLambda_primePowerFubini` records the complete prime-power
decomposition. The new file
`research/NATIVE_PRIME_POWER_RECOVERY_TEST_20261123.lean` explicitly attaches
this coefficient to `Λ(q^j)=log q` and proves, for every finite prime set `S`
and every number of iterations `m`,

\[
(D_S^m a_q)(q)=1.
\]

The proof uses the actual floor operator: `a_q(n)=0` for `n<q`, while the
identity divisor contributes one at `q`; every other divisor reads an earlier
site. The same statement remains true under iteration. Consequently this
integer coefficient is not divisible by **any** prime, even once.

The companion theorem `nativePrimePowerCoefficient_smooth_recovery` uses the
existing smooth-number inverse to reconstruct this same entire coefficient
fibre exactly, with integer coefficients and no denominator. Thus recovery
is successful in this attempt, whereas the proposed inference from repeated
native wheel differences to prime-place multiplicity fails on a literal
prime-power coefficient. No p-adic valuation of the real number `log q` is
asserted. A different geometric construction is not excluded by this test.

Exact coefficient computations, using integer coefficients of each distinct
prime logarithm, checked complete wheel transforms and `R`-fold single-prime
transforms at:

| R | N | Distinct wheel primes | Squared Frobenius cost of D_R^R | First-column squared norm |
| --- | --- | --- | --- | --- |
| 7 | 48 | 4 | 2106 | 344 |
| 31 | 960 | 11 | 894690 | 29792 |
| 101 | 10200 | 26 | 103040300 | 1030302 |

Every coefficient was recovered exactly by `I+R F_R`. Every prime's own
first logarithmic coefficient remained one after the entire wheel transform.
The determinant/index statements above follow from the explicit triangular
form; the numerical program did not claim a symbolic determinant computation.

### Existing stronger alternatives checked

The high-prime prefix minors in
`ALPOGE_GZ_PHYSICAL_LIFT_ATTACK_20261120.md` already provide growing
unimodular incidence matrices with uniformly bounded inverse differences.
That report also records their decisive source correction: distinct
semiprimes vanish from first-order `Λ`; in the second Selberg source the
selected response has exact quotient one and therefore the same value
`E(1)=-1`. The coefficient rank is not independent response multiplicity.
The near-root signed `2I-J` construction in
`ALPOGE_SIGNED_SELBERG_INTEGRAL_SCHUR_20261120.lean` retains genuine prime-square
and distinct-semiprime faces, but its centered doubling and surviving
principal mode have already been accounted for. Neither existing result
supplies the missing physical `Ga` and its mean loss bound.

**First remaining construction failure:** identify genuinely arithmetic
source/target edge lattices and pairings for which the recovered integral
conditions earn the required prime-place gain, while the global map cost and
the complete source attachment remain on the same object. Full recovery of
the finite wheel data, by itself, does not discharge this premise.

### Genuine prime-place indices: factorial comparison checked

The factorial is a concrete integer object with actual prime-power
divisibilities and an independently computed global height. The needed
identity is already proved by
`NativePNTSelberg.nativeMulLambdaRecip_eq_logFactorial_add_error`:

\[
N\sum_{n\le N}\frac{\Lambda(n)}n
 =\log(N!)+\mathrm{nativeLambdaFloorError}(N).
\]

Substituting into the original source gives

\[
G_z(N)=\log(N!)-N\log N+(1+\gamma)N
 +\mathrm{nativeLambdaFloorError}(N)-\psi(N).
\]

Hence the remaining exact complement lower bound is

\[
\psi(N)-\mathrm{nativeLambdaFloorError}(N)
 \ge\log(N!)-N\log N+(1+\gamma)N-B(N),
\]

with `B(R²-1)=O_eta(R^(1+eta))` required for the square-clock consumer.
The existing `0≤nativeLambdaFloorError≤ψ` does not supply this lower bound;
it only yields a nonnegative complement. The displayed target is an exact
restatement of the original `G_z` bound, with no improved estimate established.
No duplicate factorial identity module was added.

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

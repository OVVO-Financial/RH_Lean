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

**Execution evidence:** original source/type inspection; finite algebraic proof
of the debt propagation; independent source review by the simultaneous-windows
agent. New Lean execution is hosted-only and pending. **P2 status: OPEN.**

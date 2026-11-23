# Construct nonzero native theta sections and pay the full-level marking cost

## Status and continuation

This continuation starts from main
`07575359108d9883e18f44ff1f700451b3e801be`, the merge of PR #1199.
The previous native proof build and its theta-construction audit are preserved.
The current complete native universal bound and RH conclusion remain **OPEN**.

Three supplying constructions are added here, on the original native lattice:

1. The canonical Appell--Humbert phase and automorphy factor, with its exactly
   invariant Gaussian Hermitian fiber metric.
2. A locally normally convergent Gaussian periodization, proved holomorphic
   and nonzero by the original perfect pairing and Fourier uniqueness.
3. A coefficient-linear full-level marking count, including the fixed rational
   level-five logarithmic cost and the identification with actual period torsion.

The files are `RHLean/Geometry/NativeThetaAppellHumbert.lean`,
`RHLean/Geometry/NativeThetaGaussianSeries.lean`,
`RHLean/Geometry/NativeThetaNonzeroSection.lean` and
`RHLean/Geometry/NativeThetaFullLevelCost.lean`. The dedicated research audit is
`research/ALPOGE_NATIVE_THETA_FACTOR_LEVEL_COST_20261123.lean`. Hosted compilation
and its terminal-axiom audit are pending at the first publication of this report.
No local Lean or Lake execution has been used. Current hosted status is recorded
on [PR #1200](https://github.com/OVVO-Financial/RH_Lean/pull/1200); the first
published head was `8416870d3d99011f1493ad416a002ae5b14aecd6`.

```text
descent_payment_ack=ALPOGE_NATIVE_DESCENT_PAYMENT_V1
tractability_ack=ALPOGE_VIOLE_TRACTABLE_RH_V1
ROLE=Lean Verification; user-directed manual continuation
STATUS_AT_INITIAL_PUBLICATION=CONSTRUCTED_SOURCE_PENDING_HOSTED_VERIFICATION
SOURCE=complete native signed ASK-MAIN/De and character-completed Gm/Gz
NORMALIZER=Q=T*m*b*Delta/2; unchanged
FIRST_UNPAID=actual global theta/cusp system with measured norms and shifted ranks
GLOBAL_STATUS=OPEN
```

Latest actual published research was inspected at agent-reports commit
`a52b8d8ca946d25d3249a7b4b6c158246c3f10d4`; the latest actual role reports are
still dated 2026-11-22. This continuation does not claim that editing a report
launched or reconfigured any scheduled role.

## 1. The theta factor is constructed, including its phase law

Let `D` be the native geometric datum, `EF` its integral alternating form and
`P` its actual period map. The host's integral half-root `w0` satisfies

\[
w_0+\overline{w_0}=1.
\]

The new proof derives this from the actual CM involution and the defining
quadratic-root equation. It does not assume a semicharacter. Define

\[
q(a)=EF(a,w_0a),\qquad \epsilon(a)=(-1)^{q(a)}.
\]

Alternation and adjointness give the exact integral identity

\[
q(a+b)=q(a)+q(b)+EF(a,b)-2EF(a,\overline{w_0}b).
\]

Consequently

\[
\epsilon(a+b)=\epsilon(a)\epsilon(b)e^{\pi i EF(a,b)},
\qquad |\epsilon(a)|=1,\qquad \epsilon(2a)=1.
\]

For the already constructed positive Hermitian form `H`, which is linear in
its first variable and satisfies `Im H(Pa,Pb)=EF(a,b)`, set

\[
j(a,z)=\epsilon(a)\exp\!\left(\pi H(z,Pa)
                         +\frac\pi2H(Pa,Pa)\right).
\]

The file proves nonvanishing and the correctly oriented cocycle

\[
j(a+b,z)=j(b,z+Pa)j(a,z).
\]

It also proves exact invariance of the squared fiber metric

\[
\|u\|_z^2=|u|^2e^{-\pi\operatorname{Re}H(z,z)},
\qquad
\|j(a,z)u\|_{z+Pa}^2=\|u\|_z^2.
\]

The endpoint `nativeDyadicPrescribedPeriod_exists_thetaFactor` obtains `H`
from `nativeDyadicPrescribedGeometricDatum_isPeriod` and supplies all these
laws on the same prescribed inverse-half-different lattice and period map.
The positive form, phase, cocycle and metric identities are not new hypotheses.
The native host, the half-different ideal and the original admissible integer
parameters remain explicit inputs, as in the previous prescribed-period theorem.

This first module constructs analytic line-bundle automorphy data. The next
construction below supplies a nonzero holomorphic section. An algebraic or
integral model, the moduli family, cusp spanning and the Petersson norm of a
global cusp form remain open.
An invariant metric on one torus does not determine the measure of the
arithmetic base over which the global Petersson norm is integrated.

### Exact source

The source is Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
under `src/Development/AbelianVarietyTheory/`:

- `Definitions/TorusSections/IsTorusOf.lean`;
- `Proofs/TorusSplitting/TorusAtExistsOfParts.lean`;
- `Proofs/CuspFormEvaluations/ExistsTorusWithSignUniformisationFrame.lean`;
- `Proofs/CuspFormEvaluations/AppellHumbertFrameSemicharacter.lean`.

The native proof derives the phase identity directly from the original
native `EF`, `w0` and CM conjugation. No external compiled object or terminal
RH theorem is imported. The source archive/mirror states no license;
attribution is retained without assigning one.

### 1.1. Nonzero theta is now constructed from the native period inputs

`NativeThetaGaussianSeries.lean` reconstructs the needed analytic proofs:
positive-matrix coercivity in the actual ambient norm, Gaussian summability
on a discrete integral lattice, holomorphy of a locally normally convergent
series, and uniqueness of absolutely convergent torus Fourier coefficients.
It uses Mathlib and does not assume a theta section.

For the same `D`, `P`, positive `H` and factor `j`, define the actual series

\[
\theta_w(z)=\sum_{a\in L}j(a,z)^{-1}
                  e^{\pi H(z+Pa,w)}.
\]

The exact norm of its summand is

\[
\exp\!\left(\frac\pi2\operatorname{Re}(H(z,z)+H(w,w))\right)
\exp\!\left(-\frac\pi2\operatorname{Re}H(Pa+z-w,Pa+z-w)\right).
\]

Positive definiteness supplies a genuine `c>0` with
`c*norm(v)^2 <= Re H(v,v)` in the default native coordinate norm. Completing
the square and the proved bounded-translate Gaussian estimate give a summable
majorant on every sufficiently small neighborhood. Thus the series is
holomorphic. Reindexing the original lattice and using the constructed cocycle
gives `theta_w(z+Pa)=j(a,z)*theta_w(z)` and periodicity of its squared fiber norm.

At the center,

\[
\theta_w(w)=e^{\pi H(w,w)}
 \sum_{a\in L}c(a)e^{-2\pi i\operatorname{Im}H(w,Pa)},
\qquad
c(a)=\epsilon(a)^{-1}e^{-\pi H(Pa,Pa)/2},\quad c(0)=1.
\]

The actual integral basis and unimodular `EF` supply dual lattice vectors
`d_j` with `EF(d_j,a)` equal to the corresponding integer coordinate of `a`.
Taking `w=-sum_j t_j*P(d_j)` makes this the usual integer-frequency Fourier
series. If all center values vanished, uniqueness would force `c(0)=0`,
contradicting its exact value one. This proves an actual nonzero holomorphic
section without a theta-existence assumption or a large tensor-power threshold.

The strongest endpoint is
`RHLean.Analysis.AlpogeThin.nativeDyadicHost_exists_nonzeroThetaSections`.
It chooses one actual half-different ideal before all admissible `k,m,j`,
preserves its coprimality and Galois invariance, and supplies the positive
form, holomorphic section, nonvanishing, automorphy and invariant fiber metric
on the original prescribed lattice. Its only starting host hypotheses are
the already native prime/host conditions; it does not ask for a moduli object.

This is qualitative analytic existence. The coercivity constant is proved
positive, but no epsilon-uniform bound on it is asserted. The normalized
torus measure used for Fourier uniqueness is an auxiliary analytic device;
it is not the global automorphic Petersson measure. Neither point separation
by a theta family nor global cusp spanning follows from this one nonzero
section without further proof.

The exact supplying source proofs are
`Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean`,
`Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean`,
`Proofs/TorusSplitting/CoeffEqZeroOfOrthonormal.lean` and
`Proofs/ToricGeometry/ExistsThetaSeriesApplyNeZeroOfLargeForm.lean`, under the
same pinned `Development/AbelianVarietyTheory` tree. The native proof uses
the original coordinate norm and original perfect pairing explicitly.

## 2. Pay the full finite marking cost without an extra field-degree factor

The actual lattice `L` is finite projective over `O_E`; it need not be free
over `O_E`. For any ideal `I` with finite coefficient quotient, the proof
constructs

\[
L/IL\simeq_{O_E}(O_E/I)^N,
\qquad N=\operatorname{rank}_{O_E}L.
\]

This uses constant fibre rank of the original finite projective module and
freeness after reduction over the finite quotient. Conjugating automorphisms
through this equivalence identifies their set with `GL_N(O_E/I)`. Counting
all matrices gives

\[
|\operatorname{Aut}_{O_E}(L/IL)|\le |O_E/I|^{N^2}.
\]

At a nonzero rational integer level `g`, the exact coefficient quotient size
is `g^[E:Q]`, including ramified levels. Hence

\[
|\operatorname{Aut}_{O_E}(L/gL)|
 \le g^{[E:\mathbf Q]N^2}.
\]

This is sharper than forgetting the coefficient action and counting arbitrary
additive automorphisms, which would introduce an unnecessary second field-degree
factor in the exponent. The new construction also identifies the original
module quotient with the already constructed actual period `g`-torsion.

For the prescribed lattice, `N=k+m-1` at every stage `j`, so

\[
\log |\operatorname{Aut}_{O_E}(L/5L)|
 \le [E:\mathbf Q]\cdot(k+m-1)^2\log5.
\]

The previous fixed-level result already proves that five is prime to the
actual native conductor and that finite-order stabilizers congruent to the
identity at full level five are trivial. Together, the existing freeness
theorem and this new count remove the need for a growing level in those two
finite calculations. They do not erase the growing rank or field degree.

For comparison, the same proof at rational level `R^4` gives

\[
|\operatorname{Aut}_{O_E}(L/R^4L)|
 \le R^{4[E:\mathbf Q]N^2}.
\]

With the source convention `[E:Q]=2*fdeg(E)`, this matches the exponent
`8*fdeg(E)*N^2` in `CardLevGrpAndSpan.card_levGrp_and_span`. That comparison
charges the whole marking set; an actual form-preserving subgroup has no
larger cardinality, but its algebraic moduli-cover realization is still needed.

The three generic reduction proofs reconstruct `GlobalTheory.EtaCard`'s
`finrank_fibre`, `nonempty_equiv_mod` and `nonempty_aut_equiv` from the pinned
`Proofs/CuspFormEvaluations/CardLevGrpAndSpan.lean`. Their complete hypotheses
are visible in the native file. No global free basis is substituted for the
native inverse-half-different lattice.

Full rational level five is **not** a split-ideal level satisfying
`I * conjugate(I) = (5)`. Unramifiedness of five does not prove that split-ideal
condition. The transfer to the original moduli-level construction must be
proved explicitly before claiming the entire geometric cost is paid.

## 3. Where the universal estimate now stands

`NativeConstructedDyadicSignedSlopePayment.nativeConstructedDyadicSignedSlopePayment`
already composes the actual native host, same selected primes, full signed
source, nonprincipal/thin payment and scalar normalization. Its complete
geometric hypotheses are still explicit. It does not construct the actual
global cusp lattices required by `HidaSetting`, `DIV`, `Slopes`,
`QuotientSlopeBoundsWith`, `Count5` and the accompanying height/loss estimates.

The normalizer remains

\[
Q=\frac{Tmb\Delta}{2},\qquad
T=|TT|,\quad n=|H|,\quad \Delta=|T_2|/n.
\]

After division by this positive `Q`, the complete error bracket is

\[
x^{C\epsilon}\left[
\frac{2a_E}{mb\Delta}\left(1+\frac{m^2}{k}\right)
+\frac{4nm x^\epsilon}{T\Delta}
+\frac{2k x^{2\epsilon}}{nT}
\right]+\frac4{\Delta x}.
\]

Here `a_E` is the arithmetic height-scale parameter; it is neither Petersson
mass nor cusp rank. Upstream `Scale` chooses `b=exp(x^eps)` and `a=x*b`.
The composed native theorem still receives `0 <= a_E <= 2*x*b` through
`GeometricSizeWindows`; assigning that scalar does not supply any missing
geometric norm comparison.

Ignoring the already explicit small exponent losses, `T` comparable to `n`,
positive projection density and `a_E <= 2*x*b` reduce the bracket to

\[
O\!\left(x/m+xm/k+m x^\epsilon+k x^{2\epsilon}/n^2\right).
\]

The choice `m` near `sqrt(x)`, `k >= x*m` and the already constructed host
size near `x^(2+8*epsilon)` is the source of the square-root balance. The
existing scalar window theorem proves the corresponding precise exponent
`1/2 + (C+3)*epsilon`, once the authentic geometric budget is supplied.
The fixed level-five improvement simplifies an auxiliary bill; it does not
prove the signed-source inequality by itself.

The actual source parameter construction has further conditions, including
`x^4 <= k` and `k <= x^5` in `QuadraticLogDerivCongr.lean`. The lower
scalar-window inequality `x*m <= k` alone does not license choosing `k`
near `x*m` for that family. Any such optimization needs a proved replacement
construction; the existing payment theorem retains its full upper window.

The exponent also needs its original uniformity: `CErr=C.eDiv+C.eLoss+3`.
The source chooses upper bounds for `eDiv` and `eLoss` before epsilon, while
other geometric constants may depend on epsilon and be absorbed in the
eventual threshold. Requiring every constant to be uniform is unnecessarily
strong; allowing the two exponent losses to grow arbitrarily as epsilon
shrinks would not prove the universal square-root-plus-epsilon estimate.

The following ranks and scales are distinct:

| Quantity | Actual role |
| --- | --- |
| `R_V` | Native square index, with evaluation point `R_V^2-1` |
| `m` | Theta-chain multiplicity |
| `k+m-1` | `O_E`-rank of the prescribed geometric lattice |
| `d(u0,u)` | Rank of the actual graded cusp lattice in the source slope argument |
| source auxiliary theta dimension | A separate dimension, at least `8*fdeg(E)*(k+m-1)+4` in the cusp-span construction |
| `T=card TT` | Character summation multiplicity in `Q` |
| source `Data.T(u0,u)` | A word-dependent auxiliary prime, distinct from `card TT` |

## 4. Exact next supplier and independent source audit

For actual theta values, the pinned theorem
`GlobalTheory.exists_cover_shortVal_data` in
`Proofs/CuspFormEvaluations/ExistsFaithfullyFlatCoverShortThetaValueData.lean`
constructs lifts, finite torsion enumerations and columns **from an actual
polarized moduli object**, its multiplication maps and formal charts. The
native faithfully flat descent and phase/chart agreement mechanisms are
already proved; the missing work is instantiating those geometric inputs.

The Gaussian periodization and nonzero analytic theta step is implemented in
this continuation as described above. The next construction must realize
those sections and their jets on the actual family, prove the relevant
cusp-span property, and supply the measured comparison and shifted-rank ratio.

For the eventual slope substitution, the source's actual numeric data in
`Formalism/SharpRestriction/GlobalSchurBounds/QuadraticLogDerivCongr.lean`
uses `d(u0,u) = (D.div.Nu u).rank`, `muM` from `(D.fm u).lat 0`, `muN`
from `D.div.Nu`, and `muCC` from the dual divisor lattice `D.div.RR`.
These are the authentic measured lattices to construct; arbitrary scalars
with the same names do not discharge the native supplier.

The source's `IsGeoOf.Reads` already asks for a spanning cusp-to-lattice map,
exact lattice membership and norm proportionality by `sqrt(vol*dimKap)`.
This is more than a reflexive label. It does not, by itself, bound that
volume or control all embedding-dependent analytic scalars: the source's
`setLam` preserves `IsGeoOf` while changing off-base `logLam`. The separate
measured Petersson and slope theorems must therefore be instantiated too.
Neither names such as `anyGeometry` nor a quoted literature interface alone
establish a defect or complete the source audit; inspect the actual supplier.

In particular, `ComponentsPeterssonOrthogonalAndMasses.petAt_muOn_sq`
identifies the restricted norm squared with the component mass times the
conditional norm squared. `ComponentRanksDegreesAddWithMasses` retains the
degree correction `-(rank/2)*average(log mass)`. This actual component mass
cannot be replaced by the normalized Haar mass of a torus fiber. The source's
short-theta level `R^4` also serves its theta construction, so fixed-five
stabilizer freeness alone does not authorize replacing every such level by five.

### 4.1. The remaining arithmetic ties are independent of Petersson mass

The source does not identify its finite-place gain with ASK by a definition.
`SizeData₂.Ga` in `Formalism/LocalRingCardinality/DataParams₂.lean` is the
ramification-weighted sum of actual local gains, less the local defects.
`FrameCodeOfAdditive.askRec_at` and `askIsF` identify the complete prime-power
expression, including the explicit ramified `d` contribution. The actual
`LinkG_at` supplier and `LossRequirementsOfSmallShares.losses_of_small_share_weight`
then prove an eventual bound of the form `ASK-Ga <= C*card(TT)*m*b`.

The source's actual local counting chain is `LPprimeAt`, `LatticeSystems.jm_core`,
`jSmith`, `jLocal`, `ja_restJ`, and `theta_kernel_expansion`, followed by
`FormalGroupSystem.Pf.core`. It constructs exceptional coefficient sets from
an integral matrix identity and neighboring Hecke lattices. The native
`NativeServedPrimeLength` already proves the final length and saturation
estimate once those sets and inclusions are given. The current complex Fock
and characteristic-zero interpolation proofs do not supply the integral
matrix identity, the reduction-mod-prime rank defect, or the valuation-preserving
comparison with the original cusp lattice. These require the actual integral
family or an equally strong direct native construction.

On the main-term side, the source's `FlatDegProof.flatDegAt_of_st` uses the
actual CM-period and arithmetic-degree theorem. Its concrete supplier is
`GlobalTheory.CompanionTheory.Ar.Fl.flatDegree` in
`Development/AutomorphicSpectrum/Proofs/GeometryProofs/FlatDegreeHolds.lean`,
via the residue/GAGA route. Its proof uses the Chowla--Selberg period,
actual CM frame value and finite-place height, archimedean Gram determinant,
and the different-ideal correction. This yields the logarithmic period term

\[
\log\Omega=\gamma+\log(2\pi/\sqrt d)
 -\operatorname{Re}\frac{L'(1,\chi)}{L(1,\chi)}.
\]

The actual covolume and column-map height comparisons feed `RecNums.divIneq`,
`linkDIV_at_words` and `QuadraticLogDerivCongr.data_DIV`, supplying the
MAIN side of the same signed slope comparison. A positive invariant metric
or a normalized fiber integral alone does not establish that arithmetic
degree formula. The residue/GAGA source route avoids rebuilding an older
prismatic interface, but its actual period and valuation proofs remain needed.

### 4.2. The existing analytic consumer needs only arbitrarily late windows

The native composed slope theorem currently bounds the average of
`Gz(a(t)/b)`. It constructs the dyadic host and selected primes, but it does
not construct the entire geometric family and its valid size/height parameters
at every required scale. Its upper-height hypothesis `Amax/b <= x+1` alone
does not imply `abs(a(t)/b-x) <= 1`.

Both comparisons needed after that family construction are already proved:

- `alpogeNativePhysicalSubgroup_freezing_paid` and
  `alpogeNativeCompleteProjection_at_constructed_cutoff` pay the width-freezing
  cost on the complete signed source.
- `alpogeNativeRetainedSignal_zero_ge`, with
  `alpogeNativeDerivInt_moveConstant`, pays height movement. If `TT` is nonempty,
  `x >= 2` and every normalized height is within one of `x`, then

\[
G_z(x)-(\log4+4)\le\frac1{|TT|}\sum_{t\in TT}G_z(a(t)/b).
\]

Thus there is no new cancellation theorem needed just to move this average
back to `x`. The required height proximity must still be supplied by the
same geometric family. An inner window of a larger selected-pair window
preserves the character estimates under the movement.

The weakest already-proved RH consumer is
`RHLean.Analysis.riemannHypothesis_of_Gz_windows`. For one fixed `delta>0` it
requires exactly

\[
\forall\eta>0\;\exists K\;\forall Y_0\;\exists Y\ge Y_0\;
\forall x\in[Y,Y^{1+\delta}],\quad
G_z(x)\le Kx^{1/2+\eta}.
\]

`riemannHypothesis_of_zetaWindowWitnesses` consumes the corresponding
same-data witness formulation directly. A bound at every sufficiently large
square endpoint is also sufficient, through
`riemannHypothesis_of_eventual_squareClock_Gz_rpow`, but is stronger than
this existing window entrance condition. Both global inputs remain open.

The geometric error exponent must be bounded so that
`(CErr+3)*epsilon <= eta` uniformly across the chosen window. The constants
and thresholds may depend on `eta`. The new analytic theta theorem supplies
neither that quantitative uniformity nor the whole-window family constructor.
The exact remaining chain is: actual integral theta/cusp family and measured
ranks; actual local-gain and CM-degree comparisons; complete signed-source
inequality; compatible parameters throughout a window; the existing native
Landau consumer.

## 5. Acceptance and verification

The dedicated audit checks 57 construction roots, prints the native endpoint
types, and rejects any transitive terminal axiom outside `propext`,
`Classical.choice` and `Quot.sound`. All four new modules are in the sorted root
import manifest. Normal PR validation runs the changed research closure
before the full native build and cancels further same-head work on failure.
The retired OAI replay remains manual-only. A relative-link preflight is also
added before Lean setup: the first hosted documentation check interpreted
adjacent degree brackets and parentheses in a displayed formula as a file
link. The formula is corrected with an explicit multiplication sign. Running
the same existing link checker in the primary preflight makes such failures
stop the proof pipeline before toolchain/cache setup, with the existing
same-head cancellation of remaining runs.

The first hosted proof run,
[45247265647](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45247265647),
restored the trusted main dependency and native caches and reached the new
proofs directly. It found three rewrite/exponential-normalization errors and
one unnecessary tactic-sequencing lint in the Appell--Humbert file. The full
build was skipped and the same-head cancellation job succeeded. Those exact
proof errors are repaired without changing their statements or budgets;
the next revision adds the Gaussian and nonzero-section constructions.

The second hosted run,
[45248764912](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45248764912),
at `cf131086fcc8a49ae8f565ab7d343a9f0224b639` successfully compiled the
Appell--Humbert, full-level cost and Gaussian-series modules. The nonzero
section file then reported two elaboration/rewrite errors and three style
lints. The repairs remove an already-closed trailing tactic, make the
reindexed linear-equivalence coercion explicit, and use the current tactic
and instance syntax. The mathematical statements, source data and budgets
are unchanged. The complete closure and 57-root axiom audit remain the
authoritative verification gate on the final PR revision.

This provides three reusable non-RH constructions. Their verification status
will be updated from actual hosted evidence. Tractability of the complete
critical estimate, a new central signed-cancellation contribution, and an
unconditional RH proof remain separate unfulfilled acceptance gates.

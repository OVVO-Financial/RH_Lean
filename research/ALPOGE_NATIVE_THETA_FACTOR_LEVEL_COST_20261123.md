# Construct the native theta factor and pay the full-level marking cost

## Status and continuation

This continuation starts from main
`07575359108d9883e18f44ff1f700451b3e801be`, the merge of PR #1199.
The previous native proof build and its theta-construction audit are preserved.
The current complete native universal bound and RH conclusion remain **OPEN**.

Two supplying constructions are added here, on the original native lattice:

1. The canonical Appell--Humbert phase and automorphy factor, with its exactly
   invariant Gaussian Hermitian fiber metric.
2. A coefficient-linear full-level marking count, including the fixed rational
   level-five logarithmic cost and the identification with actual period torsion.

The files are `RHLean/Geometry/NativeThetaAppellHumbert.lean` and
`RHLean/Geometry/NativeThetaFullLevelCost.lean`. The dedicated research audit is
`research/ALPOGE_NATIVE_THETA_FACTOR_LEVEL_COST_20261123.lean`. Hosted compilation
and its terminal-axiom audit are pending at the first publication of this report.
No local Lean or Lake execution has been used.

```text
descent_payment_ack=ALPOGE_NATIVE_DESCENT_PAYMENT_V1
tractability_ack=ALPOGE_VIOLE_TRACTABLE_RH_V1
ROLE=Lean Verification; user-directed manual continuation
STATUS=CONSTRUCTED_SOURCE_PENDING_HOSTED_VERIFICATION
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

This constructs analytic line-bundle automorphy data. It does **not** yet
construct a nonzero holomorphic section, an algebraic or integral model,
the moduli family, cusp spanning, or the Petersson norm of a global cusp form.
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
 \le [E:\mathbf Q](k+m-1)^2\log5.
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

An analytic next step is the Gaussian periodization construction of a
nonzero theta section. The concrete source candidates are
`ThetaExist.exists_sec_ne_zero` in `CoeffEqZeroOfOrthonormal.lean` and
`ThetaLarge.exists_theta_apply_ne_zero` in
`ExistsThetaSeriesApplyNeZeroOfLargeForm.lean`. The latter is directly phrased
for a positive Hermitian matrix and a discrete period lattice. Its convergence,
nonvanishing threshold and tensor-power cost must be retained when adapted.

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

## 5. Acceptance and verification

The dedicated audit checks 30 construction roots, prints the native endpoint
types, and rejects any transitive terminal axiom outside `propext`,
`Classical.choice` and `Quot.sound`. Both new modules are in the sorted root
import manifest. Normal PR validation runs the changed research closure
before the full native build and cancels further same-head work on failure.
The retired OAI replay remains manual-only; no workflow change is made here.

This provides two reusable non-RH constructions. Their verification status
will be updated from actual hosted evidence. Tractability of the complete
critical estimate, a new central signed-cancellation contribution, and an
unconditional RH proof remain separate unfulfilled acceptance gates.

# Supplier erasure and exact relative-height reduction (2026-11-24)
Baseline #1201 1f7a23a36aad072c83a6f587a5f490527fd45a9f.
Upstream CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4.
Status: targeted source audit and new exact scalar paper proof.
No hosted validation of a rewritten upstream supplier; no RH claim.

## 1. Actual erasure boundary, not a renamed trivial predicate

In upstream src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/OverIx.lean,
anyGeometry is constantly True. The base constructor in NotGeoClFalse.lean
makes geoCl anyGeometry inhabited at every admissible D,J,X. It carries
no additional restriction. An OAt record at this specialization consists
of one redundant proof and the substantive LamAre predicate. Its projection
to LamAre is an equivalence in the mathematical sense: the inverse appends
the unique proof of the redundant proposition; proof irrelevance proves the
inverse identities. The replacement should contain LamAre only, no new
universal predicate and no closure.

The first exact proof-body erasure occurs in
src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/
DivisionGeometryScalarsTransferSetDivision.lean, theorem oAt_setDiv.
After the shared row, algebra and module identifications, the last two
goals are independent. The first merely transports hp.geo via GeoCl.step.
The second uses lamAre_copy with the row-coordinate identifications and
hp.lam. The latter branch survives erasure: replace the input OAt by LamAre,
remove the first constructor branch, and retain that second proof with hp
in place of hp.lam. The required identifications of the unchanged logLam
and row coordinates must remain. This is an exact leaf-level source edit,
not a compiled complete upstream rewrite.

The two supplier branches meet at the same deeper class_sum_divisor_all_alt
(LinkedTiesStatement.lean), proved by linked_ties_alt (LinkedTies.lean).
The latter constructs ExtensionReading with OX Gamma and uses
class_sum_divisibility_of_extensionWithLaw, ties_of_tiesB_alt and actual
row/linkage data. RowGeoAtGridA.lean adds HasGrid. RowFunAtGridA.lean
uses selected functional summands and evaluation; LinkedBundlesL3OfOpen.lean
uses an independent hCov and eventual_L3_of_covolume_alt. These are not
deduced from the trivial predicate alone. Erasing the predicate does not
discharge their quantitative content.

## 2. Additional seed and height issues cannot be erased just by deleting a name

The actual upstream seed x0 in TupPinsOfMuIsW.lean uses geoExample,
Lev=Empty, Qp empty, Comp=Empty and Surf=Empty. geoExample has Var=Empty
in src/Formalism/LocalRingCardinality/SpanPowerMembership/DivXExample.lean.
The subsequent geoOver_stages invokes divXFl. In
src/Formalism/LocalToGlobal/LatticeGeometry/Inhabited.lean, divXFl sets
geoDegenerate, Lev=Unit, Mp/CurveM/Comp=PUnit, degM=0, degHH=0, iMj=0.
It retains nontrivial arithmetic data from the input record. The existence
proof then grafts that construction onto the chosen divisor record.
The empty/unit/zero assignments are genuine source-level evidence;
they are not, by themselves, a contradiction or proof of invalidity.
A meaningful replacement must distinguish genuinely used measured
geometry from bookkeeping. In particular, a nonzero degree or geometric
capacity must not be inferred from an empty or constant model alone.

setDiv in SetUnipotentTranslate.lean replaces D.div.Nu.L and D.div.h,
and defines HH by max 1 of the specified frame expression. Its point
constructor supplies hExpl6 as the height. Reflexivity certifies the
assignment, not that hExpl6 equals an independently measured height.
However, the native scalar proof below shows that not all absolute height
normalizations are needed. Do not build absolute geometry simply to fill
a slot that cancels exactly.

## 3. Six-module actual native cut

Inspected all six modules at RHLean/Geometry/AlpogeSignedSlope on the
baseline (1251 source lines, counting split-newline lines):
RankGapBounds/MeanBoundSecondForm (242),
RankGapBounds/RankGapProofs/WeightedMeanData (240),
SizeWindowBrackets/QuotientSlopeBoundsWith (97),
SizeWindowBrackets/ErrorWindows (74),
SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence (267),
SizeWindowBrackets/ChainSlopeWindows/StrongErrorBound (331).
Each imports only other members of this list or Mathlib. No forbidden
identifier occurs in their text. This is an import-closure source audit,
not an elaborated declaration-level audit of a terminal RH root.
The source attachment AlpogeNativeSignedSlopeComparison uses the real
physical ASK and MAIN, preserves Ga, and applies weighted_mean_bound_statement.

## 4. New exact elimination of two absolute offsets

Use the literal Data record and predicates from MeanBoundSecondForm,
QuotientSlopeBoundsWith and ErrorWindows. Fix u0 and write
F=Fo(u0), c=muCC(u0). On each nonempty fiber W(u0) make the following
invertible change of relative coordinates (retain F,c externally if
the original record is needed):

    Fo'=0, muCC'=0,
    h'(u)=h(u)+c-F,
    muN'(u)=muN(u)-F, muMaxN'(u)=muMaxN(u)-F,
    muMinCC'=muMinCC-c.

All remaining entries, especially Ga, ASK, MAIN, IO, EeJ, T, d, aT, w,
gam, logOm, the actual budgets and every constant, remain unchanged.
This is a coordinate normalization of existing measured quantities,
NOT a method to manufacture data satisfying the premises.

For positive d and nonempty W, weighted averaging a constant is exact.
Consequently s'=s-c. Since the supremum of a finite nonempty family
shifted by a constant is shifted by that constant, uF'=uF. Also:
    muCC'+h'-Fo' = muCC+h-Fo,
    muN'-Fo' = muN-Fo,
    muMaxN'-Fo' = muMaxN-Fo,
    s'-muCC' = s-muCC,
    s'-muMinCC' = s-muMinCC.
For hComp, the added constant c-F cancels between u and u'.

These give equivalences, not merely implications, for every original
hypothesis in MeanBoundOfLossBounds:
* HidaSetting: the only changed entry tested is the comparison of muN
  with muMaxN; both receive the same offset.
* DIV: the entire left side is invariant; the right side is unchanged.
* EComp5, Count5, Slopes, Losses, FParams: none of their entries changes.
* HComp: the two height shifts cancel.
* QuotientSlopeBoundsWith: subtract F from both sides of each bound;
  Lo5 is unchanged.
* SlopeIneq: the antecedent s-muMinCC<=HH and the entire inequality
  after moving muCC to the left are invariant.
* HHBound: the only changed expression is the invariant s-muMinCC.

ErrWindows, LargeX, Main, ErrText, ErrX5at, errorTermWith and the final
normalized scalar bracket are unchanged by direct expansion of their
definitions. In particular Vvar, MLo5 and UBar5 have no dependence
on the six changed fields. The exact complete signed ASK-MAIN source
and its average are unchanged. The pointwise and mean finite
comparison conclusions therefore carry the identical numerical bound.

This reduces the native supplier to relative degrees and slopes; no
independent absolute Fo or muCC calibration is mathematically required.
The remaining height function is the relative quantity h+muCC-Fo.
It must still satisfy DIV and the real quotient/slope comparisons;
defining it to be the right-hand side would not establish a measured
degree inequality. Period logOm is NOT erased by this normalization,
nor is the rank loss, norm control, independent local gain, or
same-object realizability. Do not infer a new RH-strength estimate.

## 5. Verification project: actual inspected targets, not just leaderboard

Dashboard https://riemann.verifytask.cn/?lang=en, retrieved Nov 24.
Its Nov 23 scope notice separates pillar compression (92.23% subset)
from whole-RH optimization. Core 21 remains open on the inspected
dashboard. Core 19 reports 34.6% savings; Core 14 reports 38%.
The live dashboard and independently checked PR results are not the
same scoreboard. At Osgood001/riemann-hypothesis PR #19 head
c5a89d33c6bc782edb02ee6b7988240d82eb1cf3, inspect
community/fortytwo-phase3-4331/core{15,20,23,24,36}/Solution.lean.
Core 15 still takes 15 inputs, ending in CovolumeBoundOfX.
Core 20 still takes the seven original theta inputs.
Core 23 still takes Principalisation, and Core 24 PoincareLelong
and ResKStatement. They narrow source closures, not erase the suspect
supplier path. Core 36 gives a useful explicit integral signed
decomposition using disjoint root lattices and span membership;
its purity and spanning hypotheses must still be earned for native
data. No Core 21 replacement is in that PR. Do not import these
wrappers to claim supplier closure.

## 6. Disposition

The vacuous outer membership is logically removable. At least one
literal transport proof has an independent surviving LamAre branch.
The native finite numerical engine is already at a clean source cut,
and two absolute offsets can be eliminated exactly. The unresolved
step is a real relative-degree, relative-slope and independent recovery
comparison on the same actual arithmetic family. Full upstream
proof-body erasure remains untested; there is no complete rewritten
supplier, no new unconditional terminal theorem and no claim of
exhausting all possible reductions. Do not expand the upstream
geometric reconstruction until a concrete necessary inequality has
been identified at this cut. Use the benchmark's actual reduced
proof bodies only when they prove a necessary substantive leaf.
No build policy or Lean hypotheses changed in this commit.

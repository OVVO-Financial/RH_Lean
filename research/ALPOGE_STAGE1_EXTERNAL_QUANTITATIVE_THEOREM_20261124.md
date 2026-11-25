# Stage 1: accept the external quantitative theorem
2026-11-24. User-directed theoretical stage, separate from the strictly
dependency-clean native proof. This is an external mathematical premise,
not a new Lean axiom, imported theorem, CI exemption or claim of independence.

## 1. Exact quantitative extraction before zero exclusion

Pin: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4.

The external source does not expose the desired scalar conclusion as the
unconditional theorem core_gm: that theorem explicitly takes EAtH and
CoreAtH. Instead extract the mathematical conclusion at the already
discharged application of its windowed family version in the original
terminal proof. The following is a source-level derivation, not a newly
compiled extraction.

In Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean,
let row = UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter.
The fully applied everyCharacter_of_row uses
O = <row, UpperTheory.Zero.LLC.recTExists, row>
and hV = UpperTheory.One.vwin_of_row row.
In ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/
EveryCharacterOfLiteratureOfVWin.lean the theorem
every_character_of_literature_of_vWin supplies the exact P,F,hA,hM,hX,hL
by its displayed applications of published_results_eigen,
published_results_first, theta_integrals_agree_and_local_matching_of_literature,
topCovolSlim2_use_alt_alt and local_langlands_gl_recT_exists_of_literature.
Use precisely those closed applications, not new witness assumptions.

In SiegelEisensteinSecondTermHypotheses.lean, the actual application of
nonempty_hyps_definite_side_of_closed_bound supplies HypsAlt S0.NL
DefiniteSideCondition. Its hN is the lambda using boundAtTwoThree_linked_of_recT
P.nLink (parametersOfDependence hL cDep). Green is supplied by
GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters.
This stage expressly accepts the original geometry-dependent proof.
It does not assert that its dependency closure passes the native exclusion.

In TopPlug.lean (zero_free_all_of_green_v_win), unpack that Nonempty witness.
The exact arguments passed to zeroFreeAll_of_topG are
  la = 3/2, hla : 1 < la;
  hTop = forall_goal_of_shape_of_hyps ... (shape_closed_link_n_of_green hG)
          trivial trivial h;
  hSupply ψ = supplyChi ψ (hV ψ).

In CharacterBoxes/ZeroFreeAllOfTopG.lean, specialize the very same proof
to ψ=PChar.one before the call to zeroFreeOn_of_tiedWin_cyc. Unpack
hTop la (GChi ψ) hla (hSupply ψ) (hypV_of_cls ψ la), which returns
fixed eD,eL,eps1, eps1>0, followed by for each admissible eps a FamP eps
with class membership and uniform eventual ChainTied conditions.
eFamC_of_cls yields EFamC; class membership .1 gives Windows la.
This is exactly ChebyshevInequalityAtWindowScale at Level.cyc ψ.
Then apply UpperTheory.Comparison₂.level_gm_le_on_family_scales
(PrimitiveCosets/LevelGmLeOnFamilyScales.lean), whose proof uses
windowInequality_of_artinInputs and core_gm.

The result (unpacked from TopWin.lean and Window.lean) is:
exists eD,eL,eps1>0, forall eps in (0,eps1), exists S:Set R,x1:R,
HasWindows S (3/2), and forall x>=x1 in S,
(Level.cyc PChar.one).Gm x <= x^(1/2+(eD+eL+7)*eps).
Here HasWindows means forall Y0, exists Y>=Y0, [Y,Y^(3/2)] subset S.
Choose Y using max(Y0,x1,1). The coefficient is exactly 1.
The original argument establishes these witnesses before its final zero-free
consumer. No converse implication from the final RH theorem is needed for
the extraction. No separate absolute bound or eventual bound has been
extracted from the windows alone.

## 2. Literal existing native handoff (no new cancellation)

Set K=eD+eL+7. In the principal cyclic level KEPT is the singleton
PChar.one, so the nonprincipal sum is empty. Level.Gm = Formalism.Gz
at every real x, and the native expression statementOCGz is literally
the same finite von Mangoldt ramp minus x log x plus (1+gamma)x.
The principal equality has a separate proof on #1201 in
NativeExistingRecoveryPayment.lean. Stage 1 does not depend on that branch:
the equality follows mathematically from the singleton kept set, and
main already provides statementOCGz_eq_native for the literal source.

SmallEpsilonWindowBound K eps1 in
RHLean/Analysis/AlpogeNativeBoundHandoff.lean is exactly the external
conclusion with a possibly epsilon-dependent coefficient C.
The principal-window conversion is mathematical here (and is also
expressed by nativeSmallEpsilonWindowBound_of_principalCyclic on #1201).
C=1 suffices here. No #1201 Lean declaration is needed.
Choose eps=min(eps1/2, eta/(|K|+1)). On windows with Y>=1,
x^(1/2+K eps)<=x^(1/2+eta). The native theorem
riemannHypothesis_of_smallEpsilonWindowBound consumes this input,
using the native Landau argument rather than the upstream RH theorem.
Thus the external quantitative theorem implies RH using the existing
native handoff. That is a complete mathematical implication RELATIVE
TO the external theorem, not a new independent proof.

At each positive integer N in such a window, the native exact identity
nativeAlpogeGz_eq_NNSHistory yields
  H_NNS(N) <= N^(-1/2+eta),
where H_NNS=U_N-L_N+harmonic(N)-log N+gamma.
The existing theorem nativeAlpogeGz_rpow_le_iff_NNSUpper gives the same
upper mass comparison, including every prime power and harmonic correction.
At X_R=R^2-1 in the window, with exponent parameter eta/2, this is
Gz(X_R)=O_eta(R^(1+eta)) one-sided and
H_NNS(X_R)=O_eta(R^(-1+eta)) one-sided.
The same constant works across all qualifying windows at fixed eta.
No assertion that every R lies in one of these windows.

## 3. Floor-Li tracking and the existing transport

Once the RH conclusion is accepted, the classical von Koch theorem
gives pi(x)-Li_2(x)=O(sqrt(x) log x) for all sufficiently large x.
This standard analytic consequence is a separate mathematical implication;
the full RH->von Koch Lean proof is not supplied here. The native
VF_MID_VON_KOCH_BRIDGE.lean uses an explicit ClassicalVonKochRHCriterion.
For Q(n)=floor(Li_2(n)), the already-proved rounding debt is <1,
hence E_R=pi(R^2)-Q(R^2)=O(R log R).
The exact square-endpoint VF bridge is
vfMidPrimeError_sq_eq_floorLiBacklog_add_bridge; the deterministic
bridge has O(R) bound (and the stronger endpoint quadrature result).
For delta_R=actual prime supply minus Q supply, the existing transport
theorem gives sum_{r=A}^{B-1} delta_r=E_B-E_A.
The already-proved energy identity gives
sum_{r=A}^{B-1}(delta_r^2+2 E_r delta_r)=E_B^2-E_A^2.
These are then quantitatively bounded by O(B log B) and
O(B^2 log^2 B) respectively, for 2<=A<=B. No new signed-cancellation
law, pointwise event alignment, or uniform two-bin relocation lifetime
is inferred. The latter is neither established by RH nor required here.

## 4. Boundary and next stage

Stage 1 establishes the theory-to-native implication, treating the
geometry-dependent upstream quantitative estimate as an accepted
external theorem. The exact source-level extraction above is not yet
separately compiled. This separate PR is based on main, not #1201. The companion research Lean
file checks the same-window RH and NNS consequences with the external
theorem as an explicit argument. No native library code or global
assumptions changed; no external proof was imported; strict dependency
gates remain intact. Its hosted compilation is pending. The native
unconditional RH objective remains OPEN. Any later independent stage
must remove or independently discharge the external premise, not
invoke this stage as a geometry-free supplier. A green conditional
consumer cannot count as an independent proof.

## 5. Closed external-dependency replay (Stage 1 completion gate)

The user clarified that Stage 1 must compile a **closed** Lean RH declaration,
not merely the conditional native consumer. See
`scripts/alpoge_stage1/ClosedRH.lean.in` and its dedicated hosted workflow
`alpoge-stage1-external.yml`.

The frozen dependency is homeowmorphism/riemann-hypothesis-original@
774b9e8022f50d20be861ecc9d609cfc26436a81, with Lean 4.33.1 and original Mathlib
0df444a360eaa60ab8c11dca51a86af692955474. The mirror's source tree
24df20b62d9976ccd20da819bc20b16f808f0fdd includes its separate challenge
setup; it is not claimed identical as a whole Git tree to the CocoSgt mirror.
No mixed-toolchain imports. The replay uses the published pinned community
cache described at https://github.com/homeowmorphism/riemann-hypothesis-original/blob/774b9e8022f50d20be861ecc9d609cfc26436a81/verification/CACHE.md.
It accepts cached external proofs, not an independent fresh full build.

The root principalQuantitativeWindowBound uses the actual original
TopG supplier application and level_gm_le_on_family_scales. It supplies
externalQuantitative, with literally the #1205 SmallEpsilonWindowBound
statement copied from the checked-out native source. The new
RHLean.Analysis.AlpogeStage1External.riemannHypothesis declaration has no
arguments and applies the explicit externalQuantitative proof to the
compatible scalar handoff using Deduction.zeroFree_of_rpow_window and
the functional equation. This uses the same analytic criterion as FormB
with its general constant retained. The original terminal RH proof is not applied.
The native 4.34.1 research consumer remains separate. This choice is
necessary to avoid mixing incompatible compiler/mathlib pins; a closed
4.34.1 native-library root would still require porting the upstream proof
or a verified proof-term transfer. We do not claim such a port here.

The dedicated workflow verifies the source/dependency pins, restores
the frozen community cache, and elaborates the new root, enforcing its
exact kernel type, standard axiom list, required quantitative dependencies
and exclusion of named original terminal shortcuts. The source closure
walk is a dependency diagnostic; it is not a geometry-free audit. No native workflow or
independent-proof status gate is weakened. Acceptance requires the new
compile and its closed-root marker; a green native conditional check
alone does not complete Stage 1.

Resource constraint: upstream documents about 105 GB free disk; this
workflow targets 115 GiB during cleanup and requires 110 GiB at preflight. Set the repository variable
RHLEAN_ALPOGE_REPLAY_RUNNER to an authorized large hosted runner if the
default runner has insufficient space. The connector cannot provision
or verify such a runner. No claim of successful compilation until the
exact-head replay passes. The cache setup may also require substantial
RAM. Stage 1 is deliberately not a strict geometry-free proof.

### Exact-head resource preflight result

Run 45521381855, job 138893826723, on b5180ddc, reached the capacity
check and failed with 87 GiB free disk (145 GiB filesystem) and 15 GiB RAM.
The Lean compile was skipped, not failed on a theorem. The follow-up
workflow reclaims only explicitly listed unused SDK directories, only on
disposable GitHub-hosted runners and only until the disk threshold is
met. It does not touch Lean, Mathlib, upstream caches or native checks.
If insufficient space remains, the preflight still fails. The larger
runner variable remains available. Actual proof verification is pending.

### Correct the excess preflight reserve

Run 45521504929, job 138894238473, on 3e977d7d, completed the
approved unused-SDK cleanup and reported 113 GiB free, versus 87 GiB
previously. It was stopped solely by our 115 GiB preflight reserve.
The pinned upstream CACHE.md documents approximately 105 GB free disk
for its full published cache setup, including 4.94 GB of compressed
project archives. We therefore retain 115 GiB as the cleanup target
but set the hard resource estimate to 110 GiB. This is about 118 GB
in decimal units and retains at least 5 GiB above the documented
number even if interpreted conservatively in binary units. No proof
check, source pin, cache integrity check, or axiom/dependency audit
changes. Actual peak disk and RAM usage still need hosted measurement;
the new threshold is a documented estimate, not a guarantee that the
full cache and proof elaboration fit. A successful resource preflight
must never be treated as a successful Lean replay.

### Import-closure-only replay after the actual ENOSPC failure

Run 45522129793/job 138896348040 passed resource preflight but failed
during the original 175187-module bulk restore with ENOSPC (user-supplied
job log). We cannot fix that by reducing a disk threshold. Stage 1 only
requires the original quantitative suppliers and scalar analytic handoff.

ClosedRH.lean.in now explicitly imports the four original supplier
modules of MainConclusion.lean plus the quantitative window and analytic
criterion modules. It no longer imports MainConclusion directly or asks
Lake to build Main. The frozen supplier files themselves still contain
some terminal consumers beside the required declarations; deleting their
theorems would change the accepted upstream dependency. Actual proof-term
audit still forbids the named terminal shortcuts.

restore_closure.py traverses the literal imports of the pinned original
source from these roots, validates the entire pinned manifest, selects
only the transitive project module closure, and delegates SHA-256-checked
downloads and per-module archive/output validation to the original mirror
helpers. Restore is batched (512 modules, four leantar workers) rather
than a single 24-worker restore. After each batch discard generated C
source and editor .ilean indexes only. Preserve every compiled .olean
variant, Lean IR/signature and original proof expression. Never edit
the frozen source. The command-line Lean elaboration still fails on
any missing import. This deliberately accepts the published external
proof objects; it is not a fresh independent build of the original proof.

Save verified compressed archives before unpacking, so a later resource
or elaboration failure need not repeat the downloads. Report exact
selected and omitted module counts, imports and disk use. Initial disk
guard is retained; batch guards stop before exhausting the remaining
filesystem. No change to closed RH theorem, quantitative statement,
axiom whitelist or transitive proof audit. The actual closure cardinality,
peak storage and successful Lean replay are not yet measured. In
particular the supplier closure may still be large; the larger-runner
option remains available if the selected cache cannot fit.

### First actual Lean replay: quantitative root verified

Run 45524750963/job 138905200712 on ec75c336 restored all 175174
selected modules (13 omitted from the 175187-module manifest) and
retained 5.50 GiB free. This is an import closure, not the number of
theorems logically used. The verified compressed cache was saved before
the extraction. The full restore finished at 01:38:43 UTC; Lean
reported its result at 02:09:40 UTC on 2026-11-25.

The first substantive root, principalQuantitativeWindowBound,
elaborated with exactly the allowed axioms propext, Classical.choice,
Quot.sound. It is the closed principal-character cofinal-window
quantitative inequality on RH_Lean's literal statementOCGz source.

The only reported elaboration error was in externalQuantitative:
simp only [one_mul] did not unfold the set comprehension membership
returned by the HasWindows witness. Explicitly change the witness's
type to the pointwise inequality before simplifying 1 * rpow.
The downstream sorryAx reports are consequences of this failed
declaration, not independent missing quantitative premises. The
conditional analytic handoff had no separate reported elaboration error.
The exact-root, axiom and transitive dependency audits remain mandatory;
the latter did not complete on this attempt. No claim of a verified
closed RH declaration until the repaired exact-head job passes.

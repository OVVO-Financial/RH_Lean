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
The native theorem nativePrincipalCyclicGm_eq_statementOCGz in
NativeExistingRecoveryPayment.lean already establishes the principal
equality for RH_Lean's matching definitions.

SmallEpsilonWindowBound K eps1 in
RHLean/Analysis/AlpogeNativeBoundHandoff.lean is exactly the external
conclusion with a possibly epsilon-dependent coefficient C.
The existing theorem nativeSmallEpsilonWindowBound_of_principalCyclic
is the precise quantifier conversion. C=1 suffices here.
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
separately compiled. No native code or assumptions changed; no external
proof was imported; strict dependency gates remain intact. The native
unconditional RH objective remains OPEN. Any later independent stage
must remove or independently discharge the external premise, not
invoke this stage as a geometry-free supplier. A green conditional
consumer cannot count as an independent proof.

import RHLean.Analysis.AlpogeThin.NativePrincipalEAtH
import RHLean.Analysis.AlpogeThin.NativeConstructedDyadicGzPayment
import RHLean.Analysis.AlpogeNativeBoundHandoff
import RHLean.Geometry.NativeSquareCapacityPeriod
import RHLean.Geometry.NativeCore33HostDegree
import Lean.Util.CollectAxioms

/-!
This checks actual declarations, including opaque proof terms, for the
absolute exclusion. It is not a claim that the remaining signed cost
is paid. Renamed or definitionally erased vacuous witnesses require
independent semantic review in addition to this name-based hard gate.
-/
open Lean Elab Command

private partial def strictClosure (env : Environment) (todo : List Name)
    (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then strictClosure env rest seen else
      let deps := match env.find? n with
        | none => []
        | some info => info.type.getUsedConstants.toList ++
            ((info.value? (allowOpaque := true)).map
              (fun e => e.getUsedConstants.toList)).getD []
      strictClosure env (deps ++ rest) (seen.insert n)

run_cmd do
  let env ← getEnv
  let roots : Array Name := #[
    `RHLean.Geometry.NativeCore33.primeOrder_le_degree,
    `RHLean.Geometry.NativeCore33.primePower_eq_one,
    `RHLean.Geometry.NativeCore33.local_unipotent_primePower,
    `RHLean.Geometry.NativeCore33.local_unipotent_eq_one,
    `RHLean.Analysis.AlpogeThin.nativeCore33_primeOrder_le,
    `RHLean.Analysis.AlpogeThin.nativeCore33_localStabilizer_eq_one,
    `RHLean.Analysis.AlpogeThin.nativeDyadic_trivialCharacter_signs,
    `RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_principalTwist,
    `RHLean.Analysis.AlpogeThin.nativeDyadicHostRaw_EAtH,
    `RHLean.Analysis.AlpogeThin.nativePrincipalEAtH_windows,
    `RHLean.Analysis.AlpogeThin.nativeConstructedDyadicGzPayment,
    `RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.WeightedSlopeBounds.nativeRelativeDegreeCount_le,
    `RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.WeightedSlopeBounds.nativeGa_bound_of_coupled_period,
    `RHLean.Geometry.AlpogeSignedSlope.Formalism.LFunctionChainParameters.WeightedSlopeBounds.nativeMean_bound_of_coupled_period,
    `RHLean.Analysis.AlpogeNativeSignedSlope.physicalTopExcess_div_le_errorTerm_of_coupled_period,
    `RHLean.Analysis.AlpogeNativeBoundHandoff.riemannHypothesis_of_smallEpsilonWindowBound]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for root in roots do
    unless env.contains root do
      throwError "Missing actual principal source root: {root}"
    let axs ← liftCoreM (Lean.collectAxioms root)
    for a in axs do
      unless allowed.contains a do
        throwError "Forbidden axiom: {root} depends on {a}"
    let names := strictClosure env [root]
    for n in names.toList do
      let s := n.toString.toLower.replace "_" ""
      if (s.splitOn "geocl").length > 1 ||
          (s.splitOn "anygeometry").length > 1 then
        throwError "ABSOLUTE PROHIBITION: {root} depends on {n}"
    logInfo m!"PASS strict principal source dependency gate: {root}; axioms={axs}; dependencies={names.toList.length}"

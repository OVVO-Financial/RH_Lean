import Lean
import «research.VF_919_OPENAI_434_UNCONDITIONAL_SQUARE_BLOCK_COVARIANCE_20261019»

/-! Audit proof expressions, not just source strings. The intermediate
analytic lemmas are allowed; upstream terminal seven-eighths wrappers are not.
This metaprogram checks declarations and contributes no proof premise. -/

open Lean Elab Command

set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace VF919CommonProbeAudit

private partial def collect (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify fun s => s.insert n
  let collectExpr (e : Expr) : StateM NameSet Unit :=
    e.getUsedConstants.forM (collect env)
  match env.checked.get.find? n with
  | some (.axiomInfo v) => collectExpr v.type
  | some (.defnInfo v) => collectExpr v.type *> collectExpr v.value
  | some (.thmInfo v) => collectExpr v.type *> collectExpr v.value
  | some (.opaqueInfo v) => collectExpr v.type *> collectExpr v.value
  | some (.quotInfo _) => pure ()
  | some (.ctorInfo v) => collectExpr v.type
  | some (.recInfo v) => collectExpr v.type
  | some (.inductInfo v) => collectExpr v.type *> v.ctors.forM (collect env)
  | none => pure ()

private def roots : Array Name := #[
  `RHLean.Analysis.VF919SevenEighths.certifiedBands,
  `RHLean.Analysis.VF919SevenEighths.chosenMoments,
  `RHLean.Analysis.VF919SevenEighths.commonProbe,
  `RHLean.Analysis.VF919SevenEighths.beta_le_seven_eighths,
  `RHLean.Analysis.VF919SevenEighths.hecke_nonzero,
  `RHLean.Analysis.VF919SevenEighths.dirichlet_nonzero,
  `RHLean.Analysis.VF919SevenEighths.zeta_nonzero,
  `RHLean.Analysis.commonProbe_actual_mertens_growth,
  `RHLean.Analysis.openai434_actual_global_signed_covariance,
  `RHLean.Analysis.openai434_actual_all_square_block_covariance]

private def forbidden : Array Name := #[
  `sorryAx, `admitAx,
  `OAI.SevenEighths.ProbeFinalAssemblyUnconditional,
  `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re,
  `OAI.SevenEighths.HeckeCommonProbe.beta_le_seven_eighths,
  `OAI.SevenEighths.HeckeCommonProbe.hecke_ne_zero_of_common_probe,
  `OAI.SevenEighths.HeckeCommonProbe.dirichlet_of_common_probe,
  `OAI.SevenEighths.HeckeCommonProbe.zeta_of_common_probe,
  `OAI.SevenEighths.ProbeFinalAssembly.common_probe_of_chosen_moments,
  `OAI.SevenEighths.ProbeFinalAssembly.dirichlet_of_chosen_moments,
  `OAI.SevenEighths.ProbeFinalAssembly.zeta_of_chosen_moments,
  `OAI.SevenEighths.ProbeFinalAssembly.hecke_of_chosen_moments,
  `OAI.SevenEighths.ProbeFinalAssemblyCertifiedBands.dirichlet_of_certified,
  `OAI.SevenEighths.ProbeFinalAssemblyCertifiedBands.zeta_of_certified]

run_cmd do
  let env ← getEnv
  for root in roots do
    unless (env.find? root).isSome do
      throwError "Missing acceptance declaration: {root}"
    let axs ← collectAxioms root
    for ax in axs do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Nonstandard axiom {ax} in {root}"
    logInfo m!"PASS standard axioms: {root}"
  let deps := ((roots.forM (collect env)).run ({} : NameSet)).2
  for n in deps.toArray do
    if forbidden.any (fun bad => bad.isPrefixOf n) then
      throwError "Forbidden upstream terminal dependency: {n}"
  unless deps.contains `OAI.SevenEighths.ProbeFinalAssembly.fixed_high_bound do
    throwError "HIGH source estimate absent from the proof closure"
  unless deps.contains `OAI.SevenEighths.ProbeFinalAssembly.SourceData.probe_low do
    throwError "LOW estimate absent from the proof closure"
  unless deps.contains `OAI.SevenEighths.HeckeSignal.nonzero_of_probe_bounds do
    throwError "Mellin common-signal contradiction absent from the proof closure"
  logInfo m!"PASS: {deps.toArray.size} dependencies checked; actual LOW/HIGH/Mellin mechanism, no upstream terminal seven-eighths wrapper"

end VF919CommonProbeAudit

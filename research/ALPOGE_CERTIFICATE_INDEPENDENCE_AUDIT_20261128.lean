import «research.NativePrimitiveDeterminantCertificate»
import ImportGraph.Imports.RequiredModules
import Lean.Util.CollectAxioms

/-! Audit the finite determinant and complete-clock transfers independently of
the terminal declaration. The dependency walk includes opaque proof bodies. -/

open Lean Elab Command

run_cmd do
  let roots : Array Name := #[
    ``RHLean.Analysis.PrimitiveCertificate.block_eq_cyclotomic,
    ``RHLean.Analysis.PrimitiveCertificate.certificate_pos,
    ``RHLean.Analysis.PrimitiveCertificate.certificate_rounding,
    ``RHLean.Analysis.PrimitiveCertificate.trace_reference_uniform,
    ``RHLean.Analysis.PrimitiveCertificate.block_endpoint_correction,
    ``RHLean.Analysis.PrimitiveCertificate.statementOCGz_add_residual,
    ``RHLean.Analysis.PrimitiveCertificate.statementOCGz_rounded_residual,
    ``RHLean.Analysis.PrimitiveCertificate.statementOCGz_sub_trace]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for root in roots do
    for ax in ← liftCoreM (Lean.collectAxioms root) do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  let used ← liftCoreM (NameSet.ofList roots.toList).transitivelyUsedConstants
  let excluded := #[``RiemannHypothesis, `native_riemannHypothesis,
    `riemannHypothesis, `New.grh, `New.zeta_zeros_on_line,
    ``RHLean.Analysis.AlpogeNativeBoundHandoff.SmallEpsilonWindowBound,
    ``RHLean.Analysis.AlpogeNativeBoundHandoff.EventualRealBound,
    ``RHLean.Analysis.AlpogeNativeBoundHandoff.SquareClockBound]
  for name in excluded do
    if used.contains name then
      throwError "Signed determinant transfer depends on {name}"
  logInfo m!"Audited {roots.size} determinant and transfer theorems across {used.toList.length} declarations"

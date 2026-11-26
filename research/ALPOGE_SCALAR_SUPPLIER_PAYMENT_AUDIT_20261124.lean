import RHLean.Analysis.AlpogeThin.NativeScalarSupplierPayment

/-! These roots pay actual scalar costs. The geometric gain, compatible
widths, measured slopes, and the construction on arbitrarily late complete
windows remain hypotheses of the existing physical consumer. -/

#check RHLean.Analysis.AlpogeThin.nativeDyadicLocalShiftCost_scalar_eventually
#check RHLean.Analysis.AlpogeThin.nativeDyadicLocalLogShiftPrice_eventually
#check RHLean.Analysis.alpogeNativeGzArithmetic_sub_abs_le_global
#check RHLean.Analysis.alpogeNativeGzArithmetic_le_mean_add_move
#check RHLean.Analysis.AlpogeThin.NativeGeometricCostWindows.normalizedCosts_add_remainder_le
#check RHLean.Analysis.AlpogeThin.NativeGeometricCostWindows.normalizedCosts_add_analytic_le
#check RHLean.Analysis.AlpogeThin.geometricSizeWindows_of_squareClock_pageN
#check RHLean.Analysis.AlpogeThin.nativeGz_le_of_mean_normalizedCosts

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let roots : Array Name := #[``RHLean.Analysis.AlpogeThin.nativeDyadicLocalShiftCost_scalar_eventually,
    ``RHLean.Analysis.AlpogeThin.nativeDyadicLocalLogShiftPrice_eventually,
    ``RHLean.Analysis.alpogeNativeGzArithmetic_sub_abs_le_global,
    ``RHLean.Analysis.alpogeNativeGzArithmetic_le_mean_add_move,
    ``RHLean.Analysis.AlpogeThin.NativeGeometricCostWindows.normalizedCosts_add_remainder_le,
    ``RHLean.Analysis.AlpogeThin.NativeGeometricCostWindows.normalizedCosts_add_analytic_le,
    ``RHLean.Analysis.AlpogeThin.geometricSizeWindows_of_squareClock_pageN,
    ``RHLean.Analysis.AlpogeThin.nativeGz_le_of_mean_normalizedCosts]
  let env ← getEnv
  for root in roots do
    unless env.contains root do
      throwError "Missing native declaration: {root}"
    let axioms ← liftCoreM (Lean.collectAxioms root)
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unapproved terminal axiom for {root}: {ax}"
    logInfo m!"PASS native scalar supplier {root}: {axioms}"

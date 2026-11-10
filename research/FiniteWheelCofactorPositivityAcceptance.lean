import Lean
import «research.FiniteWheelCofactorPositivity»

open RHLean.Analysis RHLean.Proof
open scoped BigOperators

noncomputable section

example (z : ℕ) (hz : 2 ≤ z) :
    1 ≤ 3 * (z : ℝ) * vfMidPrefixWheelDensity z ^ 2 :=
  finiteWheel_density_sq_lower z hz

example (z : ℕ) (hz : 2 ≤ z) :
    1 / Real.sqrt (3 * (z : ℝ)) ≤ vfMidPrefixWheelDensity z :=
  finiteWheel_density_lower z hz

example (R q : ℕ) (hR : 47 ≤ R) (hq : R ≤ q) (hq2 : q < 2 * R) :
    0 < finiteWheelCofactorTotal (R - 1) (squareRootEndpoint R) q :=
  finiteWheel_cofactor_pos R q hR hq hq2

example (R : ℕ) (hR : 47 ≤ R) :
    0 ≤ ∑ q ∈ (Finset.Ico R (2 * R)).filter Nat.Prime,
      finiteWheelCofactorTotal (R - 1) (squareRootEndpoint R) q :=
  finiteWheel_primeFibre_sum_nonneg R hR

example : 0 < finiteWheelCofactorTotal 46 (squareRootEndpoint 47) 47 :=
  finiteWheel_cofactor_pos 47 47 (by omega) (by omega) (by omega)

example : 0 < finiteWheelCofactorTotal 46 (squareRootEndpoint 47) 93 :=
  finiteWheel_cofactor_pos 47 93 (by omega) (by omega) (by omega)

#check @finiteWheel_density_coefficient_sharp
#check @finiteWheel_cofactor_eq_count
#check @finiteWheel_cofactor_square_eq
#check @finiteWheel_cofactor_square_bounds

/-- info: 'RHLean.Analysis.finiteWheel_density_sq_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finiteWheel_density_sq_lower

/-- info: 'RHLean.Analysis.finiteWheel_density_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finiteWheel_density_lower

/-- info: 'RHLean.Analysis.finiteWheel_density_coefficient_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finiteWheel_density_coefficient_sharp

/-- info: 'RHLean.Analysis.finiteWheel_cofactor_eq_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finiteWheel_cofactor_eq_count

/-- info: 'RHLean.Analysis.finiteWheel_cofactor_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finiteWheel_cofactor_pos

/-- info: 'RHLean.Analysis.finiteWheel_primeFibre_sum_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finiteWheel_primeFibre_sum_nonneg

namespace FiniteWheelCofactorAudit

open Lean Elab Command

private partial def reduceAdmin : Expr → Expr
  | .letE _ _ value body _ => reduceAdmin (body.instantiate1 value)
  | .app fn arg =>
    match reduceAdmin fn with
    | .lam _ _ body _ => reduceAdmin (body.instantiate1 arg)
    | other => .app other (reduceAdmin arg)
  | .lam n t b bi => .lam n (reduceAdmin t) (reduceAdmin b) bi
  | .forallE n t b bi => .forallE n (reduceAdmin t) (reduceAdmin b) bi
  | .mdata _ b => reduceAdmin b
  | .proj n i b => .proj n i (reduceAdmin b)
  | other => other

private partial def proofClosure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | n :: rest =>
    if seen.contains n then proofClosure env rest seen
    else
      let refs := if (`RHLean).isPrefixOf n || (`_private).isPrefixOf n then
        match env.find? n with
        | none => []
        | some info => match info.value? (allowOpaque := true) with
          | none => []
          | some value => (reduceAdmin value).getUsedConstants.toList
        else []
      proofClosure env (refs ++ rest) (seen.insert n)

run_cmd do
  let root := `RHLean.Analysis.finiteWheel_primeFibre_sum_nonneg
  let reached := proofClosure (← getEnv) [root]
  for required in #[`RHLean.Analysis.finiteWheel_density_sq_lower,
      `RHLean.Analysis.finiteWheel_cofactor_eq_count,
      `RHLean.Analysis.finiteWheel_cofactor_square_eq,
      `RHLean.Analysis.finiteWheel_cofactor_square_bounds,
      `RHLean.Analysis.finiteWheel_cofactor_pos,
      `RHLean.Analysis.finiteWheel_divisorReciprocal_eq_eulerProduct,
      `RHLean.Analysis.finiteWheel_divisorFloor_eq_survivorCount,
      `RHLean.Analysis.vfMidPrefixWheelDensity,
      `RHLean.Proof.squareRootEndpoint] do
    unless reached.contains required do
      throwError "Missing live cofactor dependency: {required}"
  logInfo m!"PASS complete cofactor source dependencies: {root}, closure={reached.size}"

end FiniteWheelCofactorAudit

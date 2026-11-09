import Lean
import «research.DyadicPrimeNearResonance»

/-! Public types, actual arithmetic witnesses, and live proof dependencies. -/

open RHLean.Analysis

noncomputable section

example (R p q r : ℕ) (hR : 8 ≤ R)
    (hpq : dyadicPrimePair R p q) (hqr : dyadicPrimePair (2 * R) q r)
    (hstep : r + 1 = 4 * p ∨ r = 4 * p + 1) :
    dyadicPrimePhase R p q ≠ dyadicPrimePhase (2 * R) q r ∧
      ∀ t : ℝ, t ^ 2 ≤ 4 * R →
        (1 - 2 * R / ((R : ℝ) - 1) ^ 2 ≤
          Real.cos (t * (dyadicPrimePhase R p q - dyadicPrimePhase (2 * R) q r)) ∧
        (33 : ℝ) / 49 ≤
          Real.cos (t * (dyadicPrimePhase R p q - dyadicPrimePhase (2 * R) q r))) :=
  dyadicPrimePhase_near_resonance R p q r hR hpq hqr hstep

example :
    ∃ R p q r : ℕ, 8 ≤ R ∧ admittedDyadicPrimePair R p q ∧
      admittedDyadicPrimePair (2 * R) q r ∧
      dyadicPrimePhase R p q ≠ dyadicPrimePhase (2 * R) q r ∧
      ∀ t : ℝ, |t| ≤ 2 * Real.sqrt R →
        (33 : ℝ) / 49 ≤ (dyadicPrimePhaseWave R p q t *
          star (dyadicPrimePhaseWave (2 * R) q r t)).re :=
  dyadicPrimeNearResonance_counterexample

example (t : ℝ) (ht : t ^ 2 ≤ 256) :
    (33 : ℝ) / 49 ≤
      Real.cos (t * (dyadicPrimePhase 64 37 67 - dyadicPrimePhase 128 67 149)) := by
  obtain ⟨hpq, hqr⟩ := dyadicPrimeNearResonance_sixtyFour_admitted
  have h := dyadicPrimePhase_near_resonance 64 37 67 149 (by omega)
    hpq.1 hqr.1 (by omega)
  exact (h.2 t (by norm_num; exact ht)).2

#check @dyadicPrimePhase_shared
#check @sharedPrime_ratio_bounds
#check @dyadicPrimePhase_near_resonance
#check @dyadicPrimePhase_hermitian_eq_cos
#check @dyadicPrimeNearResonance_eight_admitted
#check @dyadicPrimeNearResonance_sixtyFour_admitted
#check @dyadicPrimeNearResonance_counterexample

/-- info: 'RHLean.Analysis.dyadicPrimePhase_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dyadicPrimePhase_shared

/-- info: 'RHLean.Analysis.sharedPrime_ratio_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sharedPrime_ratio_bounds

/-- info: 'RHLean.Analysis.dyadicPrimePhase_near_resonance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dyadicPrimePhase_near_resonance

/-- info: 'RHLean.Analysis.dyadicPrimePhase_hermitian_eq_cos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dyadicPrimePhase_hermitian_eq_cos

/-- info: 'RHLean.Analysis.dyadicPrimeNearResonance_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dyadicPrimeNearResonance_counterexample

namespace DyadicPrimeNearResonanceAudit

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
  let env ← getEnv
  let root := `RHLean.Analysis.dyadicPrimeNearResonance_counterexample
  let reached := proofClosure env [root]
  for required in #[`RHLean.Analysis.dyadicPrimePhase_shared,
      `RHLean.Analysis.sharedPrime_ratio_bounds,
      `RHLean.Analysis.dyadicPrimePhase_near_resonance,
      `RHLean.Analysis.dyadicPrimePhase_hermitian_eq_cos,
      `RHLean.Analysis.dyadicPrimeNearResonance_eight_admitted,
      `RHLean.Analysis.squareRootEndpoint,
      `Real.log_le_sub_one_of_pos,
      `Real.one_sub_sq_div_two_le_cos] do
    unless reached.contains required do
      throwError "Missing live near-resonance dependency: {required}"
  logInfo m!"PASS genuine near-resonance live dependencies: {root}, closure={reached.size}"

end DyadicPrimeNearResonanceAudit

#print axioms dyadicPrimeNearResonance_eight_admitted
#print axioms dyadicPrimeNearResonance_sixtyFour_admitted
#print axioms dyadicPrimePhase_near_resonance
#print axioms dyadicPrimeNearResonance_counterexample

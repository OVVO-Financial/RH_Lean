import «research.NYMAN_TAIL_PHASES»
open Finset RHLean.Analysis
open scoped BigOperators

example (N P : Nat) (c : Nat → ℝ) (hp : ∀ k ∈ Icc 2 N, k ∣ P) :
    Function.Periodic (fun t => ∑ i ∈ range t, (nymanResidual N c i^2 -
      (nymanPeriodBias N c^2 + nymanCovariance N c))) P := nyman_cutoff_primitive_periodic N P c hp

example (N P s : Nat) (c : Nat → ℝ) (hP : 0<P) (hs : 0<s) (hp : ∀ k ∈ Icc 2 N, k ∣ P) :
    HasSum (fun n : Nat => (nymanWeight (s+n)-nymanWeight (s+n+1))*
      (nymanCutoffPrimitive N c (s+n+1)-nymanCutoffPrimitive N c s))
      ((∑' n : Nat, nymanWeight (s+n)*nymanResidual N c (s+n)^2) -
        (nymanPeriodBias N c^2 + nymanCovariance N c)/(s:ℝ)) := nyman_tail_abel N P s c hP hs hp

example (N P : Nat) (c : Nat → ℝ) (hP : 0<P) (hp : ∀ k ∈ Icc 2 N, k ∣ P)
    (hv : ∃ i j, nymanResidual N c i^2 ≠ nymanResidual N c j^2) :
    ∃ a b : Fin P, a ≠ b ∧
      (∀ s : Nat, 0<s → s%P=a.val → (nymanPeriodBias N c^2+nymanCovariance N c)/(s:ℝ) < nymanPhysicalTail N c s) ∧
      (∀ s : Nat, 0<s → s%P=b.val → nymanPhysicalTail N c s < (nymanPeriodBias N c^2+nymanCovariance N c)/(s:ℝ)) :=
  nyman_tail_two_phases N P c hP hp hv

example (N P : Nat) (c : Nat → ℝ) (hP : 0<P) (hp : ∀ k ∈ Icc 2 N, k ∣ P)
    (h1 : ∑ k ∈ Icc 2 N, c k/(k:ℝ) = 1) (h3 : ∑ k ∈ Icc 2 N, c k = 3) :
    ∃ a b : Fin P, a ≠ b ∧
      (∀ s : Nat, 0<s → s%P=a.val → nymanCovariance N c/(s:ℝ) < nymanPhysicalTail N c s) ∧
      (∀ s : Nat, 0<s → s%P=b.val → nymanPhysicalTail N c s < nymanCovariance N c/(s:ℝ)) :=
  nyman_two_moment_tail_phases N P c hP hp h1 h3

#print axioms nyman_cutoff_primitive_periodic
#print axioms nyman_tail_abel
#print axioms nyman_tail_two_phases
#print axioms nyman_two_moment_tail_phases

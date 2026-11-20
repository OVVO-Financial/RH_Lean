import «research.NYMAN_WITNESS_RANK»
noncomputable section
open RHLean.Analysis

private abbrev u (k h : ℕ) := nymanFlatMoment (6*k) h
private abbrev v (k h : ℕ) := nymanRidgeV k h
private abbrev a (k h : ℕ) := nymanRidgeLeft k (u k h) (v k h)
private abbrev z (k h : ℕ) := nymanRidgeRight k (u k h) (v k h)
private abbrev c (k m : ℕ) := nymanBandCount (3*k) (4*k) m
private abbrev e (k m : ℕ) := nymanBandCount (5*k) (6*k) m
private abbrev err (k h m : ℕ) := nymanResidual (6*k) (nymanRidgeCoeff k h) m - nymanWitnessClipped k h m

example (k h p : ℕ) (hp : p.Prime) (lp : 3*k < p) (up : p < 6*k) (hh : 0 < h) (lh : h < p)
    (x y : ℚ) (rel : (x:ℝ)*u k h + (y:ℝ)*v k h = 0) : x + (p:ℚ)*y = 0 :=
  nyman_witness_relation_coordinate k h p hp lp up hh lh x y rel
example (k h m : ℕ) (hk : 0 < k) : err k h m =
    (a k h * ((c k m:ℝ)-k) + z k h * ((e k m:ℝ)-k)) / nymanFlatScale (6*k) h :=
  nyman_witness_error_counts k h m hk

section
variable (k h p q : ℕ) (hh : 0 < h) (hp : p.Prime) (hq : q.Prime) (hn : p ≠ q)
    (lp : max (3*k) h < p) (up : p < 6*k) (lq : max (3*k) h < q) (uq : q < 6*k)
include hh hp hq hn lp up lq uq
example (x y : ℚ) : (x:ℝ)*a k h + (y:ℝ)*z k h = 0 ↔ x = 0 ∧ y = 0 :=
  nyman_witness_two_amplitudes k h p q hh hp hq hn lp up lq uq x y
example (m n : ℕ) : err k h m = err k h n ↔ c k m = c k n ∧ e k m = e k n :=
  nyman_witness_clip_fibres k h p q hh hp hq hn lp up lq uq m n
example (m : ℕ) : err k h m = 0 ↔ m = 6*k ∨ m = 6*k+1 :=
  nyman_witness_clip_zero_iff k h p q hh hp hq hn lp up lq uq m
end

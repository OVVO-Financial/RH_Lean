import «research.NYMAN_WITNESS_CLIP»
noncomputable section
open RHLean.Analysis Finset
open scoped BigOperators

example (p K : ℕ) (s : Finset ℕ) (hp : p.Prime) (hk : 0 < K) (ht : K < p)
    (hs : ∀ k ∈ s, 0 < k ∧ k < 2*p) (h1 : p ∈ s → 2 ≤ K) :
    (∑ k ∈ s, 1/(k:ℚ)) ≠ (K:ℚ)/p := nyman_witness_reciprocal p K s hp hk ht hs h1

private abbrev left (K H : ℕ) := nymanRidgeLeft K (nymanFlatMoment (6*K) H) (nymanRidgeV K H)
private abbrev right (K H : ℕ) := nymanRidgeRight K (nymanFlatMoment (6*K) H) (nymanRidgeV K H)
private abbrev err (K H m : ℕ) := nymanResidual (6*K) (nymanRidgeCoeff K H) m - nymanWitnessClipped K H m
private abbrev cost (K H : ℕ) := ∑ j ∈ range (K+3), nymanWeight (8*K+j)*(err K H (8*K+j))^2

example (K H p : ℕ) (hp : p.Prime) (hl : 3*K < p) (hr : p < 6*K) (hh : 0 < H) (h : H < p) :
    left K H ≠ 0 ∧ right K H ≠ 0 := nyman_witness_amplitudes_of_prime K H p hp hl hr hh h
example (K H : ℕ) (hk : 0 < K) (hh : 0 < H) (h : H ≤ 3*K) :
    left K H ≠ 0 ∧ right K H ≠ 0 := nyman_witness_amplitudes K H hk hh h
example (K H : ℕ) (hk : 0 < K) (hh : 0 < H) (h : H ≤ 3*K) :
    err K H (6*K+2) = left K H / nymanFlatScale (6*K) H ∧ err K H (6*K+2) ≠ 0 :=
  nyman_witness_first_clip K H hk hh h
example (K H m : ℕ) (hk : 0 < K) (hl : 8*K ≤ m) (hr : m ≤ 9*K+2) :
    err K H m = K*left K H/nymanFlatScale (6*K) H := nyman_witness_clip_plateau K H m hk hl hr
example (K H : ℕ) (hk : 0 < K) : cost K H = ((K:ℝ)*(left K H/nymanFlatScale (6*K) H))^2 *
    (1/((8*K:ℕ):ℝ)-1/((9*K+3:ℕ):ℝ)) := nyman_witness_clip_energy K H hk
example (K H : ℕ) (hk : 0 < K) (hh : 0 < H) (h : H ≤ 3*K) :
    (K:ℝ)/72*(left K H/nymanFlatScale (6*K) H)^2 < cost K H := nyman_witness_clip_cost K H hk hh h

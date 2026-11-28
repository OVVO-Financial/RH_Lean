import Mathlib

/-! Exact native congruence module for the coupled depth graph.
This is the direct test of the rank-one separator in the upstream
Selmer denominator node, not a new conditional closure theorem. -/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace RHLean.Analysis.NativeDepthCongruence

/-- At a retained layer the two profiles, after removal of their common
prime power and possible coordinate swap, give (1,u) and (-u,1).
An integral operator separating those actual orthogonal lines has
an eigenvalue gap divisible by the congruence modulus. -/
theorem eigen_gap_dvd (u A B a b : ℤ)
    (ha : A+u*B=a) (hb : -u*A+B = -u*b) :
    1+u^2 ∣ a-b := by
  refine ⟨A-b, ?_⟩
  have h : B=u*(A-b) := by linarith only [hb]
  rw [← ha,h]
  ring

/-- The modulus is sharp, not just a necessary lower bound. -/
theorem eigen_gap_realizable (u a b : ℤ)
    (h : 1+u^2 ∣ a-b) :
    ∃ A B C : ℤ, A+u*B=a ∧ B+u*C=u*a ∧
      -u*A+B = -u*b ∧ -u*B+C=b := by
  obtain ⟨k,hk⟩ := h
  have ha : a = b+(1+u^2)*k := by linarith only [hk]
  refine ⟨b+k,u*k,b+u^2*k,?_,?_,?_,?_⟩ <;> try rw [ha] <;> ring

/-- Exact primitive tensor/Pluecker coordinates of the retained
coupled profile graph. A coordinate equal to one is present globally. -/
def coeff {I : Type*} [Fintype I] (u : I → ℕ) (x : I → Bool) : ℤ :=
  ∏ i, if x i then (u i:ℤ) else 1

def content {I : Type*} [Fintype I] (u : I → ℕ) : ℕ :=
  ∏ i, (1+(u i)^2)

@[simp] theorem coeff_zero {I : Type*} [Fintype I] (u : I → ℕ) :
    coeff u (fun _ => false) = 1 := by simp [coeff]

theorem content_pos {I : Type*} [Fintype I] (u : I → ℕ) : 0 < content u :=
  Finset.prod_pos fun i _ => by positivity

theorem coeff_normSq {I : Type*} [Fintype I] (u : I → ℕ) :
    (∑ x : I → Bool, coeff u x ^ 2) = (content u:ℤ) := by
  classical
  unfold coeff content
  rw [Nat.cast_prod]
  calc
    _ = ∑ x : I → Bool, ∏ i, (if x i then (u i:ℤ) else 1)^2 := by
      simp only [Finset.prod_pow]
    _ = ∏ i, ∑ t : Bool, (if t then (u i:ℤ) else 1)^2 := by rw [Fintype.prod_sum]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      simp [Fintype.sum_bool, add_comm]

/-- The actual orthogonal projection onto the exterior graph line. -/
def entry {I : Type*} [Fintype I] (u : I → ℕ) (x y : I → Bool) : ℚ :=
  (coeff u x:ℚ)*(coeff u y:ℚ)/(content u:ℚ)

theorem entry_pivot {I : Type*} [Fintype I] (u : I → ℕ) :
    entry u (fun _ => false) (fun _ => false) = 1/(content u:ℚ) := by
  simp [entry]

/-- Common class multiplier h and clearing M must pay the complete
exterior determinant. Taking an lcm of separate scalar line tests
does not replace this same-family determinant test. -/
theorem projector_clear_iff {I : Type*} [Fintype I] (u : I → ℕ) (h M : ℕ) :
    (∀ x y : I → Bool, ∃ z : ℤ, ((h*M:ℕ):ℚ)*entry u x y=z) ↔
      content u ∣ h*M := by
  have hn : (content u:ℚ) ≠ 0 := by exact_mod_cast (content_pos u).ne'
  constructor
  · intro hc
    obtain ⟨z,hz⟩ := hc (fun _ => false) (fun _ => false)
    rw [entry_pivot,mul_one_div] at hz
    have hz' : ((h*M:ℕ):ℚ) = (content u:ℚ)*z := by
      exact ((div_eq_iff hn).mp hz).trans (mul_comm _ _)
    have hi : ((content u:ℕ):ℤ) ∣ ((h*M:ℕ):ℤ) := by
      refine ⟨z,?_⟩
      exact_mod_cast hz'
    exact Int.natCast_dvd_natCast.mp hi
  · rintro ⟨k,hk⟩ x y
    refine ⟨(k:ℤ)*coeff u x*coeff u y,?_⟩
    rw [hk,entry]
    push_cast
    field_simp [hn] <;> ring

/-- Even allowing arbitrary mixed rational retractions of the
primitive exterior line, clearing the global coefficients and
paying their real size has this independent lower bound.
Here z is the cleared test, with exact common-table reading h. -/
theorem cleared_retraction_energy {I : Type*} [Fintype I] (u : I → ℕ)
    (z : (I → Bool) → ℤ) (h : ℕ) (hh : 0 < h)
    (hpair : ∑ x, z x*coeff u x = (h:ℤ)) :
    (content u:ℤ) ≤
      (∑ x : I → Bool, coeff u x^2)*(∑ x : I → Bool,z x^2) := by
  classical
  have hnz : ∃ x, z x ≠ 0 := by
    by_contra! h0
    have hz : (∑ x, z x*coeff u x) = 0 := by simp [h0]
    have hp : (0:ℤ) < h := by exact_mod_cast hh
    omega
  obtain ⟨x,hx⟩ := hnz
  have hsq : (1:ℤ) ≤ z x^2 := by
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · have hn : z x ≤ -1 := by omega
      nlinarith only [hn,sq_nonneg (z x+1)]
    · have hp : 1 ≤ z x := by omega
      nlinarith only [hp,sq_nonneg (z x-1)]
  have hs : (1:ℤ) ≤ ∑ x : I → Bool,z x^2 :=
    hsq.trans (Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ x))
  have hcontent : (0:ℤ) ≤ content u := by positivity
  rw [coeff_normSq]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hs hcontent

/-- The primitive integral retraction using the unit coefficient
attains the combined price (take h=1). -/
theorem unit_retraction {I : Type*} [Fintype I] [DecidableEq I] (u : I → ℕ) :
    let z : (I → Bool) → ℤ := fun x => if x=(fun _ => false) then 1 else 0
    (∑ x,z x*coeff u x)=1 ∧ (∑ x,z x^2)=1 := by
  classical
  intro z
  constructor <;> simp [z,ite_mul,ite_pow]

/-- Comparing the two swapped orthogonal projectors cancels their
off-diagonal NNS cross terms. The surviving signed probability is
(1-u²)/(1+u²), whose odd-prime denominator is still present. -/
theorem signed_swap_read (u : ℚ) :
    1/(1+u^2)-u^2/(1+u^2)=(1-u^2)/(1+u^2) := by
  rw [← sub_div]

theorem signed_swap_clearing (u a b : ℤ)
    (h : a*(1-u^2)=b*(1+u^2)) :
    1+u^2 ∣ 2*a := by
  refine ⟨a+b,?_⟩
  nlinarith only [h]

end RHLean.Analysis.NativeDepthCongruence

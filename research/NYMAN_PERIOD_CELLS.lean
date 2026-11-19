import «research.NYMAN_VARIANCE_REPAIR»
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic

/-! Complete-period first and second moments of the actual residue numerators. -/
set_option autoImplicit false
noncomputable section
open Finset
open scoped BigOperators
namespace RHLean.Analysis

/-- The unscaled centered numerator of the original Nyman residue. -/
def nymanCellFluct (k m : Nat) : Real := ((m % k : Nat) : Real) - ((k : Real)-1)/2

private theorem grid (a b : Nat) (f : Nat → Real) :
    ∑ i : Fin (a*b), f i.val = ∑ r : Fin b, ∑ q : Fin a, f (r.val+b*q.val) := by
  calc
    _ = ∑ x : Fin a × Fin b, f (finProdFinEquiv x).val :=
      (finProdFinEquiv.sum_comp (fun i : Fin (a*b) => f i.val)).symm
    _ = _ := by simp only [Fintype.sum_prod_type_right, finProdFinEquiv_apply_val]

private theorem firstMoment (n : Nat) :
    ∑ i : Fin n, (i.val : Real) = (n : Real)*(n-1)/2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i : Nat => (i : Real)) n]
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

private theorem secondMoment (n : Nat) :
    ∑ i : Fin n, (i.val : Real)^2 = (n : Real)*(n-1)*(2*n-1)/6 := by
  rw [Fin.sum_univ_eq_sum_range (fun i : Nat => (i : Real)^2) n]
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

private theorem centeredMoment (g : Nat) :
    ∑ r : Fin g, ((r.val : Real)-((g : Real)-1)/2)^2 =
      (g : Real)*((g : Real)^2-1)/12 := by
  let h := ((g : Real)-1)/2
  change (∑ r : Fin g, ((r.val : Real)-h)^2) = _
  simp_rw [show ∀ x : Real, (x-h)^2 = x^2-2*h*x+h^2 by intro x; ring]
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, firstMoment, secondMoment]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  dsimp [h]; ring

private theorem row (a g r : Nat) :
    ∑ u : Fin a, ((r : Real)+(g : Real)*u.val-((a : Real)*g-1)/2) =
      (a : Real)*((r : Real)-((g : Real)-1)/2) := by
  rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, firstMoment]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private theorem residuesCRT (a b : Nat) (ha : 0<a) (hb : 0<b) (co : a.Coprime b)
    (F G : Nat → Real) :
    ∑ q : Fin (a*b), F (q.val%a)*G (q.val%b) =
      (∑ i : Fin a, F i.val)*(∑ j : Fin b, G j.val) := by
  let e : Fin (a*b) → Fin a × Fin b := fun q =>
    (⟨q.val%a, Nat.mod_lt _ ha⟩, ⟨q.val%b, Nat.mod_lt _ hb⟩)
  have he : Function.Bijective e := by
    apply (Fintype.bijective_iff_injective_and_card e).2
    constructor
    · intro x y h
      apply Fin.ext
      have hx : Nat.ModEq a x.val y.val := congrArg (fun t : Fin a × Fin b => t.1.val) h
      have hy : Nat.ModEq b x.val y.val := congrArg (fun t : Fin a × Fin b => t.2.val) h
      have hh := (Nat.modEq_and_modEq_iff_modEq_mul co).1 ⟨hx, hy⟩
      change x.val%(a*b) = y.val%(a*b) at hh
      rwa [Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] at hh
    · simp
  calc
    _ = ∑ t : Fin a × Fin b, F t.1.val * G t.2.val :=
      he.sum_comp (fun t : Fin a × Fin b => F t.1.val * G t.2.val)
    _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_mul]; simp only [Finset.mul_sum]

private theorem rowCell (a g q r : Nat) (ha : 0<a) (hr : r<g) :
    nymanCellFluct (a*g) (r+g*q) =
      (r : Real) + (g : Real)*((q%a : Nat) : Real) - ((a : Real)*g-1)/2 := by
  have hm : Nat.ModEq (a*g) (r+g*q) (r+g*(q%a)) := by
    simpa only [Nat.mul_comm g q, Nat.mul_comm g (q%a)] using
      (((Nat.mod_modEq q a).symm.mul_right' g).add_left r)
  have hb : r+g*(q%a)<a*g := calc
    r+g*(q%a) < g+g*(q%a) := Nat.add_lt_add_right hr _
    _ = (q%a+1)*g := by ring
    _ ≤ a*g := Nat.mul_le_mul_right _ (Nat.mod_lt q ha)
  change (r+g*q)%(a*g) = (r+g*(q%a))%(a*g) at hm
  rw [Nat.mod_eq_of_lt hb] at hm
  simp only [nymanCellFluct, hm, Nat.cast_add, Nat.cast_mul]

private theorem basePair (a b g : Nat) (ha : 0<a) (hb : 0<b) (co : a.Coprime b) :
    (∑ m : Fin (a*b*g), nymanCellFluct (a*g) m.val * nymanCellFluct (b*g) m.val) =
      ((a*b*g : Nat) : Real)*((g : Real)^2-1)/12 := by
  rw [grid (a*b) g (fun m => nymanCellFluct (a*g) m * nymanCellFluct (b*g) m)]
  calc
    _ = ∑ r : Fin g, ((a : Real)*b)*((r.val : Real)-((g : Real)-1)/2)^2 := by
      apply sum_congr rfl
      intro r _
      simp_rw [rowCell a g _ r.val ha r.isLt, rowCell b g _ r.val hb r.isLt]
      calc
        _ = (∑ u : Fin a, ((r.val : Real)+(g : Real)*u.val-((a : Real)*g-1)/2))*
            (∑ v : Fin b, ((r.val : Real)+(g : Real)*v.val-((b : Real)*g-1)/2)) :=
          residuesCRT a b ha hb co
            (fun u => (r.val : Real)+(g : Real)*u-((a : Real)*g-1)/2)
            (fun v => (r.val : Real)+(g : Real)*v-((b : Real)*g-1)/2)
        _ = _ := by rw [row, row]; ring
    _ = _ := by rw [← mul_sum, centeredMoment]; push_cast; ring

private theorem repeatSum (n P : Nat) (f : Nat → Real)
    (h : ∀ r q : Nat, f (r+P*q) = f r) :
    ∑ i : Fin (n*P), f i.val = (n : Real)*∑ r : Fin P, f r.val := by
  rw [grid]; simp only [h, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_sum]

private theorem cellShift {k P : Nat} (hd : k ∣ P) (r q : Nat) :
    nymanCellFluct k (r+P*q) = nymanCellFluct k r := by
  obtain ⟨t, rfl⟩ := hd
  simp [nymanCellFluct, Nat.mul_assoc]

/-- Each centered residue has zero unweighted sum over every whole common period. -/
theorem nyman_period_cell_sum (P k : Nat) (hkP : k ∣ P) :
    ∑ m : Fin P, nymanCellFluct k m.val = 0 := by
  obtain ⟨t, rfl⟩ := hkP
  rw [Nat.mul_comm k t, repeatSum t k _ (cellShift (dvd_refl k))]
  have hz : (∑ m : Fin k, nymanCellFluct k m.val) = 0 := by
    have hh (m : Fin k) : nymanCellFluct k m.val = (m.val : Real)-((k : Real)-1)/2 := by
      rw [nymanCellFluct, Nat.mod_eq_of_lt m.isLt]
    simp only [hh, sum_sub_distrib, firstMoment, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]; ring
  rw [hz, mul_zero]

/-- Exact ordered pair sum, including shared divisors and diagonal pairs. -/
theorem nyman_period_cell_pair (P k l : Nat) (hk : 0<k) (hl : 0<l)
    (hkP : k ∣ P) (hlP : l ∣ P) :
    ∑ m : Fin P, nymanCellFluct k m.val * nymanCellFluct l m.val =
      (P : Real)*((Nat.gcd k l : Real)^2-1)/12 := by
  let g := Nat.gcd k l
  have hg : 0<g := Nat.gcd_pos_of_pos_left l hk
  obtain ⟨a,b,co,hk',hl'⟩ := Nat.exists_coprime k l
  change k = a*g at hk'
  change l = b*g at hl'
  have ha : 0<a := Nat.pos_of_ne_zero (fun hz => hk.ne' (hk'.trans (by rw [hz, Nat.zero_mul])))
  have hb : 0<b := Nat.pos_of_ne_zero (fun hz => hl.ne' (hl'.trans (by rw [hz, Nat.zero_mul])))
  let B := a*b*g
  have hB : 0<B := Nat.mul_pos (Nat.mul_pos ha hb) hg
  have hkB : k ∣ B := ⟨b, by change a*b*g=k*b; rw [hk']; ring⟩
  have hlB : l ∣ B := ⟨a, by change a*b*g=l*a; rw [hl']; ring⟩
  let f := fun m => nymanCellFluct k m * nymanCellFluct l m
  have repeats (t L : Nat) (hkL : k ∣ L) (hlL : l ∣ L) :
      ∑ m : Fin (t*L), f m.val = (t : Real)*∑ m : Fin L, f m.val :=
    repeatSum t L f (by intro r q; simp only [f, cellShift hkL, cellShift hlL])
  have hbase : ∑ m : Fin B, f m.val = (B : Real)*((g : Real)^2-1)/12 := by
    change (∑ m : Fin (a*b*g), nymanCellFluct k m.val*nymanCellFluct l m.val) = _
    rw [hk', hl']
    exact basePair a b g ha hb co
  have hx : (B : Real)*(∑ m : Fin P, f m.val) = (P : Real)*(∑ m : Fin B, f m.val) := calc
    _ = ∑ m : Fin (B*P), f m.val := (repeats B P hkP hlP).symm
    _ = ∑ m : Fin (P*B), f m.val := by rw [Nat.mul_comm B P]
    _ = _ := repeats P B hkB hlB
  change (∑ m : Fin P, f m.val) = (P : Real)*((g : Real)^2-1)/12
  apply mul_left_cancel₀ (show (B : Real) ≠ 0 by exact_mod_cast hB.ne')
  rw [hx, hbase]; ring

end RHLean.Analysis

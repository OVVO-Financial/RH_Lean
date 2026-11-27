import «research.NativeMeasuredSlotProjector»
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.RingTheory.RootsOfUnity.Lemmas

/-! Differences at the distinct residue displacements of one admitted prime.
The cyclic calculation applies on complete fibres of actual integer slots. -/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace RHLean.Analysis.AlpogeThin.SlotProjector

/-- Difference along one displacement within a single prime-wheel fibre. -/
def wheelDiff {p : ℕ} {R : Type*} [AddGroup R] (a : ZMod p) (f : ZMod p → R) :
    ZMod p → R := fun u => f u - f (u+a)

theorem wheelDiff_comm {p : ℕ} (a b : ZMod p) (f : ZMod p → ℤ) :
    wheelDiff a (wheelDiff b f) = wheelDiff b (wheelDiff a f) := by
  funext u
  simp only [wheelDiff, add_assoc, add_comm a b]
  abel

/-- Apply each of the displacements 1 through m exactly once in this fibre. -/
def wheelSweep {p : ℕ} {R : Type*} [AddGroup R] (f : ZMod p → R) : ℕ → ZMod p → R
  | 0 => f
  | m+1 => wheelDiff ((m+1 : ℕ) : ZMod p) (wheelSweep f m)

private theorem wheel_dft_shift {p : ℕ} [NeZero p] (f : ZMod p → ℂ) (a k : ZMod p) :
    ZMod.dft (fun j => f (j+a)) k = ZMod.stdAddChar (a*k) * ZMod.dft f k := by
  simp only [ZMod.dft_apply, smul_eq_mul, Finset.mul_sum, ← mul_assoc]
  refine Fintype.sum_equiv (Equiv.addRight a) _ _ fun j => ?_
  change ZMod.stdAddChar (-(j*k)) * f (j+a) =
    (ZMod.stdAddChar (a*k) * ZMod.stdAddChar (-((j+a)*k))) * f (j+a)
  rw [← AddChar.map_add_eq_mul, show a*k + -((j+a)*k) = -(j*k) by ring]

private theorem wheel_spectrum {p : ℕ} [NeZero p] (f : ZMod p → ℂ) (k : ZMod p) (m : ℕ) :
    ZMod.dft (wheelSweep f m) k =
      (∏ j ∈ Finset.range m, (1 - ZMod.stdAddChar k^(j+1))) * ZMod.dft f k := by
  induction m with
  | zero => simp [wheelSweep]
  | succ m ih =>
    let h := wheelSweep f m
    change ZMod.dft (h - fun j => h (j+((m+1 : ℕ) : ZMod p))) k = _
    rw [map_sub, Pi.sub_apply, wheel_dft_shift, Finset.prod_range_succ]
    rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
    change ZMod.dft (wheelSweep f m) k - _ * ZMod.dft (wheelSweep f m) k = _
    rw [ih]
    ring

private theorem wheel_complex (m : ℕ) (hp : (m+1).Prime) (f : ZMod (m+1) → ℂ) :
    wheelSweep f m = fun j => ((m+1:ℕ):ℂ)*f j - ∑ i, f i := by
  apply ZMod.dft.injective
  funext k
  change ZMod.dft (wheelSweep f m) k =
    ZMod.dft ((fun j => ((m+1:ℕ):ℂ)*f j) - fun _ => ∑ i, f i) k
  rw [map_sub, Pi.sub_apply, ZMod.dft_const_mul]
  by_cases hk : k = 0
  · subst k
    have hm : 0 < m := by have := hp.two_le; omega
    have prod0 : (∏ j ∈ Finset.range m, (1 - ZMod.stdAddChar (0 : ZMod (m+1))^(j+1))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.mpr hm : 0 ∈ Finset.range m) (by simp)
    rw [wheel_spectrum, prod0, zero_mul, ZMod.dft_apply_zero, ZMod.dft_apply_zero]
    simp [ZMod.card]
  · have hne : ZMod.stdAddChar k ≠ 1 := fun h => hk <| ZMod.injective_stdAddChar
        (h.trans (AddChar.map_zero_eq_one _).symm)
    have root : IsPrimitiveRoot (ZMod.stdAddChar k) (m+1) := by
      apply isPrimitiveRoot_of_mem_nthRootsFinset hp _ hne
      rw [mem_nthRootsFinset hp.pos, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul,
        ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]
    let C : ZMod (m+1) → ℂ := fun _ => ∑ i, f i
    have hs : ZMod.dft C k = ZMod.stdAddChar k * ZMod.dft C k := by
      simpa only [one_mul] using wheel_dft_shift C 1 k
    have hz : ZMod.dft C k = 0 := by
      rcases mul_eq_zero.mp (show (1-ZMod.stdAddChar k)*ZMod.dft C k = 0 by
        linear_combination hs) with h | h
      · exact (hne (sub_eq_zero.mp h).symm).elim
      · exact h
    rw [wheel_spectrum, root.prod_one_sub_pow_eq_order, hz, sub_zero, Nat.cast_add, Nat.cast_one]

private theorem wheel_cast {p : ℕ} (f : ZMod p → ℤ) (m : ℕ) (j : ZMod p) :
    (wheelSweep f m j : ℂ) = wheelSweep (fun u => (f u : ℂ)) m j := by
  induction m generalizing j with
  | zero => rfl
  | succ m ih => simp only [wheelSweep, wheelDiff, Int.cast_sub, ih]

/-- All p-1 different residue displacements at the admitted prime. In particular
a fibre with r occupied seats in an indicator cut has every output congruent
to -r modulo p, including the fibres meeting a clipping boundary. -/
theorem wheelSweep_eq (m : ℕ) (hp : (m+1).Prime) (f : ZMod (m+1) → ℤ) (j : ZMod (m+1)) :
    wheelSweep f m j = (m+1 : ℕ)*f j - ∑ u, f u := by
  have hc := (wheel_cast f m j).trans (congrFun (wheel_complex m hp (fun u => (f u : ℂ))) j)
  exact_mod_cast hc

/-- On the actual quotient slots in one full p-cycle, the result for an
indicator is divisible by p exactly when the number of occupied seats is.
The incomplete arithmetic cut stays visible in every output coordinate. -/
theorem wheelSweep_cut (m : ℕ) (hp : (m+1).Prime) (U : Finset (ZMod (m+1))) (j : ZMod (m+1)) :
    ((m+1:ℕ):ℤ) ∣ wheelSweep (fun t => if t ∈ U then (1:ℤ) else 0) m j ↔ m+1 ∣ U.card := by
  rw [wheelSweep_eq m hp]
  simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [dvd_sub_right (dvd_mul_right _ _)]
  exact Int.natCast_dvd_natCast

/-- The actual star columns on a complete wheel fibre inside a measured layer
are constant. The distinct residue differences therefore yield zero on them. -/
theorem wheelSweep_layer {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D : Fin (r+1) → ℕ)
    (m : ℕ) (hp : (m+1).Prime) (base stride : ℕ) (i : Fin (r+1)) (j : Fin r)
    (inside : ∀ t : ZMod (m+1), base + stride*t.val ∈ S i) (t : ZMod (m+1)) :
    wheelSweep (fun u : ZMod (m+1) =>
      columns S D ⟨i, ⟨base + stride*u.val, inside u⟩⟩ j) m t = 0 := by
  rw [wheelSweep_eq m hp]
  simp [columns, starColumn, ZMod.card, nsmul_eq_mul]

end RHLean.Analysis.AlpogeThin.SlotProjector

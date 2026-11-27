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
    rw [wheel_spectrum, prod0, zero_mul]
    simp only [ZMod.dft_apply_zero, Finset.sum_const,
      Finset.card_univ, ZMod.card, nsmul_eq_mul, sub_self]
  · have hne : ZMod.stdAddChar k ≠ 1 := fun h => hk <| ZMod.injective_stdAddChar
        (h.trans (AddChar.map_zero_eq_one _).symm)
    have root : IsPrimitiveRoot (ZMod.stdAddChar k) (m+1) := by
      apply isPrimitiveRoot_of_mem_nthRootsFinset hp _ hne
      rw [Polynomial.mem_nthRootsFinset hp.pos, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul,
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
    ((wheelSweep f m j : ℤ) : ℂ) = wheelSweep (fun u => (f u : ℂ)) m j := by
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

/-- The single residue that obstructs simultaneous divisibility on a full fibre. -/
def wheelFibreSum (p : ℕ) [NeZero p] : (ZMod p → ℤ) →+ ZMod p where
  toFun f := ((∑ i, f i : ℤ) : ZMod p)
  map_zero' := by simp
  map_add' f g := by simp [Finset.sum_add_distrib]

/-- On one common integral lattice, one index-p restriction makes all p output
coordinates divisible. The image is exactly p times the whole mean-zero lattice.
The constant vector is a single exceptional generator for the ambient inclusion. -/
theorem wheel_joint_recovery (m : ℕ) (hp : (m+1).Prime) :
    let P := wheelFibreSum (m+1)
    let d := ((m+1:ℕ):ℤ)
    P.ker.index = m+1 ∧
    (∀ f, (∀ j, d ∣ wheelSweep f m j) ↔ f ∈ P.ker) ∧
    (∀ w : ZMod (m+1) → ℤ, (∃ f ∈ P.ker, wheelSweep f m = w) ↔
      ∃ z : ZMod (m+1) → ℤ, (∑ j, z j) = 0 ∧ w = fun j => d*z j) ∧
    (∀ f : ZMod (m+1) → ℤ, ∃ a : ℤ, ∀ j, d*f j = wheelSweep f m j + a) := by
  classical
  intro P d
  have mem (f : ZMod (m+1) → ℤ) : f ∈ P.ker ↔ d ∣ ∑ j, f j := by
    change ((∑ j, f j : ℤ) : ZMod (m+1)) = 0 ↔ ((m+1:ℕ):ℤ) ∣ ∑ j, f j
    exact ZMod.intCast_zmod_eq_zero_iff_dvd (∑ j, f j) (m+1)
  have onto : Function.Surjective P := by
    intro y
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective y
    exact ⟨fun i => if i = 0 then a else 0, by simpa [P, wheelFibreSum] using ha⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [AddSubgroup.index_ker, P.range_eq_top_of_surjective onto, AddSubgroup.card_top,
      Nat.card_eq_fintype_card, ZMod.card]
  · intro f
    rw [mem]
    have atSeat j : d ∣ wheelSweep f m j ↔ d ∣ ∑ i, f i := by
      rw [wheelSweep_eq m hp, dvd_sub_right (dvd_mul_right _ _)]
    exact ⟨fun h => (atSeat 0).1 (h 0), fun h j => (atSeat j).2 h⟩
  · intro w
    constructor
    · rintro ⟨f, hf, rfl⟩
      obtain ⟨a, ha⟩ := (mem f).1 hf
      refine ⟨fun i => f i - a, ?_, funext fun j => ?_⟩
      · simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          ZMod.card, nsmul_eq_mul, ha, d, sub_self]
      · rw [wheelSweep_eq m hp, ha, mul_sub]
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z, (mem z).2 (hz ▸ dvd_zero d), funext fun j => by rw [wheelSweep_eq m hp, hz, sub_zero]⟩
  · intro f
    exact ⟨∑ i, f i, fun j => by rw [wheelSweep_eq m hp, sub_add_cancel]⟩

/-- On the actual quotient slots in one full p-cycle, the result for an
indicator is divisible by p exactly when the number of occupied seats is.
The incomplete arithmetic cut stays visible in every output coordinate. -/
theorem wheelSweep_cut (m : ℕ) (hp : (m+1).Prime) (U : Finset (ZMod (m+1))) (j : ZMod (m+1)) :
    ((m+1:ℕ):ℤ) ∣ wheelSweep (fun t => if t ∈ U then (1:ℤ) else 0) m j ↔ m+1 ∣ U.card := by
  rw [wheelSweep_eq m hp]
  simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [dvd_sub_right (dvd_mul_right _ _)]
  exact Int.natCast_dvd_natCast

/-- A fibre crossing one genuine layer interface. Every output is divisible at
the admitted prime precisely when the two adjacent integral readings agree there. -/
theorem wheelSweep_jump (m : ℕ) (hp : (m+1).Prime) (U : Finset (ZMod (m+1)))
    (hlo : 0 < U.card) (hhi : U.card < m+1) (a b : ℤ) (j : ZMod (m+1)) :
    ((m+1:ℕ):ℤ) ∣ wheelSweep (fun i => if i ∈ U then a else b) m j ↔
      ((m+1:ℕ):ℤ) ∣ a-b := by
  have mass : (∑ i : ZMod (m+1), if i ∈ U then a else b) =
      (U.card:ℤ)*(a-b) + ((m+1:ℕ):ℤ)*b := by
    calc
      _ = ∑ i : ZMod (m+1), ((if i ∈ U then (1:ℤ) else 0)*(a-b) + b) :=
        Finset.sum_congr rfl fun i _ => by by_cases h : i ∈ U <;> simp [h]
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_boole]
        simp [ZMod.card]
  have hunit : ¬ ((m+1:ℕ):ℤ) ∣ (U.card:ℤ) :=
    fun h => hhi.not_ge (Nat.le_of_dvd hlo (Int.natCast_dvd_natCast.mp h))
  rw [wheelSweep_eq m hp, dvd_sub_right (dvd_mul_right _ _), mass,
    dvd_add_left (dvd_mul_right _ _), (Nat.prime_iff_prime_int.mp hp).dvd_mul,
    or_iff_right hunit]

/-- The actual star columns on a complete wheel fibre inside a measured layer
are constant. The distinct residue differences therefore yield zero on them. -/
theorem wheelSweep_layer {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D : Fin (r+1) → ℕ)
    (m : ℕ) (hp : (m+1).Prime) (base stride : ℕ) (i : Fin (r+1)) (j : Fin r)
    (inside : ∀ t : ZMod (m+1), base + stride*t.val ∈ S i) (t : ZMod (m+1)) :
    wheelSweep (fun u : ZMod (m+1) =>
      columns S D ⟨i, ⟨base + stride*u.val, inside u⟩⟩ j) m t = 0 := by
  rw [wheelSweep_eq m hp]
  let v := starColumn D j i 0
  change ((m+1:ℕ):ℤ)*v - (∑ _u : ZMod (m+1), v) = 0
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, sub_self]

/-- Layer amplitude of the original integral star sections, reduced at p. -/
private def levelValue {r p : ℕ} (D : Fin (r+1) → ℕ) (z : Fin r → ZMod p)
    (i : Fin (r+1)) : ZMod p :=
  ∑ j, (starColumn D j i 0 : ZMod p)*z j

/-- Require the residue jump to vanish on precisely the chosen boundaries,
using one integer coefficient vector for the actual star sections at all cuts. -/
def starJump {r : ℕ} (D : Fin (r+1) → ℕ) (p : ℕ) (edges : Finset (Fin r)) :
    (Fin r → ℤ) →+ (↥edges → ZMod p) where
  toFun z e := levelValue D (fun j => (z j : ZMod p)) e.val.succ -
    levelValue D (fun j => (z j : ZMod p)) e.val.castSucc
  map_zero' := by funext e; simp [levelValue]
  map_add' v w := by
    funext e
    simp only [Pi.add_apply, Int.cast_add, levelValue, mul_add, Finset.sum_add_distrib]
    abel

private theorem levelValue_sumZero {r p : ℕ} (D : Fin (r+1) → ℕ) (U : Fin (r+1) → ZMod p)
    (hs : ∑ i, U i = 0) (i : Fin (r+1)) :
    levelValue D (fun j => U j.succ) i = (D i : ZMod p)*U i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Fin.sum_univ_succ] at hs
    have h0 : U 0 = -(∑ j : Fin r, U j.succ) := eq_neg_of_add_eq_zero_left hs
    have coeff (j : Fin r) : (starColumn D j 0 0 : ZMod p) = -(D 0 : ZMod p) := by
      simp [starColumn, (Fin.succ_ne_zero j).symm]
    calc
      _ = -(D 0 : ZMod p) * ∑ j : Fin r, U j.succ := by simp only [levelValue, coeff, Finset.mul_sum]
      _ = _ := by rw [h0, neg_mul, mul_neg]
  · simp [levelValue, starColumn, Fin.succ_ne_zero, ite_mul]

private theorem star_shift_onto {r p : ℕ} [Fact p.Prime] (D : Fin (r+1) → ℕ)
    (a : Fin (r+1)) (ha : (D a : ZMod p) = 0) (others : ∀ i, i ≠ a → (D i : ZMod p) ≠ 0)
    (t : Fin (r+1) → ZMod p) : ∃ z : Fin r → ZMod p, ∀ i, levelValue D z i = t i - t a := by
  classical
  let v := fun i => (t i - t a)/(D i : ZMod p)
  let U := fun i => v i - if i = a then ∑ l, v l else 0
  have hU : ∑ i, U i = 0 := by simp [U, Finset.sum_sub_distrib]
  refine ⟨fun j => U j.succ, fun i => ?_⟩
  rw [levelValue_sumZero D U hU]
  by_cases h : i = a
  · subst i
    rw [ha, zero_mul, sub_self]
  · change (D i : ZMod p)*((t i-t a)/(D i : ZMod p) - (if i = a then ∑ l, v l else 0)) = _
    rw [ite_eq_right h, sub_zero, mul_comm, div_mul_cancel₀ _ (others i h)]

/-- Each separated, unaligned interior edge costs exactly one factor of the
admitted prime on the genuine star coefficient lattice, even jointly. A wheel
power divisible by p at its own layer fixes the otherwise free common shift. -/
theorem starJump_index {r : ℕ} (prime : Fin (r+1) → ℕ) (hp : ∀ i, (prime i).Prime)
    (inj : Function.Injective prime) (depth : Fin (r+1) → ℕ) (a : Fin (r+1)) (hd : 0 < depth a)
    (edges : Finset (Fin r)) :
    (starJump (fun i => prime i ^ depth i) (prime a) edges).ker.index = prime a ^ edges.card := by
  classical
  let p := prime a
  let _ : Fact p.Prime := ⟨hp a⟩
  let D := fun i => prime i ^ depth i
  let F := starJump D p edges
  have ha : (D a : ZMod p) = 0 := by
    change ((p^depth a:ℕ):ZMod p) = 0
    rw [Nat.cast_pow, ZMod.natCast_self, zero_pow hd.ne']
  have others (i) (h : i ≠ a) : (D i : ZMod p) ≠ 0 := by
    change (((prime i)^depth i : ℕ) : ZMod p) ≠ 0
    rw [Nat.cast_pow]
    apply pow_ne_zero
    intro hz
    have hdvd : prime a ∣ prime i := (ZMod.natCast_eq_zero_iff _ _).mp hz
    exact h (inj ((Nat.prime_dvd_prime_iff_eq (hp a) (hp i)).mp hdvd).symm)
  have onto : Function.Surjective F := by
    intro y
    let step (i : ℕ) := if hi : i < r then
      if hh : (⟨i,hi⟩ : Fin r) ∈ edges then y ⟨⟨i,hi⟩,hh⟩ else 0 else 0
    let t := fun i : Fin (r+1) => ∑ j ∈ Finset.range i.val, step j
    obtain ⟨z, hz⟩ := star_shift_onto D a ha others t
    choose v hv using fun i => ZMod.intCast_surjective (z i)
    refine ⟨v, funext fun e => ?_⟩
    change levelValue D (fun i => (v i : ZMod p)) e.val.succ -
      levelValue D (fun i => (v i : ZMod p)) e.val.castSucc = _
    rw [funext hv, hz, hz, sub_sub_sub_cancel_right]
    change (∑ j ∈ Finset.range (e.val.val+1), step j) - (∑ j ∈ Finset.range e.val.val, step j) = _
    rw [Finset.sum_range_succ, add_sub_cancel_left]
    simp [step, e.val.isLt, e.property]
  change F.ker.index = _
  rw [AddSubgroup.index_ker, F.range_eq_top_of_surjective onto, AddSubgroup.card_top]
  simp [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, p]

end RHLean.Analysis.AlpogeThin.SlotProjector

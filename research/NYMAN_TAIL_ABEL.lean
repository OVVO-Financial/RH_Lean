import «research.NYMAN_PERIOD_MEAN»

/-! Abel comparison for the original infinite, location-weighted Nyman tail. -/
set_option autoImplicit false
noncomputable section
open Finset Filter
open scoped BigOperators Topology
namespace RHLean.Analysis

/-- The tail includes the cutoff itself. No finite last output is imposed. -/
def nymanPhysicalTail (N : Nat) (c : Nat → ℝ) (s : Nat) : ℝ :=
  ∑' n : Nat, nymanWeight (s+n) * nymanResidual N c (s+n)^2

/-- The stationary energy includes the bias even outside the two-moment family. -/
def nymanPeriodLevel (N : Nat) (c : Nat → ℝ) : ℝ :=
  nymanPeriodBias N c ^ 2 + nymanCovariance N c

/-- Signed discrepancy strictly before the supplied output. -/
def nymanCutoffPrimitive (N : Nat) (c : Nat → ℝ) (t : Nat) : ℝ :=
  ∑ i ∈ range t, (nymanResidual N c i ^ 2 - nymanPeriodLevel N c)

theorem nyman_cutoff_primitive_periodic (N P : Nat) (c : Nat → ℝ)
    (hp : ∀ k ∈ Icc 2 N, k ∣ P) : Function.Periodic (nymanCutoffPrimitive N c) P := by
  have hr (m : Nat) : nymanResidual N c (m+P) = nymanResidual N c m := by
    unfold nymanResidual
    congr 1
    apply sum_congr rfl; intro k hk
    have he : (m+P)%k = m%k := by rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd (hp k hk)]; simp
    simp only [nymanResidue, he]
  have he := nyman_period_residual_energy N P c hp
  rw [Fin.sum_univ_eq_sum_range (fun i => nymanResidual N c i ^ 2) P] at he
  intro n
  induction n with
  | zero => simp [nymanCutoffPrimitive, sum_sub_distrib, nsmul_eq_mul, he, nymanPeriodLevel]
  | succ n ih =>
    rw [show n+1+P = (n+P)+1 by omega]
    unfold nymanCutoffPrimitive at ih ⊢
    rw [sum_range_succ, sum_range_succ, ih, hr]

private theorem weight_mass (s : Nat) (hs : 0<s) :
    HasSum (fun n : Nat => nymanWeight (s+n)) (1/(s:ℝ)) := by
  have partials (n : Nat) : ∑ i ∈ range n, nymanWeight (s+i) =
      1/(s:ℝ)-1/((s+n:Nat):ℝ) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih, Nat.add_succ, Nat.cast_succ]
      have hp : 0 < ((s+n:Nat):ℝ) := by exact_mod_cast (show 0<s+n by omega)
      unfold nymanWeight
      field_simp <;> ring
  have ht : Tendsto (fun n : Nat => s+n) atTop atTop := by
    apply tendsto_atTop.2; intro b; filter_upwards [eventually_ge_atTop b] with n hn; dsimp; omega
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => nymanWeight_nonneg (s+n)) _).2
  simp_rw [partials]
  simpa only [sub_zero] using (tendsto_const_nhds (x := 1/(s:ℝ))).sub
    ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp ht)

private theorem bounded_abel (w u D : Nat → ℝ) (A M C : ℝ)
    (hw : HasSum w M) (hw0 : ∀ n, 0 ≤ w n) (hD : ∀ n, |D n| ≤ C)
    (h0 : D 0 = 0) (hd : ∀ n, D (n+1)-D n = u n-A) :
    HasSum (fun n => (w n-w (n+1))*D (n+1)) ((∑' n, w n*u n)-M*A) := by
  let a := fun n => w n*D n
  let b := fun n => w n*D (n+1)
  have bound (f : Nat → ℝ) (hf : ∀ n, |f n| ≤ C) : Summable (fun n => w n*f n) := by
    apply (hw.summable.mul_right C).of_norm_bounded
    intro n; rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 n)]
    exact mul_le_mul_of_nonneg_left (hf n) (hw0 n)
  have ha : Summable a := bound D hD
  have hb : Summable b := bound _ (fun n => hD (n+1))
  have ha0 : a 0 = 0 := by simp [a, h0]
  have hshift : HasSum (fun n => a (n+1)) (∑' n, a n) := by
    have he : (∑' n, a n) = ∑' n, a (n+1) := by simpa only [ha0, zero_add] using ha.tsum_eq_zero_add
    rw [he]; exact ((summable_nat_add_iff 1).2 ha).hasSum
  have hu : HasSum (fun n => w n*u n) ((∑' n, b n)-(∑' n, a n)+M*A) := by
    convert (hb.hasSum.sub ha.hasSum).add (hw.mul_right A) using 1
    funext n; dsimp [a,b]; rw [show u n = D (n+1)-D n+A by linarith [hd n]]; ring
  rw [hu.tsum_eq, add_sub_cancel_right]
  convert hb.hasSum.sub hshift using 1
  funext n; dsimp [a,b]; ring

/-- The complete physical error is a positive-weight sum of signed primitive differences. -/
theorem nyman_tail_abel (N P s : Nat) (c : Nat → ℝ) (hP : 0<P) (hs : 0<s)
    (hp : ∀ k ∈ Icc 2 N, k ∣ P) :
    HasSum (fun n : Nat => (nymanWeight (s+n)-nymanWeight (s+n+1))*
      (nymanCutoffPrimitive N c (s+n+1)-nymanCutoffPrimitive N c s))
      (nymanPhysicalTail N c s - nymanPeriodLevel N c / (s:ℝ)) := by
  let F := nymanCutoffPrimitive N c
  have hper : Function.Periodic F P := nyman_cutoff_primitive_periodic N P c hp
  let C : ℝ := ∑ i ∈ range P, |F i-F s|
  have hb (n : Nat) : |F (s+n)-F s| ≤ C := by
    rw [← hper.map_mod_nat (s+n)]
    exact single_le_sum (f := fun i => |F i-F s|) (fun i _ => abs_nonneg _) (mem_range.mpr (Nat.mod_lt _ hP))
  have hd (n : Nat) : (F (s+(n+1))-F s)-(F (s+n)-F s) =
      nymanResidual N c (s+n)^2 - nymanPeriodLevel N c := by
    simp only [F, nymanCutoffPrimitive, ← Nat.add_assoc, sum_range_succ]; ring
  have h := bounded_abel (fun n => nymanWeight (s+n)) (fun n => nymanResidual N c (s+n)^2)
    (fun n => F (s+n)-F s) _ _ C (weight_mass s hs) (fun n => nymanWeight_nonneg _) hb (by simp) hd
  simpa only [Nat.add_assoc, nymanPhysicalTail, F, one_div, div_eq_mul_inv, mul_comm (s:ℝ)⁻¹] using h

end RHLean.Analysis

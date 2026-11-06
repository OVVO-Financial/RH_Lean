import «research.NYMAN_FLAT_TAPER_RETURN_20261104»

/-!
The finite obstruction in 20261106-analytic-2/RM5, independently accepted
by 20261106-referee-7. The original residues and complete squared residual
are retained. Fixed early cells and both moments do not uniformly control
later energy over unrestricted high corrections. This does not refute a
bound for the specified two-band FAMILY, an optimized norm, or NYMAN.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace RHLean.Analysis

def nymanMomentNullDirection (k : Nat) : Real :=
  if k = 7 then 7 else if k = 8 then -16 else if k = 9 then 9 else 0

def nymanNullPerturb (h : Nat -> Real) (t : Real) (k : Nat) : Real :=
  h k + t * nymanMomentNullDirection k

private theorem nyman_null_sum (f : Nat -> Real) :
    Finset.sum (Icc 2 12) (fun k => nymanMomentNullDirection k * f k) =
      7 * f 7 - 16 * f 8 + 9 * f 9 := by
  norm_num [Finset.sum_Icc_succ_top, nymanMomentNullDirection]
  <;> ring

theorem nyman_null_perturb_off_support (h : Nat -> Real) (t : Real)
    (k : Nat) (hk : k <= 6 ∨ 12 < k) : nymanNullPerturb h t k = h k := by
  have h7 : k ≠ 7 := by omega
  have h8 : k ≠ 8 := by omega
  have h9 : k ≠ 9 := by omega
  simp [nymanNullPerturb, nymanMomentNullDirection, h7, h8, h9]

theorem nyman_null_perturb_moments (h : Nat -> Real) (t : Real) :
    (Finset.sum (Icc 2 12) (nymanNullPerturb h t) =
      Finset.sum (Icc 2 12) h) ∧
    nymanCorrectionMoment 12 (nymanNullPerturb h t) =
      nymanCorrectionMoment 12 h := by
  constructor <;>
    norm_num [nymanNullPerturb, nymanMomentNullDirection,
      nymanCorrectionMoment, Finset.sum_Icc_succ_top] <;> ring

theorem nyman_null_perturb_mean (c : Nat -> Real) (t : Real) :
    Finset.sum (Icc 2 12) (fun k =>
      nymanNullPerturb c t k * (((k : Real) - 1) / (2 * k))) =
    Finset.sum (Icc 2 12) (fun k => c k * (((k : Real) - 1) / (2 * k))) := by
  norm_num [nymanNullPerturb, nymanMomentNullDirection, Finset.sum_Icc_succ_top]
  <;> ring

theorem nyman_null_residual (c : Nat -> Real) (t : Real) (m : Nat) :
    nymanResidual 12 (nymanNullPerturb c t) m = nymanResidual 12 c m -
      t * (7 * nymanResidue 7 m - 16 * nymanResidue 8 m +
        9 * nymanResidue 9 m) := by
  unfold nymanResidual nymanNullPerturb
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, <- Finset.mul_sum]
  rw [nyman_null_sum]
  ring

theorem nyman_null_residual_early (c : Nat -> Real) (t : Real)
    (m : Nat) (hm : m <= 6) :
    nymanResidual 12 (nymanNullPerturb c t) m = nymanResidual 12 c m := by
  rw [nyman_null_residual]
  have h7 : m < 7 := by omega
  have h8 : m < 8 := by omega
  have h9 : m < 9 := by omega
  simp only [nymanResidue, Nat.mod_eq_of_lt h7, Nat.mod_eq_of_lt h8,
    Nat.mod_eq_of_lt h9, Nat.cast_ofNat]
  ring

theorem nyman_null_residual_seven (c : Nat -> Real) (t : Real) :
    nymanResidual 12 (nymanNullPerturb c t) 7 = nymanResidual 12 c 7 + 7 * t := by
  rw [nyman_null_residual]
  norm_num [nymanResidue]
  <;> ring

/-- One genuine nonnegative cell already prevents a uniform later-energy bound. -/
theorem nyman_null_finite_energy_unbounded (c : Nat -> Real)
    (T : Nat) (hT : 7 <= T) (B : Real) :
    ∃ t : Real, B < Finset.sum (Icc 1 T) (fun m =>
      nymanResidual 12 (nymanNullPerturb c t) m ^ 2 /
        ((m : Real) * (m + 1))) := by
  let t : Real := (56 * (|B| + 1) - nymanResidual 12 c 7) / 7
  have he : nymanResidual 12 (nymanNullPerturb c t) 7 = 56 * (|B| + 1) := by
    rw [nyman_null_residual_seven]
    dsimp only [t]
    ring
  have hcell : nymanResidual 12 (nymanNullPerturb c t) 7 ^ 2 / 56 <=
      Finset.sum (Icc 1 T) (fun m =>
        nymanResidual 12 (nymanNullPerturb c t) m ^ 2 /
          ((m : Real) * (m + 1))) := by
    simpa using (Finset.single_le_sum
      (f := fun m : Nat => nymanResidual 12 (nymanNullPerturb c t) m ^ 2 /
        ((m : Real) * (m + 1)))
      (fun m _ => div_nonneg (sq_nonneg _) (by positivity))
      (show 7 ∈ Icc 1 T from Finset.mem_Icc.mpr ⟨by omega, hT⟩))
  have hbig : B < (56 * (|B| + 1)) ^ 2 / 56 := by
    have habs := abs_nonneg B
    have hB := le_abs_self B
    nlinarith [sq_nonneg (|B|)]
  exact ⟨t, hbig.trans_le (by simpa only [he] using hcell)⟩

theorem nyman_flat_null_perturb (H : Nat) (hH : 1 <= H) (hHN : H < 12)
    (h : Nat -> Real) (t : Real) :
    nymanFlatCoefficient 12 H (nymanNullPerturb h (t * nymanFlatScale 12 H)) =
      nymanNullPerturb (nymanFlatCoefficient 12 H h) t := by
  have hs := ne_of_gt (nymanFlatScale_pos 12 H hH hHN)
  funext k
  unfold nymanFlatCoefficient nymanNullPerturb
  field_simp [hs]
  <;> ring

/-- Original flat coefficients, with the complete early residual and both
moments fixed, admit arbitrarily large complete finite energy after admission. -/
theorem nyman_flat_null_obstruction (H : Nat) (hH : 1 <= H) (hHN : H < 12)
    (h : Nat -> Real) (B : Real) :
    ∃ g : Nat -> Real,
      (∀ k, k <= 6 ∨ 12 < k -> g k = h k) ∧
      nymanCorrectionMoment 12 g = nymanCorrectionMoment 12 h ∧
      Finset.sum (Icc 2 12) g = Finset.sum (Icc 2 12) h ∧
      (Finset.sum (Icc 2 12) (fun k =>
        nymanFlatCoefficient 12 H g k * (((k : Real) - 1) / (2 * k))) =
       Finset.sum (Icc 2 12) (fun k =>
        nymanFlatCoefficient 12 H h k * (((k : Real) - 1) / (2 * k)))) ∧
      (∀ m, m <= 6 -> nymanResidual 12 (nymanFlatCoefficient 12 H g) m =
        nymanResidual 12 (nymanFlatCoefficient 12 H h) m) ∧
      B < Finset.sum (Icc 1 7) (fun m =>
        nymanResidual 12 (nymanFlatCoefficient 12 H g) m ^ 2 /
          ((m : Real) * (m + 1))) := by
  obtain ⟨t, ht⟩ := nyman_null_finite_energy_unbounded
    (nymanFlatCoefficient 12 H h) 7 (by omega) B
  let g := nymanNullPerturb h (t * nymanFlatScale 12 H)
  have hg : nymanFlatCoefficient 12 H g =
      nymanNullPerturb (nymanFlatCoefficient 12 H h) t :=
    nyman_flat_null_perturb H hH hHN h t
  have hm := nyman_null_perturb_moments h (t * nymanFlatScale 12 H)
  refine ⟨g, ?_, hm.2, hm.1, ?_, ?_, ?_⟩
  · exact fun k hk => nyman_null_perturb_off_support h _ k hk
  · rw [hg]
    exact nyman_null_perturb_mean _ t
  · intro m hm6
    rw [hg]
    exact nyman_null_residual_early _ t m hm6
  · rwa [hg]

#check nyman_null_perturb_off_support
#check nyman_null_perturb_moments
#check nyman_null_perturb_mean
#check nyman_null_residual
#check nyman_null_residual_early
#check nyman_null_residual_seven
#check nyman_null_finite_energy_unbounded
#check nyman_flat_null_perturb
#check nyman_flat_null_obstruction
#print axioms nyman_null_perturb_off_support
#print axioms nyman_null_perturb_moments
#print axioms nyman_null_perturb_mean
#print axioms nyman_null_residual
#print axioms nyman_null_residual_early
#print axioms nyman_null_residual_seven
#print axioms nyman_null_finite_energy_unbounded
#print axioms nyman_flat_null_perturb
#print axioms nyman_flat_null_obstruction

end RHLean.Analysis

import Mathlib
import «research.VF_919_SEXTIC_SECTOR_MEAN_DEFECT_20261022»

/-!
# Exact resonant-fiber recombination in original signed NNS coordinates

Every column occurrence survives. A proposed classOf map is not
assumed to be the actual arithmetic phase-locked relation; identifying
it with the original Hecke resonance is a SEPARATE arithmetic obligation.

The inter-fiber term is the LITERAL ordered Hermitian Gram, not
defined as the difference between two unexplained energies.
The source may include a separate minus-principal atom.
No new analytic moment estimate is assumed or claimed.
-/

noncomputable section
open scoped Classical BigOperators

namespace RHLean.Analysis
open RHLean.Proof

private theorem resonant_complex_norm_sq (z : ℂ) :
    ‖z‖ ^ 2 = (z * star z).re := by
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]

/-- Full diagonal and every different-label ordered complex Gram pair. -/
theorem resonant_norm_sq_sum_eq_diagonal_plus_off
    {κ : Type*} (s : Finset κ) (f : κ → ℂ) :
    ‖∑ c ∈ s, f c‖ ^ 2 =
      (∑ c ∈ s, ‖f c‖ ^ 2) +
        (∑ c ∈ s, ∑ d ∈ s.erase c, (f c * star (f d)).re) := by
  classical
  calc
    ‖∑ c ∈ s, f c‖ ^ 2 =
        ((∑ c ∈ s, f c) * star (∑ d ∈ s, f d)).re :=
          resonant_complex_norm_sq _
    _ = (∑ c ∈ s, ∑ d ∈ s, f c * star (f d)).re := by
      rw [star_sum, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = (∑ c ∈ s, ∑ d ∈ s, (f c * star (f d)).re) := by
      simp only [Complex.re_sum]
    _ = ∑ c ∈ s, (‖f c‖ ^ 2 +
          ∑ d ∈ s.erase c, (f c * star (f d)).re) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [← Finset.sum_erase_add s
        (fun d => (f c * star (f d)).re) hc]
      rw [resonant_complex_norm_sq]
      ring
    _ = (∑ c ∈ s, ‖f c‖ ^ 2) +
        (∑ c ∈ s, ∑ d ∈ s.erase c,
          (f c * star (f d)).re) := by
      rw [Finset.sum_add_distrib]

/-- Sum every admitted original atom with the same class label. -/
def resonantFiberSum {ι α κ : Type*}
    (atoms : Finset α) (classOf : α → κ)
    (a : ι → α → ℂ) (u : ι) (c : κ) : ℂ :=
  ∑ I ∈ atoms with classOf I = c, a u I

def resonantFiberClasses {α κ : Type*}
    (atoms : Finset α) (classOf : α → κ) : Finset κ :=
  atoms.image classOf

/-- True fiberwise regrouping without injectivity or norm collapsing. -/
theorem resonant_fiber_sum_eq_total
    {ι α κ : Type*} (atoms : Finset α) (classOf : α → κ)
    (a : ι → α → ℂ) (u : ι) :
    (∑ c ∈ resonantFiberClasses atoms classOf,
      resonantFiberSum atoms classOf a u c) =
      ∑ I ∈ atoms, a u I := by
  classical
  simpa only [resonantFiberClasses, resonantFiberSum] using
    (Finset.sum_fiberwise_of_maps_to (s := atoms)
      (t := atoms.image classOf) (g := classOf)
      (fun I hI => Finset.mem_image_of_mem classOf hI) (a u))

/-- Fully recombined within-class energy before squaring. -/
def resonantFiberEnergy {ι α κ : Type*}
    (rows : Finset ι) (atoms : Finset α)
    (classOf : α → κ) (a : ι → α → ℂ)
    (omega : ι → ℝ) : ℝ :=
  ∑ u ∈ rows, omega u *
    (∑ c ∈ resonantFiberClasses atoms classOf,
      ‖resonantFiberSum atoms classOf a u c‖ ^ 2)

/-- Inter-fiber ordered Gram with original complex coefficients. -/
def nonresonantInterfiberGram {ι α κ : Type*}
    (rows : Finset ι) (atoms : Finset α)
    (classOf : α → κ) (a : ι → α → ℂ)
    (omega : ι → ℝ) : ℝ :=
  ∑ u ∈ rows, omega u *
    (∑ c ∈ resonantFiberClasses atoms classOf,
      ∑ d ∈ (resonantFiberClasses atoms classOf).erase c,
        (resonantFiberSum atoms classOf a u c *
          star (resonantFiberSum atoms classOf a u d)).re)

/-- Exact recombination, with a LITERAL inter-fiber bilinear term. -/
theorem resonant_fiber_recombination_eq
    {ι α κ : Type*} (rows : Finset ι) (atoms : Finset α)
    (classOf : α → κ) (a : ι → α → ℂ)
    (omega : ι → ℝ) :
    (∑ u ∈ rows, omega u * ‖∑ I ∈ atoms, a u I‖ ^ 2) =
      resonantFiberEnergy rows atoms classOf a omega +
      nonresonantInterfiberGram rows atoms classOf a omega := by
  classical
  unfold resonantFiberEnergy nonresonantInterfiberGram
  calc
    (∑ u ∈ rows, omega u * ‖∑ I ∈ atoms, a u I‖ ^ 2) =
      ∑ u ∈ rows, omega u *
        ((∑ c ∈ resonantFiberClasses atoms classOf,
            ‖resonantFiberSum atoms classOf a u c‖ ^ 2) +
         (∑ c ∈ resonantFiberClasses atoms classOf,
           ∑ d ∈ (resonantFiberClasses atoms classOf).erase c,
             (resonantFiberSum atoms classOf a u c *
                star (resonantFiberSum atoms classOf a u d)).re)) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [← resonant_fiber_sum_eq_total atoms classOf a u]
      rw [resonant_norm_sq_sum_eq_diagonal_plus_off]
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib]

/-- Exact zero-target NNS Co minus Div after grouped compensation. -/
theorem resonant_fiber_recombination_NNS_eq
    {ι α κ : Type*} (rows : Finset ι) (atoms : Finset α)
    (classOf : α → κ) (a : ι → α → ℂ)
    (omega : ι → ℝ) :
    vf919WeightedPhiCoMass rows atoms omega
        (fun u I => (stableFarComplexToRealPair (a u I)).1)
        (fun u I => (stableFarComplexToRealPair (a u I)).2) -
      vf919WeightedPhiDivMass rows atoms omega
        (fun u I => (stableFarComplexToRealPair (a u I)).1)
        (fun u I => (stableFarComplexToRealPair (a u I)).2) =
      resonantFiberEnergy rows atoms classOf a omega +
      nonresonantInterfiberGram rows atoms classOf a omega := by
  classical
  let x : ι → α → ℝ :=
    fun u I => (stableFarComplexToRealPair (a u I)).1
  let y : ι → α → ℝ :=
    fun u I => (stableFarComplexToRealPair (a u I)).2
  have hNNS := vf919WeightedPhiMarkedMoment_eq_co_sub_div
    rows atoms omega x y
  change vf919WeightedPhiCoMass rows atoms omega x y -
    vf919WeightedPhiDivMass rows atoms omega x y = _
  rw [← hNNS]
  have hReal :
      vf919WeightedPhiMarkedMoment rows atoms omega x y =
        ∑ u ∈ rows, omega u * ‖∑ I ∈ atoms, a u I‖ ^ 2 := by
    unfold vf919WeightedPhiMarkedMoment
    apply Finset.sum_congr rfl
    intro u hu
    have hPhi := vf919Phi_sum_idealAtoms atoms (a u)
    have hEnergy :=
      stableFarRealPairNormalizedEnergy_complexToRealPair
        (∑ I ∈ atoms, a u I)
    rw [hPhi] at hEnergy
    change (((∑ I ∈ atoms, x u I) ^ 2 +
      (∑ I ∈ atoms, y u I) ^ 2) / 2) =
        ‖∑ I ∈ atoms, a u I‖ ^ 2 at hEnergy
    rw [hEnergy]
  rw [hReal]
  exact resonant_fiber_recombination_eq rows atoms classOf a omega


/-- EXACT weld from the different-fiber Hermitian Gram to the
    NONUNIFORM six-sector defect. This is not a Fourier estimate:
    hPhase is the EXPLICIT missing source-specific statement that
    each pair of original resonant classes has the indicated sixth-root
    character on every admitted row, with complex coefficient.
    For a globally trivial relative Hecke character, hPhase is NOT the
    nontrivial six-sector hypothesis and the pair must remain grouped.
    Ramified zero character values use phase=none. -/
theorem resonant_interfiber_Gram_eq_sextic_defects
    {ι α κ : Type*} (rows : Finset ι) (atoms : Finset α)
    (classOf : α → κ) (a : ι → α → ℂ)
    (omega : ι → ℝ)
    (phase : κ → κ → ι → Option (Fin 6))
    (coefficient : κ → κ → ι → ℂ)
    (ζ : ℂ) (hpow : ζ ^ 6 = 1) (hne : ζ ≠ 1)
    (hPhase : ∀ c ∈ resonantFiberClasses atoms classOf,
      ∀ d ∈ (resonantFiberClasses atoms classOf).erase c,
      ∀ u ∈ rows,
        resonantFiberSum atoms classOf a u c *
          star (resonantFiberSum atoms classOf a u d) =
          coefficient c d u *
            sexticPhaseWithZero ζ (phase c d u)) :
    nonresonantInterfiberGram rows atoms classOf a omega =
      ∑ c ∈ resonantFiberClasses atoms classOf,
        ∑ d ∈ (resonantFiberClasses atoms classOf).erase c,
          (sexticSectorDefect ζ
            (sexticWeightedSectorMass rows (phase c d) omega
              (coefficient c d))).re := by
  classical
  let s := resonantFiberClasses atoms classOf
  let B := resonantFiberSum atoms classOf a
  change
    (∑ u ∈ rows, omega u *
      (∑ c ∈ s, ∑ d ∈ s.erase c,
        (B u c * star (B u d)).re)) =
    ∑ c ∈ s, ∑ d ∈ s.erase c,
      (sexticSectorDefect ζ
        (sexticWeightedSectorMass rows (phase c d) omega
          (coefficient c d))).re
  calc
    (∑ u ∈ rows, omega u *
      (∑ c ∈ s, ∑ d ∈ s.erase c,
        (B u c * star (B u d)).re)) =
      ∑ c ∈ s, ∑ d ∈ s.erase c, ∑ u ∈ rows,
        omega u * (B u c * star (B u d)).re := by
      calc
        _ = ∑ u ∈ rows, ∑ c ∈ s, ∑ d ∈ s.erase c,
          omega u * (B u c * star (B u d)).re := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c hc
          rw [Finset.mul_sum]
        _ = ∑ c ∈ s, ∑ u ∈ rows, ∑ d ∈ s.erase c,
          omega u * (B u c * star (B u d)).re := by
          rw [Finset.sum_comm]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro c hc
          rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      have hpair :
          (∑ u ∈ rows, omega u *
            (B u c * star (B u d)).re) =
          (∑ u ∈ rows, (omega u : ℂ) *
            (B u c * star (B u d))).re := by
        rw [Complex.re_sum]
        apply Finset.sum_congr rfl
        intro u hu
        simp only [Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero]
      rw [hpair]
      congr 1
      calc
        (∑ u ∈ rows, (omega u : ℂ) *
          (B u c * star (B u d))) =
          ∑ u ∈ rows, (omega u : ℂ) *
            coefficient c d u *
              sexticPhaseWithZero ζ (phase c d u) := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [hPhase c hc d hd u hu]
            ring
        _ = _ := sextic_weighted_nonuniform_defect_exact
          rows (phase c d) omega (coefficient c d) ζ hpow hne

/-- Requested two-part exact proof contract, now explicitly
    with six-sector defect rather than a generic cross Gram.
    The only premise is the ORIGINAL phase admission hPhase; no
    source-moment estimate, global hHigh, or saving is imported. -/
theorem resonant_fiber_recombination_eq_sextic
    {ι α κ : Type*} (rows : Finset ι) (atoms : Finset α)
    (classOf : α → κ) (a : ι → α → ℂ)
    (omega : ι → ℝ)
    (phase : κ → κ → ι → Option (Fin 6))
    (coefficient : κ → κ → ι → ℂ)
    (ζ : ℂ) (hpow : ζ ^ 6 = 1) (hne : ζ ≠ 1)
    (hPhase : ∀ c ∈ resonantFiberClasses atoms classOf,
      ∀ d ∈ (resonantFiberClasses atoms classOf).erase c,
      ∀ u ∈ rows,
        resonantFiberSum atoms classOf a u c *
          star (resonantFiberSum atoms classOf a u d) =
          coefficient c d u *
            sexticPhaseWithZero ζ (phase c d u)) :
    (∑ u ∈ rows, omega u * ‖∑ I ∈ atoms, a u I‖ ^ 2) =
      resonantFiberEnergy rows atoms classOf a omega +
      ∑ c ∈ resonantFiberClasses atoms classOf,
        ∑ d ∈ (resonantFiberClasses atoms classOf).erase c,
          (sexticSectorDefect ζ
            (sexticWeightedSectorMass rows (phase c d) omega
              (coefficient c d))).re := by
  rw [resonant_fiber_recombination_eq,
    resonant_interfiber_Gram_eq_sextic_defects
      rows atoms classOf a omega phase coefficient ζ hpow hne hPhase]

/-- Original high-row constants must pay c1+c2, not merely exist. -/
theorem compensated_resonant_and_nonresonant_bounds_close_NNS
    (resonant nonresonant target c₁ c₂ : ℝ)
    (htarget : 0 ≤ target)
    (hres : resonant ≤ c₁ * target)
    (hnonres : nonresonant ≤ c₂ * target)
    (hbudget : c₁ + c₂ ≤ 1) :
    resonant + nonresonant ≤ target := by
  calc
    resonant + nonresonant ≤ c₁ * target + c₂ * target :=
      add_le_add hres hnonres
    _ = (c₁ + c₂) * target := by ring
    _ ≤ 1 * target := mul_le_mul_of_nonneg_right hbudget htarget
    _ = target := one_mul target

/-- Exact joint NNS certificate from two EXTERNAL arithmetic bounds. -/
theorem resonant_NNS_uniform_saving_from_two_payments
    {ι α κ : Type*} (rows : Finset ι) (atoms : Finset α)
    (classOf : α → κ) (a : ι → α → ℂ)
    (omega : ι → ℝ) (target c₁ c₂ : ℝ)
    (htarget : 0 ≤ target)
    (hres : resonantFiberEnergy rows atoms classOf a omega ≤ c₁ * target)
    (hdefect : nonresonantInterfiberGram rows atoms classOf a omega ≤ c₂ * target)
    (hbudget : c₁ + c₂ ≤ 1) :
    vf919WeightedPhiCoMass rows atoms omega
        (fun u I => (stableFarComplexToRealPair (a u I)).1)
        (fun u I => (stableFarComplexToRealPair (a u I)).2) -
      vf919WeightedPhiDivMass rows atoms omega
        (fun u I => (stableFarComplexToRealPair (a u I)).1)
        (fun u I => (stableFarComplexToRealPair (a u I)).2) ≤ target := by
  rw [resonant_fiber_recombination_NNS_eq]
  exact compensated_resonant_and_nonresonant_bounds_close_NNS
    _ _ _ _ _ htarget hres hdefect hbudget

/-- Ideal anti-aligned parent and child cancel before squaring. -/
theorem resonant_parent_child_energy_is_remainder
    (parent remainder : ℂ) :
    ‖parent + (-parent + remainder)‖ ^ 2 = ‖remainder‖ ^ 2 := by
  have h : parent + (-parent + remainder) = remainder := by ring
  rw [h]

/-- Exact favorable NNS offdiagonal payment for such a PAIR. -/
theorem resonant_parent_child_diagonal_payment
    (parent remainder : ℂ) :
    ‖parent‖ ^ 2 + ‖remainder - parent‖ ^ 2 +
        2 * (parent * star (remainder - parent)).re =
      ‖remainder‖ ^ 2 := by
  have htwo (z w : ℂ) :
      ‖z + w‖ ^ 2 =
      ‖z‖ ^ 2 + ‖w‖ ^ 2 + 2 * (z * star w).re := by
    simp only [Complex.sq_norm, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  calc
    _ = ‖parent + (remainder - parent)‖ ^ 2 :=
      (htwo parent (remainder - parent)).symm
    _ = ‖remainder‖ ^ 2 := by
      have h : parent + (remainder - parent) = remainder := by ring
      rw [h]

end RHLean.Analysis

#print axioms RHLean.Analysis.resonant_norm_sq_sum_eq_diagonal_plus_off
#print axioms RHLean.Analysis.resonant_fiber_sum_eq_total
#print axioms RHLean.Analysis.resonant_fiber_recombination_eq
#print axioms RHLean.Analysis.resonant_fiber_recombination_NNS_eq
#print axioms RHLean.Analysis.compensated_resonant_and_nonresonant_bounds_close_NNS
#print axioms RHLean.Analysis.resonant_NNS_uniform_saving_from_two_payments
#print axioms RHLean.Analysis.resonant_parent_child_energy_is_remainder
#print axioms RHLean.Analysis.resonant_parent_child_diagonal_payment

#print axioms RHLean.Analysis.resonant_interfiber_Gram_eq_sextic_defects
#print axioms RHLean.Analysis.resonant_fiber_recombination_eq_sextic

import Mathlib
import RHLean.Analysis.CanonicalHighSectorCore
import «research.SQUARE_SHELL_MASK_ENERGY_20261030»
import «research.SQUARE_SHELL_INCIDENCE_COMPENSATION_LEAN»

/-!
# Exact physical Euler / smooth-minus-transport / incidence synthesis

Every profile here is evaluated on genuine shell integers and Mobius signs.
The smooth cutoff is the original canonical largest prime factor <=R.
Finite inverse incidence then identifies the corrected original Euler source,
including every signed quadratic cross term. No analytic bound is assumed.
The separate cofactor-count interpretation z-a requires its prime-labelled
Fubini map; the present statements do not pretend that map is an estimate.
-/
noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators
namespace RHLean.Proof
attribute [local instance] Classical.propDecidable

/-- Actual smooth-site divisor profile, using the repo's largest-prime geometry. -/
def synthesisSmoothDivisorProfile (R h : ℕ) : ℤ :=
  ∑ n ∈ Finset.Ico (R*R) ((R+1)*(R+1)),
    if h ∣ n then (if canonicalLargestPrimeFactor n ≤ R then μ n else 0) else 0

/-- Actual sign-reversed rough transport, with the SAME physical divisor mask. -/
def synthesisTransportDivisorProfile (R h : ℕ) : ℤ :=
  -∑ n ∈ Finset.Ico (R*R) ((R+1)*(R+1)),
    if h ∣ n then (if R < canonicalLargestPrimeFactor n then μ n else 0) else 0

theorem synthesisDivisorMobius_eq_smooth_sub_transport (R h : ℕ) :
    synthesisDivisorMobiusWindow R h =
      synthesisSmoothDivisorProfile R h - synthesisTransportDivisorProfile R h := by
  unfold synthesisDivisorMobiusWindow synthesisSmoothDivisorProfile
    synthesisTransportDivisorProfile
  rw [sub_neg_eq_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hd : h ∣ n
  · by_cases hp : canonicalLargestPrimeFactor n ≤ R
    · simp [hd, hp, Nat.not_lt.mpr hp]
    · have hl : R < canonicalLargestPrimeFactor n := Nat.lt_of_not_ge hp
      simp [hd, hp, hl]
  · simp [hd]

/-- Actual compensated residual: inverse incidence of the physical shell profile. -/
def synthesisCompensatedIncidence (R c : ℕ) : ℤ :=
  -shellIncidenceCompensator R (synthesisDivisorMobiusWindow R) c

/-- Smooth and transport contributions are compensated BEFORE taking norms. -/
theorem synthesisCompensatedIncidence_eq_transport_sub_smooth
    (R c : ℕ) :
    synthesisCompensatedIncidence R c =
      shellIncidenceCompensator R (synthesisTransportDivisorProfile R) c -
      shellIncidenceCompensator R (synthesisSmoothDivisorProfile R) c := by
  unfold synthesisCompensatedIncidence shellIncidenceCompensator
  rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [synthesisDivisorMobius_eq_smooth_sub_transport]
  by_cases hc : c ∣ n <;> simp [hc] <;> ring

/-- Every divisor channel is the corrected ORIGINAL Euler source. -/
theorem synthesisCompensatedIncidence_profile
    (R h : ℕ) (hR : 3 ≤ R) (hh : 1 ≤ h) (hhR : h ≤ R) :
    shellDivisibilityProfile R (synthesisCompensatedIncidence R) h =
      synthesisDivisorEulerWindow R h - synthesisDivisorCornerWindow R h := by
  have hinv := shellIncidenceCompensator_matches R h
    (synthesisDivisorMobiusWindow R) hh hhR
  have hsum :
      shellDivisibilityProfile R (synthesisCompensatedIncidence R) h =
      -synthesisDivisorMobiusWindow R h := by
    unfold shellDivisibilityProfile synthesisCompensatedIncidence
    rw [← hinv, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro c _hc
    by_cases hd : h ∣ c <;> simp [hd]
  rw [hsum, synthesisDivisorEuler_eq_neg_mobius_add_corner R h hR]
  ring

/-- Arbitrary SIGNED divisor kernel, not assumed positive or stationary. -/
def synthesisDivisorGramKernel (R : ℕ) (weight : ℕ → ℤ) (c cp : ℕ) : ℤ :=
  ∑ h ∈ Finset.Icc 1 R, if h ∣ c ∧ h ∣ cp then weight h else 0

lemma synthesisDivisorGram_factor
    (R : ℕ) (weight u : ℕ → ℤ) :
    shellBilinear (Finset.Icc 1 R) (synthesisDivisorGramKernel R weight) u u =
      ∑ h ∈ Finset.Icc 1 R, weight h * (shellDivisibilityProfile R u h)^2 := by
  let I := Finset.Icc 1 R
  let m (h c : ℕ) : ℤ := if h ∣ c then u c else 0
  have hatom (c cp : ℕ) :
      u c * (∑ h ∈ I, if h ∣ c ∧ h ∣ cp then weight h else 0) * u cp =
      ∑ h ∈ I, weight h * m h c * m h cp := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro h _hh
    by_cases h1 : h ∣ c <;> by_cases h2 : h ∣ cp <;>
      simp [m,h1,h2] <;> ring
  change (∑ c ∈ I, ∑ cp ∈ I,
    u c * (∑ h ∈ I, if h ∣ c ∧ h ∣ cp then weight h else 0) * u cp) = _
  simp_rw [hatom]
  calc
    (∑ c ∈ I, ∑ cp ∈ I, ∑ h ∈ I, weight h * m h c * m h cp) =
        ∑ c ∈ I, ∑ h ∈ I, ∑ cp ∈ I, weight h * m h c * m h cp := by
      apply Finset.sum_congr rfl
      intro c _hc
      exact Finset.sum_comm
    _ = ∑ h ∈ I, ∑ c ∈ I, ∑ cp ∈ I, weight h * m h c * m h cp :=
      Finset.sum_comm
    _ = ∑ h ∈ Finset.Icc 1 R, weight h * (shellDivisibilityProfile R u h)^2 := by
      apply Finset.sum_congr rfl
      intro h _hh
      simp only [shellDivisibilityProfile, pow_two, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _hc
      apply Finset.sum_congr rfl
      intro cp _hcp
      rfl

/-- Full physical signed Gram, with no omitted cofactor cross terms. -/
theorem synthesisCompensatedIncidence_gram
    (R : ℕ) (weight : ℕ → ℤ) (hR : 3 ≤ R) :
    shellBilinear (Finset.Icc 1 R) (synthesisDivisorGramKernel R weight)
      (synthesisCompensatedIncidence R) (synthesisCompensatedIncidence R) =
    ∑ h ∈ Finset.Icc 1 R, weight h *
      (synthesisDivisorEulerWindow R h - synthesisDivisorCornerWindow R h)^2 := by
  rw [synthesisDivisorGram_factor]
  apply Finset.sum_congr rfl
  intro h hh
  rw [synthesisCompensatedIncidence_profile R h hR
    (Finset.mem_Icc.mp hh).1 (Finset.mem_Icc.mp hh).2]

/-- The unit channel is retained and remains a genuine arithmetic obligation. -/
theorem synthesisCompensatedIncidence_total
    (R : ℕ) (hR : 3 ≤ R) :
    (∑ c ∈ Finset.Icc 1 R, synthesisCompensatedIncidence R c) =
      -synthesisDivisorMobiusWindow R 1 := by
  have h := synthesisCompensatedIncidence_profile R 1 hR (by omega) (by omega)
  simp only [shellDivisibilityProfile, one_dvd, ite_true] at h
  rw [synthesisDivisorEuler_eq_neg_mobius_add_corner R 1 hR] at h
  linear_combination h

#print axioms synthesisDivisorMobius_eq_smooth_sub_transport
#print axioms synthesisCompensatedIncidence_eq_transport_sub_smooth
#print axioms synthesisCompensatedIncidence_profile
#print axioms synthesisDivisorGram_factor
#print axioms synthesisCompensatedIncidence_gram
#print axioms synthesisCompensatedIncidence_total
end RHLean.Proof

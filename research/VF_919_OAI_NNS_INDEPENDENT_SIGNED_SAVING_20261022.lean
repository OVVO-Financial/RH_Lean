import Mathlib
import «research.VF_919_OAI_GAUSSIAN_SUBSET_EXACT_COEFFICIENT_NNS_20261021»

/-!
# Original OAI signed moment: the saving demanded, and a genuinely
# independent finite character-phase payment in NNS coordinates

The original OAI high-row saving at scale Z is
  |Σ_J A_J/normer - principalSignal| <= B Z^(beta-11/16-sigma).
Its exact NNS target is
  Div_all - Co_off >= D - B^2 Z^(2*(beta-11/16-sigma)).
This is the PROOF OBLIGATION, not an axiom of arithmetic.

The finite two-phase theorem below supplies a real, independent and
unconditional cancellation of the offdiagonal NNS covariance for a
COMPLETE ± character orbit. Its proof does not cite OAI's high-row bound,
RH, PNT, or a signed-moment assumption. The original OAI high-row family
is NOT known to be a complete phase orbit; therefore this useful
arithmetic toy theorem is NOT itself the required OAI uniform saving.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis
open RHLean.Proof

/-- Exact signed NNS payment criterion for the original OAI saving,
    given the already proved identity E = diagonal+Co_off-Div. -/
theorem nns_original_saving_iff_signed_payment
    (energy diagonal coOff divOff budget : ℝ)
    (hSource : energy = diagonal + coOff - divOff) :
    energy ≤ budget ↔
      diagonal - budget ≤ divOff - coOff := by
  rw [hSource]
  constructor <;> intro h <;> linarith

/-- The original positive power gain σ in a COMPLEX first moment
    requires a TWICE-σ gain in the signed NNS second moment.
    This is algebraically EXACT for the true integrated source. -/
theorem nns_original_sigma_saving_iff_payment
    (energy diagonal coOff divOff B Z beta sigma : ℝ)
    (hSource : energy = diagonal + coOff - divOff) :
    energy ≤ B ^ 2 * Z ^ (2 * (beta - 11 / 16 - sigma)) ↔
      diagonal - B ^ 2 * Z ^ (2 * (beta - 11 / 16 - sigma))
        ≤ divOff - coOff :=
  nns_original_saving_iff_signed_payment energy diagonal coOff divOff
    (B ^ 2 * Z ^ (2 * (beta - 11 / 16 - sigma))) hSource

/-- The finite ± orbit, with two labelled complex source atoms.
    The 'high' atom changes phase across the FULL orbit; the low atom
    does not. No probabilistic independence hypothesis appears. -/
def nnsTwoPhaseAtom (a b : ℂ) (phase atom : Bool) : ℂ :=
  if atom then (if phase then -b else b) else a

private theorem nnsTwoPhase_row (a b : ℂ) (phase : Bool) :
    (∑ atom : Bool, nnsTwoPhaseAtom a b phase atom) =
      if phase then a - b else a + b := by
  cases phase <;> simp [nnsTwoPhaseAtom, Fintype.sum_bool] <;> ring

/-- Unconditional complex parallelogram payment from the two ACTUAL
    opposite character phases. No moment estimate is assumed. -/
theorem nnsTwoPhase_complex_saving (a b : ℂ) :
    ‖a + b‖ ^ 2 + ‖a - b‖ ^ 2 =
      2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring

/-- Native NNS realification of the same original complex atoms. -/
def nnsTwoPhaseX (a b : ℂ) (phase atom : Bool) : ℝ :=
  (stableFarComplexToRealPair (nnsTwoPhaseAtom a b phase atom)).1

def nnsTwoPhaseY (a b : ℂ) (phase atom : Bool) : ℝ :=
  (stableFarComplexToRealPair (nnsTwoPhaseAtom a b phase atom)).2

/-- Genuine independent cancellation IN NNS CO-DIV COORDINATES.
    Every diagonal and offdiagonal is still in Co_all-Div_all.

    Over the two equally represented opposite phases:
      Σphase (Co_all - Div_all) = 2*(|a|²+|b|²).
    A naive termwise absolute bound can cost (|a|+|b|)² per phase;
    the genuine cross-orbit covariance cancels exactly. -/
theorem nnsTwoPhase_independent_signed_moment (a b : ℂ) :
    vf919WeightedPhiCoMass
      (Finset.univ : Finset Bool) (Finset.univ : Finset Bool)
      (fun _ => (1 : ℝ)) (nnsTwoPhaseX a b) (nnsTwoPhaseY a b) -
    vf919WeightedPhiDivMass
      (Finset.univ : Finset Bool) (Finset.univ : Finset Bool)
      (fun _ => (1 : ℝ)) (nnsTwoPhaseX a b) (nnsTwoPhaseY a b) =
      2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  classical
  let rows : Finset Bool := Finset.univ
  let atoms : Finset Bool := Finset.univ
  let w : Bool → ℝ := fun _ => 1
  let x := nnsTwoPhaseX a b
  let y := nnsTwoPhaseY a b
  have hNNS := vf919WeightedPhiMarkedMoment_eq_co_sub_div
    rows atoms w x y
  change vf919WeightedPhiCoMass rows atoms w x y -
    vf919WeightedPhiDivMass rows atoms w x y =
    2 * (‖a‖ ^ 2 + ‖b‖ ^ 2)
  rw [← hNNS]
  have hRow (u : Bool) :
      ((∑ i ∈ atoms, x u i) ^ 2 +
        (∑ i ∈ atoms, y u i) ^ 2) / 2 =
      ‖∑ i ∈ atoms, nnsTwoPhaseAtom a b u i‖ ^ 2 := by
    have hphi :=
      vf919Phi_sum_idealAtoms atoms (nnsTwoPhaseAtom a b u)
    have henergy :=
      stableFarRealPairNormalizedEnergy_complexToRealPair
        (∑ i ∈ atoms, nnsTwoPhaseAtom a b u i)
    rw [hphi] at henergy
    change ((∑ i ∈ atoms, x u i) ^ 2 +
      (∑ i ∈ atoms, y u i) ^ 2) / 2 =
      ‖∑ i ∈ atoms, nnsTwoPhaseAtom a b u i‖ ^ 2 at henergy
    exact henergy
  have hRows :
      vf919WeightedPhiMarkedMoment rows atoms w x y =
        ∑ u ∈ rows, ‖∑ i ∈ atoms,
          nnsTwoPhaseAtom a b u i‖ ^ 2 := by
    unfold vf919WeightedPhiMarkedMoment
    apply Finset.sum_congr rfl
    intro u hu
    change 1 * (((∑ i ∈ atoms, x u i) ^ 2 +
      (∑ i ∈ atoms, y u i) ^ 2) / 2) =
      ‖∑ i ∈ atoms, nnsTwoPhaseAtom a b u i‖ ^ 2
    rw [one_mul]
    exact hRow u
  rw [hRows]
  change (∑ u : Bool, ‖∑ i : Bool,
    nnsTwoPhaseAtom a b u i‖ ^ 2) =
      2 * (‖a‖ ^ 2 + ‖b‖ ^ 2)
  rw [Fintype.sum_bool]
  rw [nnsTwoPhase_row, nnsTwoPhase_row]
  simp only [Bool.ite_true, Bool.ite_false]
  exact (nnsTwoPhase_complex_saving a b).symm.trans
    (by ring)

/-- NNS realification CANNOT establish a uniform saving on arbitrary
    signed sources: n coherent atoms have n² energy, not O(n).
    Any original OAI power saving MUST exploit original arithmetic phase
    restrictions, not the coordinate system by itself. -/
theorem nnsCoherentSource_no_free_gain (n : ℕ) :
    ‖∑ _i ∈ Finset.range n, (1 : ℂ)‖ ^ 2 = (n : ℝ) ^ 2 := by
  simp

end RHLean.Analysis

#print axioms RHLean.Analysis.nns_original_saving_iff_signed_payment
#print axioms RHLean.Analysis.nns_original_sigma_saving_iff_payment
#print axioms RHLean.Analysis.nnsTwoPhase_complex_saving
#print axioms RHLean.Analysis.nnsTwoPhase_independent_signed_moment
#print axioms RHLean.Analysis.nnsCoherentSource_no_free_gain

import «research.oai_434.VF919PrincipalFiniteResponse»
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Finite labelled principal response and its coefficient mass

Claim 20261110-coordinator-2309-EST/FFR1, independently accepted by
20261111-referee-1. Logarithmic delays add under multiplication. Lists retain
occurrence multiplicity and every mixed term, even when delays coincide.
Only the exact tail coefficient mass is bounded; no signal or endpoint bound
is assumed. The Mellin return and complete physical assembly are separate.
-/

namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.PrincipalSlotEstimate

namespace FiniteResponse

abbrev Atom := ℝ × ℂ
abbrev Terms := List Atom

def evalAtom (s : ℂ) (a : Atom) : ℂ :=
  a.2 * Complex.exp (-(a.1 : ℂ) * s)

def massAtom (theta : ℝ) (a : Atom) : ℝ :=
  ‖a.2‖ * Real.exp (-a.1 * theta)

def eval (s : ℂ) : Terms → ℂ
  | [] => 0
  | a :: p => evalAtom s a + eval s p

def mass (theta : ℝ) : Terms → ℝ
  | [] => 0
  | a :: p => massAtom theta a + mass theta p

def shift (a : Atom) (p : Terms) : Terms :=
  p.map (fun b => (a.1 + b.1, a.2 * b.2))

def mul : Terms → Terms → Terms
  | [], _ => []
  | a :: p, q => shift a q ++ mul p q

def scale (c : ℂ) (p : Terms) : Terms := shift (0, c) p

def constant (c : ℂ) : Terms := [(0, c)]

@[simp] theorem eval_append (s : ℂ) (p q : Terms) :
    eval s (p ++ q) = eval s p + eval s q := by
  induction p with
  | nil => simp [eval]
  | cons a p ih => simp [eval, ih, add_assoc]

@[simp] theorem mass_append (theta : ℝ) (p q : Terms) :
    mass theta (p ++ q) = mass theta p + mass theta q := by
  induction p with
  | nil => simp [mass]
  | cons a p ih => simp [mass, ih, add_assoc]

theorem mass_nonneg (theta : ℝ) (p : Terms) : 0 ≤ mass theta p := by
  induction p with
  | nil => simp [mass]
  | cons a p ih => exact add_nonneg (by unfold massAtom; positivity) ih

@[simp] theorem eval_shift (s : ℂ) (a : Atom) (p : Terms) :
    eval s (shift a p) = evalAtom s a * eval s p := by
  induction p with
  | nil => simp [shift, eval]
  | cons b p ih =>
    simp only [shift, List.map_cons, eval] at ih ⊢
    rw [ih]
    simp only [evalAtom, Complex.ofReal_add]
    rw [show -((a.1 : ℂ) + b.1) * s = -(a.1 : ℂ) * s + -(b.1 : ℂ) * s by ring,
      Complex.exp_add]
    ring

@[simp] theorem mass_shift (theta : ℝ) (a : Atom) (p : Terms) :
    mass theta (shift a p) = massAtom theta a * mass theta p := by
  induction p with
  | nil => simp [shift, mass]
  | cons b p ih =>
    simp only [shift, List.map_cons, mass] at ih ⊢
    rw [ih]
    simp only [massAtom, norm_mul]
    rw [show -(a.1 + b.1) * theta = -a.1 * theta + -b.1 * theta by ring,
      Real.exp_add]
    ring

@[simp] theorem eval_mul (s : ℂ) (p q : Terms) :
    eval s (mul p q) = eval s p * eval s q := by
  induction p with
  | nil => simp [mul, eval]
  | cons a p ih => simp [mul, eval, ih, add_mul]

@[simp] theorem mass_mul (theta : ℝ) (p q : Terms) :
    mass theta (mul p q) = mass theta p * mass theta q := by
  induction p with
  | nil => simp [mul, mass]
  | cons a p ih => simp [mul, mass, ih, add_mul]

@[simp] theorem eval_scale (s : ℂ) (c : ℂ) (p : Terms) :
    eval s (scale c p) = c * eval s p := by simp [scale, evalAtom]

@[simp] theorem mass_scale (theta : ℝ) (c : ℂ) (p : Terms) :
    mass theta (scale c p) = ‖c‖ * mass theta p := by simp [scale, massAtom]

@[simp] theorem eval_constant (s c : ℂ) : eval s (constant c) = c := by
  simp [constant, eval, evalAtom]

@[simp] theorem mass_constant (theta : ℝ) (c : ℂ) :
    mass theta (constant c) = ‖c‖ := by simp [constant, mass, massAtom]

/-- Nonconstant terms of q+(1-q)(1-W) sum_(j<=K) H^j. -/
def response (q : ℝ) (H W : Terms) : ℕ → Terms
  | 0 => scale (-(1 - (q : ℂ))) W
  | K + 1 => scale (-(1 - (q : ℂ))) W ++
      mul H (constant (1 - (q : ℂ)) ++ response q H W K)

theorem response_eval (q : ℝ) (H W : Terms) (K : ℕ) (s : ℂ) :
    1 + eval s (response q H W K) = (q : ℂ) +
      (1 - (q : ℂ)) * (1 - eval s W) *
        ∑ k ∈ Finset.range (K + 1), eval s H ^ k := by
  induction K with
  | zero => simp [response]; ring
  | succ K ih =>
    have hgeom : (∑ k ∈ Finset.range (K + 1 + 1), eval s H ^ k) =
        1 + eval s H * ∑ k ∈ Finset.range (K + 1), eval s H ^ k := by
      rw [Finset.sum_range_succ']
      simp only [pow_zero, pow_succ', ← Finset.mul_sum]
      ring
    simp only [response, eval_append, eval_scale, eval_mul, eval_constant]
    rw [hgeom]
    linear_combination ih * eval s H

/-- The explicit geometric coefficient bound is uniform in truncation order. -/
theorem response_mass_le (q : ℝ) (H W : Terms) (K : ℕ) (theta r w : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hw : 0 ≤ w) (hH : mass theta H ≤ r) (hW : mass theta W ≤ w) :
    mass theta (response q H W K) ≤ (1 - q) * (r + w) / (1 - r) := by
  have hnorm : ‖1 - (q : ℂ)‖ = 1 - q := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hq1)]
  have hden : 0 < 1 - r := sub_pos.mpr hr1
  have hL : 0 ≤ (1 - q) * (r + w) / (1 - r) := by positivity
  induction K with
  | zero =>
    simp only [response, mass_scale, norm_neg, hnorm]
    apply (mul_le_mul_of_nonneg_left hW (sub_nonneg.mpr hq1)).trans
    apply (le_div_iff₀ hden).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hq1) hr0,
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hq1) hw) hr0]
  | succ K ih =>
    have hpositive : 0 ≤ 1 - q + mass theta (response q H W K) :=
      add_nonneg (sub_nonneg.mpr hq1) (mass_nonneg _ _)
    simp only [response, mass_append, mass_scale, mass_mul, mass_constant, norm_neg, hnorm]
    calc
      _ ≤ (1 - q) * w + r * ((1 - q) + (1 - q) * (r + w) / (1 - r)) := by
        gcongr
      _ = (1 - q) * (r + w) / (1 - r) := by field_simp; ring

/-- Expand the entire product of 1+response, retaining both linear and mixed terms. -/
def complete : List Terms → Terms
  | [] => []
  | p :: ps => p ++ complete ps ++ mul p (complete ps)

theorem complete_eval (ps : List Terms) (s : ℂ) :
    1 + eval s (complete ps) = (ps.map (fun p => 1 + eval s p)).prod := by
  induction ps with
  | nil => simp [complete, eval]
  | cons p ps ih =>
    simp only [complete, eval_append, eval_mul, List.map_cons, List.prod_cons]
    rw [← ih]
    ring

theorem complete_mass (ps : List Terms) (theta : ℝ) :
    1 + mass theta (complete ps) = (ps.map (fun p => 1 + mass theta p)).prod := by
  induction ps with
  | nil => simp [complete, mass]
  | cons p ps ih =>
    simp only [complete, mass_append, mass_mul, List.map_cons, List.prod_cons]
    rw [← ih]
    ring

theorem complete_mass_le (ps : List Terms) (theta L : ℝ) (hL : 0 ≤ L)
    (hp : ∀ p ∈ ps, mass theta p ≤ L) :
    mass theta (complete ps) ≤ (1 + L) ^ ps.length - 1 := by
  induction ps with
  | nil => simp [complete, mass]
  | cons p ps ih =>
    have hp0 := mass_nonneg theta p
    have hp1 := hp p (by simp)
    have ht := ih (fun q hq => hp q (by simp [hq]))
    have htp := mass_nonneg theta (complete ps)
    simp only [complete, mass_append, mass_mul, List.length_cons, pow_succ]
    nlinarith [mul_le_mul hp1 ht htp hL]

private theorem eval_flatMap {ι : Type*} (s : ℂ) (is : List ι) (f : ι → Terms) :
    eval s (is.flatMap f) = (is.map (fun i => eval s (f i))).sum := by
  induction is with
  | nil => simp [eval]
  | cons i is ih => simp [ih]

private theorem mass_flatMap {ι : Type*} (theta : ℝ) (is : List ι) (f : ι → Terms) :
    mass theta (is.flatMap f) = (is.map (fun i => mass theta (f i))).sum := by
  induction is with
  | nil => simp [mass]
  | cons i is ih => simp [ih]

def average {ι : Type*} (T : Finset ι) (w : ι → ℝ) (p : ι → Terms) : Terms :=
  T.toList.flatMap (fun i => scale ((w i / ∑ k ∈ T, w k : ℝ) : ℂ) (p i))

theorem average_eval {ι : Type*} (T : Finset ι) (w : ι → ℝ) (p : ι → Terms)
    (s : ℂ) (hM : (∑ i ∈ T, w i) ≠ 0) :
    1 + eval s (average T w p) =
      (∑ i ∈ T, (w i : ℂ) * (1 + eval s (p i))) / (∑ i ∈ T, w i : ℝ) := by
  have hc : ((∑ i ∈ T, w i : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hM
  have hc' : (∑ i ∈ T, (w i : ℂ)) ≠ 0 := by
    simpa only [Complex.ofReal_sum] using hc
  simp only [average, eval_flatMap, eval_scale, Finset.sum_map_toList,
    Complex.ofReal_div, div_mul_eq_mul_div, ← Finset.sum_div,
    mul_add, mul_one, Finset.sum_add_distrib, Complex.ofReal_sum]
  rw [add_div, div_self hc']

theorem average_mass_le {ι : Type*} (T : Finset ι) (w : ι → ℝ) (p : ι → Terms)
    (theta L : ℝ) (hw : ∀ i ∈ T, 0 ≤ w i) (hM : 0 < ∑ i ∈ T, w i)
    (hp : ∀ i ∈ T, mass theta (p i) ≤ L) :
    mass theta (average T w p) ≤ L := by
  simp only [average, mass_flatMap, mass_scale, Finset.sum_map_toList]
  calc
    _ = ∑ i ∈ T, (w i / ∑ k ∈ T, w k) * mass theta (p i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (hw i hi) hM.le)]
    _ ≤ ∑ i ∈ T, (w i / ∑ k ∈ T, w k) * L := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hp i hi) (div_nonneg (hw i hi) hM.le)
    _ = L := by rw [← Finset.sum_mul, ← Finset.sum_div, div_self hM.ne', one_mul]

def nonnegativeDelays (p : Terms) : Prop := ∀ a ∈ p, 0 ≤ a.1

private theorem nonnegative_shift (a : Atom) (p : Terms)
    (ha : 0 ≤ a.1) (hp : nonnegativeDelays p) : nonnegativeDelays (shift a p) := by
  intro b hb
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
  exact add_nonneg ha (hp c hc)

private theorem nonnegative_append (p q : Terms)
    (hp : nonnegativeDelays p) (hq : nonnegativeDelays q) : nonnegativeDelays (p ++ q) := by
  intro a ha
  exact (List.mem_append.mp ha).elim (hp a) (hq a)

private theorem nonnegative_mul (p q : Terms)
    (hp : nonnegativeDelays p) (hq : nonnegativeDelays q) : nonnegativeDelays (mul p q) := by
  induction p with
  | nil => simp [mul, nonnegativeDelays]
  | cons a p ih =>
    apply nonnegative_append
    · exact nonnegative_shift a q (hp a (by simp)) hq
    · exact ih (fun b hb => hp b (by simp [hb]))

theorem response_nonnegative (q : ℝ) (H W : Terms) (K : ℕ)
    (hH : nonnegativeDelays H) (hW : nonnegativeDelays W) :
    nonnegativeDelays (response q H W K) := by
  have hinit := nonnegative_shift (0, -(1 - (q : ℂ))) W (le_refl 0) hW
  induction K with
  | zero => exact hinit
  | succ K ih =>
    apply nonnegative_append _ _ hinit
    apply nonnegative_mul _ _ hH
    exact nonnegative_append _ _ (by simp [constant, nonnegativeDelays]) ih

theorem complete_nonnegative (ps : List Terms)
    (hp : ∀ p ∈ ps, nonnegativeDelays p) : nonnegativeDelays (complete ps) := by
  induction ps with
  | nil => simp [complete, nonnegativeDelays]
  | cons p ps ih =>
    have h := hp p (by simp)
    have ht := ih (fun q hq => hp q (by simp [hq]))
    exact nonnegative_append _ _ (nonnegative_append _ _ h ht) (nonnegative_mul _ _ h ht)

theorem average_nonnegative {ι : Type*} (T : Finset ι) (w : ι → ℝ) (p : ι → Terms)
    (hp : ∀ i ∈ T, nonnegativeDelays (p i)) : nonnegativeDelays (average T w p) := by
  intro a ha
  obtain ⟨i, hi, hai⟩ := List.mem_flatMap.mp ha
  exact nonnegative_shift _ _ (le_refl 0) (hp i (Finset.mem_toList.mp hi)) a hai

end FiniteResponse

open FiniteResponse ProbeEuler

def principalBaseTerms (Q : ℝ) (A eta : ℂ) : Terms :=
  [(6 * Real.log Q, A * (Q : ℂ) ^ 2),
   (Real.log Q, (1 - (Q : ℂ)⁻¹) * eta)]

def principalWeightTerms (Q : ℝ) (A eta : ℂ) : Terms :=
  [(5 * Real.log Q, A * star eta * (Q : ℂ) ^ 3)]

def principalResponseTerms (K : ℕ) (Q : ℝ) (A eta : ℂ) : Terms :=
  response Q⁻¹ (principalBaseTerms Q A eta) (principalWeightTerms Q A eta) K

private theorem positive_cpow (Q : ℝ) (hQ : 0 < Q) (s : ℂ) :
    (Q : ℂ) ^ s = Complex.exp ((Real.log Q : ℂ) * s) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hQ.ne'),
    ← Complex.ofReal_log hQ.le]

/-- The log-labelled atoms are literal positive Mellin delays. -/
theorem response_atom_eval_delay (a : Atom) (s : ℂ) :
    evalAtom s a = a.2 * (Real.exp a.1 : ℂ) ^ (-s) := by
  rw [evalAtom, positive_cpow _ (Real.exp_pos _) _, Real.log_exp]
  congr 2
  ring

theorem response_atom_mass_delay (a : Atom) (theta : ℝ) :
    massAtom theta a = ‖a.2‖ * (Real.exp a.1) ^ (-theta) := by
  rw [massAtom, ← Real.exp_mul]
  congr 2
  ring

theorem principal_base_terms_eval (Q : ℝ) (hQ : 0 < Q) (A eta s : ℂ) :
    eval s (principalBaseTerms Q A eta) = principalResponseBase Q A eta s := by
  have hc : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  have hpow : (Q : ℂ) ^ (4 - 6 * s - 6 * (1 / 6)) =
      (Q : ℂ) ^ 3 * Complex.exp (-(6 * (Real.log Q : ℂ)) * s) := by
    rw [show (4 - 6 * s - 6 * (1 / 6) : ℂ) = 3 + (-6 * s) by ring,
      Complex.cpow_add _ _ hc, Complex.cpow_ofNat, positive_cpow Q hQ]
    congr 2
    ring
  simp only [principalBaseTerms, eval, evalAtom, principalResponseBase,
    coordR, coordD, star_one, mul_one, hpow, positive_cpow Q hQ,
    Complex.ofReal_mul, Complex.ofReal_ofNat, add_zero]
  rw [show (Real.log Q : ℂ) * -s = -(Real.log Q : ℂ) * s by ring]
  field_simp

theorem principal_weight_terms_eval (Q : ℝ) (hQ : 0 < Q) (A eta s : ℂ) :
    eval s (principalWeightTerms Q A eta) = principalResponseWeight Q A eta s := by
  have hc : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  have hpow : (Q : ℂ) ^ s * (Q : ℂ) ^ (4 - 6 * s - 6 * (1 / 6)) =
      (Q : ℂ) ^ 3 * Complex.exp (-(5 * (Real.log Q : ℂ)) * s) := by
    rw [← Complex.cpow_add _ _ hc,
      show s + (4 - 6 * s - 6 * (1 / 6)) = 3 + (-5 * s) by ring,
      Complex.cpow_add _ _ hc, Complex.cpow_ofNat, positive_cpow Q hQ]
    congr 2
    ring
  simp only [principalWeightTerms, eval, evalAtom, principalResponseWeight,
    coordR, Complex.ofReal_mul, Complex.ofReal_ofNat, add_zero]
  calc
    _ = A * star eta * ((Q : ℂ) ^ 3 *
        Complex.exp (-(5 * (Real.log Q : ℂ)) * s)) := by ring
    _ = _ := by rw [← hpow]; ring

/-- Exact signed original finite slot, on every complex argument. -/
theorem principal_response_terms_eval (K : ℕ) (Q : ℝ) (hQ : 0 < Q)
    (A eta s : ℂ) :
    1 + eval s (principalResponseTerms K Q A eta) = principalSlotPartial K Q A eta s := by
  rw [principalResponseTerms, response_eval, principal_base_terms_eval Q hQ,
    principal_weight_terms_eval Q hQ]
  simp only [principalSlotPartial, Complex.ofReal_inv]

def principalMassBase (Q theta : ℝ) : ℝ := Q ^ (2 - 6 * theta) + Q ^ (-theta)
def principalMassWeight (Q theta : ℝ) : ℝ := Q ^ (3 - 5 * theta)

private theorem power_exp (Q : ℝ) (hQ : 0 < Q) (n : ℕ) (v theta : ℝ) :
    Q ^ n * Real.exp (-(v * Real.log Q) * theta) = Q ^ ((n : ℝ) - v * theta) := by
  rw [← Real.rpow_natCast Q n, Real.rpow_def_of_pos hQ, ← Real.exp_add,
    Real.rpow_def_of_pos hQ]
  congr 1
  ring

theorem principal_terms_mass_bounds (Q theta : ℝ) (hQ : 1 ≤ Q) (A eta : ℂ)
    (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) :
    mass theta (principalBaseTerms Q A eta) ≤ principalMassBase Q theta ∧
    mass theta (principalWeightTerms Q A eta) ≤ principalMassWeight Q theta := by
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hq0 : 0 ≤ Q⁻¹ := inv_nonneg.mpr hQ0.le
  have hq1 : Q⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hQ
  have hnorm : ‖1 - (Q : ℂ)⁻¹‖ = 1 - Q⁻¹ := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hq1)]
  have hnQ : ‖(Q : ℂ)‖ = Q := by simp [Complex.norm_real, abs_of_pos hQ0]
  have hA2 : ‖A‖ * Q ^ 2 ≤ Q ^ 2 := mul_le_of_le_one_left (sq_nonneg Q) hA
  have hqe : (1 - Q⁻¹) * ‖eta‖ ≤ 1 := by
    calc
      _ ≤ (1 - Q⁻¹) * 1 := mul_le_mul_of_nonneg_left heta (sub_nonneg.mpr hq1)
      _ ≤ 1 := by nlinarith
  have hAe : ‖A‖ * ‖eta‖ ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hA) (norm_nonneg eta)]
  constructor
  · simp only [principalBaseTerms, mass, massAtom, norm_mul, norm_pow, hnQ,
      hnorm, add_zero]
    calc
      _ ≤ Q ^ 2 * Real.exp (-(6 * Real.log Q) * theta) + Real.exp (-Real.log Q * theta) := by
        exact add_le_add (mul_le_mul_of_nonneg_right hA2 (Real.exp_pos _).le)
          (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hqe (Real.exp_pos _).le)
      _ = principalMassBase Q theta := by
        rw [power_exp Q hQ0 2 6 theta]
        congr 1
        rw [Real.rpow_def_of_pos hQ0]
        congr 1
        ring
  · simp only [principalWeightTerms, mass, massAtom, norm_mul, norm_pow, norm_star,
      hnQ, add_zero]
    calc
      _ ≤ Q ^ 3 * Real.exp (-(5 * Real.log Q) * theta) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_of_le_one_left (pow_nonneg hQ0.le 3) hAe) (Real.exp_pos _).le
      _ = principalMassWeight Q theta := power_exp Q hQ0 3 5 theta

/-- A coefficient-mass estimate, not merely a bound on polynomial values.
The explicit scalar condition is geometric convergence, not an assumed source bound. -/
theorem principal_response_terms_mass_le (K : ℕ) (Q theta : ℝ) (hQ : 1 ≤ Q)
    (A eta : ℂ) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1)
    (hr : principalMassBase Q theta < 1) :
    mass theta (principalResponseTerms K Q A eta) ≤
      (1 - Q⁻¹) * (principalMassBase Q theta + principalMassWeight Q theta) /
        (1 - principalMassBase Q theta) := by
  have hQ0 : 0 ≤ Q := le_trans zero_le_one hQ
  obtain ⟨hH, hW⟩ := principal_terms_mass_bounds Q theta hQ A eta hA heta
  apply response_mass_le Q⁻¹ _ _ K theta _ _ (inv_nonneg.mpr hQ0)
    (inv_le_one_of_one_le₀ hQ) _ hr _ hH hW
  · unfold principalMassBase
    positivity
  · unfold principalMassWeight
    positivity

/-- A common explicit bound for every moving pool element Q>=P. -/
theorem principal_response_terms_mass_uniform (K : ℕ) (P Q theta : ℝ)
    (hP : 1 ≤ P) (hQ : P ≤ Q) (htheta : 3 / 5 ≤ theta)
    (A eta : ℂ) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1)
    (hr : principalMassBase P theta ≤ 1 / 2) :
    mass theta (principalResponseTerms K Q A eta) ≤
      2 * (principalMassBase P theta + principalMassWeight P theta) := by
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hQ1 := hP.trans hQ
  have hQ0 : 0 ≤ Q := le_trans zero_le_one hQ1
  have hmono (e : ℝ) (he : e ≤ 0) : Q ^ e ≤ P ^ e :=
    Real.rpow_le_rpow_of_nonpos hP0 hQ he
  have hbase : principalMassBase Q theta ≤ principalMassBase P theta := by
    unfold principalMassBase
    exact add_le_add (hmono _ (by linarith)) (hmono _ (by linarith))
  have hweight : principalMassWeight Q theta ≤ principalMassWeight P theta :=
    hmono _ (by linarith)
  have hr0 : 0 ≤ principalMassBase P theta := by unfold principalMassBase; positivity
  have hw0 : 0 ≤ principalMassWeight P theta := by unfold principalMassWeight; positivity
  obtain ⟨hH, hW⟩ := principal_terms_mass_bounds Q theta hQ1 A eta hA heta
  have hbound := response_mass_le Q⁻¹ (principalBaseTerms Q A eta)
    (principalWeightTerms Q A eta) K theta (principalMassBase P theta)
    (principalMassWeight P theta) (inv_nonneg.mpr hQ0)
    (inv_le_one_of_one_le₀ hQ1) hr0 (by linarith) hw0
    (hH.trans hbase) (hW.trans hweight)
  apply hbound.trans
  apply (div_le_iff₀ (by linarith : 0 < 1 - principalMassBase P theta)).mpr
  have hq0 : 0 ≤ Q⁻¹ := inv_nonneg.mpr hQ0
  nlinarith [mul_nonneg hq0 (add_nonneg hr0 hw0),
    mul_nonneg (sub_nonneg.mpr hr) (add_nonneg hr0 hw0)]

def principalProductResponseTerms {κ ι : Type*} (K : ℕ) (S : Finset κ)
    (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A eta : κ → ι → ℂ) : Terms :=
  complete (S.toList.map (fun j => average (T j) (w j)
    (fun i => principalResponseTerms K (Q j i) (A j i) (eta j i))))

/-- Finite labelled expansion of the COMPLETE original weighted product. -/
theorem principal_product_response_terms_eval {κ ι : Type*} (K : ℕ) (S : Finset κ)
    (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A eta : κ → ι → ℂ) (s : ℂ)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, 0 < Q j i)
    (hM : ∀ j ∈ S, (∑ i ∈ T j, w j i) ≠ 0) :
    1 + eval s (principalProductResponseTerms K S T w Q A eta) =
      ∏ j ∈ S, (∑ i ∈ T j, (w j i : ℂ) *
        principalSlotPartial K (Q j i) (A j i) (eta j i) s) /
          (∑ i ∈ T j, w j i : ℝ) := by
  rw [principalProductResponseTerms, complete_eval, List.map_map]
  simp only [Function.comp_apply, Finset.prod_map_toList]
  apply Finset.prod_congr rfl
  intro j hj
  rw [average_eval _ _ _ s (hM j hj)]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [principal_response_terms_eval K _ (hQ j hj i hi)]

/-- Every cross-slot term survives; the bound has no truncation-order or
moving-pool-cardinality factor. Its scalar right side tends to zero for theta>3/5. -/
theorem principal_product_response_terms_mass {κ ι : Type*} (K : ℕ) (S : Finset κ)
    (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A eta : κ → ι → ℂ)
    (P theta : ℝ) (hP : 1 ≤ P) (htheta : 3 / 5 ≤ theta)
    (hr : principalMassBase P theta ≤ 1 / 2)
    (hw : ∀ j ∈ S, ∀ i ∈ T j, 0 ≤ w j i)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, P ≤ Q j i)
    (hA : ∀ j ∈ S, ∀ i ∈ T j, ‖A j i‖ ≤ 1)
    (heta : ∀ j ∈ S, ∀ i ∈ T j, ‖eta j i‖ ≤ 1)
    (hM : ∀ j ∈ S, 0 < ∑ i ∈ T j, w j i) :
    mass theta (principalProductResponseTerms K S T w Q A eta) ≤
      (1 + 2 * (principalMassBase P theta + principalMassWeight P theta)) ^ S.card - 1 := by
  have hP0 : 0 ≤ P := le_trans zero_le_one hP
  apply (complete_mass_le _ theta (2 * (principalMassBase P theta + principalMassWeight P theta)) (by
    unfold principalMassBase principalMassWeight
    positivity) ?_).trans_eq (by simp)
  intro p hp
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
  have hjS := Finset.mem_toList.mp hj
  apply average_mass_le _ _ _ theta _ (hw j hjS) (hM j hjS)
  intro i hi
  exact principal_response_terms_mass_uniform K P (Q j i) theta hP (hQ j hjS i hi)
    htheta (A j i) (eta j i) (hA j hjS i hi) (heta j hjS i hi) hr

theorem principal_product_response_delays {κ ι : Type*} (K : ℕ) (S : Finset κ)
    (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A eta : κ → ι → ℂ)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, 1 ≤ Q j i) :
    nonnegativeDelays (principalProductResponseTerms K S T w Q A eta) := by
  apply complete_nonnegative
  intro p hp
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
  apply average_nonnegative
  intro i hi
  have hl := Real.log_nonneg (hQ j (Finset.mem_toList.mp hj) i hi)
  apply response_nonnegative
  · change nonnegativeDelays [(6 * Real.log (Q j i), _), (Real.log (Q j i), _)]
    intro a ha
    rcases List.mem_cons.mp ha with ha | ha
    · subst a
      exact mul_nonneg (by norm_num) hl
    · have ha' := List.mem_singleton.mp ha
      subst a
      exact hl
  · simp only [principalWeightTerms, nonnegativeDelays, List.mem_singleton]
    intro a ha
    subst a
    exact mul_nonneg (by norm_num) hl

/-- The labelled response approximates the original negative-normalized
principal source, not a surrogate polynomial chosen to satisfy a norm bound. -/
theorem principal_product_response_original_error {κ ι : Type*} (K : ℕ) (S : Finset κ)
    (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A eta : κ → ι → ℂ)
    (s : ℂ) (P : ℝ) (hP : 480 ≤ P) (hs : 7 / 8 ≤ s.re)
    (hw : ∀ j ∈ S, ∀ i ∈ T j, 0 ≤ w j i)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, P ≤ Q j i)
    (hA : ∀ j ∈ S, ∀ i ∈ T j, ‖A j i‖ ≤ 1)
    (heta : ∀ j ∈ S, ∀ i ∈ T j, ‖eta j i‖ = 1)
    (hM : ∀ j ∈ S, 0 < ∑ i ∈ T j, w j i) :
    ‖(∏ j ∈ S, ∑ i ∈ T j, (w j i : ℂ) * principalSlot (Q j i) (A j i) (eta j i) s) /
          principalScalar S (fun j => ∑ i ∈ T j, w j i) -
        (1 + eval s (principalProductResponseTerms K S T w Q A eta))‖ ≤
      S.card * (5 : ℝ) ^ S.card * (4 * (2 * P ^ (-(7 / 8 : ℝ))) ^ (K + 1)) := by
  rw [principal_product_response_terms_eval K S T w Q A eta s
    (fun j hj i hi => lt_of_lt_of_le (by linarith) (hQ j hj i hi))
    (fun j hj => (hM j hj).ne')]
  exact weighted_principal_product_partial_error S T w Q A eta s P K hP hs hw hQ hA heta hM

/-- The explicit common coefficient majorant vanishes at every fixed theta>3/5.
This limit is independent of K and does not assume any bound on the signal. -/
theorem principal_response_mass_majorant_tendsto (N : ℕ) (theta : ℝ)
    (htheta : 3 / 5 < theta) :
    Filter.Tendsto (fun P : ℝ =>
      (1 + 2 * (principalMassBase P theta + principalMassWeight P theta)) ^ N - 1)
      Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun P : ℝ => P ^ (2 - 6 * theta)) Filter.atTop (nhds 0) := by
    convert Real.tendsto_rpow_neg_atTop (by linarith : 0 < 6 * theta - 2) using 1 <;>
      congr 1 <;> ring
  have h2 := Real.tendsto_rpow_neg_atTop (by linarith : 0 < theta)
  have h3 : Filter.Tendsto (fun P : ℝ => P ^ (3 - 5 * theta)) Filter.atTop (nhds 0) := by
    convert Real.tendsto_rpow_neg_atTop (by linarith : 0 < 5 * theta - 3) using 1 <;>
      congr 1 <;> ring
  have hc1 : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    Filter.tendsto_const_nhds
  have hc2 : Filter.Tendsto (fun _ : ℝ => (2 : ℝ)) Filter.atTop (nhds 2) :=
    Filter.tendsto_const_nhds
  have h := ((hc1.add (hc2.mul ((h1.add h2).add h3))).pow N).sub hc1
  simpa only [principalMassBase, principalMassWeight, add_zero, mul_zero,
    one_pow, sub_self] using h

/-- The scalar geometric gate is eventually paid at exactly the same theta. -/
theorem principal_response_mass_gate_eventually (theta : ℝ) (htheta : 3 / 5 < theta) :
    ∀ᶠ P : ℝ in Filter.atTop, 1 ≤ P ∧ principalMassBase P theta ≤ 1 / 2 := by
  have h1 : Filter.Tendsto (fun P : ℝ => P ^ (2 - 6 * theta)) Filter.atTop (nhds 0) := by
    convert Real.tendsto_rpow_neg_atTop (by linarith : 0 < 6 * theta - 2) using 1 <;>
      congr 1 <;> ring
  have h2 := Real.tendsto_rpow_neg_atTop (by linarith : 0 < theta)
  have hsum : Filter.Tendsto (fun P : ℝ => principalMassBase P theta)
      Filter.atTop (nhds 0) := by simpa [principalMassBase] using h1.add h2
  exact (Filter.eventually_ge_atTop 1).and
    (hsum.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2))

end SevenEighths.PrincipalSlotEstimate
end
end OAI

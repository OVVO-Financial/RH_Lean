import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.Weight
import RHLean.Geometry.NativeThetaInvariantDerivatives

/-!
# Mixed principal symbols of the native invariant column operator

On a germ vanishing below order N, the order-N coordinate invariant
derivative measures the full coefficient with the product of its
individual exponent factorials. This uses the Jacobian of the original
formal group. The final identity retains the source gauge.
-/

set_option autoImplicit false

noncomputable section

namespace RHLean.Geometry.NativeTheta.InvariantPrincipalSymbol

open MvPowerSeries FormalCalculus JetEvaluation

variable {R σ : Type} [CommRing R]

/-- Vanishing of the strictly lower homogeneous pieces of a formal germ. -/
def VanishesBelow (n : ℕ) (f : MvPowerSeries σ R) : Prop :=
  ∀ b : σ →₀ ℕ, b.degree < n → coeff b f = 0

/-- At the first possible degree, a multiplier contributes its constant term. -/
theorem coeff_mul_leading (a : σ →₀ ℕ) (t f : MvPowerSeries σ R)
    (hf : VanishesBelow a.degree f) :
    coeff a (t * f) = constantCoeff t * coeff a f := by
  classical
  rw [coeff_mul, Finset.sum_eq_single (0, a)]
  · rw [coeff_zero_eq_constantCoeff_apply]
  · rintro ⟨b, c⟩ hbc hne
    have he : b + c = a := Finset.HasAntidiagonal.mem_antidiagonal.mp hbc
    have hb : b ≠ 0 := by
      rintro rfl
      have hc : c = a := by simpa only [zero_add] using he
      exact hne (Prod.ext rfl hc)
    have hpos : b.degree ≠ 0 := fun h => hb ((Finsupp.degree_eq_zero_iff b).mp h)
    have hsum : b.degree + c.degree = a.degree := by
      rw [← map_add, he]
    rw [hf c (by omega), mul_zero]
  · simp

private theorem vanishes_mul (n : ℕ) (f t : MvPowerSeries σ R) (hf : VanishesBelow n f) :
    VanishesBelow n (f * t) := by
  intro a ha
  rw [mul_comm f t, coeff_mul_leading a t f (fun b hb => hf b (hb.trans ha)),
    hf a ha, mul_zero]

/-- The product of the factorials of a full coordinate multiindex. -/
def factorialWeight [Fintype σ] (a : σ →₀ ℕ) : ℕ := ∏ j, (a j).factorial

private theorem factorialWeight_step [Fintype σ] (a : σ →₀ ℕ) (j : σ) :
    factorialWeight (a + Finsupp.single j 1) = (a j + 1) * factorialWeight a := by
  classical
  have ht (k : σ) : ((a + Finsupp.single j 1 : σ →₀ ℕ) k).factorial =
      (if k = j then a k + 1 else 1) * (a k).factorial := by
    by_cases hk : k = j
    · subst k
      rw [Finsupp.add_apply, Finsupp.single_eq_same, ite_eq_left rfl, Nat.factorial_succ]
    · rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hk, Nat.add_zero, ite_eq_right hk, one_mul]
  simp only [factorialWeight, ht, Finset.prod_mul_distrib, Fintype.prod_ite_eq']

variable {d : ℕ}
private abbrev Coord (d : ℕ) := Fin 1 × Fin d

private def step (G : FormalGroup R d) (j : Coord d) (f : PS R 1 d) : PS R 1 d :=
  directionalDerivative G.F (Pi.single j.2 1) f

private theorem coeff_step (G : FormalGroup R d) (j : Coord d) (a : Coord d →₀ ℕ)
    (f : PS R 1 d) (hf : VanishesBelow (a.degree + 1) f) :
    coeff a (step G j f) = coeff (a + Finsupp.single j 1) f * ((a j : R) + 1) := by
  classical
  have hpartial (k : Coord d) : VanishesBelow a.degree (pderiv k f) := by
    intro b hb
    rw [coeff_pderiv, hf (b + Finsupp.single k 1) (by
      rw [map_add, Finsupp.degree_single]
      omega), zero_mul]
  have hc (k : Fin d) :
      constantCoeff (co G (Pi.single j.2 1) ((0 : Fin 1), k)) =
        (Pi.single j.2 (1 : R) : Fin d → R) k := by
    simp [co, cc_jac', mul_ite]
  obtain ⟨j₀, j⟩ := j
  have h₀ : j₀ = 0 := Subsingleton.elim _ _
  subst j₀
  simp only [step, dof_vf, vf, Fintype.sum_prod_type, Fin.sum_univ_one, map_sum]
  simp only [coeff_mul_leading a _ _ (hpartial _), hc, coeff_pderiv]
  simp [Pi.single_apply, ite_mul]

private theorem vanishes_step (G : FormalGroup R d) (j : Coord d) (n : ℕ)
    (f : PS R 1 d) (hf : VanishesBelow (n + 1) f) :
    VanishesBelow n (step G j f) := by
  intro a ha
  rw [coeff_step G j a f (fun b hb => hf b (by omega)),
    hf (a + Finsupp.single j 1) (by rw [map_add, Finsupp.degree_single]; omega), zero_mul]

private def profile (w : List σ) : σ →₀ ℕ := (w.map (fun j => Finsupp.single j 1)).sum

private theorem profile_cons (j : σ) (w : List σ) :
    profile (j :: w) = Finsupp.single j 1 + profile w := by
  simp only [profile, List.map_cons, List.sum_cons]

private theorem vanishes_word (G : FormalGroup R d) (w : List (Coord d))
    (n : ℕ) (f : PS R 1 d) (hf : VanishesBelow (n + w.length) f) :
    VanishesBelow n (w.foldr (step G) f) := by
  induction w generalizing n with
  | nil => simpa using hf
  | cons j w ih =>
    apply vanishes_step
    apply ih
    have he : (n + 1) + w.length = n + (j :: w).length := by
      simp only [List.length_cons]
      omega
    rwa [he]

private theorem principal_word (G : FormalGroup R d) (w : List (Coord d))
    (a : Coord d →₀ ℕ) (f : PS R 1 d) (hf : VanishesBelow (a.degree + w.length) f) :
    (factorialWeight a : R) * coeff a (w.foldr (step G) f) =
      (factorialWeight (a + profile w) : R) * coeff (a + profile w) f := by
  induction w generalizing a with
  | nil => simp [profile]
  | cons j w ih =>
    have hd : (a.degree + 1) + w.length = a.degree + (j :: w).length := by
      simp only [List.length_cons]
      omega
    have hv : VanishesBelow (a.degree + 1) (w.foldr (step G) f) :=
      vanishes_word G w (a.degree + 1) f (hd.symm ▸ hf)
    have hd' : (a + Finsupp.single j 1).degree + w.length = a.degree + (j :: w).length := by
      rwa [map_add, Finsupp.degree_single]
    calc
      _ = (factorialWeight (a + Finsupp.single j 1) : R) *
            coeff (a + Finsupp.single j 1) (w.foldr (step G) f) := by
        rw [List.foldr_cons, coeff_step G j a _ hv, factorialWeight_step, Nat.cast_mul,
          Nat.cast_add, Nat.cast_one]
        ring
      _ = _ := by
        rw [ih (a + Finsupp.single j 1) (hd'.symm ▸ hf), profile_cons, add_assoc]

private theorem native_word (G : FormalGroup R d) (a : Coord d →₀ ℕ)
    (s : List (Coord d)) (f : PS R 1 d) :
    s.foldr (fun j y => (step G j)^[a j] y) f =
      (s.flatMap (fun j => List.replicate (a j) j)).foldr (step G) f := by
  have hrep (j : Coord d) (n : ℕ) (y : PS R 1 d) :
      (List.replicate n j).foldr (step G) y = (step G j)^[n] y := by
    induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ, List.foldr_cons, ih, Function.iterate_succ_apply']
  induction s with
  | nil => rfl
  | cons j s ih =>
    rw [List.foldr_cons, List.flatMap_cons, List.foldr_append, hrep, ih]

private theorem profile_native [Fintype σ] (a : σ →₀ ℕ) :
    profile ((Finset.univ : Finset σ).toList.flatMap (fun j => List.replicate (a j) j)) = a := by
  classical
  have hp (s : List σ) :
      profile (s.flatMap (fun j => List.replicate (a j) j)) =
        (s.map (fun j => Finsupp.single j (a j))).sum := by
    have hs (j : σ) : a j • (Finsupp.single j 1 : σ →₀ ℕ) = Finsupp.single j (a j) := by
      ext k
      by_cases hk : j = k <;> simp [hk]
    induction s with
    | nil => rfl
    | cons j s ih =>
      simp only [List.flatMap_cons, profile, List.map_append, List.sum_append,
        List.map_replicate, List.sum_replicate, List.map_cons, List.sum_cons, hs]
      exact congrArg (fun v => Finsupp.single j (a j) + v) ih
  rw [hp, Finset.sum_map_toList, Finsupp.univ_sum_single]

private theorem degree_profile (w : List σ) : (profile w).degree = w.length := by
  induction w with
  | nil => simp [profile]
  | cons j w ih => simp only [profile_cons, map_add, Finsupp.degree_single, ih, List.length_cons, Nat.add_comm 1]

/-- On the degree slice the original normalized coordinate directions see
every repeated exponent with its own factorial. No inversion is required. -/
theorem monomialDerivative_principal (G : FormalGroup R d)
    (a : Fin 1 × Fin d →₀ ℕ) (f : PS R 1 d) (hf : VanishesBelow a.degree f) :
    constantCoeff (monomialDerivative G.F (fun j : Fin 1 × Fin d => Pi.single j.2 1) a f) =
      (factorialWeight a : R) * coeff a f := by
  classical
  let s := (Finset.univ : Finset (Coord d)).toList
  let w := s.flatMap (fun j => List.replicate (a j) j)
  have hp : profile w = a := profile_native a
  have hn : w.length = a.degree := (degree_profile w).symm.trans (congrArg Finsupp.degree hp)
  have h := principal_word G w 0 f (by simpa only [map_zero, zero_add, hn] using hf)
  simp only [zero_add, hp, coeff_zero_eq_constantCoeff_apply, factorialWeight,
    Finsupp.zero_apply, Nat.factorial_zero, Finset.prod_const_one, Nat.cast_one, one_mul] at h
  change constantCoeff (s.foldr (fun j y => (step G j)^[a j] y) f) = _
  rw [native_word]
  exact h

/-- The actual gauge-corrected column on any germ vanishing below the
specified degree. Its homogeneous coefficient and the gauge factor remain
visible, in the same chart and with the same exponent multiplicities. -/
theorem formalColumnJet_principal [Algebra ℚ R] (G : FormalGroup R d)
    (actW0 : Fin d → PS R 1 d) (φ : PS R 2 d) (m : ℕ) (a : Fin 1 × Fin d →₀ ℕ)
    (f : PS R 1 d) (hf : VanishesBelow a.degree f) :
    formalColumnJet G.F actW0 φ m f (fun j : Fin 1 × Fin d => Pi.single j.2 1) a =
      (factorialWeight a : R) * coeff a f *
        constantCoeff (exponentialSeries ((m : R) • lineGauge actW0 φ)) := by
  let t := exponentialSeries ((m : R) • lineGauge actW0 φ)
  change constantCoeff (monomialDerivative G.F _ a (f * t)) = _
  rw [monomialDerivative_principal G a (f * t) (vanishes_mul a.degree f t hf),
    mul_comm f t, coeff_mul_leading a t f hf]
  change (factorialWeight a : R) * (constantCoeff t * coeff a f) =
    (factorialWeight a : R) * coeff a f * constantCoeff t
  ring

end RHLean.Geometry.NativeTheta.InvariantPrincipalSymbol

end

/-!
# Leading powers in the original invariant column jets

If a germ has the form g^k h with g vanishing at the identity, a word
of k invariant derivatives evaluates to k! times the product of the
directional linear coefficients of g and the value of h. The proof
uses the given formal group and retains every exponent and the original
gauge of the column operator.
-/

set_option autoImplicit false

noncomputable section

namespace RHLean.Geometry.NativeTheta.InvariantLeadingJets

open MvPowerSeries FormalCalculus JetEvaluation

variable {R : Type} [CommRing R] {d : ℕ}

/-- The first homogeneous coefficient of an actual germ in direction v. -/
def tangentCoefficient (v : Fin d → R) (g : PS R 1 d) : R :=
  ∑ j, v j * coeff (Finsupp.single ((0 : Fin 1), j) 1) g

theorem constantCoeff_directionalDerivative (G : FormalGroup R d) (v : Fin d → R)
    (g : PS R 1 d) :
    constantCoeff (directionalDerivative G.F v g) = tangentCoefficient v g := by
  classical
  have hc (j : Fin d) : constantCoeff (co G v ((0 : Fin 1), j)) = v j := by
    simp [co, cc_jac', mul_ite]
  have hp (j : Fin d) : constantCoeff (pderiv ((0 : Fin 1), j) g) =
      coeff (Finsupp.single ((0 : Fin 1), j) 1) g := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
    simp
  rw [dof_vf]
  simp only [vf, Fintype.sum_prod_type, Fin.sum_univ_one, map_sum, map_mul,
    hc, hp, tangentCoefficient]

private theorem leibniz_power_factor {A : Type} [CommRing A] (D : A → A)
    (hD : ∀ a b, D (a * b) = D a * b + a * D b) (g h : A) (k : ℕ) :
    D (g ^ (k + 1) * h) =
      g ^ k * ((((k + 1 : ℕ) : A) * D g) * h + g * D h) := by
  have hd (n : ℕ) : D (g ^ (n + 1)) = ((n + 1 : ℕ) : A) * g ^ n * D g := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ g (n + 1), hD, ih]
      simp only [Nat.cast_succ, pow_succ g n]
      ring
  rw [hD, hd, pow_succ g k]
  ring

private theorem word_leading (G : FormalGroup R d) (g : PS R 1 d)
    (hg : constantCoeff g = 0) (w : List (Fin d → R)) (h : PS R 1 d) :
    constantCoeff (w.foldl (fun f v => directionalDerivative G.F v f) (g ^ w.length * h)) =
      (w.length.factorial : R) * (w.map (fun v => tangentCoefficient v g)).prod *
        constantCoeff h := by
  induction w generalizing h with
  | nil => simp
  | cons v w ih =>
    have hD (a b : PS R 1 d) : directionalDerivative G.F v (a * b) =
        directionalDerivative G.F v a * b + a * directionalDerivative G.F v b := by
      simp only [dof_vf, vf_mul]
    simp only [List.length_cons, List.foldl_cons, List.map_cons, List.prod_cons]
    rw [leibniz_power_factor _ hD g h w.length, ih]
    simp only [map_add, map_mul, map_natCast, constantCoeff_directionalDerivative,
      hg, zero_mul, add_zero, Nat.factorial_succ, Nat.cast_mul]
    ring

variable {ι : Type}

private def word (u : ι → Fin d → R) (a : ι →₀ ℕ) : List ι → List (Fin d → R)
  | [] => []
  | i :: s => word u a s ++ List.replicate (a i) (u i)

omit [CommRing R] in
private theorem word_length (u : ι → Fin d → R) (a : ι →₀ ℕ) (s : List ι) :
    (word u a s).length = (s.map (fun i => a i)).sum := by
  induction s with
  | nil => rfl
  | cons i s ih => simp [word, ih, Nat.add_comm]

private theorem word_product (u : ι → Fin d → R) (a : ι →₀ ℕ) (s : List ι)
    (q : (Fin d → R) → R) :
    ((word u a s).map q).prod = (s.map (fun i => q (u i) ^ a i)).prod := by
  induction s with
  | nil => rfl
  | cons i s ih => simp [word, ih, mul_comm]

private theorem word_fold (G : FormalGroup R d) (u : ι → Fin d → R) (a : ι →₀ ℕ)
    (s : List ι) (f : PS R 1 d) :
    s.foldr (fun i z => (directionalDerivative G.F (u i))^[a i] z) f =
      (word u a s).foldl (fun z v => directionalDerivative G.F v z) f := by
  have hrep (v : Fin d → R) (n : ℕ) (z : PS R 1 d) :
      (List.replicate n v).foldl (fun b w => directionalDerivative G.F w b) z =
        (directionalDerivative G.F v)^[n] z := by
    induction n generalizing z with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ, List.foldl_cons, ih, Function.iterate_succ_apply]
  induction s with
  | nil => rfl
  | cons i s ih => rw [List.foldr_cons, word, List.foldl_append, hrep, ih]

/-- The original ordered row operator on a pure leading power, with every
direction repeated according to its exponent. This identity holds over
the coefficient ring before cancelling any factorial. -/
theorem monomialDerivative_leading [Fintype ι] (G : FormalGroup R d)
    (u : ι → Fin d → R) (a : ι →₀ ℕ) (g h : PS R 1 d) (hg : constantCoeff g = 0) :
    constantCoeff (monomialDerivative G.F u a (g ^ (∑ i, a i) * h)) =
      ((∑ i, a i).factorial : R) * (∏ i, tangentCoefficient (u i) g ^ a i) * constantCoeff h := by
  classical
  let s := (Finset.univ : Finset ι).toList
  have hn : (word u a s).length = ∑ i, a i := by
    rw [word_length, Finset.sum_map_toList]
  have hp : ((word u a s).map (fun v => tangentCoefficient v g)).prod =
      ∏ i, tangentCoefficient (u i) g ^ a i := by
    rw [word_product, Finset.prod_map_toList]
  have hand := word_leading G g hg (word u a s) h
  rw [hn, hp] at hand
  unfold monomialDerivative
  rw [word_fold G]
  exact hand

/-- The exact leading-power value of the actual gauge-corrected column.
The gauge on the residual germ is the same one that occurs in the
native finite theta formula. -/
theorem formalColumnJet_leading [Fintype ι] [Algebra ℚ R] (G : FormalGroup R d)
    (actW0 : Fin d → PS R 1 d) (φ : PS R 2 d) (m : ℕ) (u : ι → Fin d → R)
    (a : ι →₀ ℕ) (g h : PS R 1 d) (hg : constantCoeff g = 0) :
    formalColumnJet G.F actW0 φ m (g ^ (∑ i, a i) * h) u a =
      ((∑ i, a i).factorial : R) * (∏ i, tangentCoefficient (u i) g ^ a i) *
        constantCoeff (gaugedGerm actW0 φ m h) := by
  unfold formalColumnJet
  have he : gaugedGerm actW0 φ m (g ^ (∑ i, a i) * h) =
      g ^ (∑ i, a i) * gaugedGerm actW0 φ m h := by
    simp only [gaugedGerm, mul_assoc]
  rw [he, monomialDerivative_leading G u a g _ hg]

/-- One extra vanishing factor annihilates the whole gauge-corrected column test. -/
theorem formalColumnJet_zero_of_extra_factor [Fintype ι] [Algebra ℚ R] (G : FormalGroup R d)
    (actW0 : Fin d → PS R 1 d) (φ : PS R 2 d) (m : ℕ) (u : ι → Fin d → R)
    (a : ι →₀ ℕ) (g h : PS R 1 d) (hg : constantCoeff g = 0) :
    formalColumnJet G.F actW0 φ m (g ^ ((∑ i, a i) + 1) * h) u a = 0 := by
  rw [pow_succ g (∑ i, a i), mul_assoc, formalColumnJet_leading G actW0 φ m u a g _ hg]
  simp only [gaugedGerm, map_mul, hg, zero_mul, mul_zero]

end RHLean.Geometry.NativeTheta.InvariantLeadingJets

end

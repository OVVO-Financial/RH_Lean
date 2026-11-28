import Mathlib

/-! Real positive integral quadratic twists. Unlike Gaussian phases,
the selected roots are fixed by complex conjugation. The exact
rank-one norm ratio has reciprocal finite height on the original
physical depth direction. No signed asymptotic bound is asserted. -/

set_option autoImplicit false
noncomputable section

namespace RHLean.Analysis.NativePositiveTwist

def upper (n : ℕ) : ℝ := (2*(n:ℝ)+1+Real.sqrt (4*(n:ℝ)+1))/2
def lower (n : ℕ) : ℝ := (2*(n:ℝ)+1-Real.sqrt (4*(n:ℝ)+1))/2

theorem root_sum (n : ℕ) : upper n+lower n=2*(n:ℝ)+1 := by
  unfold upper lower
  ring

theorem root_product (n : ℕ) : upper n*lower n=(n:ℝ)^2 := by
  have h : Real.sqrt (4*(n:ℝ)+1)^2=4*(n:ℝ)+1 := Real.sq_sqrt (by positivity)
  unfold upper lower
  nlinarith only [h]

theorem upper_pos (n : ℕ) : 0 < upper n := by
  unfold upper
  positivity

theorem lower_pos (n : ℕ) (hn : 0 < n) : 0 < lower n := by
  have h : 0 < upper n*lower n := by rw [root_product]; positivity
  exact (mul_pos_iff_of_pos_left (upper_pos n)).mp h

theorem root_upper_le (n : ℕ) : lower n ≤ upper n := by
  unfold upper lower
  linarith only [Real.sqrt_nonneg (4*(n:ℝ)+1)]

theorem upper_quadratic (n : ℕ) :
    upper n^2-(2*(n:ℝ)+1)*upper n+(n:ℝ)^2=0 := by
  rw [← root_sum n,← root_product n]
  ring

theorem lower_quadratic (n : ℕ) :
    lower n^2-(2*(n:ℝ)+1)*lower n+(n:ℝ)^2=0 := by
  rw [← root_sum n,← root_product n]
  ring

/-- Monic integral equation on the actual positive norm scalars. -/
theorem root_integral (n : ℕ) :
    IsIntegral ℤ (upper n:ℂ) ∧ IsIntegral ℤ (lower n:ℂ) := by
  let p : Polynomial ℤ := Polynomial.X^2-
    (Polynomial.C (2*(n:ℤ)+1)*Polynomial.X-Polynomial.C ((n:ℤ)^2))
  have hm : p.Monic := by
    apply Polynomial.monic_X_pow_sub
    apply lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
    apply max_lt
    · exact (Polynomial.degree_C_mul_X_le _).trans_lt (by norm_num)
    · exact Polynomial.degree_C_le.trans_lt (by norm_num)
  have eval_eq (t : ℂ) : Polynomial.aeval t p = t^2 - (2*(n:ℂ)+1)*t + (n:ℂ)^2 := by
    change Polynomial.eval₂ (Int.castRingHom ℂ) t p = _
    simp only [p, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_mul,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    simp [sub_sub]
  refine ⟨⟨p,hm,?_⟩,⟨p,hm,?_⟩⟩
  · rw [eval_eq]
    exact_mod_cast upper_quadratic n
  · rw [eval_eq]
    exact_mod_cast lower_quadratic n

/-- At every embedding the two roots of the same monic equation are
integral; the chosen root is a unit. The companion root has exactly
the doubled valuation of the original depth. -/
theorem unit_root {K : Type*} [NormedField K] [IsUltrametricDist K]
    (a b N : K) (hs : a+b=2*N+1) (hp : a*b=N^2) (hN : ‖N‖≤1) :
    ‖a‖≤1 ∧ ‖b‖≤1 ∧ (‖a‖=1 ∨ ‖b‖=1) := by
  have hsum : ‖a+b‖≤1 := by
    rw [hs]
    calc
      _ ≤ max ‖(2:K)*N‖ ‖(1:K)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le (by
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg N)
          (by exact_mod_cast IsUltrametricDist.norm_natCast_le_one K 2)).trans hN) (by simp)
  have hprod : ‖a‖*‖b‖≤1 := by
    rw [← norm_mul,hp,norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hN
  have ha : ‖a‖≤1 := by
    by_contra! h
    have hb : ‖b‖≤1 := by
      by_contra! hb
      exact (not_lt_of_ge hprod) (by
        calc
          1 < ‖b‖ := hb
          _ ≤ ‖a‖*‖b‖ := le_mul_of_one_le_left (norm_nonneg b) h.le)
    have hh := IsUltrametricDist.norm_add_le_max (a+b) (-b)
    rw [add_neg_cancel_right,norm_neg] at hh
    exact h.not_ge (hh.trans (max_le hsum hb))
  have hb : ‖b‖≤1 := by
    by_contra! h
    have hh := IsUltrametricDist.norm_add_le_max (a+b) (-a)
    rw [show a+b+-a=b by abel,norm_neg] at hh
    exact h.not_ge (hh.trans (max_le hsum ha))
  refine ⟨ha,hb,?_⟩
  by_contra! h
  have hA := lt_of_le_of_ne ha h.1
  have hB := lt_of_le_of_ne hb h.2
  have hS : ‖a+b‖<1 := (IsUltrametricDist.norm_add_le_max a b).trans_lt (max_lt hA hB)
  by_cases hNu : ‖N‖=1
  · have eqn : ‖a‖*‖b‖=1 := by rw [← norm_mul,hp,norm_pow,hNu,one_pow]
    exact (ne_of_lt ((mul_le_of_le_one_left (norm_nonneg b) ha).trans_lt hB)) eqn
  · have hNt := lt_of_le_of_ne hN hNu
    have ht : ‖(2:K)*N‖<1 := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right
        (show ‖(2:K)‖≤1 by exact_mod_cast IsUltrametricDist.norm_natCast_le_one K 2)
        (norm_nonneg N)).trans_lt (by simpa using hNt)
    have h := IsUltrametricDist.norm_add_le_max (a+b) (-(2*N))
    rw [show a+b+-(2*N)=1 by rw [hs]; ring,norm_one,norm_neg] at h
    exact (not_lt_of_ge h) (max_lt hS ht)

theorem chosen_norm_ratio {K : Type*} [NormedField K]
    (N t : K) (ht : ‖t‖=1) :
    ‖(N/t)^2‖=‖N‖^2 ∧ ‖(t/N)^2‖=(‖N‖⁻¹)^2 := by
  simp [norm_pow,norm_div,ht,one_div]

/-- Independent physical line test: normalized indicator paired with
the scaled indicator, on the very same retained addresses. -/
theorem indicator_pair {I : Type*} [Fintype I]
    (t : ℝ) (h : 0 < Fintype.card I) :
    (∑ _i : I, (1/(Fintype.card I:ℝ))*t)=t := by
  have hn : (Fintype.card I:ℝ) ≠ 0 := by exact_mod_cast h.ne'
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  field_simp [hn]

theorem indicator_energy {I : Type*} [Fintype I]
    (h : 0 < Fintype.card I) :
    (∑ _i : I, (1/(Fintype.card I:ℝ))^2)=1/(Fintype.card I:ℝ) := by
  have hn : (Fintype.card I:ℝ) ≠ 0 := by exact_mod_cast h.ne'
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  field_simp [hn]

/-- The finite bill for a ratio of two independently fitted positive
depths is exactly the original signed rational factor, not an
additional directional gain. -/
theorem signed_ratio_norm {K : Type*} [NormedField K]
    (D E a b : K)
    (ha : ‖a‖=1) (hb : ‖b‖=1) :
    ‖((D/a)/(E/b))^2‖=‖(D/E)^2‖ := by
  simp [norm_pow,norm_div,ha,hb]

/-- The actual class average on a retained physical layer, with no
change of the original mask. Its scalar denominator is the class size. -/
def classProjector {I : Type*} [Fintype I] (y : I → ℂ) : I → ℂ :=
  fun _ => (∑ i, y i)/(Fintype.card I:ℂ)

theorem class_pair {I : Type*} [Fintype I] (h : 0 < Fintype.card I)
    (x y : I → ℂ) :
    (Fintype.card I:ℂ)*(∑ i, star (x i)*classProjector y i) =
      (∑ i, star (x i))*(∑ i, y i) := by
  have hn : (Fintype.card I:ℂ) ≠ 0 := by exact_mod_cast h.ne'
  unfold classProjector
  rw [← Finset.sum_mul]
  field_simp [hn]

private theorem norm_sum_units {I K : Type*} [NormedField K] [IsUltrametricDist K]
    (s : Finset I) (x : I → K) (hx : ∀ i ∈ s, ‖x i‖≤1) :
    ‖∑ i ∈ s, x i‖≤1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
      (hx i (Finset.mem_insert_self _ _))
      (ih fun j hj => hx j (Finset.mem_insert_of_mem hj)))

/-- Paired tests integral at all embeddings above the selected prime
pay the actual class factor, including the conjugate test. -/
theorem class_projector_bound {I K : Type*} [Fintype I]
    [NormedField K] [IsUltrametricDist K] (ι : ℂ →+* K)
    (h : 0 < Fintype.card I) (x y : I → ℂ)
    (hx : ∀ i, ‖ι (star (x i))‖≤1) (hy : ∀ i, ‖ι (y i)‖≤1) :
    ‖ι ((Fintype.card I:ℂ)*(∑ i, star (x i)*classProjector y i))‖≤1 := by
  rw [class_pair h,map_mul,map_sum,map_sum,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (norm_sum_units _ _ fun i _ => hx i)).trans
    (norm_sum_units _ _ fun i _ => hy i)

/-- On the literal physical layer, the indicator is an integral
test against both positive quadratic depths. It is in the lift
range itself and hence orthogonal to its full complement. -/
theorem class_indicator_read {I : Type*} [Fintype I] (t : ℂ) :
    (∑ _i : I, star (1:ℂ)*t) = (Fintype.card I:ℂ)*t := by
  simp [nsmul_eq_mul]

/-- Measured rank-one squared norm, not an assigned height. -/
theorem class_lift_energy {I : Type*} [Fintype I] (t : ℝ) :
    (∑ _i : I, t^2) = (Fintype.card I:ℝ)*t^2 := by
  simp [nsmul_eq_mul]

theorem class_scalar {I : Type*} [Fintype I] (N t : ℝ) (hN : N≠0) :
    (∑ _i : I, t) = (t/N)*(∑ _i : I, N) := by
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  field_simp [hN]

theorem class_norm_ratio {I : Type*} [Fintype I] (N t : ℝ)
    (h : 0 < Fintype.card I) (hN : N≠0) :
    (∑ _i : I, t^2)/(∑ _i : I, N^2)=(t/N)^2 := by
  have hn : (Fintype.card I:ℝ) ≠ 0 := by exact_mod_cast h.ne'
  rw [class_lift_energy,class_lift_energy]
  field_simp [hn,hN]

end RHLean.Analysis.NativePositiveTwist

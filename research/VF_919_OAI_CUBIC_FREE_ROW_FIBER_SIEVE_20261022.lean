import Mathlib

/-!
# Exact sixth-free to cubic sieve fiber algebra (RH_Lean / OAI)

Finite ideal-prime valuation coordinates are decomposed by base-3.
The original OpenAI FreeRow is an ELEMENT whose principal ideal is
sixth-power-free. Thus the coordinate equivalence below becomes an
equivalence of IDEALS only after normalized-factor reassembly and
a further primary-unit representative audit.

The cubic character mask identity is unconditional once the SOURCE
sextic multiplicativity and sixth-root relations are admitted.

Two further native results are finite consumers with VISIBLE premises:
(i) actual row weights are nonnegative and bounded by rhoMax;
(ii) the cube-free fiber satisfies de Faveri's cubic operator bound.
No theorem here assumes source admission, character-family matching,
or physical weight-spread as a disguised established lemma.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- Base-3 split of the exponents 0,...,5 into 3*c+r,
with c in {0,1} and r in {0,1,2}. -/
theorem sixthFree_valuation_base3 (v : ℕ) (hv : v < 6) :
    v = 3 * (v / 3) + (v % 3) ∧ v / 3 < 2 ∧ v % 3 < 3 := by
  omega

/-- Strong uniqueness, including overlapping support of c and r.
No coprimality between the cube root and cube-free remainder is assumed. -/
theorem sixthFree_valuation_base3_unique
    (v c r : ℕ) (hc : c < 2) (hr : r < 3)
    (h : v = 3 * c + r) :
    c = v / 3 ∧ r = v % 3 := by
  omega

/-- The exact LOCAL prime valuation equivalence for every finite
ideal factor support. Genuine ideal factorization supplies the
finite support; the theorem has no artificial coprimality condition.
The positive-coordinate source FreeRow relation must still be
transported through normalizedFactors and unit representatives. -/
def sixthPowerFree_equiv_sqFree_mul_cube_cubeFree (κ : Type*) :
    (κ → Fin 6) ≃ ((κ → Fin 2) × (κ → Fin 3)) where
  toFun v :=
    (fun p => ⟨(v p).val / 3, by
       have hv := (v p).isLt
       omega⟩,
     fun p => ⟨(v p).val % 3, by omega⟩)
  invFun cr := fun p =>
    ⟨3 * (cr.1 p).val + (cr.2 p).val, by
      have hc := (cr.1 p).isLt
      have hr := (cr.2 p).isLt
      omega⟩
  left_inv v := by
    funext p
    apply Fin.ext
    change 3 * ((v p).val / 3) + ((v p).val % 3) = (v p).val
    omega
  right_inv cr := by
    rcases cr with ⟨c, r⟩
    apply Prod.ext
    · funext p
      apply Fin.ext
      change (3 * (c p).val + (r p).val) / 3 = (c p).val
      have hc := (c p).isLt
      have hr := (r p).isLt
      omega
    · funext p
      apply Fin.ext
      change (3 * (c p).val + (r p).val) % 3 = (r p).val
      have hc := (c p).isLt
      have hr := (r p).isLt
      omega

/-- On the rows where a marked prime does NOT divide the cube-root
factor c, the sextic cube has trivial CUBIC phase:
(v_c^3)^2 = v_c^6 = 1. The zero phase on a masked-out
prime is not discarded. Both masks are fully preserved.
This is the precise fiberwise algebraic content of
chi_p(c^3*u0)^2 = chi_p(u0)^2 on p-coprime c. -/
theorem cubic_masked_cube_character_invariant
    (coprimeC coprimeU : Prop) (zC zU : ℂ)
    (hUnit : coprimeC → zC ^ 6 = 1) :
    (if coprimeC ∧ coprimeU then (zC ^ 3 * zU) ^ 2 else 0) =
      (if coprimeC then (1 : ℂ) else 0) *
        (if coprimeU then zU ^ 2 else 0) := by
  classical
  by_cases hc : coprimeC
  · by_cases hu : coprimeU
    · have hpow := hUnit hc
      simpa [hc, hu] using
        (show (zC ^ 3 * zU) ^ 2 = zU ^ 2 by
          calc
            _ = zC ^ 6 * zU ^ 2 := by ring
            _ = zU ^ 2 := by rw [hpow]; ring)
    · simp [hc, hu]
  · simp [hc]

/-- A conjugated cubic symbol has the same fiber invariance,
which is the orientation of RH_Lean's *leading* compensated D-head:
-vInv*D proportional to conjugate(v)^2. -/
theorem conjugate_cubic_masked_cube_character_invariant
    (coprimeC coprimeU : Prop) (zC zU : ℂ)
    (hUnit : coprimeC → zC ^ 6 = 1) :
    (if coprimeC ∧ coprimeU then
      star ((zC ^ 3 * zU) ^ 2) else 0) =
      (if coprimeC then (1 : ℂ) else 0) *
        (if coprimeU then star (zU ^ 2) else 0) := by
  classical
  by_cases hc : coprimeC
  · by_cases hu : coprimeU
    · have hpow := hUnit hc
      simpa [hc, hu] using
        (show star ((zC ^ 3 * zU) ^ 2) = star (zU ^ 2) by
          congr 1
          calc
            _ = zC ^ 6 * zU ^ 2 := by ring
            _ = zU ^ 2 := by rw [hpow]; ring)
    · simp [hc, hu]
  · simp [hc]

/-- Directly from nonnegative physical weights and a cube-free
fiber large-sieve estimate. The input hSieve is NOT a proof of
de Faveri's theorem for actual RH_Lean rows: character matching,
all masks, correct ideal representatives, and the true row set
must be justified independently.

A single physical pointwise rhoMax works despite arbitrary
nonuniform weights. The masked coefficient norm of a c-fiber
cannot exceed the original unmasked coefficient norm. -/
theorem cubic_head_fiber_reduction_le
    {κ ι : Type*}
    (fibers : Finset κ) (rows : κ → Finset ι)
    (rho : κ → ι → ℝ) (amplitude : κ → ι → ℂ)
    (B : κ → ℝ) (rhoMax coeffSq : ℝ)
    (hrhoMax : 0 ≤ rhoMax)
    (hrho : ∀ c ∈ fibers, ∀ u ∈ rows c,
      0 ≤ rho c u ∧ rho c u ≤ rhoMax)
    (hSieve : ∀ c ∈ fibers,
      (∑ u ∈ rows c, ‖amplitude c u‖ ^ 2) ≤ B c * coeffSq) :
    (∑ c ∈ fibers, ∑ u ∈ rows c,
      rho c u * ‖amplitude c u‖ ^ 2) ≤
      rhoMax * (∑ c ∈ fibers, B c) * coeffSq := by
  have hFiber (c : κ) (hc : c ∈ fibers) :
      (∑ u ∈ rows c, rho c u * ‖amplitude c u‖ ^ 2) ≤
        rhoMax * (B c * coeffSq) := by
    have hb : (∑ u ∈ rows c,
        rho c u * ‖amplitude c u‖ ^ 2) ≤
        rhoMax * (∑ u ∈ rows c, ‖amplitude c u‖ ^ 2) := by
      calc
        _ ≤ ∑ u ∈ rows c, rhoMax * ‖amplitude c u‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro u hu
          exact mul_le_mul_of_nonneg_right (hrho c hc u hu).2
            (sq_nonneg _)
        _ = rhoMax * ∑ u ∈ rows c, ‖amplitude c u‖ ^ 2 := by
          rw [Finset.mul_sum]
    exact hb.trans (mul_le_mul_of_nonneg_left (hSieve c hc) hrhoMax)
  calc
    _ ≤ ∑ c ∈ fibers, rhoMax * (B c * coeffSq) := by
      apply Finset.sum_le_sum
      intro c hc
      exact hFiber c hc
    _ = ∑ c ∈ fibers, (rhoMax * coeffSq) * B c := by
      apply Finset.sum_congr rfl
      intro c hc
      ring
    _ = (rhoMax * coeffSq) * ∑ c ∈ fibers, B c := by
      rw [Finset.mul_sum]
    _ = rhoMax * (∑ c ∈ fibers, B c) * coeffSq := by ring

/-- The EXACT finite arithmetic payment for the three de Faveri
operator terms after sixth-free -> cube-free slicing.
Use B(c) <= L*(U/N(c)^3 + P + 2*(UP)^(2/3)/N(c)^2)
with L encompassing C_eps*(UP)^eps. It only requires independent
bounds for the two convergent inverse-norm sums and cube-root
fiber-counting; no asymptotic ideal count is asserted here. -/
theorem deFaveri_cubic_fiber_sum_bound
    {κ : Type*}
    (fibers : Finset κ) (q B : κ → ℝ)
    (U P L Z2 Z3 K : ℝ)
    (hU : 0 ≤ U) (hP : 0 ≤ P) (hL : 0 ≤ L)
    (hQ2 : (∑ c ∈ fibers, q c ^ (-(2 : ℝ))) ≤ Z2)
    (hQ3 : (∑ c ∈ fibers, q c ^ (-(3 : ℝ))) ≤ Z3)
    (hCount : (fibers.card : ℝ) ≤ K * U ^ (1 / 3 : ℝ))
    (hSlice : ∀ c ∈ fibers,
      B c ≤ L * (U * q c ^ (-(3 : ℝ)) + P +
        2 * (U * P) ^ (2 / 3 : ℝ) * q c ^ (-(2 : ℝ)))) :
    (∑ c ∈ fibers, B c) ≤
      L * (U * Z3 + P * K * U ^ (1 / 3 : ℝ) +
        2 * (U * P) ^ (2 / 3 : ℝ) * Z2) := by
  let G : ℝ := 2 * (U * P) ^ (2 / 3 : ℝ)
  have hG : 0 ≤ G := by
    dsimp [G]
    positivity
  have hsum :
      (∑ c ∈ fibers,
        L * (U * q c ^ (-(3 : ℝ)) + P + G * q c ^ (-(2 : ℝ)))) =
      L * (U * (∑ c ∈ fibers, q c ^ (-(3 : ℝ))) +
        P * (fibers.card : ℝ) +
        G * (∑ c ∈ fibers, q c ^ (-(2 : ℝ)))) := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul]
    ring
  have hInner :
      U * (∑ c ∈ fibers, q c ^ (-(3 : ℝ))) +
        P * (fibers.card : ℝ) +
        G * (∑ c ∈ fibers, q c ^ (-(2 : ℝ))) ≤
      U * Z3 + P * (K * U ^ (1 / 3 : ℝ)) + G * Z2 := by
    have hu := mul_le_mul_of_nonneg_left hQ3 hU
    have hp := mul_le_mul_of_nonneg_left hCount hP
    have hg := mul_le_mul_of_nonneg_left hQ2 hG
    linarith
  calc
    _ ≤ ∑ c ∈ fibers,
        L * (U * q c ^ (-(3 : ℝ)) + P +
          G * q c ^ (-(2 : ℝ))) := by
      apply Finset.sum_le_sum
      intro c hc
      exact hSlice c hc
    _ = L * (U * (∑ c ∈ fibers, q c ^ (-(3 : ℝ))) +
        P * (fibers.card : ℝ) +
        G * (∑ c ∈ fibers, q c ^ (-(2 : ℝ)))) := hsum
    _ ≤ L * (U * Z3 + P * (K * U ^ (1 / 3 : ℝ)) +
        G * Z2) := mul_le_mul_of_nonneg_left hInner hL
    _ = L * (U * Z3 + P * K * U ^ (1 / 3 : ℝ) +
        2 * (U * P) ^ (2 / 3 : ℝ) * Z2) := by
      dsimp [G]
      ring

/-- The cube-fiber norm costs at U=P^(5/4).
The diagonal, extra cube-root fibers, and mixed Gauss terms
are respectively P^-3/4, P^-7/12, P^-1/2, before (UP)^eps
and the actual physical row-spread multiplier. -/
theorem deFaveri_cubic_P54_exponent_budget
    (P : ℝ) (hP : 0 < P) :
    P ^ (-(3 / 4 : ℝ)) *
        (P ^ (5 / 4 : ℝ)) ^ (-(2 / 3 : ℝ)) *
        P = P ^ (-(7 / 12 : ℝ)) ∧
    P ^ (-(3 / 4 : ℝ)) *
        (P ^ (5 / 4 : ℝ)) ^ (-(1 / 3 : ℝ)) *
        P ^ (2 / 3 : ℝ) = P ^ (-(1 / 2 : ℝ)) := by
  have h2 :
      (P ^ (5 / 4 : ℝ)) ^ (-(2 / 3 : ℝ)) =
        P ^ (-(5 / 6 : ℝ)) := by
    rw [← Real.rpow_mul hP.le]
    congr 1
    ring
  have h3 :
      (P ^ (5 / 4 : ℝ)) ^ (-(1 / 3 : ℝ)) =
        P ^ (-(5 / 12 : ℝ)) := by
    rw [← Real.rpow_mul hP.le]
    congr 1
    ring
  constructor
  · rw [h2]
    calc
      _ = P ^ (-(3 / 4 : ℝ)) * P ^ (-(5 / 6 : ℝ)) *
        P ^ (1 : ℝ) := by norm_num
      _ = P ^ (-(7 / 12 : ℝ)) := by
        rw [← Real.rpow_add hP, ← Real.rpow_add hP]
        congr 1
        ring
  · rw [h3]
    calc
      _ = P ^ (-(3 / 4 : ℝ)) *
          P ^ (-(5 / 12 : ℝ)) *
          P ^ (2 / 3 : ℝ) := rfl
      _ = P ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_add hP, ← Real.rpow_add hP]
        congr 1
        ring

end RHLean.Analysis

#print axioms RHLean.Analysis.sixthFree_valuation_base3
#print axioms RHLean.Analysis.sixthFree_valuation_base3_unique
#print axioms RHLean.Analysis.sixthPowerFree_equiv_sqFree_mul_cube_cubeFree
#print axioms RHLean.Analysis.cubic_masked_cube_character_invariant
#print axioms RHLean.Analysis.conjugate_cubic_masked_cube_character_invariant
#print axioms RHLean.Analysis.cubic_head_fiber_reduction_le
#print axioms RHLean.Analysis.deFaveri_cubic_fiber_sum_bound
#print axioms RHLean.Analysis.deFaveri_cubic_P54_exponent_budget

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
open scoped BigOperators Classical

namespace RHLean.Analysis

/-- Base-3 split of the exponents 0,...,5 into 3*c+r,
with c in {0,1} and r in {0,1,2}. -/
theorem sixthFree_valuation_base3 (v : ℕ) (hv : v < 6) :
    v = 3 * (v / 3) + (v % 3) ∧ v / 3 < 2 ∧ v % 3 < 3 := by
  omega

/-- Strong uniqueness, including overlapping support of c and r.
No coprimality between the cube root and cube-free remainder is assumed. -/
theorem sixthFree_valuation_base3_unique
    (v c r : ℕ) (_hc : c < 2) (hr : r < 3)
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
    · simp [hu]
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
    · simp [hu]
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
      Finset.sum_const, nsmul_eq_mul]
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


/-! ## Conjugate cubic operator norm and explicit dyadic ideal mass -/

/-- Conjugating a cubic Hecke matrix is an EXACT L² isometry
    after conjugating column coefficients. No assumption about
    equidistribution of the row weights is needed. -/
theorem cubic_conjugate_operator_energy_eq
    {ι κ : Type*}
    (rows : Finset ι) (primes : Finset κ)
    (rho : ι → ℝ) (alpha : κ → ℂ) (chi : ι → κ → ℂ) :
    (∑ u ∈ rows, rho u *
      ‖∑ p ∈ primes, alpha p * star (chi u p)‖ ^ 2) =
      (∑ u ∈ rows, rho u *
        ‖∑ p ∈ primes, star (alpha p) * chi u p‖ ^ 2) := by
  apply Finset.sum_congr rfl
  intro u hu
  congr 1
  have heq :
      (∑ p ∈ primes, alpha p * star (chi u p)) =
        star (∑ p ∈ primes, star (alpha p) * chi u p) := by
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro p hp
    simp [star_mul, mul_comm]
  rw [heq, norm_star]

/-- The natural elementary 36 labels are six unit classes and
    six valuations at the unique prime above 3. This does NOT
    assert the as-yet-unproved primary-generator bijection of
    original OpenAI element rows. -/
theorem cubic_primary_unit_ramified_cosets_card :
    Fintype.card (Fin 6 × Fin 6) = 36 := by
  simp

private theorem oai_sum_half_geometric (K : ℕ) :
    (∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k) =
      2 * (1 - (1 / 2 : ℝ) ^ K) := by
  induction K with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

private theorem oai_sum_quarter_geometric (K : ℕ) :
    (∑ k ∈ Finset.range K, (1 / 4 : ℝ) ^ k) =
      (4 / 3 : ℝ) * (1 - (1 / 4 : ℝ) ^ K) := by
  induction K with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

/-- From the *actual dyadic norm lower bound*, not an
    independent analytic hypothesis, the two inverse-norm
    monotonicity bounds follow with exact constants. -/
theorem dyadic_inverse_norm_pointwise_from_lower
    (q : ℝ) (k : ℕ)
    (hq : (2 : ℝ) ^ k ≤ q) :
    q ^ (-(2 : ℝ)) ≤ (1 / 4 : ℝ) ^ k ∧
    q ^ (-(3 : ℝ)) ≤ (1 / 8 : ℝ) ^ k := by
  have hpowPos : 0 < (2 : ℝ) ^ k := by positivity
  have htwo :
      ((2 : ℝ) ^ k) ^ (-(2 : ℝ)) =
        (1 / 4 : ℝ) ^ k := by
    calc
      _ = (2 : ℝ) ^ ((k : ℝ) * (-(2 : ℝ))) :=
        (Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2) k (-(2 : ℝ))).symm
      _ = (2 : ℝ) ^ (-(2 : ℝ) * (k : ℝ)) := by
        congr 1
        ring
      _ = ((2 : ℝ) ^ (-(2 : ℝ))) ^ k :=
        Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2) (-(2 : ℝ)) k
      _ = (1 / 4 : ℝ) ^ k := by norm_num
  have hthree :
      ((2 : ℝ) ^ k) ^ (-(3 : ℝ)) =
        (1 / 8 : ℝ) ^ k := by
    calc
      _ = (2 : ℝ) ^ ((k : ℝ) * (-(3 : ℝ))) :=
        (Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2) k (-(3 : ℝ))).symm
      _ = (2 : ℝ) ^ (-(3 : ℝ) * (k : ℝ)) := by
        congr 1
        ring
      _ = ((2 : ℝ) ^ (-(3 : ℝ))) ^ k :=
        Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2) (-(3 : ℝ)) k
      _ = (1 / 8 : ℝ) ^ k := by norm_num
  constructor
  · calc
      _ ≤ ((2 : ℝ) ^ k) ^ (-(2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hpowPos hq (by norm_num)
      _ = (1 / 4 : ℝ) ^ k := htwo
  · calc
      _ ≤ ((2 : ℝ) ^ k) ^ (-(3 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hpowPos hq (by norm_num)
      _ = (1 / 8 : ℝ) ^ k := hthree

/-- EXACT FINITE DYADIC PAYMENT: if all ideal masses are assigned
    to 2^k<=N<2^(k+1), the original OAI ball bound
    # {I: N(I)<=X} <=128X gives bucketCount<=256*2^k.
    The h2 and h3 premises are precisely the elementary
    monotonicity bounds N^-2<=2^(-2k), N^-3<=2^(-3k).
    No false claim of a full ideal-to-primary element adapter. -/
theorem dyadic_inverse_norm_two_three_constants
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (bucket : ι → ℕ) (K : ℕ)
    (normVal : ι → ℝ)
    (hRange : ∀ i ∈ s, bucket i < K)
    (hCount : ∀ k < K,
      ((s.filter (fun i => bucket i = k)).card : ℝ) ≤
        256 * (2 : ℝ) ^ k)
    (h2 : ∀ i ∈ s, normVal i ^ (-(2 : ℝ)) ≤
        (1 / 4 : ℝ) ^ (bucket i))
    (h3 : ∀ i ∈ s, normVal i ^ (-(3 : ℝ)) ≤
        (1 / 8 : ℝ) ^ (bucket i)) :
    (∑ i ∈ s, normVal i ^ (-(2 : ℝ))) ≤ 512 ∧
    (∑ i ∈ s, normVal i ^ (-(3 : ℝ))) ≤ 1024 / 3 := by
  have hmap : ∀ i ∈ s, bucket i ∈ Finset.range K := by
    intro i hi
    exact Finset.mem_range.mpr (hRange i hi)
  have hfib (f : ι → ℝ) :
      (∑ i ∈ s, f i) =
        ∑ k ∈ Finset.range K,
          ∑ i ∈ s with bucket i = k, f i := by
    exact (Finset.sum_fiberwise_of_maps_to
      (s := s) (t := Finset.range K) (g := bucket) hmap f).symm
  have hcell2 (k : ℕ) (hk : k < K) :
      (∑ i ∈ s with bucket i = k,
        normVal i ^ (-(2 : ℝ))) ≤
      256 * (1 / 2 : ℝ) ^ k := by
    let S : Finset ι := s.filter (fun i => bucket i = k)
    have hupper :
        (∑ i ∈ S, normVal i ^ (-(2 : ℝ))) ≤
          (S.card : ℝ) * (1 / 4 : ℝ) ^ k := by
      calc
        _ ≤ ∑ i ∈ S, (1 / 4 : ℝ) ^ k := by
          apply Finset.sum_le_sum
          intro i hi
          have hh := Finset.mem_filter.mp hi
          simpa only [hh.2] using h2 i hh.1
        _ = (S.card : ℝ) * (1 / 4 : ℝ) ^ k := by simp
    calc
      _ ≤ (S.card : ℝ) * (1 / 4 : ℝ) ^ k := hupper
      _ ≤ (256 * (2 : ℝ) ^ k) * (1 / 4 : ℝ) ^ k := by
        exact mul_le_mul_of_nonneg_right (hCount k hk)
          (by positivity)
      _ = 256 * (1 / 2 : ℝ) ^ k := by
        rw [mul_assoc, ← mul_pow]
        norm_num
  have hcell3 (k : ℕ) (hk : k < K) :
      (∑ i ∈ s with bucket i = k,
        normVal i ^ (-(3 : ℝ))) ≤
      256 * (1 / 4 : ℝ) ^ k := by
    let S : Finset ι := s.filter (fun i => bucket i = k)
    have hupper :
        (∑ i ∈ S, normVal i ^ (-(3 : ℝ))) ≤
          (S.card : ℝ) * (1 / 8 : ℝ) ^ k := by
      calc
        _ ≤ ∑ i ∈ S, (1 / 8 : ℝ) ^ k := by
          apply Finset.sum_le_sum
          intro i hi
          have hh := Finset.mem_filter.mp hi
          simpa only [hh.2] using h3 i hh.1
        _ = (S.card : ℝ) * (1 / 8 : ℝ) ^ k := by simp
    calc
      _ ≤ (S.card : ℝ) * (1 / 8 : ℝ) ^ k := hupper
      _ ≤ (256 * (2 : ℝ) ^ k) * (1 / 8 : ℝ) ^ k := by
        exact mul_le_mul_of_nonneg_right (hCount k hk)
          (by positivity)
      _ = 256 * (1 / 4 : ℝ) ^ k := by
        rw [mul_assoc, ← mul_pow]
        norm_num
  constructor
  · calc
      _ = ∑ k ∈ Finset.range K,
          ∑ i ∈ s with bucket i = k,
            normVal i ^ (-(2 : ℝ)) :=
        hfib (fun i => normVal i ^ (-(2 : ℝ)))
      _ ≤ ∑ k ∈ Finset.range K,
            256 * (1 / 2 : ℝ) ^ k := by
        apply Finset.sum_le_sum
        intro k hk
        exact hcell2 k (Finset.mem_range.mp hk)
      _ = 256 * ∑ k ∈ Finset.range K,
            (1 / 2 : ℝ) ^ k := by rw [Finset.mul_sum]
      _ ≤ 512 := by
        rw [oai_sum_half_geometric]
        have hp : 0 ≤ (1 / 2 : ℝ) ^ K := by positivity
        nlinarith
  · calc
      _ = ∑ k ∈ Finset.range K,
          ∑ i ∈ s with bucket i = k,
            normVal i ^ (-(3 : ℝ)) :=
        hfib (fun i => normVal i ^ (-(3 : ℝ)))
      _ ≤ ∑ k ∈ Finset.range K,
            256 * (1 / 4 : ℝ) ^ k := by
        apply Finset.sum_le_sum
        intro k hk
        exact hcell3 k (Finset.mem_range.mp hk)
      _ = 256 * ∑ k ∈ Finset.range K,
            (1 / 4 : ℝ) ^ k := by rw [Finset.mul_sum]
      _ ≤ 1024 / 3 := by
        rw [oai_sum_quarter_geometric]
        have hp : 0 ≤ (1 / 4 : ℝ) ^ K := by positivity
        nlinarith

end RHLean.Analysis

#print axioms RHLean.Analysis.sixthFree_valuation_base3
#print axioms RHLean.Analysis.sixthFree_valuation_base3_unique
#print axioms RHLean.Analysis.sixthPowerFree_equiv_sqFree_mul_cube_cubeFree
#print axioms RHLean.Analysis.cubic_masked_cube_character_invariant
#print axioms RHLean.Analysis.conjugate_cubic_masked_cube_character_invariant
#print axioms RHLean.Analysis.cubic_head_fiber_reduction_le
#print axioms RHLean.Analysis.deFaveri_cubic_fiber_sum_bound
#print axioms RHLean.Analysis.deFaveri_cubic_P54_exponent_budget
#print axioms RHLean.Analysis.cubic_conjugate_operator_energy_eq
#print axioms RHLean.Analysis.cubic_primary_unit_ramified_cosets_card
#print axioms RHLean.Analysis.dyadic_inverse_norm_two_three_constants
#print axioms RHLean.Analysis.dyadic_inverse_norm_pointwise_from_lower

import RHLean.Geometry.NativeNewtonCongruence

/-!
# Newton coefficients of running products of integral affine factors

Each affine increment has one factor of `p`. Taking a forward difference
of a product gives three products of lower-order differences. The resulting
divisibility is preserved by the cumulative product, over any commutative ring.
-/

set_option autoImplicit false

open scoped BigOperators

namespace RHLean.Geometry.NativeNewtonCongruence

variable {O : Type*} [CommRing O]

private theorem coefficient_succ (f : ℕ → O) (j : ℕ) :
    coefficient f (j + 1) = coefficient (fwdDiff 1 f) j := by
  simp only [coefficient, Function.iterate_succ_apply]

private theorem coefficient_add' (f g : ℕ → O) (j : ℕ) :
    coefficient (f + g) j = coefficient f j + coefficient g j := by
  simp only [coefficient, fwdDiff_iter_add, Pi.add_apply]

private theorem coefficient_zero_fn (j : ℕ) : coefficient (fun _ : ℕ => (0 : O)) j = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [coefficient_succ, fwdDiff_const]; exact ih

private theorem diff_mul (f g : ℕ → O) :
    fwdDiff 1 (f * g) =
      fwdDiff 1 f * g + f * fwdDiff 1 g + fwdDiff 1 f * fwdDiff 1 g := by
  funext n
  simp only [fwdDiff, Pi.mul_apply, Pi.add_apply]
  ring

private def CoeffBound (p : O) (s N : ℕ) (f : ℕ → O) : Prop :=
  ∀ j ≤ N, p ^ ((j + s + 1) / 2) ∣ coefficient f j

private theorem lower_power {p x : O} {a b : ℕ} (h : p ^ b ∣ x) (hab : a ≤ b) :
    p ^ a ∣ x := (pow_dvd_pow p hab).trans h

private theorem bound_diff {p : O} {s N : ℕ} {f : ℕ → O} (h : CoeffBound p s (N + 1) f) :
    CoeffBound p (s + 1) N (fwdDiff 1 f) := by
  intro j hj
  rw [← coefficient_succ, show j + (s + 1) + 1 = j + 1 + s + 1 by omega]
  exact h (j + 1) (by omega)

private theorem product_bound (p : O) (N : ℕ) :
    ∀ (a b : ℕ) (f g : ℕ → O), CoeffBound p a N f → CoeffBound p b N g →
      p ^ ((N + (a + b) + 1) / 2) ∣ coefficient (f * g) N := by
  induction N with
  | zero =>
    intro a b f g hf hg
    have h := mul_dvd_mul (hf 0 le_rfl) (hg 0 le_rfl)
    rw [← pow_add] at h
    exact lower_power h (by omega)
  | succ N ih =>
    intro a b f g hf hg
    have hf' := bound_diff hf
    have hg' := bound_diff hg
    have hf0 : CoeffBound p a N f := fun j hj => hf j (hj.trans (Nat.le_succ N))
    have hg0 : CoeffBound p b N g := fun j hj => hg j (hj.trans (Nat.le_succ N))
    rw [coefficient_succ, diff_mul, coefficient_add', coefficient_add']
    exact dvd_add (dvd_add (lower_power (ih _ _ _ _ hf' hg0) (by omega))
      (lower_power (ih _ _ _ _ hf0 hg') (by omega)))
      (lower_power (ih _ _ _ _ hf' hg') (by omega))

private theorem affine_bound (p c d : O) (j : ℕ) :
    p ^ ((j + 1 + 1) / 2) ∣ coefficient (fun n : ℕ => p * c * ((n : O) + d)) j := by
  have hd : fwdDiff 1 (fun n : ℕ => p * c * ((n : O) + d)) = fun _ => p * c := by
    funext n
    simp only [fwdDiff, Nat.cast_add, Nat.cast_one]
    ring
  cases j with
  | zero =>
    change p ^ 1 ∣ p * c * (((0 : ℕ) : O) + d)
    rw [pow_one]
    exact ⟨c * (((0 : ℕ) : O) + d), by ring⟩
  | succ j =>
    rw [coefficient_succ, hd]
    cases j with
    | zero =>
      change p ^ 1 ∣ p * c
      rw [pow_one]
      exact ⟨c, rfl⟩
    | succ j =>
      rw [coefficient_succ, fwdDiff_const, coefficient_zero_fn]
      exact dvd_zero _

private theorem factors_bound {ι : Type*} (p : O) (S : Finset ι) (c d : ι → O) :
    ∀ j, p ^ ((j + 1 + 1) / 2) ∣ coefficient
      (fun n : ℕ => (∏ i ∈ S, (1 + p * c i * ((n : O) + d i))) - 1) j := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro j
    simp only [Finset.prod_empty, sub_self, coefficient_zero_fn, dvd_zero]
  | @insert i S hi ih =>
    let t (n : ℕ) : O := p * c i * ((n : O) + d i)
    let g (n : ℕ) : O := (∏ u ∈ S, (1 + p * c u * ((n : O) + d u))) - 1
    have hins : (fun n : ℕ => (∏ u ∈ insert i S, (1 + p * c u * ((n : O) + d u))) - 1) =
        t + g + t * g := by
      funext n
      simp only [Finset.prod_insert hi, Pi.add_apply, Pi.mul_apply, t, g]
      ring
    intro j
    have hprod := product_bound p j 1 1 t g (fun k _ => affine_bound p (c i) (d i) k)
      (fun k _ => ih k)
    rw [hins, coefficient_add', coefficient_add']
    exact dvd_add (dvd_add (affine_bound p (c i) (d i) j) (ih j)) (lower_power hprod (by omega))

/-- The order-`j` Newton coefficient of a running product is divisible by
`p ^ ⌈j/2⌉` whenever each one-step ratio is a finite product of these integral
affine factors. The number of factors and the initial value are unrestricted. -/
theorem pow_dvd_coefficient_of_affine_product_rec {ι : Type*} (p : O) (S : Finset ι)
    (c d : ι → O) (f : ℕ → O)
    (hs : ∀ n, f (n + 1) = f n * ∏ i ∈ S, (1 + p * c i * ((n : O) + d i))) (j : ℕ) :
    p ^ ((j + 1) / 2) ∣ coefficient f j := by
  let u (n : ℕ) : O := (∏ i ∈ S, (1 + p * c i * ((n : O) + d i))) - 1
  have hD : fwdDiff 1 f = f * u := by
    funext n
    simp only [fwdDiff, Pi.mul_apply, u, hs n]
    ring
  have h : ∀ N, CoeffBound p 0 N f := by
    intro N
    induction N with
    | zero =>
      intro k hk
      obtain rfl : k = 0 := by omega
      change p ^ 0 ∣ coefficient f 0
      rw [pow_zero]
      exact one_dvd _
    | succ N ih =>
      intro k hk
      by_cases hk' : k ≤ N
      · exact ih k hk'
      · obtain rfl : k = N + 1 := by omega
        rw [coefficient_succ, hD]
        exact lower_power (product_bound p N 0 1 f u ih (fun m _ => factors_bound p S c d m))
          (by omega)
  simpa only [Nat.add_zero] using h j j le_rfl


private theorem coefficient_const_dvd (p a : O) (j : ℕ) :
    p ^ ((j + 1) / 2) ∣ coefficient (fun _ : ℕ => a) j := by
  cases j with
  | zero => change p ^ 0 ∣ a; simp
  | succ j => rw [coefficient_succ, fwdDiff_const, coefficient_zero_fn]; exact dvd_zero _

private theorem coefficient_neg' (f : ℕ → O) (j : ℕ) :
    coefficient (-f) j = -coefficient f j := by
  have h := coefficient_add' f (-f) j
  have hz : coefficient (0 : ℕ → O) j = 0 := coefficient_zero_fn j
  rw [add_neg_cancel, hz] at h
  linear_combination -h

private theorem coefficient_dvd_of_values (d : O) (j : ℕ) (f : ℕ → O)
    (hf : ∀ n, d ∣ f n) : d ∣ coefficient f j := by
  induction j generalizing f with
  | zero => exact hf 0
  | succ j ih =>
    rw [coefficient_succ]
    exact ih _ (fun n => dvd_sub (hf (n + 1)) (hf n))

/-- A pointwise reciprocal of a sequence starting at one has the same half-slope
divisibility. The approximants `a ↦ 1 + (1 - f) * a` gain one power of `p`
pointwise at each step. -/
theorem pow_dvd_coefficient_inverse (p : O) (f q : ℕ → O) (hf0 : f 0 = 1)
    (hf : ∀ j, p ^ ((j + 1) / 2) ∣ coefficient f j)
    (hinv : ∀ n, f n * q n = 1) (j : ℕ) : p ^ ((j + 1) / 2) ∣ coefficient q j := by
  have hmod (n : ℕ) : p ∣ f n - 1 := by
    have h := sub_readout_mem (Ideal.span ({p} : Set O)) f 0 (fun k hk =>
      Ideal.mem_span_singleton.mpr (by
        simpa only [pow_one] using lower_power (hf k) (by omega : 1 ≤ (k + 1) / 2))) n
    apply Ideal.mem_span_singleton.mp
    simpa [readout, coefficient, hf0] using h
  let u : ℕ → O := (fun _ => 1) + (-f)
  have hu (k : ℕ) : p ^ ((k + 1) / 2) ∣ coefficient u k := by
    change _ ∣ coefficient ((fun _ => 1) + (-f)) k
    rw [coefficient_add', coefficient_neg']
    exact dvd_add (coefficient_const_dvd p 1 k) (dvd_neg.mpr (hf k))
  have hup (n : ℕ) : p ∣ u n := by
    change p ∣ 1 + -f n
    simpa only [neg_sub, sub_eq_add_neg] using (dvd_neg.mpr (hmod n))
  have approx (N : ℕ) : ∃ a : ℕ → O,
      (∀ k, p ^ ((k + 1) / 2) ∣ coefficient a k) ∧ ∀ n, p ^ N ∣ q n - a n := by
    induction N with
    | zero =>
      refine ⟨fun _ => 0, fun k => coefficient_const_dvd p 0 k, ?_⟩
      intro n
      simp
    | succ N ih =>
      obtain ⟨a, ha, he⟩ := ih
      refine ⟨(fun _ => 1) + u * a, ?_, ?_⟩
      · intro k
        rw [coefficient_add']
        exact dvd_add (coefficient_const_dvd p 1 k)
          (product_bound p k 0 0 u a (fun m _ => hu m) (fun m _ => ha m))
      · intro n
        have heq : q n - ((fun _ => 1) + u * a) n = u n * (q n - a n) := by
          change q n - (1 + (1 + -f n) * a n) = (1 + -f n) * (q n - a n)
          linear_combination hinv n
        rw [heq, pow_succ']
        exact mul_dvd_mul (hup n) (he n)
  obtain ⟨a, ha, he⟩ := approx ((j + 1) / 2)
  have hq : q = a + (fun n => q n - a n) := by
    funext n
    change q n = a n + (q n - a n)
    ring
  rw [hq, coefficient_add']
  exact dvd_add (ha j) (coefficient_dvd_of_values _ j (fun n => q n - a n) he)

end RHLean.Geometry.NativeNewtonCongruence

import «research.NativeRetainedDegreePreimage»
import RHLean.Geometry.NativePrimeExponentJet

/-! The actual quotient-slot interval is order convex for divisibility.
Its prime-exponent Hasse translation therefore needs no extra ancestor
rows. This constructs non-layer-constant integral observations with a
common exact inverse and an independent norm bound. -/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open RHLean.Geometry.NativePrimeExponentJet

namespace RHLean.Analysis.AlpogeThin.SlotProjector.PhysicalJet

/-- Restrict the Hasse group law to a convex subfamily of the genuine
divisor-closed exponent list. Omitted intermediate terms vanish. -/
theorem restricted_mul {I J σ : Type} [Fintype I] [Fintype J] [Fintype σ]
    (e : I → σ →₀ ℕ) (he : Function.Injective e) (hc : DivisorClosed e)
    (f : J ↪ I)
    (hv : ∀ i j : J, ∀ k : I, e (f i) ≤ e k → e k ≤ e (f j) → k ∈ Set.range f)
    (s t : ℤ) :
    translation (e ∘ f) s * translation (e ∘ f) t = translation (e ∘ f) (s+t) := by
  classical
  ext i j
  let g (k : I) := translation e s (f i) k * translation e t k (f j)
  have hzero (k : {k : I // k ∉ Set.range f}) : g k.val = 0 := by
    by_cases h : e (f i) ≤ e k.val
    · have h' : ¬e k.val ≤ e (f j) := fun h' => k.property (hv i j k.val h h')
      change translation e s (f i) k.val * translation e t k.val (f j) = 0
      rw [entry_zero_of_not_le e t h', mul_zero]
    · change translation e s (f i) k.val * translation e t k.val (f j) = 0
      rw [entry_zero_of_not_le e s h, zero_mul]
  have hs : (∑ k : J, g (f k)) = ∑ k : I, g k := by
    calc
      _ = ∑ k : Set.range f, g k.val :=
        Fintype.sum_equiv (Equiv.ofInjective f f.injective) _ _ fun _ => rfl
      _ = _ := by
        have hz : (∑ k : {k : I // k ∉ Set.range f}, g k.val) = 0 :=
          Finset.sum_eq_zero fun k _ => hzero k
        have hh := Fintype.sum_subtype_add_sum_subtype (fun k : I => k ∈ Set.range f) g
        rw [hz, add_zero] at hh
        exact hh
  change (∑ k : J, g (f k)) = translation e (s+t) (f i) (f j)
  rw [hs]
  exact congrArg (fun M : Matrix I I ℤ => M (f i) (f j))
    (translation_mul e he hc s t)

/-- Degree dilation on the original exponent coordinates. -/
def degreeDiagonal {J σ : Type} [Fintype σ] [DecidableEq J]
    (e : J → σ →₀ ℕ) (N : ℤ) : Matrix J J ℤ :=
  Matrix.diagonal fun j => ∏ p : σ, N^(e j p)

/-- Integral form of the degree-changing conjugation. No division or
new integral lattice is used in the identity. -/
theorem translation_dilation {J σ : Type} [Fintype J] [Fintype σ] [DecidableEq J]
    (e : J → σ →₀ ℕ) (N s : ℤ) :
    degreeDiagonal e N * translation e (N*s) =
      translation e s * degreeDiagonal e N := by
  ext i j
  rw [degreeDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : e i ≤ e j
  · rw [translation_apply, translation_apply, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p _
    have ha : e i p + (e j p-e i p) = e j p := by have := h p; omega
    have hp : N^(e j p) = N^(e i p)*N^(e j p-e i p) := by
      rw [← pow_add, ha]
    rw [hp, mul_pow]
    ring
  · rw [entry_zero_of_not_le e (N*s) h, entry_zero_of_not_le e s h, mul_zero, zero_mul]

abbrev Prefix (u : ℕ) := ↥(Finset.Ioc 0 u)

private theorem prefix_pos (u : ℕ) : ∀ k ∈ Finset.Ioc 0 u, k ≠ 0 :=
  fun _ hk => (Finset.mem_Ioc.mp hk).1.ne'

private theorem prefix_closed (u : ℕ) :
    DivisorClosed (factorizationProfile (Finset.Ioc 0 u)) := by
  apply factorizationProfile_closed
  intro n hn k hk
  have hn' := Finset.mem_Ioc.mp hn
  have hk0 : k ≠ 0 := by
    intro h
    subst k
    exact hn'.1.ne' (zero_dvd_iff.mp hk)
  exact Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hk0, (Nat.le_of_dvd hn'.1 hk).trans hn'.2⟩

/-- Every original slot has its original integer, not an assigned
degree label or an auxiliary copy. -/
def physicalEmbedding {r : ℕ} (h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) :
    Address (bands h v) ↪ Prefix ⌊h 0⌋₊ :=
  let e := (original_addresses h v hne).choose
  { toFun := fun a => ⟨(e a).val, Finset.mem_Ioc.mpr
      ⟨(Nat.zero_le _).trans_lt (Finset.mem_Ioc.mp (e a).property).1,
        (Finset.mem_Ioc.mp (e a).property).2⟩⟩
    inj' := fun a b hab => e.injective (Subtype.ext (congrArg (fun k : Prefix ⌊h 0⌋₊ => k.val) hab)) }

theorem physicalEmbedding_val {r : ℕ} (h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) (a : Address (bands h v)) :
    (physicalEmbedding h v hne a).val = a.2.val :=
  (original_addresses h v hne).choose_spec a

theorem physicalEmbedding_range {r : ℕ} (h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) (k : Prefix ⌊h 0⌋₊) :
    k ∈ Set.range (physicalEmbedding h v hne) ↔ ⌈v⌉₊ < k.val := by
  let e := (original_addresses h v hne).choose
  constructor
  · rintro ⟨a,rfl⟩
    exact (Finset.mem_Ioc.mp (e a).property).1
  · intro hk
    let j : ↥(Finset.Ioc ⌈v⌉₊ ⌊h 0⌋₊) :=
      ⟨k.val, Finset.mem_Ioc.mpr ⟨hk,(Finset.mem_Ioc.mp k.property).2⟩⟩
    refine ⟨e.symm j, Subtype.ext ?_⟩
    change (e (e.symm j)).val = k.val
    rw [e.apply_symm_apply]

/-- Original physical quotient slots carry their genuine prime
factorization profile. -/
def profile {r : ℕ} (h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) :=
  factorizationProfile (Finset.Ioc 0 ⌊h 0⌋₊) ∘ physicalEmbedding h v hne

theorem profile_injective {r : ℕ} (h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) : Function.Injective (profile h v hne) :=
  (factorizationProfile_injective _ (prefix_pos _)).comp (physicalEmbedding h v hne).injective

/-- Actual physical wheel transport, including the missing ancestors:
none of them can lie between two retained divisors. -/
theorem physical_mul {r : ℕ} (h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) (s t : ℤ) :
    translation (profile h v hne) s * translation (profile h v hne) t =
      translation (profile h v hne) (s+t) := by
  apply restricted_mul _ (factorizationProfile_injective _ (prefix_pos _))
    (prefix_closed _) (physicalEmbedding h v hne)
  intro i _ k hi _
  have hd := (factorizationProfile_le_iff_dvd _ (prefix_pos _) _ _).mp hi
  have hle := Nat.le_of_dvd (Finset.mem_Ioc.mp k.property).1 hd
  exact (physicalEmbedding_range h v hne k).2
    (((physicalEmbedding_range h v hne _).1 ⟨i,rfl⟩).trans_le hle)

theorem physical_inverse {r : ℕ} (h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) :
    translation (profile h v hne) (-1) * translation (profile h v hne) 1 = 1 := by
  rw [physical_mul]
  norm_num [translation_zero _ (profile_injective h v hne)]

theorem physical_det {r : ℕ} (h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) :
    (translation (profile h v hne) 1).det = 1 :=
  det_one _ (profile_injective h v hne)

/-- The same translated integral frame recovers every original signed
depth profile. The CRT decoder is not altered except by an integral
inverse on the actual physical addresses. -/
theorem physical_decode {r : ℕ} (h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) (D : Fin (r+1) → ℕ) :
    translation (profile h v hne) (-1) *
      (translation (profile h v hne) 1 * columns (bands h v) D) =
        columns (bands h v) D := by
  rw [← Matrix.mul_assoc, physical_inverse h v hne, Matrix.one_mul]

theorem physical_lift_left_inverse {r : ℕ} (h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) (D : Fin (r+1) → ℕ)
    (hD : ∀ i, 0 < D i) (hc : Pairwise (fun i j => (D i).Coprime (D j))) :
    ∃ Y : Matrix (Fin r) (Address (bands h v)) ℤ,
      Y * (translation (profile h v hne) 1 * columns (bands h v) D) = 1 := by
  obtain ⟨Y,hY⟩ := left_inverse (bands h v) D hne hD hc
  refine ⟨Y * translation (profile h v hne) (-1), ?_⟩
  rw [Matrix.mul_assoc, physical_decode, hY]

/-- The exact degree transport on the two original signed profiles
uses one and the same physical address map. -/
theorem physical_dilation {r : ℕ} (h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) (D : Fin (r+1) → ℕ) (N s : ℤ) :
    degreeDiagonal (profile h v hne) N *
      (translation (profile h v hne) (N*s) * columns (bands h v) D) =
    translation (profile h v hne) s *
      (degreeDiagonal (profile h v hne) N * columns (bands h v) D) := by
  rw [← Matrix.mul_assoc, translation_dilation, Matrix.mul_assoc]

private theorem prefix_degree_cap (u : ℕ) (a : Prefix u) :
    (2:ℕ)^(factorizationProfile (Finset.Ioc 0 u) a).degree ≤ a.val := by
  rw [factorizationProfile_degree, ← Finset.prod_pow_eq_pow_sum]
  calc
    _ ≤ ∏ p ∈ a.val.primeFactors, p ^ a.val.factorization p := by
      exact Finset.prod_le_prod (fun p hp =>
        Nat.pow_le_pow_left (Nat.prime_of_mem_primeFactors hp).two_le _)
    _ = _ := Nat.prod_factorization_pow_eq_self (prefix_pos u a.val a.property)

/-- A polynomial-size entry bound on the actual wheel. It applies to
the inverse as well as the forward translated frame. -/
theorem physical_entry_cap {r : ℕ} (h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) (i j : Address (bands h v)) :
    |translation (profile h v hne) 1 i j| ≤ (⌊h 0⌋₊:ℤ) ∧
      |translation (profile h v hne) (-1) i j| ≤ (⌊h 0⌋₊:ℤ) := by
  let u := ⌊h 0⌋₊
  let e := factorizationProfile (Finset.Ioc 0 u)
  let a := physicalEmbedding h v hne i
  let b := physicalEmbedding h v hne j
  have cap : (2:ℤ)^(e b).degree ≤ (u:ℤ) := by
    exact_mod_cast (prefix_degree_cap u b).trans (Finset.mem_Ioc.mp b.property).2
  have H := column_mass e (factorizationProfile_injective _ (prefix_pos u)) (prefix_closed u) b
  have hn : ∀ s : ℤ, |translation e s a b| ≤ ∑ k, |translation e s k b| :=
    fun s => Finset.single_le_sum (fun k _ => abs_nonneg (translation e s k b)) (Finset.mem_univ a)
  constructor
  · change |translation e 1 a b| ≤ (u:ℤ)
    exact (hn 1).trans (H.2.le.trans cap)
  · change |translation e (-1) a b| ≤ (u:ℤ)
    exact (hn (-1)).trans (H.1.le.trans cap)

/-- For real vectors the true counting-measure energy is controlled
without changing the metric or estimating the four sectors separately. -/
theorem energy_bound {J : Type} [Fintype J] (T : Matrix J J ℝ)
    (U : ℝ) (hcard : (Fintype.card J:ℝ) ≤ U)
    (hT : ∀ i j, |T i j| ≤ U) (z : J → ℝ) :
    (∑ i, (T.mulVec z i)^2) ≤ U^4 * ∑ i, (z i)^2 := by
  have hu : 0 ≤ U := (Nat.cast_nonneg _).trans hcard
  have hsq i j : (T i j)^2 ≤ U^2 := by
    have H := hT i j
    nlinarith only [mul_nonneg (sub_nonneg.mpr H) (add_nonneg hu (abs_nonneg (T i j))),
      sq_abs (T i j)]
  have row i : (T.mulVec z i)^2 ≤ (Fintype.card J:ℝ)*U^2 * ∑ j, (z j)^2 := by
    change (∑ j, T i j * z j)^2 ≤ _
    calc
      _ ≤ (∑ j, (T i j)^2) * ∑ j, (z j)^2 :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (T i) z
      _ ≤ (∑ _j : J, U^2) * ∑ j, (z j)^2 :=
        mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun j _ => hsq i j) (by positivity)
      _ = _ := by simp
  calc
    _ ≤ ∑ _i : J, (Fintype.card J:ℝ)*U^2 * ∑ j, (z j)^2 :=
      Finset.sum_le_sum fun i _ => row i
    _ = (Fintype.card J:ℝ)^2*U^2 * ∑ j, (z j)^2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ U^4 * ∑ j, (z j)^2 := by
      have H : (Fintype.card J:ℝ)^2 ≤ U^2 := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr hcard) (add_nonneg hu (Nat.cast_nonneg (Fintype.card J)))]
      calc
        _ ≤ U^2*U^2 * ∑ j, (z j)^2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right H (sq_nonneg _)) (by positivity)
        _ = _ := by ring

theorem physical_energy {r : ℕ} (h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) (z : Address (bands h v) → ℝ) :
    let T := (translation (profile h v hne) 1).map (Int.castRingHom ℝ)
    let R := (translation (profile h v hne) (-1)).map (Int.castRingHom ℝ)
    (∑ i, (T.mulVec z i)^2) ≤ (⌊h 0⌋₊:ℝ)^4 * ∑ i, (z i)^2 ∧
    (∑ i, (R.mulVec z i)^2) ≤ (⌊h 0⌋₊:ℝ)^4 * ∑ i, (z i)^2 := by
  dsimp only
  have hc : Fintype.card (Address (bands h v)) ≤ ⌊h 0⌋₊ := by
    calc
      _ ≤ Fintype.card (Prefix ⌊h 0⌋₊) := Fintype.card_le_of_embedding (physicalEmbedding h v hne)
      _ = _ := by simp [Nat.card_Ioc]
  constructor
  · apply energy_bound _ _ (by exact_mod_cast hc)
    intro i j
    change |(translation (profile h v hne) 1 i j : ℝ)| ≤ (⌊h 0⌋₊:ℝ)
    exact_mod_cast (physical_entry_cap h v hne i j).1
  · apply energy_bound _ _ (by exact_mod_cast hc)
    intro i j
    change |(translation (profile h v hne) (-1) i j : ℝ)| ≤ (⌊h 0⌋₊:ℝ)
    exact_mod_cast (physical_entry_cap h v hne i j).2

/-- The NNS four-sector reconstruction reads exactly the original
matrix after the common actual integral decoder. -/
theorem physical_coDiv_decode {r : ℕ} (h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) (D : Fin (r+1) → ℕ) :
    let T := (translation (profile h v hne) 1).map (Int.castRingHom ℝ)
    let R := (translation (profile h v hne) (-1)).map (Int.castRingHom ℝ)
    let X := (columns (bands h v) D).map (Int.castRingHom ℝ)
    WheelNNS.coDiv (R * (T * X)) = WheelNNS.coDiv X := by
  dsimp only
  rw [← Matrix.map_mul, ← Matrix.map_mul, physical_decode]

end RHLean.Analysis.AlpogeThin.SlotProjector.PhysicalJet

import RHLean.Analysis.AlpogeNativeCompleteSourcePayment

/-!
# Zeta-only character balance for the native Alpoge source

With the full host as averaging subgroup (`A0 = ⊤`) the annihilator projection
keeps at most four characters: the principal one, whose response is the literal
`alpogeNativeGzArithmetic`, and at most three nonprincipal ones. This file
proves, for `Kp = {0}`:

* the movement bound `AlpogeNativeDerivInt` from the native Mertens estimate,
  with the explicit constant `alpogeNativeMoveConstant`;
* the one-sided balance between `alpogeNativeGzArithmetic x` and the projected
  signal at the moved heights `a t / b`, charging the nonprincipal characters
  by their norms at `x` and by their movement;
* the thin return bound from `AlpogeNativeThinScales` and thin widths, paid by
  the explicit window `2 * f * (x + 1) * θ ≤ 1 / x`;
* their combination with the freezing bill already paid in
  `alpogeNativeCompleteProjection_normalized_le`.

Every statement is a conditional consumer. The norm bounds on the nonprincipal
characters and the thin scales are hypotheses here and are not proved for any
host. The physical top excess stays on the right-hand side unbounded.

Blueprint: CocoSgt/riemann-hypothesis-lean at
7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean and
Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean.
-/

noncomputable section
open scoped ArithmeticFunction.vonMangoldt BigOperators Classical

namespace RHLean.Analysis

section Movement

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem alpogeNativeInertiaCosetMean_norm_le_one
    (I : AddSubgroup G) (a : G) (ψ : AddChar G ℂ) :
    ‖alpogeNativeInertiaCosetMean I a ψ‖ ≤ 1 := by
  classical
  unfold alpogeNativeInertiaCosetMean
  rw [norm_div, Complex.norm_natCast]
  apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
  refine (norm_sum_le _ _).trans ?_
  simp [AddChar.norm_apply]

theorem alpogeNativeFrobInertiaPrimeValue_norm_le_one
    (inertia : ℕ → AddSubgroup G) (frob : ℕ → G)
    (ψ : AddChar G ℂ) (n : ℕ) :
    ‖alpogeNativeFrobInertiaPrimeValue inertia frob ψ n‖ ≤ 1 := by
  unfold alpogeNativeFrobInertiaPrimeValue
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    (fun _ _ => alpogeNativeInertiaCosetMean_norm_le_one _ _ _)

omit [AddCommGroup G] [Fintype G] [DecidableEq G] in
/-- The sharp cutoff at `⌊t⌋` is the positive part over any longer range. -/
theorem alpogeNativeWeightedSource_eq_cut
    (c : ℕ → ℂ) (t : ℝ) (ht : 0 ≤ t) (M : ℕ) (hM : ⌊t⌋₊ ≤ M) :
    (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, c n * ((t / (n : ℝ) - 1 : ℝ) : ℂ)) =
      ∑ n ∈ Finset.Icc 1 M, c n * ((max (t / (n : ℝ) - 1) 0 : ℝ) : ℂ) := by
  have hin : ∀ n ∈ Finset.Icc 1 ⌊t⌋₊,
      c n * ((t / (n : ℝ) - 1 : ℝ) : ℂ) =
        c n * ((max (t / (n : ℝ) - 1) 0 : ℝ) : ℂ) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnt : (n : ℝ) ≤ t := (Nat.le_floor_iff ht).mp hn2
    have hpos : 0 ≤ t / (n : ℝ) - 1 := by
      rw [sub_nonneg, le_div_iff₀ hn0]
      linarith
    rw [max_eq_left hpos]
  rw [Finset.sum_congr rfl hin]
  apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hM)
  intro n hn hnot
  obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlt : ⌊t⌋₊ < n := by
    by_contra hle
    exact hnot (Finset.mem_Icc.mpr ⟨hn1, not_lt.mp hle⟩)
  have htn : t < n := Nat.lt_of_floor_lt hlt
  have hneg : t / (n : ℝ) - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_iff₀ hn0]
    linarith
  rw [max_eq_right hneg]
  simp

omit [AddCommGroup G] [Fintype G] [DecidableEq G] in
/-- Movement of a weighted prime-power source with coefficients dominated by
the von Mangoldt function, in terms of the native reciprocal channel. -/
theorem alpogeNativeWeightedSource_sub_norm_le
    (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ Λ n) (y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊y⌋₊, c n * ((y / (n : ℝ) - 1 : ℝ) : ℂ)) -
        ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n * ((z / (n : ℝ) - 1 : ℝ) : ℂ)‖ ≤
      |y - z| * nativeLambdaRecip ⌊max y z⌋₊ := by
  rw [alpogeNativeWeightedSource_eq_cut c y hy ⌊max y z⌋₊
      (Nat.floor_le_floor (le_max_left y z)),
    alpogeNativeWeightedSource_eq_cut c z hz ⌊max y z⌋₊
      (Nat.floor_le_floor (le_max_right y z)),
    ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  unfold nativeLambdaRecip
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast (Finset.mem_Icc.mp hn).1
  rw [← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]
  have hcut : |max (y / (n : ℝ) - 1) 0 - max (z / (n : ℝ) - 1) 0| ≤
      |y - z| / (n : ℝ) := by
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    rw [show y / (n : ℝ) - 1 - (z / (n : ℝ) - 1) = (y - z) / (n : ℝ) by ring,
      abs_div, abs_of_pos hn0]
  calc
    ‖c n‖ * |max (y / (n : ℝ) - 1) 0 - max (z / (n : ℝ) - 1) 0| ≤
        Λ n * (|y - z| / (n : ℝ)) :=
      mul_le_mul (hc n) hcut (abs_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
    _ = |y - z| * (Λ n / (n : ℝ)) := by ring

omit [AddCommGroup G] [Fintype G] [DecidableEq G] in
theorem alpogeNativeLambdaRecip_floor_le (t : ℝ) (ht : 1 ≤ t) :
    nativeLambdaRecip ⌊t⌋₊ ≤ Real.log t + (Real.log 4 + 2) := by
  have hfl : 1 ≤ ⌊t⌋₊ := Nat.floor_pos.mpr ht
  have hflR : (0 : ℝ) < (⌊t⌋₊ : ℝ) := by exact_mod_cast hfl
  have hM := (nativeLambdaRecip_sub_log_bounds ⌊t⌋₊ hfl).2
  have hlog : Real.log (⌊t⌋₊ : ℝ) ≤ Real.log t :=
    Real.log_le_log hflR (Nat.floor_le (by linarith))
  linarith

omit [AddCommGroup G] [Fintype G] [DecidableEq G] in
theorem alpogeNativeLambdaRecip_floor_ge (t : ℝ) (ht : 1 ≤ t) :
    Real.log t - Real.log 2 - 1 ≤ nativeLambdaRecip ⌊t⌋₊ := by
  have hfl : 1 ≤ ⌊t⌋₊ := Nat.floor_pos.mpr ht
  have hflR : (1 : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast hfl
  have hM := (nativeLambdaRecip_sub_log_bounds ⌊t⌋₊ hfl).1
  have hhalf : t / 2 ≤ (⌊t⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one t
    linarith
  have hlog : Real.log (t / 2) ≤ Real.log (⌊t⌋₊ : ℝ) :=
    Real.log_le_log (by linarith) hhalf
  rw [Real.log_div (by linarith) (by norm_num)] at hlog
  linarith

/-- Nonprincipal movement, valid for all heights at least one. Only the
upper Mertens bound enters. -/
theorem alpogeNativeFrobInertiaGPsi_sub_norm_le
    (inertia : ℕ → AddSubgroup G) (frob : ℕ → G)
    (ell : AddChar G ℂ → ℂ) (ψ : AddChar G ℂ) (hψ : ψ ≠ 0)
    (y z : ℝ) (hy : 1 ≤ y) (hz : 1 ≤ z) :
    ‖alpogeNativeFrobInertiaGPsi inertia frob ell ψ y -
        alpogeNativeFrobInertiaGPsi inertia frob ell ψ z‖ ≤
      |y - z| * (Real.log (max y z) + (Real.log 4 + 2) + ‖ell ψ‖) := by
  rw [alpogeNativeFrobInertiaGPsi_nonprincipal inertia frob ell ψ y hψ,
    alpogeNativeFrobInertiaGPsi_nonprincipal inertia frob ell ψ z hψ]
  have hc : ∀ n, ‖((Λ n : ℝ) : ℂ) *
      alpogeNativeFrobInertiaPrimeValue inertia frob ψ n‖ ≤ Λ n := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
      (alpogeNativeFrobInertiaPrimeValue_norm_le_one inertia frob ψ n)
  have hsrc := alpogeNativeWeightedSource_sub_norm_le
    (fun n => ((Λ n : ℝ) : ℂ) *
      alpogeNativeFrobInertiaPrimeValue inertia frob ψ n) hc y z
    (by linarith) (by linarith)
  have hmert := alpogeNativeLambdaRecip_floor_le (max y z)
    (hy.trans (le_max_left y z))
  have hsplit :
      alpogeNativeFrobInertiaPrimeSum inertia frob ψ y + (y : ℂ) * ell ψ -
          (alpogeNativeFrobInertiaPrimeSum inertia frob ψ z + (z : ℂ) * ell ψ) =
        (alpogeNativeFrobInertiaPrimeSum inertia frob ψ y -
          alpogeNativeFrobInertiaPrimeSum inertia frob ψ z) +
          ((y - z : ℝ) : ℂ) * ell ψ := by
    push_cast
    ring
  have hell : ‖((y - z : ℝ) : ℂ) * ell ψ‖ = |y - z| * ‖ell ψ‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [hell]
  have hscaled := mul_le_mul_of_nonneg_left hmert (abs_nonneg (y - z))
  unfold alpogeNativeFrobInertiaPrimeSum
  linarith

omit [AddCommGroup G] [Fintype G] [DecidableEq G] in
/-- Two-sided movement of the principal prime-power source. -/
theorem alpogeNativePrincipalPrimeSum_sub_bounds
    (y z : ℝ) (hz : 0 ≤ z) (hzy : z ≤ y) :
    (y - z) * nativeLambdaRecip ⌊z⌋₊ ≤
        alpogeNativePrincipalPrimeSum y - alpogeNativePrincipalPrimeSum z ∧
      alpogeNativePrincipalPrimeSum y - alpogeNativePrincipalPrimeSum z ≤
        (y - z) * nativeLambdaRecip ⌊y⌋₊ := by
  have hsub : Finset.Icc 1 ⌊z⌋₊ ⊆ Finset.Icc 1 ⌊y⌋₊ :=
    Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor hzy)
  have hdiff : ∀ s : Finset ℕ,
      (y - z) * ∑ n ∈ s, Λ n / (n : ℝ) =
        ∑ n ∈ s, Λ n * (y / (n : ℝ) - 1) - ∑ n ∈ s, Λ n * (z / (n : ℝ) - 1) := by
    intro s
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  unfold alpogeNativePrincipalPrimeSum alpogeNativePrimePowerWeight
    nativeLambdaRecip
  constructor
  · have hdrop : ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, Λ n * (y / (n : ℝ) - 1) ≤
        ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Λ n * (y / (n : ℝ) - 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro n hn _
      obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hny : (n : ℝ) ≤ y := (Nat.le_floor_iff (hz.trans hzy)).mp hn2
      apply mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      rw [sub_nonneg, le_div_iff₀ hn0]
      linarith
    rw [hdiff]
    linarith
  · have hadd : ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, Λ n * (1 - z / (n : ℝ)) ≤
        ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Λ n * (1 - z / (n : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro n hn hnot
      obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hlt : ⌊z⌋₊ < n := by
        by_contra hle
        exact hnot (Finset.mem_Icc.mpr ⟨hn1, not_lt.mp hle⟩)
      have hzn : z < n := Nat.lt_of_floor_lt hlt
      apply mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      rw [sub_nonneg, div_le_iff₀ hn0]
      linarith
    have hneg : ∀ s : Finset ℕ,
        ∑ n ∈ s, Λ n * (z / (n : ℝ) - 1) =
          -∑ n ∈ s, Λ n * (1 - z / (n : ℝ)) := by
      intro s
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun n _ => by ring)
    rw [hdiff, hneg (Finset.Icc 1 ⌊y⌋₊)]
    have h := hneg (Finset.Icc 1 ⌊z⌋₊)
    linarith

omit [AddCommGroup G] [Fintype G] [DecidableEq G] in
theorem alpogeNative_mul_log_sub_bounds (y z : ℝ) (hz : 0 < z) (hzy : z ≤ y) :
    (y - z) * (Real.log z + 1) ≤ y * Real.log y - z * Real.log z ∧
      y * Real.log y - z * Real.log z ≤ (y - z) * (Real.log y + 1) := by
  have hy : 0 < y := hz.trans_le hzy
  have h1 := Real.log_le_sub_one_of_pos (div_pos hy hz)
  have h2 := Real.log_le_sub_one_of_pos (div_pos hz hy)
  rw [Real.log_div hy.ne' hz.ne'] at h1
  rw [Real.log_div hz.ne' hy.ne'] at h2
  have h1' : z * (Real.log y - Real.log z) ≤ y - z := by
    have h := mul_le_mul_of_nonneg_left h1 hz.le
    rwa [show z * (y / z - 1) = y - z by field_simp] at h
  have h2' : y * (Real.log z - Real.log y) ≤ z - y := by
    have h := mul_le_mul_of_nonneg_left h2 hy.le
    rwa [show y * (z / y - 1) = z - y by field_simp] at h
  constructor <;> linarith

/-- Explicit movement constant: `log 4 + 2` is the native Mertens constant
and the remaining `2` absorbs `log 2` and the Euler constant. -/
def alpogeNativeMoveConstant : ℝ := Real.log 4 + 4

omit [AddCommGroup G] [Fintype G] [DecidableEq G] in
theorem alpogeNativeMoveConstant_nonneg : 0 ≤ alpogeNativeMoveConstant := by
  have : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  unfold alpogeNativeMoveConstant
  linarith

omit [AddCommGroup G] [Fintype G] [DecidableEq G] in
theorem alpogeNativeGzArithmetic_sub_abs_le_of_le
    (y z : ℝ) (hz : 1 ≤ z) (hzy : z ≤ y) (hy1 : y ≤ z + 1) :
    |alpogeNativeGzArithmetic y - alpogeNativeGzArithmetic z| ≤
      alpogeNativeMoveConstant * (y - z) := by
  have hz0 : 0 < z := by linarith
  have hy : 1 ≤ y := hz.trans hzy
  have hd : 0 ≤ y - z := sub_nonneg.mpr hzy
  obtain ⟨hPlo, hPhi⟩ :=
    alpogeNativePrincipalPrimeSum_sub_bounds y z hz0.le hzy
  obtain ⟨hDlo, hDhi⟩ := alpogeNative_mul_log_sub_bounds y z hz0 hzy
  have hRy := mul_le_mul_of_nonneg_left
    (alpogeNativeLambdaRecip_floor_le y hy) hd
  have hRz := mul_le_mul_of_nonneg_left
    (alpogeNativeLambdaRecip_floor_ge z hz) hd
  have hlog : Real.log y - Real.log z ≤ Real.log 2 := by
    have h := Real.log_le_log (by linarith : (0 : ℝ) < y)
      (by linarith : y ≤ 2 * z)
    rw [Real.log_mul (by norm_num) hz0.ne'] at h
    linarith
  have hlog0 : 0 ≤ Real.log y - Real.log z := by
    have := Real.log_le_log hz0 hzy
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hγ1 := Real.eulerMascheroniConstant_lt_two_thirds
  have hγ0 := Real.one_half_lt_eulerMascheroniConstant
  have hup := mul_le_mul_of_nonneg_left
    (show Real.log y - Real.log z + Real.log 4 + 2 +
        Real.eulerMascheroniConstant ≤ alpogeNativeMoveConstant by
      unfold alpogeNativeMoveConstant
      linarith) hd
  have hdown := mul_le_mul_of_nonneg_left
    (show Real.log y - Real.log z + Real.log 2 + 1 -
        Real.eulerMascheroniConstant ≤ alpogeNativeMoveConstant by
      unfold alpogeNativeMoveConstant
      linarith) hd
  rw [alpogeNativeGzArithmetic_eq_principal y,
    alpogeNativeGzArithmetic_eq_principal z, abs_le]
  constructor <;> linarith

/-- Native analogue of Alpoge's `DerivInt`. The nonprincipal clause holds at
all heights; the principal clause is stated on unit windows, which is the
range used by the moved heights `|a t / b - x| ≤ 1`. -/
def AlpogeNativeDerivInt
    (inertia : ℕ → AddSubgroup G) (frob : ℕ → G)
    (ell : AddChar G ℂ → ℂ) (Cd : ℝ) : Prop :=
  (∀ ψ : AddChar G ℂ, ψ ≠ 0 → ∀ y z : ℝ, 1 ≤ y → 1 ≤ z →
      ‖alpogeNativeFrobInertiaGPsi inertia frob ell ψ y -
          alpogeNativeFrobInertiaGPsi inertia frob ell ψ z‖ ≤
        |y - z| * (Real.log (max y z) + Cd + ‖ell ψ‖)) ∧
    (∀ y z : ℝ, 1 ≤ y → 1 ≤ z → |y - z| ≤ 1 →
      |alpogeNativeGzArithmetic y - alpogeNativeGzArithmetic z| ≤ Cd * |y - z|)

/-- The movement bound holds for every Frobenius/inertia assignment and every
`ell`, with one explicit constant. -/
theorem alpogeNativeDerivInt_moveConstant
    (inertia : ℕ → AddSubgroup G) (frob : ℕ → G) (ell : AddChar G ℂ → ℂ) :
    AlpogeNativeDerivInt inertia frob ell alpogeNativeMoveConstant := by
  constructor
  · intro ψ hψ y z hy hz
    refine (alpogeNativeFrobInertiaGPsi_sub_norm_le inertia frob ell ψ hψ
      y z hy hz).trans ?_
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    unfold alpogeNativeMoveConstant
    linarith
  · intro y z hy hz hyz
    obtain ⟨hlo, hhi⟩ := abs_le.mp hyz
    rcases le_total z y with hzy | hyz'
    · rw [abs_of_nonneg (sub_nonneg.mpr hzy)]
      exact alpogeNativeGzArithmetic_sub_abs_le_of_le y z hz hzy (by linarith)
    · rw [abs_sub_comm, abs_sub_comm y z, abs_of_nonneg (sub_nonneg.mpr hyz')]
      exact alpogeNativeGzArithmetic_sub_abs_le_of_le z y hy hyz' (by linarith)

theorem AlpogeNativeDerivInt.nonneg
    {inertia : ℕ → AddSubgroup G} {frob : ℕ → G} {ell : AddChar G ℂ → ℂ}
    {Cd : ℝ} (h : AlpogeNativeDerivInt inertia frob ell Cd) : 0 ≤ Cd := by
  have h21 := h.2 2 1 (by norm_num) le_rfl (by norm_num)
  have habs : |(2 : ℝ) - 1| = 1 := by norm_num
  rw [habs, mul_one] at h21
  exact (abs_nonneg _).trans h21

end Movement

section ZetaCharacters

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
theorem alpogeNativeProjectionChars_zero_mem (A0 : AddSubgroup H) :
    (0 : AddChar (AlpogeNativeE0 × H) ℂ) ∈ alpogeNativeProjectionChars A0 := by
  rw [alpogeNativeProjectionChars_mem]
  intro s _
  exact AddChar.zero_apply _

omit [DecidableEq H] in
/-- Characters trivial on the whole host factor through the two-bit group. -/
theorem alpogeNativeProjectionChars_top_card_le :
    (alpogeNativeProjectionChars (⊤ : AddSubgroup H)).card ≤ 4 := by
  classical
  let f : AddChar (AlpogeNativeE0 × H) ℂ → AddChar AlpogeNativeE0 ℂ :=
    fun ψ => ψ.compAddMonoidHom (AddMonoidHom.inl AlpogeNativeE0 H)
  have hinj : Set.InjOn f
      (alpogeNativeProjectionChars (⊤ : AddSubgroup H) : Set _) := by
    intro ψ hψ φ hφ hfg
    have hψ' := (alpogeNativeProjectionChars_mem ⊤ ψ).1 (Finset.mem_coe.mp hψ)
    have hφ' := (alpogeNativeProjectionChars_mem ⊤ φ).1 (Finset.mem_coe.mp hφ)
    have hval : ∀ (χ : AddChar (AlpogeNativeE0 × H) ℂ),
        (∀ s ∈ (⊤ : AddSubgroup H), χ (0, s) = 1) →
        ∀ g : AlpogeNativeE0 × H, χ g = f χ g.1 := by
      intro χ hχ g
      have hg : g = (g.1, 0) + (0, g.2) := by
        ext <;> simp
      calc
        χ g = χ ((g.1, 0) + (0, g.2)) := by rw [← hg]
        _ = χ (g.1, 0) * χ (0, g.2) := AddChar.map_add_eq_mul χ _ _
        _ = χ (g.1, 0) := by rw [hχ g.2 (AddSubgroup.mem_top _), mul_one]
        _ = f χ g.1 := rfl
    apply DFunLike.ext
    intro g
    rw [hval ψ hψ' g, hval φ hφ' g, hfg]
  have hcard := Finset.card_le_card_of_injOn f
    (fun ψ _ => Finset.mem_univ (f ψ)) hinj
  have hE0 : Fintype.card (AddChar AlpogeNativeE0 ℂ) = 4 := by
    rw [AddChar.card_eq]
    rfl
  rw [Finset.card_univ, hE0] at hcard
  exact hcard

omit [DecidableEq H] in
/-- At most three nonprincipal characters survive the full-host average. -/
theorem alpogeNativeProjectionChars_top_sdiff_card_le :
    (alpogeNativeProjectionChars (⊤ : AddSubgroup H) \ {0}).card ≤ 3 := by
  classical
  rw [Finset.sdiff_singleton_eq_erase,
    Finset.card_erase_of_mem (alpogeNativeProjectionChars_zero_mem ⊤)]
  have := alpogeNativeProjectionChars_top_card_le (H := H)
  omega

/-- The principal retained signal at the moved heights is within the
movement constant of `alpogeNativeGzArithmetic x`. -/
theorem alpogeNativeRetainedSignal_zero_ge
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (TT : Finset H) (hTT : TT.Nonempty) (a : H → ℝ) {b x Cd : ℝ}
    (hx : 2 ≤ x) (hmove : ∀ t ∈ TT, |a t / b - x| ≤ 1)
    (hder : AlpogeNativeDerivInt inertia frob ell Cd) :
    alpogeNativeGzArithmetic x - Cd ≤
      alpogeNativeRetainedSignal
        (alpogeNativeFrobInertiaGPsi inertia frob ell) {0} TT a b := by
  have hT : (0 : ℝ) < TT.card := by exact_mod_cast Finset.card_pos.mpr hTT
  have hCd := hder.nonneg
  have hterm : ∀ t ∈ TT, alpogeNativeGzArithmetic x - Cd ≤
      ∑ ψ ∈ ({0} : Finset (AddChar (AlpogeNativeE0 × H) ℂ)),
        (ψ (alpogeNativeProjectionE1 t) *
          alpogeNativeFrobInertiaGPsi inertia frob ell ψ (a t / b)).re := by
    intro t ht
    rw [Finset.sum_singleton, AddChar.zero_apply, one_mul,
      alpogeNativeFrobInertiaGPsi_principal, Complex.ofReal_re]
    obtain ⟨hlo, _⟩ := abs_le.mp (hmove t ht)
    have hG := hder.2 (a t / b) x (by linarith) (by linarith) (hmove t ht)
    have hG' := hG.trans (mul_le_of_le_one_right hCd (hmove t ht))
    have := (abs_le.mp hG').1
    linarith
  unfold alpogeNativeRetainedSignal
  calc
    alpogeNativeGzArithmetic x - Cd =
        (1 / (TT.card : ℝ)) * ∑ _t ∈ TT, (alpogeNativeGzArithmetic x - Cd) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)

/-- The excluded mass at the moved heights: at most three nonprincipal
characters, each charged its norm at `x` and its movement. -/
theorem alpogeNativeExcludedCharacterMass_top_le
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (TT : Finset H) (hTT : TT.Nonempty) (a : H → ℝ) {b x Cd B L : ℝ}
    (hx : 2 ≤ x) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hmove : ∀ t ∈ TT, |a t / b - x| ≤ 1)
    (hder : AlpogeNativeDerivInt inertia frob ell Cd)
    (hval : ∀ ψ ∈ alpogeNativeProjectionChars (⊤ : AddSubgroup H), ψ ≠ 0 →
      ‖alpogeNativeFrobInertiaGPsi inertia frob ell ψ x‖ ≤ B ∧ ‖ell ψ‖ ≤ L) :
    alpogeNativeExcludedCharacterMass ⊤
        (alpogeNativeFrobInertiaGPsi inertia frob ell) {0} TT a b ≤
      3 * (B + Real.log (x + 1) + Cd + L) := by
  have hT : (0 : ℝ) < TT.card := by exact_mod_cast Finset.card_pos.mpr hTT
  have hCd := hder.nonneg
  have hlogx : 0 ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
  have hP : 0 ≤ B + Real.log (x + 1) + Cd + L := by linarith
  have hchar : ∀ t ∈ TT,
      ∀ ψ ∈ alpogeNativeProjectionChars (⊤ : AddSubgroup H) \ {0},
        ‖alpogeNativeFrobInertiaGPsi inertia frob ell ψ (a t / b)‖ ≤
          B + Real.log (x + 1) + Cd + L := by
    intro t ht ψ hψ
    obtain ⟨hmem, hne⟩ := Finset.mem_sdiff.mp hψ
    have hψ0 : ψ ≠ 0 := fun h => hne (Finset.mem_singleton.mpr h)
    obtain ⟨hBψ, hLψ⟩ := hval ψ hmem hψ0
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hmove t ht)
    have hy1 : 1 ≤ a t / b := by linarith
    have hmv := hder.1 ψ hψ0 (a t / b) x hy1 (by linarith)
    have hmax1 : 1 ≤ max (a t / b) x := hy1.trans (le_max_left _ _)
    have hmaxle : max (a t / b) x ≤ x + 1 := max_le (by linarith) (by linarith)
    have hlogmax : Real.log (max (a t / b) x) ≤ Real.log (x + 1) :=
      Real.log_le_log (by linarith) hmaxle
    have hlogmax0 : 0 ≤ Real.log (max (a t / b) x) := Real.log_nonneg hmax1
    have hfac : 0 ≤ Real.log (max (a t / b) x) + Cd + ‖ell ψ‖ := by
      have := norm_nonneg (ell ψ)
      linarith
    have hmv' := hmv.trans (mul_le_of_le_one_left hfac (hmove t ht))
    have htri := norm_sub_norm_le
      (alpogeNativeFrobInertiaGPsi inertia frob ell ψ (a t / b))
      (alpogeNativeFrobInertiaGPsi inertia frob ell ψ x)
    linarith
  have hinner : ∀ t ∈ TT,
      (∑ ψ ∈ alpogeNativeProjectionChars (⊤ : AddSubgroup H) \ {0},
        ‖alpogeNativeFrobInertiaGPsi inertia frob ell ψ (a t / b)‖) ≤
        3 * (B + Real.log (x + 1) + Cd + L) := by
    intro t ht
    refine (Finset.sum_le_sum (hchar t ht)).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((alpogeNativeProjectionChars (⊤ : AddSubgroup H) \ {0}).card : ℝ) ≤ 3 := by
      exact_mod_cast alpogeNativeProjectionChars_top_sdiff_card_le (H := H)
    exact mul_le_mul_of_nonneg_right hcard hP
  unfold alpogeNativeExcludedCharacterMass
  calc
    _ ≤ (1 / (TT.card : ℝ)) *
        ∑ _t ∈ TT, 3 * (B + Real.log (x + 1) + Cd + L) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hinner) (by positivity)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp

/-- Zeta-only character balance. `B` bounds the nonprincipal responses at `x`
and `L` bounds their `ell` constants; both are hypotheses. With
`B = x ^ (1 / 2 + ε)` this is the native form of Alpoge's
`GrowthInequalityExplicit` signal step. -/
theorem alpogeNativeGz_sub_le_projectedSignal
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (TT : Finset H) (hTT : TT.Nonempty) (a : H → ℝ) {b x Cd B L : ℝ}
    (hx : 2 ≤ x) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hmove : ∀ t ∈ TT, |a t / b - x| ≤ 1)
    (hder : AlpogeNativeDerivInt inertia frob ell Cd)
    (hval : ∀ ψ ∈ alpogeNativeProjectionChars (⊤ : AddSubgroup H), ψ ≠ 0 →
      ‖alpogeNativeFrobInertiaGPsi inertia frob ell ψ x‖ ≤ B ∧ ‖ell ψ‖ ≤ L) :
    alpogeNativeGzArithmetic x - 3 * B -
        (Cd + 3 * (Real.log (x + 1) + Cd + L)) ≤
      alpogeNativeProjectedSignal ⊤
        (alpogeNativeFrobInertiaGPsi inertia frob ell) TT a b := by
  have hret := alpogeNativeRetainedSignal_zero_ge inertia frob ell TT hTT a
    hx hmove hder
  have hexc := alpogeNativeExcludedCharacterMass_top_le inertia frob ell TT hTT a
    hx hB hL hmove hder hval
  have hproj := alpogeNativeRetained_sub_excluded_le_projected ⊤
    (alpogeNativeFrobInertiaGPsi inertia frob ell) {0}
    (Finset.singleton_subset_iff.mpr (alpogeNativeProjectionChars_zero_mem ⊤))
    TT a b
  linarith

end ZetaCharacters

section ThinReturn

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- Native `ThinScales`: every character response is at most `y * θ` beyond
`X' / 3`. This includes the principal character and the characters that the
projection annihilates. -/
def AlpogeNativeThinScales {G : Type*} [AddCommGroup G]
    (F : AddChar G ℂ → ℝ → ℂ) (X' θ : ℝ) : Prop :=
  ∀ ψ : AddChar G ℂ, ∀ y : ℝ, X' / 3 ≤ y → ‖F ψ y‖ ≤ y * θ

/-- The number `f` of positive sites, as a real. It equals `2 * |H|`. -/
def alpogeNativePhiCard (H : Type*) [AddCommGroup H] [Fintype H]
    [DecidableEq H] : ℝ :=
  ((alpogeNativePhiSet H).card : ℝ)

theorem alpogeNativePhiCard_eq :
    alpogeNativePhiCard H = 2 * (Fintype.card H : ℝ) := by
  unfold alpogeNativePhiCard
  rw [alpogeNativeProjectionPhi_card]
  push_cast
  ring

theorem alpogeNativePhiCard_pos : 0 < alpogeNativePhiCard H := by
  rw [alpogeNativePhiCard_eq]
  have : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  positivity

omit [AddCommGroup H] [DecidableEq H] in
theorem alpogeNativeNonPhi_card :
    (Finset.univ.filter
      (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g)).card =
      2 * Fintype.card H := by
  classical
  have hset : Finset.univ.filter
      (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g) =
      ((Finset.univ : Finset AlpogeNativeE0).filter (fun e => ¬ e.1 = 0)) ×ˢ
        (Finset.univ : Finset H) := by
    ext ρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      and_true]
    rfl
  have htwo : ((Finset.univ : Finset AlpogeNativeE0).filter
      (fun e => ¬ e.1 = 0)).card = 2 := by decide
  rw [hset, Finset.card_product, htwo, Finset.card_univ]

omit [DecidableEq H] in
theorem alpogeNativeAddChar_card :
    Fintype.card (AddChar (AlpogeNativeE0 × H) ℂ) = 4 * Fintype.card H := by
  rw [AddChar.card_eq, Fintype.card_prod]
  rfl

/-- Pointwise thin return: every complementary colour and every character is
charged the same bound `K`, giving exactly `2 * f * K`. -/
theorem alpogeNativeProjectionThinReturn_norm_le
    (F : AddChar (AlpogeNativeE0 × H) ℂ → ℝ → ℂ)
    (T2 : Finset H) (a : ℝ) (u t : H) (w : AlpogeNativeE0 × H → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ ρ, alpogeNativeInPhi ρ →
      ρ ∉ alpogeNativeThickPositiveSites T2 u →
      ∀ ψ : AddChar (AlpogeNativeE0 × H) ℂ,
        ‖(w ρ : ℂ) * F ψ (a / w ρ)‖ ≤ K) :
    ‖alpogeNativeProjectionThinReturn F T2 a u t w‖ ≤
      2 * alpogeNativePhiCard H * K := by
  classical
  have hf := alpogeNativePhiCard_pos (H := H)
  have hcol : ∀ g ∈ (Finset.univ.filter
      (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g)) \
        alpogeNativeProjectionThickColours T2 u t,
      ‖alpogeNativeProjectionColourTerm F a t w g‖ ≤
        (Fintype.card (AddChar (AlpogeNativeE0 × H) ℂ) : ℝ) * K := by
    intro g hg
    obtain ⟨hgφ, hgthick⟩ := Finset.mem_sdiff.mp hg
    have hp := alpogeNativeFreezing_partner_inPhi t g (Finset.mem_filter.mp hgφ).2
    have hnot : alpogeNativePartner t g ∉ alpogeNativeThickPositiveSites T2 u := by
      rw [alpogeNativeFreezing_partner_mem_iff]
      exact hgthick
    unfold alpogeNativeProjectionColourTerm
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _ψ : AddChar (AlpogeNativeE0 × H) ℂ, K := by
        apply Finset.sum_le_sum
        intro ψ _
        rw [norm_mul, AddChar.norm_apply, one_mul]
        exact hbound _ hp hnot ψ
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hcount : (((Finset.univ.filter
      (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g)) \
        alpogeNativeProjectionThickColours T2 u t).card : ℝ) ≤
      alpogeNativePhiCard H := by
    rw [alpogeNativePhiCard_eq]
    have h := (Finset.card_le_card (Finset.sdiff_subset
      (s := Finset.univ.filter
        (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g))
      (t := alpogeNativeProjectionThickColours T2 u t))).trans
      alpogeNativeNonPhi_card.le
    exact_mod_cast h
  have hchars : (Fintype.card (AddChar (AlpogeNativeE0 × H) ℂ) : ℝ) =
      2 * alpogeNativePhiCard H := by
    rw [alpogeNativeAddChar_card, alpogeNativePhiCard_eq]
    push_cast
    ring
  have hnorm : ‖(1 : ℂ) / ((alpogeNativePhiSet H).card : ℂ)‖ =
      1 / alpogeNativePhiCard H := by
    rw [norm_div, norm_one, Complex.norm_natCast]
    rfl
  unfold alpogeNativeProjectionThinReturn
  rw [norm_mul, hnorm]
  have hsum := (norm_sum_le _ _).trans (Finset.sum_le_sum hcol)
  rw [Finset.sum_const, nsmul_eq_mul, hchars] at hsum
  have hcountK := mul_le_mul_of_nonneg_right hcount
    (show 0 ≤ 2 * alpogeNativePhiCard H * K by positivity)
  calc
    _ ≤ 1 / alpogeNativePhiCard H *
        (alpogeNativePhiCard H * (2 * alpogeNativePhiCard H * K)) :=
      mul_le_mul_of_nonneg_left (hsum.trans hcountK) (by positivity)
    _ = _ := by field_simp

/-- The averaged thin return is bounded below from thin scales and thin
widths. The height window gives `(x - 1) * b ≤ a t ≤ (x + 1) * b`. -/
theorem alpogeNativeProjectionThinAverage_neg_le
    (A0 : AddSubgroup H)
    (F : AddChar (AlpogeNativeE0 × H) ℂ → ℝ → ℂ)
    (TT T2 : Finset H) {m : ℕ} (a : H → ℝ)
    (w : H → Fin m → AlpogeNativeE0 × H → ℝ) {x b b' X' θ : ℝ}
    (hx : 3 ≤ x) (hb : 0 < b) (hX' : 0 < X') (hbX : b' * X' ≤ x * b)
    (hθ : 0 ≤ θ)
    (hmove : ∀ t ∈ TT, |a t / b - x| ≤ 1)
    (hw : ∀ u j ρ, alpogeNativeInPhi ρ → 0 < w u j ρ)
    (hthin : ∀ u j ρ, alpogeNativeInPhi ρ →
      ρ ∉ alpogeNativeThickPositiveSites T2 u → w u j ρ ≤ 2 * b')
    (hThin : AlpogeNativeThinScales F X' θ) :
    -alpogeNativeProjectionThinAverage A0 F TT T2 a w ≤
      (TT.card : ℝ) * m * (2 * alpogeNativePhiCard H * (x + 1) * b * θ) := by
  classical
  have hf := alpogeNativePhiCard_pos (H := H)
  have hK : 0 ≤ (x + 1) * b * θ := by positivity
  have hpoint : ∀ (u : A0), ∀ t ∈ TT, ∀ j : Fin m,
      -(2 * alpogeNativePhiCard H * ((x + 1) * b * θ)) ≤
        (alpogeNativeProjectionThinReturn F T2 (a t) u t (w u j)).re := by
    intro u t ht j
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hmove t ht)
    have ha1 : (x - 1) * b ≤ a t := by
      have h : x - 1 ≤ a t / b := by linarith
      rwa [le_div_iff₀ hb] at h
    have ha2 : a t ≤ (x + 1) * b := by
      have h : a t / b ≤ x + 1 := by linarith
      rwa [div_le_iff₀ hb] at h
    have hnorm := alpogeNativeProjectionThinReturn_norm_le F T2 (a t) u t (w u j)
      ((x + 1) * b * θ) hK (by
        intro ρ hρ hnot ψ
        have hw0 := hw u j ρ hρ
        have hw2 := hthin u j ρ hρ hnot
        have hy : X' / 3 ≤ a t / w u j ρ := by
          rw [le_div_iff₀ hw0]
          have h1 : X' / 3 * w u j ρ ≤ X' / 3 * (2 * b') :=
            mul_le_mul_of_nonneg_left hw2 (by positivity)
          nlinarith
        have hsc := hThin ψ _ hy
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw0]
        calc
          w u j ρ * ‖F ψ (a t / w u j ρ)‖ ≤
              w u j ρ * (a t / w u j ρ * θ) :=
            mul_le_mul_of_nonneg_left hsc hw0.le
          _ = a t * θ := by field_simp
          _ ≤ (x + 1) * b * θ := mul_le_mul_of_nonneg_right ha2 hθ)
    have := (abs_le.mp ((Complex.abs_re_le_norm _).trans hnorm)).1
    linarith
  have hsum : (∑ _u : A0, ∑ _t ∈ TT, ∑ _j : Fin m,
      -(2 * alpogeNativePhiCard H * ((x + 1) * b * θ))) ≤
      ∑ u : A0, ∑ t ∈ TT, ∑ j : Fin m,
        (alpogeNativeProjectionThinReturn F T2 (a t) u t (w u j)).re :=
    Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun t ht =>
      Finset.sum_le_sum (fun j _ => hpoint u t ht j)))
  have hu : (0 : ℝ) < Fintype.card A0 := by exact_mod_cast Fintype.card_pos
  have hscaled := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ 1 / (Fintype.card A0 : ℝ) by positivity)
  have hconst : (1 / (Fintype.card A0 : ℝ)) *
      (∑ _u : A0, ∑ _t ∈ TT, ∑ _j : Fin m,
        -(2 * alpogeNativePhiCard H * ((x + 1) * b * θ))) =
      -((TT.card : ℝ) * m * (2 * alpogeNativePhiCard H * (x + 1) * b * θ)) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  rw [hconst] at hscaled
  unfold alpogeNativeProjectionThinAverage
  linarith

/-- The thin return under the earned divisor, paid by the explicit cost
window `2 * f * (x + 1) * θ ≤ 1 / x`. Every factor is visible: the bound is
`T * m * b / x` before division and `2 / (Δ * x)` after it. -/
theorem alpogeNativeProjectionThin_normalized_le
    (A0 : AddSubgroup H)
    (F : AddChar (AlpogeNativeE0 × H) ℂ → ℝ → ℂ)
    (TT T2 : Finset H) (hTT : TT.Nonempty) (hT2 : T2.Nonempty)
    {m : ℕ} (hm : 0 < m) (a : H → ℝ)
    (w : H → Fin m → AlpogeNativeE0 × H → ℝ) {x b b' X' θ : ℝ}
    (hx : 3 ≤ x) (hb : 0 < b) (hX' : 0 < X') (hbX : b' * X' ≤ x * b)
    (hθ : 0 ≤ θ)
    (hmove : ∀ t ∈ TT, |a t / b - x| ≤ 1)
    (hw : ∀ u j ρ, alpogeNativeInPhi ρ → 0 < w u j ρ)
    (hthin : ∀ u j ρ, alpogeNativeInPhi ρ →
      ρ ∉ alpogeNativeThickPositiveSites T2 u → w u j ρ ≤ 2 * b')
    (hThin : AlpogeNativeThinScales F X' θ)
    (hcost : 2 * alpogeNativePhiCard H * (x + 1) * θ ≤ 1 / x) :
    -alpogeNativeProjectionThinAverage A0 F TT T2 a w /
        alpogeNativeProjectionDivisor TT T2 m b ≤
      2 / (alpogeNativeProjectionDensity T2 * x) := by
  have hQ := alpogeNativeProjectionDivisor_pos TT T2 hTT hT2 m hm b hb
  have hraw := alpogeNativeProjectionThinAverage_neg_le A0 F TT T2 a w
    hx hb hX' hbX hθ hmove hw hthin hThin
  have hTmb : 0 ≤ (TT.card : ℝ) * m * b := by positivity
  have hpaid : -alpogeNativeProjectionThinAverage A0 F TT T2 a w ≤
      (TT.card : ℝ) * m * b * (1 / x) := by
    have h := mul_le_mul_of_nonneg_left hcost hTmb
    linarith
  have hnorm := alpogeNativeTransportCost_div_projectionDivisor TT T2 m b x
    hTT hT2 hm hb
  calc
    _ ≤ ((TT.card : ℝ) * m * b * (1 / x)) /
        alpogeNativeProjectionDivisor TT T2 m b :=
      div_le_div_of_nonneg_right hpaid hQ.le
    _ = (1 / 2) * ((2 * (TT.card : ℝ) * (m : ℝ) * b / x) /
        alpogeNativeProjectionDivisor TT T2 m b) := by ring
    _ = _ := by rw [hnorm]; ring

end ThinReturn

section Balance

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- The complete zeta-only balance at one scale. The left side is the scalar
`alpogeNativeGzArithmetic x` minus the explicit character and movement
charges. The right side is the physical full-host top excess under the earned
divisor plus `3 / (Δ * x)`: `2 / (Δ * x)` for the thin return and
`1 / (Δ * x)` for the Chebyshev freezing bill. No bound on the top excess is
assumed or proved here. -/
theorem alpogeNativeGz_balance_le
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N : ℕ) {m : ℕ} (TT T2 : Finset H)
    (hTT : TT.Nonempty) (hT2 : T2.Nonempty) (hm : 0 < m)
    (a : H → ℝ) (w : H → Fin m → AlpogeNativeE0 × H → ℝ)
    {x b b' h X' θ Cd B L : ℝ}
    (hx : 3 ≤ x) (hb : 0 < b) (hh : 0 ≤ h) (hX' : 0 < X')
    (hbX : b' * X' ≤ x * b) (hθ : 0 ≤ θ) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hmove : ∀ t ∈ TT, |a t / b - x| ≤ 1)
    (hw : ∀ u j ρ, alpogeNativeInPhi ρ → 0 < w u j ρ)
    (hthick : ∀ u j ρ, ρ ∈ alpogeNativeThickPositiveSites T2 u →
      b ≤ w u j ρ ∧ w u j ρ ≤ b + h)
    (hthin : ∀ u j ρ, alpogeNativeInPhi ρ →
      ρ ∉ alpogeNativeThickPositiveSites T2 u → w u j ρ ≤ 2 * b')
    (hN : ∀ u j t, t ∈ TT →
      ∀ ρ, alpogeNativeInPhi ρ → a t / w u j ρ ≤ (N : ℝ))
    (hNx : x + 1 ≤ (N : ℝ))
    (hder : AlpogeNativeDerivInt inertia frob ell Cd)
    (hval : ∀ ψ ∈ alpogeNativeProjectionChars (⊤ : AddSubgroup H), ψ ≠ 0 →
      ‖alpogeNativeFrobInertiaGPsi inertia frob ell ψ x‖ ≤ B ∧ ‖ell ψ‖ ≤ L)
    (hThin : AlpogeNativeThinScales
      (alpogeNativeFrobInertiaGPsi inertia frob ell) X' θ)
    (hcost : 2 * alpogeNativePhiCard H * (x + 1) * θ ≤ 1 / x)
    (hfreeze : 4 * h * (Real.log 4 + 2) * (x + 1) ≤ b / x) :
    alpogeNativeGzArithmetic x - 3 * B -
        (Cd + 3 * (Real.log (x + 1) + Cd + L)) ≤
      alpogeNativePhysicalSubgroupTopExcess ⊤ inertia frob ell N TT a w /
          alpogeNativeProjectionDivisor TT T2 m b +
        3 / (alpogeNativeProjectionDensity T2 * x) := by
  have hx0 : 0 < x := by linarith
  have hΔ : 0 < alpogeNativeProjectionDensity T2 := by
    unfold alpogeNativeProjectionDensity
    have h1 : (0 : ℝ) < T2.card := by exact_mod_cast Finset.card_pos.mpr hT2
    have h2 : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
    positivity
  have hheight : ∀ t ∈ TT, 0 < a t ∧ a t / b ≤ x + 1 := by
    intro t ht
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hmove t ht)
    refine ⟨?_, by linarith⟩
    have hpos : 0 < a t / b := by linarith
    have := mul_pos hpos hb
    rwa [div_mul_cancel₀ _ hb.ne'] at this
  have hbal := alpogeNativeGz_sub_le_projectedSignal inertia frob ell TT hTT a
    (b := b) (by linarith : (2 : ℝ) ≤ x) hB hL hmove hder hval
  have hproj := alpogeNativeCompleteProjection_normalized_le ⊤ inertia frob ell
    N TT T2 hTT hT2 hm (fun s _ => AddSubgroup.mem_top s) a b h (x + 1) w
    hb hh (fun t ht => (hheight t ht).1) (fun t ht => (hheight t ht).2)
    hw hthick hN (fun t ht => (hheight t ht).2.trans hNx)
  have hthinPaid := alpogeNativeProjectionThin_normalized_le ⊤
    (alpogeNativeFrobInertiaGPsi inertia frob ell) TT T2 hTT hT2 hm a w
    hx hb hX' hbX hθ hmove hw hthin hThin hcost
  have hfrozen : 4 * h * (Real.log 4 + 2) * (x + 1) /
      (b * alpogeNativeProjectionDensity T2) ≤
      1 / (alpogeNativeProjectionDensity T2 * x) := by
    calc
      _ ≤ (b / x) / (b * alpogeNativeProjectionDensity T2) :=
        div_le_div_of_nonneg_right hfreeze (by positivity)
      _ = _ := by field_simp
  have hsplit :
      (alpogeNativePhysicalSubgroupTopExcess ⊤ inertia frob ell N TT a w -
          alpogeNativeProjectionThinAverage ⊤
            (alpogeNativeFrobInertiaGPsi inertia frob ell) TT T2 a w) /
          alpogeNativeProjectionDivisor TT T2 m b =
        alpogeNativePhysicalSubgroupTopExcess ⊤ inertia frob ell N TT a w /
            alpogeNativeProjectionDivisor TT T2 m b +
          -alpogeNativeProjectionThinAverage ⊤
            (alpogeNativeFrobInertiaGPsi inertia frob ell) TT T2 a w /
            alpogeNativeProjectionDivisor TT T2 m b := by ring
  have hthree : 3 / (alpogeNativeProjectionDensity T2 * x) =
      2 / (alpogeNativeProjectionDensity T2 * x) +
        1 / (alpogeNativeProjectionDensity T2 * x) := by ring
  rw [hsplit] at hproj
  rw [hthree]
  linarith

end Balance

end RHLean.Analysis

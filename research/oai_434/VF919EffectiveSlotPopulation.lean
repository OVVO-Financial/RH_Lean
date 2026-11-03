import «research.oai_434.VF919ActualSlotMinRetighten»

/-!
# Effective finite-slot population for the pinned OpenAI detector

The original constructor uses affine weights w j = 1 + j/N,
ell j = w j / (6 * sum w). Its unbounded existential choice of N loses
the numerical lower bound for the true minimum.

Here N = ceil(1/L) + 1 is an explicit bounded count and the affine family
is unchanged. This is a FINITE SOURCE theorem, not a new zero-free claim.
-/

namespace OAI
noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.RHLeanEffectiveSlotMinimum

noncomputable def effectiveSlotCount (L : ℝ) : ℕ := ⌈1/L⌉₊ + 1

private theorem effectiveSlotCount_pos (L : ℝ) : 0 < effectiveSlotCount L := by
  unfold effectiveSlotCount
  omega

private theorem effectiveSlotCount_bounds (L : ℝ) (hL : 0 < L) :
    1/L < (effectiveSlotCount L : ℝ) ∧
    (effectiveSlotCount L : ℝ) < 1/L + 2 := by
  have hceil := Nat.le_ceil (1/L)
  have hceilUpper : (⌈1/L⌉₊ : ℝ) < 1/L + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  unfold effectiveSlotCount
  push_cast
  constructor <;> linarith

private def effectiveSlotWeight (N : ℕ) (j : Fin N) : ℝ :=
  1 + (j.val : ℝ) / (N : ℝ)

private def effectiveSlotWeightSum (N : ℕ) : ℝ :=
  ∑ j : Fin N, effectiveSlotWeight N j

private theorem weight_range (N : ℕ) (hN : 0 < N) (j : Fin N) :
    1 ≤ effectiveSlotWeight N j ∧ effectiveSlotWeight N j < 2 := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hj : (j.val : ℝ) < N := by exact_mod_cast j.isLt
  have hdiv : (j.val : ℝ) / N < 1 := (div_lt_one hn).mpr hj
  dsimp [effectiveSlotWeight]
  constructor
  · linarith [div_nonneg (Nat.cast_nonneg j.val) hn.le]
  · linarith

private theorem weight_sum_bounds (N : ℕ) (hN : 0 < N) :
    (N : ℝ) ≤ effectiveSlotWeightSum N ∧
    effectiveSlotWeightSum N ≤ 2 * (N : ℝ) := by
  unfold effectiveSlotWeightSum
  constructor
  · calc
      (N : ℝ) = ∑ _j : Fin N, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j _ => (weight_range N hN j).1)
  · calc
      (∑ j : Fin N, effectiveSlotWeight N j) ≤
          ∑ _j : Fin N, (2 : ℝ) :=
        Finset.sum_le_sum (fun j _ => (weight_range N hN j).2.le)
      _ = 2 * (N : ℝ) := by simp

noncomputable def effectiveSlotLength (N : ℕ) (j : Fin N) : ℝ :=
  effectiveSlotWeight N j / (6 * effectiveSlotWeightSum N)

theorem effectiveSlotLength_pos (N : ℕ) (hN : 0 < N) (j : Fin N) :
    0 < effectiveSlotLength N j := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have ha : 0 < effectiveSlotWeightSum N :=
    lt_of_lt_of_le hn (weight_sum_bounds N hN).1
  unfold effectiveSlotLength
  exact div_pos (by linarith [(weight_range N hN j).1]) (by positivity)

theorem effectiveSlotLength_sum (N : ℕ) (hN : 0 < N) :
    (∑ j : Fin N, effectiveSlotLength N j) = (1/6 : ℝ) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have ha : 0 < effectiveSlotWeightSum N :=
    lt_of_lt_of_le hn (weight_sum_bounds N hN).1
  unfold effectiveSlotLength
  rw [← Finset.sum_div]
  change effectiveSlotWeightSum N / (6 * effectiveSlotWeightSum N) = (1/6 : ℝ)
  field_simp

theorem effectiveSlotLength_injective (N : ℕ) (hN : 0 < N) :
    Function.Injective (effectiveSlotLength N) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have ha : 0 < effectiveSlotWeightSum N :=
    lt_of_lt_of_le hn (weight_sum_bounds N hN).1
  intro j k he
  have hden : (6 * effectiveSlotWeightSum N) ≠ 0 := by positivity
  have hw : effectiveSlotWeight N j = effectiveSlotWeight N k := by
    exact (div_left_inj' hden).mp he
  have hquot : (j.val : ℝ) / N = (k.val : ℝ) / N := by
    dsimp [effectiveSlotWeight] at hw
    linarith
  have hcast : (j.val : ℝ) = (k.val : ℝ) :=
    (div_left_inj' hn.ne').mp hquot
  exact Fin.ext (by exact_mod_cast hcast)

/-- Same original affine weights, bounded N and explicit positive floor. -/
theorem effective_slot_population
    (L : ℝ) (hL : 0 < L) (hL1 : L ≤ 1) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) < 1/L + 2 ∧
      ∃ ell : Fin N → ℝ,
        Function.Injective ell ∧
        (∑ j, ell j) = 1/6 ∧
        ∀ j, 0 < ell j ∧ ell j < L ∧ L/36 ≤ ell j := by
  let N := effectiveSlotCount L
  let ell := effectiveSlotLength N
  have hNp : 0 < N := effectiveSlotCount_pos L
  have hn : 0 < (N : ℝ) := by exact_mod_cast hNp
  obtain ⟨hNlo, hNhi⟩ := effectiveSlotCount_bounds L hL
  obtain ⟨hAlow, hAhigh⟩ := weight_sum_bounds N hNp
  have hApos : 0 < effectiveSlotWeightSum N := lt_of_lt_of_le hn hAlow
  have hNL : (N : ℝ) * L ≤ 3 := by
    have hh := mul_le_mul_of_nonneg_right hNhi.le hL.le
    have hdiv : (1/L) * L = 1 := by field_simp
    nlinarith only [hh, hdiv, hL1, hL]
  have hNLgt : 1 < (N : ℝ) * L := by
    have hh := mul_lt_mul_of_pos_right hNlo hL
    have hdiv : (1/L) * L = 1 := by field_simp
    nlinarith only [hh, hdiv]
  have hLA : L * effectiveSlotWeightSum N ≤ 6 := by
    have hh := mul_le_mul_of_nonneg_left hAhigh hL.le
    nlinarith only [hh, hNL]
  refine ⟨N, hNp, hNhi, ell, effectiveSlotLength_injective N hNp,
    effectiveSlotLength_sum N hNp, ?_⟩
  intro j
  have hw1 := (weight_range N hNp j).1
  have hw2 := (weight_range N hNp j).2
  refine ⟨effectiveSlotLength_pos N hNp j, ?_, ?_⟩
  · change effectiveSlotWeight N j / (6 * effectiveSlotWeightSum N) < L
    apply (div_lt_iff₀ (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left hAlow hL.le
    nlinarith only [hh, hNLgt, hw2]
  · change L/36 ≤ effectiveSlotWeight N j / (6 * effectiveSlotWeightSum N)
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 36)
      (by positivity : 0 < 6 * effectiveSlotWeightSum N)).mpr
    nlinarith only [hLA, hw1]

#print axioms effective_slot_population
end SevenEighths.RHLeanEffectiveSlotMinimum
end
end OAI

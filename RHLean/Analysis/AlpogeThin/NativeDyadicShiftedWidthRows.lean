import RHLean.Analysis.AlpogeNativeLocalGainSource

/-! Shifted tops can give the same positive width site in the original
Frobenius rows. The atom still retains its own height and prime power. -/

set_option autoImplicit false
namespace RHLean.Analysis

/-- A shift of the top by two Frobenius steps preserves the positive
    partner after shortening the original prime exponent by two. -/
theorem alpogeNativePartner_add_two {H : Type*} [AddCommGroup H]
    (t : H) (g : AlpogeNativeE0 × H) (i : ℕ) :
    alpogeNativePartner t ((i + 2) • g) = alpogeNativePartner (t + 2 • g.2) (i • g) := by
  have hb : ∀ x : ZMod 2, (2 : ℕ) • x = 0 := by decide
  have hg : (2 : ℕ) • g = alpogeNativeTopPl ((2 : ℕ) • g.2) := by
    apply Prod.ext
    · exact Prod.ext (hb g.1.1) (hb g.1.2)
    · rfl
  have ht : alpogeNativeTopPl (t + 2 • g.2) =
      alpogeNativeTopPl t + alpogeNativeTopPl (2 • g.2) := by
    apply Prod.ext
    · change (0 : AlpogeNativeE0) = 0 + 0
      rw [zero_add]
    · rfl
  unfold alpogeNativePartner
  rw [add_nsmul, hg, ht]
  abel

/-- An actual measurement factoring through one such width site cannot
    detect a prescribed nonzero residue while vanishing on its duplicate. -/
theorem alpogeNativePartner_add_two_no_separation {H O : Type*}
    [AddCommGroup H] [CommRing O] (I : Ideal O) (u : O) (hu : u ∉ I)
    (t : H) (g : AlpogeNativeE0 × H) (i : ℕ) (f : AlpogeNativeE0 × H → O) :
    ¬ (f (alpogeNativePartner t ((i + 2) • g)) - u ∈ I ∧
       f (alpogeNativePartner (t + 2 • g.2) (i • g)) ∈ I) := by
  rintro ⟨hE, hC⟩
  rw [alpogeNativePartner_add_two] at hE
  let z := f (alpogeNativePartner (t + 2 • g.2) (i • g))
  have hz : z - (z - u) ∈ I := I.sub_mem hC hE
  rw [show z - (z - u) = u by ring] at hz
  exact hu hz

namespace AlpogeThin

/-- The two *actual* active local source atoms have precisely the indicated
    height difference. Their common width cancels with its original sign. -/
theorem nativeDyadicLocalSourceAtom_sub_of_top_add_two
    (e q d p i : ℕ) [Fact q.Prime] [Fact d.Prime]
    (t : AlpogeNativeDyadicH e) (a b : ℝ) (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ) :
    let g := (alpogeNativeHostData e q d).frob p
    let s := t + (2 : ℕ) • g.2
    let width := w (alpogeNativePartner s (i • g))
    width ≤ a / (p : ℝ) ^ (i + 2) → width ≤ b / (p : ℝ) ^ i →
      nativeDyadicLocalSourceAtom e q d p a t w (i+2) -
        nativeDyadicLocalSourceAtom e q d p b s w i =
        a / (p : ℝ) ^ (i+2) - b / (p : ℝ) ^ i := by
  dsimp only
  intro ha hb
  simp only [nativeDyadicLocalSourceAtom, alpogeNativeSiteCut, Complex.ofReal_re,
    Nat.cast_pow, alpogeNativePartner_add_two, max_eq_left (sub_nonneg.mpr ha),
    max_eq_left (sub_nonneg.mpr hb)]
  ring

/-- After restoring each clipped part, the whole tower of shifted differences
reads a single height difference. On active reads both clipping terms vanish. -/
theorem nativeDyadicLocalSourceAtom_scaled_shift_difference
    (e q d p i : ℕ) [Fact q.Prime] [Fact d.Prime] (hp : p ≠ 0)
    (t : AlpogeNativeDyadicH e) (a b : ℝ) (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ) :
    let g := (alpogeNativeHostData e q d).frob p
    let s := t + (2 : ℕ) • g.2
    let width := w (alpogeNativePartner s (i • g))
    (p : ℝ) ^ (i + 2) *
      ((nativeDyadicLocalSourceAtom e q d p a t w (i + 2) -
          max (width - a / (p : ℝ) ^ (i + 2)) 0) -
        (nativeDyadicLocalSourceAtom e q d p b s w i -
          max (width - b / (p : ℝ) ^ i) 0)) = a - (p : ℝ) ^ 2 * b := by
  have splitCut (x y : ℝ) : max (x - y) 0 - max (y - x) 0 = x - y := by
    rcases le_total y x with h | h
    · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h), sub_zero]
    · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
      ring
  have hp' : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have cancel (k : ℕ) (x : ℝ) : (p : ℝ) ^ k * (x / (p : ℝ) ^ k) = x := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ (pow_ne_zero k hp')]
  dsimp only
  simp only [nativeDyadicLocalSourceAtom, alpogeNativeSiteCut, Complex.ofReal_re,
    Nat.cast_pow, alpogeNativePartner_add_two, splitCut, sub_sub_sub_cancel_right]
  rw [mul_sub, cancel, pow_add, mul_comm ((p : ℝ) ^ i) ((p : ℝ) ^ 2),
    mul_assoc, cancel]

end AlpogeThin
end RHLean.Analysis

open scoped BigOperators Classical

namespace RHLean.Analysis

/-- For a fixed prime displacement a later read at this site determines its
top uniquely. Its exponent can repeat at a different destination. -/
theorem alpogeNativePartner_even_offset_iff {H : Type*} [AddCommGroup H]
    (s t : H) (g : AlpogeNativeE0 × H) (i k : ℕ) :
    alpogeNativePartner t ((i + 2 * k) • g) = alpogeNativePartner s (i • g) ↔
      t = s - (2 * k) • g.2 := by
  have hshift (j : ℕ) (v : H) : alpogeNativePartner v ((i + 2 * j) • g) =
      alpogeNativePartner (v + (2 * j) • g.2) (i • g) := by
    induction j generalizing v with
    | zero => simp
    | succ j ih =>
      rw [show i + 2 * (j + 1) = (i + 2 * j) + 2 by omega,
        alpogeNativePartner_add_two, ih, Nat.mul_succ, add_nsmul]
      congr 1
      abel
  rw [hshift]
  constructor
  · intro heq
    have h := congrArg Prod.snd heq
    change _ + (t + (2 * k) • g.2) = _ + s at h
    exact eq_sub_iff_add_eq.mpr (add_left_cancel h)
  · intro heq
    rw [eq_sub_iff_add_eq.mp heq]

namespace AlpogeThin

/-- On one measured row all the later reads at the same destination, from
every eligible top and odd exponent up to N, cost at most 2/(p²-1) times
the leading clipped read. Any omitted intermediate top is allowed. -/
theorem nativeDyadic_sharedWidth_laterReads_le (e q d p N i : ℕ)
    [Fact q.Prime] [Fact d.Prime] (hp : p.Prime)
    (TT : Finset (AlpogeNativeDyadicH e)) (s : AlpogeNativeDyadicH e) (hs : s ∈ TT)
    (a : AlpogeNativeDyadicH e → ℝ) (x b : ℝ) (hx : 1 ≤ x) (hb : 0 < b)
    (ha : ∀ t ∈ TT, a t / b ∈ Set.Icc x (x + 1))
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (hw : 0 ≤ w (alpogeNativePartner s (i • (alpogeNativeHostData e q d).frob p))) :
    let g := (alpogeNativeHostData e q d).frob p
    let top := fun k : ℕ => s - (2 * k) • g.2
    (∑ k ∈ (Finset.Icc 1 N).filter (fun k => top k ∈ TT ∧ i + 2 * k ≤ N),
      nativeDyadicLocalSourceAtom e q d p (a (top k)) (top k) w (i + 2 * k)) ≤
      2 * nativeDyadicLocalSourceAtom e q d p (a s) s w i / ((p : ℝ)^2 - 1) := by
  classical
  let g := (alpogeNativeHostData e q d).frob p
  let top := fun k : ℕ => s - (2 * k) • g.2
  let J := (Finset.Icc 1 N).filter (fun k => top k ∈ TT ∧ i + 2 * k ≤ N)
  let P : ℝ := p
  let r := (P ^ 2)⁻¹
  let A := nativeDyadicLocalSourceAtom e q d p (a s) s w i
  change (∑ k ∈ J, _) ≤ 2 * A / (P ^ 2 - 1)
  have hP : (2 : ℝ) ≤ P := by
    change (2 : ℝ) ≤ (p : ℝ)
    exact_mod_cast hp.two_le
  have hPpos : 0 < P := by linarith
  have hP2 : 2 ≤ P ^ 2 := by nlinarith [sq_nonneg (P - 2)]
  have hr0 : 0 ≤ r := inv_nonneg.mpr (sq_nonneg _)
  have hr1 : r < 1 := (inv_lt_one₀ (sq_pos_of_pos hPpos)).2 (by linarith)
  have hA : 0 ≤ A := le_max_right _ _
  have hpoint (k : ℕ) (hk : k ∈ J) :
      nativeDyadicLocalSourceAtom e q d p (a (top k)) (top k) w (i + 2 * k) ≤
        (2 * A) * r ^ k := by
    obtain ⟨hkI, ht, _⟩ := Finset.mem_filter.mp hk
    have hrk : r ^ k ≤ r := by
      simpa only [pow_one] using pow_le_pow_of_le_one hr0 hr1.le (Finset.mem_Icc.mp hkI).1
    have hfactor : 2 * r ^ k ≤ 1 := by
      have hinv : 2 * r ≤ 1 := by
        change 2 * (P ^ 2)⁻¹ ≤ 1
        rwa [← div_eq_mul_inv, div_le_one (sq_pos_of_pos hPpos)]
      linarith
    have hheight : a (top k) ≤ 2 * a s := by
      have ht' := (div_le_iff₀ hb).mp (ha _ ht).2
      have hs' := (le_div_iff₀ hb).mp (ha _ hs).1
      nlinarith [mul_nonneg (sub_nonneg.mpr hx) hb.le]
    have hscale : a (top k) / P ^ (i + 2 * k) ≤
        (2 * r ^ k) * (a s / P ^ i) := by
      rw [pow_add, pow_mul, ← div_div]
      calc
        _ ≤ (2 * a s / P ^ i) / (P ^ 2) ^ k :=
          div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hheight (by positivity))
            (by positivity)
        _ = _ := by simp only [r, inv_pow, div_eq_mul_inv]; ring
    have hsite := (alpogeNativePartner_even_offset_iff s (top k) g i k).2 rfl
    change max (a (top k) / ((p ^ (i + 2 * k) : ℕ) : ℝ) -
        w (alpogeNativePartner (top k) ((i + 2 * k) • g))) 0 ≤ _
    rw [hsite, Nat.cast_pow]
    let W := w (alpogeNativePartner s (i • g))
    have hW : 0 ≤ W := hw
    have hcut : a s / P ^ i - W ≤ A := by
      change a s / (p : ℝ) ^ i - W ≤ max (a s / ((p ^ i : ℕ) : ℝ) - W) 0
      rw [Nat.cast_pow]
      exact le_max_left _ _
    have hweight := mul_le_mul_of_nonneg_left hcut
      (show 0 ≤ (2 : ℝ) * r ^ k from mul_nonneg (by norm_num) (pow_nonneg hr0 k))
    have hW' := mul_le_mul_of_nonneg_right hfactor hW
    change max (a (top k) / P ^ (i + 2 * k) - W) 0 ≤ _
    exact max_le (by linarith only [hscale, hweight, hW']) (mul_nonneg (by positivity) (pow_nonneg hr0 k))
  have hsub : J ⊆ Finset.Ico 1 (N + 1) := by
    intro k hk
    have hi := Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1
    exact Finset.mem_Ico.mpr ⟨hi.1, Nat.lt_succ_of_le hi.2⟩
  have hsum : ∑ k ∈ J, r ^ k ≤ r / (1 - r) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => pow_nonneg hr0 k)).trans
      (by simpa only [pow_one] using
        (geom_sum_Ico_le_of_lt_one (x := r) (m := 1) (n := N + 1) hr0 hr1))
  calc
    _ ≤ ∑ k ∈ J, (2 * A) * r ^ k := Finset.sum_le_sum hpoint
    _ ≤ (2 * A) * (r / (1 - r)) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
      dsimp only [r]
      have hden : 1 - (P ^ 2)⁻¹ ≠ 0 := (sub_pos.mpr hr1).ne'
      field_simp [hPpos.ne', hden, show P ^ 2 - 1 ≠ 0 by linarith] <;> ring

end AlpogeThin
end RHLean.Analysis

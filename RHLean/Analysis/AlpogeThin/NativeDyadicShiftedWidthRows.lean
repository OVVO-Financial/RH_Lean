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


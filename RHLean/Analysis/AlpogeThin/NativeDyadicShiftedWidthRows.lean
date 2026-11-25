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

end AlpogeThin
end RHLean.Analysis


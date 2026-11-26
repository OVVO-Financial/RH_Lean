import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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
      field_simp [hPpos.ne', hden, show P ^ 2 - 1 ≠ 0 by linarith]

/-- Simultaneous recovery of integral height readings at one prime. Each
admissible collar contains a full period modulo p^k. The same heights realize
every mixed first/third-power read, including on cyclically returning tops.
On an unramified inert prime these are precisely the two nonzero census rows
(up to their common prime weight). -/
theorem nativeDyadic_activeShift_residues_in_window
    (e q d p k : ℕ) [Fact q.Prime] [Fact d.Prime] (hp : p.Prime)
    (x b W : ℝ) (hb : 0 < b) (hroom : ((p ^ k : ℕ) : ℝ) ≤ W)
    (hactive : 2 * (p : ℝ)^3 ≤ x) (y : AlpogeNativeDyadicH e → ZMod (p ^ k)) :
    let g := (alpogeNativeHostData e q d).frob p
    let shift := fun t : AlpogeNativeDyadicH e => t + (2 : ℕ) • g.2
    ∃ a : AlpogeNativeDyadicH e → ℤ,
      (∀ t, (a t : ℝ) ∈ Set.Ico (x * b) (x * b + W)) ∧
      (∀ t, (a t : ZMod (p ^ k)) - (p : ZMod (p ^ k))^2 * (a (shift t) : ZMod (p ^ k)) = y t) ∧
      ∀ (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ) t,
        w (alpogeNativePartner (shift t) g) ≤ 2 * b →
        (p : ℝ)^3 * (nativeDyadicLocalSourceAtom e q d p (a t) t w 3 -
            nativeDyadicLocalSourceAtom e q d p (a (shift t)) (shift t) w 1) =
          (a t : ℝ) - (p : ℝ)^2 * (a (shift t) : ℝ) := by
  classical
  let : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let g := (alpogeNativeHostData e q d).frob p
  let shift := fun t : AlpogeNativeDyadicH e => t + (2 : ℕ) • g.2
  let c : ZMod (p ^ k) := (p : ZMod (p ^ k))^2
  let F : ℕ → AlpogeNativeDyadicH e → ZMod (p ^ k) :=
    Nat.rec (fun _ => 0) (fun _ prev t => y t + c * prev (shift t))
  have hdiff (n : ℕ) : ∀ t, F n t - c * F n (shift t) = y t - c^n * y (shift^[n] t) := by
    induction n with
    | zero => intro t; simp [F]
    | succ n ih =>
      intro t
      change (y t + c * F n (shift t)) - c * (y (shift t) + c * F n (shift (shift t))) = _
      rw [Function.iterate_succ_apply, pow_succ]
      linear_combination c * ih (shift t)
  have hzero : c^k = 0 := by
    have hm : (p : ZMod (p ^ k))^k = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    dsimp only [c]
    rw [← pow_mul, Nat.mul_comm 2 k, pow_mul, hm]
    norm_num
  let lo : ℤ := ⌈x * b⌉
  let a := fun t => lo + (((F k t - (lo : ZMod (p ^ k))).val : ℕ) : ℤ)
  have hres (t) : (a t : ZMod (p ^ k)) = F k t := by
    simp only [a, Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val]
    ring
  have hwindow (t) : (a t : ℝ) ∈ Set.Ico (x*b) (x*b+W) := by
    let m := (F k t - (lo : ZMod (p ^ k))).val
    have hm := Nat.succ_le_of_lt (ZMod.val_lt (F k t - (lo : ZMod (p ^ k))))
    have hm' : (m : ℝ) + 1 ≤ ((p ^ k : ℕ) : ℝ) := by exact_mod_cast hm
    have heq : (a t : ℝ) = (lo : ℝ) + (m : ℝ) := by simp only [a, m, Int.cast_add, Int.cast_natCast]
    rw [heq]
    exact ⟨(Int.le_ceil (x*b)).trans (le_add_of_nonneg_right (Nat.cast_nonneg m)),
      by linarith only [show (lo : ℝ) < x*b+1 from Int.ceil_lt_add_one _, hm', hroom]⟩
  refine ⟨a, hwindow, fun t => ?_, fun w t hw => ?_⟩
  · rw [hres, hres]
    simpa only [hzero, zero_mul, sub_zero] using hdiff k t
  · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
    have hthree (s) : (2*b) * (p : ℝ)^3 ≤ (a s : ℝ) := by
      calc
        _ = (2*(p : ℝ)^3)*b := by ring
        _ ≤ x*b := mul_le_mul_of_nonneg_right hactive hb.le
        _ ≤ _ := (hwindow s).1
    have hone (s) : (2*b) * (p : ℝ)^1 ≤ (a s : ℝ) :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp1 (by decide : 1 ≤ 3))
        (by positivity : 0 ≤ 2*b)).trans (hthree s)
    have hw' : w (alpogeNativePartner (shift t) ((1 : ℕ) • g)) ≤ 2*b := by simpa only [one_nsmul] using hw
    have hcut := nativeDyadicLocalSourceAtom_sub_of_top_add_two e q d p 1 t (a t) (a (shift t)) w
      (hw'.trans ((le_div_iff₀ (pow_pos hp0 3)).2 (hthree t)))
      (hw'.trans ((le_div_iff₀ (pow_pos hp0 1)).2 (hone (shift t))))
    rw [hcut]
    field [hp0.ne']

/-- An injective assignment of integral native top heights can realize every
specified active Frobenius difference at all selected primes simultaneously.
The interval cost is the number of tops times one common CRT period. -/
theorem nativeDyadic_activeShift_joint_injective_heights
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (P : Finset ℕ) (k : ℕ → ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (x b W : ℝ) (hb : 0 < b)
    (hactive : ∀ p ∈ P, 2 * (p : ℝ)^3 ≤ x)
    (hroom : ((Fintype.card (AlpogeNativeDyadicH e) * ∏ p : P, (p : ℕ)^k p : ℕ) : ℝ) ≤ W)
    (y : (p : P) → AlpogeNativeDyadicH e → ZMod ((p : ℕ)^k p)) :
    ∃ a : AlpogeNativeDyadicH e → ℤ, Function.Injective a ∧
      (∀ t, (a t : ℝ) ∈ Set.Ico (x*b) (x*b+W)) ∧
      ∀ (p : P) t,
        let s := t + (2 : ℕ) • ((alpogeNativeHostData e q d).frob p).2
        (a t : ZMod ((p : ℕ)^k p)) - ((p : ℕ) : ZMod ((p : ℕ)^k p))^2 *
          (a s : ZMod ((p : ℕ)^k p)) = y p t := by
  classical
  let m := fun p : P => (p : ℕ)^k p
  let M := ∏ p : P, m p
  have hne (p : P) : m p ≠ 0 := pow_ne_zero _ (hP p p.property).ne_zero
  have pair : Set.Pairwise (↑(Finset.univ : Finset P) : Set P) (fun p r => (m p).Coprime (m r)) := by
    intro p _ r _ h
    exact (((Nat.coprime_primes (hP p p.property) (hP r r.property)).2
      (fun he => h (Subtype.ext he))).pow_left _).pow_right _
  let shift := fun (p : P) (t : AlpogeNativeDyadicH e) => t + (2 : ℕ) • ((alpogeNativeHostData e q d).frob p).2
  have one (p : P) : ∃ u : AlpogeNativeDyadicH e → ℤ, ∀ t,
      (u t : ZMod (m p)) - ((p : ℕ) : ZMod (m p))^2 * (u (shift p t) : ZMod (m p)) = y p t := by
    obtain ⟨u, _, h, _⟩ := nativeDyadic_activeShift_residues_in_window e q d p (k p) (hP p p.property)
      x b (m p) hb le_rfl (hactive p p.property) (y p)
    exact ⟨u, h⟩
  choose u hu using one
  let ix := fun t => ((Fintype.equivFin (AlpogeNativeDyadicH e)) t).val
  let lo := fun t => ⌈x*b⌉ + ((ix t * M : ℕ) : ℤ)
  let offset := fun t (p : P) => ((u p t : ZMod (m p)) - (lo t : ZMod (m p))).val
  let c := fun t => Nat.chineseRemainderOfFinset (offset t) m Finset.univ (fun p _ => hne p) pair
  let a := fun t => lo t + ((c t).val : ℤ)
  have hc (t) : (c t).val < M :=
    Nat.chineseRemainderOfFinset_lt_prod (offset t) m (fun p _ => hne p) pair
  have hres (p : P) (t) : (a t : ZMod (m p)) = (u p t : ZMod (m p)) := by
    let : NeZero (m p) := ⟨hne p⟩
    have hr := (ZMod.natCast_eq_natCast_iff _ _ _).2 ((c t).property p (Finset.mem_univ p))
    change (((c t).val : ℕ) : ZMod (m p)) = (((offset t p : ℕ)) : ZMod (m p)) at hr
    simp only [offset, ZMod.natCast_zmod_val] at hr
    change ((lo t + ((c t).val : ℤ) : ℤ) : ZMod (m p)) = _
    rw [Int.cast_add, Int.cast_natCast, hr]
    ring
  have hstrip (t) : (a t : ℝ) ∈ Set.Ico (x*b + (ix t : ℝ)*M) (x*b + ((ix t : ℝ)+1)*M) := by
    have hc' : ((c t).val : ℝ) + 1 ≤ M := by exact_mod_cast Nat.succ_le_of_lt (hc t)
    have ha : (a t : ℝ) = (⌈x*b⌉ : ℝ) + (ix t : ℝ)*M + ((c t).val : ℝ) := by
      simp only [a, lo, Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    rw [ha]
    constructor
    · linarith only [Int.le_ceil (x*b), Nat.cast_nonneg (α := ℝ) (c t).val]
    · linarith only [Int.ceil_lt_add_one (x*b), hc']
  have horder (s t) (h : ix s < ix t) : (a s : ℝ) < (a t : ℝ) :=
    (hstrip s).2.trans_le ((add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.succ_le_of_lt h : (ix s : ℝ)+1 ≤ ix t) (Nat.cast_nonneg (α := ℝ) M))).trans (hstrip t).1)
  refine ⟨a, ?_, ?_, fun p t => ?_⟩
  · intro s t he
    have he' : (a s : ℝ) = (a t : ℝ) := congrArg (fun z : ℤ => (z : ℝ)) he
    apply (Fintype.equivFin (AlpogeNativeDyadicH e)).injective
    apply Fin.ext
    rcases lt_trichotomy (ix s) (ix t) with h | h | h
    · exact ((ne_of_lt (horder s t h)) he').elim
    · exact h
    · exact ((ne_of_lt (horder t s h)) he'.symm).elim
  · intro t
    have hindex : (ix t : ℝ) + 1 ≤ Fintype.card (AlpogeNativeDyadicH e) := by
      exact_mod_cast Nat.succ_le_of_lt (((Fintype.equivFin (AlpogeNativeDyadicH e)) t).isLt)
    have hbudget : (Fintype.card (AlpogeNativeDyadicH e) : ℝ) * M ≤ W := by
      simpa only [Nat.cast_mul] using hroom
    exact ⟨(le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))).trans (hstrip t).1,
      (hstrip t).2.trans_le (add_le_add le_rfl ((mul_le_mul_of_nonneg_right hindex (Nat.cast_nonneg _)).trans hbudget))⟩
  · change (a t : ZMod (m p)) - ((p : ℕ) : ZMod (m p))^2 * (a (shift p t) : ZMod (m p)) = _
    rw [hres, hres]
    exact hu p t

/-- The scaled first/third-power difference on the full host, with the real
factor p² divided out. Its translate acts on the original height coordinates. -/
noncomputable def nativeDyadicNormalizedHeightShift (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (p : ℕ) (v : EuclideanSpace ℂ (AlpogeNativeDyadicH e)) :
    EuclideanSpace ℂ (AlpogeNativeDyadicH e) :=
  ((p : ℝ)^2)⁻¹ • v - WithLp.toLp 2
    (fun t => v (t + (2 : ℕ) • ((alpogeNativeHostData e q d).frob p).2))

/-- All distinct prime admissions together distort Euclidean lengths in the
height coordinates by at most two, uniformly in the host, order and rank. -/
theorem nativeDyadic_normalizedHeightShift_chain_norm (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (primes : List ℕ) (hn : primes.Nodup) (hp : ∀ p ∈ primes, Nat.Prime p)
    (v : EuclideanSpace ℂ (AlpogeNativeDyadicH e)) :
    ‖v‖ / 2 ≤ ‖primes.foldr (nativeDyadicNormalizedHeightShift e q d) v‖ ∧
    ‖primes.foldr (nativeDyadicNormalizedHeightShift e q d) v‖ ≤ 2 * ‖v‖ := by
  classical
  let r := fun p : ℕ => ((p : ℝ)^2)⁻¹
  let lo := fun p : ℕ => 1 - r p
  have hr (p : ℕ) (h : 2 ≤ p) : 0 ≤ r p ∧ r p ≤ 1 := by
    have hreal : 2 ≤ (p : ℝ) := by exact_mod_cast h
    have hs : 1 ≤ (p : ℝ)^2 := by nlinarith [sq_nonneg ((p : ℝ)-2)]
    exact ⟨inv_nonneg.mpr (sq_nonneg _), (inv_le_one₀ (zero_lt_one.trans_le hs)).2 hs⟩
  let op := nativeDyadicNormalizedHeightShift e q d
  have step (p : ℕ) (h : 2 ≤ p) (u : EuclideanSpace ℂ (AlpogeNativeDyadicH e)) :
      lo p * ‖u‖ ≤ ‖op p u‖ ∧ lo p * ‖op p u‖ ≤ ‖u‖ := by
    let σ := Equiv.addRight ((2 : ℕ) • ((alpogeNativeHostData e q d).frob p).2)
    let T := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ.symm
    have hT : ‖T u‖ = ‖u‖ := T.norm_map u
    have hscalar : ‖r p • u‖ = r p * ‖u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hr p h).1]
    change lo p * ‖u‖ ≤ ‖r p • u - T u‖ ∧ lo p * ‖r p • u - T u‖ ≤ ‖u‖
    have lower := norm_sub_norm_le (T u) (r p • u)
    rw [norm_sub_rev (T u), hT, hscalar] at lower
    have upper := norm_sub_le (r p • u) (T u)
    rw [hscalar, hT] at upper
    have nonneg : 0 ≤ lo p := sub_nonneg.mpr (hr p h).2
    refine ⟨by simpa only [lo, sub_mul, one_mul] using lower, ?_⟩
    calc
      _ ≤ lo p * (r p * ‖u‖ + ‖u‖) := mul_le_mul_of_nonneg_left upper nonneg
      _ = ‖u‖ - (r p)^2 * ‖u‖ := by dsimp only [lo]; ring
      _ ≤ ‖u‖ := sub_le_self _ (mul_nonneg (sq_nonneg _) (norm_nonneg _))
  have chain (l : List ℕ) (nd : l.Nodup) (pr : ∀ p ∈ l, Nat.Prime p) :
      (∏ p ∈ l.toFinset, lo p) * ‖v‖ ≤ ‖l.foldr op v‖ ∧
      (∏ p ∈ l.toFinset, lo p) * ‖l.foldr op v‖ ≤ ‖v‖ := by
    induction l with
    | nil => simp
    | cons p l ih =>
      obtain ⟨hnot, hn'⟩ := List.nodup_cons.mp nd
      have h2 := (pr p List.mem_cons_self).two_le
      have hpos : 0 ≤ lo p := sub_nonneg.mpr (hr p h2).2
      have rest (i : ℕ) (hi : i ∈ l) : Nat.Prime i := pr i (List.mem_cons_of_mem _ hi)
      have hprod : 0 ≤ ∏ i ∈ l.toFinset, lo i := Finset.prod_nonneg fun i hi =>
        sub_nonneg.mpr (hr i (rest i (List.mem_toFinset.mp hi)).two_le).2
      obtain ⟨ha, hb⟩ := ih hn' rest
      obtain ⟨hs, ht⟩ := step p h2 (l.foldr op v)
      simp only [List.toFinset_cons, Finset.prod_insert (by simpa using hnot : p ∉ l.toFinset),
        List.foldr_cons]
      constructor
      · rw [mul_assoc]
        exact (mul_le_mul_of_nonneg_left ha hpos).trans hs
      · calc
          _ = (∏ i ∈ l.toFinset, lo i) * (lo p * ‖op p (l.foldr op v)‖) := by ring
          _ ≤ _ := (mul_le_mul_of_nonneg_left ht hprod).trans hb
  have telescope (n : ℕ) :
      (∏ i ∈ Finset.Icc 2 (n+1), lo i) = ((n:ℝ)+2)/(2*((n:ℝ)+1)) := by
    induction n with
    | zero => norm_num [Finset.Icc_eq_empty_of_lt (by decide : 1 < 2)]
    | succ n ih =>
      rw [Finset.prod_Icc_succ_top (by omega : 2 ≤ (n+1)+1), ih]
      simp only [lo, r, Nat.cast_succ]
      have h1 : (n:ℝ)+1 ≠ 0 := by positivity
      have h2 : (n:ℝ)+1+1 ≠ 0 := by positivity
      field_simp [h1, h2]
      ring
  let N := primes.toFinset.sup id
  have hsub : primes.toFinset ⊆ Finset.Icc 2 (N+1) := by
    intro i hi
    exact Finset.mem_Icc.mpr ⟨(hp i (List.mem_toFinset.mp hi)).two_le,
      (Finset.le_sup (f := id) hi).trans (Nat.le_succ N)⟩
  have hh : 1 / 2 ≤ ∏ i ∈ primes.toFinset, lo i := calc
    _ ≤ ((N:ℝ)+2)/(2*((N:ℝ)+1)) := (le_div_iff₀ (by positivity)).2 (by linarith)
    _ = _ := (telescope N).symm
    _ ≤ _ := Finset.prod_le_prod_of_subset_of_le_one₀ hsub
      (fun i hi => sub_nonneg.mpr (hr i (Finset.mem_Icc.mp hi).1).2)
      (fun i hi _ => sub_le_self 1 (hr i (Finset.mem_Icc.mp hi).1).1)
  obtain ⟨h1, h2⟩ := chain primes hn hp
  have h1' := (mul_le_mul_of_nonneg_right hh (norm_nonneg v)).trans h1
  have h2' := (mul_le_mul_of_nonneg_right hh (norm_nonneg (primes.foldr op v))).trans h2
  change ‖v‖ / 2 ≤ ‖primes.foldr op v‖ ∧ ‖primes.foldr op v‖ ≤ 2 * ‖v‖
  constructor <;> linarith only [h1', h2']

/-- Clearing the denominator of the normalized shift forces p² in every
height coordinate. Every retained n-row minor incurs p^(2n), regardless of
the overlap between translated rows. -/
theorem nativeDyadic_normalizedHeightShift_clearing_minor (e q d p n : ℕ)
    [Fact q.Prime] [Fact d.Prime] (U : Matrix (AlpogeNativeDyadicH e) (Fin n) ℤ)
    (rows : Fin n → AlpogeNativeDyadicH e)
    (hc : ∀ t j, (p : ℤ)^2 ∣ U t j -
      (p : ℤ)^2 * U (t + (2 : ℕ) • ((alpogeNativeHostData e q d).frob p).2) j) :
    ((p : ℤ)^2)^n ∣ (U.submatrix rows id).det := by
  classical
  have hd (i j : Fin n) : (p : ℤ)^2 ∣ U (rows i) j := by
    obtain ⟨c, heq⟩ := hc (rows i) j
    refine ⟨c + U (rows i + (2 : ℕ) • ((alpogeNativeHostData e q d).frob p).2) j, ?_⟩
    linear_combination heq
  choose V hV using hd
  have hmat : U.submatrix rows id = (p:ℤ)^2 • Matrix.of V := by
    ext i j
    exact hV i j
  rw [hmat, Matrix.det_smul, Fintype.card_fin]
  exact dvd_mul_right _ _

/-- The square of the product of the admitted primes clears every complex
height column at once. Its logarithmic price per column is at most 2 Z log 4
for prime indices at most Z, independently of the number of host coordinates. -/
theorem nativeDyadic_normalizedHeightShift_chain_denominator (e q d Z : ℕ)
    [Fact q.Prime] [Fact d.Prime] (primes : List ℕ) (hn : primes.Nodup)
    (hp : ∀ p ∈ primes, p ∈ Nat.primesLE Z) (a : AlpogeNativeDyadicH e → ℤ) :
    let M := ∏ p ∈ primes.toFinset, p^2
    (∃ u : AlpogeNativeDyadicH e → ℤ, ∀ t,
      (M : ℂ) * (primes.foldr (nativeDyadicNormalizedHeightShift e q d)
        (WithLp.toLp 2 (fun s => (a s : ℂ))) t) = (u t : ℂ)) ∧
    Real.log (M : ℝ) ≤ 2 * Real.log 4 * Z := by
  classical
  let M (l : List ℕ) := ∏ p ∈ l.toFinset, p^2
  let v : EuclideanSpace ℂ (AlpogeNativeDyadicH e) := WithLp.toLp 2 (fun t => (a t : ℂ))
  let op := nativeDyadicNormalizedHeightShift e q d
  have clear (l : List ℕ) (nd : l.Nodup) (pr : ∀ p ∈ l, p ∈ Nat.primesLE Z) :
      ∃ u : AlpogeNativeDyadicH e → ℤ, ∀ t,
        (M l : ℂ) * (l.foldr op v t) = (u t : ℂ) := by
    induction l with
    | nil =>
      exact ⟨a, fun t => by simp [M, v]⟩
    | cons p l ih =>
      obtain ⟨hnp, ht⟩ := List.nodup_cons.mp nd
      obtain ⟨u, hu⟩ := ih ht (fun i hi => pr i (List.mem_cons_of_mem _ hi))
      have hnpr := (Nat.mem_primesLE.mp (pr p List.mem_cons_self)).2.ne_zero
      have p0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hnpr
      let sh := fun t => t + (2 : ℕ) • ((alpogeNativeHostData e q d).frob p).2
      refine ⟨fun t => u t - (p : ℤ)^2 * u (sh t), fun t => ?_⟩
      have hm : M (p :: l) = p^2 * M l := by simp [M, hnp]
      rw [hm, Nat.cast_mul, Nat.cast_pow, Int.cast_sub, Int.cast_mul, Int.cast_pow,
        Int.cast_natCast, ← hu t, ← hu (sh t)]
      change (p : ℂ)^2 * (M l : ℂ) *
        (((((p : ℝ)^2)⁻¹ : ℝ) : ℂ) * l.foldr op v t - l.foldr op v (sh t)) = _
      push_cast
      field_simp [p0]
  refine ⟨clear primes hn hp, ?_⟩
  change Real.log ((M primes : ℕ) : ℝ) ≤ _
  have hsub : primes.toFinset ⊆ Nat.primesLE Z := fun i hi => hp i (List.mem_toFinset.mp hi)
  have htheta : Chebyshev.theta (Z : ℝ) = ∑ p ∈ Nat.primesLE Z, Real.log (p : ℝ) := by
    rw [Chebyshev.theta, Nat.floor_natCast, Nat.primesLE_eq_filter_Ioc_zero]
  have hsum : ∑ i ∈ primes.toFinset, Real.log (i : ℝ) ≤ Real.log 4 * Z := calc
    _ ≤ ∑ i ∈ Nat.primesLE Z, Real.log (i : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg
      hsub (fun i hi _ => Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hi).2.one_le))
    _ = _ := htheta.symm
    _ ≤ _ := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg Z)
  dsimp only [M]
  rw [Nat.cast_prod, Real.log_prod]
  · simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat, ← Finset.mul_sum]
    linarith only [hsum]
  · intro i hi
    exact_mod_cast pow_ne_zero 2 (Nat.mem_primesLE.mp (hsub hi)).2.ne_zero

end AlpogeThin
end RHLean.Analysis

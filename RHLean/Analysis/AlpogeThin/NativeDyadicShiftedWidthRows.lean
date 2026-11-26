import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
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

/-- On the actual top/prime addresses of one binary Frobenius colour,
reverse increasing prime order in each fibre of the physical width site. The resulting
disjoint two-cycles each join distinct first primes. At most one address
per host site is left, with its actual logarithmic prime weight. -/
theorem nativeDyadic_firstPrime_sameWidth_matching (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (TT : Finset (AlpogeNativeDyadicH e)) (P : Finset ℕ) (c : AlpogeNativeE0)
    (hc : ∀ p ∈ P, ((alpogeNativeHostData e q d).frob p).1 = c)
    (x : ℝ) (hx : 1 ≤ x) (hP : ∀ p ∈ P, Nat.Prime p ∧ (p : ℝ) ≤ x) :
    let site := fun i : ↥TT × ↥P =>
      alpogeNativePartner i.1.val ((alpogeNativeHostData e q d).frob i.2.val)
    ∃ mate : Equiv.Perm (↥TT × ↥P), (∀ i, mate (mate i) = i) ∧
      (∀ i, site (mate i) = site i) ∧
      (∀ i, mate i ≠ i → (mate i).2 ≠ i.2) ∧
      (∀ i j, site i = site j → i.2.val ≤ j.2.val → (mate j).2.val ≤ (mate i).2.val) ∧
      ((Finset.univ.filter (fun i => mate i = i)).card ≤ Fintype.card (AlpogeNativeDyadicH e)) ∧
      (∑ i ∈ Finset.univ.filter (fun i => mate i = i), Real.log (i.2.val : ℝ)) ≤
        (Fintype.card (AlpogeNativeDyadicH e) : ℝ) * Real.log x := by
  classical
  let I := ↥TT × ↥P
  let g := (alpogeNativeHostData e q d).frob
  let site := fun i : I => alpogeNativePartner i.1.val (g i.2.val)
  let key := fun i : I => (site i).2
  let F := fun y : AlpogeNativeDyadicH e => {i : I // key i = y}
  have same (i j : I) (hk : key i = key j) (hp : i.2 = j.2) : i = j := by
    apply Prod.ext _ hp
    apply Subtype.ext
    change (alpogeNativeCconj _).2 + (g i.2.val).2 + i.1.val =
      (alpogeNativeCconj _).2 + (g j.2.val).2 + j.1.val at hk
    rw [hp] at hk
    have cancel {H : Type} [AddCommGroup H] (z u v : H) (h : z+u = z+v) : u = v :=
      add_left_cancel h
    exact cancel (H := AlpogeNativeDyadicH e) ((alpogeNativeCconj _).2 + (g j.2.val).2)
      i.1.val j.1.val hk
  let prime (y) (i : F y) := i.val.2.val
  have pinj (y) : Function.Injective (prime y) := fun i j hij => Subtype.ext
    (same i.val j.val (i.property.trans j.property.symm) (Subtype.ext hij))
  let (y : AlpogeNativeDyadicH e) : LinearOrder (F y) := LinearOrder.lift' (prime y) (pinj y)
  let ord (y : AlpogeNativeDyadicH e) := Fintype.orderIsoFinOfCardEq (F y) rfl
  let idx := fun y => (ord y).symm.toEquiv
  let flip := fun y (i : F y) => (idx y).symm ((idx y i).rev)
  have twice (y) (i : F y) : flip y (flip y i) = i := by simp [flip]
  have uniqueFixed (y) (i j : F y) (hi : flip y i = i) (hj : flip y j = j) : i = j := by
    have atFixed (v : F y) (hv : flip y v = v) : ((idx y v).rev).val = (idx y v).val := by
      exact congrArg Fin.val (by simpa only [flip, Equiv.apply_symm_apply] using congrArg (idx y) hv)
    have hi' := atFixed i hi
    have hj' := atFixed j hj
    rw [Fin.val_rev] at hi' hj'
    apply (idx y).injective
    apply Fin.ext
    have hiL := (idx y i).isLt
    have hjL := (idx y j).isLt
    omega
  let m := fun i : I => (flip (key i) ⟨i, rfl⟩).val
  have fibre (y) (i : F y) : m i.val = (flip y i).val := by
    obtain ⟨i, rfl⟩ := i
    rfl
  have invol : Function.Involutive m := fun i => calc
    m (m i) = (flip (key i) (flip (key i) ⟨i, rfl⟩)).val := fibre _ _
    _ = i := congrArg Subtype.val (twice _ _)
  let mate := Function.Involutive.toPerm m invol
  have hkey (i : I) : key (m i) = key i := (flip (key i) ⟨i, rfl⟩).property
  have hsite (i : I) : site (m i) = site i := by
    apply Prod.ext _ (hkey i)
    change (alpogeNativeCconj _).1 + (g (m i).2.val).1 + 0 =
      (alpogeNativeCconj _).1 + (g i.2.val).1 + 0
    rw [hc _ (m i).2.property, hc _ i.2.property]
  have hsep (i : I) (h : m i ≠ i) (hp : (m i).2 = i.2) : False :=
    h (same (m i) i (hkey i) hp)
  have reverse (y) (i j : F y) (h : i ≤ j) : flip y j ≤ flip y i := by
    change ord y ((ord y).symm j).rev ≤ ord y ((ord y).symm i).rev
    exact (ord y).monotone (Fin.rev_le_rev.mpr ((ord y).symm.monotone h))
  have horder (i j : I) (hs : site i = site j) (hp : i.2.val ≤ j.2.val) :
      (m j).2.val ≤ (m i).2.val := by
    let u : F (key i) := ⟨i, rfl⟩
    let v : F (key i) := ⟨j, congrArg Prod.snd hs.symm⟩
    have h := reverse (key i) u v hp
    change (flip (key i) v).val.2.val ≤ (flip (key i) u).val.2.val at h
    rw [show m j = (flip (key i) v).val from fibre _ v,
      show m i = (flip (key i) u).val from fibre _ u]
    exact h
  let Z := Finset.univ.filter (fun i : I => m i = i)
  have hinj : Set.InjOn key (↑Z : Set I) := by
    intro i hi j hj hij
    let u : F (key i) := ⟨i, rfl⟩
    let v : F (key i) := ⟨j, hij.symm⟩
    have hu : flip (key i) u = u := Subtype.ext ((fibre _ u).symm.trans (Finset.mem_filter.mp hi).2)
    have hv : flip (key i) v = v := Subtype.ext ((fibre _ v).symm.trans (Finset.mem_filter.mp hj).2)
    exact congrArg Subtype.val (uniqueFixed _ u v hu hv)
  have hcard : Z.card ≤ Fintype.card (AlpogeNativeDyadicH e) := by
    simpa using Finset.card_le_card_of_injOn (t := Finset.univ) key (fun _ _ => Finset.mem_univ _) hinj
  refine ⟨mate, invol, hsite, hsep, horder, hcard, ?_⟩
  change (∑ i ∈ Z, Real.log (i.2.val : ℝ)) ≤ _
  calc
    _ ≤ ∑ _i ∈ Z, Real.log x := Finset.sum_le_sum fun i _ =>
      Real.log_le_log (by exact_mod_cast (hP i.2.val i.2.property).1.pos) (hP i.2.val i.2.property).2
    _ = (Z.card : ℝ) * Real.log x := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Real.log_nonneg hx)

/-- Two different first primes at the same rounded thick width produce
a strictly ordered difference, on the actual rows, throughout the interior
of the high first-prime band. Its scaled size is the stated integral
linear expression when the top heights are integral. -/
theorem nativeDyadic_sameWidth_firstPrime_signed (e q d p r : ℕ) [Fact q.Prime] [Fact d.Prime]
    (t s : AlpogeNativeDyadicH e) (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (x b a c : ℝ) (hb : 0 < b) (hp : 0 < p) (hpr : p < r) (hr : (r:ℝ)+1 ≤ x)
    (ha : a ∈ Set.Icc (x*b) ((x+1)*b)) (hc : c ∈ Set.Icc (x*b) ((x+1)*b))
    (hs : alpogeNativePartner t ((alpogeNativeHostData e q d).frob p) =
      alpogeNativePartner s ((alpogeNativeHostData e q d).frob r))
    (hw : w (alpogeNativePartner s ((alpogeNativeHostData e q d).frob r)) ≤ b*(1+1/x)) :
    let v := nativeDyadicLocalSourceAtom e q d p a t w 1 - nativeDyadicLocalSourceAtom e q d r c s w 1
    (p:ℝ)*r*v = (r:ℝ)*a - (p:ℝ)*c ∧
      b*(x*((r:ℝ)-p)-p) ≤ (p:ℝ)*r*v ∧ 0 < v := by
  have hp' : 0 < (p:ℝ) := by exact_mod_cast hp
  have hgap : (p:ℝ)+1 ≤ r := by exact_mod_cast Nat.succ_le_of_lt hpr
  have hr' : 0 < (r:ℝ) := by linarith
  have hx : 0 < x := by linarith
  let W := w (alpogeNativePartner s ((alpogeNativeHostData e q d).frob r))
  have hcap : W * r ≤ x*b := calc
    _ ≤ (b*(1+1/x)) * r := mul_le_mul_of_nonneg_right hw hr'.le
    _ ≤ (b*(1+1/x)) * (x-1) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = x*b - b/x := by field [hx.ne']
    _ ≤ x*b := sub_le_self _ (div_nonneg hb.le hx.le)
  have hcapP : W * p ≤ x*b := calc
    _ ≤ (b*(1+1/x)) * p := mul_le_mul_of_nonneg_right hw hp'.le
    _ ≤ (b*(1+1/x)) * (x-1) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = x*b - b/x := by field [hx.ne']
    _ ≤ x*b := sub_le_self _ (div_nonneg hb.le hx.le)
  have hwa := (le_div_iff₀ hp').2 (hcapP.trans ha.1)
  have hwc := (le_div_iff₀ hr').2 (hcap.trans hc.1)
  dsimp only [W] at hwa hwc
  dsimp only
  simp only [nativeDyadicLocalSourceAtom, alpogeNativeSiteCut, Complex.ofReal_re, pow_one,
    one_nsmul, hs, max_eq_left (sub_nonneg.mpr hwa), max_eq_left (sub_nonneg.mpr hwc),
    sub_sub_sub_cancel_right]
  have heq : (p:ℝ)*r*(a/p-c/r) = (r:ℝ)*a - (p:ℝ)*c := by field [hp'.ne', hr'.ne']
  rw [heq]
  have low : b*(x*((r:ℝ)-p)-p) ≤ (r:ℝ)*a - (p:ℝ)*c := by
    linarith only [mul_le_mul_of_nonneg_left ha.1 hr'.le, mul_le_mul_of_nonneg_left hc.2 hp'.le]
  have hpos : 0 < b*(x*((r:ℝ)-p)-p) := by
    apply mul_pos hb
    nlinarith only [mul_nonneg hx.le (by linarith only [hgap] : 0 ≤ (r:ℝ)-p-1), hr, hgap]
  have hv : 0 < (p:ℝ)*r*(a/p-c/r) := by rw [heq]; exact hpos.trans_le low
  exact ⟨rfl, low, pos_of_mul_pos_right hv (mul_nonneg hp'.le hr'.le)⟩

/-- With the actual logarithmic weights, the smaller of two odd first
primes earns a positive signed margin on a common active thick width. -/
theorem nativeDyadic_sameWidth_firstPrime_weighted_gain (e q d p r : ℕ) [Fact q.Prime] [Fact d.Prime]
    (t s : AlpogeNativeDyadicH e) (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (x b a c : ℝ) (hb : 0 < b) (hp : 0 < p) (hgap : p+2 ≤ r) (hr : (r:ℝ)+1 ≤ x)
    (hlog : 3 ≤ Real.log (p:ℝ)) (ha : a ∈ Set.Icc (x*b) ((x+1)*b))
    (hc : c ∈ Set.Icc (x*b) ((x+1)*b))
    (hs : alpogeNativePartner t ((alpogeNativeHostData e q d).frob p) =
      alpogeNativePartner s ((alpogeNativeHostData e q d).frob r))
    (hw : w (alpogeNativePartner s ((alpogeNativeHostData e q d).frob r)) ∈
      Set.Icc 0 (b*(1+1/x))) :
    let margin := b*((x*((r:ℝ)-p)-p)*Real.log p-(x+1)*((r:ℝ)-p))
    b*(x-2) ≤ margin ∧ margin ≤ (p:ℝ)*r*
      (Real.log p * nativeDyadicLocalSourceAtom e q d p a t w 1 -
        Real.log r * nativeDyadicLocalSourceAtom e q d r c s w 1) := by
  let U := nativeDyadicLocalSourceAtom e q d p a t w 1
  let V := nativeDyadicLocalSourceAtom e q d r c s w 1
  have h := (nativeDyadic_sameWidth_firstPrime_signed e q d p r t s w x b a c hb hp
    (by omega) hr ha hc hs hw.2).2.1
  change b*(x*((r:ℝ)-p)-p) ≤ (p:ℝ)*r*(U-V) at h
  have hp0 : 0 < (p:ℝ) := by exact_mod_cast hp
  have hgap' : (p:ℝ)+2 ≤ r := by exact_mod_cast hgap
  have hr0 : 0 < (r:ℝ) := by linarith
  have hx : 1 ≤ x := by linarith
  have hc0 : 0 ≤ c := (mul_nonneg (by linarith) hb.le).trans hc.1
  have hV0 : 0 ≤ V := le_max_right _ _
  have hV : V ≤ ((x+1)*b)/r := calc
    _ ≤ c/(r:ℝ) := by
      change max (c / ((r^1 : ℕ) : ℝ) - w (alpogeNativePartner s
        ((1 : ℕ) • (alpogeNativeHostData e q d).frob r))) 0 ≤ _
      simpa only [pow_one, one_nsmul] using max_le (sub_le_self _ hw.1)
        (div_nonneg hc0 hr0.le)
    _ ≤ _ := div_le_div_of_nonneg_right hc.2 hr0.le
  have hratio : Real.log (r:ℝ) - Real.log (p:ℝ) ≤ ((r:ℝ)-p)/p := calc
    _ = Real.log ((r:ℝ)/p) := (Real.log_div hr0.ne' hp0.ne').symm
    _ ≤ (r:ℝ)/p-1 := Real.log_le_sub_one_of_pos (div_pos hr0 hp0)
    _ = _ := by field [hp0.ne']
  have hpen : (p:ℝ)*r*((Real.log r-Real.log p)*V) ≤ b*(x+1)*((r:ℝ)-p) := calc
    _ ≤ (p:ℝ)*r*((((r:ℝ)-p)/p)*(((x+1)*b)/r)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hratio hV hV0 (div_nonneg (by linarith) hp0.le))
        (mul_nonneg hp0.le hr0.le)
    _ = _ := by field [hp0.ne', hr0.ne']
  have hg0 : 0 ≤ x*((r:ℝ)-p)-(p:ℝ) := by
    nlinarith only [mul_nonneg (by linarith : 0 ≤ x) (by linarith only [hgap'] : 0 ≤ (r:ℝ)-p-1),
      hr, hgap']
  have hbase : x-2 ≤ (x*((r:ℝ)-p)-p)*Real.log p-(x+1)*((r:ℝ)-p) := by
    linarith only [mul_le_mul_of_nonneg_right hlog hg0, hr, hgap',
      mul_le_mul_of_nonneg_left (by linarith only [hgap'] : 2 ≤ (r:ℝ)-p)
        (by linarith only [hx] : 0 ≤ 2*x-1)]
  refine ⟨mul_le_mul_of_nonneg_left hbase hb.le, ?_⟩
  change b*((x*((r:ℝ)-p)-p)*Real.log p-(x+1)*((r:ℝ)-p)) ≤ (p:ℝ)*r*(Real.log p*U-Real.log r*V)
  linarith only [hpen,
    mul_le_mul_of_nonneg_left h (by linarith only [hlog] : 0 ≤ Real.log (p:ℝ))]

private theorem native_firstPrime_divides_read_iff {p r : ℕ} (hp : Nat.Prime p) (hr : Nat.Prime r)
    (hne : p ≠ r) (a c : ℤ) : (p:ℤ) ∣ (r:ℤ)*a - (p:ℤ)*c ↔ (p:ℤ) ∣ a := by
  have hpr : ¬ (p:ℤ) ∣ (r:ℤ) := fun h =>
    hne ((Nat.prime_dvd_prime_iff_eq hp hr).mp (Int.natCast_dvd_natCast.mp h))
  rw [dvd_sub_left (dvd_mul_right _ _), (Nat.prime_iff_prime_int.mp hp).dvd_mul, or_iff_right hpr]

/-- For one fixed integral height profile, the paired first-prime read is
a unit at every p-power depth unless p divides this top height. All such
exceptional primes together have logarithmic weight at most log(a_t).
The matching may supply a different second prime and top at every address. -/
theorem nativeDyadic_firstPrime_paired_unit_price (e : ℕ) (t : AlpogeNativeDyadicH e)
    (a : AlpogeNativeDyadicH e → ℕ) (ht : 0 < a t) (P : Finset ℕ)
    (r : ℕ → ℕ) (s : ℕ → AlpogeNativeDyadicH e)
    (hp : ∀ p ∈ P, Nat.Prime p ∧ Nat.Prime (r p) ∧ p ≠ r p) :
    let D := fun p : ℕ => (r p : ℤ) * a t - (p : ℤ) * a (s p)
    (∑ p ∈ P.filter (fun p : ℕ => (p : ℤ) ∣ D p), Real.log (p : ℝ)) ≤ Real.log (a t : ℝ) ∧
    ∀ p ∈ P, ¬ p ∣ a t → ∀ k : ℕ, IsUnit (D p : ZMod (p^k)) := by
  classical
  let D := fun p : ℕ => (r p : ℤ) * a t - (p : ℤ) * a (s p)
  have hd (p : ℕ) (h : p ∈ P) : (p : ℤ) ∣ D p ↔ p ∣ a t := by
    exact (native_firstPrime_divides_read_iff (hp p h).1 (hp p h).2.1 (hp p h).2.2 _ _).trans
      Int.natCast_dvd_natCast
  let S : Finset ℕ := P.filter (fun p : ℕ => (p : ℤ) ∣ D p)
  have hsub : S ⊆ (a t).primeFactors := by
    intro p h
    obtain ⟨hP, hv⟩ := Finset.mem_filter.mp h
    exact Nat.mem_primeFactors.mpr ⟨(hp p hP).1, (hd p hP).mp hv, ht.ne'⟩
  refine ⟨?_, ?_⟩
  · change (∑ p ∈ S, Real.log (p : ℝ)) ≤ _
    calc
      _ ≤ ∑ p ∈ (a t).primeFactors, Real.log (p : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun p h _ => Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors h).one_le))
      _ = Real.log ((∏ p ∈ (a t).primeFactors, p : ℕ) : ℝ) := by
        rw [Nat.cast_prod, Real.log_prod (fun p h => Nat.cast_ne_zero.mpr (Nat.pos_of_mem_primeFactors h).ne')]
      _ ≤ Real.log ((a t : ℕ) : ℝ) := by
        have hpos : 0 < (∏ p ∈ (a t).primeFactors, p : ℕ) :=
          Finset.prod_pos fun p h => Nat.pos_of_mem_primeFactors h
        apply Real.log_le_log (by exact_mod_cast hpos)
        exact_mod_cast Nat.le_of_dvd ht (Nat.prod_primeFactors_dvd (a t))
  · intro p h hnd k
    let : Fact p.Prime := ⟨(hp p h).1⟩
    have hne : (D p : ZMod p) ≠ 0 :=
      fun hz => hnd ((hd p h).mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz))
    have hco := (ZMod.coe_int_isUnit_iff_isCoprime (D p) p).mp (isUnit_iff_ne_zero.mpr hne)
    apply (ZMod.coe_int_isUnit_iff_isCoprime (D p) (p^k)).mpr
    simpa only [Nat.cast_pow] using hco.pow_left (m := k)

/-- On the actual top coordinates the simultaneous vanishing lattice for
the disjoint first-prime pair reads has exact index ∏_t ∏_{p served at t} p.
The diagonal integral frame attains this value. -/
theorem nativeDyadic_firstPrime_matching_kernel_det (e : ℕ) (TT : Finset (AlpogeNativeDyadicH e))
    (P : ↥TT → Finset ℕ) (r : ↥TT → ℕ → ℕ) (s : ↥TT → ℕ → ↥TT)
    (hp : ∀ t p, p ∈ P t → Nat.Prime p ∧ Nat.Prime (r t p) ∧ p ≠ r t p) :
    let M := fun t => ∏ p ∈ P t, (p : ℤ)
    let clears := fun U : Matrix (↥TT) (↥TT) ℤ => ∀ t p, p ∈ P t → ∀ j,
      (p : ℤ) ∣ (r t p : ℤ)*U t j - (p : ℤ)*U (s t p) j
    (∀ U, clears U → (∏ t, M t) ∣ U.det) ∧
    ∃ U, clears U ∧ U.det = ∏ t, M t := by
  classical
  let M (t : ↥TT) := ∏ p ∈ P t, (p : ℤ)
  let clears := fun U : Matrix (↥TT) (↥TT) ℤ => ∀ t p, p ∈ P t → ∀ j,
    (p : ℤ) ∣ (r t p : ℤ)*U t j - (p : ℤ)*U (s t p) j
  have rows (U : Matrix (↥TT) (↥TT) ℤ) : clears U ↔ ∀ t j, M t ∣ U t j := by
    constructor
    · intro h t j
      apply Finset.prod_dvd_of_coprime
      · intro p h1 l h2 hne
        exact ((Nat.coprime_primes (hp t p h1).1 (hp t l h2).1).2 hne).isCoprime
      · intro p h1
        exact (native_firstPrime_divides_read_iff (hp t p h1).1 (hp t p h1).2.1
          (hp t p h1).2.2 _ _).mp (h t p h1 j)
    · intro h t p h1 j
      apply (native_firstPrime_divides_read_iff (hp t p h1).1 (hp t p h1).2.1
        (hp t p h1).2.2 _ _).mpr
      exact (Finset.dvd_prod_of_mem (fun i : ℕ => (i : ℤ)) h1).trans (h t j)
  constructor
  · intro U h
    choose V hv using (rows U).mp h
    have heq : U = Matrix.diagonal M * Matrix.of V := by
      ext i j
      rw [Matrix.diagonal_mul]
      exact hv i j
    rw [heq, Matrix.det_mul, Matrix.det_diagonal]
    exact dvd_mul_right _ _
  · refine ⟨Matrix.diagonal M, (rows _).mpr ?_, Matrix.det_diagonal⟩
    intro i j
    by_cases h : i = j
    · subst j
      simp
    · simp [h]

/-- Every vector of target residues for the actual two-top first-prime
differences is simultaneously attained at any depth. The other top may
repeat arbitrarily often. At a served row coprimality follows from the
two distinct paired primes. -/
theorem nativeDyadic_firstPrime_depth_surjective (e p k : ℕ) (TT : Finset (AlpogeNativeDyadicH e))
    (r : ↥TT → ℕ) (s : ↥TT → ↥TT) (hr : ∀ t, (r t).Coprime p) :
    Function.Surjective (fun u : ↥TT → ZMod (p^k) => fun t =>
      (r t : ZMod (p^k))*u t - (p : ZMod (p^k))*u (s t)) := by
  intro y
  let R := ZMod (p^k)
  let c : ↥TT → R := fun t => (r t : ZMod (p^k))
  let z : R := (p : ZMod (p^k))
  have unit (t) : IsUnit (c t) := (ZMod.isUnit_iff_coprime _ _).mpr ((hr t).pow_right k)
  have inv (t) : c t * (c t)⁻¹ = 1 := ZMod.mul_inv_of_unit _ (unit t)
  let F : ℕ → ↥TT → R := Nat.rec (fun _ => 0)
    (fun _ v t => (c t)⁻¹ * (y t + z*v (s t)))
  have residual (n : ℕ) : ∀ t, ∃ w : R,
      c t * F n t - z * F n (s t) - y t = z^n * w := by
    induction n with
    | zero => intro t; exact ⟨-y t, by simp [F]⟩
    | succ n ih =>
      intro t
      obtain ⟨w, hw⟩ := ih (s t)
      refine ⟨(c (s t))⁻¹*w, ?_⟩
      change c t * ((c t)⁻¹*(y t + z * F n (s t))) -
        z*((c (s t))⁻¹*(y (s t)+z*F n (s (s t)))) - y t = _
      rw [← mul_assoc (c t), inv, one_mul]
      calc
        _ = z*((c (s t))⁻¹*(c (s t)*F n (s t)-z*F n (s (s t))-y (s t))) := by
          linear_combination -(z*F n (s t)) * inv (s t)
        _ = _ := by rw [hw, pow_succ]; ring
  have hz : z^k = 0 := by change (p : ZMod (p^k))^k = 0; rw [← Nat.cast_pow, ZMod.natCast_self]
  refine ⟨F k, funext fun t => ?_⟩
  obtain ⟨w, hw⟩ := residual k t
  rw [hz, zero_mul] at hw
  exact sub_eq_zero.mp hw

/-- Reduction of the integral height variations at the two top coordinates
read by each measured first-prime pair, at its prescribed depth. -/
noncomputable def nativeDyadicMatchedReadReduction (e : ℕ) (TT : Finset (AlpogeNativeDyadicH e))
    (P : Finset ℕ) (k r : ↥P → ↥TT → ℕ) (s : ↥P → ↥TT → ↥TT) :
    (↥TT → ℤ) →+ ((p : ↥P) → (t : ↥TT) → ZMod (p.val ^ k p t)) where
  toFun a p t := (r p t : ZMod (p.val ^ k p t)) * (a t : ZMod (p.val ^ k p t)) -
    (p.val : ZMod (p.val ^ k p t)) * (a (s p t) : ZMod (p.val ^ k p t))
  map_zero' := by funext p t; simp
  map_add' a b := by funext p t; simp only [Pi.add_apply, Int.cast_add]; ring

/-- At unequal measured depths, repeated secondary tops cost no extra
multiplicity. The quotient of the single integral height lattice has exactly
the product of the measured prime powers as its cardinality. -/
theorem nativeDyadic_matchedRead_joint_index (e : ℕ) (TT : Finset (AlpogeNativeDyadicH e))
    (P : Finset ℕ) (k r : ↥P → ↥TT → ℕ) (s : ↥P → ↥TT → ↥TT)
    (hp : ∀ p ∈ P, Nat.Prime p) (hr : ∀ p t, (r p t).Coprime p.val) :
    (nativeDyadicMatchedReadReduction e TT P k r s).ker.index =
      ∏ p : ↥P, ∏ t : ↥TT, p.val ^ k p t := by
  classical
  let F := nativeDyadicMatchedReadReduction e TT P k r s
  let K (p : ↥P) := Finset.univ.sup (k p)
  let M (p : ↥P) := p.val ^ K p
  have hM (p : ↥P) : M p ≠ 0 := pow_ne_zero _ (hp p p.property).ne_zero
  let (p : ↥P) : NeZero (M p) := ⟨hM p⟩
  let (p : ↥P) (t : ↥TT) : NeZero (p.val ^ k p t) := ⟨pow_ne_zero _ (hp p p.property).ne_zero⟩
  have hc : (↑(Finset.univ : Finset (↥P)) : Set (↥P)).Pairwise (fun p l => (M p).Coprime (M l)) := by
    intro p _ l _ h
    exact (((Nat.coprime_primes (hp p p.property) (hp l l.property)).2
      (fun hpl => h (Subtype.ext hpl))).pow_left _).pow_right _
  have hdiv (p : ↥P) (t : ↥TT) : p.val ^ k p t ∣ M p :=
    pow_dvd_pow _ (Finset.le_sup (s := Finset.univ) (f := k p) (Finset.mem_univ t))
  let red (p : ↥P) (t : ↥TT) := ZMod.castHom (hdiv p t) (ZMod (p.val ^ k p t))
  have onto : Function.Surjective F := by
    intro y
    have lifts (p : ↥P) (t : ↥TT) : ∃ b : ZMod (M p), red p t b = y p t :=
      ZMod.castHom_surjective (hdiv p t) (y p t)
    choose b hb using lifts
    have inverse (p : ↥P) : ∃ u : ↥TT → ZMod (M p), ∀ t,
        (r p t : ZMod (M p))*u t - (p.val : ZMod (M p))*u (s p t) = b p t := by
      obtain ⟨u, h⟩ := nativeDyadic_firstPrime_depth_surjective e p (K p) TT (r p) (s p) (hr p) (b p)
      exact ⟨u, congrFun h⟩
    choose u hu using inverse
    let a (t : ↥TT) := Nat.chineseRemainderOfFinset (fun p : ↥P => (u p t).val) M
      Finset.univ (fun p _ => hM p) hc
    have ha (p : ↥P) (t : ↥TT) : ((a t).val : ZMod (M p)) = u p t := by
      have h := (ZMod.natCast_eq_natCast_iff _ _ _).2 ((a t).property p (Finset.mem_univ p))
      simpa only [ZMod.natCast_zmod_val] using h
    refine ⟨fun t => ((a t).val : ℤ), funext fun p => funext fun t => ?_⟩
    have hred (v : ↥TT) : red p t (u p v) = ((a v).val : ZMod (p.val ^ k p t)) := by
      rw [← ha p v]
      exact map_natCast (red p t) _
    have h := congrArg (red p t) (hu p t)
    rw [map_sub, map_mul, map_mul, map_natCast, map_natCast, hred, hred, hb] at h
    change (r p t : ZMod (p.val ^ k p t)) * (((a t).val : ℤ) : ZMod (p.val ^ k p t)) -
      (p.val : ZMod (p.val ^ k p t)) * (((a (s p t)).val : ℤ) : ZMod (p.val ^ k p t)) = y p t
    simpa only [Int.cast_natCast] using h
  change F.ker.index = _
  rw [AddSubgroup.index_ker, F.range_eq_top_of_surjective onto, AddSubgroup.card_top]
  simp only [Nat.card_eq_fintype_card, Fintype.card_pi, ZMod.card]

/-- On one original measured row, twice the log index of its matched height
readings recovers twice the high first-prime ASK up to one log(p) per served
address (before the common factor two). The error retains the thick mask. -/
theorem nativeDyadic_firstPrime_measured_logIndex_price (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (TT : Finset (AlpogeNativeDyadicH e)) (P : Finset ℕ) (served : ↥P → Finset (↥TT))
    (r : ↥P → ↥TT → ℕ) (s : ↥P → ↥TT → ↥TT) (hp : ∀ p ∈ P, Nat.Prime p)
    (hr : ∀ p t, (r p t).Coprime p.val) (a : AlpogeNativeDyadicH e → ℝ)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ) :
    let U := fun (p : ↥P) (t : ↥TT) => if t ∈ served p then
      nativeDyadicLocalSourceAtom e q d p.val (a t.val) t.val w 1 else 0
    let k := fun p t => ⌊U p t⌋₊
    let lattice := (nativeDyadicMatchedReadReduction e TT P k r s).ker
    let excess := (∑ p : ↥P, ∑ t : ↥TT, U p t * Real.log (p.val : ℝ)) - Real.log (lattice.index : ℝ)
    0 ≤ excess ∧ excess ≤ ∑ p : ↥P, ∑ t : ↥TT, if t ∈ served p then Real.log (p.val : ℝ) else 0 := by
  classical
  let U := fun (p : ↥P) (t : ↥TT) => if t ∈ served p then
    nativeDyadicLocalSourceAtom e q d p.val (a t.val) t.val w 1 else 0
  let k := fun p t => ⌊U p t⌋₊
  let L := (nativeDyadicMatchedReadReduction e TT P k r s).ker
  have hu (p t) : 0 ≤ U p t := by
    dsimp only [U]
    split_ifs
    · exact le_max_right _ _
    · exact le_rfl
  have hlog (p : ↥P) : 0 ≤ Real.log (p.val : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (hp p p.property).one_le)
  have hn (p : ↥P) : (p.val : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hp p p.property).ne_zero
  have logIndex : Real.log (L.index : ℝ) = ∑ p : ↥P, ∑ t : ↥TT, (k p t : ℝ)*Real.log (p.val : ℝ) := by
    rw [show L.index = _ from nativeDyadic_matchedRead_joint_index e TT P k r s hp hr]
    simp only [Nat.cast_prod, Nat.cast_pow]
    rw [Real.log_prod (fun p _ => Finset.prod_ne_zero_iff.mpr (fun t _ => pow_ne_zero (k p t) (hn p)))]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Real.log_prod (fun t _ => pow_ne_zero (k p t) (hn p))]
    simp only [Real.log_pow]
  let E := fun (p : ↥P) (t : ↥TT) => (U p t - (k p t : ℝ)) * Real.log (p.val : ℝ)
  have hnneg (p t) : 0 ≤ E p t := mul_nonneg (sub_nonneg.mpr (Nat.floor_le (hu p t))) (hlog p)
  have hpoint (p t) : E p t ≤ if t ∈ served p then Real.log (p.val : ℝ) else 0 := by
    split_ifs with h
    · exact mul_le_of_le_one_left (hlog p) (by
        have hf := Nat.lt_floor_add_one (U p t)
        change U p t - (⌊U p t⌋₊ : ℝ) ≤ 1
        linarith)
    · simp [E, k, U, h]
  change 0 ≤ (∑ p : ↥P, ∑ t : ↥TT, U p t*Real.log (p.val : ℝ)) - Real.log (L.index : ℝ) ∧ _
  rw [logIndex]
  have split : (∑ p : ↥P, ∑ t : ↥TT, U p t*Real.log (p.val : ℝ)) -
      (∑ p : ↥P, ∑ t : ↥TT, (k p t : ℝ)*Real.log (p.val : ℝ)) =
      ∑ p : ↥P, ∑ t : ↥TT, E p t := by simp only [E, sub_mul, Finset.sum_sub_distrib]
  rw [split]
  exact ⟨Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun t _ => hnneg p t)),
    Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun t _ => hpoint p t))⟩

/-- A single explicit integer factorial supplies a first-prime valuation
depth for every measured top. The three losses are the higher powers in
Legendre's formula, the change of height, and the change of thick width. -/
theorem nativeDyadic_firstPrime_factorial_depth (e q d p A : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hp : Nat.Prime p) (t : AlpogeNativeDyadicH e) (a b : ℝ) (hb : 0 ≤ b)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ) :
    let v := w (alpogeNativePartner t ((alpogeNativeHostData e q d).frob p))
    let k := padicValNat p A.factorial - ⌊b⌋₊
    |(k : ℝ) - nativeDyadicLocalSourceAtom e q d p a t w 1| ≤
      (A : ℝ)/((p:ℝ)*((p:ℝ)-1)) + |(A:ℝ)-a|/p + |v-b| + 2 := by
  let : Fact p.Prime := ⟨hp⟩
  let V := padicValNat p A.factorial
  let B := ⌊b⌋₊
  let v := w (alpogeNativePartner t ((alpogeNativeHostData e q d).frob p))
  have hp0 : 0 < (p:ℝ) := by exact_mod_cast hp.pos
  have hp1 : 1 < (p:ℝ) := by exact_mod_cast hp.one_lt
  have upperN : (p-1)*V ≤ A := by
    change (p-1)*padicValNat p A.factorial ≤ A
    rw [sub_one_mul_padicValNat_factorial]
    exact Nat.sub_le _ _
  have hu : (V:ℝ) ≤ (A:ℝ)/((p:ℝ)-1) := by
    apply (le_div_iff₀ (sub_pos.mpr hp1)).2
    have z : ((((p-1)*V : ℕ)) : ℝ) ≤ (A:ℝ) := by exact_mod_cast upperN
    rw [Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one, mul_comm] at z
    exact z
  have htail : (A:ℝ)/((p:ℝ)-1) = (A:ℝ)/p + (A:ℝ)/((p:ℝ)*((p:ℝ)-1)) := by
    field [hp0.ne', (sub_pos.mpr hp1).ne']
  have hdiv : A / p ≤ V := by
    have hv := (padicValNat_mul_div_factorial (p := p) A).symm.trans (padicValNat_factorial_mul (A / p))
    change A/p ≤ padicValNat p A.factorial
    rw [hv]
    omega
  have hF : (A:ℝ)/p - 1 ≤ V := by
    have h : A < (A/p+1)*p := (Nat.div_lt_iff_lt_mul hp.pos).mp (Nat.lt_succ_self _)
    have hr : (A:ℝ) < (((A/p:ℕ):ℝ)+1)*p := by exact_mod_cast h
    have hV : ((A/p:ℕ):ℝ) ≤ (V:ℝ) := by exact_mod_cast hdiv
    linarith only [(div_lt_iff₀ hp0).2 hr, hV]
  have hfloor : (B:ℝ) ≤ b := Nat.floor_le hb
  have hfloor' : b < (B:ℝ)+1 := Nat.lt_floor_add_one b
  have hcut : ((V-B : ℕ):ℝ) = max ((V:ℝ)-B) 0 := by
    by_cases h : B ≤ V
    · rw [Nat.cast_sub h, max_eq_left (sub_nonneg.mpr (by exact_mod_cast h))]
    · have h' : V ≤ B := by omega
      rw [Nat.sub_eq_zero_of_le h', Nat.cast_zero, max_eq_right (sub_nonpos.mpr (by exact_mod_cast h'))]
  dsimp only
  simp only [nativeDyadicLocalSourceAtom, alpogeNativeSiteCut, Complex.ofReal_re, one_nsmul, pow_one]
  change |((V-B : ℕ):ℝ) - max (a/p-v) 0| ≤ _
  rw [hcut]
  apply (abs_max_sub_max_le_abs _ _ _).trans
  have hmove : |(A:ℝ)/p - a/p| ≤ |(A:ℝ)-a|/p := by
    rw [← sub_div, abs_div, abs_of_pos hp0]
  have hn : 0 ≤ (A:ℝ)/((p:ℝ)*((p:ℝ)-1)) := by positivity
  have hab := abs_le.mp hmove
  have hw := abs_le.mp (le_rfl : |v-b| ≤ |v-b|)
  change |((V:ℝ)-B) - (a/p-v)| ≤ (A:ℝ)/((p:ℝ)*((p:ℝ)-1)) + |(A:ℝ)-a|/p + |v-b|+2
  apply abs_le.mpr
  constructor <;> linarith only [hF, hu, htail, hfloor, hfloor', hn, hab.1, hab.2, hw.1, hw.2]

/-- In the original prime wheel, admitting a prime counts each of its
downstream multiples once. After clearing the first c multiples at each
prime, the entire remaining payment is one integer product on the wheel. -/
theorem nativeDyadic_firstPrime_wheel_product (P : Finset ℕ) (N c : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hc : ∀ p ∈ P, c ≤ N/p) :
    (∏ n ∈ Finset.range N, Nat.gcd (n+1) (∏ p ∈ P, p)) =
      (∏ p ∈ P, p)^c * ∏ p ∈ P, p^(N/p-c) := by
  classical
  have factor (n : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
      Nat.gcd n (∏ p ∈ S, p) = ∏ p ∈ S, if p ∣ n then p else 1 := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert p S hps ih =>
      have hs := fun r (hr : r ∈ S) => hS r (Finset.mem_insert_of_mem hr)
      have hp := hS p (Finset.mem_insert_self p S)
      have cop : p.Coprime (∏ r ∈ S, r) := Nat.coprime_prod_right_iff.mpr fun r hr =>
        (Nat.coprime_primes hp (hs r hr)).2 (fun h => hps (by simpa only [h] using hr))
      simp only [Finset.prod_insert hps, Nat.Coprime.gcd_mul n cop, ih hs]
      by_cases hd : p ∣ n
      · rw [ite_eq_left hd, Nat.gcd_eq_right hd]
      · rw [ite_eq_right hd, (hp.coprime_iff_not_dvd.mpr hd).symm.gcd_eq_one]
  calc
    _ = ∏ n ∈ Finset.range N, ∏ p ∈ P, if p ∣ n+1 then p else 1 :=
      Finset.prod_congr rfl (fun n _ => factor (n+1) P hP)
    _ = ∏ p ∈ P, ∏ n ∈ Finset.range N, if p ∣ n+1 then p else 1 := Finset.prod_comm
    _ = ∏ p ∈ P, p^(N/p) := by
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [← Finset.prod_filter, Finset.prod_const, Nat.card_multiples]
    _ = _ := by
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [← pow_add]
      have he : c + (N/p-c) = N/p := by have := hc p hp; omega
      rw [he]

/-- A wheel through floor(c*x) prices the original normalized thick read.
The scale c is free and is independent of the measured height scale b. -/
theorem nativeDyadic_firstPrime_wheel_depth (e q d p c : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hp : Nat.Prime p) (hc : 0 < c) (t : AlpogeNativeDyadicH e)
    (a b x : ℝ) (hb : 0 < b) (hpx : (p:ℝ) ≤ x) (ha : x ≤ a/b ∧ a/b ≤ x+1)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ) :
    let v := w (alpogeNativePartner t ((alpogeNativeHostData e q d).frob p))
    let k := ⌊(c:ℝ)*x⌋₊ / p - c
    |nativeDyadicLocalSourceAtom e q d p a t w 1 / b - (k:ℝ)/c| ≤
      1/(p:ℝ) + |v/b-1| + 1/(c:ℝ) := by
  let K := ⌊(c:ℝ)*x⌋₊ / p
  let v := w (alpogeNativePartner t ((alpogeNativeHostData e q d).frob p))
  have pc : 0 < (p:ℝ) := by exact_mod_cast hp.pos
  have cc : 0 < (c:ℝ) := by exact_mod_cast hc
  have hx : 0 ≤ x := pc.le.trans hpx
  have xp : 1 ≤ x/p := (one_le_div pc).2 hpx
  have hK : K = ⌊(c:ℝ)*x/p⌋₊ := (Nat.floor_div_natCast _ _).symm
  have hmin : c ≤ K := by
    rw [hK]
    apply Nat.le_floor
    rw [mul_div_assoc]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left xp cc.le
  have lo : (K:ℝ)/c ≤ x/p := by
    apply (div_le_iff₀ cc).2
    rw [hK, mul_comm (x/(p:ℝ)) (c:ℝ), ← mul_div_assoc]
    exact Nat.floor_le (by positivity)
  have hi : x/p ≤ (K:ℝ)/c + 1/c := by
    rw [← add_div, le_div_iff₀ cc, mul_comm (x/(p:ℝ)) (c:ℝ), ← mul_div_assoc, hK]
    exact (Nat.lt_floor_add_one _).le
  have base : 0 ≤ (K:ℝ)/c-1 :=
    sub_nonneg.mpr ((one_le_div cc).2 (by exact_mod_cast hmin))
  have hlo := div_le_div_of_nonneg_right ha.1 pc.le
  have hhi := div_le_div_of_nonneg_right ha.2 pc.le
  rw [add_div] at hhi
  have hw := abs_le.mp (le_rfl : |v/b-1| ≤ |v/b-1|)
  dsimp only
  simp only [nativeDyadicLocalSourceAtom, alpogeNativeSiteCut, Complex.ofReal_re, one_nsmul, pow_one]
  change |max (a/p-v) 0 / b - ((K-c:ℕ):ℝ)/c| ≤ _
  rw [← max_div_div_right hb.le, zero_div, sub_div, div_right_comm a (p:ℝ) b,
    Nat.cast_sub hmin, sub_div, div_self cc.ne']
  rw [← max_eq_left base]
  apply (abs_max_sub_max_le_abs _ _ _).trans
  change |a/b/p-v/b - ((K:ℝ)/c-1)| ≤ 1/(p:ℝ) + |v/b-1| + 1/(c:ℝ)
  apply abs_le.mpr
  constructor <;> linarith only [lo, hi, hlo, hhi, hw.1, hw.2,
    (by positivity : 0 ≤ 1/(p:ℝ)), (by positivity : 0 ≤ 1/(c:ℝ))]

/-- Two sites in one consecutive square-root block have coprime active
wheel factors: a common high prime would divide their smaller difference. -/
theorem nativeDyadic_firstPrime_wheel_block_coprime (P : Finset ℕ) (c a b : ℕ)
    (hp : ∀ p ∈ P, p.Prime ∧ c < p) (hab : a < b) (hg : b-a ≤ c) :
    let active := fun n => P.filter (fun p => p ∣ n ∧ c*p < n)
    (∏ p ∈ active a, p).Coprime (∏ p ∈ active b, p) := by
  dsimp only
  apply Nat.coprime_prod_left_iff.mpr
  intro p ha
  apply Nat.coprime_prod_right_iff.mpr
  intro r hb
  obtain ⟨hpP, hpa, _⟩ := Finset.mem_filter.mp ha
  obtain ⟨hrP, hrb, _⟩ := Finset.mem_filter.mp hb
  apply (Nat.coprime_primes (hp p hpP).1 (hp r hrP).1).mpr
  rintro rfl
  have hdiv : p ∣ b-a := Nat.dvd_sub hrb hpa
  exact (not_lt_of_ge ((Nat.le_of_dvd (Nat.sub_pos_of_lt hab) hdiv).trans hg)) (hp p hpP).2

/-- A single integral functional prescribes every star-column pairing at
once on a coprime block. The preceding arithmetic supplies the coprimality
for the actual squarefree wheel factors, including every shared multiple. -/
theorem nativeDyadic_firstPrime_wheel_block_dual {I : Type*} [Fintype I] [DecidableEq I]
    (D : I → ℕ) (d : ℕ) (hne : ∀ i, D i ≠ 0) (hd : ∀ i, d.Coprime (D i))
    (hc : Pairwise (fun i j => (D i).Coprime (D j))) (y : I → ℤ) :
    ∃ (v : ℤ) (u : I → ℤ), ∀ i, (D i : ℤ)*u i - (d : ℤ)*v = y i := by
  classical
  let (i : I) : NeZero (D i) := ⟨hne i⟩
  let z (i : I) : ZMod (D i) := -(y i : ZMod (D i)) * (d : ZMod (D i))⁻¹
  let a := Nat.chineseRemainderOfFinset (fun i => (z i).val) D Finset.univ
    (fun i _ => hne i) (fun _ _ _ _ h => hc h)
  have hv (i : I) : (a.val : ZMod (D i)) = z i := by
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).2 (a.property i (Finset.mem_univ i))
    simpa only [ZMod.natCast_zmod_val] using h
  have hdvd (i : I) : (D i : ℤ) ∣ y i + (d : ℤ)*a.val := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, hv]
    have hi := ZMod.mul_inv_of_unit (d : ZMod (D i)) ((ZMod.isUnit_iff_coprime _ _).mpr (hd i))
    change (y i : ZMod (D i)) + d * (-(y i : ZMod (D i))*(d : ZMod (D i))⁻¹) = 0
    linear_combination -(y i : ZMod (D i)) * hi
  choose u hu using hdvd
  exact ⟨a.val, u, fun i => by linarith only [hu i]⟩

/-- The actual diagonal wheel factors and their common pivot give the
Gram determinant of the very columns on which the integral dual acts. -/
theorem nativeDyadic_firstPrime_wheel_block_gram {I : Type*} [Fintype I] [DecidableEq I]
    (D : I → ℕ) (d : ℕ) (hne : ∀ i, D i ≠ 0) :
    let B := Matrix.fromRows (Matrix.diagonal (fun i => (D i : ℝ)))
      (Matrix.replicateRow Unit (fun _ : I => -(d:ℝ)))
    (B.transpose * B).det =
      (∏ i, (D i : ℝ))^2 * (1 + ∑ i, ((d:ℝ)/(D i:ℝ))^2) := by
  classical
  let A := Matrix.diagonal (fun i => (D i : ℝ))
  let z := fun i => -((d:ℝ)/(D i:ℝ))
  let G := Matrix.fromRows (1 : Matrix I I ℝ) (Matrix.replicateRow Unit z)
  let B := Matrix.fromRows A (Matrix.replicateRow Unit (fun _ : I => -(d:ℝ)))
  have factor : B = G * A := by
    change Matrix.fromRows A _ = Matrix.fromRows (1 : Matrix I I ℝ) (Matrix.replicateRow Unit z) * A
    rw [Matrix.fromRows_mul, Matrix.one_mul]
    apply congrArg (Matrix.fromRows A)
    ext i j
    change -(d:ℝ) = (Matrix.replicateRow Unit z * Matrix.diagonal (fun i => (D i : ℝ))) i j
    rw [Matrix.mul_diagonal, Matrix.replicateRow_apply]
    change -(d:ℝ) = -((d:ℝ)/(D j:ℝ))*(D j:ℝ)
    rw [neg_mul, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (hne j))]
  have normal : (G.transpose * G).det = 1 + ∑ i, ((d:ℝ)/(D i:ℝ))^2 := by
    dsimp only [G]
    rw [Matrix.transpose_fromRows, Matrix.fromCols_mul_fromRows, Matrix.transpose_one,
      Matrix.one_mul, Matrix.transpose_replicateRow, Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp only [dotProduct, z, neg_mul_neg, pow_two]
  change (B.transpose * B).det = _
  calc
    _ = (A.transpose * ((G.transpose * G) * A)).det := by
      rw [factor, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, normal,
        show A.det = _ from Matrix.det_diagonal _]
      ring

end AlpogeThin
end RHLean.Analysis

import RHLean.Analysis.AlpogeThin.NativeDyadicShiftedWidthRows
import Mathlib.Algebra.Order.Ring.GeomSum

/-! A common integer translation of the original top heights controls divisibility
of differences between their actual quotient-slot endpoints. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace RHLean.Analysis.AlpogeThin.SlotProjector

/-- Difference of the integer endpoints for the two actual primes. The offsets
can be equal when the primes share an original top. -/
def heightEndpointGap (a b p q h : ℕ) : ℤ :=
  (((a+h)/p : ℕ) : ℤ) - (((b+h)/q : ℕ) : ℤ)

theorem heightEndpointGap_shift (a b p q h j : ℕ) (hp : 0 < p) (hq : 0 < q) :
    heightEndpointGap a b p q (h+p*q*j) =
      heightEndpointGap a b p q h + ((q:ℤ)-p)*j := by
  unfold heightEndpointGap
  rw [show a+(h+p*q*j) = (a+h)+p*(q*j) by ring, Nat.add_mul_div_left _ _ hp,
    show b+(h+p*q*j) = (b+h)+q*(p*j) by ring, Nat.add_mul_div_left _ _ hq]
  push_cast
  ring

private theorem owner_unit (p q k : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    IsUnit ((q : ZMod (p^k)) - p) := by
  have unit (n : ℕ) (hh : ¬p ∣ n) : IsUnit (n : ZMod (p^k)) :=
    (ZMod.isUnit_iff_coprime _ _).2 ((hp.coprime_iff_not_dvd.mpr hh).symm.pow_right k)
  rcases le_total p q with h | h
  · rw [← Nat.cast_sub h]
    apply unit
    intro h'
    have hd := dvd_add h' (dvd_refl p)
    rw [Nat.sub_add_cancel h] at hd
    exact hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd)
  · have hlt := lt_of_le_of_ne h hne.symm
    have hv : ¬p ∣ p-q := fun hh =>
      (Nat.sub_lt hp.pos hq.pos).not_ge (Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hh)
    have hh := (unit (p-q) hv).neg
    rwa [Nat.cast_sub h, neg_sub] at hh

private theorem gap_residue (a b p q h k j : ℕ) (hp : p.Prime) (hq : q.Prime) :
    ((heightEndpointGap a b p q (h+p*q*j):ℤ) : ZMod (p^k)) =
      (heightEndpointGap a b p q h : ZMod (p^k)) + ((q:ZMod (p^k))-p)*j := by
  rw [heightEndpointGap_shift _ _ _ _ _ _ hp.pos hq.pos]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_natCast]

/-- Along each progression of common translates spaced by pq, the difference
of endpoints hits every residue modulo every power of its owner prime exactly
once per period. Both starting heights are fixed before the progression. -/
theorem sharedHeight_period (a b p q h k : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    Function.Bijective (fun j : ZMod (p^k) =>
      ((heightEndpointGap a b p q (h+p*q*j.val) : ℤ) : ZMod (p^k))) := by
  let u := (q : ZMod (p^k)) - p
  have hu : IsUnit u := owner_unit p q k hp hq hne
  let _ : NeZero (p^k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let c := ((heightEndpointGap a b p q h : ℤ) : ZMod (p^k))
  have formula (j : ZMod (p^k)) :
      ((heightEndpointGap a b p q (h+p*q*j.val) : ℤ) : ZMod (p^k)) = c+u*j := by
    rw [gap_residue _ _ _ _ _ _ _ hp hq, ZMod.natCast_zmod_val]
  rw [funext formula]
  obtain ⟨v, hv⟩ := hu
  rw [← hv]
  exact (v.mulLeft.trans (Equiv.addLeft c)).bijective

/-- Arbitrary intervals of the common height shift. The endpoint correction
is pq independently of the depth, so summing through the largest possible
valuation is affordable inside the original height collar. -/
theorem sharedHeight_count (a b p q h k N : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    ((Finset.range N).filter fun i =>
      ((heightEndpointGap a b p q (h+i) : ℤ) : ZMod (p^k)) = 0).card ≤ N/(p^k)+p*q := by
  classical
  let s := p*q
  let d := p^k
  let u := (q : ZMod d)-p
  let F (i : ℕ) := ((heightEndpointGap a b p q (h+i) : ℤ) : ZMod d)
  let E := (Finset.range N).filter (fun i => F i = 0)
  let address (i : ℕ) := (i%s, i/s/d)
  have hs : 0 < s := Nat.mul_pos hp.pos hq.pos
  have hd : 0 < d := pow_pos hp.pos k
  have hu : IsUnit u := owner_unit p q k hp hq hne
  have identify (i : ℕ) : F i = (heightEndpointGap a b p q (h+i%s) : ZMod d) + u*(i/s:ℕ) := by
    change ((heightEndpointGap a b p q (h+i) : ℤ) : ZMod (p^k)) = _
    have eqn : h+i = (h+i%s)+p*q*(i/s) := by rw [add_assoc, Nat.mod_add_div]
    rw [eqn, gap_residue _ _ _ _ _ _ _ hp hq]
  have reconstruct {i j n : ℕ} (hm : i%n = j%n) (hd' : i/n = j/n) : i = j := calc
    _ = i%n+n*(i/n) := (Nat.mod_add_div i n).symm
    _ = j%n+n*(j/n) := by rw [hm, hd']
    _ = _ := Nat.mod_add_div j n
  have inject : Set.InjOn address E := by
    intro i hi j hj eqn
    have low : i%s = j%s := congrArg Prod.fst eqn
    have high : i/s/d = j/s/d := congrArg Prod.snd eqn
    have eqF : F i = F j := (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm
    rw [identify i, identify j, low] at eqF
    have middle := hu.mul_left_cancel (add_left_cancel eqF)
    apply reconstruct low (reconstruct _ high)
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 middle
  change E.card ≤ N/d+s
  calc
    _ ≤ ((Finset.range s) ×ˢ (Finset.range (N/s/d+1))).card := by
      apply Finset.card_le_card_of_injOn address _ inject
      intro i hi
      have hlt : i < N := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hs),
        Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.div_le_div_right hlt.le)))⟩
    _ = s*(N/s/d)+s := by rw [Finset.card_product, Finset.card_range, Finset.card_range, Nat.mul_add, Nat.mul_one]
    _ ≤ _ := by
      apply Nat.add_le_add_right
      apply (Nat.le_div_iff_mul_le hd).2
      calc
        _ = s*((N/s/d)*d) := Nat.mul_assoc ..
        _ ≤ s*(N/s) := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
        _ ≤ N := (Nat.mul_comm _ _).trans_le (Nat.div_mul_le_self _ _)

private theorem sharedHeight_sum (a b p q h N L : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (size : ∀ i < N, 0 < (heightEndpointGap a b p q (h+i)).natAbs ∧
      (heightEndpointGap a b p q (h+i)).natAbs < p^L) :
    ∑ i ∈ Finset.range N, (heightEndpointGap a b p q (h+i)).natAbs.factorization p ≤
      N/(p-1)+(L-1)*(p*q) := by
  classical
  let g i := heightEndpointGap a b p q (h+i)
  let T := Finset.Ico 1 L
  have levels i (hi : i ∈ Finset.range N) : (g i).natAbs.factorization p =
      ∑ k ∈ T, if (g i : ZMod (p^k)) = 0 then 1 else 0 := by
    have hs := size i (Finset.mem_range.mp hi)
    rw [Nat.factorization_eq_card_pow_dvd_of_lt hp hs.1 hs.2, Finset.card_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    have test : (g i : ZMod (p^k)) = 0 ↔ p^k ∣ (g i).natAbs := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← Int.natCast_dvd_natCast, Int.dvd_natAbs]
    simp only [test]
  calc
    _ = ∑ i ∈ Finset.range N, ∑ k ∈ T, if (g i : ZMod (p^k)) = 0 then 1 else 0 :=
      Finset.sum_congr rfl levels
    _ = ∑ k ∈ T, ∑ i ∈ Finset.range N, if (g i : ZMod (p^k)) = 0 then 1 else 0 := Finset.sum_comm
    _ ≤ ∑ k ∈ T, (N/(p^k)+p*q) := by
      refine Finset.sum_le_sum fun k _ => ?_
      rw [← Finset.card_filter]
      exact sharedHeight_count a b p q h k N hp hq hne
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
      exact Nat.add_le_add_right (Nat.geom_sum_Ico_le hp.two_le N L) _

/-- One common shift in the allowed interval pays the actual full owner-prime
valuations for every labelled comparison together, including repeated use of
a starting height. The natural endpoint correction uses only the number of
possible valuation levels. -/
theorem sharedHeight_total {I : Type*} (tags : Finset I) (p q a b L : I → ℕ) (h N : ℕ)
    (hN : 0 < N) (hp : ∀ i ∈ tags, (p i).Prime) (hq : ∀ i ∈ tags, (q i).Prime)
    (hne : ∀ i ∈ tags, p i ≠ q i) (size : ∀ i ∈ tags, ∀ j < N,
      0 < (heightEndpointGap (a i) (b i) (p i) (q i) (h+j)).natAbs ∧
      (heightEndpointGap (a i) (b i) (p i) (q i) (h+j)).natAbs < p i ^ L i) :
    ∃ j < N, (N:ℝ)*(∑ i ∈ tags,
      ((heightEndpointGap (a i) (b i) (p i) (q i) (h+j)).natAbs.factorization (p i):ℝ)*
        Real.log (p i)) ≤
      ∑ i ∈ tags, ((N/(p i-1)+(L i-1)*(p i*q i):ℕ):ℝ)*Real.log (p i) := by
  classical
  let mass (i : I) j := (heightEndpointGap (a i) (b i) (p i) (q i) (h+j)).natAbs.factorization (p i)
  let bill j := ∑ i ∈ tags, (mass i j:ℝ)*Real.log (p i)
  obtain ⟨j, hj, least⟩ := Finset.exists_min_image (Finset.range N) bill (Finset.nonempty_range_iff.mpr hN.ne')
  refine ⟨j, Finset.mem_range.mp hj, ?_⟩
  change (N:ℝ)*bill j ≤ _
  calc
    _ = ∑ _t ∈ Finset.range N, bill j := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    _ ≤ ∑ t ∈ Finset.range N, bill t := Finset.sum_le_sum fun t ht => least t ht
    _ = ∑ i ∈ tags, (∑ t ∈ Finset.range N, (mass i t:ℝ))*Real.log (p i) := by
      simp only [bill, Finset.sum_mul]
      exact Finset.sum_comm
    _ ≤ _ := by
      refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg _)
      exact_mod_cast sharedHeight_sum (a i) (b i) (p i) (q i) h N (L i)
        (hp i hi) (hq i hi) (hne i hi) (size i hi)

/-- Integral diagonal multiplier on the original integer slots. Each distinct
factor is read at the actual cutoff of a competitor on the same height profile. -/
def slotSelector {I : Type*} (C : Finset I) (z : I → ℕ) (k : ℕ) : ℤ :=
  ∏ i ∈ C, ((k:ℤ)-z i)

/-- Exact lost valuation at the owner's endpoint, vanishing at every competing
endpoint and an independent real norm bound on the whole physical slot set. -/
theorem slotSelector_price {I : Type*} (C : Finset I) (a q : I → ℕ) (b p h A : ℕ)
    (U : Finset ℕ) (hcut : ∀ i ∈ C, (a i+h)/q i ≤ A) (hslot : ∀ k ∈ U, k ≤ A)
    (hs : ∀ i ∈ C, heightEndpointGap b (a i) p (q i) h ≠ 0) :
    let z := fun i => (a i+h)/q i
    let S := slotSelector C z
    (∀ i ∈ C, S (z i) = 0) ∧
    (S ((b+h)/p)).natAbs.factorization p =
      ∑ i ∈ C, (heightEndpointGap b (a i) p (q i) h).natAbs.factorization p ∧
    ∀ f : ℕ → ℝ, ∑ k ∈ U, ((S k:ℝ)*f k)^2 ≤
      ((A:ℝ)^C.card)^2 * ∑ k ∈ U, (f k)^2 := by
  classical
  intro z S
  refine ⟨fun i hi => Finset.prod_eq_zero hi (sub_self _), ?_, ?_⟩
  · change (Int.natAbsHom (∏ i ∈ C, heightEndpointGap b (a i) p (q i) h)).factorization p = _
    rw [map_prod]
    exact Nat.factorization_prod_apply fun i hi => Int.natAbs_ne_zero.mpr (hs i hi)
  · intro f
    have bound (k : ℕ) (hk : k ∈ U) : |(S k:ℝ)| ≤ (A:ℝ)^C.card := by
      change |((∏ i ∈ C, ((k:ℤ)-z i) : ℤ):ℝ)| ≤ _
      rw [Int.cast_prod, Finset.abs_prod, ← Finset.prod_const]
      refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i hi => ?_
      have h1 : (k:ℝ) ≤ A := by exact_mod_cast hslot k hk
      have h2 : (z i:ℝ) ≤ A := by exact_mod_cast hcut i hi
      push_cast
      exact abs_le.mpr ⟨by linarith only [h2,Nat.cast_nonneg (α := ℝ) k],
        by linarith only [h1,Nat.cast_nonneg (α := ℝ) (z i)]⟩
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [mul_pow]
    have power := pow_le_pow_left₀ (abs_nonneg _) (bound k hk) 2
    rw [sq_abs] at power
    exact mul_le_mul_of_nonneg_right power (sq_nonneg _)

end RHLean.Analysis.AlpogeThin.SlotProjector

import RHLean.Analysis.AlpogeThin.NativeDyadicShiftedWidthRows

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

end RHLean.Analysis.AlpogeThin.SlotProjector

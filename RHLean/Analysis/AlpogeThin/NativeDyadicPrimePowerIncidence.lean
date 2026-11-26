import RHLean.Analysis.AlpogeNativeLocalGainSource
import RHLean.Analysis.AlpogeNativeDyadicHostSize
import RHLean.Analysis.AlpogeNativeSharpASKBalance
import RHLean.Analysis.AlpogeThin.NativeDyadicHostWindows

/-!
# Prime powers and first visits on the dyadic host

On a central orbit every step has top sign. Its positive first visits to distinct
tops are precisely the odd steps before the order of the dyadic displacement
that land in the top set. This gives an exact mask at every cutoff. For the
actual CRT Frobenius, equality of two displacements also determines the two
prime powers whenever their sum is below the dyadic modulus.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace RHLean.Analysis

theorem alpogeNativeLocalGainExcluded_iff_order {H : Type*} [AddCommGroup H] [Finite H]
    (TT : Finset H) (g : AlpogeNativeE0 × H) (t : H) (i : ℕ) :
    alpogeNativeLocalGainExcluded TT g t i ↔
      Odd i ∧ g.1.2 = 1 ∧ i < addOrderOf g.2 ∧ t + i • g.2 ∈ TT := by
  classical
  have hpartner (hg : g.1.2 = 1) (j : ℕ) : alpogeNativeLocalGainPartner g t j =
      alpogeNativeTopPl (t + j • g.2) := by
    simp only [alpogeNativeLocalGainPartner, alpogeNativeTopPl, hg,
      show (1 : ZMod 2) + 1 = 0 by decide, nsmul_zero]
  constructor
  · intro h
    have hbit : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    have hg := (hbit g.1.2).resolve_left fun hz =>
      alpogeNativeLocalGain_not_excluded_of_signal TT g t i hz h
    obtain ⟨hi, s, hs, hst, hret, hfirst⟩ := h
    have hdest : t + i • g.2 = s := congrArg Prod.snd hret
    refine ⟨hi, hg, ?_, hdest.symm ▸ hs⟩
    by_contra! hle
    let j := i % addOrderOf g.2
    have hjlt : j < addOrderOf g.2 := Nat.mod_lt _ (addOrderOf_pos g.2)
    have hjEq : j • g.2 = i • g.2 := mod_addOrderOf_nsmul g.2 i
    have hjPos : 0 < j := by
      by_contra! hj
      have hj0 : j = 0 := by omega
      rw [← hjEq, hj0, zero_nsmul, add_zero] at hdest
      exact hst hdest.symm
    apply hfirst j hjPos (hjlt.trans_le hle)
    rw [hpartner hg, hjEq, hdest]
  · rintro ⟨hi, hg, ho, ht⟩
    have hinj : (Set.Iio (addOrderOf g.2)).InjOn (fun j : ℕ => j • g.2) :=
      pow_injOn_Iio_orderOf (x := Multiplicative.ofAdd g.2)
    have hdistinct (j : ℕ) (hj : j < i) : t + j • g.2 ≠ t + i • g.2 := by
      intro heq
      exact hj.ne (hinj (hj.trans ho) ho (add_left_cancel heq))
    refine ⟨hi, t + i • g.2, ht, ?_, hpartner hg i, ?_⟩
    · intro h
      apply hdistinct 0 hi.pos
      simpa only [zero_nsmul, add_zero] using h.symm
    · intro j _hj hji heq
      exact hdistinct j hji (congrArg Prod.snd heq)

namespace AlpogeThin

/-- Exact first-return contribution at the physical site, with the original
    cutoff, widths and all odd prime-power weights. -/
theorem nativeDyadicLocalExcludedSource_eq_order_sum (e q d N p : ℕ)
    [Fact q.Prime] [Fact d.Prime] (TT : Finset (AlpogeNativeDyadicH e))
    (a : ℝ) (t : AlpogeNativeDyadicH e)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ) :
    nativeDyadicLocalExcludedSource e q d N p TT a t w =
      ∑ i ∈ (Finset.Icc 1 N).filter Odd,
        if ((alpogeNativeHostData e q d).frob p).1.2 = 1 ∧
            i < addOrderOf ((alpogeNativeHostData e q d).frob p).2 ∧
            t + i • ((alpogeNativeHostData e q d).frob p).2 ∈ TT then
          nativeDyadicLocalSourceAtom e q d p a t w i else 0 := by
  unfold nativeDyadicLocalExcludedSource
  apply Finset.sum_congr rfl
  intro i hi
  simp only [alpogeNativeLocalGainExcluded_iff_order, (Finset.mem_filter.mp hi).2, true_and]

private theorem dyadic_unit_val_eq_of_short_class_eq {e a b : ℕ}
    {u v : (ZMod (2 ^ (e + 2)))ˣ} (ha : (u : ZMod (2 ^ (e + 2))) = a)
    (hb : (v : ZMod (2 ^ (e + 2))) = b) (hpos : 0 < a)
    (hsum : a + b < 2 ^ (e + 2))
    (hclass : (QuotientGroup.mk u : Formalism.FrobeniusOrbits.HGrp e) =
      QuotientGroup.mk v) : a = b := by
  let π := QuotientGroup.mk' (Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ))
  have hπ : π u = π v := hclass
  have h1 : π (u / v) = 1 := by rw [map_div, hπ, div_self']
  have hh := (QuotientGroup.eq_one_iff (u / v)).mp h1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
  rcases Int.even_or_odd k with he | ho
  · rw [he.neg_one_zpow] at hk
    have huv : u = v := div_eq_one.mp hk.symm
    have hab := ha.symm.trans ((congrArg Units.val huv).trans hb)
    have ham : a < 2 ^ (e + 2) := by omega
    have hbm : b < 2 ^ (e + 2) := by omega
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt ham, Nat.mod_eq_of_lt hbm] using
      congrArg ZMod.val hab
  · rw [ho.neg_one_zpow] at hk
    have huv : u = (-1 : (ZMod (2 ^ (e + 2)))ˣ) * v := div_eq_iff_eq_mul.mp hk.symm
    have hz : (a : ZMod (2 ^ (e + 2))) = -b := by
      simpa only [Units.val_mul, Units.val_neg, Units.val_one, ha, hb, neg_one_mul] using
        congrArg Units.val huv
    have hz' : ((a + b : ℕ) : ZMod (2 ^ (e + 2))) = 0 := by
      rw [Nat.cast_add, hz, neg_add_cancel]
    have h0 : a + b = 0 := by
      simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hsum, ZMod.val_zero] using
        congrArg ZMod.val hz'
    omega

/-- Distinct integer prime powers at one top have distinct displacements on
    the actual CRT host if their sum is smaller than its dyadic modulus. -/
theorem nativeDyadicPrimePower_eq_of_displacement_eq (e q d p l i j : ℕ)
    [Fact q.Prime] [Fact d.Prime] (hp : p.Prime) (hl : l.Prime)
    (hpN : ¬ p ∣ alpogeNativeHostN e q d) (hlN : ¬ l ∣ alpogeNativeHostN e q d)
    (hsum : p ^ i + l ^ j < 2 ^ (e + 2))
    (h : i • ((alpogeNativeHostData e q d).frob p).2 =
      j • ((alpogeNativeHostData e q d).frob l).2) : p ^ i = l ^ j := by
  let u (s : ℕ) := ZMod.unitsMap (alpogeNativeTwo_dvd_hostN e q d)
    (alpogeNativeFrobUnit (alpogeNativeHostN e q d) s)
  let π := QuotientGroup.mk' (Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ))
  have hu (s : ℕ) (hs : s.Prime) (hsN : ¬ s ∣ alpogeNativeHostN e q d) :
      ((u s : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = s := by
    have hcrt := (alpogeNativeFrobUnit_modEq (N := alpogeNativeHostN e q d) hs).1
    rw [(Nat.ordCompl_eq_self_iff_zero_or_not_dvd _ hs).mpr (Or.inr hsN)] at hcrt
    dsimp only [u]
    rw [ZMod.unitsMap_val, ZMod.cast_eq_val]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hcrt.of_dvd (alpogeNativeTwo_dvd_hostN e q d))
  change π (u p) ^ i = π (u l) ^ j at h
  refine dyadic_unit_val_eq_of_short_class_eq (u := u p ^ i) (v := u l ^ j) ?_ ?_
    (pow_pos hp.pos i) hsum ?_
  · rw [Units.val_pow_eq_pow_val, hu p hp hpN, Nat.cast_pow]
  · rw [Units.val_pow_eq_pow_val, hu l hl hlN, Nat.cast_pow]
  · change π (u p ^ i) = π (u l ^ j)
    simpa only [map_pow] using h

/-- Every power below half the dyadic modulus occurs before the displacement's
    first repetition, even when comparing earlier steps of either parity. -/
theorem nativeDyadicFrobenius_exp_lt_order_of_short_power (e q d p i : ℕ)
    [Fact q.Prime] [Fact d.Prime] (hp : p.Prime) (hpN : ¬ p ∣ alpogeNativeHostN e q d)
    (hshort : 2 * p ^ i < 2 ^ (e + 2)) :
    i < addOrderOf ((alpogeNativeHostData e q d).frob p).2 := by
  let h := ((alpogeNativeHostData e q d).frob p).2
  change i < addOrderOf h
  by_contra! hle
  let j := i % addOrderOf h
  have hji : j < i := (Nat.mod_lt _ (addOrderOf_pos h)).trans_le hle
  have hpows := Nat.pow_lt_pow_right hp.one_lt hji
  have hh : j • h = i • h := mod_addOrderOf_nsmul h i
  have heq := nativeDyadicPrimePower_eq_of_displacement_eq e q d p p j i hp hp hpN hpN
    (by omega) hh
  exact hpows.ne heq

/-- A visit to an actual top contributes zero once the full power crosses the
    top-width cutoff. This does not require the thin width to equal a thick width. -/
theorem nativeDyadicLocalSourceAtom_eq_zero_of_top_of_power_ge
    (e q d p i : ℕ) [Fact q.Prime] [Fact d.Prime] (hp : p.Prime) (hi : Odd i)
    (hInert : ¬ alpogeNativeInPhi ((alpogeNativeHostData e q d).frob p))
    (a bTop : ℝ) (hbTop : 0 < bTop) (t s : AlpogeNativeDyadicH e)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (hTop : bTop ≤ w (alpogeNativeTopPl s))
    (hret : alpogeNativeLocalGainPartner ((alpogeNativeHostData e q d).frob p) t i =
      alpogeNativeTopPl s) (hhigh : a / bTop ≤ ((p ^ i : ℕ) : ℝ)) :
    nativeDyadicLocalSourceAtom e q d p a t w i = 0 := by
  have hpart : alpogeNativePartner t (i • (alpogeNativeHostData e q d).frob p) =
      alpogeNativeTopPl s :=
    (alpogeNativeLocalGainPartner_eq_partner_of_odd _ t i hInert hi).symm.trans hret
  have hpow : 0 < ((p ^ i : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.pos i
  have hcut : a / ((p ^ i : ℕ) : ℝ) ≤ w (alpogeNativeTopPl s) := by
    apply (div_le_iff₀ hpow).mpr
    calc
      a ≤ ((p ^ i : ℕ) : ℝ) * bTop := (div_le_iff₀ hbTop).mp hhigh
      _ = bTop * ((p ^ i : ℕ) : ℝ) := mul_comm _ _
      _ ≤ w (alpogeNativeTopPl s) * ((p ^ i : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hTop hpow.le
  simp only [nativeDyadicLocalSourceAtom, alpogeNativeSiteCut, Complex.ofReal_re,
    hpart, max_eq_right (sub_nonpos.mpr hcut)]

end AlpogeThin
end RHLean.Analysis

noncomputable section

namespace RHLean.Analysis

section FrobeniusCoset

variable {G : Type*} [AddCommGroup G]

/-- Order of the image of the specified Frobenius in its inertia quotient. -/
def frobeniusCosetOrder (I : AddSubgroup G) (g : G) : ℕ :=
  addOrderOf (QuotientAddGroup.mk' I g)

theorem frobeniusCosetOrder_dvd_natCard (I : AddSubgroup G) (g : G) :
    frobeniusCosetOrder I g ∣ Nat.card G :=
  (addOrderOf_map_dvd (QuotientAddGroup.mk' I) g).trans (addOrderOf_dvd_natCard g)

theorem frobeniusCosetOrder_dvd_iff (I : AddSubgroup G) (g : G) (k : ℕ) :
    frobeniusCosetOrder I g ∣ k ↔ k • g ∈ I := by
  change addOrderOf ((QuotientAddGroup.mk' I) g) ∣ k ↔ _
  rw [addOrderOf_dvd_iff_nsmul_eq_zero, ← map_nsmul]
  exact QuotientAddGroup.eq_zero_iff _

private theorem frobeniusCoset_pos_inj (I : AddSubgroup G) (g : G) {i j : ℕ}
    (hi : i < frobeniusCosetOrder I g) (hj : j < frobeniusCosetOrder I g)
    (h : (j + 1) • g - (i + 1) • g ∈ I) : i = j := by
  let π := QuotientAddGroup.mk' I
  let x := π g
  have hq : π ((j + 1) • g - (i + 1) • g) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr h
  have he : (j + 1) • x = (i + 1) • x := by
    simpa only [map_sub, map_nsmul, sub_eq_zero] using hq
  have hx : j • x = i • x := by
    simpa only [add_nsmul, one_nsmul, add_right_cancel_iff] using he
  have hinj : (Set.Iio (addOrderOf x)).InjOn (fun z : ℕ => z • x) :=
    pow_injOn_Iio_orderOf (x := Multiplicative.ofAdd x)
  exact (hinj hj hi hx).symm

private theorem frobenius_self_sub_mem {A : Type*} [AddGroup A] (I : AddSubgroup A)
    (v : A) : v - v ∈ I := by
  rw [sub_self]
  exact I.zero_mem

/-- The integral incidence read for a positive or zero power at a group site. -/
def frobeniusCosetIncidence (I : AddSubgroup G) (g : G) (i : ℕ) (z : G) : ℤ := by
  classical
  exact if z - i • g ∈ I then 1 else 0

/-- The literal identity-matrix assertion on the consecutive representatives.
Keeping the matrix size inside this definition lets the same proof specialize
to a dyadic host without reducing its Frobenius order during elaboration. -/
def ConsecutiveFrobeniusMinor (I : AddSubgroup G) (g : G) (K : ℕ) : Prop :=
  let n := min K (frobeniusCosetOrder I g)
  (Matrix.of fun i j : Fin n =>
    frobeniusCosetIncidence I g (i.val + 1) ((j.val + 1) • g)) =
    (1 : Matrix (Fin n) (Fin n) ℤ)

private theorem frobeniusCoset_consecutive_matrix (I : AddSubgroup G) (g : G) (K : ℕ) :
    ConsecutiveFrobeniusMinor I g K := by
  classical
  let n := min K (frobeniusCosetOrder I g)
  change (Matrix.of fun i j : Fin n =>
    frobeniusCosetIncidence I g (i.val + 1) ((j.val + 1) • g)) = 1
  have hdeg (i : Fin n) : i.val < frobeniusCosetOrder I g :=
    i.isLt.trans_le (Nat.min_le_right _ _)
  ext i j
  rw [Matrix.of_apply, frobeniusCosetIncidence, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left (frobenius_self_sub_mem I ((i.val + 1) • g)), ite_eq_left rfl]
  · have hsep : (j.val + 1) • g - (i.val + 1) • g ∉ I :=
      fun h => hij (Fin.ext (frobeniusCoset_pos_inj (G := G) I g (i := i.val) (j := j.val)
        (hdeg i) (hdeg j) h))
    rw [ite_eq_right hsep, ite_eq_right hij]

private theorem frobenius_nsmul_shift (g : G) (i k : ℕ) :
    (i + k) • g - i • g = k • g := by rw [add_nsmul]; abel

private theorem frobenius_translate_mem (I : AddSubgroup G) (g a : G) (i k : ℕ)
    (hk : k • g ∈ I) : a - (i + k) • g ∈ I ↔ a - i • g ∈ I := by
  have hs : a - (i + k) • g = a - i • g - k • g := by rw [add_nsmul]; abel
  rw [hs]
  constructor
  · intro h
    simpa only [sub_add_cancel] using I.add_mem h hk
  · exact fun h => I.sub_mem h hk

end FrobeniusCoset

/-- Integral indicator of the original Frobenius coset of inertia at a
prime-power site. -/
def nativeDyadicPrimePowerIncidence (e q d p i : ℕ) [Fact q.Prime] [Fact d.Prime]
    (g : AlpogeNativeE0 × AlpogeNativeDyadicH e) : ℤ :=
  let H := alpogeNativeHostData e q d
  frobeniusCosetIncidence (H.inertia p) (H.frob p) i g

open Classical in
/-- Normalization relating the integer row to the full kernel at each
genuine prime power, including its ramified inertia factor. -/
theorem nativeDyadic_colourKernel_eq_incidence (e q d p i : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hp : p.Prime) (hi : 0 < i) (g : AlpogeNativeE0 × AlpogeNativeDyadicH e) :
    let H := alpogeNativeHostData e q d
    alpogeNativeColourKernel H.inertia H.frob (p ^ i) g =
      (2 / ((Finset.univ.filter (fun u : AlpogeNativeE0 × AlpogeNativeDyadicH e =>
        u ∈ H.inertia p)).card : ℂ)) * (nativeDyadicPrimePowerIncidence e q d p i g : ℂ) := by
  let H := alpogeNativeHostData e q d
  change alpogeNativeColourKernel H.inertia H.frob (p ^ i) g = _
  rw [alpogeNativeColourKernel_primePower H.inertia H.frob p i hp hi g]
  by_cases h : g - i • H.frob p ∈ H.inertia p
  · have hrow : nativeDyadicPrimePowerIncidence e q d p i g = 1 := ite_eq_left h
    simp only [ite_eq_left h, hrow, Int.cast_one, mul_one]
    rfl
  · have hrow : nativeDyadicPrimePowerIncidence e q d p i g = 0 := ite_eq_right h
    simp only [ite_eq_right h, hrow, Int.cast_zero, mul_zero]

/-- Distinct retained Frobenius cosets have an integral identity submatrix
on their actual representatives. Every competing coset disjoint from those
cosets has the zero matrix on the same columns. This is depth-zero recovery
of the retained colour coordinates on the unrestricted integer site lattice. -/
theorem nativeDyadic_colourIncidence_minor {I J : Type*} [DecidableEq I]
    (e q d p : ℕ) [Fact q.Prime] [Fact d.Prime]
    (selected : I → ℕ) (competing : J → ℕ) :
    let H := alpogeNativeHostData e q d
    (∀ i j, selected j • H.frob p - selected i • H.frob p ∈ H.inertia p → i = j) →
    (∀ s j, selected j • H.frob p - competing s • H.frob p ∉ H.inertia p) →
    (Matrix.of fun i j : I => nativeDyadicPrimePowerIncidence e q d p (selected i)
        (selected j • H.frob p)) = (1 : Matrix I I ℤ) ∧
    (Matrix.of fun s j => nativeDyadicPrimePowerIncidence e q d p (competing s)
        (selected j • H.frob p)) = (0 : Matrix J I ℤ) := by
  classical
  let H := alpogeNativeHostData e q d
  change (∀ i j, selected j • H.frob p - selected i • H.frob p ∈ H.inertia p → i = j) →
    (∀ s j, selected j • H.frob p - competing s • H.frob p ∉ H.inertia p) → _
  intro hsep hdisj
  constructor
  · ext i j
    change (if selected j • H.frob p - selected i • H.frob p ∈ H.inertia p then (1 : ℤ) else 0) =
      (1 : Matrix I I ℤ) i j
    by_cases hij : i = j
    · subst j
      have hz : selected i • H.frob p - selected i • H.frob p ∈ H.inertia p :=
        frobenius_self_sub_mem (A := AlpogeNativeE0 × AlpogeNativeDyadicH e)
          (H.inertia p) (selected i • H.frob p)
      exact (ite_eq_left hz).trans (Matrix.one_apply_eq (α := ℤ) i).symm
    · rw [ite_eq_right (fun h => hij (hsep i j h)), Matrix.one_apply, ite_eq_right hij]
  · ext s j
    change (if selected j • H.frob p - competing s • H.frob p ∈ H.inertia p then (1 : ℤ) else 0) = 0
    exact ite_eq_right (hdisj s j)

section HostMinor

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- The consecutive identity minor for the inertia and Frobenius of one host. -/
def AlpogeNativeArithData.consecutiveColourMinor (D : AlpogeNativeArithData H)
    (p K : ℕ) : Prop :=
  ConsecutiveFrobeniusMinor (G := AlpogeNativeE0 × H) (D.inertia p) (D.frob p) K

private theorem host_consecutive_colourIncidence_minor (D : AlpogeNativeArithData H)
    (p K : ℕ) : D.consecutiveColourMinor p K :=
  frobeniusCoset_consecutive_matrix (G := AlpogeNativeE0 × H) (D.inertia p) (D.frob p) K

end HostMinor

set_option maxHeartbeats 1000000 in
attribute [local irreducible] AlpogeNativeArithData.consecutiveColourMinor alpogeNativeHostData in
/-- Consecutive positive powers have an explicit identity minor up to the
order of the actual Frobenius class modulo inertia. The host-level application
keeps the concrete quotient out of definitional equality during elaboration. -/
theorem nativeDyadic_consecutive_colourIncidence_minor (e q d p K : ℕ)
    [Fact q.Prime] [Fact d.Prime] :
    AlpogeNativeArithData.consecutiveColourMinor (H := AlpogeNativeDyadicH e)
      (alpogeNativeHostData e q d) p K :=
  host_consecutive_colourIncidence_minor (H := AlpogeNativeDyadicH e)
    (alpogeNativeHostData e q d) p K

open Classical in
/-- Both numerator and denominator in the ramified colour normalization are
coprime to every odd prime on the square-clock host. -/
theorem nativeDyadic_colourNormalization_coprime (e q d p : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hp : p.Prime) (hodd : p ≠ 2) :
    let I := (alpogeNativeHostData e q d).inertia p
    Nat.Coprime p 2 ∧ Nat.Coprime p
      (Finset.univ.filter (fun u : AlpogeNativeE0 × AlpogeNativeDyadicH e => u ∈ I)).card := by
  let I := (alpogeNativeHostData e q d).inertia p
  have h2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hodd
  have hsize : Nat.card (AlpogeNativeE0 × AlpogeNativeDyadicH e) = 2 ^ (e + 2) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, alpogeNativeDyadicH_card, pow_add]
    have h4 : Fintype.card AlpogeNativeE0 = 4 := by decide
    rw [h4]
    ring
  have hd : Nat.card I ∣ 2 ^ (e + 2) :=
    I.card_addSubgroup_dvd_card.trans (dvd_of_eq hsize)
  have hc : (Finset.univ.filter (fun u : AlpogeNativeE0 × AlpogeNativeDyadicH e => u ∈ I)).card =
      Nat.card I := by
    change _ = Nat.card {u : AlpogeNativeE0 × AlpogeNativeDyadicH e // u ∈ I}
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  change Nat.Coprime p 2 ∧ Nat.Coprime p _
  rw [hc]
  exact ⟨h2, Nat.Coprime.of_dvd_right hd (h2.pow_right _)⟩

/-- Full prime-power colour rows coincide exactly on returns modulo inertia,
including at ramified primes. The physical height and prime power remain
separately indexed. -/
theorem nativeDyadic_colourKernel_eq_iff_frob_return (e q d p i k : ℕ)
    [Fact q.Prime] [Fact d.Prime] (hp : p.Prime) (hi : 0 < i) :
    let H := alpogeNativeHostData e q d
    alpogeNativeColourKernel H.inertia H.frob (p ^ (i + k)) =
        alpogeNativeColourKernel H.inertia H.frob (p ^ i) ↔ k • H.frob p ∈ H.inertia p := by
  classical
  let H := alpogeNativeHostData e q d
  change alpogeNativeColourKernel H.inertia H.frob (p ^ (i + k)) =
    alpogeNativeColourKernel H.inertia H.frob (p ^ i) ↔ k • H.frob p ∈ H.inertia p
  have hik : 0 < i + k := by omega
  constructor
  · intro h
    let g := (i + k) • H.frob p
    have hval := congrFun h g
    have hself : g - (i + k) • H.frob p ∈ H.inertia p :=
      frobenius_self_sub_mem (H.inertia p) g
    have hshift : g - i • H.frob p = k • H.frob p := frobenius_nsmul_shift (H.frob p) i k
    rw [alpogeNativeColourKernel_primePower H.inertia H.frob p (i + k) hp hik g,
      alpogeNativeColourKernel_primePower H.inertia H.frob p i hp hi g,
      ite_eq_left hself, hshift] at hval
    by_contra hn
    rw [ite_eq_right hn] at hval
    have hc : (Finset.univ.filter (fun u : AlpogeNativeE0 × AlpogeNativeDyadicH e =>
        u ∈ H.inertia p)).card ≠ 0 := Finset.card_ne_zero.mpr ⟨0, by simp⟩
    exact (div_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (Nat.cast_ne_zero.mpr hc)) hval
  · intro hreturn
    funext g
    have hcoset := frobenius_translate_mem (H.inertia p) (H.frob p) g i k hreturn
    rw [alpogeNativeColourKernel_primePower H.inertia H.frob p (i + k) hp hik g,
      alpogeNativeColourKernel_primePower H.inertia H.frob p i hp hi g, hcoset]

/-- When the proposed integral readout factors through a colour row, decoding
one occurrence and imposing a competing congruence on a returning occurrence
forces that congruence modulus to divide the decoded scalar. -/
theorem nativeDyadic_competing_dvd_of_colour_return {O L : Type*} [CommRing O]
    (e q d p i k D c : ℕ) [Fact q.Prime] [Fact d.Prime] (hp : p.Prime) (hi : 0 < i)
    (w : O) (readRow : ((AlpogeNativeE0 × AlpogeNativeDyadicH e) → ℂ) → L → O) :
    let H := alpogeNativeHostData e q d
    let K := alpogeNativeColourKernel H.inertia H.frob
    k • H.frob p ∈ H.inertia p →
      (∃ v, readRow (K (p ^ i)) v = (p : O) ^ D ∧ w ^ c ∣ readRow (K (p ^ (i + k))) v) →
        w ^ c ∣ (p : O) ^ D := by
  let H := alpogeNativeHostData e q d
  let K := alpogeNativeColourKernel H.inertia H.frob
  change k • H.frob p ∈ H.inertia p →
    (∃ v, readRow (K (p ^ i)) v = (p : O) ^ D ∧ w ^ c ∣ readRow (K (p ^ (i + k))) v) → _
  intro hreturn h
  obtain ⟨v, hE, hC⟩ := h
  have hrows : K (p ^ (i + k)) = K (p ^ i) :=
    (nativeDyadic_colourKernel_eq_iff_frob_return e q d p i k hp hi).mpr hreturn
  rwa [hrows, hE] at hC

end RHLean.Analysis

end

namespace RHLean.Analysis.AlpogeThin

/-- All four sign pairs and every displacement on this PageN host. -/
theorem squareClock_bareColourCard_le (R e : ℕ) (hR : 2 ≤ R)
    (ε : ℝ) (hε : ε < 1 / 52)
    (hPage : UpperTheory.Top.PageN ε ((R ^ 2 - 1 : ℕ) : ℝ) e) :
    Fintype.card (AlpogeNativeE0 × AlpogeNativeDyadicH e) ≤ 8 * R ^ 6 := by
  let x : ℝ := (R ^ 2 - 1 : ℕ)
  change UpperTheory.Top.PageN ε x e at hPage
  have hR2 : 4 ≤ R ^ 2 := Nat.pow_le_pow_left hR 2
  have hx : 1 ≤ x := by
    dsimp [x]
    exact_mod_cast (show 1 ≤ R ^ 2 - 1 by omega)
  have hxR : x ≤ (R : ℝ) ^ 2 := by
    dsimp [x]
    exact_mod_cast Nat.sub_le (R ^ 2) 1
  have hpow : x ^ (2 + 8 * ε) ≤ ((R : ℝ) ^ 2) ^ (3 : ℕ) := by
    calc
      x ^ (2 + 8 * ε) ≤ x ^ ((3 : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx (by norm_num at hε ⊢; linarith)
      _ = x ^ (3 : ℕ) := Real.rpow_natCast x 3
      _ ≤ ((R : ℝ) ^ 2) ^ (3 : ℕ) := pow_le_pow_left₀ (by linarith) hxR 3
  have hreal : (2 : ℝ) ^ e ≤ 2 * (R : ℝ) ^ 6 := by
    calc
      (2 : ℝ) ^ e ≤ 2 * x ^ (2 + 8 * ε) := hPage.2
      _ ≤ 2 * ((R : ℝ) ^ 2) ^ (3 : ℕ) := mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ = 2 * (R : ℝ) ^ 6 := by ring
  have hn : 2 ^ e ≤ 2 * R ^ 6 := by exact_mod_cast hreal
  have hfour : Fintype.card AlpogeNativeE0 = 4 := by
    norm_num [AlpogeNativeE0, Fintype.card_prod, ZMod.card]
  rw [Fintype.card_prod, hfour, alpogeNativeDyadicH_card]
  omega

private theorem eight_mul_pow_six_lt (R : ℕ) (hR : 3 ≤ R) :
    8 * R ^ 6 < 13 ^ (2 * (R - 1)) := by
  induction R, hR using Nat.le_induction with
  | base => norm_num
  | succ R hR ih =>
    have hstep : R + 1 ≤ 2 * R := by omega
    have he : 2 * ((R + 1) - 1) = 2 * (R - 1) + 2 := by omega
    calc
      8 * (R + 1) ^ 6 ≤ 8 * (2 * R) ^ 6 :=
        Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hstep 6)
      _ = (8 * R ^ 6) * 64 := by ring
      _ < 13 ^ (2 * (R - 1)) * 64 := Nat.mul_lt_mul_of_pos_right ih (by decide)
      _ ≤ 13 ^ (2 * (R - 1)) * 13 ^ 2 := Nat.mul_le_mul_left _ (by decide)
      _ = 13 ^ (2 * ((R + 1) - 1)) := by rw [he, pow_add]

/-- The graph quota dominates the square-clock polynomial throughout the
interior rank range. This only uses a lower bound on the base and on the
residue degree. -/
theorem squareClock_polynomial_lt_graphQuota (R r f p : ℕ) (hp : 13 ≤ p)
    (hf : 1 ≤ f) (hr : 2 ≤ r) (hr' : r ≤ (R + 1) - 2) :
    8 * R ^ 6 < p ^ (f * (r * (R + 1 - r))) := by
  let s := R + 1 - r
  have hs : 2 ≤ s := by dsimp [s]; omega
  have hrs : r + s = R + 1 := by dsimp [s]; omega
  obtain ⟨a, ha⟩ : ∃ a, r = a + 2 := ⟨r - 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, s = b + 2 := ⟨s - 2, by omega⟩
  have hmin : 2 * (R - 1) ≤ r * s := by
    rw [show R - 1 = a + b + 2 by omega, ha, hb]
    nlinarith only [Nat.zero_le (a * b)]
  have hexp : 2 * (R - 1) ≤ f * (r * s) :=
    hmin.trans (by simpa only [one_mul] using Nat.mul_le_mul_right (r * s) hf)
  calc
    8 * R ^ 6 < 13 ^ (2 * (R - 1)) := eight_mul_pow_six_lt R (by omega)
    _ ≤ 13 ^ (f * (r * s)) := Nat.pow_le_pow_right (by decide) hexp
    _ ≤ p ^ (f * (r * s)) := Nat.pow_le_pow_left hp _

/-- Every assignment of a full graph quota to the bare native colours
identifies two labels. The label type can be any finite set realizing the
upstream lower cardinality. -/
theorem squareClock_not_injective_graphLabels_to_colours {A : Type*} [Fintype A]
    (R e r f p : ℕ) (hp : 13 ≤ p) (hf : 1 ≤ f)
    (hr : 2 ≤ r) (hr' : r ≤ (R + 1) - 2) (ε : ℝ) (hε : ε < 1 / 52)
    (hPage : UpperTheory.Top.PageN ε ((R ^ 2 - 1 : ℕ) : ℝ) e)
    (hA : p ^ (f * (r * (R + 1 - r))) ≤ Fintype.card A)
    (colour : A → AlpogeNativeE0 × AlpogeNativeDyadicH e) :
    ¬ Function.Injective colour := by
  intro hinj
  have hlarge := squareClock_polynomial_lt_graphQuota R r f p hp hf hr hr'
  have hsmall := squareClock_bareColourCard_le R e (by omega) ε hε hPage
  exact (not_lt_of_ge ((Fintype.card_le_of_injective colour hinj).trans hsmall))
    (hlarge.trans_le hA)

end RHLean.Analysis.AlpogeThin

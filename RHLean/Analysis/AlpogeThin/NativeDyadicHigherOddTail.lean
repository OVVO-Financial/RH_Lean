import RHLean.Analysis.AlpogeNativeLocalGainSource

/-!
# Uniform tail of the original odd prime-power source

After the first power, an odd power has exponent at least three. Above the
threshold X this leaves a summable prime weight after extracting X^(-5/8).
The mask, conductor, physical widths and original exponent cutoff are arbitrary.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators Classical
namespace RHLean.Analysis.AlpogeThin

private def powerWeight (i : ℕ) : ℝ := ((2 : ℝ) ^ (-(3 / 8) : ℝ)) ^ (i - 3)
private def baseWeight (p : ℕ) : ℝ := (p : ℝ) ^ (-(17 / 16) : ℝ)

private theorem powerWeight_nonnegative (i : ℕ) : 0 ≤ powerWeight i :=
  pow_nonneg (Real.rpow_nonneg (by norm_num) _) _

private theorem baseWeight_nonnegative (p : ℕ) : 0 ≤ baseWeight p :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

private theorem powerWeight_summable : Summable powerWeight := by
  apply (summable_nat_add_iff 3).mp
  simpa only [powerWeight, Nat.add_sub_cancel] using
    (summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(3 / 8)))
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)))

private theorem baseWeight_summable : Summable baseWeight :=
  Real.summable_nat_rpow.mpr (by norm_num : (-(17 / 16) : ℝ) < -1)

/-- A fixed finite constant, independent of the host, cutoff and masking. -/
def nativeDyadicHigherPowerConstant : ℝ :=
  16 * (∑' p, baseWeight p) * (∑' i, powerWeight i)

theorem nativeDyadicHigherPowerConstant_nonneg : 0 ≤ nativeDyadicHigherPowerConstant :=
  mul_nonneg (mul_nonneg (by norm_num) (tsum_nonneg baseWeight_nonnegative))
    (tsum_nonneg powerWeight_nonnegative)

private theorem log_over_power_le (p i : ℕ) (hp : p.Prime) (hi : 3 ≤ i)
    (X : ℝ) (hX : 0 < X) (hlarge : X ≤ (p : ℝ) ^ i) :
    Real.log p / (p : ℝ) ^ i ≤
      16 * X ^ (-(5 / 8) : ℝ) * baseWeight p * powerWeight i := by
  have hp0 : 0 < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  let r := (p : ℝ) ^ (-(3 / 8) : ℝ)
  let R := (2 : ℝ) ^ (-(3 / 8) : ℝ)
  have hr0 : 0 ≤ r := Real.rpow_nonneg hp0.le _
  have hR0 : 0 ≤ R := Real.rpow_nonneg (by norm_num) _
  have hrR : r ≤ R := Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
  have h3 : r ^ 3 = (p : ℝ) ^ (-(9 / 8) : ℝ) := by
    dsimp only [r]
    rw [← Real.rpow_mul_natCast hp0.le]
    norm_num
  have hrpower : r ^ i ≤ (p : ℝ) ^ (-(9 / 8) : ℝ) * R ^ (i - 3) := by
    calc
      r ^ i = r ^ (3 + (i - 3)) := congrArg (r ^ ·) (by omega)
      _ = r ^ 3 * r ^ (i - 3) := pow_add _ _ _
      _ ≤ _ := by
        rw [h3]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hrR _) (Real.rpow_nonneg hp0.le _)
  have hfac : ((p : ℝ) ^ i)⁻¹ =
      ((p : ℝ) ^ i) ^ (-(5 / 8) : ℝ) * r ^ i := by
    calc
      _ = ((p : ℝ) ^ i) ^ (-1 : ℝ) := (Real.rpow_neg_one _).symm
      _ = ((p : ℝ) ^ i) ^ ((-(5 / 8) : ℝ) + -(3 / 8)) := by norm_num
      _ = ((p : ℝ) ^ i) ^ (-(5 / 8) : ℝ) * ((p : ℝ) ^ i) ^ (-(3 / 8) : ℝ) :=
        Real.rpow_add (pow_pos hp0 i) _ _
      _ = _ := by
        congr 1
        dsimp only [r]
        rw [← Real.rpow_natCast_mul hp0.le, ← Real.rpow_mul_natCast hp0.le, mul_comm (i : ℝ)]
  have hinv : ((p : ℝ) ^ i)⁻¹ ≤
      X ^ (-(5 / 8) : ℝ) * ((p : ℝ) ^ (-(9 / 8) : ℝ) * R ^ (i - 3)) := by
    rw [hfac]
    exact mul_le_mul (Real.rpow_le_rpow_of_nonpos hX hlarge (by norm_num)) hrpower
      (pow_nonneg hr0 i) (Real.rpow_nonneg hX.le _)
  have hlog : Real.log p * (p : ℝ) ^ (-(9 / 8) : ℝ) ≤ 16 * baseWeight p := by
    calc
      _ ≤ ((p : ℝ) ^ (1 / 16 : ℝ) / (1 / 16)) * (p : ℝ) ^ (-(9 / 8) : ℝ) :=
        mul_le_mul_of_nonneg_right (Real.log_le_rpow_div hp0.le (by norm_num))
          (Real.rpow_nonneg hp0.le _)
      _ = 16 * ((p : ℝ) ^ (1 / 16 : ℝ) * (p : ℝ) ^ (-(9 / 8) : ℝ)) := by ring
      _ = 16 * baseWeight p := by
        rw [← Real.rpow_add hp0]
        norm_num [baseWeight]
  calc
    Real.log p / (p : ℝ) ^ i = Real.log p * ((p : ℝ) ^ i)⁻¹ := div_eq_mul_inv _ _
    _ ≤ Real.log p * (X ^ (-(5 / 8) : ℝ) * ((p : ℝ) ^ (-(9 / 8) : ℝ) * R ^ (i - 3))) :=
      mul_le_mul_of_nonneg_left hinv (Real.log_natCast_nonneg _)
    _ = X ^ (-(5 / 8) : ℝ) * (Real.log p * (p : ℝ) ^ (-(9 / 8) : ℝ)) * R ^ (i - 3) := by ring
    _ ≤ X ^ (-(5 / 8) : ℝ) * (16 * baseWeight p) * R ^ (i - 3) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hX.le _)) (pow_nonneg hR0 _)
    _ = _ := by dsimp only [powerWeight, R]; ring

/-- The masked part of the literal unramified odd-power sum above X, retaining
    its original exponent cutoff, moving partner width, and prime weight. -/
def nativeDyadicHigherOddTail (e q d N : ℕ) [Fact q.Prime] [Fact d.Prime]
    (X a : ℝ) (t : AlpogeNativeDyadicH e) (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (mask : ℕ → ℕ → Prop) : ℝ :=
  ∑ p ∈ nativeDyadicInertPrimes e q d N,
    ∑ i ∈ (Finset.Icc 1 N).filter (fun i => Odd i ∧ 3 ≤ i ∧ X < (p : ℝ) ^ i ∧ mask p i),
      (2 * Real.log p) * nativeDyadicLocalSourceAtom e q d p a t w i

/-- Remove the priced masked tail from the existing signed-source presentation.
    Every complementary prime power retains its original coefficient. -/
theorem nativeDyadicOddClassASK_re_eq_tail_add_complement (e q d N : ℕ)
    [Fact q.Prime] [Fact d.Prime] (X a : ℝ) (t : AlpogeNativeDyadicH e)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ) (mask : ℕ → ℕ → Prop) :
    (nativeDyadicOddClassASK e q d N a t w).re = nativeDyadicHigherOddTail e q d N X a t w mask +
      ∑ p ∈ nativeDyadicInertPrimes e q d N,
        ∑ i ∈ ((Finset.Icc 1 N).filter Odd).filter
            (fun i => ¬ (3 ≤ i ∧ X < (p : ℝ) ^ i ∧ mask p i)),
          (2 * Real.log p) * nativeDyadicLocalSourceAtom e q d p a t w i := by
  rw [nativeDyadicOddClassASK_re_eq_localSource]
  unfold nativeDyadicHigherOddTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  unfold nativeDyadicLocalOddSource
  rw [Finset.mul_sum]
  symm
  simpa only [Finset.filter_filter] using
    (Finset.sum_filter_add_sum_filter_not (s := (Finset.Icc 1 N).filter Odd)
      (p := fun i => 3 ≤ i ∧ X < (p : ℝ) ^ i ∧ mask p i)
      (f := fun i => (2 * Real.log p) * nativeDyadicLocalSourceAtom e q d p a t w i))

theorem nativeDyadicHigherOddTail_le (e q d N : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hhost : Formalism.FrobeniusOrbits.HostHyp q d) (X a : ℝ) (hX : 0 < X) (ha : 0 ≤ a)
    (t : AlpogeNativeDyadicH e) (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (hw : ∀ z, alpogeNativeInPhi z → 0 ≤ w z) (mask : ℕ → ℕ → Prop) :
    nativeDyadicHigherOddTail e q d N X a t w mask ≤
      2 * a * X ^ (-(5 / 8) : ℝ) * nativeDyadicHigherPowerConstant := by
  let P := nativeDyadicInertPrimes e q d N
  let I (p : ℕ) := (Finset.Icc 1 N).filter (fun i => Odd i ∧ 3 ≤ i ∧ X < (p : ℝ) ^ i ∧ mask p i)
  let A := 2 * a * (16 * X ^ (-(5 / 8) : ℝ))
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (by norm_num) ha)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg hX.le _))
  have hW : 0 ≤ ∑' i, powerWeight i := tsum_nonneg powerWeight_nonnegative
  have hrow (p : ℕ) (hp : p ∈ P) (i : ℕ) (hi : i ∈ I p) :
      (2 * Real.log p) * nativeDyadicLocalSourceAtom e q d p a t w i ≤
        (A * baseWeight p) * powerWeight i := by
    change p ∈ ((Finset.range (N + 1)).filter Nat.Prime).filter
      (fun r => ¬ r ∣ alpogeNativeHostN e q d ∧ jacobiSym (-(d : ℤ)) r = -1) at hp
    obtain ⟨hpB, hpN, hsign⟩ := Finset.mem_filter.mp hp
    have hpP := (Finset.mem_filter.mp hpB).2
    obtain ⟨_, hodd, h3, hXpow, _⟩ := Finset.mem_filter.mp hi
    have hinert := (nativeDyadicHostData_frob_not_inPhi_iff e q d p hhost hpP hpN).mpr hsign
    have hphi : alpogeNativeInPhi (alpogeNativePartner t (i • (alpogeNativeHostData e q d).frob p)) := by
      rw [← alpogeNativeLocalGainPartner_eq_partner_of_odd _ t i hinert hodd]
      rfl
    have hatom : nativeDyadicLocalSourceAtom e q d p a t w i ≤ a / (p : ℝ) ^ i := by
      simp only [nativeDyadicLocalSourceAtom, alpogeNativeSiteCut, Complex.ofReal_re, Nat.cast_pow]
      exact max_le (sub_le_self _ (hw _ hphi)) (div_nonneg ha (pow_nonneg (Nat.cast_nonneg _) _))
    calc
      _ ≤ 2 * Real.log p * (a / (p : ℝ) ^ i) :=
        mul_le_mul_of_nonneg_left hatom (mul_nonneg (by norm_num) (Real.log_natCast_nonneg _))
      _ = (2 * a) * (Real.log p / (p : ℝ) ^ i) := by ring
      _ ≤ (2 * a) * (16 * X ^ (-(5 / 8) : ℝ) * baseWeight p * powerWeight i) :=
        mul_le_mul_of_nonneg_left (log_over_power_le p i hpP h3 X hX hXpow.le)
          (mul_nonneg (by norm_num) ha)
      _ = _ := by dsimp only [A]; ring
  calc
    nativeDyadicHigherOddTail e q d N X a t w mask ≤
        ∑ p ∈ P, ∑ i ∈ I p, (A * baseWeight p) * powerWeight i :=
      Finset.sum_le_sum fun p hp => Finset.sum_le_sum (hrow p hp)
    _ ≤ ∑ p ∈ P, (A * baseWeight p) * (∑' i, powerWeight i) := by
      apply Finset.sum_le_sum
      intro p _
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (powerWeight_summable.sum_le_tsum (I p) (fun i _ => powerWeight_nonnegative i))
        (mul_nonneg hA (baseWeight_nonnegative p))
    _ = (A * (∑' i, powerWeight i)) * ∑ p ∈ P, baseWeight p := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    _ ≤ (A * (∑' i, powerWeight i)) * ∑' p, baseWeight p :=
      mul_le_mul_of_nonneg_left
        (baseWeight_summable.sum_le_tsum P (fun p _ => baseWeight_nonnegative p))
        (mul_nonneg hA hW)
    _ = _ := by dsimp only [A, nativeDyadicHigherPowerConstant]; ring

/-- Sum the original masks on every top, lift and translated profile. The
    same positive projection divisor produces exactly one factor four. Taking
    X = x + 1 uses the existing height condition a(t)/b ≤ x+1. -/
theorem nativeDyadicHigherOddTail_normalized_le (e q d N m : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hhost : Formalism.FrobeniusOrbits.HostHyp q d)
    (TT T2 : Finset (AlpogeNativeDyadicH e)) (hTT : TT.Nonempty) (hT2 : T2.Nonempty)
    (hm : 0 < m) (b X : ℝ) (hb : 0 < b) (hX : 0 < X)
    (a : AlpogeNativeDyadicH e → ℝ) (ha : ∀ t ∈ TT, 0 ≤ a t)
    (hheight : ∀ t ∈ TT, a t / b ≤ X)
    (w : AlpogeNativeDyadicH e → Fin m → AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (hw : ∀ u j z, alpogeNativeInPhi z → 0 ≤ w u j z)
    (mask : AlpogeNativeDyadicH e → AlpogeNativeDyadicH e → Fin m → ℕ → ℕ → Prop) :
    ((1 / (Fintype.card (⊤ : AddSubgroup (AlpogeNativeDyadicH e)) : ℝ)) *
      ∑ u : (⊤ : AddSubgroup (AlpogeNativeDyadicH e)), ∑ t ∈ TT, ∑ j : Fin m,
        nativeDyadicHigherOddTail e q d N X (a t) t (w u j) (mask u t j)) /
      alpogeNativeProjectionDivisor TT T2 m b ≤
        4 * X ^ (3 / 8 : ℝ) * nativeDyadicHigherPowerConstant / alpogeNativeProjectionDensity T2 := by
  let B := 2 * b * X ^ (3 / 8 : ℝ) * nativeDyadicHigherPowerConstant
  have hscale : X * X ^ (-(5 / 8) : ℝ) = X ^ (3 / 8 : ℝ) := by
    calc
      X * X ^ (-(5 / 8) : ℝ) = X ^ (1 : ℝ) * X ^ (-(5 / 8) : ℝ) := by rw [Real.rpow_one]
      _ = X ^ ((1 : ℝ) + -(5 / 8)) := (Real.rpow_add hX _ _).symm
      _ = _ := by norm_num
  have hpoint (u : (⊤ : AddSubgroup (AlpogeNativeDyadicH e))) (t : AlpogeNativeDyadicH e)
      (ht : t ∈ TT) (j : Fin m) : nativeDyadicHigherOddTail e q d N X (a t) t (w u j)
        (mask u t j) ≤ B := by
    have ham := (div_le_iff₀ hb).mp (hheight t ht)
    calc
      _ ≤ 2 * a t * X ^ (-(5 / 8) : ℝ) * nativeDyadicHigherPowerConstant :=
        nativeDyadicHigherOddTail_le e q d N hhost X (a t) hX (ha t ht) t _ (hw u j) _
      _ ≤ 2 * (X * b) * X ^ (-(5 / 8) : ℝ) * nativeDyadicHigherPowerConstant :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ham (by norm_num))
            (Real.rpow_nonneg hX.le _)) nativeDyadicHigherPowerConstant_nonneg
      _ = (2 * b * (X * X ^ (-(5 / 8) : ℝ))) * nativeDyadicHigherPowerConstant := by ring
      _ = B := by rw [hscale]
  have hsum :
      (∑ u : (⊤ : AddSubgroup (AlpogeNativeDyadicH e)), ∑ t ∈ TT, ∑ j : Fin m,
        nativeDyadicHigherOddTail e q d N X (a t) t (w u j) (mask u t j)) ≤
      ∑ _u : (⊤ : AddSubgroup (AlpogeNativeDyadicH e)), ∑ _t ∈ TT, ∑ _j : Fin m, B :=
    Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun t ht =>
      Finset.sum_le_sum fun j _ => hpoint u t ht j
  have hu : 0 < (Fintype.card (⊤ : AddSubgroup (AlpogeNativeDyadicH e)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hQ := alpogeNativeProjectionDivisor_pos TT T2 hTT hT2 m hm b hb
  have ht : (0 : ℝ) < TT.card := by exact_mod_cast hTT.card_pos
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hDelta : 0 < alpogeNativeProjectionDensity T2 := by
    unfold alpogeNativeProjectionDensity
    exact div_pos (by exact_mod_cast hT2.card_pos) (by exact_mod_cast Fintype.card_pos)
  refine (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (one_div_nonneg.mpr hu.le))
    hQ.le).trans_eq ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  dsimp only [B, alpogeNativeProjectionDivisor]
  field_simp [hu.ne', ht.ne', hm'.ne', hb.ne', hDelta.ne']
  ring

end RHLean.Analysis.AlpogeThin
end

import RHLean.Analysis.AlpogeNativeRootDiscriminantBounds
import RHLean.Analysis.AlpogeNativeRootDiscriminantDifferent
import RHLean.Analysis.AlpogeThin.NativeDyadicHostRamifiedPrimes

/-!
# The original root-discriminant bounds on the SAME native raw host

The root discriminant is computed from the actual cyclotomic different and
from the kernel of the constructed Artin map. The original finite weighted
kernel-density estimates then give all three HostDer root-discriminant
bounds. The lower d-term is supplied by the actual CRT d-inertia unit;
no discriminant bound or positive density premise is assumed.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`InertiaGaloisSymmetry/DvdDiscrOfInertia.lean`,
`Rd.{log_rd_eq,rho_d,rho_q}` and `Der.{rd_ge,rd_le,rd_sq_ge}`.
The source archive/mirror states no license; attribution is retained without
assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField IntermediateField Ideal
open scoped Pointwise

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits NativeRootDiscriminant

namespace NativeHostRootDiscriminant

theorem hcl_eq_one {e : ℕ} {v : (ZMod (2 ^ (e + 2)))ˣ} (h : hcl e v = 1) : v = 1 ∨ v = -1 := by
  unfold hcl at h
  rw [QuotientGroup.eq_one_iff] at h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← hk, ← two_mul, zpow_mul]
    simp
  · right
    rw [← hk, zpow_add, zpow_mul]
    simp

variable {φ : Frame} (H : HostRaw φ)

private theorem neZeroN : NeZero H.condN :=
  ⟨by have := H.QS_pos; have := H.hyp.1.pos; have := H.hyp.2.1.pos; positivity⟩

attribute [local instance] neZeroN

theorem log_rd_eq : Real.log H.rd = SS H.art.ker := by
  have : NeZero (H.condN : ℚ) := ⟨by exact_mod_cast (NeZero.ne H.condN)⟩
  have : IsCyclotomicExtension {H.condN} ℚ (CyclotomicField H.condN ℚ) :=
    CyclotomicField.isCyclotomicExtension H.condN ℚ
  let : Algebra H.E (CyclotomicField H.condN ℚ) := H.cycEmb.toRingHom.toAlgebra
  have h1 := log_rd H.cycZeta_prim H.E H.art.ker (fun σ u hσ => by
    have h2 := H.art_spec u σ hσ
    rw [MonoidHom.mem_ker, ← H.gal.symm.map_eq_one_iff]
    constructor
    · intro h3
      exact AlgEquiv.ext fun x => H.cycEmb.injective ((h2 x).trans (h3 x))
    · intro h3 x
      rw [h3] at h2
      exact (h2 x).symm)
  have h0 : (0 : ℝ) < |(discr H.E : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero H.E))
  rw [HostRaw.rd, Real.log_rpow h0, one_div_mul_eq_div, h1, SS, ← abel]

theorem rd_pos : 0 < H.rd := by
  unfold Formalism.HC.HostRaw.rd
  apply Real.rpow_pos_of_pos
  apply abs_pos.2
  exact_mod_cast NumberField.discr_ne_zero H.E

theorem two_dvd : 2 ^ (φ.e + 2) ∣ H.condN := (H.tower_dvd.mul_right _).mul_right _

theorem hH_art (u : (ZMod H.condN)ˣ) : φ.hH (H.art u).2 = hcl φ.e (ZMod.unitsMap (two_dvd H) u) := by
  apply H.art_h
  show (ZMod.castHom (two_dvd H) (ZMod (2 ^ (φ.e + 2)))) (u : ZMod H.condN) = _
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

private theorem q_mul_d_ne_zero : H.q * H.d ≠ 0 :=
  Nat.mul_ne_zero H.hyp.1.ne_zero H.hyp.2.1.ne_zero

theorem div_d : H.condN / H.d = H.QS * H.q := by
  show H.QS * H.q * H.d / H.d = H.QS * H.q
  exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (right_ne_zero_of_mul (q_mul_d_ne_zero H)))

theorem div_q : H.condN / H.q = H.QS * H.d := by
  show H.QS * H.q * H.d / H.q = H.QS * H.d
  rw [show H.QS * H.q * H.d = H.QS * H.d * H.q by ring]
  exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (left_ne_zero_of_mul (q_mul_d_ne_zero H)))

theorem q_ne_d : H.q ≠ H.d := by
  intro h
  have h1 := H.hyp.2.2.1
  have h2 := H.hyp.2.2.2.1
  rw [h] at h1
  omega

theorem rho_d : rho H.art.ker (H.condN / H.d) ≤ 1 / 2 := by
  rw [div_d]
  refine rho_le_half _ (dvd_mul_right _ _) fun u hu v hv h1 h2 => ?_
  rw [MonoidHom.mem_ker] at h1 h2 ⊢
  rw [map_mul, (H.art_d u (mem_KK.mp hu)).resolve_left h1, (H.art_d v (mem_KK.mp hv)).resolve_left h2]
  exact Prod.ext (show ((1, -1) : G0) * (1, -1) = 1 by decide) (mul_one _)

theorem rho_q : rho H.art.ker (H.condN / H.q) ≤ 1 / 2 := by
  rw [div_q]
  have : Fact H.q.Prime := ⟨H.hyp.1⟩
  have hf : H.QS * H.d ∣ H.condN := ⟨H.q, mul_right_comm _ _ _⟩
  have hq : H.q ∣ H.condN := (dvd_mul_left _ _).mul_right _
  have hc : Nat.Coprime (H.QS * H.d) H.q := Nat.Coprime.mul_left H.QS_coprime.coprime_mul_right_right
    ((Nat.coprime_primes H.hyp.2.1 H.hyp.1).mpr (q_ne_d H).symm)
  have hcyc : IsCyclic (ZMod.unitsMap hf).ker := by
    refine isCyclic_of_injective ((ZMod.unitsMap hq).comp (ZMod.unitsMap hf).ker.subtype) ?_
    rw [injective_iff_map_eq_one]
    rintro ⟨u, hu⟩ h1
    have h2 := (Nat.modEq_and_modEq_iff_modEq_mul hc).mp ⟨(mem_ker_iff hf u).mp hu, (mem_ker_iff hq u).mp h1⟩
    rw [mul_right_comm, ← mem_ker_iff dvd_rfl, ZMod.unitsMap_self, MonoidHom.mem_ker, MonoidHom.id_apply] at h2
    exact Subtype.ext h2
  obtain ⟨⟨g, hg⟩, hgen⟩ := hcyc.exists_generator
  have hg2 := H.art_q g ((mem_ker_iff hf g).mp hg)
  have key : ∀ u ∈ KK H.condN (H.QS * H.d), H.art u ≠ 1 → H.art u = H.art g := by
    intro u hu h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨u, (mem_ker_iff hf u).mpr (mem_KK.mp hu)⟩)
    have h2 : g ^ k = u := congrArg Subtype.val hk
    rw [← h2, map_zpow] at h1 ⊢
    obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
    · rw [zpow_mul, zpow_ofNat, hg2, one_zpow] at h1
      exact absurd rfl h1
    · rw [zpow_add, zpow_mul, zpow_ofNat, hg2, one_zpow, one_mul, zpow_one]
  refine rho_le_half _ hf fun u hu v hv h1 h2 => ?_
  rw [MonoidHom.mem_ker] at h1 h2 ⊢
  rw [map_mul, key u hu h1, key v hv h2, ← sq, hg2]

end NativeHostRootDiscriminant

open NativeHostRootDiscriminant

/-- The original lower root-discriminant bound for the actual field. -/
theorem nativeDyadicHostRaw_rd_ge
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) * Real.sqrt d ≤
      (nativeDyadicHostRaw e q d he hH).rd := by
  let H := nativeDyadicHostRaw e q d he hH
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  have hd2 : d ≠ 2 := by omega
  have hqd : q ≠ d := by omega
  have hd4 : d % 4 = 3 := by omega
  have hrho : 1 / 2 ≤ rho H.art.ker (H.condN / H.d) := by
    rw [div_d]
    apply half_le_rho H.art.ker (dvd_mul_right _ _)
    obtain ⟨u, hu, hArt⟩ := nativeDyadicArt_exists_iod e q d hd2 hqd hd4
    refine ⟨u, mem_KK.mpr hu, ?_⟩
    rw [MonoidHom.mem_ker]
    intro h
    have hsign := congrArg (fun g : (nativeDyadicFrame e).GG => g.1.2)
      (hArt.symm.trans h)
    change (-1 : ℤˣ) = 1 at hsign
    exact (by decide : (-1 : ℤˣ) ≠ 1) hsign
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  have h1 := le_SS H.art.ker (two_dvd H) H.hyp.2.1 (dvd_mul_left _ _)
    (by have := H.hyp.2.2.2.1; omega)
    (fun u hu => hcl_eq_one (by
      rw [← hH_art, MonoidHom.mem_ker.mp hu]
      exact map_one _)) hrho
  change (2 : ℝ) ^ (((nativeDyadicFrame e).e : ℝ) + 1 -
    (2 : ℝ) ^ (-((nativeDyadicFrame e).e : ℝ))) * Real.sqrt H.d ≤ H.rd
  rw [← Real.log_le_log_iff (by positivity) (rd_pos H), log_rd_eq,
    Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num),
    Real.log_sqrt hd.le, Real.rpow_neg (by norm_num), Real.rpow_natCast, ← one_div]
  exact h1

/-- The original upper root-discriminant bound with the actual dyadic QS. -/
theorem nativeDyadicHostRaw_rd_le
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    (nativeDyadicHostRaw e q d he hH).rd ≤
      ((2 ^ (e + 2) : ℕ) : ℝ) / 2 * Real.sqrt ((q : ℝ) * d) := by
  let H := nativeDyadicHostRaw e q d he hH
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  have hq : (0 : ℝ) < H.q := by exact_mod_cast H.hyp.1.pos
  have hS : (0 : ℝ) < H.QS := by exact_mod_cast H.QS_pos
  have h1 := SS_le H.art.ker ((dvd_pow_self 2 (by omega)).trans (two_dvd H))
    H.hyp.1 H.hyp.2.1 ((dvd_mul_left _ _).mul_right _) (dvd_mul_left _ _)
    (by have := H.hyp.2.2.1; omega) (by have := H.hyp.2.2.2.1; omega)
    (q_ne_d H) (rho_q H) (rho_d H)
  have hN : Real.log (H.condN : ℝ) = Real.log H.QS + Real.log H.q + Real.log H.d := by
    rw [Nat.cast_mul, Nat.cast_mul, Real.log_mul (by positivity) hd.ne',
      Real.log_mul hS.ne' hq.ne']
  rw [hN] at h1
  change H.rd ≤ (H.QS : ℝ) / 2 * Real.sqrt ((H.q : ℝ) * H.d)
  rw [← Real.log_le_log_iff (rd_pos H) (by positivity), log_rd_eq,
    Real.log_mul (by positivity) (by positivity), Real.log_div hS.ne' (by norm_num),
    Real.log_sqrt (by positivity), Real.log_mul hq.ne' hd.ne']
  linarith

/-- The actual field degree is bounded by the square of its root discriminant. -/
theorem nativeDyadicHostRaw_rd_sq_ge
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    (4 * (nativeDyadicFrame e).ord : ℝ) ≤
      (nativeDyadicHostRaw e q d he hH).rd ^ 2 := by
  let H := nativeDyadicHostRaw e q d he hH
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  have hq2 : q ≠ 2 := by omega
  have hd2 : d ≠ 2 := by omega
  have hqd : q ≠ d := by omega
  have hsurj : Function.Surjective H.art := nativeDyadicArt_surjective e q d hq2 hd2 hqd
  have h1 := log_index_le H.art.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
    (nativeDyadicFrame e).natCard_GG] at h1
  have h0 : (0 : ℝ) < (nativeDyadicFrame e).ord := by
    exact_mod_cast (nativeDyadicFrame e).ord_pos
  rw [← Real.log_le_log_iff (by positivity) (pow_pos (rd_pos H) 2),
    Real.log_pow, log_rd_eq]
  exact_mod_cast h1

end RHLean.Analysis.AlpogeThin

end

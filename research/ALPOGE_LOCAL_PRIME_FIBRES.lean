import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib

/-! Finite LOCALITY2 on the three CRT inertia cosets. The literal principal
channel is identical in the two ledgers. Only nonprincipal characters enter
their difference. No conductor, height, or infinite-tail estimate is assumed. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace RHLean.Analysis

def localityOffPrincipal {G : Type*} [AddCommGroup G] [Fintype G] (x g : G) : ℂ := by
  classical
  exact ∑ χ ∈ (Finset.univ : Finset (AddChar G ℂ)).erase 0, χ (x - g)

theorem localityOffPrincipal_eq {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (x g : G) : localityOffPrincipal x g =
    (if x = g then (Fintype.card G : ℂ) else 0) - 1 := by
  classical
  apply (eq_sub_iff_add_eq).2
  simpa only [localityOffPrincipal, AddChar.zero_apply, AddChar.sum_apply_eq_ite,
    sub_eq_zero] using Finset.sum_erase_add (Finset.univ : Finset (AddChar G ℂ))
      (fun χ : AddChar G ℂ => χ (x - g)) (Finset.mem_univ (0 : AddChar G ℂ))

variable {H : Type*} [AddCommGroup H] [Fintype H]

def localityMean (v : ZMod 2 × H → ℂ) : ℂ := (∑ s, v s) / Fintype.card (ZMod 2 × H)

def localityFibre {I : Type*} [Fintype I] (f : I → ZMod 2 × (ZMod 2 × H))
    (v : ZMod 2 × H → ℂ) : ℂ :=
  (∑ s, v s * ((∑ j, localityOffPrincipal (f j) (1, s)) / Fintype.card I)) /
    Fintype.card (ZMod 2 × H)

private theorem locality_miss {I : Type*} [Fintype I] [Nonempty I]
    (f : I → ZMod 2 × (ZMod 2 × H)) (v : ZMod 2 × H → ℂ)
    (hm : ∀ j s, f j ≠ (1, s)) : localityFibre f v = -localityMean v := by
  classical
  have hI : (Fintype.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h (s : ZMod 2 × H) : (∑ j, localityOffPrincipal (f j) (1, s)) /
      (Fintype.card I : ℂ) = -1 := by
    simp [localityOffPrincipal_eq, hm, nsmul_eq_mul, hI]
  simp only [localityFibre, h, mul_neg, mul_one, Finset.sum_neg_distrib, neg_div, localityMean]

theorem locality_two (i : ℕ) (v : ZMod 2 × H → ℂ) :
    localityFibre (fun h : H => ((0 : ZMod 2), (i : ZMod 2), h)) v = -localityMean v := by
  apply locality_miss
  intro h s he
  exact (zero_ne_one : (0 : ZMod 2) ≠ 1) (congrArg Prod.fst he)

theorem locality_q (i : ℕ) (Q : H) (v : ZMod 2 × H → ℂ) :
    localityFibre (fun b : ZMod 2 => ((0 : ZMod 2), b, i • Q)) v = -localityMean v := by
  apply locality_miss
  intro b s he
  exact (zero_ne_one : (0 : ZMod 2) ≠ 1) (congrArg Prod.fst he)

theorem locality_d (i : ℕ) (D : H) (v : ZMod 2 × H → ℂ) :
    localityFibre (fun b : ZMod 2 => (b, (i : ZMod 2), i • D)) v =
      v ((i : ZMod 2), i • D) - localityMean v := by
  classical
  let z : ZMod 2 × H := ((i : ZMod 2), i • D)
  have h (s : ZMod 2 × H) : (∑ b : ZMod 2, localityOffPrincipal (b, z) (1, s)) /
      (Fintype.card (ZMod 2) : ℂ) = (if z = s then (Fintype.card (ZMod 2 × H) : ℂ) else 0) - 1 := by
    by_cases hz : z = s <;>
      simp [localityOffPrincipal_eq, Prod.mk.injEq, Finset.sum_sub_distrib, hz,
        Fintype.card_prod, ZMod.card, nsmul_eq_mul] <;> ring
  change (∑ s, v s * ((∑ b : ZMod 2, localityOffPrincipal (b, z) (1, s)) /
    (Fintype.card (ZMod 2) : ℂ))) / _ = v z - localityMean v
  have hc : (Fintype.card (ZMod 2 × H) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [h, mul_sub, mul_one, Finset.sum_sub_distrib, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, localityMean, sub_div, mul_div_cancel_right₀ _ hc]

/-- The physical dyadic unit class, before choosing a discrete-log coordinate. -/
abbrev LocalityDyadic (e : ℕ) := Additive (((ZMod (2 ^ (e + 2)))ˣ) ⧸
  Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ))

def localityClass (e p : ℕ) (hp : p.Coprime (2 ^ (e + 2))) : LocalityDyadic e :=
  Additive.ofMul (QuotientGroup.mk (ZMod.unitOfCoprime p hp))

/-- The finite prime-power summand for the specified CRT cosets, with the
actual two odd prime classes. Weights may vary by prime, exponent and site.
This statement does not identify L-derivatives or bound the geometric sum. -/
theorem locality_primePower (e q d i : ℕ) (hq : q.Prime) (hd : d.Prime) (hi : i ≠ 0)
    (hQ : q.Coprime (2 ^ (e + 2))) (hD : d.Coprime (2 ^ (e + 2)))
    [Fintype (LocalityDyadic e)] (v₂ vq vd : ZMod 2 × LocalityDyadic e → ℂ) :
    (Λ (2 ^ i) : ℂ) * localityFibre (fun h : LocalityDyadic e => ((0 : ZMod 2), (i : ZMod 2), h)) v₂ +
    (Λ (q ^ i) : ℂ) * localityFibre (fun b : ZMod 2 => ((0 : ZMod 2), b, i • localityClass e q hQ)) vq +
    (Λ (d ^ i) : ℂ) * localityFibre (fun b : ZMod 2 => (b, (i : ZMod 2), i • localityClass e d hD)) vd =
      -(Real.log 2 : ℂ) * localityMean v₂ - (Real.log q : ℂ) * localityMean vq +
      (Real.log d : ℂ) * (vd ((i : ZMod 2), i • localityClass e d hD) - localityMean vd) := by
  rw [locality_two, locality_q, locality_d]
  simp only [ArithmeticFunction.vonMangoldt_apply_pow hi, ArithmeticFunction.vonMangoldt_apply_prime
    Nat.prime_two, ArithmeticFunction.vonMangoldt_apply_prime hq, ArithmeticFunction.vonMangoldt_apply_prime hd,
    Nat.cast_ofNat]
  ring

/-- Sharp movement of the distinguished point relative to the full mean. -/
theorem locality_width {S : Type*} [Fintype S] [DecidableEq S] (z : S) (v : S → ℝ)
    (w : ℝ) (hw : ∀ s, |v z - v s| ≤ w) :
    |v z - (∑ s, v s) / Fintype.card S| ≤
      (((Finset.univ.erase z).card : ℝ) / Fintype.card S) * w := by
  classical
  let _ : Nonempty S := ⟨z⟩
  have hc : (0 : ℝ) < Fintype.card S := Nat.cast_pos.mpr Fintype.card_pos
  have he := Finset.sum_erase_add (Finset.univ : Finset S) (fun s => v z - v s) (Finset.mem_univ z)
  have hr : (∑ s ∈ Finset.univ.erase z, (v z - v s)) = (Fintype.card S : ℝ) * v z - ∑ s, v s := by
    simpa [Finset.sum_sub_distrib, nsmul_eq_mul] using he
  have ha : |∑ s ∈ Finset.univ.erase z, (v z - v s)| ≤ ((Finset.univ.erase z).card : ℝ) * w := by
    calc
      _ ≤ ∑ s ∈ Finset.univ.erase z, |v z - v s| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _s ∈ Finset.univ.erase z, w := Finset.sum_le_sum fun s _ => hw s
      _ = _ := by simp [nsmul_eq_mul]
  rw [hr] at ha
  have hid : v z - (∑ s, v s) / Fintype.card S =
      ((Fintype.card S : ℝ) * v z - ∑ s, v s) / Fintype.card S := by field_simp
  rw [hid, abs_div, abs_of_pos hc]
  simpa [div_mul_eq_mul_div] using div_le_div_of_nonneg_right ha hc.le

/-- Positive two-level weights attain the movement factor on every d-fibre. -/
theorem locality_dSpike [DecidableEq H] (i : ℕ) (D : H) :
    localityFibre (fun b : ZMod 2 => (b, (i : ZMod 2), i • D))
      (fun s => (1 : ℂ) + if ((i : ZMod 2), i • D) = s then 1 else 0) =
        1 - 1 / (Fintype.card (ZMod 2 × H) : ℂ) := by
  classical
  have hc : (Fintype.card (ZMod 2 × H) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [locality_d]
  simp only [if_pos rfl, localityMean, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, Finset.sum_ite_eq, Finset.mem_univ, ite_true, add_div, div_self hc] <;> ring

end RHLean.Analysis

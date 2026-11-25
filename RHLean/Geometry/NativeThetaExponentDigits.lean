import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.NatCard
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
# Residue and coarse indices of homogeneous symbols

Quotient and remainder preserve every exponent on a homogeneous slice.
The p-adic cost of a block factorial splits exactly into its residue,
block and coarse factorials. This is the valuation part of the digit
split in Lemma5aAt at community revision 251c7b05.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace RHLean.Geometry.NativeTheta.ExponentDigits

/-- Exponents of all degree-`d` monomials, including repeated variables. -/
abbrev DegreeIndex (ι : Type*) [Fintype ι] (d : ℕ) :=
  {a : ι → ℕ // ∑ i, a i = d}

/-- A residue class together with all its coarse exponents on the same slice. -/
abbrev DigitIndex (ι : Type*) [Fintype ι] (P d : ℕ) :=
  {z : (ι → Fin P) × (ι → ℕ) //
    (∑ i, (z.1 i : ℕ)) + P * (∑ i, z.2 i) = d}

private theorem decode_mod (P a b : ℕ) (ha : a < P) :
    (a + P * b) % P = a := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

private theorem decode_div (P a b : ℕ) (hP : 0 < P) (ha : a < P) :
    (a + P * b) / P = b := by
  rw [Nat.add_comm, Nat.mul_add_div hP, Nat.div_eq_of_lt ha, Nat.add_zero]

/-- Bijection on the entire degree slice. Selecting a residue alone would
discard the second component. -/
def degreeDigitEquiv (ι : Type*) [Fintype ι] (P d : ℕ) (hP : 0 < P) :
    DegreeIndex ι d ≃ DigitIndex ι P d where
  toFun a := ⟨(fun i => ⟨a.1 i % P, Nat.mod_lt _ hP⟩, fun i => a.1 i / P), by
    calc
      (∑ i, a.1 i % P) + P * (∑ i, a.1 i / P) = ∑ i, (a.1 i % P + P * (a.1 i / P)) := by
        rw [Finset.mul_sum, Finset.sum_add_distrib]
      _ = d := by simpa only [Nat.mod_add_div] using a.2⟩
  invFun z := ⟨fun i => (z.1.1 i : ℕ) + P * z.1.2 i, by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    exact z.2⟩
  left_inv a := Subtype.ext (funext fun i => Nat.mod_add_div _ _)
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact Fin.ext (decode_mod P _ _ (z.1.1 i).isLt)
    · funext i
      exact decode_div P _ _ hP (z.1.1 i).isLt

/-- Stars and bars with both exponent digits retained. -/
theorem card_digitIndex (ι : Type*) [Fintype ι] (P d : ℕ) (hP : 0 < P) :
    Nat.card (DigitIndex ι P d) = (Fintype.card ι + d - 1).choose d := by
  calc
    _ = Nat.card (Sym ι d) := Nat.card_congr
      ((degreeDigitEquiv ι P d hP).symm.trans (Sym.equivNatSumOfFintype ι d).symm)
    _ = _ := by rw [Sym.natCard_sym_eq_multichoose, Nat.multichoose_eq, Nat.card_eq_fintype_card]

/-- At fixed residue and total degree |ρ|+P k, the entire space of coarse
degree-k monomials survives. -/
theorem card_digitFiber (ι : Type*) [Fintype ι] (P k : ℕ) (hP : 0 < P) (ρ : ι → Fin P) :
    Nat.card {β : ι → ℕ // (∑ i, (ρ i : ℕ)) + P * (∑ i, β i) = (∑ i, (ρ i : ℕ)) + P * k} =
      (Fintype.card ι + k - 1).choose k := by
  let e : {β : ι → ℕ // (∑ i, (ρ i : ℕ)) + P * (∑ i, β i) = (∑ i, (ρ i : ℕ)) + P * k} ≃
      DegreeIndex ι k :=
    { toFun := fun b => ⟨b.1, Nat.eq_of_mul_eq_mul_left hP (Nat.add_left_cancel b.2)⟩
      invFun := fun b => ⟨b.1, by rw [b.2]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr (e.trans (degreeDigitEquiv ι P k hP))).trans (card_digitIndex ι P k hP)

/-- Read the coefficient at the full exponent encoded by a residue and a coarse index. -/
def digitCoefficient {ι R : Type*} [Fintype ι] [CommSemiring R] {P d : ℕ} (hP : 0 < P)
    (z : DigitIndex ι P d) (f : MvPolynomial ι R) : R :=
  f.coeff (Finsupp.equivFunOnFinite.symm ((degreeDigitEquiv ι P d hP).symm z).1)

theorem digitCoefficient_encode {ι R : Type*} [Fintype ι] [CommSemiring R] {P d : ℕ}
    (hP : 0 < P) (a : DegreeIndex ι d) (f : MvPolynomial ι R) :
    digitCoefficient hP (degreeDigitEquiv ι P d hP a) f =
      f.coeff (Finsupp.equivFunOnFinite.symm a.1) := by
  simp only [digitCoefficient, Equiv.symm_apply_apply]

private theorem factorial_div_recurrence {p : ℕ} [Fact p.Prime] (n : ℕ) :
    padicValNat p n.factorial = padicValNat p (n / p).factorial + n / p :=
  (padicValNat_mul_div_factorial (p := p) n).symm.trans (padicValNat_factorial_mul (n / p))

/-- The exact valuation of the digit-split factorial in one coordinate. -/
theorem factorial_digit_valuation (p : ℕ) [Fact p.Prime] (g ρ β : ℕ) (hρ : ρ < p ^ g) :
    padicValNat p (ρ + p ^ g * β).factorial =
      padicValNat p ρ.factorial + β * padicValNat p (p ^ g).factorial +
        padicValNat p β.factorial := by
  have hp := (Fact.out : p.Prime).pos
  induction g generalizing ρ with
  | zero =>
    have hz : ρ = 0 := by simpa only [pow_zero, Nat.lt_one_iff] using hρ
    simp [hz]
  | succ g ih =>
    have hsmall : ρ / p < p ^ g := (Nat.div_lt_iff_lt_mul hp).mpr (by simpa only [pow_succ] using hρ)
    have hdiv : (ρ + p ^ (g + 1) * β) / p = ρ / p + p ^ g * β := by
      rw [pow_succ', Nat.mul_assoc, Nat.add_comm ρ, Nat.mul_add_div hp, Nat.add_comm]
    have hpower : padicValNat p (p ^ (g + 1)).factorial =
        padicValNat p (p ^ g).factorial + p ^ g := by
      rw [pow_succ', padicValNat_factorial_mul]
    calc
      _ = padicValNat p ((ρ + p ^ (g + 1) * β) / p).factorial + (ρ + p ^ (g + 1) * β) / p :=
        factorial_div_recurrence _
      _ = _ := by
        rw [hdiv, ih (ρ / p) hsmall, factorial_div_recurrence (p := p) ρ, hpower]
        ring

/-- The quotient of the factorial by the three extracted factors is a p-adic unit. -/
theorem factorial_digit_unit (p : ℕ) [Fact p.Prime] (g ρ β : ℕ) (hρ : ρ < p ^ g) :
    let γ : ℚ := ((ρ + p ^ g * β).factorial : ℚ) /
      ((ρ.factorial : ℚ) * ((p ^ g).factorial : ℚ) ^ β * (β.factorial : ℚ))
    γ ≠ 0 ∧ padicValRat p γ = 0 := by
  dsimp only
  have hpos (k : ℕ) : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hp := pow_ne_zero β (hpos (p ^ g))
  have hm := mul_ne_zero (hpos ρ) hp
  have hden := mul_ne_zero hm (hpos β)
  refine ⟨div_ne_zero (hpos _) hden, ?_⟩
  rw [padicValRat.div (hpos _) hden, padicValRat.mul hm (hpos β),
    padicValRat.mul (hpos ρ) hp, padicValRat.pow]
  simp only [padicValRat.of_nat]
  rw [factorial_digit_valuation p g ρ β hρ]
  push_cast
  ring

end RHLean.Geometry.NativeTheta.ExponentDigits

end

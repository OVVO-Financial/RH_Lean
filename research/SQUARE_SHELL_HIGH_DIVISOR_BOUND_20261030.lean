import Mathlib
import «research.SQUARE_SHELL_COMPENSATED_SYNTHESIS_20261030»

/-!
# Independent physical high-divisor energy

For the actual shell Mobius divisibility profile F_R(h), prove an explicit
finite estimate on an entire dyadic divisor band, not a conjectural
signed-cancellation input. In the range 3<=H and 1<=D<=H:

 D * sum_(H<=R<2H) sum_(D<=h<2D) F_R(h)^2 <= 36*H^3.

This is useful for D above sqrt(H); the primitive small-divisor channel
remains unpaid. The compensated original Euler source obeys the same bound
by the source-level crosswalk. No packet activation is omitted.
-/
noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators
namespace RHLean.Proof
attribute [local instance] Classical.propDecidable

private lemma synthesisMultiples_card_mul_le
    (a b h : ℕ) (hab : a ≤ b) (hh : 0 < h) :
    ((Finset.Icc a b).filter (fun n => h ∣ n)).card * h ≤ b-a+2*h := by
  let S := (Finset.Icc a b).filter (fun n => h ∣ n)
  have hinj : Set.InjOn (fun n : ℕ => n/h) (S : Set ℕ) := by
    intro n hn m hm heq
    have hnD : h ∣ n := (Finset.mem_filter.mp hn).2
    have hmD : h ∣ m := (Finset.mem_filter.mp hm).2
    calc
      n = h*(n/h) := (Nat.mul_div_cancel' hnD).symm
      _ = h*(m/h) := by rw [heq]
      _ = m := Nat.mul_div_cancel' hmD
  have hsub : S.image (fun n => n/h) ⊆ Finset.Icc (a/h) (b/h) := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨n,hn,rfl⟩
    have hnB := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    exact Finset.mem_Icc.mpr ⟨Nat.div_le_div_right hnB.1, Nat.div_le_div_right hnB.2⟩
  have hcard : S.card ≤ (Finset.Icc (a/h) (b/h)).card := by
    rw [← Finset.card_image_iff.mpr hinj]
    exact Finset.card_le_card hsub
  have hquot : a/h ≤ b/h := Nat.div_le_div_right hab
  have hcard2 : S.card ≤ b/h+1-a/h := by simpa [Nat.card_Icc] using hcard
  have htimes := Nat.mul_le_mul_right h hcard2
  have hqa := Nat.mod_add_div a h
  have hqb := Nat.mod_add_div b h
  have hra := Nat.mod_lt a hh
  have hrb := Nat.mod_lt b hh
  have hdiff : b/h+1-a/h+a/h = b/h+1 := Nat.sub_add_cancel (by omega)
  have hdiff2 : b-a+a = b := Nat.sub_add_cancel hab
  change S.card*h ≤ b-a+2*h
  nlinarith

/-- A source-exact pointwise divisor budget. This uses scarcity of actual
multiples, not independence of their Mobius signs. -/
theorem synthesisDivisorMobius_abs_mul_le
    (R h : ℕ) (hh : 0 < h) :
    |synthesisDivisorMobiusWindow R h| * (h : ℤ) ≤
      2*(R : ℤ)+2*(h : ℤ) := by
  let S := (Finset.Ico (R*R) ((R+1)*(R+1))).filter (fun n => h ∣ n)
  have hsum : synthesisDivisorMobiusWindow R h = ∑ n ∈ S, (μ n : ℤ) := by
    unfold synthesisDivisorMobiusWindow
    exact (Finset.sum_filter ..).symm
  have hmass : |synthesisDivisorMobiusWindow R h| ≤ (S.card : ℤ) := by
    rw [hsum]
    calc
      |∑ n ∈ S, (μ n : ℤ)| ≤ ∑ n ∈ S, |(μ n : ℤ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ S, (1 : ℤ) := Finset.sum_le_sum (by
        intro n _hn
        exact ArithmeticFunction.abs_moebius_le_one)
      _ = (S.card : ℤ) := by simp
  have hset : Finset.Ico (R*R) ((R+1)*(R+1)) = Finset.Icc (R*R) (R*R+2*R) := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    nlinarith
  have hcardN := synthesisMultiples_card_mul_le (R*R) (R*R+2*R) h (by omega) hh
  have hcard : S.card*h ≤ 2*R+2*h := by
    simpa only [S, hset, Nat.add_sub_cancel_left] using hcardN
  have hcardZ : (S.card : ℤ)*(h : ℤ) ≤ 2*(R : ℤ)+2*(h : ℤ) := by
    exact_mod_cast hcard
  exact (mul_le_mul_of_nonneg_right hmass (by positivity)).trans hcardZ

private lemma synthesisBand_pointwise
    (H D R h : ℕ) (hD : 0 < D) (hDH : D ≤ H)
    (hR : R < 2*H) (hDh : D ≤ h) :
    synthesisDivisorMobiusWindow R h ^ 2 * (D : ℤ)^2 ≤ 36*(H : ℤ)^2 := by
  have hhp : 0 < h := lt_of_lt_of_le hD hDh
  have hb := synthesisDivisorMobius_abs_mul_le R h hhp
  have hdZ : (0 : ℤ) < D := by exact_mod_cast hD
  have hdH : (D : ℤ) ≤ H := by exact_mod_cast hDH
  have hrH : (R : ℤ) < 2*(H : ℤ) := by exact_mod_cast hR
  have hdh : (D : ℤ) ≤ h := by exact_mod_cast hDh
  let A : ℤ := |synthesisDivisorMobiusWindow R h|
  have hA : 0 ≤ A := abs_nonneg _
  have hAD : A*(D : ℤ) ≤ 6*(H : ℤ) := by
    by_cases hsmall : A ≤ 2
    · nlinarith [mul_nonneg (sub_nonneg.mpr hsmall) (le_of_lt hdZ)]
    · have hprod : 0 ≤ (A-2)*((h : ℤ)-(D : ℤ)) :=
        mul_nonneg (by omega) (sub_nonneg.mpr hdh)
      change A*(h : ℤ) ≤ 2*(R : ℤ)+2*(h : ℤ) at hb
      nlinarith
  have hprod : 0 ≤ (6*(H : ℤ)-A*(D : ℤ)) * (6*(H : ℤ)+A*(D : ℤ)) := by
    apply mul_nonneg (sub_nonneg.mpr hAD)
    positivity
  have hsq : A^2 = synthesisDivisorMobiusWindow R h ^ 2 := sq_abs _
  nlinarith

/-- Quantified independent proper-sector energy, valid at every admissible
integer scale. Dividing by D gives 36 H^3/D, not an assumed RH-scale rate. -/
theorem synthesisHighDivisor_energy
    (H D : ℕ) (hD : 0 < D) (hDH : D ≤ H) :
    (∑ R ∈ Finset.Ico H (2*H),
      ∑ h ∈ Finset.Ico D (2*D), synthesisDivisorMobiusWindow R h ^ 2) * (D : ℤ) ≤
        36*(H : ℤ)^3 := by
  have hpoint :
      (∑ R ∈ Finset.Ico H (2*H),
        ∑ h ∈ Finset.Ico D (2*D),
          synthesisDivisorMobiusWindow R h ^ 2 * (D : ℤ)^2) ≤
      ∑ _R ∈ Finset.Ico H (2*H), ∑ _h ∈ Finset.Ico D (2*D), 36*(H : ℤ)^2 := by
    apply Finset.sum_le_sum
    intro R hr
    apply Finset.sum_le_sum
    intro h hh
    exact synthesisBand_pointwise H D R h hD hDH
      (Finset.mem_Ico.mp hr).2 (Finset.mem_Ico.mp hh).1
  have hcountH : (Finset.Ico H (2*H)).card = H := by simp [Nat.card_Ico]; omega
  have hcountD : (Finset.Ico D (2*D)).card = D := by simp [Nat.card_Ico]; omega
  simp only [← Finset.sum_mul] at hpoint
  simp only [Finset.sum_const, nsmul_eq_mul, hcountH, hcountD] at hpoint
  have hdZ : (0 : ℤ) < D := by exact_mod_cast hD
  apply (mul_le_mul_right hdZ).mp
  nlinarith [hpoint]

/-- The same estimate on the corrected ORIGINAL Euler source, including all
its fully and partially admitted pair families and their exact corners. -/
theorem synthesisHighDivisor_correctedEuler_energy
    (H D : ℕ) (hH : 3 ≤ H) (hD : 0 < D) (hDH : D ≤ H) :
    (∑ R ∈ Finset.Ico H (2*H),
      ∑ h ∈ Finset.Ico D (2*D),
        (synthesisDivisorEulerWindow R h - synthesisDivisorCornerWindow R h)^2) * (D : ℤ) ≤
        36*(H : ℤ)^3 := by
  have heq :
      (∑ R ∈ Finset.Ico H (2*H), ∑ h ∈ Finset.Ico D (2*D),
        (synthesisDivisorEulerWindow R h - synthesisDivisorCornerWindow R h)^2) =
      (∑ R ∈ Finset.Ico H (2*H), ∑ h ∈ Finset.Ico D (2*D),
        synthesisDivisorMobiusWindow R h ^ 2) := by
    apply Finset.sum_congr rfl
    intro R hr
    apply Finset.sum_congr rfl
    intro h _hh
    rw [synthesisDivisorEuler_eq_neg_mobius_add_corner R h
      (by have := (Finset.mem_Ico.mp hr).1; omega)]
    ring
  rw [heq]
  exact synthesisHighDivisor_energy H D hD hDH

#print axioms synthesisDivisorMobius_abs_mul_le
#print axioms synthesisHighDivisor_energy
#print axioms synthesisHighDivisor_correctedEuler_energy
end RHLean.Proof

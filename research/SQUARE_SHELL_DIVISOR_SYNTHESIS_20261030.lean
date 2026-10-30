import Mathlib
import «research.EULER_SELF_DUAL_POINTWISE_20261027»

/-! Exact original Euler coefficients on one square shell, with all corner terms.
No source estimate, random signs, or RH hypothesis is assumed. -/
noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators
namespace RHLean.Proof
open ArithmeticFunction RHLean.Analysis.MertensFiniteExtension
attribute [local instance] Classical.propDecidable

def synthesisMobiusTail (R : ℕ) : ArithmeticFunction ℤ :=
  ArithmeticFunction.moebius - eulerSelfDualPrefix R

lemma synthesisMobiusTail_of_lt (R n : ℕ) (hn : n < R) :
    synthesisMobiusTail R n = 0 := by
  have hle : n ≤ R - 1 := by omega
  change (μ n : ℤ) - (if n ≤ R-1 then μ n else 0) = 0
  rw [ite_eq_left hle]
  ring

lemma synthesisMobiusTail_of_ge (R n : ℕ) (hR : 1 ≤ R) (hn : R ≤ n) :
    synthesisMobiusTail R n = μ n := by
  have hnot : ¬ n ≤ R - 1 := by omega
  change (μ n : ℤ) - (if n ≤ R-1 then μ n else 0) = μ n
  rw [ite_eq_right hnot]
  ring

lemma synthesisTailSquare_zero_below (R n : ℕ) (hn : n < R * R) :
    (synthesisMobiusTail R * synthesisMobiusTail R) n = 0 := by
  exact mul_zero_below (synthesisMobiusTail_of_lt R)
    (synthesisMobiusTail_of_lt R) hn

lemma synthesis_zeta_no_proper_divisor
    (F : ArithmeticFunction ℤ) (B n : ℕ)
    (hF : ∀ k < B, F k = 0) (hn : 0 < n) (hupper : n < 2 * B) :
    (F * zetaInt) n = F n := by
  change (F * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) n = F n
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_eq_single n
  · intro d hd hdn
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
    rcases hdvd with ⟨k, hk⟩
    have hdpos : 0 < d := by nlinarith
    have hkpos : 0 < k := by nlinarith
    have hk2 : 2 ≤ k := by
      by_contra hh
      have hk1 : k = 1 := by omega
      simp only [hk1, mul_one] at hk
      exact hdn hk.symm
    have hdk : 2 * d ≤ n := by nlinarith
    exact hF d (by omega)
  · intro hnot
    exact False.elim (hnot (Nat.mem_divisors.mpr ⟨dvd_rfl, ne_of_gt hn⟩))

def synthesisCornerPairs (R : ℕ) : Finset (ℕ × ℕ) :=
  {(R,R), (R,R+1), (R+1,R), (R,R+2), (R+2,R)}

lemma synthesis_tail_pair_corner
    (R n : ℕ) (hR : 3 ≤ R) (_hn : R * R ≤ n)
    (hupper : n < (R+1) * (R+1))
    (p : ℕ × ℕ) (hp : p ∈ n.divisorsAntidiagonal)
    (ha : R ≤ p.1) (hb : R ≤ p.2) :
    p ∈ synthesisCornerPairs R := by
  have hab : p.1 * p.2 = n := (Nat.mem_divisorsAntidiagonal.mp hp).1
  have ha2 : p.1 ≤ R+2 := by
    by_contra hh
    have hprod := Nat.mul_le_mul (show R+3 ≤ p.1 by omega) hb
    nlinarith
  have hb2 : p.2 ≤ R+2 := by
    by_contra hh
    have hprod := Nat.mul_le_mul ha (show R+3 ≤ p.2 by omega)
    nlinarith
  have hedge : p.1 = R ∨ p.2 = R := by
    by_contra hh
    have h1 : R+1 ≤ p.1 := by omega
    have h2 : R+1 ≤ p.2 := by omega
    have hprod := Nat.mul_le_mul h1 h2
    nlinarith
  rcases hedge with h1 | h2
  · have hc : p.2 = R ∨ p.2 = R+1 ∨ p.2 = R+2 := by omega
    rcases hc with h | h | h <;>
      simp [synthesisCornerPairs, Prod.ext_iff, h1, h]
  · have hc : p.1 = R ∨ p.1 = R+1 ∨ p.1 = R+2 := by omega
    rcases hc with h | h | h <;>
      simp [synthesisCornerPairs, Prod.ext_iff, h2, h]

def synthesisCornerCoefficient (R n : ℕ) : ℤ :=
  (if n = R*R then (μ R : ℤ)^2 else 0) +
  (if n = R*(R+1) then 2*(μ R : ℤ)*μ (R+1) else 0) +
  (if n = R*(R+2) then 2*(μ R : ℤ)*μ (R+2) else 0)

lemma synthesisTailSquare_eq_corner
    (R n : ℕ) (hR : 3 ≤ R) (hn : R * R ≤ n)
    (hupper : n < (R+1) * (R+1)) :
    (synthesisMobiusTail R * synthesisMobiusTail R) n =
      synthesisCornerCoefficient R n := by
  let A := n.divisorsAntidiagonal
  let S := synthesisCornerPairs R
  let f : ℕ × ℕ → ℤ := fun p =>
    synthesisMobiusTail R p.1 * synthesisMobiusTail R p.2
  have hn0 : n ≠ 0 := by nlinarith
  have hrestrict : (∑ p ∈ A, f p) = ∑ p ∈ A ∩ S, f p := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro p hp hnot
    by_cases ha : p.1 < R
    · simp [f, synthesisMobiusTail_of_lt R p.1 ha]
    by_cases hb : p.2 < R
    · simp [f, synthesisMobiusTail_of_lt R p.2 hb]
    have hS : p ∈ S := synthesis_tail_pair_corner R n hR hn hupper p hp
      (by omega) (by omega)
    exact False.elim (hnot (Finset.mem_inter.mpr ⟨hp,hS⟩))
  have hfilter : A ∩ S = S.filter (fun p => p ∈ A) := by
    ext p
    simp [and_comm]
  rw [ArithmeticFunction.mul_apply]
  change (∑ p ∈ A, f p) = _
  rw [hrestrict, hfilter, Finset.sum_filter]
  have ht0 := synthesisMobiusTail_of_ge R R (by omega) (by omega)
  have ht1 := synthesisMobiusTail_of_ge R (R+1) (by omega) (by omega)
  have ht2 := synthesisMobiusTail_of_ge R (R+2) (by omega) (by omega)
  simp [S, A, f, synthesisCornerPairs, Nat.mem_divisorsAntidiagonal,
    hn0, ht0, ht1, ht2, Prod.ext_iff,
    synthesisCornerCoefficient, Nat.mul_comm, eq_comm, pow_two]
  split_ifs <;> ring

/-- Source-level identity at EVERY original integer in EVERY square shell. -/
theorem synthesisEulerCoefficient_eq_neg_moebius_add_corner
    (R n : ℕ) (hR : 3 ≤ R) (hn : R*R ≤ n)
    (hupper : n < (R+1)*(R+1)) :
    eulerSelfDualConvolutionCoefficient R n =
      -μ n + synthesisCornerCoefficient R n := by
  have hN := congrArg (fun f : ArithmeticFunction ℤ => f n)
    (newtonLift_eq_moebius_sub_tail (eulerSelfDualPrefix R))
  have hprefix : eulerSelfDualPrefix R n = 0 := by
    have hroot : R ≤ n := by nlinarith
    have hnot : ¬ n ≤ R-1 := by omega
    change (if n ≤ R-1 then (μ n : ℤ) else 0) = 0
    exact ite_eq_right hnot
  have hproper := synthesis_zeta_no_proper_divisor
    (synthesisMobiusTail R * synthesisMobiusTail R) (R*R) n
    (synthesisTailSquare_zero_below R) (by nlinarith) (by nlinarith)
  have hcorner := synthesisTailSquare_eq_corner R n hR hn hupper
  change eulerSelfDualPrefix R n + eulerSelfDualPrefix R n -
      eulerSelfDualConvolutionCoefficient R n =
    μ n - ((synthesisMobiusTail R * synthesisMobiusTail R) * zetaInt) n at hN
  rw [hprefix, hproper, hcorner] at hN
  omega

def synthesisDivisorEulerWindow (R h : ℕ) : ℤ :=
  ∑ n ∈ Finset.Ico (R*R) ((R+1)*(R+1)),
    if h ∣ n then eulerSelfDualConvolutionCoefficient R n else 0

def synthesisDivisorMobiusWindow (R h : ℕ) : ℤ :=
  ∑ n ∈ Finset.Ico (R*R) ((R+1)*(R+1)), if h ∣ n then μ n else 0

def synthesisDivisorCornerWindow (R h : ℕ) : ℤ :=
  ∑ n ∈ Finset.Ico (R*R) ((R+1)*(R+1)),
    if h ∣ n then synthesisCornerCoefficient R n else 0

theorem synthesisDivisorEuler_eq_neg_mobius_add_corner
    (R h : ℕ) (hR : 3 ≤ R) :
    synthesisDivisorEulerWindow R h =
      -synthesisDivisorMobiusWindow R h + synthesisDivisorCornerWindow R h := by
  unfold synthesisDivisorEulerWindow synthesisDivisorMobiusWindow
    synthesisDivisorCornerWindow
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hs := Finset.mem_Ico.mp hn
  by_cases hh : h ∣ n
  · simp only [ite_eq_left hh]
    exact synthesisEulerCoefficient_eq_neg_moebius_add_corner R n hR hs.1 hs.2
  · simp only [ite_eq_right hh, neg_zero, add_zero]

theorem synthesisDivisorMobius_eq_zero_of_not_squarefree
    (R h : ℕ) (hh : ¬ Squarefree h) :
    synthesisDivisorMobiusWindow R h = 0 := by
  unfold synthesisDivisorMobiusWindow
  apply Finset.sum_eq_zero
  intro n _hn
  by_cases hdiv : h ∣ n
  · have hns : ¬ Squarefree n := fun hn => hh (hn.squarefree_of_dvd hdiv)
    have hz : μ n = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns
    simp [hdiv,hz]
  · simp [hdiv]

theorem synthesisSquarefulEuler_eq_corner
    (R h : ℕ) (hR : 3 ≤ R) (hh : ¬ Squarefree h) :
    synthesisDivisorEulerWindow R h = synthesisDivisorCornerWindow R h := by
  rw [synthesisDivisorEuler_eq_neg_mobius_add_corner R h hR,
    synthesisDivisorMobius_eq_zero_of_not_squarefree R h hh]
  ring

#print axioms synthesisEulerCoefficient_eq_neg_moebius_add_corner
#print axioms synthesisDivisorEuler_eq_neg_mobius_add_corner
#print axioms synthesisSquarefulEuler_eq_corner
end RHLean.Proof

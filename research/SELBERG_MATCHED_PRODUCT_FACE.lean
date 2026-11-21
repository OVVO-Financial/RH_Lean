import «research.ALPOGE_SIGNED_SELBERG_INTEGRAL_SCHUR_20261120»
import RHLean.Analysis.MobiusRenewalTelescope
import RHLean.Proof.FinitePartialMoments

/-! Match the two second-Selberg channels on the same physical products.
The dyadic bound below is for this matched prime face, not for the complement. -/

set_option autoImplicit false
noncomputable section
open scoped ArithmeticFunction.vonMangoldt BigOperators
namespace RHLean.Analysis

def selbergMatchedMass (N : ℕ) (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A, (nativePNTSignedSecondSelbergKernel n - (Λ * Λ) n) * nativePNTError (N / n)

theorem selbergMatched_eq_log (N : ℕ) (A : Finset ℕ) :
    selbergMatchedMass N A = -(∑ n ∈ A, Λ n * Real.log n * nativePNTError (N / n)) := by
  unfold selbergMatchedMass
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n _
  unfold nativePNTSignedSecondSelbergKernel
  ring

private theorem matched_convolution (N : ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 N, (Λ * Λ) n * w n) =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (N / a), Λ a * Λ b * w (a * b) := by
  calc
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ z ∈ n.divisorsAntidiagonal,
        Λ z.1 * Λ z.2 * w (z.1 * z.2) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [ArithmeticFunction.mul_apply, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z hz
      rw [(Nat.mem_divisorsAntidiagonal.mp hz).1]
    _ = _ := by
      have h := sum_Icc_divisorsAntidiagonal_eq_sum_div
        (fun a b => ((Λ a * Λ b * w (a * b) : ℝ) : ℂ)) N
      exact_mod_cast h

/-- The second term is the actual ordered return in the expanded lower remainder. -/
theorem selbergMatched_ordered (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N) :
    selbergMatchedMass N A = (∑ n ∈ A, nativePNTSignedSecondSelbergKernel n *
      nativePNTError (N / n)) - ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (N / a),
      if a * b ∈ A then Λ a * Λ b * nativePNTError ((N / a) / b) else 0 := by
  classical
  have hf : (Finset.Icc 1 N).filter (· ∈ A) = A :=
    Finset.ext fun n => by simp only [Finset.mem_filter]; exact ⟨And.right, fun h => ⟨hA h, h⟩⟩
  have h := matched_convolution N (fun n => if n ∈ A then nativePNTError (N / n) else 0)
  simp only [mul_ite, mul_zero, ← Finset.sum_filter, hf] at h
  unfold selbergMatchedMass
  simp only [sub_mul, Finset.sum_sub_distrib, Nat.div_div_eq_div_mul, ← Finset.sum_filter]
  rw [h]

/-- The primitive S, lower logarithms, signed defect and every off-mask site survive. -/
theorem selbergMatched_complete (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N) :
    nativePNTError N * (Real.log N) ^ 2 =
      nativePNTSignedSelbergRemainder N * Real.log N - nativePNTLambdaFloorLogSignedErrorMass N -
      nativePNTLambdaFloorLogSignedDefectMass N + selbergMatchedMass N (Finset.Icc 1 N \ A) +
      selbergMatchedMass N A := by
  have hpart : selbergMatchedMass N (Finset.Icc 1 N \ A) + selbergMatchedMass N A =
      selbergMatchedMass N (Finset.Icc 1 N) := Finset.sum_sdiff hA
  have hall : selbergMatchedMass N (Finset.Icc 1 N) = nativePNTSignedSecondSelbergKernelErrorMass N -
      nativePNTLambdaConvolutionSignedErrorMass N := by
    simp only [selbergMatchedMass, sub_mul, Finset.sum_sub_distrib,
      nativePNTSignedSecondSelbergKernelErrorMass, nativePNTLambdaConvolutionSignedErrorMass]
  linarith only [nativePNTError_mul_log_sq_eq_signedSecondSelberg N,
    nativePNTLambdaFloorLogSignedErrorMass_eq_remainder_sub_convolution N, hpart, hall]

private theorem matched_mixed {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    nativePNTSignedSecondSelbergKernel (p*q) - (Λ * Λ) (p*q) = 0 := by
  have h := nativePNTSignedSecondSelbergKernel_eq_lambdaTwo_sub_two_log (p*q)
  rw [nativePNTSignedSecondSelbergKernel_mul_distinct_primes p q hp hq hne,
    nativeLambdaTwo_mul_distinct_primes p q hp hq hne] at h
  unfold nativePNTSignedSecondSelbergKernel
  linarith only [h]

theorem selbergMatched_oddChildren (N : ℕ) (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime ∧ 2 < p) :
    selbergMatchedMass N (P.image (fun p => 2*p)) = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  obtain ⟨p, hmem, rfl⟩ := Finset.mem_image.mp hn
  rw [matched_mixed Nat.prime_two (hp p hmem).1 (ne_of_lt (hp p hmem).2), zero_mul]

/-- A set of products, not a multiset of ordered prime labels. -/
def selbergPairSites (P : Finset ℕ) : Finset ℕ :=
  (P ×ˢ P).image (fun z => z.1 * z.2)

theorem selbergPairSites_admitted (R : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, AlpogeSelbergPrimeBand R p) : selbergPairSites P ⊆ Finset.Icc 1 (R^2-1) := by
  intro n hn
  obtain ⟨⟨p,q⟩, hpq, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hp,hq⟩ := Finset.mem_product.mp hpq
  have hlt := (hP p hp).2.2
  have hgt : 0 < R := (hP p hp).1.pos.trans hlt
  have hu : p*q < R^2 := by
    rw [pow_two]
    exact (Nat.mul_le_mul_left p (hP q hq).2.2.le).trans_lt (Nat.mul_lt_mul_of_pos_right hlt hgt)
  exact Finset.mem_Icc.mpr ⟨Nat.mul_pos (hP p hp).1.pos (hP q hq).1.pos, by change p*q ≤ R^2-1; omega⟩

theorem selbergMatched_schur (R : ℕ) (hR : 4 ≤ R) (P : Finset ℕ)
    (hP : ∀ p ∈ P, AlpogeSelbergPrimeBand R p) :
    selbergMatchedMass (R^2-1) (selbergPairSites P) = ∑ p ∈ P, 2 * (Real.log p)^2 := by
  classical
  let f := fun n => (nativePNTSignedSecondSelbergKernel n - (Λ * Λ) n) * nativePNTError ((R^2-1)/n)
  have hsub : P.image (fun p => p^2) ⊆ selbergPairSites P := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_image.mpr ⟨(p,p), Finset.mem_product.mpr ⟨hp,hp⟩, (pow_two p).symm⟩
  change (∑ n ∈ selbergPairSites P, f n) = _
  calc
    _ = ∑ n ∈ P.image (fun p => p^2), f n := by
      symm
      apply Finset.sum_subset hsub
      intro n hn hnot
      obtain ⟨⟨p,q⟩, hpq, rfl⟩ := Finset.mem_image.mp hn
      obtain ⟨hp,hq⟩ := Finset.mem_product.mp hpq
      have hne : p ≠ q := by
        rintro rfl
        exact hnot (Finset.mem_image.mpr ⟨p,hp,pow_two p⟩)
      change (nativePNTSignedSecondSelbergKernel (p*q) - (Λ * Λ) (p*q)) * _ = 0
      rw [matched_mixed (hP p hp).1 (hP q hq).1 hne, zero_mul]
    _ = _ := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro p hp
        have hq : (R^2-1)/(p^2) = 1 := by
          simpa only [pow_two] using alpogeSelbergPrimeBand_quotient_one R p p hR (hP p hp) (hP p hp)
        dsimp only [f, nativePNTSignedSecondSelbergKernel]
        rw [hq, nativePNTError_one, ArithmeticFunction.vonMangoldt_apply_pow (by decide : 2 ≠ 0),
          ArithmeticFunction.vonMangoldt_apply_prime (hP p hp).1, Nat.cast_pow, Real.log_pow]
        push_cast
        ring
      · intro a _ b _ hab
        simpa using congrArg Nat.sqrt hab

theorem selbergMatched_completeSchur (R : ℕ) (hR : 4 ≤ R) (P : Finset ℕ)
    (hP : ∀ p ∈ P, AlpogeSelbergPrimeBand R p) :
    let N := R^2-1
    nativePNTError N * (Real.log N)^2 = nativePNTSignedSelbergRemainder N * Real.log N -
      nativePNTLambdaFloorLogSignedErrorMass N - nativePNTLambdaFloorLogSignedDefectMass N +
      selbergMatchedMass N (Finset.Icc 1 N \ selbergPairSites P) + ∑ p ∈ P, 2*(Real.log p)^2 := by
  dsimp only
  rw [selbergMatched_complete _ _ (selbergPairSites_admitted R P hP), selbergMatched_schur R hR P hP]

theorem selbergMatched_normalized (R : ℕ) (hR : 4 ≤ R) (P : Finset ℕ)
    (hP : ∀ p ∈ P, AlpogeSelbergPrimeBand R p) :
    selbergMatchedMass (R^2-1) (selbergPairSites P) / (Real.log ((R^2-1 : ℕ) : ℝ))^2 ≤
      (P.card : ℝ) / 2 := by
  let X := R^2-1
  have hX : 1 < X := by
    dsimp [X]
    have : 4 ≤ R^2 := by nlinarith
    omega
  have hxl : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
  rw [selbergMatched_schur R hR P hP]
  apply (div_le_iff₀ (sq_pos_of_pos hxl)).2
  calc
    _ ≤ ∑ _p ∈ P, (Real.log (X : ℝ))^2 / 2 := by
      apply Finset.sum_le_sum
      intro p hp
      have hlt : p^2 < R^2 := Nat.pow_lt_pow_left (hP p hp).2.2 (by decide)
      have hle : p^2 ≤ X := by dsimp [X]; omega
      have hp1 : 1 ≤ p := (hP p hp).1.pos
      have hpl : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp1)
      have hcast : ((p^2 : ℕ) : ℝ) ≤ (X : ℝ) := by exact_mod_cast hle
      have hlog := Real.log_le_log (by positivity) hcast
      rw [Nat.cast_pow, Real.log_pow] at hlog
      norm_num only [Nat.cast_ofNat] at hlog
      nlinarith [mul_nonneg (sub_nonneg.mpr hlog) (by positivity : 0 ≤ Real.log (X : ℝ) + 2 * Real.log (p : ℝ))]
    _ = _ := by simp [X]; ring

theorem selbergMatched_dyadic (H : ℕ) (hH : 4 ≤ H) (P : ℕ → Finset ℕ)
    (hP : ∀ R ∈ Finset.Ico H (2*H), ∀ p ∈ P R, AlpogeSelbergPrimeBand R p) :
    upperPartialMomentNat 2 (Finset.Ico H (2*H)) (fun R =>
      selbergMatchedMass (R^2-1) (selbergPairSites (P R)) / (Real.log ((R^2-1 : ℕ) : ℝ))^2) ≤ (H : ℝ)^3 := by
  unfold upperPartialMomentNat
  calc
    _ ≤ ∑ _R ∈ Finset.Ico H (2*H), (H : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro R hmem
      have hR := Finset.mem_Ico.mp hmem
      have hs : P R ⊆ Finset.range R := fun p hp => Finset.mem_range.mpr (hP R hmem p hp).2.2
      have hc : (P R).card ≤ R := by simpa using Finset.card_le_card hs
      have hcnt : (P R).card ≤ 2*H := hc.trans hR.2.le
      have hc' : ((P R).card : ℝ) ≤ 2*(H : ℝ) := by exact_mod_cast hcnt
      have hb := selbergMatched_normalized R (hH.trans hR.1) (P R) (hP R hmem)
      exact pow_le_pow_left₀ (le_max_right _ 0)
        (max_le (hb.trans (by linarith only [hc'])) (Nat.cast_nonneg H)) 2
    _ = _ := by
      have hcard : (Finset.Ico H (2*H)).card = H := by rw [Nat.card_Ico]; omega
      simp only [Finset.sum_const, hcard, nsmul_eq_mul]
      ring

end RHLean.Analysis

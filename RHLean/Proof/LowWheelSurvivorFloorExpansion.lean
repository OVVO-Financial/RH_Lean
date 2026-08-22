import Mathlib
import RHLean.Analysis.MobiusRenewalTelescope
import RHLean.Arithmetic.SignedBuchstabRecursion
import RHLean.Proof.LowWheelSurvivorInclusionExclusion

/-!
# Floor expansion of low-wheel survivor frequencies

The Boolean-cube expansion of the high-prime survivor count is now converted
into the exact arithmetic floor formula.  For each low-prime face `t`, the
number of multiples of its squarefree product `d = primeFaceProduct t` in the
interval `(R,B]` is

`floor(B/d) - floor(R/d)`.

Specializing `B = floor((R^2-1)/c)` therefore removes the prime-count function
from every transport multiplicity.  The high-prime frequency is expressed
entirely through low-prime Boolean-cube signs and the hyperbolic cutoff
`c * d * k <= R^2 - 1`.

The second half records the exact closure of the resulting one-prime frontier
coordinate.  Its pointwise incidence is a finite Mertens bundle.  On the top
half of the root range it is literally `1 - M(floor((R^2-1)/n))`, so a positive
energy contains local Mertens energy verbatim.  The remaining signed bootstrap
collapses by `mu * 1 = delta` to `M(X) = M(X)`.

No norm estimate, prime-number theorem, Strong Mertens estimate, asymptotic,
or RH input is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Exact count of multiples of a positive integer in a half-open interval. -/
theorem card_Ioc_filter_dvd_eq_div_sub_div
    (A B d : ℕ) (hd : 0 < d) :
    ((Finset.Ioc A B).filter fun q => d ∣ q).card =
      B / d - A / d := by
  classical
  have hbij :
      (Finset.Ioc (A / d) (B / d)).card =
        ((Finset.Ioc A B).filter fun q => d ∣ q).card := by
    refine Finset.card_bij (fun k _hk => d * k) ?_ ?_ ?_
    · intro k hk
      rcases Finset.mem_Ioc.mp hk with ⟨hlow, hupp⟩
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_Ioc.mpr
        constructor
        · have h := (Nat.div_lt_iff_lt_mul hd).1 hlow
          simpa [Nat.mul_comm] using h
        · have h := (Nat.le_div_iff_mul_le hd).1 hupp
          simpa [Nat.mul_comm] using h
      · exact ⟨k, rfl⟩
    · intro a _ha b _hb hab
      exact Nat.eq_of_mul_eq_mul_left hd hab
    · intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hqIoc, hdiv⟩
      rcases hdiv with ⟨k, rfl⟩
      refine ⟨k, ?_, rfl⟩
      apply Finset.mem_Ioc.mpr
      constructor
      · apply (Nat.div_lt_iff_lt_mul hd).2
        simpa [Nat.mul_comm] using (Finset.mem_Ioc.mp hqIoc).1
      · apply (Nat.le_div_iff_mul_le hd).2
        simpa [Nat.mul_comm] using (Finset.mem_Ioc.mp hqIoc).2
  simpa using hbij.symm

/-- Every Boolean-cube prime-face product is positive. -/
theorem primeFaceProduct_pos_of_mem_powerset
    {R : ℕ} {t : Finset ℕ}
    (ht : t ∈ (primesUpTo R).powerset) :
    0 < primeFaceProduct t := by
  unfold primeFaceProduct
  apply Finset.prod_pos
  intro p hp
  have hpR : p ∈ primesUpTo R := (Finset.mem_powerset.mp ht) hp
  exact (prime_of_mem_primesUpTo hpR).pos

/-- One face's divisibility population is the elementary floor difference. -/
theorem lowWheelFaceMultipleSet_card_eq_floorDiff
    {R B : ℕ} {t : Finset ℕ}
    (ht : t ∈ (primesUpTo R).powerset) :
    (lowWheelFaceMultipleSet R B t).card =
      B / primeFaceProduct t - R / primeFaceProduct t := by
  unfold lowWheelFaceMultipleSet
  exact card_Ioc_filter_dvd_eq_div_sub_div
    R B (primeFaceProduct t) (primeFaceProduct_pos_of_mem_powerset ht)

/-- **Boolean-cube floor expansion.**  Every high-survivor count is now an
exact finite alternating sum of floor differences indexed only by low-prime
faces. -/
theorem lowWheelHighSurvivorSet_card_eq_faceFloorDiff
    (R B : ℕ) :
    ((lowWheelHighSurvivorSet R B).card : ℤ) =
      ∑ t ∈ (primesUpTo R).powerset,
        booleanCubeSign t *
          ((B / primeFaceProduct t - R / primeFaceProduct t : ℕ) : ℤ) := by
  rw [lowWheelHighSurvivorSet_card_eq_faceMultipleCounts]
  apply Finset.sum_congr rfl
  intro t ht
  rw [lowWheelFaceMultipleSet_card_eq_floorDiff ht]

/-- The cofactor-specific high-prime multiplicity has no remaining prime-count
term: it is a signed low-wheel face sum with a reciprocal hyperbolic cutoff. -/
theorem lowWheelHighPrimeMultiplicity_eq_faceFloorDiff
    (R c : ℕ) :
    (lowWheelHighPrimeMultiplicity R c : ℤ) =
      ∑ t ∈ (primesUpTo R).powerset,
        booleanCubeSign t *
          ((squareRootEndpoint R / (c * primeFaceProduct t) -
              R / primeFaceProduct t : ℕ) : ℤ) := by
  unfold lowWheelHighPrimeMultiplicity
  rw [lowWheelHighSurvivorSet_card_eq_faceFloorDiff]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [Nat.div_div_eq_div_mul]

/-- Complex form of the exact frequency expansion, ready to substitute into
the cofactor-first transport sum without changing its signed order. -/
theorem lowWheelHighPrimeMultiplicity_cast_eq_faceFloorDiff
    (R c : ℕ) :
    (lowWheelHighPrimeMultiplicity R c : ℂ) =
      ∑ t ∈ (primesUpTo R).powerset,
        (booleanCubeSign t : ℂ) *
          ((squareRootEndpoint R / (c * primeFaceProduct t) -
              R / primeFaceProduct t : ℕ) : ℂ) := by
  have h := lowWheelHighPrimeMultiplicity_eq_faceFloorDiff R c
  exact_mod_cast h

/-- **Prime-count-free transport identity.**  The whole upper-prime transport
mass is a finite double sum over a low cofactor `c` and a low-prime Boolean face
`t`.  The high region now appears only through the floor cutoff. -/
theorem squareRootTransportCofactorFirst_eq_lowWheelFaceFloorSum
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootTransportCofactorFirst R =
      ∑ c ∈ Finset.Ico 1 R,
        ∑ t ∈ (primesUpTo R).powerset,
          canonicalMoebiusWeight c * (booleanCubeSign t : ℂ) *
            ((squareRootEndpoint R / (c * primeFaceProduct t) -
                R / primeFaceProduct t : ℕ) : ℂ) := by
  rw [squareRootTransportCofactorFirst_eq_lowWheelFrequency R hR]
  unfold squareRootTransportLowWheelFrequency
  apply Finset.sum_congr rfl
  intro c _hc
  rw [lowWheelHighPrimeMultiplicity_cast_eq_faceFloorDiff R c]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _ht
  ring

/-! ## Exact closure of the one-prime frontier coordinate -/

/-- Pointwise canonical frontier incidence in its exact lower-scale Mertens
bundle form. -/
def canonicalFrontierIncidence (R n : ℕ) : ℂ :=
  1 - ∑ q ∈ Finset.Icc 1 (R / n),
    mertensSummatory (squareRootEndpoint R / (n * q))

/-- The pointwise incidence is exactly the finite lower-scale Mertens bundle. -/
theorem canonicalIncidence_eq_one_sub_mertensBundle
    (R n : ℕ) :
    canonicalFrontierIncidence R n =
      1 - ∑ q ∈ Finset.Icc 1 (R / n),
        mertensSummatory (squareRootEndpoint R / (n * q)) := by
  rfl

/-- On the upper half of the root range the bundle has only the `q = 1` term. -/
theorem canonicalIncidence_eq_one_sub_mertens_of_half_lt
    {R n : ℕ} (hn : 1 ≤ n) (hnR : n ≤ R) (hhalf : R / 2 < n) :
    canonicalFrontierIncidence R n =
      1 - mertensSummatory (squareRootEndpoint R / n) := by
  have hnpos : 0 < n := by omega
  have hRlt : R < n * 2 :=
    (Nat.div_lt_iff_lt_mul (by norm_num : 0 < (2 : ℕ))).1 hhalf
  have hlt2 : R / n < 2 := by
    apply (Nat.div_lt_iff_lt_mul hnpos).2
    simpa [Nat.mul_comm] using hRlt
  have hge1 : 1 ≤ R / n := (Nat.one_le_div_iff hnpos).2 hnR
  have hdiv : R / n = 1 := by omega
  simp [canonicalFrontierIncidence, hdiv]

/-- Positive top-half energy of the incidence field. -/
def canonicalFrontierTopEnergy (R : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc (R / 2) R,
    (n : ℝ) * ‖canonicalFrontierIncidence R n‖ ^ 2

/-- The top-half positive energy literally contains the local Mertens values
`M(floor((R^2-1)/n))`; no positive norm has removed them. -/
theorem canonicalFrontierTopEnergy_eq_localMertensEnergy
    (R : ℕ) :
    canonicalFrontierTopEnergy R =
      ∑ n ∈ Finset.Ioc (R / 2) R,
        (n : ℝ) * ‖1 - mertensSummatory (squareRootEndpoint R / n)‖ ^ 2 := by
  classical
  unfold canonicalFrontierTopEnergy
  apply Finset.sum_congr rfl
  intro n hnI
  rcases Finset.mem_Ioc.mp hnI with ⟨hhalf, hnR⟩
  have hn : 1 ≤ n := by omega
  rw [canonicalIncidence_eq_one_sub_mertens_of_half_lt hn hnR hhalf]

/-- Generic triangular Möbius collapse.  Regrouping by `m = n*q` gives
coefficient `sum_{n | m} mu(n)`, hence only `m = 1` survives. -/
theorem mobius_hyperbola_double_sum_eq_head
    (F : ℕ → ℂ) {R : ℕ} (hR : 1 ≤ R) :
    (∑ n ∈ Finset.Icc 1 R,
        (((μ n : ℤ) : ℂ)) *
          ∑ q ∈ Finset.Icc 1 (R / n), F (n * q)) =
      F 1 := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 R,
        (((μ n : ℤ) : ℂ)) *
          ∑ q ∈ Finset.Icc 1 (R / n), F (n * q)) =
      ∑ n ∈ Finset.Icc 1 R,
        ∑ q ∈ Finset.Icc 1 (R / n),
          (((μ n : ℤ) : ℂ)) * F (n * q) := by
            apply Finset.sum_congr rfl
            intro n _hn
            rw [Finset.mul_sum]
    _ = ∑ m ∈ Finset.Icc 1 R,
        ∑ p ∈ m.divisorsAntidiagonal,
          (((μ p.1 : ℤ) : ℂ)) * F (p.1 * p.2) := by
            symm
            exact RHLean.Analysis.sum_Icc_divisorsAntidiagonal_eq_sum_div
              (fun a b => (((μ a : ℤ) : ℂ)) * F (a * b)) R
    _ = ∑ m ∈ Finset.Icc 1 R,
        (if m = 1 then F 1 else 0) := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [Nat.sum_divisorsAntidiagonal]
          calc
            (∑ d ∈ m.divisors,
                (((μ d : ℤ) : ℂ)) * F (d * (m / d))) =
              ∑ d ∈ m.divisors,
                (((μ d : ℤ) : ℂ)) * F m := by
                  apply Finset.sum_congr rfl
                  intro d hd
                  have hdData := Nat.mem_divisors.mp hd
                  rw [Nat.mul_div_cancel' hdData.1]
            _ = (∑ d ∈ m.divisors, (((μ d : ℤ) : ℂ))) * F m := by
                  rw [Finset.sum_mul]
            _ = (if m = 1 then (1 : ℂ) else 0) * F m := by
                  rw [RHLean.Analysis.sum_divisors_moebius_eq_ite]
            _ = if m = 1 then F 1 else 0 := by
                  by_cases hm1 : m = 1
                  · subst m
                    simp
                  · simp [hm1]
    _ = F 1 := by
      have h1mem : (1 : ℕ) ∈ Finset.Icc 1 R :=
        Finset.mem_Icc.mpr ⟨le_rfl, hR⟩
      simp [h1mem]

/-- Corrected lower-half/top-half bootstrap expression. -/
def frontierBootstrapRHS (R : ℕ) : ℂ :=
  mertensSummatory (R / 2) -
    ∑ n ∈ Finset.Icc 1 (R / 2),
      (((μ n : ℤ) : ℂ)) * canonicalFrontierIncidence R n +
    ∑ n ∈ Finset.Ioc (R / 2) R,
      (((μ n : ℤ) : ℂ)) *
        mertensSummatory (squareRootEndpoint R / n)

/-- The corrected split bootstrap is exactly the full triangular Möbius bundle.
This is the algebraic step that makes the no-go transparent. -/
theorem frontierBootstrapRHS_eq_fullHyperbola
    (R : ℕ) (hR : 2 ≤ R) :
    frontierBootstrapRHS R =
      ∑ n ∈ Finset.Icc 1 R,
        (((μ n : ℤ) : ℂ)) *
          ∑ q ∈ Finset.Icc 1 (R / n),
            mertensSummatory (squareRootEndpoint R / (n * q)) := by
  classical
  let H := R / 2
  have hset : Finset.Icc 1 R = Finset.Icc 1 H ∪ Finset.Ioc H R := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 H) (Finset.Ioc H R) := by
    rw [Finset.disjoint_left]
    intro n hnlo hnhi
    simp only [Finset.mem_Icc] at hnlo
    simp only [Finset.mem_Ioc] at hnhi
    omega
  have hM : mertensSummatory H =
      ∑ n ∈ Finset.Icc 1 H, (((μ n : ℤ) : ℂ)) :=
    RHLean.Analysis.mertensSummatory_eq_sum_Icc H
  have htop :
      (∑ n ∈ Finset.Ioc H R,
          (((μ n : ℤ) : ℂ)) *
            ∑ q ∈ Finset.Icc 1 (R / n),
              mertensSummatory (squareRootEndpoint R / (n * q))) =
        ∑ n ∈ Finset.Ioc H R,
          (((μ n : ℤ) : ℂ)) *
            mertensSummatory (squareRootEndpoint R / n) := by
    apply Finset.sum_congr rfl
    intro n hnI
    rcases Finset.mem_Ioc.mp hnI with ⟨hHn, hnR⟩
    have hnpos : 0 < n := by omega
    have hRlt : R < n * 2 := by
      dsimp [H] at hHn
      exact (Nat.div_lt_iff_lt_mul (by norm_num : 0 < (2 : ℕ))).1 hHn
    have hlt2 : R / n < 2 := by
      apply (Nat.div_lt_iff_lt_mul hnpos).2
      simpa [Nat.mul_comm] using hRlt
    have hge1 : 1 ≤ R / n := (Nat.one_le_div_iff hnpos).2 hnR
    have hdiv : R / n = 1 := by omega
    simp [hdiv]
  unfold frontierBootstrapRHS canonicalFrontierIncidence
  dsimp [H] at hM ⊢
  rw [hM]
  rw [hset, Finset.sum_union hdisj]
  rw [htop]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- Corrected finite self-consistency relation. -/
theorem frontier_bootstrap_self_consistency
    (R : ℕ) (hR : 2 ≤ R) :
    mertensSummatory (squareRootEndpoint R) = frontierBootstrapRHS R := by
  rw [frontierBootstrapRHS_eq_fullHyperbola R hR]
  symm
  simpa using mobius_hyperbola_double_sum_eq_head
    (F := fun m => mertensSummatory (squareRootEndpoint R / m))
    (R := R) (by omega)

/-- **Definitive one-prime-frontier no-go.**  After the incidence bundle is
substituted, the bootstrap is exactly `mu * 1 = delta`; it collapses to the
identity `M(X) = M(X)` and imposes no additional finite-volume constraint. -/
theorem frontier_bootstrap_collapses_to_identity
    (R : ℕ) (hR : 2 ≤ R) :
    frontierBootstrapRHS R = mertensSummatory (squareRootEndpoint R) := by
  exact (frontier_bootstrap_self_consistency R hR).symm

end RHLean.Proof

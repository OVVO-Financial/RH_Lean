import Mathlib
import RHLean.Proof.SquareRootMertensEndpointAmplification

/-!
# The original historical amplification and its logarithmic growth target

This file defines the actual finite maximum

`K_R = max_{0 <= y < R} (M(y)-1)^2/(y+1)`

and the original endpoint ratio `(M(R^2-1)-1)^2/(R^2*K_R)`.
The finite maximum has the harmless value zero for the empty history `R=0`.
For `R>=1`, the term `y=0` proves `K_R>=1`.  In particular, there is no
assumed positivity or hidden estimate in the denominator.

The running maximum includes exactly the endpoints `R>=2`, `R^2-1<=X`.
Its zero logarithmic growth is defined as a proposition; it is not proved here.
The equivalence with the existing fixed-amplification statement is only an
identification of the same arithmetic object, not a proof of that statement.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius Topology

namespace RHLean.Proof

/-- A finite maximum with the nonnegative baseline `0`. -/
private def prefixMax (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => max (prefixMax f n) (f n)

private theorem prefixMax_nonneg (f : ℕ → ℝ) (n : ℕ) :
    0 ≤ prefixMax f n := by
  induction n with
  | zero => simp [prefixMax]
  | succ n ih =>
      exact ih.trans (le_max_left _ _)

private theorem prefixMax_le_iff (f : ℕ → ℝ) (n : ℕ) (C : ℝ) :
    prefixMax f n ≤ C ↔ 0 ≤ C ∧ ∀ i : ℕ, i < n → f i ≤ C := by
  induction n with
  | zero => simp [prefixMax]
  | succ n ih =>
      change max (prefixMax f n) (f n) ≤ C ↔ _
      rw [max_le_iff, ih]
      constructor
      · rintro ⟨⟨hC, hprefix⟩, hn⟩
        refine ⟨hC, ?_⟩
        intro i hi
        by_cases hin : i = n
        · simpa [hin] using hn
        · exact hprefix i (by omega)
      · rintro ⟨hC, hprefix⟩
        exact ⟨⟨hC, fun i hi => hprefix i (by omega)⟩,
          hprefix n (by omega)⟩

/-- The centered critical energy at a historical integer argument. -/
def mertensHistoricalCriticalEnergy (y : ℕ) : ℝ :=
  (((mertensSummatoryInt y - 1 : ℤ) : ℝ) ^ 2) / (((y + 1 : ℕ) : ℝ))

/-- The exact maximum over `0 <= y < R`, extended by `0` when `R=0`. -/
def squareRootHistoricalK (R : ℕ) : ℝ :=
  prefixMax mertensHistoricalCriticalEnergy R

theorem squareRootHistoricalK_nonneg (R : ℕ) :
    0 ≤ squareRootHistoricalK R :=
  prefixMax_nonneg _ _

/-- This maximum is the least lower critical envelope already used by the
original fixed-amplification statement. -/
theorem squareRootHistoricalK_le_iff (R : ℕ) (K : ℝ) :
    squareRootHistoricalK R ≤ K ↔ LowerMertensCriticalEnvelope R K := by
  rw [squareRootHistoricalK, prefixMax_le_iff]
  constructor
  · rintro ⟨hK, hbound⟩
    refine ⟨hK, ?_⟩
    intro y hy
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < ((y + 1 : ℕ) : ℝ))).1
      (hbound y hy)
  · rintro ⟨hK, hbound⟩
    refine ⟨hK, ?_⟩
    intro y hy
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < ((y + 1 : ℕ) : ℝ))).2
      (hbound y hy)

theorem squareRootHistoricalK_envelope (R : ℕ) :
    LowerMertensCriticalEnvelope R (squareRootHistoricalK R) :=
  (squareRootHistoricalK_le_iff R _).1 le_rfl

theorem squareRootHistoricalK_one_le {R : ℕ} (hR : 1 ≤ R) :
    1 ≤ squareRootHistoricalK R := by
  have h := (squareRootHistoricalK_envelope R).2 0 (by omega)
  simpa [mertensSummatoryInt] using h

theorem squareRootHistoricalK_pos {R : ℕ} (hR : 1 ≤ R) :
    0 < squareRootHistoricalK R :=
  lt_of_lt_of_le (by norm_num) (squareRootHistoricalK_one_le hR)

theorem squareRootHistoricalK_mono {R S : ℕ} (hRS : R ≤ S) :
    squareRootHistoricalK R ≤ squareRootHistoricalK S := by
  apply (squareRootHistoricalK_le_iff R _).2
  refine ⟨squareRootHistoricalK_nonneg S, ?_⟩
  intro y hy
  exact (squareRootHistoricalK_envelope S).2 y (lt_of_lt_of_le hy hRS)

/-- At the first relevant root, the two historical terms are `1` and `0`. -/
@[simp] theorem squareRootHistoricalK_two : squareRootHistoricalK 2 = 1 := by
  norm_num [squareRootHistoricalK, prefixMax, mertensHistoricalCriticalEnergy,
    mertensSummatoryInt, Finset.sum_range_succ]

/-- Original centered endpoint amplification, with no compensated proxy. -/
def squareRootEndpointAmplification (R : ℕ) : ℝ :=
  (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ) ^ 2) /
    ((R : ℝ) ^ 2 * squareRootHistoricalK R)

theorem squareRootAmplificationDenominator_pos {R : ℕ} (hR : 1 ≤ R) :
    0 < (R : ℝ) ^ 2 * squareRootHistoricalK R := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  exact mul_pos (pow_pos hRpos _) (squareRootHistoricalK_pos hR)

theorem squareRootEndpointAmplification_nonneg (R : ℕ) :
    0 ≤ squareRootEndpointAmplification R := by
  unfold squareRootEndpointAmplification
  exact div_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _)
    (squareRootHistoricalK_nonneg R))

/-- A centering and cutoff regression: `M(3)=-1`, so the original ratio at
`R=2` is `1`, not the seed-only value `1/4`. -/
@[simp] theorem squareRootEndpointAmplification_two :
    squareRootEndpointAmplification 2 = 1 := by
  have htwo : (μ 2 : ℤ) = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  have hthree : (μ 3 : ℤ) = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  norm_num [squareRootEndpointAmplification, squareRootEndpoint,
    mertensSummatoryInt, Finset.sum_range_succ, htwo, hthree]

/-- Clearing the denominator recovers the literal original endpoint bound. -/
theorem squareRootEndpointAmplification_le_iff {R : ℕ} (hR : 1 ≤ R) (A : ℝ) :
    squareRootEndpointAmplification R ≤ A ↔
      (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ) ^ 2) ≤
        A * (R : ℝ) ^ 2 * squareRootHistoricalK R := by
  unfold squareRootEndpointAmplification
  rw [div_le_iff₀ (squareRootAmplificationDenominator_pos hR)]
  simp only [mul_assoc]

/-- The concrete ratio is the same finite-`A` target already present in the
repository, including its quantification over every admissible envelope. -/
theorem squareRootMertensEndpointAmplification_iff_uniformRatio :
    SquareRootMertensEndpointAmplificationStatement ↔
      ∃ A : ℝ, 0 ≤ A ∧
        ∀ R : ℕ, 2 ≤ R → squareRootEndpointAmplification R ≤ A := by
  constructor
  · rintro ⟨A, hA, hbound⟩
    refine ⟨A, hA, ?_⟩
    intro R hR
    apply (squareRootEndpointAmplification_le_iff (by omega) A).2
    exact hbound R (squareRootHistoricalK R) hR
      (squareRootHistoricalK_envelope R)
  · rintro ⟨A, hA, hbound⟩
    refine ⟨A, hA, ?_⟩
    intro R K hR hK
    have hratio :=
      (squareRootEndpointAmplification_le_iff (by omega) A).1 (hbound R hR)
    have hKle := (squareRootHistoricalK_le_iff R K).2 hK
    exact hratio.trans
      (mul_le_mul_of_nonneg_left hKle (mul_nonneg hA (sq_nonneg _)))

/-- The running maximum over precisely the admitted square endpoints.  The
finite range `X+2` contains every `R>=2` with `R^2-1<=X`. -/
def squareRootAmplificationMax (X : ℕ) : ℝ :=
  prefixMax (fun R =>
    if 2 ≤ R ∧ squareRootEndpoint R ≤ X then
      squareRootEndpointAmplification R else 0) (X + 2)

private theorem root_lt_cutoff_add_two {R X : ℕ}
    (hR : 2 ≤ R) (hX : squareRootEndpoint R ≤ X) : R < X + 2 := by
  have hR2 : 0 < R ^ 2 := pow_pos (by omega) _
  have hRle : R ≤ R ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul_left R (show 1 ≤ R by omega)
  have hsquare : R ^ 2 ≤ X + 1 := by
    unfold squareRootEndpoint at hX
    omega
  omega

theorem squareRootAmplificationMax_nonneg (X : ℕ) :
    0 ≤ squareRootAmplificationMax X :=
  prefixMax_nonneg _ _

/-- Exact characterization of an upper bound for the running maximum. -/
theorem squareRootAmplificationMax_le_iff (X : ℕ) (A : ℝ) :
    squareRootAmplificationMax X ≤ A ↔
      0 ≤ A ∧ ∀ R : ℕ, 2 ≤ R → squareRootEndpoint R ≤ X →
        squareRootEndpointAmplification R ≤ A := by
  rw [squareRootAmplificationMax, prefixMax_le_iff]
  constructor
  · rintro ⟨hA, hbound⟩
    refine ⟨hA, ?_⟩
    intro R hR hX
    have h := hbound R (root_lt_cutoff_add_two hR hX)
    simpa [hR, hX] using h
  · rintro ⟨hA, hbound⟩
    refine ⟨hA, ?_⟩
    intro R _hRrange
    split_ifs with h
    · exact hbound R h.1 h.2
    · exact hA

theorem squareRootEndpointAmplification_le_max {R X : ℕ}
    (hR : 2 ≤ R) (hX : squareRootEndpoint R ≤ X) :
    squareRootEndpointAmplification R ≤ squareRootAmplificationMax X :=
  ((squareRootAmplificationMax_le_iff X _).1 le_rfl).2 R hR hX

theorem squareRootAmplificationMax_mono {X Y : ℕ} (hXY : X ≤ Y) :
    squareRootAmplificationMax X ≤ squareRootAmplificationMax Y := by
  apply (squareRootAmplificationMax_le_iff X _).2
  refine ⟨squareRootAmplificationMax_nonneg Y, ?_⟩
  intro R hR hX
  exact squareRootEndpointAmplification_le_max hR (hX.trans hXY)

/-- Bounding this running maximum by one fixed constant is exactly the
repository's original fixed-amplification statement. -/
theorem squareRootMertensEndpointAmplification_iff_boundedRunningMax :
    SquareRootMertensEndpointAmplificationStatement ↔
      ∃ A : ℝ, 0 ≤ A ∧ ∀ X : ℕ, squareRootAmplificationMax X ≤ A := by
  rw [squareRootMertensEndpointAmplification_iff_uniformRatio]
  constructor
  · rintro ⟨A, hA, hbound⟩
    refine ⟨A, hA, ?_⟩
    intro X
    exact (squareRootAmplificationMax_le_iff X A).2
      ⟨hA, fun R hR _hX => hbound R hR⟩
  · rintro ⟨A, hA, hbound⟩
    refine ⟨A, hA, ?_⟩
    intro R hR
    exact (squareRootEndpointAmplification_le_max hR le_rfl).trans
      (hbound (squareRootEndpoint R))

/-- A nonnegative bound on the logarithm of the running maximum is exactly
the same bound on every admitted endpoint logarithm. -/
theorem squareRootAmplificationMax_log_le_iff (X : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    Real.log (1 + squareRootAmplificationMax X) ≤ B ↔
      ∀ R : ℕ, 2 ≤ R → squareRootEndpoint R ≤ X →
        Real.log (1 + squareRootEndpointAmplification R) ≤ B := by
  constructor
  · intro h R hR hX
    have hpos : 0 < 1 + squareRootEndpointAmplification R := by
      linarith [squareRootEndpointAmplification_nonneg R]
    exact (Real.log_le_log hpos
      (add_le_add_left (squareRootEndpointAmplification_le_max hR hX) 1)).trans h
  · intro h
    have hexp : 1 ≤ Real.exp B := by
      simpa using (Real.exp_le_exp.mpr hB)
    have hmax : squareRootAmplificationMax X ≤ Real.exp B - 1 := by
      apply (squareRootAmplificationMax_le_iff X (Real.exp B - 1)).2
      refine ⟨by linarith, ?_⟩
      intro R hR hX
      have hpos : 0 < 1 + squareRootEndpointAmplification R := by
        linarith [squareRootEndpointAmplification_nonneg R]
      have hbound := (Real.log_le_iff_le_exp hpos).1 (h R hR hX)
      linarith
    have hpos : 0 < 1 + squareRootAmplificationMax X := by
      linarith [squareRootAmplificationMax_nonneg X]
    apply (Real.log_le_iff_le_exp hpos).2
    linarith

/-- The exact logarithmic ratio at natural cutoffs.  The values below `2`
are immaterial for a limit at infinity. -/
def squareRootAmplificationLogRatio (X : ℕ) : ℝ :=
  Real.log (1 + squareRootAmplificationMax X) / Real.log (X : ℝ)

theorem squareRootAmplificationLogRatio_nonneg {X : ℕ} (hX : 2 ≤ X) :
    0 ≤ squareRootAmplificationLogRatio X := by
  unfold squareRootAmplificationLogRatio
  apply div_nonneg
  · exact Real.log_nonneg (by linarith [squareRootAmplificationMax_nonneg X])
  · apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ X by omega)

/-- Finite, all-prefix characterization of the requested ratio.  Every
endpoint through `X` must satisfy the same logarithmic budget. -/
theorem squareRootAmplificationLogRatio_le_iff
    (X : ℕ) (ε : ℝ) (hX : 2 ≤ X) (hε : 0 ≤ ε) :
    squareRootAmplificationLogRatio X ≤ ε ↔
      ∀ R : ℕ, 2 ≤ R → squareRootEndpoint R ≤ X →
        Real.log (1 + squareRootEndpointAmplification R) ≤
          ε * Real.log (X : ℝ) := by
  have hlog : 0 < Real.log (X : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < X by omega)
  rw [squareRootAmplificationLogRatio, div_le_iff₀ hlog]
  exact squareRootAmplificationMax_log_le_iff X
    (ε * Real.log (X : ℝ)) (mul_nonneg hε hlog.le)

/-- The requested zero growth limit.  This is an open proposition, not an
axiom and not a theorem asserted by this module. -/
def SquareRootAmplificationZeroLogGrowthStatement : Prop :=
  Filter.Tendsto squareRootAmplificationLogRatio Filter.atTop (𝓝 0)

end RHLean.Proof

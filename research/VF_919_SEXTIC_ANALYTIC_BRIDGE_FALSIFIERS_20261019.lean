import «research.VF_919_NATIVE_SEXTIC_IDEAL_FIBER_20261019»

/-!
# Independent RHLean 7/8 lift: exact source-validity falsifiers

These are proved from Mathlib and RHLean's OWN Eisenstein coordinate
multiplication. No OAI proof result or conditional 7/8 hypothesis is imported.

The substantive issue is not existence of finite phases at 317/1027,
which the native sextic modules verify. The issue is preserving actual
primary normalization and proving a character-sensitive power saving
uniformly in conductor, height and source mask.

This file records three unconditional mathematical corrections to a
proposed wholesale 40-step bridge:

1. Primary generators are normalized mod (3) and multiplicatively
   closed. A further positive-real sign constraint is not admissible.
2. The Stage II gate U^(1/6) D^(5/6) <= U requires D<=U, not
   D<=U^(6/5); the counterexample U=32, D=64 is exact.
3. A bound on coefficient l^(6/5) energy ALONE cannot deliver the
   proposed 5/6+epsilon second-moment gain: a principal character
   row with constant coefficients has no oscillation. A concrete
   polynomial family disproves a putative fixed implied constant
   even with epsilon = 1/12.

The theorems are **NOT** a statement that the genuine, fully
Möbius-compensated OpenAI estimate is false. They prove that the
listed weaker hypotheses are insufficient.
-/

namespace RHLean.Analysis

/-- Multiplicative primary coordinates in Z[omega]: a=1 (mod 3),
b=0 (mod 3). This avoids an additional nonmultiplicative sign rule. -/
def vf919PrimaryCongruence (a b : ℤ) : Prop :=
  ∃ k l : ℤ, a = 1 + 3 * k ∧ b = 3 * l

/-- The primary congruence is multiplicatively stable using the
literal RHLean Eisenstein coordinate product. -/
theorem vf919PrimaryCongruence_mul
    {a b c d : ℤ}
    (hα : vf919PrimaryCongruence a b)
    (hβ : vf919PrimaryCongruence c d) :
    vf919PrimaryCongruence
      (vf919EisensteinCoordMul a b c d).1
      (vf919EisensteinCoordMul a b c d).2 := by
  obtain ⟨k, l, ha, hb⟩ := hα
  obtain ⟨m, n, hc, hd⟩ := hβ
  unfold vf919PrimaryCongruence vf919EisensteinCoordMul
  refine ⟨k + m + 3 * (k * m - l * n),
    l + n + 3 * (k * n + l * m - l * n), ?_, ?_⟩
  · dsimp
    rw [ha, hb, hc, hd]
    ring
  · dsimp
    rw [ha, hb, hc, hd]
    ring

/-- A NORM-SEVEN primary generator from the x=317 and x=1027
witnesses has strictly NEGATIVE real part. Therefore positivity
cannot be imposed together with unique normalization mod (3). -/
theorem vf919PrimaryNormSeven_negativeRealWitness :
    vf919PrimaryCongruence (-2) (-3) ∧
    vf919EisensteinCoordNorm (-2) (-3) = 7 ∧
    ((-2 : ℚ) - (-3 : ℚ) / 2) = -(1 / 2 : ℚ) := by
  constructor
  · exact ⟨-1, -1, by norm_num, by norm_num⟩
  constructor
  · norm_num [vf919EisensteinCoordNorm]
  · norm_num

/-- The six Eisenstein unit coordinates 1,-1,omega,-omega,
omega^2,-omega^2. -/
def vf919SixEisensteinUnits : Fin 6 → ℤ × ℤ :=
  ![(1, 0), (-1, 0), (0, 1), (0, -1), (-1, -1), (1, 1)]

/-- Literal exact norm-one check for all six candidate units. -/
theorem vf919SixEisensteinUnits_normOne :
    ∀ i : Fin 6,
      vf919EisensteinCoordNorm
        (vf919SixEisensteinUnits i).1
        (vf919SixEisensteinUnits i).2 = 1 := by
  decide

/-- Among the six unit associates of the norm-7 witness, only the
identity unit preserves the primary congruence mod (3).
It cannot simultaneously repair the negative real part. -/
theorem vf919SixUnits_primaryNormSeven_onlyIdentity :
    ∀ i : Fin 6,
      let u := vf919SixEisensteinUnits i
      let v := vf919EisensteinCoordMul u.1 u.2 (-2) (-3)
      (v.1 % 3 = 1 ∧ v.2 % 3 = 0) →
        vf919SixEisensteinUnits i = (1, 0) := by
  decide

/-- Raising the proposed Stage-II low-band inequality to its sixth
power gives U*D^5 <= U^6. At U=32 and D=64=U^(6/5),
the inequality is FALSE. -/
theorem vf919AmplificationLowBand_U32_D64_fails :
    (32 : ℕ) * 64 ^ 5 > 32 ^ 6 := by
  norm_num

/-- The candidate coefficient-only moment gain (with eps=1/12,
D=t^12, U=1, constant principal phase and t^12 unit coefficients)
would assert t^12 <= C * (t+t^11) uniformly in t. This is impossible
for any fixed C, even before adding actual owner crossing weights.

This does NOT contradict a marked, signed IDEAL-Mobius moment
inequality: that theorem uses additional arithmetic cancellation that
the general coefficient l^(6/5) energy hypothesis omits. -/
theorem vf919NoCoefficientOnlyFiveSixthsMomentGain :
    ¬ ∃ C : ℕ, ∀ t : ℕ, 1 ≤ t →
      t ^ 12 ≤ C * (t + t ^ 11) := by
  rintro ⟨C, hC⟩
  let t : ℕ := 2 * C + 2
  have ht : 1 ≤ t := by dsimp [t]; omega
  have htgt : 2 * C < t := by dsimp [t]; omega
  have hpow : 1 ≤ t ^ 10 := by
    have hp : 0 < t ^ 10 := pow_pos (by omega : 0 < t) 10
    omega
  have hsmall : t ≤ t ^ 11 := by
    calc
      t = t * 1 := by ring
      _ ≤ t * (t ^ 10) := Nat.mul_le_mul_left t hpow
      _ = t ^ 11 := by ring
  have hsum : t + t ^ 11 ≤ 2 * t ^ 11 := by omega
  have hupper : C * (t + t ^ 11) ≤ 2 * C * t ^ 11 := by
    calc
      C * (t + t ^ 11) ≤ C * (2 * t ^ 11) :=
        Nat.mul_le_mul_left C hsum
      _ = 2 * C * t ^ 11 := by ring
  have hlarge : 2 * C * t ^ 11 < t ^ 12 := by
    have hp : 0 < t ^ 11 := pow_pos (by omega : 0 < t) 11
    calc
      2 * C * t ^ 11 < t * t ^ 11 :=
        Nat.mul_lt_mul_of_pos_right htgt hp
      _ = t ^ 12 := by ring
  exact (not_le_of_gt hlarge) ((hC t ht).trans hupper)

#print axioms vf919PrimaryCongruence_mul
#print axioms vf919PrimaryNormSeven_negativeRealWitness
#print axioms vf919SixEisensteinUnits_normOne
#print axioms vf919SixUnits_primaryNormSeven_onlyIdentity
#print axioms vf919AmplificationLowBand_U32_D64_fails
#print axioms vf919NoCoefficientOnlyFiveSixthsMomentGain

end RHLean.Analysis

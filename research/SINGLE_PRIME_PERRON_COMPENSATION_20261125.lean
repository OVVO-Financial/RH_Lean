import RHLean.Proof.LowWheelSurvivorFloorExpansion
import «research.GLOBAL_RETURNED_CORE_WEIGHTED_ALIGNMENT_INTERTWINING»

/-!
# Signed Euler compensation on the actual Perron-aligned carrier

A fresh-prime physical removal is a weighted floor difference on the old
survivor set. Its real centered version has a finite Boolean-face interval
bound. Finite Abel summation pays the *whole* monotone attenuation of this
signed prefix, without charging individual subsequent-prime flips separately.
The accompanying paper specializes the weights and gives the independent
linear main term and initial-owner aggregate bound. No terminal RH estimate
is assumed or claimed in this module.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Research.SinglePrimePerronCompensation

open RHLean.Arithmetic RHLean.Analysis RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- The actual old-wheel survivor population, including the unit. -/
def oldSites (r x : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 x).filter (lowWheelHighSurvivor r)

/-- The actual sites removed by introducing p. -/
def removedSites (p x : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 x).filter (fun n => lowWheelHighSurvivor (p - 1) n ∧ p ∣ n)

theorem old_survives_mul_iff {p : ℕ} (hp : p.Prime) (m : ℕ) :
    lowWheelHighSurvivor (p - 1) (p * m) ↔
      lowWheelHighSurvivor (p - 1) m := by
  unfold lowWheelHighSurvivor
  constructor
  · intro h q hq hd
    exact h q hq (dvd_mul_of_dvd_right hd p)
  · intro h q hq hd
    rcases (prime_of_mem_primesUpTo hq).dvd_mul.mp hd with hqp | hqm
    · have heq : q = p :=
        (Nat.prime_dvd_prime_iff_eq (prime_of_mem_primesUpTo hq) hp).mp hqp
      have hle : q ≤ p - 1 := (mem_primesUpTo.mp hq).2
      have hp0 := hp.pos
      omega
    · exact h q hq hqm

/-- Multiplicity is physical: the cofactor map is an exact bijection on
these sets, not a selection of independent abstract directions. -/
theorem oldSites_image_eq_removedSites {p : ℕ} (hp : p.Prime) (x : ℕ) :
    (oldSites (p - 1) (x / p)).image (fun m => p * m) = removedSites p x := by
  classical
  ext n
  simp only [oldSites, removedSites, Finset.mem_image, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨m, ⟨⟨hm0, hmx⟩, hs⟩, rfl⟩
    refine ⟨⟨Nat.mul_pos hp.pos hm0, ?_⟩, (old_survives_mul_iff hp m).2 hs, ⟨m, rfl⟩⟩
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp.pos).1 hmx
  · rintro ⟨⟨hn0, hnx⟩, hs, ⟨m, rfl⟩⟩
    have hm0 : 0 < m := by
      by_contra h
      have hm : m = 0 := by omega
      simp [hm] at hn0
    refine ⟨m, ⟨⟨hm0, ?_⟩, (old_survives_mul_iff hp m).1 hs⟩, rfl⟩
    apply (Nat.le_div_iff_mul_le hp.pos).2
    simpa [Nat.mul_comm] using hnx

def oldPhasePrefix (r : ℕ) (chi : ℕ → ℂ) (x : ℕ) : ℂ :=
  ∑ n ∈ oldSites r x, chi n

theorem removed_phase_sum {p : ℕ} (hp : p.Prime) (x : ℕ)
    (chi : ℕ → ℂ) (z : ℂ) (hz : ∀ m, chi (p * m) = z * chi m) :
    (∑ n ∈ removedSites p x, chi n) =
      z * oldPhasePrefix (p - 1) chi (x / p) := by
  classical
  rw [← oldSites_image_eq_removedSites hp x,
    Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp.pos h)]
  unfold oldPhasePrefix
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  exact hz m

/-- Actual centered physical removal equals the EXISTING arbitrary-ratio
Perron difference. For chi(n)=n^(-s), z=p^(-s). The extra p in the ratio
is necessary for the Euler centering 1/p, not a q² half-density. -/
theorem actual_centered_phase_eq_perron_difference {p : ℕ} (hp : p.Prime)
    (x : ℕ) (chi : ℕ → ℂ) (z : ℂ)
    (hz : ∀ m, chi (p * m) = z * chi m) :
    (∑ n ∈ removedSites p x, chi n) -
        (1 / (p : ℂ)) * oldPhasePrefix (p - 1) chi x =
      -(1 / (p : ℂ)) * weightedFreshPrimeDifference ((p : ℂ) * z) p
        (oldPhasePrefix (p - 1) chi) x := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hc : (1 / (p : ℂ)) * (p : ℂ) = 1 := one_div_mul_cancel hpc
  rw [removed_phase_sum hp x chi z hz, weightedFreshPrimeDifference_apply]
  calc
    _ = -(1 / (p : ℂ)) * oldPhasePrefix (p - 1) chi x +
        z * oldPhasePrefix (p - 1) chi (x / p) := by ring
    _ = -(1 / (p : ℂ)) * oldPhasePrefix (p - 1) chi x +
        ((1 / (p : ℂ)) * (p : ℂ)) * (z * oldPhasePrefix (p - 1) chi (x / p)) := by
      rw [hc, one_mul]
    _ = _ := by ring

/-- The later-prime square crossing uses precisely the existing arbitrary-ratio
floor operator on a prefix clipped at the actual cofactor upper endpoint. -/
theorem clipped_square_crossing_eq_perron_difference
    (q d M : ℕ) (F : ℕ → ℂ) :
    F (min M (q ^ 2 - 1)) - F (min M ((q ^ 2 - 1) / d)) =
      weightedFreshPrimeDifference 1 d (fun x => F (min M x)) (q ^ 2 - 1) := by
  simp [weightedFreshPrimeDifference_apply]

def oldCount (r x : ℕ) : ℝ := (oldSites r x).card

def centeredCount (r p x : ℕ) : ℝ :=
  oldCount r (x / p) - oldCount r x / (p : ℝ)

theorem removed_card_eq_oldCount {p : ℕ} (hp : p.Prime) (x : ℕ) :
    ((removedSites p x).card : ℝ) = oldCount (p - 1) (x / p) := by
  unfold oldCount
  rw [← oldSites_image_eq_removedSites hp x,
    Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left hp.pos h)]

/-- Apply the already-proved Boolean-cube physical survivor indicator and
the existing interval floor count on the positive prefix. -/
theorem oldCount_eq_faceFloor (r x : ℕ) :
    oldCount r x =
      ∑ t ∈ (primesUpTo r).powerset,
        (booleanCubeSign t : ℝ) * ((x / primeFaceProduct t : ℕ) : ℝ) := by
  classical
  have h : ((oldSites r x).card : ℤ) =
      ∑ t ∈ (primesUpTo r).powerset,
        booleanCubeSign t * ((x / primeFaceProduct t : ℕ) : ℤ) := by
    calc
      _ = ∑ n ∈ Finset.Ioc 0 x, lowWheelDivisorFaceSum r n := by
        unfold oldSites
        calc
          _ = ∑ n ∈ (Finset.Ioc 0 x).filter (lowWheelHighSurvivor r), (1 : ℤ) := by simp
          _ = ∑ n ∈ Finset.Ioc 0 x,
                if lowWheelHighSurvivor r n then (1 : ℤ) else 0 := by
            rw [Finset.sum_filter]
          _ = _ := by
            apply Finset.sum_congr rfl
            intro n _
            rw [lowWheelDivisorFaceSum_eq_survivorIndicator]
      _ = _ := by
        unfold lowWheelDivisorFaceSum
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro t ht
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [card_Ioc_filter_dvd_eq_div_sub_div 0 x (primeFaceProduct t)
          (primeFaceProduct_pos_of_mem_powerset ht)]
        simp [mul_comm]
  unfold oldCount
  exact_mod_cast h

/-- Each face's centered finite-difference defect is a bounded remainder,
including endpoints at exact multiples. -/
def floorDefect (p d x : ℕ) : ℝ :=
  ((x / (d * p) : ℕ) : ℝ) - ((x / d : ℕ) : ℝ) / (p : ℝ)

theorem floorDefect_eq_remainder {p : ℕ} (hp : 0 < p) (d x : ℕ) :
    floorDefect p d x = -((x / d % p : ℕ) : ℝ) / (p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : ((x / d % p : ℕ) : ℝ) + (p : ℝ) *
      (((x / d) / p : ℕ) : ℝ) = ((x / d : ℕ) : ℝ) := by
    exact_mod_cast Nat.mod_add_div (x / d) p
  unfold floorDefect
  rw [← Nat.div_div_eq_div_mul]
  apply (eq_div_iff hpR.ne').2
  rw [sub_mul, div_mul_cancel₀ _ hpR.ne']
  nlinarith

theorem floorDefect_bounds {p : ℕ} (hp : 0 < p) (d x : ℕ) :
    -1 ≤ floorDefect p d x ∧ floorDefect p d x ≤ 0 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hm : ((x / d % p : ℕ) : ℝ) < p := by
    exact_mod_cast Nat.mod_lt (x / d) hp
  have hm0 : 0 ≤ ((x / d % p : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [floorDefect_eq_remainder hp]
  constructor
  · apply (le_div_iff₀ hpR).2
    linarith
  · apply (div_le_iff₀ hpR).2
    linarith

theorem floorDefect_interval_le {p : ℕ} (hp : 0 < p) (d x y : ℕ) :
    |floorDefect p d x - floorDefect p d y| ≤ 1 := by
  obtain ⟨hx0, hx1⟩ := floorDefect_bounds hp d x
  obtain ⟨hy0, hy1⟩ := floorDefect_bounds hp d y
  rw [abs_le]
  constructor <;> linarith

theorem centeredCount_eq_faceFloor (r p x : ℕ) :
    centeredCount r p x =
      ∑ t ∈ (primesUpTo r).powerset,
        (booleanCubeSign t : ℝ) * floorDefect p (primeFaceProduct t) x := by
  unfold centeredCount
  rw [oldCount_eq_faceFloor, oldCount_eq_faceFloor, Finset.sum_div,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  unfold floorDefect
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm p (primeFaceProduct t)]
  ring

/-- Uniform interval bound for the actual centered signed removal prefix.
The cost is the Boolean face budget of the old wheel, not the number of
later-prime flips. -/
theorem centeredCount_interval_le (r : ℕ) {p : ℕ} (hp : 0 < p) (x y : ℕ) :
    |centeredCount r p x - centeredCount r p y| ≤
      (2 : ℝ) ^ (primesUpTo r).card := by
  rw [centeredCount_eq_faceFloor, centeredCount_eq_faceFloor, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ t ∈ (primesUpTo r).powerset,
        |(booleanCubeSign t : ℝ) * floorDefect p (primeFaceProduct t) x -
          (booleanCubeSign t : ℝ) * floorDefect p (primeFaceProduct t) y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ (primesUpTo r).powerset, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [← mul_sub, abs_mul]
      have hs : |(booleanCubeSign t : ℝ)| ≤ 1 := by
        have hm := ArithmeticFunction.abs_moebius_le_one (n := primeFaceProduct t)
        rw [moebius_primeFaceProduct_eq_booleanCubeSign t
          (fun q hq => prime_of_mem_primesUpTo ((Finset.mem_powerset.mp ht) hq))] at hm
        exact_mod_cast hm
      calc
        _ ≤ 1 * |floorDefect p (primeFaceProduct t) x -
            floorDefect p (primeFaceProduct t) y| :=
          mul_le_mul_of_nonneg_right hs (abs_nonneg _)
        _ ≤ 1 := by
          rw [one_mul]
          exact floorDefect_interval_le hp (primeFaceProduct t) x y
    _ = _ := by simp [Finset.card_powerset]

def finitePrefix (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, f i

theorem finitePrefix_succ (f : ℕ → ℝ) (n : ℕ) :
    finitePrefix f (n + 1) = finitePrefix f n + f n := by
  simp [finitePrefix, Finset.sum_range_succ]

theorem finitePrefix_difference (F : ℕ → ℝ) (b n : ℕ) :
    finitePrefix (fun i => F (b + i + 1) - F (b + i)) n =
      F (b + n) - F b := by
  induction n with
  | zero => simp [finitePrefix]
  | succ n ih =>
    rw [finitePrefix_succ, ih]
    ring

/-- Finite signed Abel identity, before any magnitude is taken. -/
theorem finiteAbel (f g : ℕ → ℝ) (n : ℕ) :
    finitePrefix (fun i => f i * g i) n =
      finitePrefix f n * g n +
        finitePrefix (fun i => finitePrefix f (i + 1) * (g i - g (i + 1))) n := by
  induction n with
  | zero => simp [finitePrefix]
  | succ n ih =>
    rw [finitePrefix_succ (fun i => f i * g i) n, ih,
      finitePrefix_succ (fun i => finitePrefix f (i + 1) * (g i - g (i + 1))) n,
      finitePrefix_succ f n]
    ring

theorem finiteAbel_variation_le (f g : ℕ → ℝ) (n : ℕ) (B : ℝ)
    (h : ∀ j ≤ n, |finitePrefix f j| ≤ B) :
    |finitePrefix (fun i => f i * g i) n| ≤
      B * (|g n| + finitePrefix (fun i => |g i - g (i + 1)|) n) := by
  rw [finiteAbel]
  calc
    _ ≤ |finitePrefix f n * g n| +
        |finitePrefix (fun i => finitePrefix f (i + 1) * (g i - g (i + 1))) n| :=
      abs_add_le _ _
    _ ≤ B * |g n| + B * finitePrefix (fun i => |g i - g (i + 1)|) n := by
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (h n le_rfl) (abs_nonneg _)
      · unfold finitePrefix
        rw [Finset.mul_sum]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        have hle : i + 1 ≤ n := by
          have := Finset.mem_range.mp hi
          omega
        exact mul_le_mul_of_nonneg_right (h (i + 1) hle) (abs_nonneg _)
    _ = _ := by ring

theorem finitePrefix_antitoneVariation (a : ℕ → ℝ) (ha : Antitone a) (n : ℕ) :
    finitePrefix (fun i => |a i - a (i + 1)|) n = a 0 - a n := by
  induction n with
  | zero => simp [finitePrefix]
  | succ n ih =>
    rw [finitePrefix_succ, ih,
      abs_of_nonneg (sub_nonneg.mpr (ha (Nat.le_succ n)))]
    ring

/-- All later-prime attenuation drops sum to the initial mass. This bound
does not multiply the prefix budget by the number of drops. -/
theorem finiteAbel_antitone_le (f a : ℕ → ℝ) (n : ℕ) (B : ℝ)
    (h : ∀ j ≤ n, |finitePrefix f j| ≤ B)
    (ha : Antitone a) (ha0 : ∀ i, 0 ≤ a i) :
    |finitePrefix (fun i => f i * a i) n| ≤ B * a 0 := by
  have hv := finitePrefix_antitoneVariation a ha n
  have hb := finiteAbel_variation_le f a n B h
  rw [abs_of_nonneg (ha0 n), hv] at hb
  calc
    _ ≤ B * (a n + (a 0 - a n)) := hb
    _ = _ := by ring

/-- Consecutive physical centered count increments, starting at b+1.
For prime p and r=p-1, removed_card_eq_oldCount identifies the removed
prefix with the actual cofactor population. -/
def centeredIncrement (r p b i : ℕ) : ℝ :=
  centeredCount r p (b + i + 1) - centeredCount r p (b + i)

theorem actual_centered_attenuated_prefix_le (r : ℕ) {p : ℕ} (hp : 0 < p)
    (b n : ℕ) (a : ℕ → ℝ) (ha : Antitone a) (ha0 : ∀ i, 0 ≤ a i) :
    |finitePrefix (fun i => centeredIncrement r p b i * a i) n| ≤
      (2 : ℝ) ^ (primesUpTo r).card * a 0 := by
  refine finiteAbel_antitone_le (centeredIncrement r p b) a n
    ((2 : ℝ) ^ (primesUpTo r).card) ?_ ha ha0
  intro j _
  unfold centeredIncrement
  rw [finitePrefix_difference]
  exact centeredCount_interval_le r hp (b + j) b

/-- The entire signed attenuated physical ledger can be tested against any
real finite-variation weight. For the V4 paper the weight is the clipped
logarithmic kernel after subtracting the independently convergent linear
main term. No logarithmic variation estimate is assumed here. -/
theorem actual_centered_weighted_compensation_le (r : ℕ) {p : ℕ} (hp : 0 < p)
    (b n : ℕ) (a g : ℕ → ℝ) (ha : Antitone a) (ha0 : ∀ i, 0 ≤ a i) :
    |finitePrefix (fun i => (centeredIncrement r p b i * a i) * g i) n| ≤
      ((2 : ℝ) ^ (primesUpTo r).card * a 0) *
        (|g n| + finitePrefix (fun i => |g i - g (i + 1)|) n) := by
  apply finiteAbel_variation_le
  intro j _
  exact actual_centered_attenuated_prefix_le r hp b j a ha ha0

#print axioms oldSites_image_eq_removedSites
#print axioms actual_centered_phase_eq_perron_difference
#print axioms centeredCount_interval_le
#print axioms finiteAbel
#print axioms actual_centered_attenuated_prefix_le
#print axioms actual_centered_weighted_compensation_le

end RHLean.Research.SinglePrimePerronCompensation

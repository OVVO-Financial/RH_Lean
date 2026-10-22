import Mathlib

/-!
# Independent weighted Co-Div decay: BR, BKV, and sextic defects

Every source condition is explicit. BR and BKV are *already extracted*
complex tier amplitudes; this module does not fabricate the original
ProbeLocal's three-way decomposition from its two-bill identity.

The BR bound uses a summable extra prime-norm exponent 77/25.
The BKV bound uses only an extra 33/100 (or 29/50 at the target contour);
its band sum may GROW, so BKV is NOT fully paid at the D-diagonal rate.

The final offdiagonal Gauss consumer takes a TRUE, physical, weighted
pairwise character estimate as a visible premise. The finite Cauchy-
Schwarz step after that premise is independent of the analytic proof.

Modulo-6 nonresonance holds for a pair of distinct ideal coordinates
at harmonics 1..5, but it does not assert source phase admission,
equal physical sector weights, or sixth-moment diagonal multiplicity 6
for nonprimitive harmonics 2,3,4.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- Finite weighted complex energy estimate before *any* phase averaging.
The only nontrivial input is the source pointwise factor bound.
No cardinality bound or restriction on the signs/phases of the terms. -/
theorem oai_weighted_complex_tier_cauchy
    {ι κ : Type*}
    (rows : Finset ι) (primes : Finset κ)
    (rho : ι → ℝ) (term : ι → κ → ℂ)
    (f g : κ → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hrho : ∀ u ∈ rows, 0 ≤ rho u)
    (hf : ∀ p ∈ primes, 0 ≤ f p)
    (hg : ∀ p ∈ primes, 0 ≤ g p)
    (hterm : ∀ u ∈ rows, ∀ p ∈ primes,
      ‖term u p‖ ≤ C * (f p * g p)) :
    (∑ u ∈ rows, rho u * ‖∑ p ∈ primes, term u p‖ ^ 2) ≤
      C ^ 2 * (∑ p ∈ primes, (f p) ^ 2) *
        (∑ p ∈ primes, (g p) ^ 2) * (∑ u ∈ rows, rho u) := by
  have hfg : 0 ≤ ∑ p ∈ primes, f p * g p := by
    apply Finset.sum_nonneg
    intro p hp
    exact mul_nonneg (hf p hp) (hg p hp)
  have hCS : (∑ p ∈ primes, f p * g p) ^ 2 ≤
      (∑ p ∈ primes, (f p) ^ 2) *
        (∑ p ∈ primes, (g p) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq primes f g
  have hpoint (u : ι) (hu : u ∈ rows) :
      ‖∑ p ∈ primes, term u p‖ ^ 2 ≤
        C ^ 2 * (∑ p ∈ primes, (f p) ^ 2) *
          (∑ p ∈ primes, (g p) ^ 2) := by
    have hnorm :
        ‖∑ p ∈ primes, term u p‖ ≤
          C * ∑ p ∈ primes, f p * g p := by
      calc
        _ ≤ ∑ p ∈ primes, ‖term u p‖ := norm_sum_le _ _
        _ ≤ ∑ p ∈ primes, C * (f p * g p) := by
          apply Finset.sum_le_sum
          intro p hp
          exact hterm u hu p hp
        _ = C * ∑ p ∈ primes, f p * g p := by
          rw [Finset.mul_sum]
    have hcNonneg : 0 ≤ C * ∑ p ∈ primes, f p * g p :=
      mul_nonneg hC hfg
    have hsquare :
        ‖∑ p ∈ primes, term u p‖ ^ 2 ≤
          (C * ∑ p ∈ primes, f p * g p) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hcNonneg).2 hnorm
    calc
      _ ≤ (C * ∑ p ∈ primes, f p * g p) ^ 2 := hsquare
      _ = C ^ 2 * (∑ p ∈ primes, f p * g p) ^ 2 := by ring
      _ ≤ C ^ 2 * ((∑ p ∈ primes, (f p) ^ 2) *
          (∑ p ∈ primes, (g p) ^ 2)) :=
        mul_le_mul_of_nonneg_left hCS (sq_nonneg C)
      _ = _ := by ring
  calc
    _ ≤ ∑ u ∈ rows, rho u *
          (C ^ 2 * (∑ p ∈ primes, (f p) ^ 2) *
            (∑ p ∈ primes, (g p) ^ 2)) := by
      apply Finset.sum_le_sum
      intro u hu
      exact mul_le_mul_of_nonneg_left (hpoint u hu) (hrho u hu)
    _ = (∑ u ∈ rows, rho u) *
          (C ^ 2 * (∑ p ∈ primes, (f p) ^ 2) *
            (∑ p ∈ primes, (g p) ^ 2)) := by
      rw [Finset.sum_mul]
    _ = C ^ 2 * (∑ p ∈ primes, (f p) ^ 2) *
          (∑ p ∈ primes, (g p) ^ 2) *
          (∑ u ∈ rows, rho u) := by ring

private theorem oai_tier_rpow_square
    (q a : ℝ) (hq : 0 < q) :
    (q ^ a) ^ 2 = q ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]
  congr 1
  ring

/-- Entire BR tier (INCLUDING all off-diagonal prime pairs) is paid
    by its true source exponent -483/200 = -2.415 and one application
    of weighted Cauchy--Schwarz. The extra exponent -77/25=-3.08
    has a summable prime-ideal mass. -/
theorem br_tier_global_energy_bound
    {ι κ : Type*}
    (rows : Finset ι) (primes : Finset κ)
    (rho : ι → ℝ) (q : κ → ℝ) (br : ι → κ → ℂ) (C : ℝ)
    (hC : 0 ≤ C)
    (hrho : ∀ u ∈ rows, 0 ≤ rho u)
    (hq : ∀ p ∈ primes, 0 < q p)
    (hbr : ∀ u ∈ rows, ∀ p ∈ primes,
      ‖br u p‖ ≤ C * q p ^ (-(483 / 200 : ℝ))) :
    (∑ u ∈ rows, rho u * ‖∑ p ∈ primes, br u p‖ ^ 2) ≤
      C ^ 2 * (∑ p ∈ primes, q p ^ (-(7 / 4 : ℝ))) *
        (∑ p ∈ primes, q p ^ (-(77 / 25 : ℝ))) *
        (∑ u ∈ rows, rho u) := by
  have hpow (p : κ) (hp : p ∈ primes) :
      q p ^ (-(483 / 200 : ℝ)) =
        q p ^ (-(7 / 8 : ℝ)) *
          q p ^ (-(77 / 50 : ℝ)) := by
    rw [← Real.rpow_add (hq p hp)]
    congr 1
    norm_num
  have h := oai_weighted_complex_tier_cauchy
    rows primes rho br
    (fun p => q p ^ (-(7 / 8 : ℝ)))
    (fun p => q p ^ (-(77 / 50 : ℝ))) C hC hrho
    (fun p hp => Real.rpow_nonneg (hq p hp).le _)
    (fun p hp => Real.rpow_nonneg (hq p hp).le _)
    (by
      intro u hu p hp
      rw [← hpow p hp]
      exact hbr u hu p hp)
  have hsum1 :
      (∑ p ∈ primes, (q p ^ (-(7 / 8 : ℝ))) ^ 2) =
        ∑ p ∈ primes, q p ^ (-(7 / 4 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [oai_tier_rpow_square _ _ (hq p hp)]
    congr 1
    ring
  have hsum2 :
      (∑ p ∈ primes, (q p ^ (-(77 / 50 : ℝ))) ^ 2) =
        ∑ p ∈ primes, q p ^ (-(77 / 25 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [oai_tier_rpow_square _ _ (hq p hp)]
    congr 1
    ring
  rw [hsum1, hsum2] at h
  exact h

/-- BKV tier gains a *relative* -33/100 exponent versus coherent
    prime counting, but the extra sum is NOT uniformly bounded in
    dyadic norm bands. No claim that BKV has been completely paid. -/
theorem bkv_tier_global_energy_bound
    {ι κ : Type*}
    (rows : Finset ι) (primes : Finset κ)
    (rho : ι → ℝ) (q : κ → ℝ) (bkv : ι → κ → ℂ) (C : ℝ)
    (hC : 0 ≤ C)
    (hrho : ∀ u ∈ rows, 0 ≤ rho u)
    (hq : ∀ p ∈ primes, 0 < q p)
    (hbkv : ∀ u ∈ rows, ∀ p ∈ primes,
      ‖bkv u p‖ ≤ C * q p ^ (-(26 / 25 : ℝ))) :
    (∑ u ∈ rows, rho u * ‖∑ p ∈ primes, bkv u p‖ ^ 2) ≤
      C ^ 2 * (∑ p ∈ primes, q p ^ (-(7 / 4 : ℝ))) *
        (∑ p ∈ primes, q p ^ (-(33 / 100 : ℝ))) *
        (∑ u ∈ rows, rho u) := by
  have hpow (p : κ) (hp : p ∈ primes) :
      q p ^ (-(26 / 25 : ℝ)) =
        q p ^ (-(7 / 8 : ℝ)) *
          q p ^ (-(33 / 200 : ℝ)) := by
    rw [← Real.rpow_add (hq p hp)]
    congr 1
    norm_num
  have h := oai_weighted_complex_tier_cauchy
    rows primes rho bkv
    (fun p => q p ^ (-(7 / 8 : ℝ)))
    (fun p => q p ^ (-(33 / 200 : ℝ))) C hC hrho
    (fun p hp => Real.rpow_nonneg (hq p hp).le _)
    (fun p hp => Real.rpow_nonneg (hq p hp).le _)
    (by
      intro u hu p hp
      rw [← hpow p hp]
      exact hbkv u hu p hp)
  have hsum1 :
      (∑ p ∈ primes, (q p ^ (-(7 / 8 : ℝ))) ^ 2) =
        ∑ p ∈ primes, q p ^ (-(7 / 4 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [oai_tier_rpow_square _ _ (hq p hp)]
    congr 1
    ring
  have hsum2 :
      (∑ p ∈ primes, (q p ^ (-(33 / 200 : ℝ))) ^ 2) =
        ∑ p ∈ primes, q p ^ (-(33 / 100 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [oai_tier_rpow_square _ _ (hq p hp)]
    congr 1
    ring
  rw [hsum1, hsum2] at h
  exact h

/-- At a=7/8 and e=0, w.re=1/8 and the BKV exponent is -233/200.
    The new cross-prime loss is -29/50 instead of -33/100.
    Strict e>0 in the original source is handled by a limiting bound
    only when uniformity in e is independently established. -/
theorem bkv_tier_boundary_energy_bound
    {ι κ : Type*}
    (rows : Finset ι) (primes : Finset κ)
    (rho : ι → ℝ) (q : κ → ℝ) (bkv : ι → κ → ℂ) (C : ℝ)
    (hC : 0 ≤ C)
    (hrho : ∀ u ∈ rows, 0 ≤ rho u)
    (hq : ∀ p ∈ primes, 0 < q p)
    (hbkv : ∀ u ∈ rows, ∀ p ∈ primes,
      ‖bkv u p‖ ≤ C * q p ^ (-(233 / 200 : ℝ))) :
    (∑ u ∈ rows, rho u * ‖∑ p ∈ primes, bkv u p‖ ^ 2) ≤
      C ^ 2 * (∑ p ∈ primes, q p ^ (-(7 / 4 : ℝ))) *
        (∑ p ∈ primes, q p ^ (-(29 / 50 : ℝ))) *
        (∑ u ∈ rows, rho u) := by
  have hpow (p : κ) (hp : p ∈ primes) :
      q p ^ (-(233 / 200 : ℝ)) =
        q p ^ (-(7 / 8 : ℝ)) *
          q p ^ (-(29 / 100 : ℝ)) := by
    rw [← Real.rpow_add (hq p hp)]
    congr 1
    norm_num
  have h := oai_weighted_complex_tier_cauchy
    rows primes rho bkv
    (fun p => q p ^ (-(7 / 8 : ℝ)))
    (fun p => q p ^ (-(29 / 100 : ℝ))) C hC hrho
    (fun p hp => Real.rpow_nonneg (hq p hp).le _)
    (fun p hp => Real.rpow_nonneg (hq p hp).le _)
    (by
      intro u hu p hp
      rw [← hpow p hp]
      exact hbkv u hu p hp)
  have hsum1 :
      (∑ p ∈ primes, (q p ^ (-(7 / 8 : ℝ))) ^ 2) =
        ∑ p ∈ primes, q p ^ (-(7 / 4 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [oai_tier_rpow_square _ _ (hq p hp)]
    congr 1
    ring
  have hsum2 :
      (∑ p ∈ primes, (q p ^ (-(29 / 100 : ℝ))) ^ 2) =
        ∑ p ∈ primes, q p ^ (-(29 / 50 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [oai_tier_rpow_square _ _ (hq p hp)]
    congr 1
    ring
  rw [hsum1, hsum2] at h
  exact h

/-- Algebraic sextic nonresonance for distinct *prime-ideal coordinates*:
    1..5 never gives an exponent divisible by 6. This is NOT a
    nonuniform physical Gauss bound or proof of actual source phases. -/
def oaiDistinctPrimeHarmonicValuation
    {κ : Type*} [DecidableEq κ] (p q : κ) (m : ℕ) (r : κ) : ℕ :=
  (if r = p then m else 0) + (if r = q then 6 - m else 0)

theorem distinct_prime_harmonic_nonresonant
    {κ : Type*} [DecidableEq κ] (p q : κ) (hpq : p ≠ q)
    (m : ℕ) (hm : 1 ≤ m) (hm5 : m ≤ 5) :
    ¬ (6 : ℤ) ∣ ((oaiDistinctPrimeHarmonicValuation p q m p : ℕ) : ℤ) := by
  have hp : oaiDistinctPrimeHarmonicValuation p q m p = m := by
    simp [oaiDistinctPrimeHarmonicValuation, hpq]
  rw [hp]
  omega

/-- IMPORTANT COUNTEREXAMPLE to an automatic 3! sixth-moment diagonal
    for nonprimitive sextic harmonics. The 2nd harmonic taken three
    times is a TRIVIAL local character (6 divides 3*2), even with no
    matching prime on the conjugate side. The 3rd harmonic is likewise
    trivial when repeated twice (6 divides 2*3). -/
theorem sextic_sixth_moment_nonprimitive_repeat_collisions :
    (6 : ℤ) ∣ (3 * (2 : ℤ)) ∧
      (6 : ℤ) ∣ (2 * (3 : ℤ)) := by
  constructor <;> norm_num

/-- For the original compensated leading cubic harmonic m=4,
    a sixth-moment resonance among 3 plus and 3 minus prime slots
    forces equality of each local occupancy, EXCEPT for the pure-cube
    deviations 3-to-0 and 0-to-3. This is the exact local collision
    classification that replaces the false universal 3! rule. -/
theorem cubic_m4_three_slot_local_collision_classification
    (c d : ℕ) (hc : c ≤ 3) (hd : d ≤ 3)
    (hphase : (6 : ℤ) ∣ (4 : ℤ) * ((c : ℤ) - (d : ℤ))) :
    c = d ∨ (c = 3 ∧ d = 0) ∨ (c = 0 ∧ d = 3) := by
  omega

/-- The additional resonant pure-cube packet pairs are absolutely
    payable by cube coefficient mass even though their number is O(N²).
    No Gauss/Poisson or incomplete row hypothesis is used. -/
theorem cubic_repeated_prime_offdiagonal_mass_bound
    {κ : Type*} [DecidableEq κ]
    (primes : Finset κ) (a : κ → ℂ) :
    ‖∑ p ∈ primes, ∑ q ∈ primes.erase p,
        (a p) ^ 3 * star ((a q) ^ 3)‖ ≤
      (∑ p ∈ primes, ‖a p‖ ^ 3) ^ 2 := by
  have hnonneg (p : κ) : 0 ≤ ‖a p‖ ^ 3 := by positivity
  calc
    _ ≤ ∑ p ∈ primes,
        ‖∑ q ∈ primes.erase p,
          (a p) ^ 3 * star ((a q) ^ 3)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ primes, ∑ q ∈ primes.erase p,
          ‖(a p) ^ 3 * star ((a q) ^ 3)‖ := by
      apply Finset.sum_le_sum
      intro p hp
      exact norm_sum_le _ _
    _ = ∑ p ∈ primes, ∑ q ∈ primes.erase p,
          ‖a p‖ ^ 3 * ‖a q‖ ^ 3 := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      simp only [norm_mul, norm_star, norm_pow]
    _ ≤ ∑ p ∈ primes, ∑ q ∈ primes,
          ‖a p‖ ^ 3 * ‖a q‖ ^ 3 := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.erase_subset p primes)
      intro q hq _hnot
      exact mul_nonneg (hnonneg p) (hnonneg q)
    _ = (∑ p ∈ primes, ‖a p‖ ^ 3) ^ 2 := by
      rw [← Finset.sum_mul_sum]
      ring

/-- Conditional GAUSS consumer for the offdiagonal D-tier: its input
    is a *real* physical weighted, nontrivial pair estimate.
    No complete-residue or uniformly distributed row assumption is
    manufactured. The finite pair sum costs only the two prime-norm
    sums supplied by Cauchy--Schwarz. -/
theorem d_tier_gauss_off_diagonal_bound
    {κ : Type*} [DecidableEq κ]
    (primes : Finset κ) (q : κ → ℝ)
    (cross : κ → κ → ℂ) (C : ℝ)
    (hC : 0 ≤ C)
    (hq : ∀ p ∈ primes, 0 < q p)
    (hGauss : ∀ p ∈ primes, ∀ r ∈ primes, p ≠ r →
      ‖cross p r‖ ≤ C *
        (q p ^ (-(11 / 8 : ℝ)) * q r ^ (-(11 / 8 : ℝ)))) :
    ‖∑ p ∈ primes, ∑ r ∈ primes.erase p, cross p r‖ ≤
      C * (∑ p ∈ primes, q p ^ (-(7 / 4 : ℝ))) *
        (∑ p ∈ primes, q p ^ (-(1 : ℝ))) := by
  let a : κ → ℝ := fun p => q p ^ (-(11 / 8 : ℝ))
  let B : ℝ := ∑ p ∈ primes, a p
  have ha (p : κ) (hp : p ∈ primes) : 0 ≤ a p :=
    Real.rpow_nonneg (hq p hp).le _
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg (fun p hp => ha p hp)
  have hRow (p : κ) (hp : p ∈ primes) :
      ‖∑ r ∈ primes.erase p, cross p r‖ ≤ C * a p * B := by
    calc
      _ ≤ ∑ r ∈ primes.erase p, ‖cross p r‖ := norm_sum_le _ _
      _ ≤ ∑ r ∈ primes.erase p, C * (a p * a r) := by
        apply Finset.sum_le_sum
        intro r hr
        have hrS : r ∈ primes := (Finset.mem_erase.mp hr).2
        have hne : p ≠ r := (Finset.mem_erase.mp hr).1.symm
        exact hGauss p hp r hrS hne
      _ ≤ ∑ r ∈ primes, C * (a p * a r) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset p primes)
        intro r hr _hrNot
        exact mul_nonneg hC (mul_nonneg (ha p hp) (ha r hr))
      _ = C * a p * B := by
        dsimp [B]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
  have hFull : ‖∑ p ∈ primes, ∑ r ∈ primes.erase p, cross p r‖ ≤
      C * B ^ 2 := by
    calc
      _ ≤ ∑ p ∈ primes,
          ‖∑ r ∈ primes.erase p, cross p r‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ primes, C * a p * B := by
        apply Finset.sum_le_sum
        intro p hp
        exact hRow p hp
      _ = ∑ p ∈ primes, (C * B) * a p := by
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ = (C * B) * B := by
         change (∑ p ∈ primes, (C * B) * a p) =
           (C * B) * (∑ p ∈ primes, a p)
         conv_rhs => rw [Finset.mul_sum]
      _ = C * B ^ 2 := by ring
  have hSplit (p : κ) (hp : p ∈ primes) :
      a p = q p ^ (-(7 / 8 : ℝ)) *
        q p ^ (-(1 / 2 : ℝ)) := by
    dsimp [a]
    rw [← Real.rpow_add (hq p hp)]
    congr 1
    norm_num
  have hCauchy :
      B ^ 2 ≤ (∑ p ∈ primes, q p ^ (-(7 / 4 : ℝ))) *
        (∑ p ∈ primes, q p ^ (-(1 : ℝ))) := by
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq primes
      (fun p => q p ^ (-(7 / 8 : ℝ)))
      (fun p => q p ^ (-(1 / 2 : ℝ)))
    have hBsum : B = ∑ p ∈ primes,
        q p ^ (-(7 / 8 : ℝ)) * q p ^ (-(1 / 2 : ℝ)) := by
      dsimp [B]
      apply Finset.sum_congr rfl
      intro p hp
      exact hSplit p hp
    rw [← hBsum] at hCS
    have hF :
        (∑ p ∈ primes, (q p ^ (-(7 / 8 : ℝ))) ^ 2) =
          ∑ p ∈ primes, q p ^ (-(7 / 4 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [oai_tier_rpow_square _ _ (hq p hp)]
      congr 1
      ring
    have hG :
        (∑ p ∈ primes, (q p ^ (-(1 / 2 : ℝ))) ^ 2) =
          ∑ p ∈ primes, q p ^ (-(1 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [oai_tier_rpow_square _ _ (hq p hp)]
      congr 1
      ring
    simpa only [hF, hG] using hCS
  calc
    _ ≤ C * B ^ 2 := hFull
    _ ≤ C * ((∑ p ∈ primes, q p ^ (-(7 / 4 : ℝ))) *
        (∑ p ∈ primes, q p ^ (-(1 : ℝ)))) :=
      mul_le_mul_of_nonneg_left hCauchy hC
    _ = _ := by ring

end RHLean.Analysis

#print axioms RHLean.Analysis.oai_weighted_complex_tier_cauchy
#print axioms RHLean.Analysis.br_tier_global_energy_bound
#print axioms RHLean.Analysis.bkv_tier_global_energy_bound
#print axioms RHLean.Analysis.bkv_tier_boundary_energy_bound
#print axioms RHLean.Analysis.distinct_prime_harmonic_nonresonant
#print axioms RHLean.Analysis.sextic_sixth_moment_nonprimitive_repeat_collisions
#print axioms RHLean.Analysis.cubic_m4_three_slot_local_collision_classification
#print axioms RHLean.Analysis.cubic_repeated_prime_offdiagonal_mass_bound
#print axioms RHLean.Analysis.d_tier_gauss_off_diagonal_bound

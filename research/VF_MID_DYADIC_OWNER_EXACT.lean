import Mathlib
import «research.VF_MID_DYADIC_PREFIX_OWNER»

/-!
# Exact chronological-owner form of the VF dyadic late correction

This file completes the combinatorial side of the VF-only dyadic reduction.
The four-endpoint prefix supply is proved equal to the sum of physical prefix
survivors over the adjacent square blocks.  The difference between those
survivors and the actual primes is then partitioned exactly by least prime
factor.  Thus the dyadic late-removal term T is not an abstract residual:
it is literally the cumulative chronological owner census.

No Li/PNT approximation or asymptotic input is used.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-! ## Endpoint counting really is the sum of physical square-block survivors -/

/-- Prefix-wheel survivors in an arbitrary natural interval (A,B]. -/
def vfMidPrefixWheelIntervalCounting (z A B : ℕ) : ℕ := by
  classical
  exact ((Finset.Ioc A B).filter (lowWheelHighSurvivor z)).card

/-- Splitting (0,B] at A exactly splits the fixed-prefix survivor count. -/
theorem vfMidPrefixWheelCounting_add_intervalCounting
    (z A B : ℕ) (hAB : A ≤ B) :
    vfMidPrefixWheelCounting z A +
        vfMidPrefixWheelIntervalCounting z A B =
      vfMidPrefixWheelCounting z B := by
  classical
  let SA : Finset ℕ :=
    (Finset.Ioc 0 A).filter (lowWheelHighSurvivor z)
  let SAB : Finset ℕ :=
    (Finset.Ioc A B).filter (lowWheelHighSurvivor z)
  let SB : Finset ℕ :=
    (Finset.Ioc 0 B).filter (lowWheelHighSurvivor z)
  have hdisj : Disjoint SA SAB := by
    rw [Finset.disjoint_left]
    intro n hnA hnAB
    have hnAI := (Finset.mem_filter.mp hnA).1
    have hnABI := (Finset.mem_filter.mp hnAB).1
    have hna := (Finset.mem_Ioc.mp hnAI).2
    have han := (Finset.mem_Ioc.mp hnABI).1
    omega
  have hunion : SA ∪ SAB = SB := by
    ext n
    simp only [SA, SAB, SB, Finset.mem_union, Finset.mem_filter,
      Finset.mem_Ioc]
    constructor
    · rintro (⟨⟨h0n, hnA⟩, hs⟩ | ⟨⟨hAn, hnB⟩, hs⟩)
      · exact ⟨⟨h0n, hnA.trans hAB⟩, hs⟩
      · exact ⟨⟨by omega, hnB⟩, hs⟩
    · rintro ⟨⟨h0n, hnB⟩, hs⟩
      by_cases hnA : n ≤ A
      · exact Or.inl ⟨⟨h0n, hnA⟩, hs⟩
      · exact Or.inr ⟨⟨lt_of_not_ge hnA, hnB⟩, hs⟩
  change SA.card + SAB.card = SB.card
  calc
    SA.card + SAB.card = (SA ∪ SAB).card := by
      symm
      exact Finset.card_union_of_disjoint hdisj
    _ = SB.card := by rw [hunion]

/-- A square survives a fixed low-prime wheel exactly when its root survives. -/
theorem lowWheelHighSurvivor_sq_iff
    (z n : ℕ) :
    lowWheelHighSurvivor z (n ^ 2) ↔
      lowWheelHighSurvivor z n := by
  constructor
  · intro hs p hp hpd
    apply hs p hp
    rw [pow_two]
    exact dvd_mul_of_dvd_left hpd n
  · intro hs p hp hpd
    have hpPrime := prime_of_mem_primesUpTo hp
    apply hs p hp
    exact hpPrime.dvd_of_dvd_pow hpd

/-- The closed square interval consists of the open physical square carrier
plus its upper square; the corresponding root interval carries exactly the
same one-site survival indicator. -/
theorem vfMidPrefixWheelIntervalCounting_square_eq_block_add_root
    (z R : ℕ) :
    vfMidPrefixWheelIntervalCounting z (R ^ 2) ((R + 1) ^ 2) =
      (vfMidSquarePrefixWheelSurvivors z R).card +
        vfMidPrefixWheelIntervalCounting z R (R + 1) := by
  classical
  have hsquareExpand :
      (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by
    ring
  have hsqIoc :
      Finset.Ioc (R ^ 2) ((R + 1) ^ 2) =
        insert ((R + 1) ^ 2)
          (Finset.Ioo (R ^ 2) ((R + 1) ^ 2)) := by
    rw [hsquareExpand]
    ext n
    simp
    omega
  have hrootIoc :
      Finset.Ioc R (R + 1) = {R + 1} := by
    ext n
    simp
  unfold vfMidPrefixWheelIntervalCounting
    vfMidSquarePrefixWheelSurvivors vfMidSquareWheelSites
  rw [hsqIoc, hrootIoc]
  have hupperNot :
      (R + 1) ^ 2 ∉
        (Finset.Ioo (R ^ 2) ((R + 1) ^ 2)).filter
          (lowWheelHighSurvivor z) := by
    simp
  by_cases hroot : lowWheelHighSurvivor z (R + 1)
  · have hsquare :
        lowWheelHighSurvivor z ((R + 1) ^ 2) :=
      (lowWheelHighSurvivor_sq_iff z (R + 1)).2 hroot
    have hrootFilter :
        ({R + 1} : Finset ℕ).filter (lowWheelHighSurvivor z) =
          {R + 1} := by
      ext n
      constructor
      · intro hn
        exact (Finset.mem_filter.mp hn).1
      · intro hn
        have hnEq : n = R + 1 := by
          simpa using hn
        subst n
        exact Finset.mem_filter.mpr ⟨by simp, hroot⟩
    rw [Finset.filter_insert]
    simp only [hsquare, if_true]
    rw [Finset.card_insert_of_notMem hupperNot, hrootFilter]
    simp
  · have hsquare :
        ¬ lowWheelHighSurvivor z ((R + 1) ^ 2) := by
      intro h
      exact hroot ((lowWheelHighSurvivor_sq_iff z (R + 1)).1 h)
    have hrootFilter :
        ({R + 1} : Finset ℕ).filter (lowWheelHighSurvivor z) =
          ∅ := by
      ext n
      constructor
      · intro hn
        have hnData := Finset.mem_filter.mp hn
        have hnEq : n = R + 1 := by
          simpa using hnData.1
        subst n
        exact (hroot hnData.2).elim
      · intro hn
        simp at hn
    rw [Finset.filter_insert]
    simp only [hsquare, if_false]
    rw [hrootFilter]
    simp

/-- One physical square-block prefix survivor count is exactly the four
endpoint difference F_z((R+1)^2)-F_z(R^2)-F_z(R+1)+F_z(R). -/
theorem vfMidSquarePrefixWheelSurvivors_card_eq_fourEndpoints
    (z R : ℕ) :
    ((vfMidSquarePrefixWheelSurvivors z R).card : ℝ) =
      (vfMidPrefixWheelCounting z ((R + 1) ^ 2) : ℝ) -
      (vfMidPrefixWheelCounting z (R ^ 2) : ℝ) -
      (vfMidPrefixWheelCounting z (R + 1) : ℝ) +
      (vfMidPrefixWheelCounting z R : ℝ) := by
  have hsq :=
    vfMidPrefixWheelCounting_add_intervalCounting
      z (R ^ 2) ((R + 1) ^ 2)
        (Nat.pow_le_pow_left (by omega : R ≤ R + 1) 2)
  have hroot :=
    vfMidPrefixWheelCounting_add_intervalCounting
      z R (R + 1) (by omega)
  have hsplit :=
    vfMidPrefixWheelIntervalCounting_square_eq_block_add_root z R
  have hsqR :
      (vfMidPrefixWheelCounting z (R ^ 2) : ℝ) +
          (vfMidPrefixWheelIntervalCounting z (R ^ 2) ((R + 1) ^ 2) : ℝ) =
        (vfMidPrefixWheelCounting z ((R + 1) ^ 2) : ℝ) := by
    exact_mod_cast hsq
  have hrootR :
      (vfMidPrefixWheelCounting z R : ℝ) +
          (vfMidPrefixWheelIntervalCounting z R (R + 1) : ℝ) =
        (vfMidPrefixWheelCounting z (R + 1) : ℝ) := by
    exact_mod_cast hroot
  have hsplitR :
      (vfMidPrefixWheelIntervalCounting z (R ^ 2) ((R + 1) ^ 2) : ℝ) =
        (vfMidSquarePrefixWheelSurvivors z R).card +
          (vfMidPrefixWheelIntervalCounting z R (R + 1) : ℝ) := by
    exact_mod_cast hsplit
  linarith

/-- Endpoint potential whose discrete derivative is one square-block prefix
survivor population. -/
def vfMidPrefixWheelSquarePotential (z R : ℕ) : ℝ :=
  (vfMidPrefixWheelCounting z (R ^ 2) : ℝ) -
    (vfMidPrefixWheelCounting z R : ℝ)

theorem vfMidSquarePrefixWheelSurvivors_card_eq_potential_increment
    (z R : ℕ) :
    ((vfMidSquarePrefixWheelSurvivors z R).card : ℝ) =
      vfMidPrefixWheelSquarePotential z (R + 1) -
        vfMidPrefixWheelSquarePotential z R := by
  rw [vfMidSquarePrefixWheelSurvivors_card_eq_fourEndpoints]
  unfold vfMidPrefixWheelSquarePotential
  ring

/-- The four-endpoint prefix expression telescopes exactly across adjacent
square blocks.  This is the physical version of the endpoint cancellation. -/
theorem vfMidDyadicPrefixSupply_eq_sum_prefixWheelCards
    (z A B : ℕ) (hAB : A ≤ B) :
    vfMidDyadicPrefixSupply z A B =
      ∑ r ∈ Finset.Ico A B,
        ((vfMidSquarePrefixWheelSurvivors z r).card : ℝ) := by
  calc
    vfMidDyadicPrefixSupply z A B =
        vfMidPrefixWheelSquarePotential z B -
          vfMidPrefixWheelSquarePotential z A := by
            unfold vfMidDyadicPrefixSupply
              vfMidPrefixWheelSquarePotential
            ring
    _ = ∑ r ∈ Finset.Ico A B,
          (vfMidPrefixWheelSquarePotential z (r + 1) -
            vfMidPrefixWheelSquarePotential z r) := by
          symm
          exact Finset.sum_Ico_sub
            (vfMidPrefixWheelSquarePotential z) hAB
    _ = ∑ r ∈ Finset.Ico A B,
          ((vfMidSquarePrefixWheelSurvivors z r).card : ℝ) := by
          apply Finset.sum_congr rfl
          intro r _hr
          symm
          exact
            vfMidSquarePrefixWheelSurvivors_card_eq_potential_increment z r

/-! ## The prime endpoint difference telescopes over the same square blocks -/

def vfMidPrimeSquarePotential (R : ℕ) : ℝ :=
  (Nat.primeCounting (R ^ 2) : ℝ)

theorem vfMidIntegerBlockPrimeSupply_cast_eq_potential_increment
    (R : ℕ) :
    (vfMidIntegerBlockPrimeSupply R : ℝ) =
      vfMidPrimeSquarePotential (R + 1) -
        vfMidPrimeSquarePotential R := by
  have h := vfMidIntegerBlockPrimeSupply_add_primeCounting R
  have hR :
      (vfMidIntegerBlockPrimeSupply R : ℝ) +
          (Nat.primeCounting (R ^ 2) : ℝ) =
        (Nat.primeCounting ((R + 1) ^ 2) : ℝ) := by
    exact_mod_cast h
  unfold vfMidPrimeSquarePotential
  linarith

theorem vfMidDyadicPrimeSupply_eq_sum_blockPrimeSupply
    (A B : ℕ) (hAB : A ≤ B) :
    vfMidDyadicPrimeSupply A B =
      ∑ r ∈ Finset.Ico A B,
        (vfMidIntegerBlockPrimeSupply r : ℝ) := by
  calc
    vfMidDyadicPrimeSupply A B =
        vfMidPrimeSquarePotential B -
          vfMidPrimeSquarePotential A := by
            rfl
    _ = ∑ r ∈ Finset.Ico A B,
          (vfMidPrimeSquarePotential (r + 1) -
            vfMidPrimeSquarePotential r) := by
          symm
          exact Finset.sum_Ico_sub vfMidPrimeSquarePotential hAB
    _ = ∑ r ∈ Finset.Ico A B,
          (vfMidIntegerBlockPrimeSupply r : ℝ) := by
          apply Finset.sum_congr rfl
          intro r _hr
          symm
          exact vfMidIntegerBlockPrimeSupply_cast_eq_potential_increment r

/-- Before invoking least-prime-factor ownership, T is already the signed sum
of the physical per-block excess prefix survivors over actual primes. -/
theorem vfMidDyadicLateRemoval_eq_sum_blockExcess
    (z A B : ℕ) (hAB : A ≤ B) :
    vfMidDyadicLateRemoval z A B =
      ∑ r ∈ Finset.Ico A B,
        (((vfMidSquarePrefixWheelSurvivors z r).card : ℝ) -
          (vfMidIntegerBlockPrimeSupply r : ℝ)) := by
  unfold vfMidDyadicLateRemoval
  rw [vfMidDyadicPrefixSupply_eq_sum_prefixWheelCards z A B hAB,
    vfMidDyadicPrimeSupply_eq_sum_blockPrimeSupply A B hAB,
    ← Finset.sum_sub_distrib]

/-! ## One terminal wheel resolves an entire short square run -/

/-- If the terminal root B still lies below the first square A^2, then on
every block r in [A,B) the single wheel through B has exactly the actual
prime survivors. Composites were already killed by the smaller wheel through
r, while every prime site lies above r^2 >= A^2 > B and therefore cannot
equal any prime coordinate of the terminal wheel. -/
theorem vfMidSquarePrefixWheelSurvivors_terminal_eq_primes
    {A B r : ℕ} (hA : 2 ≤ A)
    (hr : r ∈ Finset.Ico A B)
    (hterminal : B < A ^ 2) :
    vfMidSquarePrefixWheelSurvivors B r =
      vfMidSquareWheelPrimes r := by
  classical
  have hAr : A ≤ r := (Finset.mem_Ico.mp hr).1
  have hrB : r < B := (Finset.mem_Ico.mp hr).2
  have hr2 : 2 ≤ r := hA.trans hAr
  have hAsqRsq : A ^ 2 ≤ r ^ 2 :=
    Nat.pow_le_pow_left hAr 2
  have hBltRsq : B < r ^ 2 :=
    hterminal.trans_le hAsqRsq
  ext n
  simp only [vfMidSquarePrefixWheelSurvivors,
    vfMidSquareWheelPrimes, Finset.mem_filter]
  constructor
  · rintro ⟨hnSite, hsurvB⟩
    refine ⟨hnSite, ?_⟩
    apply (vfMidSquareBand_commonWheelSurvivor_iff_prime hr2 hnSite).1
    intro p hpR hpd
    have hpData := mem_primesUpTo.mp hpR
    have hpB : p ∈ primesUpTo B :=
      mem_primesUpTo.mpr
        ⟨hpData.1, hpData.2.trans hrB.le⟩
    exact hsurvB p hpB hpd
  · rintro ⟨hnSite, hnPrime⟩
    refine ⟨hnSite, ?_⟩
    intro p hpB hpd
    have hpPrime : p.Prime :=
      prime_of_mem_primesUpTo hpB
    have hpLeB : p ≤ B :=
      (mem_primesUpTo.mp hpB).2
    have hpn : p = n :=
      (Nat.prime_dvd_prime_iff_eq hpPrime hnPrime).mp hpd
    have hnI := Finset.mem_Ioo.mp hnSite
    subst p
    omega

/-- Terminal-wheel square-run identity.

On any short square run with A <= B < A^2, the whole cumulative actual prime
population is already the four-endpoint survivor supply of the single wheel
through the terminal root B. The changing per-block wheels disappear. -/
theorem vfMidDyadicPrefixSupply_terminal_eq_primeSupply
    {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B)
    (hterminal : B < A ^ 2) :
    vfMidDyadicPrefixSupply B A B =
      vfMidDyadicPrimeSupply A B := by
  rw [vfMidDyadicPrefixSupply_eq_sum_prefixWheelCards B A B hAB,
    vfMidDyadicPrimeSupply_eq_sum_blockPrimeSupply A B hAB]
  apply Finset.sum_congr rfl
  intro r hr
  have hset :=
    vfMidSquarePrefixWheelSurvivors_terminal_eq_primes
      hA hr hterminal
  have hcard :
      (vfMidSquarePrefixWheelSurvivors B r).card =
        vfMidIntegerBlockPrimeSupply r := by
    unfold vfMidIntegerBlockPrimeSupply
    rw [vfMidDirectPrimeBand_eq_squareWheelPrimes]
    exact congrArg Finset.card hset
  exact_mod_cast hcard

/-- Consequently the cumulative prime supply over the entire square run has an
exact terminal-wheel density-plus-four-endpoint-error formula. This is the
direct carrier for a run-level lower-bound attack: the block count has vanished
before any absolute value is taken. -/
theorem vfMidDyadicPrimeSupply_sub_terminalDensity_eq_fourEndpointErrors
    {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B)
    (hterminal : B < A ^ 2) :
    vfMidDyadicPrimeSupply A B -
        vfMidPrefixWheelDensity B * vfMidDyadicInteriorLength A B =
      ((vfMidPrefixWheelCounting B (B ^ 2) : ℝ) -
          vfMidPrefixWheelDensity B * ((B : ℝ) ^ 2)) -
      ((vfMidPrefixWheelCounting B (A ^ 2) : ℝ) -
          vfMidPrefixWheelDensity B * ((A : ℝ) ^ 2)) -
      ((vfMidPrefixWheelCounting B B : ℝ) -
          vfMidPrefixWheelDensity B * (B : ℝ)) +
      ((vfMidPrefixWheelCounting B A : ℝ) -
          vfMidPrefixWheelDensity B * (A : ℝ)) := by
  rw [← vfMidDyadicPrefixSupply_terminal_eq_primeSupply
    hA hAB hterminal]
  exact
    vfMidDyadicPrefixSupply_sub_density_eq_four_endpoint_errors
      B A B

/-! ## Exact least-prime-factor ownership of the remaining removals -/

/-- Composite prefix survivors in one physical square block. -/
def vfMidSquareBandPrefixCompositeSurvivors (z R : ℕ) : Finset ℕ :=
  (vfMidSquareBandComposites R).filter (lowWheelHighSurvivor z)

/-- On a genuine square-band composite, surviving the fixed prefix through z
is exactly the statement that its least prime factor is larger than z. -/
theorem vfMidSquareBandComposite_survives_prefix_iff_minFac_gt
    {z R n : ℕ} (hR : 2 ≤ R)
    (hn : n ∈ vfMidSquareBandComposites R) :
    lowWheelHighSurvivor z n ↔ z < n.minFac := by
  have hnSite := (Finset.mem_filter.mp hn).1
  have hnI := Finset.mem_Ioo.mp hnSite
  have hnOne : n ≠ 1 := by
    have hR2 : 1 < R ^ 2 := by nlinarith
    omega
  have hminPrime : n.minFac.Prime := Nat.minFac_prime hnOne
  have hminDvd : n.minFac ∣ n := Nat.minFac_dvd n
  constructor
  · intro hs
    by_contra hnot
    have hminz : n.minFac ≤ z := by omega
    have hmem :
        n.minFac ∈ primesUpTo z :=
      mem_primesUpTo_of_prime_le hminPrime hminz
    exact hs n.minFac hmem hminDvd
  · intro hz p hpMem hpDvd
    have hpPrime := prime_of_mem_primesUpTo hpMem
    have hpz := (mem_primesUpTo.mp hpMem).2
    have hminle : n.minFac ≤ p :=
      Nat.minFac_le_of_dvd hpPrime.two_le hpDvd
    omega

/-- Owners that remain after the fixed prefix: precisely least-prime owners
larger than z. -/
def vfMidSquareBandLateOwnerPrimes (z R : ℕ) : Finset ℕ :=
  (vfMidSquareBandOwnerPrimes R).filter (fun p => z < p)

@[simp] theorem mem_vfMidSquareBandLateOwnerPrimes
    {z R p : ℕ} :
    p ∈ vfMidSquareBandLateOwnerPrimes z R ↔
      p ∈ vfMidSquareBandOwnerPrimes R ∧ z < p := by
  simp [vfMidSquareBandLateOwnerPrimes]

/-- Filtered owner Fubini: the composite survivors after the fixed prefix are
exactly the disjoint sum of owner fibres with owner p>z. -/
theorem vfMidSquareBandPrefixComposite_card_eq_sum_lateOwnerCards
    (z R : ℕ) (hR : 2 ≤ R) :
    (vfMidSquareBandPrefixCompositeSurvivors z R).card =
      ∑ p ∈ vfMidSquareBandLateOwnerPrimes z R,
        (vfMidSquareBandCompositeOwner R p).card := by
  let S : Finset ℕ := vfMidSquareBandPrefixCompositeSurvivors z R
  let O : Finset ℕ := vfMidSquareBandLateOwnerPrimes z R
  let owner : ℕ → ℕ := fun n => n.minFac
  have hmaps : ∀ n ∈ S, owner n ∈ O := by
    intro n hn
    have hnData := Finset.mem_filter.mp hn
    have hnComp : n ∈ vfMidSquareBandComposites R := hnData.1
    have hnSurv : lowWheelHighSurvivor z n := hnData.2
    have howner :=
      vfMidSquareBandComposite_minFac_mem_ownerPrimes hR hnComp
    have hzlt :=
      (vfMidSquareBandComposite_survives_prefix_iff_minFac_gt
        hR hnComp).1 hnSurv
    exact Finset.mem_filter.mpr ⟨howner, hzlt⟩
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to
      (s := S) (t := O) (g := owner) hmaps (fun _ => (1 : ℕ))
  have hraw :
      (∑ n ∈ S, (1 : ℕ)) =
        ∑ p ∈ O, ∑ n ∈ S with owner n = p, (1 : ℕ) :=
    hfiber.symm
  calc
    (vfMidSquareBandPrefixCompositeSurvivors z R).card =
        ∑ n ∈ S, (1 : ℕ) := by
          rw [Finset.card_eq_sum_ones]
    _ = ∑ p ∈ O, ∑ n ∈ S with owner n = p, (1 : ℕ) := hraw
    _ = ∑ p ∈ vfMidSquareBandLateOwnerPrimes z R,
          (vfMidSquareBandCompositeOwner R p).card := by
      dsimp [O, S, owner]
      apply Finset.sum_congr rfl
      intro p hp
      have hpLate : z < p := (Finset.mem_filter.mp hp).2
      have hset :
          ((vfMidSquareBandComposites R).filter
              (lowWheelHighSurvivor z)).filter
                (fun n => n.minFac = p) =
            vfMidSquareBandCompositeOwner R p := by
        ext n
        simp only [vfMidSquareBandCompositeOwner, Finset.mem_filter]
        constructor
        · rintro ⟨⟨hnComp, _hnSurv⟩, hmin⟩
          exact ⟨hnComp, hmin⟩
        · rintro ⟨hnComp, hmin⟩
          have hs :
              lowWheelHighSurvivor z n :=
            (vfMidSquareBandComposite_survives_prefix_iff_minFac_gt
              hR hnComp).2 (by simpa [hmin] using hpLate)
          exact ⟨⟨hnComp, hs⟩, hmin⟩
      rw [Finset.card_eq_sum_ones, ← hset]
      rfl

/-- Prime survivors and composite survivors partition every partial-prefix
survivor population in the square block. -/
theorem vfMidSquarePrefixWheelSurvivors_card_eq_prime_add_prefixComposite
    (z R : ℕ) (hR : 2 ≤ R) (hzR : z ≤ R) :
    (vfMidSquarePrefixWheelSurvivors z R).card =
      vfMidIntegerBlockPrimeSupply R +
        (vfMidSquareBandPrefixCompositeSurvivors z R).card := by
  classical
  let P : Finset ℕ := vfMidSquareWheelPrimes R
  let C : Finset ℕ := vfMidSquareBandPrefixCompositeSurvivors z R
  let S : Finset ℕ := vfMidSquarePrefixWheelSurvivors z R
  have hpart : P ∪ C = S := by
    ext n
    simp only [P, C, S, vfMidSquareWheelPrimes,
      vfMidSquareBandPrefixCompositeSurvivors,
      vfMidSquareBandComposites, vfMidSquareBandSites,
      vfMidSquarePrefixWheelSurvivors, vfMidSquareWheelSites,
      Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hnSite, hnPrime⟩ | ⟨⟨hnSite, _hnPrime⟩, hnSurv⟩)
      · have hnPrimeMem : n ∈ vfMidSquareWheelPrimes R :=
          Finset.mem_filter.mpr ⟨hnSite, hnPrime⟩
        have hnPref :=
          vfMidSquareWheelPrimes_subset_prefixWheelSurvivors
            hR hzR hnPrimeMem
        exact Finset.mem_filter.mp hnPref
      · exact ⟨hnSite, hnSurv⟩
    · rintro ⟨hnSite, hnSurv⟩
      by_cases hnPrime : n.Prime
      · exact Or.inl ⟨hnSite, hnPrime⟩
      · exact Or.inr ⟨⟨hnSite, hnPrime⟩, hnSurv⟩
  have hdisj : Disjoint P C := by
    rw [Finset.disjoint_left]
    intro n hnP hnC
    have hp := (Finset.mem_filter.mp hnP).2
    have hc0 := (Finset.mem_filter.mp hnC).1
    have hc := (Finset.mem_filter.mp hc0).2
    exact hc hp
  have hcard := congrArg Finset.card hpart
  have hprime :
      P.card = vfMidIntegerBlockPrimeSupply R := by
    dsimp [P]
    unfold vfMidIntegerBlockPrimeSupply
    rw [vfMidDirectPrimeBand_eq_squareWheelPrimes]
  rw [Finset.card_union_of_disjoint hdisj, hprime] at hcard
  exact hcard.symm

/-- One prefix survivor excess over the exact prime supply is literally the
number of composites whose least-prime owner has not yet acted. -/
theorem vfMidSquarePrefixWheelExcess_eq_sum_lateOwnerCards
    (z R : ℕ) (hR : 2 ≤ R) (hzR : z ≤ R) :
    ((vfMidSquarePrefixWheelSurvivors z R).card : ℝ) -
        (vfMidIntegerBlockPrimeSupply R : ℝ) =
      ∑ p ∈ vfMidSquareBandLateOwnerPrimes z R,
        ((vfMidSquareBandCompositeOwner R p).card : ℝ) := by
  have hpart :=
    vfMidSquarePrefixWheelSurvivors_card_eq_prime_add_prefixComposite
      z R hR hzR
  have howners :=
    vfMidSquareBandPrefixComposite_card_eq_sum_lateOwnerCards z R hR
  have hpartR :
      ((vfMidSquarePrefixWheelSurvivors z R).card : ℝ) =
        (vfMidIntegerBlockPrimeSupply R : ℝ) +
          ((vfMidSquareBandPrefixCompositeSurvivors z R).card : ℝ) := by
    exact_mod_cast hpart
  have hownersR :
      ((vfMidSquareBandPrefixCompositeSurvivors z R).card : ℝ) =
        ∑ p ∈ vfMidSquareBandLateOwnerPrimes z R,
          ((vfMidSquareBandCompositeOwner R p).card : ℝ) := by
    exact_mod_cast howners
  rw [hownersR] at hpartR
  linarith

/-- Literal chronological owner census over the whole dyadic square range. -/
def vfMidDyadicOwnerLateRemoval (z A B : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico A B,
    ∑ p ∈ vfMidSquareBandLateOwnerPrimes z r,
      ((vfMidSquareBandCompositeOwner r p).card : ℝ)

/-- **Exact T identity.**  On A<=r<B with z<=A and A>=2, the dyadic
late-removal term is exactly the cumulative least-prime-factor owner census. -/
theorem vfMidDyadicLateRemoval_eq_ownerCensus
    (z A B : ℕ) (hA : 2 ≤ A) (hzA : z ≤ A) (hAB : A ≤ B) :
    vfMidDyadicLateRemoval z A B =
      vfMidDyadicOwnerLateRemoval z A B := by
  rw [vfMidDyadicLateRemoval_eq_sum_blockExcess z A B hAB]
  unfold vfMidDyadicOwnerLateRemoval
  apply Finset.sum_congr rfl
  intro r hr
  have hAr : A ≤ r := (Finset.mem_Ico.mp hr).1
  have hr2 : 2 ≤ r := hA.trans hAr
  have hzr : z ≤ r := hzA.trans hAr
  exact vfMidSquarePrefixWheelExcess_eq_sum_lateOwnerCards
    z r hr2 hzr

/-! ## Starting-wheel late composites are quadratically sparse on short runs -/

/-- On a subdoubling run, one least-prime owner above the starting root can
occupy at most four sites of any later square block. The proof uses only the
spacing p between consecutive multiples of p and the block width 2R. -/
theorem vfMidSquareBandLateOwner_card_le_four_of_subdoubling
    {A R p : ℕ} (hA : 3 ≤ A) (hAR : A ≤ R)
    (hRlt : R < 2 * A)
    (hp : p ∈ vfMidSquareBandLateOwnerPrimes A R) :
    (vfMidSquareBandCompositeOwner R p).card ≤ 4 := by
  have hpData := mem_vfMidSquareBandLateOwnerPrimes.mp hp
  have hpOwner : p ∈ vfMidSquareBandOwnerPrimes R := hpData.1
  have hpGtA : A < p := hpData.2
  have hR3 : 3 ≤ R := hA.trans hAR
  have hpPrime : p.Prime :=
    (mem_vfMidSquareBandOwnerPrimes.mp hpOwner).1
  have hpPos : 0 < p := hpPrime.pos
  have hRlt2p : R < 2 * p := by omega
  have hroughEq :
      vfMidSquareBandCompositeOwnerChildren R p =
        vfMidSquareBandOwnerRoughChildren R p :=
    vfMidSquareBandCompositeOwnerChildren_eq_rough hR3 hpOwner
  have hsub :
      vfMidSquareBandOwnerRoughChildren R p ⊆
        Finset.Ioc (R ^ 2 / p) (R ^ 2 / p + 4) := by
    intro m hm
    rcases Finset.mem_filter.mp hm with ⟨_hmIcc, hdata⟩
    have hlo : R ^ 2 < p * m := hdata.1
    have hhi : p * m < (R + 1) ^ 2 := hdata.2.1
    have hmLower : R ^ 2 / p < m := by
      apply (Nat.div_lt_iff_lt_mul hpPos).2
      simpa [Nat.mul_comm] using hlo
    have hfloor : R ^ 2 < (R ^ 2 / p + 1) * p := by
      apply (Nat.div_lt_iff_lt_mul hpPos).1
      omega
    have hgap : 2 * R + 1 ≤ 4 * p := by omega
    have hexp : (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by ring
    have hmUpper : m ≤ R ^ 2 / p + 4 := by
      by_contra hnot
      have hmGe : R ^ 2 / p + 5 ≤ m := by omega
      have hmulGe :
          (R ^ 2 / p + 5) * p ≤ m * p :=
        Nat.mul_le_mul_right p hmGe
      have hq5 :
          (R ^ 2 / p + 5) * p =
            (R ^ 2 / p + 1) * p + 4 * p := by ring
      have hblockLt : (R + 1) ^ 2 < (R ^ 2 / p + 5) * p := by
        rw [hexp, hq5]
        omega
      have hprodHi : m * p < (R + 1) ^ 2 := by
        simpa [Nat.mul_comm] using hhi
      omega
    exact Finset.mem_Ioc.mpr ⟨hmLower, hmUpper⟩
  calc
    (vfMidSquareBandCompositeOwner R p).card =
        (vfMidSquareBandCompositeOwnerChildren R p).card := by
          symm
          exact vfMidSquareBandCompositeOwnerChildren_card R p
    _ = (vfMidSquareBandOwnerRoughChildren R p).card := by
          exact congrArg Finset.card hroughEq
    _ ≤ (Finset.Ioc (R ^ 2 / p) (R ^ 2 / p + 4)).card :=
          Finset.card_le_card hsub
    _ = 4 := by simp

/-- Hence after sieving a square block by every prime through the starting
root A, the surviving composites in a subdoubling later block R are at most
four times the root displacement R-A. -/
theorem vfMidSquareBandPrefixComposite_start_card_le_four_mul_gap
    {A R : ℕ} (hA : 3 ≤ A) (hAR : A ≤ R)
    (hRlt : R < 2 * A) :
    (vfMidSquareBandPrefixCompositeSurvivors A R).card ≤
      4 * (R - A) := by
  have howners :=
    vfMidSquareBandPrefixComposite_card_eq_sum_lateOwnerCards
      A R (by omega : 2 ≤ R)
  have hownerSub :
      vfMidSquareBandLateOwnerPrimes A R ⊆ Finset.Ioc A R := by
    intro p hp
    have hpData := mem_vfMidSquareBandLateOwnerPrimes.mp hp
    have hpRoot : p ≤ R :=
      (mem_vfMidSquareBandOwnerPrimes.mp hpData.1).2
    exact Finset.mem_Ioc.mpr ⟨hpData.2, hpRoot⟩
  have hownerCard :
      (vfMidSquareBandLateOwnerPrimes A R).card ≤ R - A := by
    have hcard := Finset.card_le_card hownerSub
    simpa using hcard
  rw [howners]
  calc
    (∑ p ∈ vfMidSquareBandLateOwnerPrimes A R,
        (vfMidSquareBandCompositeOwner R p).card) ≤
        ∑ _p ∈ vfMidSquareBandLateOwnerPrimes A R, 4 := by
          apply Finset.sum_le_sum
          intro p hp
          exact vfMidSquareBandLateOwner_card_le_four_of_subdoubling
            hA hAR hRlt hp
    _ = 4 * (vfMidSquareBandLateOwnerPrimes A R).card := by
          simp [Nat.mul_comm]
    _ ≤ 4 * (R - A) := Nat.mul_le_mul_left 4 hownerCard


/-- Summing the starting-wheel survivor excess over a subdoubling square run
costs only quadratically in the number of blocks.  In particular, the loss
does not scale like the physical length of the run. -/
theorem vfMidDyadicLateRemoval_start_le_four_mul_gap_sq
    {A B : ℕ} (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicLateRemoval A A B ≤
      4 * (((B - A : ℕ) : ℝ) ^ 2) := by
  rw [vfMidDyadicLateRemoval_eq_ownerCensus A A B
    (by omega) le_rfl hAB]
  unfold vfMidDyadicOwnerLateRemoval
  calc
    (∑ r ∈ Finset.Ico A B,
        ∑ p ∈ vfMidSquareBandLateOwnerPrimes A r,
          ((vfMidSquareBandCompositeOwner r p).card : ℝ))
        =
      ∑ r ∈ Finset.Ico A B,
        ((vfMidSquareBandPrefixCompositeSurvivors A r).card : ℝ) := by
          apply Finset.sum_congr rfl
          intro r hr
          have howners :=
            vfMidSquareBandPrefixComposite_card_eq_sum_lateOwnerCards
              A r (by
                have hAr : A ≤ r := (Finset.mem_Ico.mp hr).1
                omega : 2 ≤ r)
          exact_mod_cast howners.symm
    _ ≤ ∑ r ∈ Finset.Ico A B,
          (4 * (((r - A : ℕ) : ℝ))) := by
          apply Finset.sum_le_sum
          intro r hr
          have hAr : A ≤ r := (Finset.mem_Ico.mp hr).1
          have hrB : r < B := (Finset.mem_Ico.mp hr).2
          have hr2A : r < 2 * A := hrB.trans_le hBA
          have hcard :=
            vfMidSquareBandPrefixComposite_start_card_le_four_mul_gap
              hA hAr hr2A
          exact_mod_cast hcard
    _ ≤ ∑ _r ∈ Finset.Ico A B,
          (4 * (((B - A : ℕ) : ℝ))) := by
          apply Finset.sum_le_sum
          intro r hr
          have hAr : A ≤ r := (Finset.mem_Ico.mp hr).1
          have hrB : r < B := (Finset.mem_Ico.mp hr).2
          have hgap : r - A ≤ B - A := by omega
          have hgapR :
              (((r - A : ℕ) : ℝ)) ≤ (((B - A : ℕ) : ℝ)) := by
            exact_mod_cast hgap
          nlinarith
    _ = ((Finset.Ico A B).card : ℝ) *
          (4 * (((B - A : ℕ) : ℝ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = 4 * (((B - A : ℕ) : ℝ) ^ 2) := by
          rw [Nat.card_Ico]
          ring

/-- **Run-level lower prime-supply bound from one frozen starting wheel.**
On a subdoubling run, actual prime supply is at least the survivor supply of
the starting wheel minus the explicit quadratic late-composite budget. -/
theorem vfMidDyadicPrimeSupply_ge_startPrefix_sub_four_mul_gap_sq
    {A B : ℕ} (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicPrefixSupply A A B -
        4 * (((B - A : ℕ) : ℝ) ^ 2) ≤
      vfMidDyadicPrimeSupply A B := by
  have hlate :=
    vfMidDyadicLateRemoval_start_le_four_mul_gap_sq
      hA hAB hBA
  unfold vfMidDyadicLateRemoval at hlate
  linarith


/-! ## Canonical z=2 VF tracking defect -/

/-- At cutoff two the fixed prefix consists of the single prime coordinate 2. -/
theorem primesUpTo_two_eq_singleton :
    primesUpTo 2 = {2} := by
  ext p
  simp only [mem_primesUpTo, Finset.mem_singleton]
  constructor
  · rintro ⟨hp, hp2⟩
    have hpLower := hp.two_le
    omega
  · rintro rfl
    exact ⟨Nat.prime_two, le_rfl⟩

/-- The cutoff-two prefix counting function is exactly the count of odd
positive integers up to N.  This is the one-face inclusion-exclusion formula. -/
theorem vfMidPrefixWheelCounting_two_cast (N : ℕ) :
    (vfMidPrefixWheelCounting 2 N : ℝ) =
      (N : ℝ) - ((N / 2 : ℕ) : ℝ) := by
  rw [vfMidPrefixWheelCounting_cast_real_eq_faceFloorSum,
    primesUpTo_two_eq_singleton]
  have hpowerset :
      ({2} : Finset ℕ).powerset = {∅, {2}} := by
    ext s
    simp [Finset.subset_singleton_iff]
  rw [hpowerset]
  change
    (∑ x ∈ ({∅, {2}} : Finset (Finset ℕ)),
      (booleanCubeSign x : ℝ) *
        ((N / primeFaceProduct x : ℕ) : ℝ)) =
      (N : ℝ) - ((N / 2 : ℕ) : ℝ)
  have hempty :
      (∅ : Finset ℕ) ∉ ({{2}} : Finset (Finset ℕ)) := by
    intro h
    have heq : (∅ : Finset ℕ) = {2} := by
      simpa using h
    have hcard := congrArg Finset.card heq
    norm_num at hcard
  rw [Finset.sum_insert hempty, Finset.sum_singleton]
  norm_num [booleanCubeSign, primeFaceProduct]
  ring

/-- The parity correction in floor(N/2) is unchanged by squaring N. -/
theorem cast_sq_div_two_sub_div_two (N : ℕ) :
    (((N ^ 2) / 2 : ℕ) : ℝ) - ((N / 2 : ℕ) : ℝ) =
      (((N : ℝ) ^ 2 - (N : ℝ)) / 2) := by
  rcases Nat.even_or_odd N with hEven | hOdd
  · rw [Nat.even_iff] at hEven
    let q : ℕ := N / 2
    have hdiv := Nat.mod_add_div N 2
    have hN : N = 2 * q := by
      dsimp [q]
      omega
    have hsq : N ^ 2 / 2 = 2 * q ^ 2 := by
      rw [hN]
      have hpoly : (2 * q) ^ 2 = 2 * (2 * q ^ 2) := by ring
      rw [hpoly]
      omega
    have hhalf : N / 2 = q := by rfl
    rw [hsq, hhalf, hN]
    push_cast
    ring
  · rw [Nat.odd_iff] at hOdd
    let q : ℕ := N / 2
    have hdiv := Nat.mod_add_div N 2
    have hN : N = 2 * q + 1 := by
      dsimp [q]
      omega
    have hsq : N ^ 2 / 2 = 2 * q ^ 2 + 2 * q := by
      rw [hN]
      have hpoly :
          (2 * q + 1) ^ 2 =
            2 * (2 * q ^ 2 + 2 * q) + 1 := by ring
      rw [hpoly]
      omega
    have hhalf : N / 2 = q := by rfl
    rw [hsq, hhalf, hN]
    push_cast
    ring

/-- **Exact parity-prefix identity.**
Over any adjacent square range, the z=2 prefix supply is exactly one half of
the square-interior population.  Equivalently it is the sum of r over
A <= r < B.  Hence the generic four-endpoint prefix remainder vanishes
identically at the canonical parity cutoff. -/
theorem vfMidDyadicPrefixSupply_two_eq_half_interior
    (A B : ℕ) :
    vfMidDyadicPrefixSupply 2 A B =
      (1 / 2 : ℝ) * vfMidDyadicInteriorLength A B := by
  unfold vfMidDyadicPrefixSupply
  rw [vfMidPrefixWheelCounting_two_cast,
    vfMidPrefixWheelCounting_two_cast,
    vfMidPrefixWheelCounting_two_cast,
    vfMidPrefixWheelCounting_two_cast]
  have hB := cast_sq_div_two_sub_div_two B
  have hA := cast_sq_div_two_sub_div_two A
  unfold vfMidDyadicInteriorLength
  push_cast
  linarith

/-- The natural z=2 Euler prefix density is exactly 1/2. -/
theorem vfMidPrefixWheelDensity_two_eq_half :
    vfMidPrefixWheelDensity 2 = (1 / 2 : ℝ) := by
  unfold vfMidPrefixWheelDensity
  rw [primesUpTo_two_eq_singleton]
  norm_num

/-- At z=2 the native late-removal reference has no prefix approximation:
it is exactly the odd-composite reference 1/2 L - VF. -/
theorem vfMidDyadicLateReference_two_eq_half_interior_sub_vf
    (A B : ℕ) :
    vfMidDyadicLateReference 2 A B =
      (1 / 2 : ℝ) * vfMidDyadicInteriorLength A B -
        vfMidDyadicVFMass A B := by
  unfold vfMidDyadicLateReference
  rw [vfMidPrefixWheelDensity_two_eq_half]

/-- Canonical VF-native tracking defect: physical chronological owner removals
minus the VF-implied odd-composite population. -/
def vfMidDyadicVFTrackingDefect (A B : ℕ) : ℝ :=
  vfMidDyadicOwnerLateRemoval 2 A B -
    ((1 / 2 : ℝ) * vfMidDyadicInteriorLength A B -
      vfMidDyadicVFMass A B)

/-- The canonical tracking defect is exactly VF mass minus actual prime mass.
No Li state and no prefix remainder occurs. -/
theorem vfMidDyadicVFTrackingDefect_eq_vfMass_sub_primeSupply
    (A B : ℕ) (hA : 2 ≤ A) (hAB : A ≤ B) :
    vfMidDyadicVFTrackingDefect A B =
      vfMidDyadicVFMass A B - vfMidDyadicPrimeSupply A B := by
  unfold vfMidDyadicVFTrackingDefect
  rw [← vfMidDyadicLateRemoval_eq_ownerCensus
      2 A B hA (by omega) hAB]
  unfold vfMidDyadicLateRemoval
  rw [vfMidDyadicPrefixSupply_two_eq_half_interior]
  ring

/-- **Central VF identity.**
The owner tracking defect over [A,B) is literally the negative square-endpoint
VF error increment.  This is the quantity to recurse on from now on. -/
theorem vfMidDyadicVFTrackingDefect_eq_neg_primeError_increment
    {A B : ℕ} (hA : 2 ≤ A) (hB : 2 ≤ B) (hAB : A ≤ B) :
    vfMidDyadicVFTrackingDefect A B =
      -(vfMidPrimeError ((B : ℝ) ^ 2) -
        vfMidPrimeError ((A : ℝ) ^ 2)) := by
  rw [vfMidDyadicVFTrackingDefect_eq_vfMass_sub_primeSupply A B hA hAB]
  rw [vfMidPrimeError_sq_sub_sq_eq_dyadicPrimeVFError hA hB]
  ring

/-- The RH-scale arithmetic target can now be stated entirely on the native
VF owner census, with no Li object in its type. -/
def VFMidDyadicVFTrackingBoundedStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ A B : ℕ, 2 ≤ A → A < B → B ≤ 2 * A →
      |vfMidDyadicVFTrackingDefect A B| ≤
        C * (A : ℝ) * Real.log A

/-- A bound on the native VF tracking defect is exactly enough to supply the
existing signed late-correction consumer. -/
theorem vfMidDyadicSignedLateCorrection_of_vfTracking
    (htrack : VFMidDyadicVFTrackingBoundedStatement) :
    VFMidDyadicSignedLateCorrectionStatement := by
  rcases htrack with ⟨C, hC0, hC⟩
  refine ⟨C, hC0, ?_⟩
  intro A B hA hAB hBA
  have hABle : A ≤ B := hAB.le
  have hT :=
    vfMidDyadicLateRemoval_eq_ownerCensus
      2 A B hA (by omega) hABle
  have hRef :=
    vfMidDyadicLateReference_two_eq_half_interior_sub_vf A B
  rw [hT, hRef]
  exact hC A B hA hAB hBA

end RHLean.Analysis

import Mathlib
import «research.GLOBAL_RETURNED_CORE_FIRST_OWNER_CELL_FUBINI»
import RHLean.Proof.LowWheelCofactorQuotientToggle

/-!
# Exact compensated first-owner block

The first-owner cell identity becomes useful only after the p-divisible branch
is returned to its p-free parent coordinate.  This file performs that return
exactly on the actual AMP common-clock carrier.

For one prime owner `p` and one lower-prime signature cell, split the p-free
branch according to whether its p-multiple remains in the physical endpoint.
The admitted part is in bijection with the p-divisible child branch.  Fresh
prime Moebius reversal then gives

  base + child
    = sum_admitted mu(a) * (w(a) - w(p*a))
      + sum_clipped w(a) * mu(a).

For the actual AMP weight, the interior difference is already compiled as

  w(a) - w(p*a) = daughterCrossingWeight(a) - rootCrossingIndicator(a).

Thus the compensated parent square contains the signed daughter/root
interaction literally, while the only unmatched one-dimensional population is
the clipped p-child exit.  No norm, Cauchy--Schwarz, frame estimate, or Mertens
magnitude bound is used.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- p-free sites in one first-owner cell whose p-child is still inside the
physical common clock. -/
def lowOwnerFirstOwnerAdmittedBaseFiber
    (R p : ℕ) (sig : Finset ℕ) : Finset ℕ :=
  (lowOwnerFirstOwnerBaseFiber R p sig).filter fun a =>
    p * a ≤ squareRootEndpoint R

/-- p-free sites in one first-owner cell whose p-child has left the physical
common clock.  This is the literal one-dimensional clipped exit. -/
def lowOwnerFirstOwnerClippedBaseFiber
    (R p : ℕ) (sig : Finset ℕ) : Finset ℕ :=
  (lowOwnerFirstOwnerBaseFiber R p sig).filter fun a =>
    squareRootEndpoint R < p * a

/-- Multiplication by the owner does not change any prime coordinate strictly
below that owner. -/
theorem squarefreeLowerPrimeSignature_mul_owner
    {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    squarefreeLowerPrimeSignature p (p * a) =
      squarefreeLowerPrimeSignature p a := by
  unfold squarefreeLowerPrimeSignature squarefreePrimeFace
  rw [primeFactors_prime_mul hp (Nat.ne_of_gt ha)]
  ext q
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hq | hqa, hlt⟩
    · subst q
      omega
    · exact ⟨hqa, hlt⟩
  · rintro ⟨hqa, hlt⟩
    exact ⟨Or.inr hqa, hlt⟩

/-- Every admitted p-free parent produces a genuine p-divisible child in the
same lower-signature cell. -/
theorem lowOwnerFirstOwner_mul_mem_child_of_admitted
    {R p a : ℕ} {sig : Finset ℕ}
    (hp : p.Prime)
    (ha : a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig) :
    p * a ∈ lowOwnerFirstOwnerChildFiber R p sig := by
  rcases Finset.mem_filter.mp ha with ⟨haBase, hpaX⟩
  rcases Finset.mem_filter.mp haBase with ⟨haCar, hbase⟩
  rcases Finset.mem_filter.mp haCar with ⟨haIcc, hmu⟩
  rcases Finset.mem_Icc.mp haIcc with ⟨ha1, _haX⟩
  have haPos : 0 < a := by omega
  have hpaPos : 0 < p * a := Nat.mul_pos hp.pos haPos
  have hpa1 : 1 ≤ p * a := by omega
  have hmuMul : realMoebiusStep (p * a) ≠ 0 := by
    rw [realMoebiusStep_mul_prime_eq_neg hp hbase.2]
    exact neg_ne_zero.mpr hmu
  have hcar : p * a ∈ lowOwnerNonzeroMobiusCarrier R := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hpa1, hpaX⟩, hmuMul⟩
  have hsig : squarefreeLowerPrimeSignature p (p * a) = sig := by
    rw [squarefreeLowerPrimeSignature_mul_owner hp haPos, hbase.1]
  exact Finset.mem_filter.mpr
    ⟨hcar, ⟨hsig, ⟨a, rfl⟩⟩⟩

/-- Every actual p-divisible child returns to a unique p-free parent in the same
lower-signature cell. -/
theorem lowOwnerFirstOwner_div_mem_base_of_child
    {R p n : ℕ} {sig : Finset ℕ}
    (hp : p.Prime)
    (hn : n ∈ lowOwnerFirstOwnerChildFiber R p sig) :
    n / p ∈ lowOwnerFirstOwnerBaseFiber R p sig := by
  rcases Finset.mem_filter.mp hn with ⟨hnCar, hchild⟩
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar with
    ⟨hnsq, hnpos⟩
  have hcancel : p * (n / p) = n := Nat.mul_div_cancel' hchild.2
  have hdivpos : 0 < n / p := by
    by_contra hnotpos
    have hz : n / p = 0 := Nat.eq_zero_of_not_pos hnotpos
    rw [hz, mul_zero] at hcancel
    omega
  have hnot : ¬ p ∣ n / p :=
    prime_not_dvd_div_of_squarefree hp hnsq hchild.2
  have hmuN : realMoebiusStep n ≠ 0 :=
    (Finset.mem_filter.mp hnCar).2
  have hsign :
      realMoebiusStep n = -realMoebiusStep (n / p) := by
    calc
      realMoebiusStep n = realMoebiusStep (p * (n / p)) := by rw [hcancel]
      _ = -realMoebiusStep (n / p) :=
        realMoebiusStep_mul_prime_eq_neg hp hnot
  have hmuDiv : realMoebiusStep (n / p) ≠ 0 := by
    intro hz
    apply hmuN
    rw [hsign, hz, neg_zero]
  have hnIcc := (Finset.mem_filter.mp hnCar).1
  have hnX := (Finset.mem_Icc.mp hnIcc).2
  have hdiv1 : 1 ≤ n / p := by omega
  have hdivCar : n / p ∈ lowOwnerNonzeroMobiusCarrier R := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr
        ⟨hdiv1, (Nat.div_le_self n p).trans hnX⟩,
        hmuDiv⟩
  have hsigMul := squarefreeLowerPrimeSignature_mul_owner hp hdivpos
  have hsig : squarefreeLowerPrimeSignature p (n / p) = sig := by
    calc
      squarefreeLowerPrimeSignature p (n / p) =
          squarefreeLowerPrimeSignature p (p * (n / p)) := hsigMul.symm
      _ = squarefreeLowerPrimeSignature p n := by rw [hcancel]
      _ = sig := hchild.1
  exact Finset.mem_filter.mpr ⟨hdivCar, ⟨hsig, hnot⟩⟩

/-- A child returned by division is automatically in the admitted parent
sub-fibre. -/
theorem lowOwnerFirstOwner_div_mem_admitted_of_child
    {R p n : ℕ} {sig : Finset ℕ}
    (hp : p.Prime)
    (hn : n ∈ lowOwnerFirstOwnerChildFiber R p sig) :
    n / p ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig := by
  have hbase := lowOwnerFirstOwner_div_mem_base_of_child hp hn
  have hchildCar := (Finset.mem_filter.mp hn).1
  have hnX := (Finset.mem_Icc.mp (Finset.mem_filter.mp hchildCar).1).2
  have hcancel : p * (n / p) = n :=
    Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2.2
  exact Finset.mem_filter.mpr ⟨hbase, by simpa [hcancel] using hnX⟩

/-- The p-divisible child amplitude is exactly the returned admitted-parent
sum with the fresh-prime sign reversal exposed. -/
theorem lowOwnerFirstOwnerChildAmplitude_eq_neg_returnedAdmitted
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerChildAmplitude R p sig =
      ∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
        -(lowOwnerZeroFrequencyMobiusWeight R (p * a) * realMoebiusStep a) := by
  unfold lowOwnerFirstOwnerChildAmplitude
  refine Finset.sum_bij
    (fun n _hn => n / p)
    (fun n hn => lowOwnerFirstOwner_div_mem_admitted_of_child hp hn)
    ?_ ?_ ?_
  · intro n hn m hm heq
    have hnDvd := (Finset.mem_filter.mp hn).2.2
    have hmDvd := (Finset.mem_filter.mp hm).2.2
    change n / p = m / p at heq
    calc
      n = p * (n / p) := (Nat.mul_div_cancel' hnDvd).symm
      _ = p * (m / p) := by rw [heq]
      _ = m := Nat.mul_div_cancel' hmDvd
  · intro a ha
    refine ⟨p * a, lowOwnerFirstOwner_mul_mem_child_of_admitted hp ha, ?_⟩
    change (p * a) / p = a
    simpa [Nat.mul_comm] using Nat.mul_div_left a hp.pos
  · intro n hn
    have hbase := lowOwnerFirstOwner_div_mem_base_of_child hp hn
    have hnot := (Finset.mem_filter.mp hbase).2.2
    have hnDvd := (Finset.mem_filter.mp hn).2.2
    have hcancel : p * (n / p) = n := Nat.mul_div_cancel' hnDvd
    unfold lowOwnerZeroFrequencyMobiusSite
    calc
      lowOwnerZeroFrequencyMobiusWeight R n * realMoebiusStep n =
          lowOwnerZeroFrequencyMobiusWeight R (p * (n / p)) *
            realMoebiusStep (p * (n / p)) := by rw [hcancel]
      _ = -(lowOwnerZeroFrequencyMobiusWeight R (p * (n / p)) *
            realMoebiusStep (n / p)) := by
        rw [realMoebiusStep_mul_prime_eq_neg hp hnot]
        ring

/-- The p-free base amplitude splits exactly into admitted parents and the
literal clipped child-exit population. -/
theorem lowOwnerFirstOwnerBaseAmplitude_eq_admitted_add_clipped
    (R p : ℕ) (sig : Finset ℕ) :
    lowOwnerFirstOwnerBaseAmplitude R p sig =
      (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
        lowOwnerZeroFrequencyMobiusSite R a) +
      ∑ a ∈ lowOwnerFirstOwnerClippedBaseFiber R p sig,
        lowOwnerZeroFrequencyMobiusSite R a := by
  unfold lowOwnerFirstOwnerBaseAmplitude
    lowOwnerFirstOwnerAdmittedBaseFiber lowOwnerFirstOwnerClippedBaseFiber
  simpa only [not_le] using
    (Finset.sum_filter_add_sum_filter_not
      (s := lowOwnerFirstOwnerBaseFiber R p sig)
      (p := fun a => p * a ≤ squareRootEndpoint R)
      (f := lowOwnerZeroFrequencyMobiusSite R)).symm

/-- Signed compensated interior of one first-owner cell. -/
def lowOwnerFirstOwnerCompensatedInteriorAmplitude
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  ∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
    (lowOwnerDaughterCrossingWeight R p a -
      lowOwnerRootCrossingIndicator R p a) * realMoebiusStep a

/-- Literal clipped remainder of one first-owner cell. -/
def lowOwnerFirstOwnerClippedAmplitude
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  ∑ a ∈ lowOwnerFirstOwnerClippedBaseFiber R p sig,
    lowOwnerZeroFrequencyMobiusSite R a

/-- **Exact compensated owner block.**  The parent-cell amplitude is the actual
signed daughter/root interaction on admitted parents plus only the clipped
p-child exit.  This is the desired pre-energy joint `(S,E)` mechanism at one
first-separation owner. -/
theorem lowOwnerFirstOwnerBase_add_child_eq_compensated_add_clipped
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerBaseAmplitude R p sig +
        lowOwnerFirstOwnerChildAmplitude R p sig =
      lowOwnerFirstOwnerCompensatedInteriorAmplitude R p sig +
        lowOwnerFirstOwnerClippedAmplitude R p sig := by
  rw [lowOwnerFirstOwnerBaseAmplitude_eq_admitted_add_clipped,
    lowOwnerFirstOwnerChildAmplitude_eq_neg_returnedAdmitted hp]
  unfold lowOwnerFirstOwnerCompensatedInteriorAmplitude
    lowOwnerFirstOwnerClippedAmplitude
  have hinter :
      (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
        lowOwnerZeroFrequencyMobiusSite R a) +
        (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
          -(lowOwnerZeroFrequencyMobiusWeight R (p * a) * realMoebiusStep a)) =
      ∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
        (lowOwnerDaughterCrossingWeight R p a -
          lowOwnerRootCrossingIndicator R p a) * realMoebiusStep a := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _ha
    unfold lowOwnerZeroFrequencyMobiusSite
    rw [← lowOwnerZeroFrequencyMobiusWeight_sub_mul
      (R := R) (p := p) (n := a) hp.one_le]
    ring
  rw [← hinter]
  ring

end RHLean.Proof

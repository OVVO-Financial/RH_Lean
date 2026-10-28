import Mathlib
import «research.EULER_ASYMMETRIC_CORNER_SIGNED_GRAM_20261028»
import RHLean.Analysis.PrimeSieveCollapseIdentity
import RHLean.Proof.SquareRootTruncatedPacketEquivalences
import RHLean.Analysis.SquareRootPrimeCountGap

/-!
# Genuine admissible Euler population, reciprocal prime bands and signed Co-Div

X_R = R^2 - 1.  The low population consists of the **actual** admitted
squarefree prime products with all prime factors < R and product <= X_R.
The complementary high population is the sum of all *genuine* prime families
p >= R, each containing all admissible cofactors c <= X_R/p.

The exact signed source, its reciprocal-band prime availability, and the
historical weighted Euler Gram are related without assuming statistical
independence or a power-saving estimate.

The analytic signed return bound remains OPEN. All results here are finite
identities on the original Mobius coefficients.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof
open RHLean.Analysis RHLean.Arithmetic

/-- Genuine low Euler population, with the product cutoff and p < R. -/
def eulerAdmissibleLowPopulation (R : ℕ) : ℂ :=
  primeSieveSmoothMobiusMass (R - 1) (squareRootEndpoint R)

/-- Sum of positive cofactor Mertens masses, one per genuinely admitted
prime p >= R.  The actual innovation is its NEGATIVE. -/
def eulerAdmissiblePrimeDebt (R : ℕ) : ℂ :=
  primeSieveReciprocalMertensSignedSum (R - 1) (squareRootEndpoint R)

def eulerAdmissibleHighInnovation (R : ℕ) : ℂ :=
  -eulerAdmissiblePrimeDebt R

/-- Exact quotient-band prime availability, with no substituted Li model. -/
def eulerAdmissibleBandPopulation (R k : ℕ) : ℕ :=
  ((primeSieveReciprocalInterval (R - 1) (squareRootEndpoint R) k).filter
      Nat.Prime).card

/-- At this square endpoint, the entire post-root reciprocal range has
precisely R-1 quotient bands, including the singleton-prime band k=1. -/
theorem eulerAdmissible_endpoint_div_root (R : ℕ) (hR : 2 ≤ R) :
    squareRootEndpoint R / R = R - 1 := by
  have hpred : R - 1 + 1 = R := by omega
  have hsq : squareRootEndpoint R + 1 = R * R := by
    unfold squareRootEndpoint
    have hpos : 1 ≤ R ^ 2 := by nlinarith
    rw [Nat.sub_add_cancel hpos]
    ring
  have hmul : (R - 1) * R + R = R * R := by
    calc
      (R - 1) * R + R = ((R - 1) + 1) * R := by ring
      _ = R * R := by rw [hpred]
  have hlow : (R - 1) * R ≤ squareRootEndpoint R := by omega
  have hhigh : squareRootEndpoint R < R * R := by omega
  have hhigh' : squareRootEndpoint R < (R - 1 + 1) * R := by
    simpa [hpred] using hhigh
  exact Nat.div_eq_of_lt_le hlow hhigh'

/-- Literal endpoint equality for the admitted prime-product population.
No probabilistic or monotonicity input. -/
theorem eulerAdmissible_endpoint_eq_low_add_innovation
    (R : ℕ) (hR : 2 ≤ R) :
    mertensSummatory (squareRootEndpoint R) =
      eulerAdmissibleLowPopulation R + eulerAdmissibleHighInnovation R := by
  have hsqrt : Nat.sqrt (squareRootEndpoint R) ≤ R - 1 := by
    have h := squareRootEndpoint_sqrt_lt_root hR
    omega
  have h := mertensSummatory_eq_neg_signedSum_add_smoothMass_of_sqrt_le
    (R - 1) (squareRootEndpoint R) (by omega) hsqrt
  simpa [eulerAdmissibleLowPopulation, eulerAdmissibleHighInnovation,
    eulerAdmissiblePrimeDebt, add_comm] using h

/-- The actual band multiplicity is exactly the prime-count increment, even
when the reciprocal band is empty or clipped by the root. -/
theorem eulerAdmissibleBandPopulation_eq_primeCounting_sub
    (R k : ℕ) :
    eulerAdmissibleBandPopulation R k =
      Nat.primeCounting (squareRootEndpoint R / k) -
        Nat.primeCounting
          (max (R - 1) (squareRootEndpoint R / (k + 1))) := by
  let L := max (R - 1) (squareRootEndpoint R / (k + 1))
  let U := squareRootEndpoint R / k
  change ((Finset.Ioc L U).filter Nat.Prime).card =
    Nat.primeCounting U - Nat.primeCounting L
  by_cases hLU : L ≤ U
  · have hcount := primeCard_Ioc_add_primeCounting_eq hLU
    omega
  · have hUL : U ≤ L := Nat.le_of_lt (Nat.lt_of_not_ge hLU)
    have hcount := primeCard_Ioc_add_primeCounting_eq hUL
    have hempty : Finset.Ioc L U = ∅ := Finset.Ioc_eq_empty_of_le hUL
    have hzero : ((Finset.Ioc L U).filter Nat.Prime).card = 0 := by
      simp [hempty]
    omega

/-- Original high-prime debt equals the exact reciprocal-band sum. -/
theorem eulerAdmissiblePrimeDebt_eq_exact_bands
    (R : ℕ) (hR : 2 ≤ R) :
    eulerAdmissiblePrimeDebt R =
      ∑ k ∈ Finset.Icc 1 (R - 1),
        (eulerAdmissibleBandPopulation R k : ℂ) * mertensSummatory k := by
  unfold eulerAdmissiblePrimeDebt
    primeSieveReciprocalMertensSignedSum primeSieveQuotientSupport
  have hpred : R - 1 + 1 = R := by omega
  rw [hpred, eulerAdmissible_endpoint_div_root R hR]
  apply Finset.sum_congr rfl
  intro k hk
  rw [primeSieveReciprocalPrimeCount_eq_card]
  unfold eulerAdmissibleBandPopulation
  ring

/-- Equivalent chronological prime-family sum, including p=R when prime. -/
theorem eulerAdmissiblePrimeDebt_eq_actual_prime_sum (R : ℕ) :
    eulerAdmissiblePrimeDebt R =
      ∑ p ∈ Finset.Ioc (R - 1) (squareRootEndpoint R),
        if p.Prime then mertensSummatory (squareRootEndpoint R / p) else 0 := by
  unfold eulerAdmissiblePrimeDebt
  rw [primeSieveReciprocalMertensSignedSum_eq_mertensPrimeTail]
  rfl

/-- Separate the one potentially active p=R prime from the native p>R
transport. There is NO unrecorded root-prime exception. -/
theorem eulerAdmissiblePrimeDebt_eq_root_prime_add_far
    (R : ℕ) (hR : 2 ≤ R) :
    eulerAdmissiblePrimeDebt R =
      (if R.Prime then mertensSummatory (R - 1) else 0) +
        primeSieveMertensPrimeTail R (squareRootEndpoint R) := by
  rw [eulerAdmissiblePrimeDebt_eq_actual_prime_sum]
  have hRle : R ≤ squareRootEndpoint R := by
    have hsq : R + 1 ≤ R ^ 2 := by nlinarith
    unfold squareRootEndpoint
    omega
  have hsplit : Finset.Ioc (R - 1) (squareRootEndpoint R) =
      insert R (Finset.Ioc R (squareRootEndpoint R)) := by
    ext p
    simp only [Finset.mem_Ioc, Finset.mem_insert]
    omega
  rw [hsplit, Finset.sum_insert (by simp [Finset.mem_Ioc])]
  rw [eulerAdmissible_endpoint_div_root R hR]
  rfl

/-- The Euler self-dual source is precisely the historical population debt
minus the genuine admissible prime-family debt. -/
theorem eulerSelfDualBilinear_eq_admissible_population
    (R : ℕ) (hR : 2 ≤ R) :
    eulerSelfDualBilinear R =
      2 * mertensSummatory (R - 1) -
        eulerAdmissibleLowPopulation R +
        eulerAdmissiblePrimeDebt R := by
  rw [eulerSelfDualBilinear_eq_two_mertens_sub_endpoint R hR,
    eulerAdmissible_endpoint_eq_low_add_innovation R hR]
  unfold eulerAdmissibleHighInnovation
  ring

/-- The same population identity with the exact O(R) corner retained in the
two-cutoff Euler floor rectangle of PR #1042. -/
theorem eulerAsymBilinear_eq_admissible_population
    (R : ℕ) (hR : 2 ≤ R) :
    eulerAsymBilinear R =
      mertensSummatory (R - 1) +
        mertensSummatory (eulerAsymCutoff R) -
        eulerAdmissibleLowPopulation R +
        eulerAdmissiblePrimeDebt R + eulerAsymCorner R := by
  rw [eulerAsymBilinear_eq_mertens_add_corner R hR,
    eulerAdmissible_endpoint_eq_low_add_innovation R hR]
  unfold eulerAdmissibleHighInnovation
  ring

/-- Full physical low-prime Euler population after processing every actual
prime <=p, keeping the endpoint fixed throughout. -/
def eulerAdmissibleState (R p : ℕ) : ℂ :=
  primeSieveSmoothMobiusMass p (squareRootEndpoint R)

/-- Actual Mertens-valued cofactor family attached to candidate p. It is
zero at composite p. -/
def eulerAdmissibleAdmissionDebt (R p : ℕ) : ℂ :=
  if p.Prime then mertensSummatory (squareRootEndpoint R / p) else 0

/-- Peeling the first integer from an inclusive post-cutoff prime sum. -/
private theorem eulerAdmissible_Ioc_peel (a b : ℕ) (hab : a + 1 ≤ b)
    (f : ℕ → ℂ) :
    (∑ p ∈ Finset.Ioc a b, f p) =
      f (a + 1) + ∑ p ∈ Finset.Ioc (a + 1) b, f p := by
  have hset : Finset.Ioc a b = insert (a + 1) (Finset.Ioc (a + 1) b) := by
    ext p
    simp only [Finset.mem_Ioc, Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert (by simp [Finset.mem_Ioc])]

/-- A fresh admitted prime introduces its full product-admissible family
with the exact opposite sign. This holds at every stage p >= R, including
composite stages (zero change) and the boundary p=R if prime. -/
theorem eulerAdmissibleState_step
    (R p : ℕ) (hR : 2 ≤ R)
    (hp : R ≤ p) (hpX : p ≤ squareRootEndpoint R) :
    eulerAdmissibleState R p =
      eulerAdmissibleState R (p - 1) -
        eulerAdmissibleAdmissionDebt R p := by
  let X := squareRootEndpoint R
  have hsqrt : Nat.sqrt X ≤ p - 1 := by
    have h := squareRootEndpoint_sqrt_lt_root hR
    dsimp [X]
    omega
  have hpred : p - 1 + 1 = p := by omega
  have hlow := mertensSummatory_eq_neg_signedSum_add_smoothMass_of_sqrt_le
    (p - 1) X (by omega : 1 ≤ p - 1) hsqrt
  have hhigh := mertensSummatory_eq_neg_signedSum_add_smoothMass_of_sqrt_le
    p X (by omega : 1 ≤ p) (by omega : Nat.sqrt X ≤ p)
  rw [primeSieveReciprocalMertensSignedSum_eq_mertensPrimeTail] at hlow hhigh
  have htail : primeSieveMertensPrimeTail (p - 1) X =
      eulerAdmissibleAdmissionDebt R p + primeSieveMertensPrimeTail p X := by
    unfold primeSieveMertensPrimeTail eulerAdmissibleAdmissionDebt
    have hs := eulerAdmissible_Ioc_peel (p - 1) X (by omega)
      (fun q => if q.Prime then mertensSummatory (X / q) else 0)
    simpa [hpred, X] using hs
  unfold eulerAdmissibleState
  change primeSieveSmoothMobiusMass p X =
      primeSieveSmoothMobiusMass (p - 1) X -
        eulerAdmissibleAdmissionDebt R p
  linear_combination hlow - hhigh - htail

/-- At the final prime cutoff all squarefree products are admitted. -/
theorem eulerAdmissibleState_terminal
    (R : ℕ) (hR : 2 ≤ R) :
    eulerAdmissibleState R (squareRootEndpoint R) =
      mertensSummatory (squareRootEndpoint R) := by
  let X := squareRootEndpoint R
  have hroot : Nat.sqrt X ≤ X := by
    have hs := squareRootEndpoint_sqrt_lt_root hR
    have hRle : R ≤ X := by
      have hm : R + 1 ≤ R ^ 2 := by nlinarith
      change R ≤ R ^ 2 - 1
      omega
    change Nat.sqrt (squareRootEndpoint R) ≤ squareRootEndpoint R
    omega
  have hXone : 1 ≤ X := by
    have hsq : 2 ≤ R ^ 2 := by nlinarith
    dsimp [X, squareRootEndpoint]
    omega
  have h := mertensSummatory_eq_neg_signedSum_add_smoothMass_of_sqrt_le
    X X hXone hroot
  rw [primeSieveReciprocalMertensSignedSum_eq_mertensPrimeTail] at h
  have hzero : primeSieveMertensPrimeTail X X = 0 := by
    simp [primeSieveMertensPrimeTail]
  rw [hzero] at h
  simpa [eulerAdmissibleState, X] using h.symm

/-- The early state at p=R-1 is exactly the original admissible product
population; no artificial seed or independent-sign replacement. -/
theorem eulerAdmissibleState_initial (R : ℕ) :
    eulerAdmissibleState R (R - 1) = eulerAdmissibleLowPopulation R := rfl

/-- Full signed chronological energy step; the cross term is indispensable. -/
theorem eulerAdmissibleState_energy_step
    (R p : ℕ) (hR : 2 ≤ R)
    (hp : R ≤ p) (hpX : p ≤ squareRootEndpoint R) :
    Complex.normSq (eulerAdmissibleState R p) -
        Complex.normSq (eulerAdmissibleState R (p - 1)) =
      Complex.normSq (eulerAdmissibleAdmissionDebt R p) -
        2 * ((starRingEnd ℂ (eulerAdmissibleState R (p - 1))) *
          eulerAdmissibleAdmissionDebt R p).re := by
  rw [eulerAdmissibleState_step R p hR hp hpX]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

#print axioms eulerAdmissible_endpoint_eq_low_add_innovation
#print axioms eulerAdmissibleBandPopulation_eq_primeCounting_sub
#print axioms eulerAdmissiblePrimeDebt_eq_exact_bands
#print axioms eulerAdmissiblePrimeDebt_eq_root_prime_add_far
#print axioms eulerSelfDualBilinear_eq_admissible_population
#print axioms eulerAdmissibleState_step
#print axioms eulerAdmissibleState_energy_step

end RHLean.Proof

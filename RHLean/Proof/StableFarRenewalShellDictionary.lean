import Mathlib
import RHLean.Proof.StableFarRenewalGlobalBoundary
import RHLean.Proof.RoughDyadicQ2Compression
import RHLean.Proof.StableFarWallAdaptiveFourCornerBridge

/-!
# Physical dictionary for the two stable-far renewal shells

The two threshold shells of the centered renewal are not two new analytic
populations.

* First-cut atoms are literal points of the global top dyadic wall.
* Second-cross atoms are literal points of the old owner's q^2 rough daughter
  dyadic wall, after stripping the old owner and far-prime scales.

These are pointwise carrier statements before any summation or norm.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- Shell 1 = global endpoint wall. A production first-cut atom is an odd
physical site n with n <= X_R < 2*n. -/
theorem stableFarRenewalProductionFirstCut_transport_mem_topDyadicBoundary
    {R : ℕ} {t : StableFarRenewalShellTag}
    (ht : t ∈ stableFarRenewalProductionFirstCutCarrier R) :
    stableFarRenewalTwoShellTransport t ∈
      dyadicCofactorBoundary (squareRootEndpoint R) := by
  rcases t with ⟨q, ⟨r, ⟨e, p⟩⟩⟩
  have hmem := mem_stableFarRenewalProductionFirstCutCarrier.mp ht
  rcases stableFarRenewalProductionTwoShellCarrier_data hmem.1 with
    ⟨_hqOld, hy, hrne, heOdd, _hshell⟩
  change r ≠ 2 at hrne
  change Odd e at heOdd
  have hyBase : (r, (e, p)) ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp hy).1
  rcases mem_lowWheelFarPrimeLowCofactorTriples_iff_data.mp hyBase with
    ⟨hrPrime, hrR, he1, hpPrime, hpR, _heSq, _her, _hbaseCut⟩
  rcases hmem.2 with ⟨hqOld, hrq, hcut, _hcross, hdoubleNotCut⟩
  change q ∈ primesUpTo (R - 1) at hqOld
  change r < q at hrq
  change q * r * e * p ≤ squareRootEndpoint R at hcut
  change ¬ (q * r * (2 * e) * p ≤ squareRootEndpoint R) at hdoubleNotCut
  have hqPrime := (mem_primesUpTo.mp hqOld).1
  have hrOdd : Odd r := hrPrime.odd_of_ne_two hrne
  have hr3 : 3 ≤ r := by
    have hr2 := hrPrime.two_le
    omega
  have hqne : q ≠ 2 := by omega
  have hqOdd : Odd q := hqPrime.odd_of_ne_two hqne
  have hpne : p ≠ 2 := by omega
  have hpOdd : Odd p := hpPrime.odd_of_ne_two hpne
  have hePos : 0 < e := by omega
  have hnOdd : Odd (q * r * e * p) :=
    ((hqOdd.mul hrOdd).mul heOdd).mul hpOdd
  have hnPos : 0 < q * r * e * p :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hqPrime.pos hrPrime.pos) hePos) hpPrime.pos
  have hdouble :
      squareRootEndpoint R < 2 * (q * r * e * p) := by
    have hx : squareRootEndpoint R < q * r * (2 * e) * p :=
      Nat.lt_of_not_ge hdoubleNotCut
    have heq : q * r * (2 * e) * p = 2 * (q * r * e * p) := by ring
    simpa [heq] using hx
  apply mem_dyadicCofactorBoundary.mpr
  refine ⟨Nat.succ_le_iff.mpr hnPos, ?_, hnOdd, hdouble⟩
  simpa [stableFarRenewalTwoShellTransport,
    stableFarRenewalTransportSite] using hcut

/-- Shell 2 = recursive q^2 daughter wall. For a production second-cross
atom, the stripped returned cofactor r*e lies on the q-rough dyadic wall at
the exact daughter cutoff (X_R/q^2)/p. -/
theorem stableFarRenewalProductionSecondCross_returned_mem_q2RoughDyadicBoundary
    {R : ℕ} {t : StableFarRenewalShellTag}
    (ht : t ∈ stableFarRenewalProductionSecondCrossCarrier R) :
    t.2.1 * t.2.2.1 ∈
      roughDyadicCofactorBoundary t.1
        ((squareRootEndpoint R / (t.1 * t.1)) / t.2.2.2) := by
  rcases t with ⟨q, ⟨r, ⟨e, p⟩⟩⟩
  have hmem := mem_stableFarRenewalProductionSecondCrossCarrier.mp ht
  rcases stableFarRenewalProductionTwoShellCarrier_data hmem.1 with
    ⟨_hqOld, hy, hrne, heOdd, _hshell⟩
  change r ≠ 2 at hrne
  change Odd e at heOdd
  have hyBase : (r, (e, p)) ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp hy).1
  rcases mem_lowWheelFarPrimeLowCofactorTriples_iff_data.mp hyBase with
    ⟨hrPrime, _hrR, he1, hpPrime, _hpR, _heSq, her, _hbaseCut⟩
  rcases hmem.2 with
    ⟨hqOld, hrq, _hdoubleFirstCut, hdoubleQ2Cross, hq2NotCross⟩
  change q ∈ primesUpTo (R - 1) at hqOld
  change r < q at hrq
  change squareRootEndpoint R < q * q * r * (2 * e) * p at hdoubleQ2Cross
  change ¬ (squareRootEndpoint R < q * q * r * e * p) at hq2NotCross
  have hqPrime := (mem_primesUpTo.mp hqOld).1
  have hq2pos : 0 < q * q := Nat.mul_pos hqPrime.pos hqPrime.pos
  have hpPos : 0 < p := hpPrime.pos
  have hq2Cut :
      q * q * (r * e) * p ≤ squareRootEndpoint R := by
    have hx : q * q * r * e * p ≤ squareRootEndpoint R :=
      Nat.le_of_not_gt hq2NotCross
    simpa [Nat.mul_assoc] using hx
  have hdpCut :
      (r * e) * p ≤ squareRootEndpoint R / (q * q) := by
    apply (Nat.le_div_iff_mul_le hq2pos).2
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hq2Cut
  have hdCut :
      r * e ≤ (squareRootEndpoint R / (q * q)) / p := by
    exact (Nat.le_div_iff_mul_le hpPos).2 hdpCut
  have hq2Double :
      squareRootEndpoint R < (2 * (r * e) * p) * (q * q) := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hdoubleQ2Cross
  have hdivQ :
      squareRootEndpoint R / (q * q) < 2 * (r * e) * p :=
    (Nat.div_lt_iff_lt_mul hq2pos).2 hq2Double
  have hdouble :
      (squareRootEndpoint R / (q * q)) / p < 2 * (r * e) :=
    (Nat.div_lt_iff_lt_mul hpPos).2 hdivQ
  have hrOdd : Odd r := hrPrime.odd_of_ne_two hrne
  have hdOdd : Odd (r * e) := hrOdd.mul heOdd
  have hePos : 0 < e := by omega
  have hdPos : 0 < r * e := Nat.mul_pos hrPrime.pos hePos
  have hlpf_re : canonicalLargestPrimeFactor (r * e) = r := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough he1 hrPrime her
  apply mem_roughDyadicCofactorBoundary.mpr
  constructor
  · exact mem_dyadicCofactorBoundary.mpr
      ⟨Nat.succ_le_iff.mpr hdPos, hdCut, hdOdd, hdouble⟩
  · rw [hlpf_re]
    exact hrq

/-! ## Exact crossing-triple realization of the two shells -/

def stableFarRenewalFirstCutCrossingTriple
    (t : StableFarRenewalShellTag) : ℕ × (ℕ × ℕ) :=
  (t.1, (t.2.1 * t.2.2.1, t.2.2.2))

def stableFarRenewalSecondCrossCrossingTriple
    (t : StableFarRenewalShellTag) : ℕ × (ℕ × ℕ) :=
  (t.1, (t.2.1 * (2 * t.2.2.1), t.2.2.2))

/-- A production first-cut shell atom is literally an existing strict q^2
crossing state at the undoubled returned cofactor. -/
theorem stableFarRenewalProductionFirstCut_mem_q2CrossingTriples
    {R : ℕ} {t : StableFarRenewalShellTag}
    (ht : t ∈ stableFarRenewalProductionFirstCutCarrier R) :
    stableFarRenewalFirstCutCrossingTriple t ∈
      lowWheelFarPrimeQ2CrossingTriples R := by
  rcases t with ⟨q, ⟨r, ⟨e, p⟩⟩⟩
  have hmem := mem_stableFarRenewalProductionFirstCutCarrier.mp ht
  rcases stableFarRenewalProductionTwoShellCarrier_data hmem.1 with
    ⟨_hqOld0, hy, _hrne, _heOdd, _hshell⟩
  have hyBase : (r, (e, p)) ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp hy).1
  rcases mem_lowWheelFarPrimeLowCofactorTriples_iff_data.mp hyBase with
    ⟨hrPrime, _hrR, he1, hpPrime, hpR, heSq, her, _hbaseCut⟩
  rcases hmem.2 with ⟨hqOld, hrq, hcut, hcross, _hdoubleNotCut⟩
  rcases mem_primesUpTo.mp hqOld with ⟨hqPrime, hqPred⟩
  have hRpos : 0 < R := by
    have hqpos := hqPrime.pos
    omega
  have hqR : q < R := Nat.lt_of_le_pred hRpos hqPred
  have hePos : 0 < e := by omega
  have hd1 : 1 ≤ r * e := by
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero hrPrime.ne_zero (Nat.ne_of_gt hePos))
  have hreFresh : ¬ r ∣ e :=
    squareRootLowPrimePrime_fresh_of_lpf_lt he1 hrPrime her
  have hreCop : Nat.Coprime r e :=
    (hrPrime.coprime_iff_not_dvd).2 hreFresh
  have hdSq : Squarefree (r * e) :=
    (Nat.squarefree_mul hreCop).2 ⟨hrPrime.squarefree, heSq⟩
  have hlpf : canonicalLargestPrimeFactor (r * e) = r := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough he1 hrPrime her
  have hdq : canonicalLargestPrimeFactor (r * e) < q := by
    rw [hlpf]
    exact hrq
  have hbase :
      (q, (r * e, p)) ∈ lowWheelFarPrimeLowCofactorTriples R := by
    apply lowWheelFarPrimeLowCofactorTriple_mem_of_data
      hqPrime hqR hd1 hpPrime hpR hdSq hdq
    simpa [Nat.mul_assoc] using hcut
  unfold stableFarRenewalFirstCutCrossingTriple
  apply Finset.mem_filter.mpr
  refine ⟨hbase, ?_⟩
  simpa [Nat.mul_assoc] using hcross

/-- A production second-cross shell atom is literally an existing strict q^2
crossing state after the exact dyadic parent move e -> 2e. -/
theorem stableFarRenewalProductionSecondCross_mem_q2CrossingTriples
    {R : ℕ} {t : StableFarRenewalShellTag}
    (ht : t ∈ stableFarRenewalProductionSecondCrossCarrier R) :
    stableFarRenewalSecondCrossCrossingTriple t ∈
      lowWheelFarPrimeQ2CrossingTriples R := by
  rcases t with ⟨q, ⟨r, ⟨e, p⟩⟩⟩
  have hmem := mem_stableFarRenewalProductionSecondCrossCarrier.mp ht
  rcases stableFarRenewalProductionTwoShellCarrier_data hmem.1 with
    ⟨_hqOld0, hy, hrne, heOdd, _hshell⟩
  change r ≠ 2 at hrne
  change Odd e at heOdd
  have hyBase : (r, (e, p)) ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp hy).1
  rcases mem_lowWheelFarPrimeLowCofactorTriples_iff_data.mp hyBase with
    ⟨hrPrime, _hrR, he1, hpPrime, hpR, heSq, her, _hbaseCut⟩
  rcases hmem.2 with
    ⟨hqOld, hrq, hcut2, hcross2, _hparentNotCross⟩
  rcases mem_primesUpTo.mp hqOld with ⟨hqPrime, hqPred⟩
  have hRpos : 0 < R := by
    have hqpos := hqPrime.pos
    omega
  have hqR : q < R := Nat.lt_of_le_pred hRpos hqPred
  have hrgt : 2 < r := by
    have hr2 := hrPrime.two_le
    omega
  have hdataE : CanonicalSourceData r e :=
    squareRootLowPrimeGo_canonicalSourceData_of_rough
      hrPrime he1 heSq her
  have hdata2E : CanonicalSourceData r (2 * e) :=
    (canonicalSourceData_two_mul_iff_of_odd heOdd hrgt).mpr hdataE
  have h2eRough :
      canonicalLargestPrimeFactor (2 * e) < r :=
    canonicalLargestPrimeFactor_lt_of_sourceData hdata2E
  rcases hdata2E with
    ⟨_hrPrime2, h2e1, h2eSq, _hrCop2e, _hdom2e⟩
  have hrFresh : ¬ r ∣ 2 * e :=
    squareRootLowPrimePrime_fresh_of_lpf_lt h2e1 hrPrime h2eRough
  have hrCop : Nat.Coprime r (2 * e) :=
    (hrPrime.coprime_iff_not_dvd).2 hrFresh
  have hdSq : Squarefree (r * (2 * e)) :=
    (Nat.squarefree_mul hrCop).2 ⟨hrPrime.squarefree, h2eSq⟩
  have hd1 : 1 ≤ r * (2 * e) := by
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero hrPrime.ne_zero
        (Nat.ne_of_gt (by omega : 0 < 2 * e)))
  have hlpf : canonicalLargestPrimeFactor (r * (2 * e)) = r := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough
        h2e1 hrPrime h2eRough
  have hdq : canonicalLargestPrimeFactor (r * (2 * e)) < q := by
    rw [hlpf]
    exact hrq
  have hbase :
      (q, (r * (2 * e), p)) ∈ lowWheelFarPrimeLowCofactorTriples R := by
    apply lowWheelFarPrimeLowCofactorTriple_mem_of_data
      hqPrime hqR hd1 hpPrime hpR hdSq hdq
    simpa [Nat.mul_assoc] using hcut2
  unfold stableFarRenewalSecondCrossCrossingTriple
  apply Finset.mem_filter.mpr
  refine ⟨hbase, ?_⟩
  simpa [Nat.mul_assoc] using hcross2

/-- Shell 1 contributes no new adaptive raw correction once its far prime has
already appeared in the descending chronology. -/
theorem stableFarRenewalProductionFirstCut_rawStepCorrection_eq_zero
    {R : ℕ} {t : StableFarRenewalShellTag}
    (ht : t ∈ stableFarRenewalProductionFirstCutCarrier R)
    (pre post : List ℕ)
    (hprePrime : ∀ r ∈ pre, r.Prime)
    (hpreLarger :
      ∀ r ∈ pre, (stableFarRenewalFirstCutCrossingTriple t).2.2 < r) :
    let u := stableFarRenewalFirstCutCrossingTriple t
    let a := squareRootCanonicalRoughAdaptiveRawCoefficient
      (pre ++ u.2.2 :: post)
      (Finset.Icc 1 (squareRootEndpoint R))
      (fun _ => (1 : ℂ))
    a u.2.1 * canonicalMoebiusWeight u.2.1 *
        (((squareRootCanonicalRoughFreshLossBoundary R u.2.1 u.1).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary R u.2.1 u.1).card : ℂ)) +
      (a (u.2.1 * u.1) - a u.2.1) *
        squareRootCanonicalRoughRawCorrelationSummand R (u.2.1 * u.1) = 0 := by
  exact
    lowWheelFarPrimeQ2CrossingTriple_rawStepCorrection_eq_zero_at_farPrime
      (stableFarRenewalProductionFirstCut_mem_q2CrossingTriples ht)
      pre post hprePrime hpreLarger

/-- Shell 2 is annihilated by the same existing adaptive four-corner theorem,
now at the doubled crossing cofactor. -/
theorem stableFarRenewalProductionSecondCross_rawStepCorrection_eq_zero
    {R : ℕ} {t : StableFarRenewalShellTag}
    (ht : t ∈ stableFarRenewalProductionSecondCrossCarrier R)
    (pre post : List ℕ)
    (hprePrime : ∀ r ∈ pre, r.Prime)
    (hpreLarger :
      ∀ r ∈ pre, (stableFarRenewalSecondCrossCrossingTriple t).2.2 < r) :
    let u := stableFarRenewalSecondCrossCrossingTriple t
    let a := squareRootCanonicalRoughAdaptiveRawCoefficient
      (pre ++ u.2.2 :: post)
      (Finset.Icc 1 (squareRootEndpoint R))
      (fun _ => (1 : ℂ))
    a u.2.1 * canonicalMoebiusWeight u.2.1 *
        (((squareRootCanonicalRoughFreshLossBoundary R u.2.1 u.1).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary R u.2.1 u.1).card : ℂ)) +
      (a (u.2.1 * u.1) - a u.2.1) *
        squareRootCanonicalRoughRawCorrelationSummand R (u.2.1 * u.1) = 0 := by
  exact
    lowWheelFarPrimeQ2CrossingTriple_rawStepCorrection_eq_zero_at_farPrime
      (stableFarRenewalProductionSecondCross_mem_q2CrossingTriples ht)
      pre post hprePrime hpreLarger

end RHLean.Proof

import Mathlib
import RHLean.Proof.ReplacementFibreOrientationSplit

/-!
# Cofactor-prime windows for replacement fibres

This companion to `ReplacementFibreOrientationSplit` reindexes the two signed
orientation fibres by canonical cofactor and prime.  The output is the exact
Type-II incidence through the dilated reciprocal windows `I_z^(c)`.

No norm or estimate is taken here.  In particular, the prime window counts are
multiplied by the signed cofactor Möbius weight before any later analytic
operation.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-! ## Root orientation -/

/-- Geometric root population in reciprocal fibre `z`.  Squarefreeness is not
part of the set: nonsquarefree sources have zero Möbius weight. -/
def replacementFibreRootGeometricSourceSet (R z : ℕ) : Finset ℕ :=
  (Finset.Icc R (squareRootEndpoint R)).filter fun n =>
    squareRootEndpoint R / n = z ∧
      canonicalCofactor n < canonicalLargestPrimeFactor n

/-- Signed Möbius mass of the geometric root population. -/
def replacementFibreRootGeometricSourceMass (R z : ℕ) : ℂ :=
  ∑ n ∈ replacementFibreRootGeometricSourceSet R z,
    canonicalMoebiusWeight n

/-- Removing squarefreeness from the root set changes no signed mass because
nonsquarefree integers carry zero Möbius weight. -/
theorem replacementFibreRootMass_eq_geometricSourceMass
    (R z : ℕ) :
    replacementFibreRootMass R z =
      replacementFibreRootGeometricSourceMass R z := by
  classical
  unfold replacementFibreRootMass replacementFibreRootGeometricSourceMass
    replacementFibreRootGeometricSourceSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hdiv : squareRootEndpoint R / n = z
  · by_cases horient :
        canonicalCofactor n < canonicalLargestPrimeFactor n
    · by_cases hsq : Squarefree n
      · simp [hdiv, horient, ReplacementRootOriented, hsq,
          canonicalMoebiusWeight]
      · have hzero : (μ n : ℤ) = 0 :=
          ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
        simp [hdiv, horient, ReplacementRootOriented, hsq,
          canonicalMoebiusWeight, hzero]
    · simp [hdiv, horient, ReplacementRootOriented]
  · simp [hdiv]

/-- The automatic root-scale cofactor cutoff only uses the strict geometric
orientation `c < q`; squarefreeness is unnecessary. -/
theorem replacementRootGeometric_cofactor_lt_root
    {R n : ℕ} (hR : 2 ≤ R) (hn2 : 2 ≤ n)
    (hnX : n ≤ squareRootEndpoint R)
    (horient : canonicalCofactor n < canonicalLargestPrimeFactor n) :
    canonicalCofactor n < R := by
  have hn : 1 < n := by omega
  have hfactor := canonicalCofactor_mul_largestPrimeFactor hn
  by_contra hnot
  have hRc : R ≤ canonicalCofactor n := Nat.le_of_not_gt hnot
  have hRq : R ≤ canonicalLargestPrimeFactor n :=
    hRc.trans horient.le
  have hsqle : R ^ 2 ≤
      canonicalCofactor n * canonicalLargestPrimeFactor n := by
    simpa [pow_two] using Nat.mul_le_mul hRc hRq
  have hXlt : squareRootEndpoint R < R ^ 2 := by
    unfold squareRootEndpoint
    have hpos : 0 < R ^ 2 := by positivity
    omega
  have hnlt : n < R ^ 2 := hnX.trans_lt hXlt
  rw [hfactor] at hsqle
  exact (Nat.not_lt_of_ge hsqle) hnlt

/-- Canonical cofactor-prime coordinates for the geometric root population. -/
def replacementFibreRootPairSet (R z : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 (R - 1)).product
      (Finset.Icc 2 (squareRootEndpoint R))).filter fun cq =>
    cq.2.Prime ∧ cq.1 < cq.2 ∧
      squareRootEndpoint R / (cq.1 * cq.2) = z

/-- Signed source mass in the cofactor-prime root coordinates. -/
def replacementFibreRootPairMass (R z : ℕ) : ℂ :=
  ∑ cq ∈ replacementFibreRootPairSet R z,
    canonicalMoebiusWeight (cq.1 * cq.2)

private theorem rootGeometricSource_to_pair_mem
    {R z n : ℕ} (hR : 2 ≤ R)
    (hn : n ∈ replacementFibreRootGeometricSourceSet R z) :
    (canonicalCofactor n, canonicalLargestPrimeFactor n) ∈
      replacementFibreRootPairSet R z := by
  classical
  rcases Finset.mem_filter.mp hn with ⟨hnTail, hdiv, horient⟩
  rcases Finset.mem_Icc.mp hnTail with ⟨hnR, hnX⟩
  have hn2 : 2 ≤ n := hR.trans hnR
  have hn1 : 1 < n := by omega
  have hcpos : 1 ≤ canonicalCofactor n :=
    CanonicalGapAncestryBridge.canonicalCofactor_pos hn1
  have hcR := replacementRootGeometric_cofactor_lt_root hR hn2 hnX horient
  have hqPrime := canonicalLargestPrimeFactor_prime hn1
  have hqdvd := canonicalLargestPrimeFactor_dvd hn1
  have hqle : canonicalLargestPrimeFactor n ≤ n :=
    Nat.le_of_dvd (by omega) hqdvd
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩,
    hqPrime, horient, ?_⟩
  · exact Finset.mem_Icc.mpr ⟨hcpos, by omega⟩
  · exact Finset.mem_Icc.mpr ⟨hqPrime.two_le, hqle.trans hnX⟩
  · rw [canonicalCofactor_mul_largestPrimeFactor hn1]
    exact hdiv

private theorem rootGeometricSource_pair_injective
    {R z m n : ℕ} (hR : 2 ≤ R)
    (hm : m ∈ replacementFibreRootGeometricSourceSet R z)
    (hn : n ∈ replacementFibreRootGeometricSourceSet R z)
    (hpair :
      (canonicalCofactor m, canonicalLargestPrimeFactor m) =
        (canonicalCofactor n, canonicalLargestPrimeFactor n)) :
    m = n := by
  rcases Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1 with ⟨hmR, _⟩
  rcases Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1 with ⟨hnR, _⟩
  have hm1 : 1 < m := by
    have hm2 : 2 ≤ m := hR.trans hmR
    omega
  have hn1 : 1 < n := by
    have hn2 : 2 ≤ n := hR.trans hnR
    omega
  have hmprod := canonicalCofactor_mul_largestPrimeFactor hm1
  have hnprod := canonicalCofactor_mul_largestPrimeFactor hn1
  have hc : canonicalCofactor m = canonicalCofactor n :=
    congrArg Prod.fst hpair
  have hq : canonicalLargestPrimeFactor m = canonicalLargestPrimeFactor n :=
    congrArg Prod.snd hpair
  calc
    m = canonicalCofactor m * canonicalLargestPrimeFactor m := hmprod.symm
    _ = canonicalCofactor n * canonicalLargestPrimeFactor n := by rw [hc, hq]
    _ = n := hnprod

private theorem rootPair_surjective
    {R z : ℕ} (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z < R)
    (cq : ℕ × ℕ) (hcq : cq ∈ replacementFibreRootPairSet R z) :
    ∃ n ∈ replacementFibreRootGeometricSourceSet R z,
      (canonicalCofactor n, canonicalLargestPrimeFactor n) = cq := by
  classical
  rcases Finset.mem_filter.mp hcq with
    ⟨hbase, hqPrime, hcqLt, hdiv⟩
  rcases Finset.mem_product.mp hbase with ⟨hcMem, hqMem⟩
  rcases Finset.mem_Icc.mp hcMem with ⟨hc1, _hcR⟩
  rcases Finset.mem_Icc.mp hqMem with ⟨_hq2, _hqX⟩
  have hcpos : 0 < cq.1 := by omega
  have hprodpos : 0 < cq.1 * cq.2 :=
    Nat.mul_pos hcpos hqPrime.pos
  have hinterval :=
    (squareRootEndpoint_div_eq_iff_mem_replacementFibre
      (R := R) (n := cq.1 * cq.2) (z := z) hprodpos hz).1 hdiv
  have htailDiv :=
    (replacementTailFibre_mem_iff R z (cq.1 * cq.2) hR hz hzR).2 hinterval
  have htop := canonicalLargestPrimeFactor_mul_prime_eq hcpos hcqLt hqPrime
  have hcore := canonicalCofactor_mul_prime_eq hcpos hcqLt hqPrime
  refine ⟨cq.1 * cq.2, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨htailDiv.1, htailDiv.2, ?_⟩
    rw [htop, hcore]
    exact hcqLt
  · apply Prod.ext
    · exact hcore
    · exact htop

/-- Exact bijective reindex from root-oriented integers to their canonical
cofactor-prime coordinates. -/
theorem replacementFibreRootGeometricSourceMass_eq_pairMass
    (R z : ℕ) (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z < R) :
    replacementFibreRootGeometricSourceMass R z =
      replacementFibreRootPairMass R z := by
  classical
  unfold replacementFibreRootGeometricSourceMass replacementFibreRootPairMass
  refine Finset.sum_bij
    (fun n _hn => (canonicalCofactor n, canonicalLargestPrimeFactor n))
    (fun n hn => rootGeometricSource_to_pair_mem hR hn)
    (fun m hm n hn hmn => rootGeometricSource_pair_injective hR hm hn hmn)
    (fun cq hcq => by simpa using rootPair_surjective hR hz hzR cq hcq)
    ?_
  intro n hn
  rcases Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1 with ⟨hnR, _hnX⟩
  have hn1 : 1 < n := by
    have hn2 : 2 ≤ n := hR.trans hnR
    omega
  rw [canonicalCofactor_mul_largestPrimeFactor hn1]

/-- Prime count in the dilated reciprocal window for one root cofactor.  The
value is represented in `ℂ` so it can be multiplied directly by the signed
Möbius coefficient. -/
def replacementFibreRootPrimeWindowCount (R z c : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc
      (replacementDilatedFibreLower R z c)
      (replacementDilatedFibreUpper R z c),
    if q.Prime ∧ c < q then 1 else 0

private theorem replacementRootPrimeWindow_filter_eq
    {R z c : ℕ} (hc : 1 ≤ c) (hz : 1 ≤ z) :
    (Finset.Icc 2 (squareRootEndpoint R)).filter
        (fun q => q.Prime ∧ c < q ∧
          squareRootEndpoint R / (c * q) = z) =
      (Finset.Icc
        (replacementDilatedFibreLower R z c)
        (replacementDilatedFibreUpper R z c)).filter
          (fun q => q.Prime ∧ c < q) := by
  classical
  ext q
  constructor
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨_hqIcc, hprime, hcq, hdiv⟩
    apply Finset.mem_filter.mpr
    exact ⟨(squareRootEndpoint_div_mul_eq_iff_mem_dilatedFibre
      hc hprime.one_le hz).1 hdiv, hprime, hcq⟩
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqWin, hprime, hcq⟩
    have hdiv :=
      (squareRootEndpoint_div_mul_eq_iff_mem_dilatedFibre
        hc hprime.one_le hz).2 hqWin
    have hqUpper := (Finset.mem_Icc.mp hqWin).2
    have hupperX : replacementDilatedFibreUpper R z c ≤ squareRootEndpoint R := by
      unfold replacementDilatedFibreUpper
      exact Nat.div_le_self _ _
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨hprime.two_le, hqUpper.trans hupperX⟩,
      hprime, hcq, hdiv⟩

/-- Fubini plus the dilated-window reindex turns the root pair mass into a
signed cofactor-weighted prime-window count. -/
theorem replacementFibreRootPairMass_eq_neg_cofactorPrimeWindows
    (R z : ℕ) (hz : 1 ≤ z) :
    replacementFibreRootPairMass R z =
      -∑ c ∈ Finset.Icc 1 (R - 1),
        canonicalMoebiusWeight c *
          replacementFibreRootPrimeWindowCount R z c := by
  classical
  unfold replacementFibreRootPairMass replacementFibreRootPairSet
  rw [Finset.sum_filter]
  calc
    (∑ cq ∈ (Finset.Icc 1 (R - 1)).product
          (Finset.Icc 2 (squareRootEndpoint R)),
        if cq.2.Prime ∧ cq.1 < cq.2 ∧
            squareRootEndpoint R / (cq.1 * cq.2) = z then
          canonicalMoebiusWeight (cq.1 * cq.2)
        else 0) =
      ∑ c ∈ Finset.Icc 1 (R - 1),
        ∑ q ∈ Finset.Icc 2 (squareRootEndpoint R),
          if q.Prime ∧ c < q ∧ squareRootEndpoint R / (c * q) = z then
            canonicalMoebiusWeight (c * q)
          else 0 := by
      simpa only using
        (Finset.sum_product
          (s := Finset.Icc 1 (R - 1))
          (t := Finset.Icc 2 (squareRootEndpoint R))
          (f := fun cq : ℕ × ℕ =>
            if cq.2.Prime ∧ cq.1 < cq.2 ∧
                squareRootEndpoint R / (cq.1 * cq.2) = z then
              canonicalMoebiusWeight (cq.1 * cq.2)
            else 0))
    _ = ∑ c ∈ Finset.Icc 1 (R - 1),
        -(canonicalMoebiusWeight c *
          replacementFibreRootPrimeWindowCount R z c) := by
      apply Finset.sum_congr rfl
      intro c hcMem
      have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hcMem).1
      have hcpos : 0 < c := by omega
      have hset := replacementRootPrimeWindow_filter_eq
        (R := R) (z := z) hc1 hz
      rw [← Finset.sum_filter, hset]
      unfold replacementFibreRootPrimeWindowCount
      rw [← Finset.sum_filter]
      calc
        (∑ q ∈ (Finset.Icc
              (replacementDilatedFibreLower R z c)
              (replacementDilatedFibreUpper R z c)).filter
                (fun q => q.Prime ∧ c < q),
            canonicalMoebiusWeight (c * q)) =
          ∑ q ∈ (Finset.Icc
              (replacementDilatedFibreLower R z c)
              (replacementDilatedFibreUpper R z c)).filter
                (fun q => q.Prime ∧ c < q),
            -canonicalMoebiusWeight c := by
              apply Finset.sum_congr rfl
              intro q hq
              rcases (Finset.mem_filter.mp hq).2 with ⟨hprime, hcq⟩
              exact canonicalMoebiusWeight_mul_prime_eq_neg hcpos hcq hprime
        _ = -(canonicalMoebiusWeight c *
            ∑ q ∈ (Finset.Icc
              (replacementDilatedFibreLower R z c)
              (replacementDilatedFibreUpper R z c)).filter
                (fun q => q.Prime ∧ c < q), (1 : ℂ)) := by
              rw [Finset.mul_sum]
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro q _hq
              ring
    _ = -∑ c ∈ Finset.Icc 1 (R - 1),
        canonicalMoebiusWeight c *
          replacementFibreRootPrimeWindowCount R z c := by
      rw [Finset.sum_neg_distrib]

/-- **Root fibre prime-window dictionary.**  This is the first exact place at
which a prime-distribution estimate could later enter; no estimate is used here. -/
theorem replacementFibreRootMass_eq_neg_cofactorPrimeWindows
    (R z : ℕ) (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z < R) :
    replacementFibreRootMass R z =
      -∑ c ∈ Finset.Icc 1 (R - 1),
        canonicalMoebiusWeight c *
          replacementFibreRootPrimeWindowCount R z c := by
  rw [replacementFibreRootMass_eq_geometricSourceMass,
    replacementFibreRootGeometricSourceMass_eq_pairMass R z hR hz hzR,
    replacementFibreRootPairMass_eq_neg_cofactorPrimeWindows R z hz]

end RHLean.Proof

#!/usr/bin/env python3
"""Apply the final response-carrier repairs required by PR #473."""

from pathlib import Path


def replace_once(path: str, old: str, new: str) -> None:
    p = Path(path)
    text = p.read_text()
    count = text.count(old)
    if count == 0 and new in text:
        return
    if count != 1:
        raise SystemExit(f"expected one anchor in {path}, found {count}: {old!r}")
    p.write_text(text.replace(old, new, 1))


creation = "RHLean/Proof/SquareRootLowPrimeCreationResponseCarriers.lean"
replace_once(
    creation,
    """  have hcast := congrArg (fun w : ℂ => w.re) hflip
  simpa [squareRootLowPrimeResponseAtomWeight,
    canonicalMoebiusWeight, squareRootLowPrimeBadAtomChild] using hcast.symm
""",
    """  have hcast := congrArg (fun w : ℂ => w.re) hflip
  have hcastReal :
      ((-μ z.1 : ℤ) : ℝ) =
        ((μ (squareRootLowPrimeBadAtomChild z) : ℤ) : ℝ) := by
    simpa [canonicalMoebiusWeight] using hcast.symm
  unfold squareRootLowPrimeResponseAtomWeight
  exact_mod_cast hcastReal
""",
)

response = "RHLean/Proof/SquareRootLowPrimeResponseSeatCarrier.lean"
replace_once(
    response,
    """      z.1 = c ∧
        z.2 < squareRootLowPrimeCombinedFreshResponse R K j c := by
  simp [squareRootLowPrimeCombinedSeatFiber]
""",
    """      z.1 = c ∧
        z.2 < squareRootLowPrimeCombinedFreshResponse R K j c := by
  rcases z with ⟨z1, z2⟩
  simp [squareRootLowPrimeCombinedSeatFiber, eq_comm, and_comm]
""",
)
replace_once(
    response,
    """  intro c _hc d _hd hcd
  rw [Finset.disjoint_left]
  intro z hzc hzd
  exact hcd
""",
    """  intro c _hc d _hd hcd
  change Disjoint
    (squareRootLowPrimeCombinedSeatFiber R K j c)
    (squareRootLowPrimeCombinedSeatFiber R K j d)
  rw [Finset.disjoint_left]
  intro z hzc hzd
  exact hcd
""",
)
replace_once(
    response,
    """  rw [squareRootLowPrimeGlobalBadMass_eq_ownedCofactorSum]
  push_cast
  calc
    (∑ c ∈ squareRootLowPrimeOwnedBadCofactors R K U,
      ((-μ c : ℤ) : ℝ) *
        (squareRootLowPrimeCombinedFreshResponse R K j c : ℝ)) =
      ∑ c ∈ squareRootLowPrimeOwnedBadCofactors R K U,
        -(squareRootLowPrimeCombinedFreshResponse R K j c : ℝ) := by
      apply Finset.sum_congr rfl
      intro c hc
      have hmu := (squareRootLowPrimeOwnedBadCofactor_data hc).2.2.2
      simp [hmu]
    _ = -(∑ c ∈ squareRootLowPrimeOwnedBadCofactors R K U,
        (squareRootLowPrimeCombinedFreshResponse R K j c : ℝ)) := by
      rw [Finset.sum_neg_distrib]
""",
    """  rw [squareRootLowPrimeGlobalBadMass_eq_ownedCofactorSum]
  push_cast
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  have hmu := (squareRootLowPrimeOwnedBadCofactor_data hc).2.2.2
  simp [hmu]
""",
)
replace_once(
    response,
    """  have hincRe := congrArg Complex.re hinc
  push_cast at hincRe
  linarith
""",
    """  have hincRe := congrArg Complex.re hinc
  have hincReal :
      (∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
        squareRootLowPrimeFreshIncrementReal R K j p) =
        -(squareRootLowPrimeGlobalDeletionMass R K j K U : ℝ) +
          (squareRootLowPrimeGlobalBadMass R K j K U : ℝ) := by
    simpa [squareRootLowPrimeFreshIncrementReal] using hincRe
  linarith [hincReal]
""",
)
replace_once(
    response,
    """  unfold squareRootLowPrimeResponseSeatWeightReal
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := z.1)
""",
    """  unfold squareRootLowPrimeResponseSeatWeightReal
  have hInt : |(-μ z.1 : ℤ)| ≤ 1 := by
    simpa using (ArithmeticFunction.abs_moebius_le_one (n := z.1))
  exact_mod_cast hInt
""",
)
replace_once(
    response,
    """  have hmu :
      μ (ownerPrime x * squareRootLowPrimeCreationStateCofactor x) =
        -μ (squareRootLowPrimeCreationStateCofactor x) :=
    moebius_prime_mul_eq_neg_of_not_dvd hp hfresh
""",
    """  have hcop :
      Nat.Coprime (ownerPrime x)
        (squareRootLowPrimeCreationStateCofactor x) :=
    (hp.coprime_iff_not_dvd).2 hfresh
  have hmu :
      μ (ownerPrime x * squareRootLowPrimeCreationStateCofactor x) =
        -μ (squareRootLowPrimeCreationStateCofactor x) := by
    calc
      μ (ownerPrime x * squareRootLowPrimeCreationStateCofactor x) =
          μ (ownerPrime x) *
            μ (squareRootLowPrimeCreationStateCofactor x) :=
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
      _ = (-1) * μ (squareRootLowPrimeCreationStateCofactor x) := by
        rw [ArithmeticFunction.moebius_apply_prime hp]
      _ = -μ (squareRootLowPrimeCreationStateCofactor x) := by ring
""",
)
replace_once(
    response,
    """    · simp [squareRootLowPrimeCreationWeightReal,
        squareRootLowPrimeCreationWeightComplex,
        squareRootLowPrimeResponseSeatWeightReal,
        squareRootLowPrimeCreationToResponseSeat,
        squareRootLowPrimeCreationStateCofactor,
        squareRootLowPrimeCreationStateAbsoluteSeat,
        canonicalMoebiusWeight, hmu]
    · simp [squareRootLowPrimeCreationWeightReal,
        squareRootLowPrimeCreationWeightComplex,
        squareRootLowPrimeResponseSeatWeightReal,
        squareRootLowPrimeCreationToResponseSeat,
        squareRootLowPrimeCreationStateCofactor,
        squareRootLowPrimeCreationStateAbsoluteSeat,
        canonicalMoebiusWeight, hmu]
""",
    """    · simp only [squareRootLowPrimeCreationStateCofactor] at hmu
      have hmuReal := congrArg (fun a : ℤ => (a : ℝ)) hmu
      push_cast at hmuReal
      change -((μ z.1 : ℤ) : ℝ) +
          ((-μ (ownerPrime (some (Sum.inl z)) * z.1) : ℤ) : ℝ) = 0
      push_cast
      linarith
    · simp only [squareRootLowPrimeCreationStateCofactor] at hmu
      have hmuReal := congrArg (fun a : ℤ => (a : ℝ)) hmu
      push_cast at hmuReal
      change -((μ z.1 : ℤ) : ℝ) +
          ((-μ (ownerPrime (some (Sum.inr z)) * z.1) : ℤ) : ℝ) = 0
      push_cast
      linarith
""",
)

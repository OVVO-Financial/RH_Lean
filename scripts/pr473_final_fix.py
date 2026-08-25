#!/usr/bin/env python3
"""Apply the final processed-carrier and canonical-map repairs for PR #473."""

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


processed = "RHLean/Proof/SquareRootLowPrimeProcessedSeatCarrier.lean"
replace_once(
    processed,
    """  intro c _hc d _hd hcd
  rw [Finset.disjoint_left]
  intro z hzc hzd
""",
    """  intro c _hc d _hd hcd
  change Disjoint
    (squareRootLowPrimeCombinedSeatFiber R K j c)
    (squareRootLowPrimeCombinedSeatFiber R K j d)
  rw [Finset.disjoint_left]
  intro z hzc hzd
""",
)
replace_once(
    processed,
    """  rw [Finset.sum_insert
    (none_not_mem_squareRootLowPrimeProcessedSeatAtoms_image R K j P)]
  simp only [squareRootLowPrimeProcessedSeatWeightReal]
  have himage :
      (∑ x ∈ (squareRootLowPrimeProcessedSeatAtoms R K j P).image some,
        squareRootLowPrimeProcessedSeatWeightReal x) =
        ∑ z ∈ squareRootLowPrimeProcessedSeatAtoms R K j P,
          ((-μ z.1 : ℤ) : ℝ) := by
    symm
    apply Finset.sum_image
    intro a _ha b _hb hab
    exact Option.some_injective hab
  rw [himage, squareRootLowPrimeProcessedSeatAtoms_weight_sum]
""",
    """  rw [Finset.sum_insert
    (none_not_mem_squareRootLowPrimeProcessedSeatAtoms_image R K j P)]
  have himage :
      (∑ x ∈ (squareRootLowPrimeProcessedSeatAtoms R K j P).image some,
        squareRootLowPrimeProcessedSeatWeightReal x) =
        ∑ z ∈ squareRootLowPrimeProcessedSeatAtoms R K j P,
          ((-μ z.1 : ℤ) : ℝ) := by
    apply Finset.sum_image
    intro a _ha b _hb hab
    simpa using hab
  rw [himage, squareRootLowPrimeProcessedSeatAtoms_weight_sum]
  simp [squareRootLowPrimeProcessedSeatWeightReal]
""",
)
replace_once(
    processed,
    """    rw [← processedHighFilter_eq_honestHighRange hR,
      Finset.sum_filter, ← Finset.sum_add_distrib,
      ← Finset.sum_neg_distrib]
""",
    """    rw [← processedHighFilter_eq_honestHighRange hR,
      Finset.sum_filter, ← Finset.sum_neg_distrib,
      ← Finset.sum_sub_distrib]
""",
)
replace_once(
    processed,
    """  rw [hsplit]
  unfold squareRootBornPostTailRunningLowPrimeResponse
    canonicalMoebiusWeight
  simp only [Complex.neg_re, Complex.add_re]
  push_cast
  ring
""",
    """  rw [hsplit]
  unfold squareRootBornPostTailRunningLowPrimeResponse
  simp [canonicalMoebiusWeight, Complex.re_sum] <;> ring
""",
)
replace_once(
    processed,
    """  unfold squareRootLowPrimeRunningImbalanceReal
    squareRootLowPrimeRunningImbalance
  simp
""",
    """  unfold squareRootLowPrimeRunningImbalanceReal
    squareRootLowPrimeRunningImbalance
  simp <;> ring
""",
)
replace_once(
    processed,
    """  · unfold squareRootLowPrimeProcessedSeatWeightReal
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := z.1)
""",
    """  · unfold squareRootLowPrimeProcessedSeatWeightReal
    have hInt : |(-μ z.1 : ℤ)| ≤ 1 := by
      simpa using (ArithmeticFunction.abs_moebius_le_one (n := z.1))
    exact_mod_cast hInt
""",
)

canonical = "RHLean/Proof/SquareRootLowPrimeCanonicalCreationResponseMap.lean"
replace_once(
    canonical,
    """  · have hdata := squareRootLowPrimeShallowBornSeatAtom_data hz
    have hc := Finset.mem_filter.mp hdata.1
    have hIcc := Finset.mem_Icc.mp hc.1
    exact ⟨by omega, hc.2.1, hc.2.2⟩
  · have hdata := squareRootLowPrimeShallowHighSeatAtom_data hz
    have hc := Finset.mem_filter.mp hdata.1
    have hIcc := Finset.mem_Icc.mp hc.1
    exact ⟨by omega, hc.2.1, hc.2.2⟩
""",
    """  · have hdata := squareRootLowPrimeShallowBornSeatAtom_data hz
    have hc := Finset.mem_filter.mp hdata.1
    rcases Finset.mem_Icc.mp hc.1 with ⟨hcOne, _hcTop⟩
    exact ⟨by omega, hc.2.1, hc.2.2⟩
  · have hdata := squareRootLowPrimeShallowHighSeatAtom_data hz
    have hc := Finset.mem_filter.mp hdata.1
    rcases Finset.mem_Icc.mp hc.1 with ⟨hcOne, _hcTop⟩
    exact ⟨by omega, hc.2.1, hc.2.2⟩
""",
)
replace_once(
    canonical,
    """  · have hc : zx.1 = zy.1 := congrArg Prod.fst hxy
    have hs : zx.2 = zy.2 := congrArg Prod.snd hxy
    exact congrArg (fun z => some (Sum.inl z)) (Prod.ext hc hs)
  · have hxData := squareRootLowPrimeShallowBornSeatAtom_data hzx
    have hyData := squareRootLowPrimeShallowHighSeatAtom_data hzy
    have hc : zx.1 = zy.1 := congrArg Prod.fst hxy
    have hs := congrArg Prod.snd hxy
    rw [squareRootLowPrimeCreationStateAbsoluteSeat,
      squareRootLowPrimeCreationStateAbsoluteSeat, hc] at hs
    have hzxBound := hxData.2
    omega
  · have hxData := squareRootLowPrimeShallowHighSeatAtom_data hzx
    have hyData := squareRootLowPrimeShallowBornSeatAtom_data hzy
    have hc : zx.1 = zy.1 := congrArg Prod.fst hxy
    have hs := congrArg Prod.snd hxy
    rw [squareRootLowPrimeCreationStateAbsoluteSeat,
      squareRootLowPrimeCreationStateAbsoluteSeat, ← hc] at hs
    have hzyBound := hyData.2
    omega
  · have hc : zx.1 = zy.1 := congrArg Prod.fst hxy
    have hs := congrArg Prod.snd hxy
    rw [squareRootLowPrimeCreationStateAbsoluteSeat,
      squareRootLowPrimeCreationStateAbsoluteSeat, hc] at hs
    have hseat : zx.2 = zy.2 := by omega
    exact congrArg (fun z => some (Sum.inr z)) (Prod.ext hc hseat)
""",
    """  · have hc : zx.1 = zy.1 := by
      simpa [squareRootLowPrimeCreationStateCofactor] using
        congrArg (fun w : ℕ × ℕ => w.1) hxy
    have hs : zx.2 = zy.2 := by
      simpa [squareRootLowPrimeCreationStateAbsoluteSeat] using
        congrArg (fun w : ℕ × ℕ => w.2) hxy
    exact congrArg (fun z => some (Sum.inl z)) (Prod.ext hc hs)
  · have hxData := squareRootLowPrimeShallowBornSeatAtom_data hzx
    have hc : zx.1 = zy.1 := by
      simpa [squareRootLowPrimeCreationStateCofactor] using
        congrArg (fun w : ℕ × ℕ => w.1) hxy
    have hs :
        zx.2 = squareRootBornPartnerCount R zy.1 + zy.2 := by
      simpa [squareRootLowPrimeCreationStateAbsoluteSeat] using
        congrArg (fun w : ℕ × ℕ => w.2) hxy
    have hzxBound := hxData.2
    rw [hc] at hzxBound
    omega
  · have hyData := squareRootLowPrimeShallowBornSeatAtom_data hzy
    have hc : zx.1 = zy.1 := by
      simpa [squareRootLowPrimeCreationStateCofactor] using
        congrArg (fun w : ℕ × ℕ => w.1) hxy
    have hs :
        squareRootBornPartnerCount R zx.1 + zx.2 = zy.2 := by
      simpa [squareRootLowPrimeCreationStateAbsoluteSeat] using
        congrArg (fun w : ℕ × ℕ => w.2) hxy
    have hzyBound := hyData.2
    rw [← hc] at hzyBound
    omega
  · have hc : zx.1 = zy.1 := by
      simpa [squareRootLowPrimeCreationStateCofactor] using
        congrArg (fun w : ℕ × ℕ => w.1) hxy
    have hs :
        squareRootBornPartnerCount R zx.1 + zx.2 =
          squareRootBornPartnerCount R zy.1 + zy.2 := by
      simpa [squareRootLowPrimeCreationStateAbsoluteSeat] using
        congrArg (fun w : ℕ × ℕ => w.2) hxy
    rw [hc] at hs
    have hseat : zx.2 = zy.2 := by omega
    exact congrArg (fun z => some (Sum.inr z)) (Prod.ext hc hseat)
""",
)
replace_once(
    canonical,
    """  have hprod := congrArg Prod.fst hxy
""",
    """  have hprod :
      squareRootLowPrimeCanonicalResponseOwner R K j U x *
          squareRootLowPrimeCreationStateCofactor x =
        squareRootLowPrimeCanonicalResponseOwner R K j U y *
          squareRootLowPrimeCreationStateCofactor y := by
    simpa [squareRootLowPrimeCanonicalCreationToResponse,
      squareRootLowPrimeCreationToResponseSeat] using
      congrArg (fun z : ℕ × ℕ => z.1) hxy
""",
)
replace_once(
    canonical,
    """  have hsEq :
      squareRootLowPrimeCreationStateAbsoluteSeat R x =
        squareRootLowPrimeCreationStateAbsoluteSeat R y :=
    congrArg Prod.snd hxy
""",
    """  have hsEq :
      squareRootLowPrimeCreationStateAbsoluteSeat R x =
        squareRootLowPrimeCreationStateAbsoluteSeat R y := by
    simpa [squareRootLowPrimeCanonicalCreationToResponse,
      squareRootLowPrimeCreationToResponseSeat] using
      congrArg (fun z : ℕ × ℕ => z.2) hxy
""",
)

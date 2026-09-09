import Mathlib
import RHLean.Proof.LowWheelFrozenCofactorTopBottomCancellation
import RHLean.Proof.LowWheelCanonicalRepeatedTerminalHighPrimeBridge

/-!
# The frozen top image carries no high prime

After `LowWheelFrozenCofactorTopBottomCancellation` the canonical downcross
ledger reads

`D_R = U_R + F_R^{c=1} - T_R`,

where `T_R` is the signed mass of the post-root image of the frozen
nontrivial-cofactor sector.  A natural next move is to try to absorb `T_R` into
the already-controlled external high-prime population, whose unique-parent part
carries the root budget `R`.

**That route is closed, and this file records why.**

Every high-prime population in this repository is indexed by a prime strictly
above the root: `squareRootHighPrimeCofactorSet R c` filters
`Finset.Ioc R (squareRootEndpoint R)`, and
`lowWheelCanonicalRepeatedExternalTerminalPart R` filters on
`R < lowWheelTaggedDowncrossPivot y`.

The image states carry no such prime.  Writing `y = (t,(c,p))` for a frozen
state with `c > 1` and `q = P⁺(c)`, the image is `(t,(c/q, q*p))`, and

* the image pivot is still `p`, and `p < q ≤ c < R`;
* the image quotient is `q*p`, whose only prime factors are `q` and `p`, both
  `< R`.

So the entire image is `R`-rough-free: it lies strictly below the root wall in
every prime coordinate.  The high-prime populations are, by definition, exactly
the states carrying a prime above the root.  The two are complementary, not
nested.

Three consequences are compiled below.

1.  `lowWheelFrozenCofactorTopImage_quotient_primes_lt_root` — no prime factor
    of an image quotient reaches the root.
2.  `lowWheelFrozenCofactorTopImage_subset_repeatedExternalTerminal_iff` — the
    proposed containment holds **only** in the vacuous case where the frozen
    nontrivial-cofactor sector is itself empty.
3.  `norm_lowWheelFrozenCofactorTopImageLedger_eq` — and independently of any
    containment, the relocation is norm-preserving:
    `‖T_R‖ = ‖F_R^{c>1}‖`.  A sign-reversing bijection cannot change a
    magnitude, so bounding `T_R` *is* bounding the frozen `c > 1` sector.  No
    reindexing can supply that bound; it has to come from new information about
    the sector itself.

This is a recorded no-go in the sense of `AGENTS.md`: a coordinate change does
not itself supply a quantitative estimate.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

namespace FrozenCofactorTopBottom

/-! ## The image lies strictly below the root wall -/

/-- The cofactor of a frozen nontrivial-cofactor state is below the root. -/
theorem lowWheelFrozenCofactor_cofactor_lt_root
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    y.2.1 < R := by
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have hcarrier := (Finset.mem_filter.mp hrepeated).1
  rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hcarrier with ⟨_ht, hx⟩
  have hphysical := (mem_lowWheelCanonicalDowncrossPart.mp hx).1
  have hcRange := (mem_lowWheelCanonicalPhysicalStateSet.mp hphysical).1
  exact (Finset.mem_Ico.mp hcRange).2

/-- The descending prime `q = P⁺(c)` is itself below the root. -/
theorem lowWheelFrozenCofactorTopPrime_lt_root
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelFrozenCofactorTopPrime y < R := by
  have hcgt := (Finset.mem_filter.mp hy).2
  rcases lowWheelFrozenCofactorTopPrime_data hy with ⟨_hqPrime, hqDvd, _hpq⟩
  have hcpos : 0 < y.2.1 := by omega
  have hqle : lowWheelFrozenCofactorTopPrime y ≤ y.2.1 :=
    Nat.le_of_dvd hcpos hqDvd
  exact lt_of_le_of_lt hqle (lowWheelFrozenCofactor_cofactor_lt_root hy)

/-- Hence the canonical pivot of a frozen nontrivial-cofactor state is below the
root, since it is strictly below `q`. -/
theorem lowWheelFrozenCofactor_pivot_lt_root
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelTaggedDowncrossPivot y < R := by
  rcases lowWheelFrozenCofactorTopPrime_data hy with ⟨_hqPrime, _hqDvd, hpq⟩
  exact hpq.trans (lowWheelFrozenCofactorTopPrime_lt_root hy)

/-- The image quotient is the descending prime times the old quotient. -/
theorem lowWheelFrozenCofactorTopToggle_quotient
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    (lowWheelFrozenCofactorTopToggle y).2.2 =
      lowWheelFrozenCofactorTopPrime y * y.2.2 := by
  rw [lowWheelFrozenCofactorTopToggle_eq hy]

/-- **The image pivot never reaches the root.** -/
theorem lowWheelFrozenCofactorTopImage_pivot_lt_root
    {R : ℕ} {z : LowWheelTaggedDowncrossState}
    (hz : z ∈ lowWheelFrozenCofactorTopImage R) :
    lowWheelTaggedDowncrossPivot z < R := by
  rcases mem_lowWheelFrozenCofactorTopImage.mp hz with ⟨y, hy, rfl⟩
  have hpivot :
      lowWheelCanonicalCofactorQuotientPivot
          (lowWheelFrozenCofactorTopToggle y).2 =
        lowWheelTaggedDowncrossPivot y :=
    lowWheelFrozenCofactorTopToggle_pivot y
  have hgoal :
      lowWheelTaggedDowncrossPivot (lowWheelFrozenCofactorTopToggle y) =
        lowWheelTaggedDowncrossPivot y := hpivot
  rw [hgoal]
  exact lowWheelFrozenCofactor_pivot_lt_root hy

/-- **The image carries no prime above the root.**  Every prime factor of an
image quotient is strictly below `R`. -/
theorem lowWheelFrozenCofactorTopImage_quotient_primes_lt_root
    {R : ℕ} {z : LowWheelTaggedDowncrossState}
    (hz : z ∈ lowWheelFrozenCofactorTopImage R)
    {r : ℕ} (hr : r.Prime) (hrdvd : r ∣ z.2.2) :
    r < R := by
  rcases mem_lowWheelFrozenCofactorTopImage.mp hz with ⟨y, hy, rfl⟩
  rcases lowWheelFrozenCofactorTopPrime_data hy with ⟨hqPrime, _hqDvd, _hpq⟩
  have hp : (lowWheelTaggedDowncrossPivot y).Prime :=
    lowWheelFrozenCofactor_pivot_prime hy
  have hshape : y.2.2 = lowWheelTaggedDowncrossPivot y :=
    lowWheelFrozenCofactor_quotient_eq_pivot hy
  have hquot :
      (lowWheelFrozenCofactorTopToggle y).2.2 =
        lowWheelFrozenCofactorTopPrime y * y.2.2 :=
    lowWheelFrozenCofactorTopToggle_quotient hy
  rw [hquot, hshape] at hrdvd
  rcases (Nat.Prime.dvd_mul hr).mp hrdvd with hrq | hrp
  · have : r = lowWheelFrozenCofactorTopPrime y :=
      (Nat.prime_dvd_prime_iff_eq hr hqPrime).mp hrq
    rw [this]
    exact lowWheelFrozenCofactorTopPrime_lt_root hy
  · have : r = lowWheelTaggedDowncrossPivot y :=
      (Nat.prime_dvd_prime_iff_eq hr hp).mp hrp
    rw [this]
    exact lowWheelFrozenCofactor_pivot_lt_root hy

/-! ## The proposed containment is exactly the vacuous case -/

/-- The image is disjoint from the repeated external terminal (high-prime)
population: that population needs pivot above the root, the image has pivot
below it. -/
theorem lowWheelFrozenCofactorTopImage_disjoint_repeatedExternalTerminal
    (R : ℕ) :
    Disjoint (lowWheelFrozenCofactorTopImage R)
      (lowWheelCanonicalRepeatedExternalTerminalPart R) := by
  rw [Finset.disjoint_left]
  intro z hzImage hzExternal
  have hlt := lowWheelFrozenCofactorTopImage_pivot_lt_root hzImage
  have hgt := (mem_lowWheelCanonicalRepeatedExternalTerminalPart.mp hzExternal).2
  omega

/-- **No-go.**  The image is contained in the repeated external high-prime
population precisely when the frozen nontrivial-cofactor sector is empty, in
which case there was nothing to absorb.  So the containment can never be used to
transfer a bound. -/
theorem lowWheelFrozenCofactorTopImage_subset_repeatedExternalTerminal_iff
    (R : ℕ) :
    lowWheelFrozenCofactorTopImage R ⊆
        lowWheelCanonicalRepeatedExternalTerminalPart R ↔
      lowWheelCanonicalRepeatedFrozenCofactorPart R = ∅ := by
  constructor
  · intro hsub
    have hdisj :=
      lowWheelFrozenCofactorTopImage_disjoint_repeatedExternalTerminal R
    have himageEmpty : lowWheelFrozenCofactorTopImage R = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro z hz
      exact (Finset.disjoint_left.mp hdisj) hz (hsub hz)
    rw [Finset.eq_empty_iff_forall_notMem]
    intro y hy
    have : lowWheelFrozenCofactorTopToggle y ∈
        lowWheelFrozenCofactorTopImage R :=
      mem_lowWheelFrozenCofactorTopImage.mpr ⟨y, hy, rfl⟩
    rw [himageEmpty] at this
    exact absurd this (Finset.notMem_empty _)
  · intro hempty z hz
    rcases mem_lowWheelFrozenCofactorTopImage.mp hz with ⟨y, hy, _⟩
    rw [hempty] at hy
    exact absurd hy (Finset.notMem_empty _)

/-! ## The relocation is norm-preserving -/

/-- **The reindexing cannot supply a bound.**  The post-root image ledger and
the frozen nontrivial-cofactor ledger have equal norm, so bounding `T_R` is
literally bounding `F_R^{c>1}`.  Any linear bound on one is a linear bound on
the other; neither follows from the exact identity alone. -/
theorem norm_lowWheelFrozenCofactorTopImageLedger_eq
    (R : ℕ) :
    ‖lowWheelFrozenCofactorTopImageLedger R‖ =
      ‖lowWheelCanonicalFrozenCofactorLedger R‖ := by
  rw [lowWheelFrozenCofactorTopImageLedger_eq_neg, norm_neg]

/-- Consequently the restated seam is equivalent to a linear bound on the two
sectors that actually remain, with no contribution recoverable from the
high-prime budget. -/
theorem lowWheelCanonicalDowncrossLedger_norm_le_of_sectors
    {R : ℕ} {A B : ℝ}
    (hU : ‖lowWheelCanonicalDowncrossUniqueParentLedger R‖ ≤ A)
    (hT : ‖lowWheelCanonicalTerminalBoundaryLedger R‖ ≤ B)
    {C : ℝ}
    (hF : ‖lowWheelCanonicalFrozenCofactorLedger R‖ ≤ C) :
    ‖lowWheelCanonicalDowncrossLedger R‖ ≤ A + B + C := by
  rw [lowWheelCanonicalDowncrossLedger_eq_unique_add_terminal_sub_topImage]
  have hsplit :
      ‖lowWheelCanonicalDowncrossUniqueParentLedger R +
          lowWheelCanonicalTerminalBoundaryLedger R -
            lowWheelFrozenCofactorTopImageLedger R‖ ≤
        ‖lowWheelCanonicalDowncrossUniqueParentLedger R +
            lowWheelCanonicalTerminalBoundaryLedger R‖ +
          ‖lowWheelFrozenCofactorTopImageLedger R‖ :=
    norm_sub_le _ _
  have hadd :
      ‖lowWheelCanonicalDowncrossUniqueParentLedger R +
          lowWheelCanonicalTerminalBoundaryLedger R‖ ≤ A + B :=
    (norm_add_le _ _).trans (add_le_add hU hT)
  have himage : ‖lowWheelFrozenCofactorTopImageLedger R‖ ≤ C := by
    rw [norm_lowWheelFrozenCofactorTopImageLedger_eq]
    exact hF
  linarith

end FrozenCofactorTopBottom

end RHLean.Proof
